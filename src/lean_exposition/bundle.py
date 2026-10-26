"""Build an inspectable, explicit file set; never publish or call an LLM."""
from __future__ import annotations

import io
import os
import stat
import zipfile
import zlib
from collections.abc import Mapping
from contextlib import contextmanager
from dataclasses import dataclass, field
from importlib.resources import files
from pathlib import Path
from types import MappingProxyType

from .contracts import ContractError, decode_json, digest, encoded, local_path, require_refs, required_citation_ids, validate_artifact, validate_graph, validate_schema

STAGES = ("long", "short", "expository")
BUNDLE_FILES = ("manifest.json", "graph.json") + tuple(
    f"papers/{stage}.{ext}" for stage in STAGES for ext in ("md", "json")
)
MAX_MEMBER_BYTES = 32 * 1024 * 1024
MAX_BUNDLE_BYTES = 64 * 1024 * 1024
MAX_ARCHIVE_BYTES = MAX_BUNDLE_BYTES + 1024 * 1024
_DIRECTORY_HANDLES = (
    bool(getattr(os, "O_NOFOLLOW", 0)) and bool(getattr(os, "O_DIRECTORY", 0))
    and bool(getattr(os, "O_NONBLOCK", 0))
    and os.open in os.supports_dir_fd and os.mkdir in os.supports_dir_fd
    and os.stat in os.supports_dir_fd and os.stat in os.supports_follow_symlinks
    and os.listdir in os.supports_fd
)


@dataclass(frozen=True, init=False, slots=True)
class BundleCapture:
    """One validated, immutable edition captured from a directory or ZIP.

    Construction accepts a filesystem path, never caller-supplied payloads.
    All bytes and the validation result belong to this capture; later changes
    to the input cannot change the edition seen by a consumer.
    """

    files: Mapping[str, bytes] = field(repr=False)
    _summary_bytes: bytes = field(repr=False)

    def __init__(self, path: Path):
        if hasattr(self, "files"):
            raise AttributeError("a bundle capture cannot be reinitialized")
        payload, summary = _validated_capture(Path(path))
        object.__setattr__(self, "files", MappingProxyType(payload))
        object.__setattr__(self, "_summary_bytes", encoded(summary))


def _manifest(bundle_id: str, payload: dict[str, bytes], states: list[str]) -> dict:
    return {
        "schema_version": "1.0", "bundle_id": bundle_id, "bundle_version": "0.1.0",
        "graph": "graph.json",
        "documents": [{"stage": stage, "mapping": f"papers/{stage}.json"} for stage in STAGES],
        "files": [{"path": name, "sha256": digest(payload[name])} for name in BUNDLE_FILES[1:]],
        "status": "scaffold" if set(states) == {"scaffold"} else "authored",
        "publication": "local_only",
    }


def _require_empty_output(out: Path) -> None:
    if out.is_symlink() or (out.exists() and (not out.is_dir() or any(out.iterdir()))):
        raise ContractError("output directory must be empty")


def scaffold(graph: dict, out: Path) -> dict:
    summary = validate_graph(graph)
    out = Path(out)
    _require_empty_output(out)
    graph_bytes = encoded(graph)
    payload = {"graph.json": graph_bytes}
    for stage in STAGES:
        content = files("lean_exposition").joinpath(f"resources/templates/{stage}.md").read_bytes()
        path = f"papers/{stage}.md"
        payload[path] = content
        mapping = {
            "schema_version": "1.0", "stage": stage, "state": "scaffold", "path": path,
            "content_sha256": digest(content), "graph_sha256": digest(graph_bytes),
            "selected_goal_ids": graph["selected_goals"], "claim_ids": [],
            "citation_ids": sorted(required_citation_ids(graph)),
            "assumption_ids": summary["assumptions"], "unresolved_ids": summary["unresolved"],
            "passages": [], "review_state": "not_reviewed", "review_notes": [],
        }
        payload[f"papers/{stage}.json"] = encoded(mapping)
    manifest = _manifest(graph["id"], payload, ["scaffold"] * len(STAGES))
    payload["manifest.json"] = encoded(manifest)
    for name, content in payload.items():
        if len(content) > MAX_MEMBER_BYTES:
            raise ContractError(f"artifact exceeds size limit: {name}")
    if sum(map(len, payload.values())) > MAX_BUNDLE_BYTES:
        raise ContractError("bundle exceeds total size limit")
    _validate_payload(payload)
    _write_bundle_directory(out, payload)
    check_bundle(out)
    return manifest


@contextmanager
def _open_directory(path, name: str, *, dir_fd: int | None = None):
    """Hold a directory open without following the final component."""
    flags = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW | getattr(os, "O_NONBLOCK", 0)
    try:
        fd = os.open(path, flags, dir_fd=dir_fd) if dir_fd is not None else os.open(path, flags)
    except OSError as exc:
        raise ContractError(f"cannot open bundle directory: {name}") from exc
    try:
        if not stat.S_ISDIR(os.fstat(fd).st_mode):
            raise ContractError(f"not a bundle directory: {name}")
        yield fd
    finally:
        os.close(fd)


def _fdopen(fd: int, mode: str):
    try:
        return os.fdopen(fd, mode)
    except BaseException:
        os.close(fd)
        raise


def _read_regular(path: Path, name: str, limit: int, *, dir_fd: int | None = None) -> bytes:
    """Bound reads and refuse links or special files before consuming bytes.

    Descriptor-relative calls are anchored to an already opened directory. On
    platforms without directory handles, lstat/fstat checks retain portable use
    but cannot prevent substitution of a parent directory by a concurrent actor.
    """
    flags = (os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0)
             | getattr(os, "O_NONBLOCK", 0) | getattr(os, "O_BINARY", 0))
    try:
        before = None
        if dir_fd is None:
            before = Path(path).lstat()
            if stat.S_ISLNK(before.st_mode):
                raise ContractError(f"symlink is not a bundle artifact: {name}")
            if not stat.S_ISREG(before.st_mode):
                raise ContractError(f"not a regular artifact: {name}")
        fd = os.open(path, flags, dir_fd=dir_fd) if dir_fd is not None else os.open(path, flags)
        with _fdopen(fd, "rb") as stream:
            metadata = os.fstat(stream.fileno())
            if not stat.S_ISREG(metadata.st_mode):
                raise ContractError(f"not a regular artifact: {name}")
            if before is not None and not os.path.samestat(before, metadata):
                raise ContractError(f"artifact changed during open: {name}")
            if metadata.st_size > limit:
                raise ContractError(f"artifact exceeds size limit: {name}")
            content = stream.read(limit + 1)
    except FileNotFoundError as exc:
        raise ContractError(f"missing artifact: {name}") from exc
    except OSError as exc:
        raise ContractError(f"cannot read artifact: {name}") from exc
    if len(content) > limit:
        raise ContractError(f"artifact exceeds size limit: {name}")
    return content


def _capture_directory(root: Path) -> dict[str, bytes]:
    def capture(read):
        payload = {}
        size = 0
        for name in BUNDLE_FILES:
            content = read(name)
            size += len(content)
            if size > MAX_BUNDLE_BYTES:
                raise ContractError("bundle exceeds total size limit")
            payload[name] = content
        return payload

    if not _DIRECTORY_HANDLES:
        return capture(lambda name: _read_regular(local_path(root, name), name, MAX_MEMBER_BYTES))
    with _open_directory(root, "bundle") as root_fd:
        with _open_directory("papers", "papers", dir_fd=root_fd) as papers_fd:
            def read(name):
                parent_fd = papers_fd if name.startswith("papers/") else root_fd
                return _read_regular(Path(name).name, name, MAX_MEMBER_BYTES, dir_fd=parent_fd)
            return capture(read)


def _capture_archive(path: Path) -> dict[str, bytes]:
    # Capture the archive first; never extract untrusted entries to the filesystem.
    content = _read_regular(path, "bundle ZIP", MAX_ARCHIVE_BYTES)
    try:
        with zipfile.ZipFile(io.BytesIO(content)) as archive:
            members = archive.infolist()
            names = [member.filename for member in members]
            if len(names) != len(set(names)):
                raise ContractError("duplicate bundle ZIP member")
            if set(names) != set(BUNDLE_FILES):
                raise ContractError("bundle ZIP must contain exactly the eight contract files")
            size = 0
            for member in members:
                if member.orig_filename != member.filename:
                    raise ContractError("invalid bundle ZIP member name")
                mode = stat.S_IFMT(member.external_attr >> 16)
                if member.is_dir() or member.external_attr & 0x10 or mode not in (0, stat.S_IFREG):
                    raise ContractError(f"not a regular ZIP artifact: {member.filename}")
                if member.flag_bits & 1:
                    raise ContractError(f"encrypted ZIP artifact: {member.filename}")
                if member.compress_type not in (zipfile.ZIP_STORED, zipfile.ZIP_DEFLATED):
                    raise ContractError(f"unsupported ZIP compression: {member.filename}")
                if member.file_size > MAX_MEMBER_BYTES:
                    raise ContractError(f"artifact exceeds size limit: {member.filename}")
                size += member.file_size
            if size > MAX_BUNDLE_BYTES:
                raise ContractError("bundle exceeds total size limit")
            payload = {}
            for member in members:
                with archive.open(member) as stream:
                    data = stream.read(MAX_MEMBER_BYTES + 1)
                if len(data) != member.file_size or len(data) > MAX_MEMBER_BYTES:
                    raise ContractError(f"invalid ZIP artifact size: {member.filename}")
                payload[member.filename] = data
            return payload
    except (zipfile.BadZipFile, EOFError, OSError, RuntimeError, UnicodeError, zlib.error) as exc:
        raise ContractError("invalid bundle ZIP") from exc


def _artifact_error(name: str, error: Exception) -> ContractError:
    detail = str(error)
    if len(detail) > 240:
        detail = detail[:237] + "..."
    return ContractError(f"{name}: {detail}")


def _decode_artifact(payload: dict[str, bytes], name: str, schema: str) -> dict:
    try:
        value = decode_json(payload[name])
        validate_schema(value, schema)
    except (ContractError, ValueError, RecursionError) as exc:
        raise _artifact_error(name, exc) from exc
    return value


def _validate_payload(payload: dict[str, bytes], *, current_authoring: bool = False) -> dict:
    manifest = _decode_artifact(payload, "manifest.json", "bundle")
    if manifest["publication"] != "local_only":
        raise ContractError("this tool prepares local bundles only")
    if manifest["graph"] != "graph.json":
        raise ContractError("bundle graph must be graph.json")
    names = [r["path"] for r in manifest["files"]]
    if len(names) != len(set(names)):
        raise ContractError("duplicate bundle file")
    expected = set(BUNDLE_FILES) - {"manifest.json"}
    if set(names) != expected:
        raise ContractError("bundle must name exactly the graph and three paper/mapping pairs")
    for row in manifest["files"]:
        if digest(payload[row["path"]]) != row["sha256"]:
            raise ContractError(f"bundle hash mismatch: {row['path']}")
    graph = _decode_artifact(payload, "graph.json", "graph")
    try:
        summary = validate_graph(graph)
    except (ContractError, ValueError) as exc:
        raise _artifact_error("graph.json", exc) from exc
    if manifest["bundle_id"] != graph["id"]:
        raise ContractError("bundle identity differs from graph")
    if manifest["documents"] != [{"stage": s, "mapping": f"papers/{s}.json"} for s in STAGES]:
        raise ContractError("paper stages or mappings differ from contract")
    states, artifacts = [], {}
    for s in STAGES:
        name = f"papers/{s}.json"
        artifact = _decode_artifact(payload, name, "artifact")
        if artifact["stage"] != s or artifact["path"] != f"papers/{s}.md":
            raise ContractError("paper mapping uses wrong stage/path")
        try:
            validate_artifact(
                artifact, graph, digest(payload["graph.json"]), payload[artifact["path"]],
                require_current_formal_assurance=current_authoring,
                require_current_citations=current_authoring,
            )
        except (ContractError, ValueError) as exc:
            raise _artifact_error(name, exc) from exc
        states.append(artifact["state"])
        artifacts[s] = artifact
    # Resolve only against the exact mappings in this validated capture. A
    # separate pass permits links to later stages and forward passage anchors.
    passages = {stage: {row["anchor"]: row for row in artifact["passages"]}
                for stage, artifact in artifacts.items()}
    for stage, artifact in artifacts.items():
        try:
            for link in artifact.get("reading_links", []):
                targets = passages[link["to_stage"]]
                require_refs([link["to_anchor"]], targets,
                             f"reading link target in {link['to_stage']}")
                if link["to_text_sha256"] != targets[link["to_anchor"]]["text_sha256"]:
                    raise ContractError(f"reading link target passage hash is stale in {link['to_stage']}")
        except ContractError as exc:
            raise _artifact_error(f"papers/{stage}.json", exc) from exc
    derived = "scaffold" if set(states) == {"scaffold"} else "authored"
    if manifest["status"] != derived:
        raise ContractError("bundle status differs from paper states")
    return {"valid": True, "bundle_id": graph["id"], "paper_states": states, "graph": summary}


def _validated_capture(path: Path | BundleCapture) -> tuple[dict[str, bytes], dict]:
    if isinstance(path, BundleCapture):
        return dict(path.files), decode_json(path._summary_bytes)
    path = Path(path)
    if path.is_symlink():
        raise ContractError("bundle input must not be a symlink")
    payload = _capture_directory(path) if path.is_dir() else _capture_archive(path)
    return payload, _validate_payload(payload)


def load_bundle(path: Path | BundleCapture) -> dict[str, bytes]:
    """Read and validate a directory or ZIP, returning the exact captured files.

    Only the eight v0.1.0 contract files are returned. External sources and receipts
    are never fetched or read. ZIP members are checked without extracting them.
    An existing BundleCapture returns a fresh mapping of its immutable bytes,
    without reopening or revalidating the original filesystem input.
    """
    return _validated_capture(path)[0]


def check_bundle(root: Path | BundleCapture) -> dict:
    """Validate a directory or ZIP and return the existing graph/paper summary."""
    return _validated_capture(root)[1]


def _write_regular(path, name: str, content: bytes, *, dir_fd: int | None = None) -> None:
    flags = (os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, "O_NOFOLLOW", 0)
             | getattr(os, "O_BINARY", 0))
    try:
        fd = (os.open(path, flags, 0o666, dir_fd=dir_fd) if dir_fd is not None
              else os.open(path, flags, 0o666))
        with _fdopen(fd, "wb") as stream:
            metadata = os.fstat(stream.fileno())
            if not stat.S_ISREG(metadata.st_mode):
                raise ContractError(f"not a regular artifact: {name}")
            if dir_fd is None:
                current = Path(path).lstat()
                if not stat.S_ISREG(current.st_mode) or not os.path.samestat(current, metadata):
                    raise ContractError(f"artifact changed during open: {name}")
            stream.write(content)
    except OSError as exc:
        raise ContractError(f"cannot write artifact: {name}") from exc


def _check_directory_identity(fd: int, path, name: str, *, dir_fd: int | None = None) -> None:
    try:
        current = (os.stat(path, dir_fd=dir_fd, follow_symlinks=False) if dir_fd is not None
                   else os.stat(path, follow_symlinks=False))
        if not stat.S_ISDIR(current.st_mode) or not os.path.samestat(current, os.fstat(fd)):
            raise ContractError(f"bundle directory changed during assembly: {name}")
    except OSError as exc:
        raise ContractError(f"bundle directory changed during assembly: {name}") from exc


def _write_bundle_directory(out: Path, payload: dict[str, bytes]) -> None:
    """Write through held directory handles where available.

    The pathname fallback preserves portable use with regular-file checks, but
    cannot guarantee confinement against concurrent parent-directory swaps.
    """
    _require_empty_output(out)
    out.mkdir(parents=True, exist_ok=True)
    if not _DIRECTORY_HANDLES:
        for name in BUNDLE_FILES:
            target = local_path(out, name)
            target.parent.mkdir(parents=True, exist_ok=True)
            _write_regular(target, name, payload[name])
        return
    with _open_directory(out, "output") as root_fd:
        if os.listdir(root_fd):
            raise ContractError("output directory must be empty")
        try:
            os.mkdir("papers", dir_fd=root_fd)
        except OSError as exc:
            raise ContractError("cannot create bundle papers directory") from exc
        with _open_directory("papers", "papers", dir_fd=root_fd) as papers_fd:
            for name in BUNDLE_FILES:
                parent_fd = papers_fd if name.startswith("papers/") else root_fd
                _write_regular(Path(name).name, name, payload[name], dir_fd=parent_fd)
            _check_directory_identity(papers_fd, "papers", "papers", dir_fd=root_fd)
            _check_directory_identity(root_fd, out, "output")


def assemble_bundle(
    graph_path: Path, stage_pairs: dict[str, tuple[Path, Path]], out: Path,
) -> dict:
    """Package three existing Markdown/mapping pairs without changing bindings.

    Each pair is (Markdown path, mapping path). Graph and document hashes must
    already bind the supplied bytes. New assembly requires current citation and
    formal-result assurance checks; check_bundle and load_bundle retain the
    historical reading contract. Validation finishes before output is created.
    """
    if set(stage_pairs) != set(STAGES):
        raise ContractError("assembly requires exactly long, short and expository pairs")
    out = Path(out)
    _require_empty_output(out)
    payload = {"graph.json": _read_regular(Path(graph_path), "graph.json", MAX_MEMBER_BYTES)}
    graph = _decode_artifact(payload, "graph.json", "graph")
    states = []
    for stage in STAGES:
        pair = stage_pairs[stage]
        if not isinstance(pair, (tuple, list)) or len(pair) != 2:
            raise ContractError(f"{stage}: supply a Markdown path and a mapping path")
        for extension, source in zip(("md", "json"), pair):
            name = f"papers/{stage}.{extension}"
            payload[name] = _read_regular(Path(source), name, MAX_MEMBER_BYTES)
        artifact = _decode_artifact(payload, f"papers/{stage}.json", "artifact")
        states.append(artifact["state"])
    manifest = _manifest(graph["id"], payload, states)
    payload["manifest.json"] = encoded(manifest)
    if sum(map(len, payload.values())) > MAX_BUNDLE_BYTES:
        raise ContractError("bundle exceeds total size limit")
    _validate_payload(payload, current_authoring=True)
    _write_bundle_directory(out, payload)
    return manifest


def export_bundle(root: Path | BundleCapture, out: Path) -> dict:
    if out.exists() or out.is_symlink():
        raise ContractError("export destination already exists")
    payload, result = _validated_capture(root)
    out.parent.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(out, "x", compression=zipfile.ZIP_STORED) as archive:
        for name, content in sorted(payload.items()):
            info = zipfile.ZipInfo(name, date_time=(2026, 1, 1, 0, 0, 0))
            info.create_system = 3
            info.create_version = 20
            info.extract_version = 20
            info.external_attr = 0o100644 << 16
            info.compress_type = zipfile.ZIP_STORED
            archive.writestr(info, content)
    return {"bundle_id": result["bundle_id"], "sha256": digest(out.read_bytes()), "files": len(payload)}

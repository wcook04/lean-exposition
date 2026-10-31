"""Index a pinned Lean 4 source tree from its text, without a Lean toolchain.

The index is a sidecar for readers: it says where each declaration is written and
which indexed declarations its source text names. It never runs Lean, and text
dependencies are a reading aid. Names reached through notation, tactics or
elaboration are invisible here, and a shadowed name can be mistaken for a global
one. Elaborated dependencies from the packaged extractor replace these rows
declaration by declaration, and every row records which of the two it holds.
"""
from __future__ import annotations

import hashlib
import json
import re
from bisect import bisect_right
from pathlib import Path

from .contracts import ContractError, digest, read_json

INDEX_SCHEMA_VERSION = "1.0"
ROOTS = ("OAI", "ComparatorChallenges")
DECLARATION_KEYWORDS = {"theorem", "lemma", "def", "abbrev", "structure", "class", "instance",
                        "inductive", "opaque", "axiom", "example", "irreducible_def"}
KINDS = ("theorem", "lemma", "def", "abbrev", "structure", "class", "instance", "inductive",
         "opaque", "axiom")
# Other command words; inside a proof these can be ordinary names or tactics, so
# they begin a command only at or left of the current command's column.
SCOPE_COMMANDS = {"namespace", "section", "mutual"}
HARD_COMMANDS = {"namespace", "section", "end", "mutual", "universe", "attribute", "notation",
                 "notation3", "macro", "macro_rules", "syntax", "elab", "elab_rules", "infix",
                 "infixl", "infixr", "prefix", "postfix", "declare_syntax_cat", "initialize",
                 "builtin_initialize", "add_decl_doc", "alias", "run_cmd", "import", "export"}
SOFT_COMMANDS = {"open", "set_option", "omit", "include", "variable", "unseal", "seal"}
MODIFIERS = {"private", "protected", "public", "noncomputable", "unsafe", "partial", "nonrec",
             "scoped", "local", "meta"}
OPENERS = {"(": ")", "[": "]", "{": "}", "⟨": "⟩", "⦃": "⦄", "⟦": "⟧", "#[": "]", "@[": "]",
           "`(": ")", "⟪": "⟫"}
CLOSERS = set(OPENERS.values())
# Words of the language that are never references to a declaration.
RESERVED = {"at", "by", "calc", "deriving", "do", "else", "extends", "for", "from", "fun", "have",
            "if", "in", "instance", "let", "match", "nomatch", "nofun", "show", "suffices", "then",
            "this", "using", "where", "with", "Type", "Sort", "Prop", "_", "sorry", "rec",
            "mut", "return", "unless", "try", "catch", "finally", "true", "false"}
BINDER_KEYWORDS = {"fun", "λ", "∀", "∃", "∑", "∏", "⋃", "⋂", "⨆", "⨅", "∫", "intro", "intros",
                   "rintro", "obtain", "with", "have", "haveI", "let", "letI", "set", "suffices",
                   "ext", "funext"}
BINDER_STOPS = {":", ":=", "=>", "↦", ",", "∈", "<", "≤", ">", "≥", "∂", ";", "<;>", "using"}
# These are written after an unrelated value far more often than they name ours.
AMBIENT_FIELDS = {"add", "sub", "mul", "div", "neg", "inv", "pow", "le", "lt", "ge", "gt", "ne",
                  "eq", "symm", "trans", "mono", "comp", "const", "id", "smul", "congr", "refl",
                  "antisymm", "continuous", "measurable", "integrable", "bounded", "of", "mk",
                  "val", "property", "left", "right", "fst", "snd", "some", "none", "map", "sum"}
GENERATED = re.compile(r"(?:^|\.)(?:_[^.]*|match_\d+|proof_\d+|eq_\d+|eq_def|sizeOf_spec|rec|recOn|"
                       r"casesOn|noConfusion|noConfusionType|below|ibelow|brecOn|binductionOn|"
                       r"inj|injEq|ctorIdx)(?:\.|$)")

_START = ("A-Za-z_Α-ΟΡ΢Τ-Ωα-κμ-ωϊ-ϻ"
          "ἀ-῾℀-⅏\U0001d49c-\U0001d59f")
_REST = _START + "0-9'!?₀-₉ₐ-ₜᵢ-ᵪ"
_PART = f"(?:«[^»\\n]*»|[{_START}][{_REST}]*)"
_TOKEN = re.compile(
    r"(?P<space>\s+)|(?P<line>--[^\n]*)|(?P<block>/-)|(?P<raw>r#*\")|(?P<interp>[smf]!\")"
    r"|(?P<string>\"(?:[^\"\\]|\\.)*(?:\"|\Z))"
    r"|(?P<char>'(?:\\(?:[^xu]|x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4})|[^\\'\n])')"
    rf"|(?P<ident>\.?{_PART}(?:\.{_PART})*)"
    r"|(?P<number>[0-9][0-9a-zA-Z_]*(?:\.[0-9]+)?)"
    r"|(?P<symbol>:=|=>|::|<;>|\.\.\.?|@\[|\#\[|`\()"
    r"|(?P<other>.)", re.DOTALL)
IDENT, DOC, STRING, SYMBOL = "ident", "doc", "string", "symbol"
ANY_COLUMN = 1 << 30


def _skip_block(text, start):
    """Return the offset after a nested block comment opened at `start`."""
    depth, i = 1, start + 2
    while depth:
        opening, closing = text.find("/-", i), text.find("-/", i)
        if closing < 0:
            return len(text)
        if 0 <= opening < closing:
            depth, i = depth + 1, opening + 2
        else:
            depth, i = depth - 1, closing + 2
    return i


def _skip_interpolated(text, start):
    """Return the offset after an interpolated string body beginning at `start`."""
    i, braces = start, 0
    while i < len(text):
        c = text[i]
        if c == "\\":
            i += 2
            continue
        if braces:
            if c == '"':
                i = _skip_interpolated(text, i + 1)
                continue
            braces += (c == "{") - (c == "}")
        elif c == "{":
            braces = 1
        elif c == '"':
            return i + 1
        i += 1
    return len(text)


def tokenize(text):
    """Tokens as (kind, text, offset, line, column, first-on-line); comments are dropped."""
    starts = [0] + [m.end() for m in re.finditer("\n", text)]
    tokens, i, seen_line = [], 0, 0

    def add(kind, value, offset):
        nonlocal seen_line
        line = bisect_right(starts, offset)
        tokens.append((kind, value, offset, line, offset - starts[line - 1], line != seen_line))
        seen_line = line

    while i < len(text):
        match = _TOKEN.match(text, i)
        kind, value = match.lastgroup, match.group()
        if kind == "block":
            end = _skip_block(text, i)
            if text.startswith("/--", i) and not text.startswith("/--/", i):
                add(DOC, text[i + 3:max(i + 3, end - 2)].strip(), i)
            i = end
        elif kind == "raw":
            quotes = '"' + "#" * (len(value) - 2)
            end = text.find(quotes, match.end())
            i = len(text) if end < 0 else end + len(quotes)
            add(STRING, "", match.start())
        elif kind == "interp":
            i = _skip_interpolated(text, match.end())
            add(STRING, "", match.start())
        elif kind in {"space", "line"}:
            i = match.end()
        else:
            if kind == "ident" or kind == "symbol" or kind == "other":
                add(kind if kind == "ident" else SYMBOL, value, i)
            elif kind == "string":
                add(STRING, "", i)
            else:
                add("literal", value, i)
            i = match.end()
    return tokens


class _Scope:
    __slots__ = ("kind", "name", "opens", "variables", "noncomputable")

    def __init__(self, kind, name="", noncomputable=False):
        self.kind, self.name = kind, name
        self.opens, self.variables = [], set()
        self.noncomputable = noncomputable


def _commands(tokens):
    """Split a file into commands: (start with modifiers, keyword index, end)."""
    heads, stack, pending, current_column = [], [], None, ANY_COLUMN
    for i, token in enumerate(tokens):
        kind, value, _, _, column, _ = token
        if kind == SYMBOL and value in OPENERS and not (value == "@[" and not stack):
            stack.append(value)
            continue
        if kind == SYMBOL and value in CLOSERS:
            if stack:
                stack.pop()
            continue
        if kind == DOC and not stack:
            if pending is None:
                pending = i
            continue
        if kind == SYMBOL and value == "@[":  # depth zero: an attribute list before a command
            pending = i if pending is None else pending
            stack.append(value)
            continue
        if stack and not (column == 0 and kind == IDENT and value in DECLARATION_KEYWORDS
                          and "`(" not in stack):
            continue
        stack.clear()
        if kind != IDENT:
            if kind == SYMBOL and value == "#" and column <= current_column and token[5] \
                    and i + 1 < len(tokens) and tokens[i + 1][0] == IDENT:
                heads.append((i if pending is None else pending, i))
                current_column, pending = column, None
            else:
                pending = None
            continue
        if value in MODIFIERS:
            if pending is None and i + 1 < len(tokens):
                pending = i
            continue
        following = tokens[i + 1][1] if i + 1 < len(tokens) else ""
        written_at = tokens[pending][4] if pending is not None else column
        is_head = (value in DECLARATION_KEYWORDS or (value == "deriving" and following == "instance")
                   or (value in HARD_COMMANDS | SOFT_COMMANDS and written_at <= current_column))
        if value == "instance" and i and tokens[i - 1][1] == "deriving":
            is_head = False
        if is_head:
            heads.append((i if pending is None else pending, i))
            # The body of a scope may be indented; a declaration's proof always is.
            current_column = ANY_COLUMN if value in SCOPE_COMMANDS else written_at
        pending = None
    return [(start, head, heads[n + 1][0] if n + 1 < len(heads) else len(tokens))
            for n, (start, head) in enumerate(heads)]


def _modifiers(tokens, start, head):
    flags, docstring, depth = set(), None, 0
    for kind, value, *_ in tokens[start:head]:
        if kind == SYMBOL and value in OPENERS:
            depth += 1
        elif kind == SYMBOL and value in CLOSERS:
            depth -= 1
        elif kind == DOC:
            docstring = value
        elif not depth and value in MODIFIERS:
            flags.add(value)
    return flags, docstring


def _skip_group(tokens, i, end):
    """Return the index after the bracket group opening at `i`."""
    depth = 0
    while i < end:
        kind, value = tokens[i][0], tokens[i][1]
        if kind == SYMBOL and value in OPENERS:
            depth += 1
        elif kind == SYMBOL and value in CLOSERS:
            depth -= 1
            if depth <= 0:
                return i + 1
        i += 1
    return end


def _group_binders(tokens, i, end, into):
    """Add the names bound by the bracket group at `i`; return the index after it."""
    opener, stop = tokens[i][1], _skip_group(tokens, i, end)
    inner = tokens[i + 1:stop - 1]
    colon = next((n for n, t in enumerate(inner) if t[1] == ":"), None)
    if colon is not None or opener in {"(", "{", "⦃"}:
        for token in inner[:colon]:
            if token[0] == IDENT and "." not in token[1] and token[1] != "_":
                into.add(token[1])
            elif token[1] in OPENERS or token[1] == ":=":
                break
    return stop


def _signature_binders(tokens, i, end, into):
    while i < end and tokens[i][1] in {"(", "{", "[", "⦃"}:
        i = _group_binders(tokens, i, end, into)
    return i


def _local_binders(tokens, start, end, into):
    """Collect names a declaration binds; a coarse guard against mistaking locals for globals."""
    for i in range(start, end):
        kind, value, _, line, _, first = tokens[i]
        if value == "|" and first:
            arm = []
            for token in tokens[i + 1:end]:
                if token[1] in {"=>", "↦"} or token[3] != line:
                    break
                if token[0] == IDENT and "." not in token[1] and token[1] != "_":
                    arm.append(token[1])
            into.update(arm[1:] if len(arm) > 1 else arm)
            continue
        if value not in BINDER_KEYWORDS or kind == STRING:
            continue
        j, depth = i + 1, 0
        while j < end:
            kind, value, _, here, *_ = tokens[j]
            if depth == 0 and here != line:
                break
            if kind == SYMBOL and value in OPENERS:
                depth += 1
            elif kind == SYMBOL and value in CLOSERS:
                depth -= 1
                if depth < 0:
                    break
            elif depth == 0 and value in BINDER_STOPS:
                break
            elif depth and value == ":":
                while j + 1 < end and depth:
                    j += 1
                    if tokens[j][0] == SYMBOL and tokens[j][1] in OPENERS:
                        depth += 1
                    elif tokens[j][0] == SYMBOL and tokens[j][1] in CLOSERS:
                        depth -= 1
            elif kind == IDENT and "." not in value and value != "_":
                into.add(value)
            j += 1


def _signature_stop(tokens, i, end, kind):
    """Find where a statement stops: `:=`, `by`, `where`, or the first alternative."""
    depth = 0
    while i < end:
        token_kind, value, _, _, _, first = tokens[i]
        if token_kind == SYMBOL and value in OPENERS:
            depth += 1
        elif token_kind == SYMBOL and value in CLOSERS:
            depth -= 1
        elif not depth:
            if value in {":=", "where", "by"} or (value == "deriving" and token_kind == IDENT):
                return i
            if value == "|" and (kind == "inductive" or (first and _is_alternative(tokens, i, end))):
                return i
        i += 1
    return end


def _is_alternative(tokens, i, end):
    """`| 0 => x` opens an alternative; `|x| ≤ 1 := …` continues a type."""
    depth = 0
    for j in range(i + 1, end):
        kind, value = tokens[j][0], tokens[j][1]
        if kind == SYMBOL and value in OPENERS:
            depth += 1
        elif kind == SYMBOL and value in CLOSERS:
            depth -= 1
        elif not depth and value in {"=>", ":="}:
            return value == "=>"
    return False


def _structure_fields(tokens, i, end):
    """Name, line and docstring of each field after a structure's `where` or `:=`."""
    if i + 1 < end and tokens[i + 1][1] == "::":
        i += 2
    elif i + 2 < end and tokens[i + 1][1] in MODIFIERS and tokens[i + 2][1] == "::":
        i += 3
    fields, column, docstring = [], None, None
    while i < end:
        kind, value, _, line, here, first = tokens[i]
        if kind == IDENT and value == "deriving":
            break
        if kind == DOC:
            docstring, i = value, i + 1
            continue
        if value == "@[":
            i = _skip_group(tokens, i, end)
            continue
        if kind == IDENT and value in MODIFIERS:
            i += 1
            continue
        if value in {"(", "{", "["}:
            names = set()
            stop = _group_binders(tokens, i, end, names)
            fields.extend((name, line, docstring, stop) for name in sorted(names))
            docstring, i = None, stop
            continue
        if kind == IDENT and (column is None or (first and here == column) or column == here):
            column = here if column is None else column
            names, j = [], i
            while j < end and tokens[j][0] == IDENT and tokens[j][3] == line:
                names.append(tokens[j][1])
                j += 1
            depth = 0
            while j < end:
                token = tokens[j]
                if not depth and ((token[5] and (token[4] <= column or token[0] == DOC))
                                  or (token[0] == IDENT and token[1] == "deriving")):
                    break
                if token[0] == SYMBOL and token[1] in OPENERS:
                    depth += 1
                elif token[0] == SYMBOL and token[1] in CLOSERS:
                    depth -= 1
                j += 1
            fields.extend((name, line, docstring, j) for name in names)
            docstring, i = None, j
            continue
        i += 1
    return fields


def _constructors(tokens, i, end):
    rows, depth, docstring = [], 0, None
    while i < end:
        kind, value = tokens[i][0], tokens[i][1]
        if kind == SYMBOL and value in OPENERS:
            depth += 1
        elif kind == SYMBOL and value in CLOSERS:
            depth -= 1
        elif kind == DOC:
            docstring = value
        elif not depth and value == "|":
            name = next((t for t in tokens[i + 1:min(i + 3, end)] if t[0] == IDENT), None)
            doc = tokens[i + 1][1] if i + 1 < end and tokens[i + 1][0] == DOC else docstring
            if name is not None:
                rows.append((name[1], name[3], doc, i))
            docstring = None
        i += 1
    ends = [row[3] for row in rows[1:]] + [end]
    return [(name, line, doc, stop) for (name, line, doc, _), stop in zip(rows, ends)]


def _where_declarations(tokens, i, end, column):
    """Auxiliary declarations after a body's `where`: `aux (x) : T := …`."""
    depth, opening = 0, None
    for j in range(i, end):
        kind, value, _, line, _, first = tokens[j]
        if kind == SYMBOL and value in OPENERS:
            depth += 1
        elif kind == SYMBOL and value in CLOSERS:
            depth -= 1
        elif not depth and value == "where" and kind == IDENT:
            head = j
            while head and tokens[head - 1][3] == line:
                head -= 1
            lead = tokens[head][1]
            if (first and tokens[j][4] <= column + 2) or lead not in {
                    "have", "haveI", "let", "letI", "suffices", "show", "·", "exact", "refine"}:
                opening = j
                break
    if opening is None:
        return []
    start = opening + 1
    if start >= end:
        return []
    inner = next((t[4] for t in tokens[start:end] if t[0] == IDENT), None)
    rows, j, depth = [], start, 0
    while j < end:
        token = tokens[j]
        if token[0] == SYMBOL and token[1] in OPENERS:
            depth += 1
        elif token[0] == SYMBOL and token[1] in CLOSERS:
            depth -= 1
        elif (not depth and token[0] == IDENT and token[4] == inner
              and (j == start or token[5]) and token[1] not in RESERVED):
            rows.append((token[1], token[3], j))
        j += 1
    ends = [row[2] for row in rows[1:]] + [end]
    return [(name, line, at, stop) for (name, line, at), stop in zip(rows, ends)]


def _parse_open(tokens, start, end):
    """Read `open A B`, `open A (x)`, `open A hiding x`, `open A renaming x → y`, `open scoped A`."""
    rows, i, last = [], start + 1, end
    if tokens[last - 1][1] == "in":
        last -= 1
    if i < last and tokens[i][1] == "scoped":
        return rows
    while i < last and tokens[i][0] == IDENT:
        rows.append({"namespace": tokens[i][1], "only": None, "hiding": set(), "renaming": {}})
        i += 1
        if i >= last:
            break
        value = tokens[i][1]
        if value == "(":
            rows[-1]["only"] = {t[1] for t in tokens[i + 1:_skip_group(tokens, i, last) - 1]
                                if t[0] == IDENT}
            i = _skip_group(tokens, i, last)
        elif value == "hiding":
            rows[-1]["hiding"] = {t[1] for t in tokens[i + 1:last] if t[0] == IDENT}
            break
        elif value == "renaming":
            names = [t[1] for t in tokens[i + 1:last] if t[0] == IDENT]
            rows[-1]["renaming"] = dict(zip(names[1::2], names[0::2]))
            break
    return rows


def _join(*parts):
    return ".".join(part for part in parts if part)


def _unquote(name):
    return name.replace("«", "").replace("»", "")


def parse_module(text, module, path=None):
    """Parse one module's text; declarations carry resolution context under `_` keys."""
    tokens = tokenize(text)
    imports, declarations, scopes, transient = [], [], [_Scope("root")], []
    synthetic, mutual, mutual_group = {}, 0, None
    module_digest = hashlib.sha256(module.encode()).hexdigest()[:6]

    def namespace():
        return _join(*(s.name for s in scopes if s.kind == "namespace"))

    def context():
        chain = [s.name for s in scopes if s.kind == "namespace"]
        prefixes = tuple(_join(*chain[:n]) for n in range(len(chain), 0, -1))
        opens = tuple(o for s in scopes for o in s.opens) + tuple(transient)
        return prefixes, opens, frozenset(v for s in scopes for v in s.variables)

    def add(kind, name, written, short, line, end_line, signature_end, docstring, flags, extra=None):
        name = name.removeprefix("_root_.")
        row = {"name": name, "short": short, "written": written, "kind": kind,
               "private": "private" in flags, "protected": "protected" in flags,
               "noncomputable": "noncomputable" in flags, "line": line,
               "signature_end_line": signature_end, "end_line": end_line,
               "doc": docstring, "namespace": name.rpartition(".")[0]}
        row.update(extra or {})
        declarations.append(row)
        return row

    commands = _commands(tokens)
    for start, head, end in commands:
        value = tokens[head][1]
        if tokens[head][0] != IDENT or value in {"attribute", "universe"} \
                or value in HARD_COMMANDS - {"namespace", "section", "end", "mutual", "import"}:
            if tokens[end - 1][1] != "in":
                transient.clear()
            continue
        if value == "import":
            imports.extend(t[1] for t in tokens[head + 1:end] if t[0] == IDENT)
        elif value == "namespace":
            for part in _unquote(tokens[head + 1][1]).split(".") if head + 1 < end else ():
                scopes.append(_Scope("namespace", part))
        elif value == "section":
            flags, _ = _modifiers(tokens, start, head)
            named = head + 1 < end and tokens[head + 1][0] == IDENT
            parts = _unquote(tokens[head + 1][1]).split(".") if named else [""]
            for part in parts:
                scopes.append(_Scope("section", part, "noncomputable" in flags))
        elif value == "mutual":
            mutual += 1
            mutual_group = mutual
            scopes.append(_Scope("mutual"))
        elif value == "end":
            named = head + 1 < end and tokens[head + 1][0] == IDENT
            count = len(tokens[head + 1][1].split(".")) if named else 1
            for _ in range(count):
                if len(scopes) > 1:
                    if scopes.pop().kind == "mutual":
                        mutual_group = None
        elif value == "open":
            rows = _parse_open(tokens, head, end)
            if tokens[end - 1][1] == "in":
                transient.extend(rows)
                continue
            scopes[-1].opens.extend(rows)
        elif value == "variable":
            _signature_binders(tokens, head + 1, end, scopes[-1].variables)
        elif value in DECLARATION_KEYWORDS:
            kind = {"irreducible_def": "def"}.get(value, value)
            flags, docstring = _modifiers(tokens, start, head)
            i = head + 1
            if value == "class" and i < end and tokens[i][1] in {"inductive", "abbrev"}:
                i += 1
            if value == "instance" and i < end and tokens[i][1] == "(" \
                    and i + 1 < end and tokens[i + 1][1] == "priority":
                i = _skip_group(tokens, i, end)
            named = (i < end and tokens[i][0] == IDENT and tokens[i][1] not in {"extends"}
                     and value != "example")
            written = _unquote(tokens[i][1]) if named else None
            name_end = i + 1 if named else i
            stop = _signature_stop(tokens, name_end, end, kind)
            signature_end = tokens[stop - 1][3] if stop > head else tokens[head][3]
            start_token = next((n for n in range(start, head + 1) if tokens[n][0] != DOC), head)
            bound = set()
            _signature_binders(tokens, name_end, stop, bound)
            if value == "example":
                transient.clear()
                continue
            if named:
                base = _join("" if written.startswith("_root_.") else namespace(), written)
                extra = {}
            else:
                hashed = hashlib.sha256(" ".join(t[1] for t in tokens[name_end:stop]).encode()).hexdigest()[:8]
                synthetic[hashed] = synthetic.get(hashed, 0) + 1
                suffix = f"_{synthetic[hashed]}" if synthetic[hashed] > 1 else ""
                written = f"inst_{module_digest}_{hashed}{suffix}"
                base = _join(namespace(), written)
                extra = {"synthetic": True}
            if any(scope.noncomputable for scope in scopes):
                extra["noncomputable_section"] = True
            if mutual_group:
                extra["_mutual"] = mutual_group
            base = base.removeprefix("_root_.")
            end_line = tokens[end - 1][3]
            row = add(kind, base, written, base.rpartition(".")[2], tokens[start_token][3], end_line,
                      signature_end, docstring, flags, extra)
            prefixes, opens, variables = context()
            row.update(_scope=(prefixes, opens), _tokens=(tokens, name_end, end))
            children = []
            if kind in {"structure", "class"} and stop < end and tokens[stop][1] in {"where", ":="}:
                for field, line, doc, stop_at in _structure_fields(tokens, stop + 1, end):
                    bound.add(field)
                    children.append(("def", field, line, doc, tokens[min(stop_at, end) - 1][3]))
            elif kind == "inductive":
                for ctor, line, doc, stop_at in _constructors(tokens, stop, end):
                    children.append(("def", ctor, line, doc, tokens[stop_at - 1][3]))
            elif tokens[stop][1] != "where" if stop < end else False:
                for aux, line, at, stop_at in _where_declarations(tokens, stop, end, tokens[head][4]):
                    children.append(("def", aux, line, None, tokens[stop_at - 1][3]))
            for child_kind, short, line, doc, last in children:
                child_short = _unquote(short)
                add(child_kind, _join(base, child_short), child_short, child_short, line, last, line,
                    doc, flags & {"private"}, {"parent": base})
            row["_bound"] = bound | variables
        if tokens[end - 1][1] != "in":
            transient.clear()
    return {"name": module, **({"path": path} if path else {}), "imports": imports,
            "declarations": declarations}


class _Resolver:
    """Names visible from one module, with Lean's namespace and `open` search order."""

    def __init__(self, modules):
        self.by_name, self.by_short = {}, {}
        for module in modules:
            for row in module["declarations"]:
                row["module"] = module["name"]
                self.by_name.setdefault(row["name"], []).append(row)
                self.by_short.setdefault(row["short"], []).append(row)
        names = {module["name"]: module for module in modules}
        self.visible = {}

        def reach(name):
            if name not in self.visible:
                self.visible[name] = seen = {name}
                for dependency in names[name]["imports"]:
                    if dependency in names:
                        seen |= reach(dependency)
            return self.visible[name]

        for module in modules:
            reach(module["name"])

    def _visible(self, name, user, qualified):
        rows = []
        for row in self.by_name.get(name, ()):
            module = row["module"]
            if module == user["module"]:
                if row["line"] > user["end_line"] and not (
                        "_mutual" in user and row.get("_mutual") == user["_mutual"]):
                    continue
            elif module not in self.visible[user["module"]] or row["private"]:
                continue
            if row["protected"] and not qualified:
                continue
            rows.append(row)
        return rows

    def lookup(self, name, user):
        if name.startswith("_root_."):
            return self._visible(name[7:], user, True)
        short = "." not in name
        prefixes, opens = user["_scope"]
        own = user["name"]
        chain = [own, own.rpartition(".")[0], *prefixes]
        for prefix in chain:
            if prefix and (found := self._visible(f"{prefix}.{name}", user, not short)):
                return found
        found = list(self._visible(name, user, True))
        for row in opens:
            target = row["renaming"].get(name, name)
            if (row["only"] is not None and name not in row["only"]) or name in row["hiding"]:
                continue
            for prefix in ("", *chain):
                found += self._visible(_join(prefix, row["namespace"], target), user, not short)
        return found

    def field(self, name, user):
        """Generalized field notation resolves only to a name unique in the whole index."""
        rows = self.by_short.get(name, ())
        if len(rows) != 1 or name in AMBIENT_FIELDS or rows[0] is user:
            return []
        module = rows[0]["module"]
        if module != user["module"] and (module not in self.visible[user["module"]] or rows[0]["private"]):
            return []
        return [rows[0]]

    def resolve(self, identifier, user):
        if identifier.startswith("."):
            return self.field(_unquote(identifier).rpartition(".")[2], user)
        parts = _unquote(identifier).split(".")
        if parts[0] in user["_bound"]:
            return self.field(parts[-1], user) if len(parts) > 1 else []
        renamed = {name for row in user["_scope"][1] for name in row["renaming"]}
        for size in range(len(parts), 0, -1):
            if parts[size - 1] not in self.by_short and parts[size - 1] not in renamed:
                continue
            found = self.lookup(".".join(parts[:size]), user)
            if found:
                return found + (self.field(parts[-1], user) if size < len(parts) else [])
        if len(parts) > 1 and not parts[0][0].isupper():
            return self.field(parts[-1], user)
        return []


def _uses(declaration, resolver):
    tokens, start, end = declaration["_tokens"]
    _local_binders(tokens, start, end, declaration["_bound"])
    seen, found = set(), {}
    for i in range(start, end):
        kind, value = tokens[i][0], tokens[i][1]
        if kind != IDENT or value in RESERVED or value in seen:
            continue
        if i + 1 < end and tokens[i + 1][1] == ":=" and "." not in value:
            continue  # a named argument, field assignment or local definition
        seen.add(value)
        for row in resolver.resolve(value, declaration):
            if row is not declaration:
                found[(row["name"], row["module"])] = row
    return found


def _module_name(relative):
    return ".".join(relative.with_suffix("").parts)


def _lock(tree, explicit=None):
    if explicit is not None:
        return read_json(explicit)
    for parent in tree.resolve().parents[:4]:
        candidate = parent / "source-lock.json"
        if candidate.is_file():
            return read_json(candidate)
    return None


def _source_details(tree, lock):
    toolchain = tree / "lean-toolchain"
    details = {"revision": None, "base_url": None,
               "toolchain": toolchain.read_text().strip() if toolchain.is_file() else None}
    if lock:
        prefix = "lean/" if any(row.get("upstream_path", "").startswith("lean/")
                                for row in lock.get("files", ())) else ""
        details["revision"] = lock["revision"]
        details["base_url"] = f"{lock['repository']}/blob/{lock['revision']}/{prefix}"
    return details


def build_index(tree, *, lock=None, extraction=()):
    """Build the sidecar for one Lean tree; the result is deterministic for its bytes."""
    tree = Path(tree)
    if not tree.is_dir():
        raise ContractError(f"Lean tree is not a directory: {tree}")
    modules = []
    for root in ROOTS:
        for file in sorted((tree / root).rglob("*.lean")):
            relative = file.relative_to(tree)
            raw = file.read_bytes()
            module = parse_module(raw.decode("utf-8"), _module_name(relative), relative.as_posix())
            module.update(sha256=digest(raw), source=raw.decode("utf-8"),
                          lines=raw.count(b"\n") + (not raw.endswith(b"\n") and bool(raw)))
            modules.append(module)
    if not modules:
        raise ContractError(f"Lean tree has no modules under {' or '.join(ROOTS)}: {tree}")
    resolver = _Resolver(modules)
    edges, reverse = 0, {}
    for module in modules:
        for row in module["declarations"]:
            found = _uses(row, resolver) if "_tokens" in row else {}
            row["uses"] = sorted(key[0] for key in found)
            row["dependency_source"] = "source_text"
            ambiguous = {name: other for name, other in found if len(resolver.by_name[name]) > 1}
            if ambiguous:
                row["uses_modules"] = dict(sorted(ambiguous.items()))
            for target in found.values():
                reverse.setdefault(id(target), []).append(row["name"])
            edges += len(found)
    for module in modules:
        for row in module["declarations"]:
            row["used_by"] = sorted(set(reverse.get(id(row), ())))
            for key in [key for key in row if key.startswith("_")]:
                del row[key]
    index = {"schema_version": INDEX_SCHEMA_VERSION, "dependency_source": "source_text",
             **_source_details(tree, _lock(tree, lock)),
             "dependency_note": ("Read from source text, not elaborated. Names reached through "
                                 "notation, tactics or elaboration are absent, and a shadowed "
                                 "name can appear as a dependency."),
             "modules": modules}
    for report in extraction:
        apply_extraction(index, report)
    return index


def _clean_name(name):
    match = re.fullmatch(r"_private\.[^.].*?\.0\.(.*)", name)
    return match.group(1) if match else name


def apply_extraction(index, report):
    """Replace text dependencies with elaborated ones for declarations the report covers."""
    if not isinstance(report, dict) or not isinstance(report.get("declarations"), list):
        raise ContractError("extraction report requires a declarations array")
    if report.get("evidence_kind") != "elaborated_expression_dependencies":
        raise ContractError("extraction report does not record elaborated dependencies")
    by_name, by_line = {}, {}
    for module in index["modules"]:
        for row in module["declarations"]:
            row["module"] = module["name"]
            by_name.setdefault(row["name"], []).append(row)
            by_line[(module["name"], row["line"])] = row
    covered = unmatched = 0
    for entry in report["declarations"]:
        name, source = _clean_name(entry["name"]), entry.get("source") or {}
        if GENERATED.search(name):
            continue
        rows = by_name.get(name, ())
        if len(rows) > 1:
            rows = [row for row in rows if row["module"] == source.get("module")] or rows
        row = rows[0] if rows else by_line.get((source.get("module"), source.get("line")))
        if row is None:
            unmatched += 1
            continue
        uses = set()
        for field in ("type_dependencies", "value_dependencies", "structural_dependencies"):
            uses.update(_clean_name(value) for value in entry.get(field, ()))
        row["uses"] = sorted(value for value in uses if value in by_name and value != row["name"]
                             and not GENERATED.search(value))
        row["dependency_source"] = "elaborated"
        row.pop("uses_modules", None)
        covered += 1
    reverse = {}
    for module in index["modules"]:
        for row in module["declarations"]:
            del row["module"]
            for name in row["uses"]:
                reverse.setdefault(name, set()).add(row["name"])
    for module in index["modules"]:
        for row in module["declarations"]:
            row["used_by"] = sorted(reverse.get(row["name"], ()))
    runs = index.setdefault("extraction", {"reports": [], "elaborated_declarations": 0, "unmatched": 0})
    runs["reports"].append(digest(canonical(report)))
    runs["unmatched"] += unmatched
    runs["elaborated_declarations"] = sum(row["dependency_source"] == "elaborated"
                                          for module in index["modules"]
                                          for row in module["declarations"])
    return index


def canonical(value):
    """Canonical UTF-8 JSON, the bytes a sidecar's hash binds."""
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"),
                      allow_nan=False).encode("utf-8")


def modules_view(index):
    """Everything about the tree except source text and per-declaration rows."""
    folders = {}
    for module in index["modules"]:
        folder = module["path"].rpartition("/")[0]
        folders.setdefault(folder, []).append(
            {"module": module["name"], "path": module["path"], "lines": module["lines"],
             "declarations": len(module["declarations"]), "sha256": module["sha256"]})
    return {"revision": index["revision"], "base_url": index["base_url"],
            "toolchain": index["toolchain"], "dependency_source": index["dependency_source"],
            "dependency_note": index["dependency_note"],
            **({"extraction": index["extraction"]} if "extraction" in index else {}),
            "counts": counts(index),
            "folders": [{"path": path, "modules": folders[path]} for path in sorted(folders)]}


def names_view(index):
    """One compact row per declaration; module numbers index `modules`."""
    return {"modules": [module["name"] for module in index["modules"]],
            "names": [[row["name"], row["kind"], number, row["line"], row["end_line"]]
                      for number, module in enumerate(index["modules"])
                      for row in module["declarations"]]}


def module_view(index, name):
    """One module with its source and declarations, or None."""
    module = next((row for row in index["modules"] if row["name"] == name), None)
    if module is None:
        return None
    return {"module": module["name"],
            **{key: module[key] for key in ("path", "sha256", "imports", "source", "declarations")}}


def counts(index):
    """Flat totals: modules, declarations, edges, members and one entry per kind."""
    totals, edges, members = {}, 0, 0
    for module in index["modules"]:
        for row in module["declarations"]:
            totals[row["kind"]] = totals.get(row["kind"], 0) + 1
            edges += len(row["uses"])
            members += "parent" in row
    return {"modules": len(index["modules"]), "declarations": sum(totals.values()),
            "edges": edges, "members": members, **dict(sorted(totals.items()))}


def load_index(path, *, lock=None):
    """Read a prebuilt JSON index, or build one from a Lean tree."""
    path = Path(path)
    if path.is_dir():
        return build_index(path, lock=lock)
    index = read_json(path)
    if not isinstance(index, dict) or index.get("schema_version") != INDEX_SCHEMA_VERSION \
            or not isinstance(index.get("modules"), list):
        raise ContractError(f"not a Lean index: {path}")
    return index


def write_index(index, out):
    """Write one JSON file, or the same split views the web routes serve."""
    out = Path(out)
    if out.exists() and (out.is_file() or any(out.iterdir())):
        raise ContractError("output already exists")
    if out.suffix == ".json":
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_bytes(canonical(index))
        return
    (out / "module").mkdir(parents=True)
    (out / "modules.json").write_bytes(canonical(modules_view(index)))
    (out / "names.json").write_bytes(canonical(names_view(index)))
    for module in index["modules"]:
        (out / "module" / f"{module['name']}.json").write_bytes(
            canonical(module_view(index, module["name"])))

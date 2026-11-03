"""Maintain the packaged register rules.

The rule file, ``src/lean_exposition/resources/register/rules.json``, is the
source of truth and is edited by hand. This script checks it and re-runs the
literature test that each rule's ``probe`` describes.

  python scripts/register_rules.py validate
      Structural checks (ids, scopes, limits, specimen length and damage,
      detector features, no local paths) and a per-rule summary.

  python scripts/register_rules.py domain-test --field NAME CORPUS_DIR CITATIONS_JSON [--field ...]
      For each field, search the cited papers under CORPUS_DIR (a directory of
      paper folders, each with an ``extracted.md``, or of .md/.tex files) for the
      move each rule prescribes, and print whether it holds with up to two clean
      candidate specimens and their locators. CITATIONS_JSON maps each paper's
      folder name to the citation printed beside its specimens; papers not in
      the map are skipped. Nothing is written: a reviewer reads each candidate
      in its source before copying it into ``specimens`` and ``domain_test``.

Corpora of other people's papers stay outside the repository.
"""
from __future__ import annotations

import argparse
import json
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "src"))
from lean_exposition import register  # noqa: E402

RULES = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "src", "lean_exposition", "resources",
                     "register", "rules.json")


def cmd_validate(_args) -> int:
    data = register.load_rules(RULES)
    counts = register.validate_rules(data)
    print(json.dumps(counts, indent=1))
    for rule in data["rules"]:
        holds = {k: v["holds"] for k, v in rule.get("domain_test", {}).items()}
        print("%s %-9s %-26s specimens=%-3d instances=%-3d %s" % (
            rule["id"], rule["status"], ",".join(rule["scopes"]), len(rule["specimens"]),
            len(rule.get("instances", [])), " ".join("%s=%s" % (k, "yes" if v else "NO") for k, v in holds.items())))
    return 0


def cmd_domain_test(args) -> int:
    data = register.load_rules(RULES)
    report = {}
    for name, corpus, citations_path in args.field:
        with open(citations_path, encoding="utf-8") as fh:
            citations = json.load(fh)
        paths = [os.path.join(corpus, entry) for entry in sorted(os.listdir(corpus))]
        cited = [p for p in register.expand_paths(paths) if register._label(p) in citations]
        if not cited:
            raise SystemExit("no cited papers found under %s" % corpus)
        profile = register.build_profile(cited, name=name)
        report[name] = {rule["id"]: register.probe_rule(rule, cited, citations, profile=profile)
                        for rule in data["rules"]}
    print(json.dumps(report, indent=1, ensure_ascii=False))
    return 0


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    commands = parser.add_subparsers(dest="command", required=True)
    commands.add_parser("validate").set_defaults(func=cmd_validate)
    test = commands.add_parser("domain-test")
    test.add_argument("--field", nargs=3, action="append", required=True, metavar=("NAME", "CORPUS_DIR", "CITATIONS_JSON"))
    test.set_defaults(func=cmd_domain_test)
    args = parser.parse_args(argv)
    return args.func(args)


if __name__ == "__main__":
    raise SystemExit(main())

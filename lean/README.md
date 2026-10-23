The executable extraction template is packaged once at
[`src/lean_exposition/resources/lean/Extract.lean`](../src/lean_exposition/resources/lean/Extract.lean).
Python loads it with `importlib.resources`, including from an installed wheel.

It traverses elaborated constant expressions and explicitly records where
the requested module boundary or declaration limit stops traversal. See
[`docs/verification.md`](../docs/verification.md) for commands and limits.

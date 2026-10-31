# Record alignment

The evidence graph says which records an account uses. Its passages are whole
blocks, sometimes whole sections, so they cannot answer the question a reader
asks beside the argument map: *where exactly is this result stated, in Lean and
in each paper?* The record alignment answers that question.

It is an authored sidecar. It adds no record, edge or evidence to the graph and
changes no bundle hash. Every row is a pointer into pinned bytes, so the builder
can check that it still lands where it was written.

## The authored files

`examples/qaoa-sk/alignment/*.json`. Each file:

```json
{
  "schema_version": "1.0",
  "records": {
    "support.moment_saturation": {
      "short": "Both moments from full contact",
      "lean": [
        {
          "file": "OAI/Probability/SKSupport/Main.lean",
          "name": "minimizer_full_support_actual",
          "relation": "contains",
          "note": "Its last clause gives both identities for the constructed diffusion."
        }
      ],
      "statements": [
        {
          "paper": "short",
          "role": "statement",
          "from": "For the solution of the displayed SDE and every",
          "to": "\\mathbb E[a(t,X_t)^2]=1.\n$$"
        }
      ]
    }
  }
}
```

### `short`

A title of one to six plain words for tiles where the full label cannot fit.
Keep it faithful: it may shorten the label, never strengthen it.

### `lean`

Declarations in the vendored tree `examples/qaoa-sk/upstream/lean`, most direct
first. `file` is relative to that tree. `name` is the name as written after the
declaration keyword, for example `full_support`; the builder resolves the fully
qualified name from the namespaces around it.

| `relation` | Meaning, as the site says it |
| --- | --- |
| `states` | This declaration states the record's claim. Model details may differ; say how in `note`. |
| `contains` | This declaration is stronger or wider, and the record's claim is one of its parts. |
| `part` | This declaration states one part of the record's claim. |
| `proof` | This declaration carries the proof step the record describes, in a different form. |
| `defines` | This declaration defines the object the record is about. |

`note` is at most 25 words of plain English and says what differs or which part
applies. A link says where a reader should look. It is not a check that the two
statements are equivalent, and the site never presents it as one.

A `contains` or `part` row may add `clause`, the shortest span of the
declaration's own statement that is the record's claim, copied byte for byte so
the site can highlight it. When that span lives in the body of a definition named
by the statement, also give that definition as `clause_file` and `clause_name`.

### `statements`

Where each paper gives the record. `from` and `to` are exact substrings of the
paper's Markdown: the slice runs from the start of `from` to the end of the first
`to` after it. Add `"after": "<exact text>"` when `from` alone is not unique; the
search for `from` then starts after that text.

Select the words that carry the result. Keep a theorem whole, and keep a display
formula with the sentence that introduces it. A slice must keep its `$` and `$$`
balanced and stay under 1,800 characters.

| `role` | Meaning |
| --- | --- |
| `statement` | The paper states the result here. |
| `definition` | The paper defines this object here. |
| `explanation` | The paper explains the result in words or by a calculation around it. |
| `derivation` | The paper carries out the main step of its proof here. |
| `example` | The paper works an example of it here. |
| `mention` | The paper names it in passing here and gives nothing more. |

## The dictionary

`examples/qaoa-sk/alignment/dictionary.json` tells a reader of Lean what each
central name means in the papers:

```json
{
  "schema_version": "1.0",
  "terms": [
    {
      "file": "OAI/Probability/SKSupport/Model.lean",
      "name": "parisi",
      "tex": "\\mathcal P(\\gamma)",
      "words": "The Parisi functional of the order parameter.",
      "paper": "short",
      "from": "The Parisi functional $\\mathcal P(\\gamma)$ is defined using",
      "to": "treated as\ntime in the equation."
    }
  ]
}
```

## Checking it

`lean-exposition check-alignment examples/qaoa-sk/alignment` resolves every row
against the Lean index and the three papers and fails on a missing record, a
missing declaration, an unresolved or ambiguous quotation, unbalanced mathematics
or an oversized slice. A pass means the pointers land. It says nothing about
whether the mathematics matches: that remains a reading, recorded here as authored.

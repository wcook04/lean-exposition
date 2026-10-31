# Record alignment

The evidence graph says which records an account uses. Its passages are whole
blocks, sometimes whole sections, so they cannot answer the question a reader
asks beside the argument map: *where exactly is this result stated, in Lean and
in each paper?* The record alignment answers that question.

It is an authored sidecar. It adds no record, edge or evidence to the graph and
changes no bundle hash. Every row is a pointer into pinned bytes, so the builder
can check that it still lands where it was written.

## The authored files

`examples/qaoa-sk/alignment/*.json`. Each batch file:

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

Each resolved row adds `lines`, its first and last line inside that declaration:
the lines of the `clause` when it sits there, otherwise the declaration's statement.
A theorem's statement runs from `line` to `signature_end_line`, and `proof_lines`
gives the rest where the proof runs past that line. A definition, structure or
instance is all statement: its body is part of what it says, so `lines` is the whole
declaration and it has no `proof_lines`. When the clause lives in another definition,
`lines` stays on the row's own declaration and `clause_in`, `clause_module` and
`clause_lines` say where the clause is. A quotation found in both statement and proof
means the one in the statement.

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

### `lean` on a statement

A record's `lean` rows cover everything the record means. A statement can say which
part of that Lean this one slice means:

```json
{
  "paper": "short",
  "role": "statement",
  "from": "For the solution of the displayed SDE and every",
  "to": "\\mathbb E[a(t,X_t)^2]=1.\n$$",
  "lean": [
    {
      "name": "OAI.ZeroTemperatureSK.minimizer_full_support_actual",
      "clause": "squareMoment W γ (diffusion W γ) t=t ∧ curvatureMoment W γ t=1",
      "note": "The two identities, for the constructed diffusion."
    }
  ]
}
```

| Field | Meaning |
| --- | --- |
| `name` | Required. Any declaration in the index, on this record or not. Give the full name, or an ending that only one declaration has. |
| `file` | Which file, when a name exists in two (the Comparator challenge restates some). Not needed when the record already lists one of them. |
| `lines` | `[first, last]`, both inclusive. They must lie inside the declaration, and may lie in its proof: a `derivation` can point at the step it describes. |
| `clause` | Text copied byte for byte from the declaration. With `lines` it must land inside them. A quotation found more than once needs `lines` to choose, unless only one place is in the statement. |
| `note` | At most 25 words on what this slice means here. A name the record lists keeps the record's note if this is absent. |
| `relation` | One of the relations above, for a name the record does not list. A name the record lists keeps its relation. |

With only `name`, a declaration on the record keeps its row, and any other declaration
points at its whole statement.

A tie carries the first row's `relation`, so the reader can say "Lean covers part of this" for
`part` and "Has Lean" otherwise, and a statement with `"lean": []` carries its `note`, which the
reader shows as written where it would have said why there is no Lean.

Leaving `lean` out shows the record's rows, which is a fallback: those rows are about the
record, and nobody has said they are what this slice means. `"lean": []` says this slice
has no Lean of its own. Use it for a passage the Lean does not contain, such as an argument
it takes another way or a computation it leaves out, so that the reader is not sent to
the record's Lean as if it stated this text.

Each resolved statement carries `at`, its address `b<start_byte>-<end_byte>`, its `lean`
list, and `lean_source`. That is `"statement"` when the slice said what it means, including
`[]`, and `"record"` when it shows the record's rows.

### Add ties without touching the batch files

`ties-<paper>.json`, where `<paper>` is `long`, `short` or `expository`, adds statements
to records already aligned in a batch file. Here is a working `ties-short.json`:

```json
{
  "schema": 1,
  "statements": [
    {
      "record": "support.moment_saturation",
      "paper": "short",
      "role": "derivation",
      "from": "contact gives $q(t)=t$, and differentiation",
      "to": "including the right-hand value at zero.",
      "lean": [
        {
          "name": "OAI.ZeroTemperatureSK.minimizer_full_support_actual",
          "lines": [30, 33],
          "note": "Differentiating full contact gives the unit curvature moment."
        }
      ],
      "note": "The last step of the proof, in Lean and in the paper."
    }
  ]
}
```

`record`, `paper`, `role`, `from` and `to` are required. `after`, `lean` and `note` mean
what they mean on any statement, and the same rules for `from`, `to` and the size of a
slice apply. These files load after every batch file, and `paper` must match the file
name. A record that is not aligned, a quotation that does not land or a slice given twice
in the ties files is an error. A slice identical to one already on that record in a batch
file replaces it, role and note included, which is how to narrow an existing statement
without editing its file.

## Plain names

`names.json`, optional, is `{ "schema": 1, "names": { "<full declaration name>": "<plain title, two to six words>" } }`: every key must be a declaration in the index, and the title reaches `names` in `/alignment` and `plain` on Lean rows and ties.

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
missing declaration, a clause outside its declaration, lines outside a declaration,
an unresolved or ambiguous quotation, unbalanced mathematics or an oversized slice.
A pass means the pointers land. It says nothing about whether the mathematics matches:
that remains a reading, recorded here as authored.

## What a reader may conclude

An AI agent read the two and linked them. No independent mathematician has reviewed this,
and no program checks that they say the same thing. A tie says that the agent read a slice
of a paper and a piece of Lean and pointed one at the other, and that both ends still exist
in the pinned bytes.

A reader may conclude that the quoted text is in the paper at that byte range, that the
named lines are in the pinned Lean at that line range, and that an agent recorded a
connection between them, with the stated relation and note.

A reader may not conclude that the two statements are equivalent, that the Lean proves
what the paper says, that the hypotheses agree, or that a paragraph without a tie has no
Lean. Exact lines make a pointer precise. They do not make it a check. A pointer lands by
matching bytes, so a wrong pointer lands just as well as a right one. What Lean has
checked is reported separately, for each named declaration, by the verification records.

## The tie index

`ties/<stage>.json` is what a reader needs to mark one paper at first paint, without
loading the whole alignment. It holds three lists and a one-line `meaning`:

```json
{
  "segments": [[3280, 3326, [4]]],
  "ties": [
    {
      "record": "scalar.paper_admissible",
      "role": "definition",
      "lean": true,
      "from_record": true,
      "name": "OAI.ZeroTemperatureSK.OrderParameter",
      "module": "OAI.Probability.SKSupport.Model",
      "lines": [17, 22],
      "anchor": "model",
      "at": "b3122-3279"
    }
  ],
  "passages": [[1726, 5354, ["scalar.paper_admissible"], "model"]],
  "meaning": "Each tie is a pointer that landed. Whether the paper and the Lean say the same thing is a reading."
}
```

`segments` are `[start_byte, end_byte, tie indices]`, in document order, as UTF-8 byte
offsets into the exact paper. Together they cover every slice in that paper, and they
never overlap. Each one stays inside a block: a cut falls at a blank line, a passage
marker, a heading and either side of a display. A segment never starts or ends inside
`$...$`, because an end that falls there moves out to the edge of the math. A `$$`
display that a slice touches is its own segment, whole. Whitespace at the ends and
comments are left out. Math is found with the same rules as `site/src/reader/math.ts`.

Where slices overlap, a segment lists every tie, those with Lean first and then the
narrowest. So a slice can have several segments, and they all share one tie and one `at`.

A tie is one statement. `name`, `module` and `lines` come from its first Lean row, the most
direct, or from the row's `clause_lines` when its clause lives in another definition. All
three are null, and `lean` false, when the statement has no Lean, whether it said so with
`[]` or its record has none. `from_record` is true when the Lean is the record's rows
rather than the statement's own choice: a page should call those "the record's Lean" and
not imply that these lines are what the sentence means. For the rest of a tie's rows, find
the statement with the same `at` in `/alignment`.

`passages` are `[start_byte, end_byte, record ids, anchor]`: what each mapped passage
discusses, so that a paragraph with no slice can still say so. The ids are the claims and
assumptions mapped to the passage, with the records of any slice in it. They are less exact
than a tie, and nothing in the passage is claimed to state them. Dictionary terms are not
ties.

## Steps through the Lean

`/alignment` also carries `steps`, keyed like an edge (`from→to→kind`). Where a curated
support edge joins two records with Lean links, `route` is the shortest chain of names
in the source from a consumer's declaration to a prerequisite's, or null when none was
found within eight steps. A route shows where the Lean makes that use. A null route
shows nothing: the source scan misses names reached through tactics or notation, and
the site says nothing about the step in that case.

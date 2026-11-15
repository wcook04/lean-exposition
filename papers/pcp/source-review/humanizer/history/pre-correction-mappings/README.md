# Superseded passage mappings

These files are historical evidence, not current authoring inputs:

- [Long mapping](long.json)
- [Specialist mapping](short.json)
- [Exposition mapping](expository.json)
- [Captured bundle manifest](manifest.json)
- [Snapshot provenance and hashes](provenance.json)

The three mapping files were extracted byte-for-byte from ZIP
`81ce615798ddf8eb63b52a244ca9dd45584df65a26c3aff84f501269b74f9266`,
whose source graph hash was
`b7d92ed2314221ece705e8f7dfe676869f22937d64aa1ca47cb425cbee651cb0`.
Their hashes match the manifest inside that ZIP. No live canonical mapping was
read to construct this snapshot while other agents were repairing the mappings.

The package had passed structural validation. Subsequent reader review found
that some paragraph associations used broad fallback declarations or downstream
theorems rather than the source result the paragraph actually stated. For
example, exact-line characterization was associated with downstream weighted
proximity, and some Hadamard/correction passages included an unrelated
row-decoding fallback. Structural validity and matching byte hashes did not
establish mathematical correspondence.

Do not assemble a current reader from these files. The canonical manuscript
mappings and the current mapping-review record own the correction. This issue
does not change the separately accepted manuscript mathematics or PDF layout.

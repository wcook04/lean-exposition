# Descriptive register measurements

The matched sample compares the exposition’s PCP opening and Hadamard testing/correction passages with selected teaching paragraphs from Arora–Barak’s January 2007 draft. The complete exposition is context only. See literature-review.md for inspected source pages, extraction normalization and the single-sample limitation.

## matched

| Feature | Before | After | Teaching sample |
| --- | ---: | ---: | ---: |
| sent_len_mean | 12.833 | 13.126 | 20.568 |
| sent_len_cv | 0.451 | 0.463 | 0.557 |
| para_len_mean | 44.312 | 44.125 | 82.273 |
| contrast_rate | 2.149 | 1.444 | 1.200 |
| status_vocab_rate | 13.610 | 14.440 | 12.005 |
| negation_rate | 9.312 | 8.664 | 4.802 |

## whole_context

| Feature | Before | After | Teaching sample |
| --- | ---: | ---: | ---: |
| sent_len_mean | 13.600 | 14.027 | 20.568 |
| sent_len_cv | 0.447 | 0.445 | 0.557 |
| para_len_mean | 46.571 | 46.429 | 82.273 |
| contrast_rate | 1.453 | 1.168 | 1.200 |
| status_vocab_rate | 8.571 | 8.903 | 12.005 |
| negation_rate | 10.169 | 9.486 | 4.802 |

The whole-document extracted word count changed from 6,884 to 6,852. The matched-region count changed from 1,396 to 1,385. Citation additions increased the counted status vocabulary slightly; the general sentence-length variation decreased slightly while variation in the matched region increased. These directions were not optimization targets. Necessary negations remain because they exclude invalid inferences. Paragraph figures are particularly sensitive to mathematical displays and extraction segmentation; they are not a claim that the exposition should imitate the book’s paragraph lengths.

The final source was read sequentially; these measurements neither establish comprehension nor identify authorship. No research-paper prose was pooled into this numeric teaching sample.

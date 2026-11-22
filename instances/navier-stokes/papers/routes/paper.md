
<!-- passage:front -->
# Reading the proof routes

**Navier–Stokes pages:** [the paper](../navier-stokes-paper/paper.pdf) · [index by number](../navier-stokes-index/paper.md) · [specialist digest](../navier-stokes/digest.md) · [full account, part I](../navier-stokes-part-1/paper.md) · [part II](../navier-stokes-part-2/paper.md) · [part III](../navier-stokes-appendix-b/paper.md) · [what the Lean states](../navier-stokes/paper.md) · [statement files](../navier-stokes-statement-files/paper.md) · **proof routes** · [proof routes in detail](../navier-stokes-route-details/paper.md) · [library guide](../navier-stokes-library-01/paper.md) · [cell layer guide](../navier-stokes-cell-guide/paper.md) · [cell reference](../navier-stokes-cell-reference/paper.md) · [cell layer and Appendix B](../navier-stokes/cell-layer-fidelity.md) · [certificate checker](../navier-stokes/certificate-checker.md)

Original navigation guide for the authors' source at commit ad53419.
<!-- /passage:front -->

## What this guide records

<!-- passage:sec-what-this-guide-records -->

This guide follows selected statements and proofs in the supplied Navier–Stokes library at commit ad53419. The 400-entry catalogue gives source locations, plain titles and paper correspondences. Its 142 proved-by links and nineteen public forwarding links are navigation records read from source, separate from the compiled dependency graph shown beside this guide.

The classical cell theorem takes a complete cell-system condition as an input and concludes the two breakdown statements. The numerical certificate that would supply a particular instance is absent from the supplied repository.

Use a public export to find the exact conclusion, its provider to find the construction, and the named proposition to read the remaining hypotheses. A paper reference marked support locates the relevant argument; it does not assert that the whole paper theorem and the local Lean declaration are identical.
<!-- /passage:sec-what-this-guide-records -->

## 1. A profile gives a space obstruction

<!-- passage:sec-1-a-profile-gives-a-space-obstruction -->

If a smooth recurrent similarity profile satisfying the formal derivative and pressure bounds exists, then for every positive viscosity there is a smooth compactly supported divergence-free datum with no global smooth solution of uniformly bounded energy.

The formal profile premise includes spatial derivative bounds through order two and a bound on the pressure gradient. The public space predicate quantifies over a global competitor and one energy bound for all nonnegative times. It does not retain the constructed trajectory, its blow-up rate or its convergence to a chosen profile.

The quantitative construction is visible earlier: the transfer interface builds a mild trajectory from a dense data subspace and records convergence in similarity variables. Its listed proof still takes the dichotomy result as an input; the concrete assembly supplies that result.

The Fourier realization supplies the abstract evolution with a concrete interpretation as physical velocity fields. Its energy, reconstruction and regularity statements are the joins needed to interpret the abstract trajectory as a PDE solution.
<!-- /passage:sec-1-a-profile-gives-a-space-obstruction -->

## 2. A profile gives a periodic obstruction

<!-- passage:sec-2-a-profile-gives-a-periodic-obstruction -->

If a smooth recurrent similarity profile satisfying the formal bounds exists, then for every positive viscosity there is a smooth divergence-free periodic datum with no global smooth solution whose velocity remains periodic.

The exported periodic obstruction allows arbitrary smooth pressure in the excluded competitor. The moving-frame reduction preserves its original datum and makes the pressure periodic as well; it does not assert that the velocity has zero mean.

The torus construction combines localization, a right-inverse comparison, perturbation and gluing. The abstract torus assembly still names the analytic inputs it needs; the final provider supplies those inputs for the concrete realization.
<!-- /passage:sec-2-a-profile-gives-a-periodic-obstruction -->

## 3. A weak profile has two onward routes

<!-- passage:sec-3-a-weak-profile-has-two-onward-routes -->

If a weak recurrent similarity profile satisfying the formal integrability, nonzero and recurrence conditions exists, then the formal whole-space breakdown statement follows.

The direct whole-space proof turns the weak field into a mild recurrent orbit. The separate torus route first constructs a smooth decaying profile and then uses the smooth-profile periodic theorem.

The internal smoothing interface preserves the input period and isometry and represents the supplied orbit almost everywhere in space at each time. The later existential profile export hides that relationship, so a reader seeking estimates for the same selected profile should open the internal interface.
<!-- /passage:sec-3-a-weak-profile-has-two-onward-routes -->

## 4. A certificate gives a weak profile

<!-- passage:sec-4-a-certificate-gives-a-weak-profile -->

If the earlier formal certificate hypothesis holds, then a weak recurrent similarity profile exists.

If the extended formal certificate hypothesis holds, then a weak recurrent similarity profile exists.

The closed extended construction supplies the named analytic nodes to the certificate assembly. For each admissible parameter it obtains a correction by contraction, proves the needed continuity, and then finds a parameter at which the total multiplier vanishes.

The weak-profile export from a held correction existentially returns a period and fields without retaining their identity with the selected parameter and correction. Its proof constructs those witnesses, but the exported proposition does not state the equalities needed by the full near-candidate conclusion of Theorem 7.1.

The conversion to the earlier certificate data type reuses an operator carrier and fills several older fields with zero. It supplies no theorem that those converted data satisfy the earlier certificate predicate.
<!-- /passage:sec-4-a-certificate-gives-a-weak-profile -->

## 5. The cell condition supplies the analytic route

<!-- passage:sec-5-the-cell-condition-supplies-the-analytic-route -->

For any seven classical cell-data arguments satisfying the fifteen-field cell-system condition, the formal whole-space breakdown statement follows.

For the same seven classical cell-data arguments, the same fifteen-field condition also implies the formal periodic breakdown statement.

The combined classical cell theorem returns both breakdown statements under the full cell-system condition.

The closed cell analysis supplies general analytic interfaces for cells, traces, rows and tree estimates. The full input condition still contains structural, functional and quantitative obligations for the particular cell system.

The composition theorem produces an extended certificate after replacing its decay constant by a suitable real bound. A wrapper that promises a conclusion for the original certificate must justify transporting that conclusion across the change.

The classical condition lives in CellLayerSystem and has fifteen fields. The fractional condition lives in CellCert.CellSystem, has twelve fields and uses exponent 501/500. The two full names identify different hypotheses.
<!-- /passage:sec-5-the-cell-condition-supplies-the-analytic-route -->

## 6. A statement node needs its supplying proof

<!-- passage:sec-6-a-statement-node-needs-its-supplying-proof -->

A proposition definition records a statement. It does not record a later theorem that proves it. For the transfer step, the reader needs the statement, the conditional construction and the assembly that supplies the intermediate steps as separate selectable declarations.

The closed-graph interface says that each element has the required half-order derivative relation. The main certificate assembly supplies it pointwise with halfSsp_of_xbar. The physical-energy provider then takes this closed-graph interface as its premise.

A supplying theorem can return a conjunction. The embedding-norm and embedding-linearity statements use different components of the same theorem; a navigation link to that provider should keep the chosen component visible.
<!-- /passage:sec-6-a-statement-node-needs-its-supplying-proof -->

## 7. Fractional extensions have separate endpoints

<!-- passage:sec-7-fractional-extensions-have-separate-endpoints -->

The fractional profile exports concern dissipation exponents strictly between one and five quarters. Their whole-space and torus conclusions belong to a separate equation family from the classical paper route.

The fractional certificate and fractional cell-system exports are additional selected targets. Solution imports their providers alongside the classical providers, so its combined import closure should be distinguished from the import closure of an individual classical provider.

Several classical cell modules import reusable analysis from the fractional-named folders. The module map therefore separates the four fractional endpoint claims from the shared imported infrastructure.
<!-- /passage:sec-7-fractional-extensions-have-separate-endpoints -->

## 8. What these records establish

<!-- passage:sec-8-what-these-records-establish -->

Each source name, declaration line, title length, provider reference, selected endpoint and passage anchor was checked against the snapshot. These checks verify navigation metadata. Paper correspondences remain source-read judgements, and successful compilation or numerical validation requires its own matching evidence.

The wrapper inventory records nineteen existing user declarations and two absent full Theorem 1.1 target names. Wrapper paths and patch hashes stay separate from the authors’ pinned source locations.
<!-- /passage:sec-8-what-these-records-establish -->


# JSP-000400 / Erdős 496

This project formalizes Margulis's positive-parameter approximation theorem in Lean. For every positive irrational real α and every ε>0, there are positive integers x,y,z such that

|x²+y²−αz²| < ε.

The equivalent inequality |α(x²+y²)−z²|<ε is also proved. The denominator z can be required to exceed any prescribed natural number. The final declarations are `JSP400.positive_statement`, `JSP400.dual_statement`, `JSP400.erdos_496`, and `JSP400.erdos_496_large_denominator` in `FinalTheorem.lean`.

The original source is [Erdős, *Some unsolved problems* (1961)](https://users.renyi.hu/~p_erdos/1961-22.pdf), I.34, printed pp.238–239. It follows an explicit discussion of coefficients of mixed sign. The isolated sentence and the later web transcription omit α>0; the formal statement records the positive parameter required by that indefinite-form context.

The mathematical theorem is due to G. A. Margulis. The proof follows [*Indefinite quadratic forms and unipotent flows on homogeneous spaces*](https://www.impan.pl/en/publishing-house/banach-center-publications/all/23/1/106367/indefinite-quadratic-forms-and-unipotent-flows-on-homogeneous-spaces), Banach Center Publications 23 (1989), pp.399–409. The basis-reduction component uses the classical method of A. K. Lenstra, H. W. Lenstra Jr. and L. Lovász ([1982 paper](https://doi.org/10.1007/BF01457454)).

## Proof structure

- Actual real quadratic forms and determinant-one standardization connect the diagonal form to Margulis's standard form.
- The homogeneous space is the ordinary quotient SL(3,ℝ)/SL(3,ℤ). Its lattice-point sets, topology, stabilizers and compact-family bounds are proved directly.
- `MargulisLemma5`, `MargulisLemma6`, and `MargulisLemma7` prove the matrix enlargement and closure statements using explicit invariant flags, unbounded curves, compact limits, and continuous local sections. The minimal-set collision lemmas and signed orbit noncompactness supply the dynamical steps.
- `MargulisTheorem2` proves the compactness of the actual stabilizer quotient whenever the corresponding H-orbit has compact closure.
- For the diagonal irrational form, integer coefficient separation makes the integer stabilizer compact. Its real form stabilizer is noncompact, so the relevant orbit cannot have compact closure.
- `MahlerBoundedBasis` constructs a determinant-one integer basis whose matrix norm is at most 4/ε² whenever nonzero lattice vectors have norm at least ε. `MahlerCompactness` turns this into arbitrary short vectors on the orbit. The final modules produce strictly positive natural witnesses and both original approximation formulations.

The basis-reduction proof minimizes the product of the first squared column length and the first squared exterior area over actual integer changes of basis. Integer shears preserve this potential, and adjacent column swaps give the successive Gram length bounds. Every minimization and reduction step is proved in the project.

## Reproduction

Lean **4.34.0**, Mathlib commit **5ed2965256430c3649e86755f9576b54eca72435**.

```sh
lake exe cache get
python3 verify.py
```

The script builds every project module, checks the final theorems and intermediate endpoints with `#print axioms`, verifies the pinned Mathlib revision, and scans project Lean sources for unfinished proofs and added axioms. The allowed logical dependencies are `propext`, `Classical.choice`, and `Quot.sound`. `verification/manifest.json` records UTC times, the Git revision at verification, exact source hashes, and command results. The GitHub Actions workflow repeats the build and audit.

All mathematical credit belongs to the cited human authors. The Lean proof is independently written and uses Mathlib under its existing license.

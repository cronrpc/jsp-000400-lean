# JSP-000400: statement and verification evidence

## Mathematical statement

For every positive irrational real alpha and every positive real epsilon, there exist strictly positive natural numbers x, y and z such that

`|x^2 + y^2 - alpha*z^2| < epsilon`.

The project also proves the equivalent first formulation `|alpha*(x^2+y^2)-z^2| < epsilon`, and permits z to exceed any prescribed natural bound. The declarations are `JSP400.positive_statement`, `JSP400.dual_statement`, `JSP400.erdos_496` and `JSP400.erdos_496_large_denominator` in [FinalTheorem.lean](FinalTheorem.lean). The exact definitions and all hypotheses are in [Core.lean](Core.lean) and [Quantifiers.lean](Quantifiers.lean).

Erdos's [1961 original paper](https://users.renyi.hu/~p_erdos/1961-22.pdf), I.34, pp.238-239, introduces these inequalities in the context of indefinite quadratic forms with coefficients of mixed signs. This is why alpha is strictly positive here. The isolated sentence and the later transcription omit that condition. For negative alpha and positive coordinates the form cannot approach zero; this submission covers the intended indefinite-form theorem, with every positive irrational parameter.

The mathematical solution is due to G. A. Margulis. The main source is [Indefinite quadratic forms and unipotent flows on homogeneous spaces](https://www.impan.pl/en/publishing-house/banach-center-publications/all/23/1/106367/indefinite-quadratic-forms-and-unipotent-flows-on-homogeneous-spaces), Banach Center Publications 23 (1989), 399-409. The formalization proves the required homogeneous-space theorem, the arithmetic stabilizer argument, three-dimensional Mahler compactness and the conversion to positive witnesses. The lattice basis-reduction method is attributed to A. K. Lenstra, H. W. Lenstra Jr. and L. Lovasz; see the [1982 paper](https://doi.org/10.1007/BF01457454).

## Fixed source and reproduction

Independent repository: [cronrpc/jsp-000400-lean](https://github.com/cronrpc/jsp-000400-lean).

Current proof and audit commit: [`e89bad0fdcfce3c6fb9d2e3de9f35b52ffdd38cd`](https://github.com/cronrpc/jsp-000400-lean/tree/e89bad0fdcfce3c6fb9d2e3de9f35b52ffdd38cd).

Lean: `leanprover/lean4:v4.34.0`. Mathlib: `5ed2965256430c3649e86755f9576b54eca72435`. All package revisions are locked in [lake-manifest.json](lake-manifest.json).

```sh
git clone https://github.com/cronrpc/jsp-000400-lean.git
cd jsp-000400-lean
git checkout e89bad0fdcfce3c6fb9d2e3de9f35b52ffdd38cd
lake exe cache get
python3 verify.py
lake env leanchecker Core TernaryForm Quantifiers PositiveWitness StandardForm FormStabilizer UnipotentGroups SmallVectors LatticeSpace MinimalInvariant CompactRepresentatives CompactLattices CompactStabilizers DiagonalContraction UpperUnipotentCompact Shearing ShearOrbit ShearLemma6C ShearFixedSpace ShearCurves ShearFixedRays ShearNormalization ShearFlag ConnectedCompactLimits CurveTruncation BoundaryBumping ShearOrbitClosure ShearDescent ShearLemma6B2 ShearB1 ShearCentralizer ShearNormalizer NilpotentSection ShearClosureLift UpperGeneration MargulisLemma6 UpperDiagonalEscape SignedShearEscape MinimalHitting GramShear GramCurves GramDescent GramOrbitClosure GramQuotient GramHull GramTriangular GramSection GramClosureLift MargulisLemma7 PrincipalRepresentation PrincipalFixed PrincipalFlag PrincipalCurves PrincipalDescent PrincipalSection NormalizerCoordinates PrincipalClosure MargulisLemma5 MinimalCollision LatticeCollision MinimalSubsystem OrbitQuotientTopology UnipotentOneNormalizer CompactGroupQuotient CompactHOrbit AffineSubgroup AffineTranslations AffineClassification AffineMatrixBridge PositiveNormalizerQuotient DiagonalInvariance CollisionInvariant MargulisTheorem2 IrrationalIntegerStabilizer NoncompactTernaryStabilizer StandardizedQuotient NoncompactOrbit ReducedBasisBounds MahlerCompactness MahlerPotential MahlerBasisChanges MahlerGram MahlerSizeReduction MahlerDualGram MahlerBoundedBasis FinalTheorem
```

The original v1.0.0 clean local verification started with no compiled artifacts from this project. Dependencies were freshly checked out at their locked revisions and the public Mathlib cache was retrieved. `python3 verify.py` rebuilt all 86 proof modules and audited 386 named theorem endpoints. Both commands exited 0. The permitted axiom set is `propext`, `Classical.choice`, `Quot.sound`; the complete source scan found no forbidden proof commands. Exact command results, source/configuration hashes and UTC timestamps are in the manifest. Source and third-party library licenses are retained.

The dedicated Lean workflow builds this same project, replays the project modules with leanchecker and runs the axiom audit. Its results are available under [repository Actions](https://github.com/cronrpc/jsp-000400-lean/actions). The ordinary awards workflows separately check record schemas, Markdown links, generated data and history.

## Complete direct final-theorem audit

The supplemental verification on 2026-09-18 used commit `e89bad0fdcfce3c6fb9d2e3de9f35b52ffdd38cd`.
It adds the direct `#print axioms JSP400.dual_statement` report and makes
`verify.py` require separate reports for all four final declarations, both in
the audit commands and in Lean's actual output. The mathematical proofs,
Lean version and locked dependencies are unchanged.

The local build check used the existing project cache and exited 0. The fresh
audit reported **387 named endpoints**; a separate
`lake env leanchecker FinalTheorem` run exited 0. Each of the four final
declarations depends only on `propext`, `Classical.choice` and `Quot.sound`.
A negative coverage check removed the dual-statement audit line from an
isolated fixture and confirmed that verification exits nonzero before building.

The [supplemental manifest](verification/final-audit-20260918/manifest.json)
records the exact source commit, hashes and a `final_theorem_axioms` mapping
for all four declarations. The [axiom output](verification/final-audit-20260918/axioms.log),
[build output](verification/final-audit-20260918/build.log), and
[command record](verification/final-audit-20260918/local-validation.json)
preserve the actual results and timings. The original 386-endpoint release
records below remain historical evidence for their original commit.

## Original v1.0.0 archived artifacts

The original source archive is produced by `git archive` at proof commit `f9080e7480a7a1bd07df6dd8b9eacfa744e5b8f8`; no dependency cache or local research workspace is included. Published release assets identify the exact build evidence.

| Artifact | SHA-256 | Bytes |
| --- | --- | --- |
| [axioms.log](https://github.com/cronrpc/jsp-000400-lean/releases/download/v1.0.0/axioms.log) | `9c522a55b1b23c4c7f63f84f68ce1a256c3dd554b945ae1041cc9b6627ac1808` | 38248 |
| [build.log](https://github.com/cronrpc/jsp-000400-lean/releases/download/v1.0.0/build.log) | `d3083c5040423faa75c1834399785ecab14c4f9c90b7744bff77013cdb47d818` | 9153 |
| [jsp-000400-lean-source.tar.gz](https://github.com/cronrpc/jsp-000400-lean/releases/download/v1.0.0/jsp-000400-lean-source.tar.gz) | `ac0b34c947831fc6ddcae9b71b532023d7af827a026c60657e860d7a38eb8c8d` | 108692 |
| [manifest.json](https://github.com/cronrpc/jsp-000400-lean/releases/download/v1.0.0/manifest.json) | `d1e2027dcb92d0dc1f02b2984a82a5c6ca4b67dc7b10508568083b14605446e3` | 14699 |

## Review status

This package is submitted as a Lean formalization contribution. The underlying mathematical authorship remains with the cited authors. Recipient confirmation and the prize repository's designated verification remain pending. The candidate's formal review record is left for authorized reviewers; build results and internal statement checks are supplied as evidence, without replacing that record.

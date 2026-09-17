import Lake
open Lake DSL

package jsp400 where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "5ed2965256430c3649e86755f9576b54eca72435"

@[default_target]
lean_lib JSP400 where
  roots := #[`Core, `TernaryForm, `Quantifiers, `PositiveWitness,
    `StandardForm, `FormStabilizer, `UnipotentGroups, `SmallVectors,
    `LatticeSpace, `MinimalInvariant, `CompactRepresentatives,
    `CompactLattices, `CompactStabilizers, `DiagonalContraction, `UpperUnipotentCompact,
    `Shearing, `ShearOrbit, `ShearLemma6C, `ShearFixedSpace, `ShearCurves,
    `ShearFixedRays, `ShearNormalization, `ShearFlag, `ConnectedCompactLimits,
    `CurveTruncation, `BoundaryBumping, `ShearOrbitClosure, `ShearDescent, `ShearLemma6B2,
    `ShearB1, `ShearCentralizer, `ShearNormalizer, `NilpotentSection,
    `ShearClosureLift, `UpperGeneration, `MargulisLemma6, `UpperDiagonalEscape,
    `SignedShearEscape, `MinimalHitting, `GramShear, `GramCurves, `GramDescent,
    `GramOrbitClosure, `GramQuotient, `GramHull, `GramTriangular, `GramSection,
    `GramClosureLift, `MargulisLemma7,
    `PrincipalRepresentation, `PrincipalFixed, `PrincipalFlag, `PrincipalCurves, `PrincipalDescent, `PrincipalSection, `NormalizerCoordinates, `PrincipalClosure, `MargulisLemma5, `MinimalCollision, `LatticeCollision, `MinimalSubsystem, `OrbitQuotientTopology, `UnipotentOneNormalizer, `CompactGroupQuotient, `CompactHOrbit, `AffineSubgroup, `AffineTranslations, `AffineClassification, `AffineMatrixBridge, `PositiveNormalizerQuotient, `DiagonalInvariance, `CollisionInvariant, `MargulisTheorem2, `IrrationalIntegerStabilizer, `NoncompactTernaryStabilizer, `StandardizedQuotient,
    `NoncompactOrbit, `ReducedBasisBounds, `MahlerCompactness, `MahlerPotential, `MahlerBasisChanges, `MahlerGram, `MahlerSizeReduction, `MahlerDualGram, `MahlerBoundedBasis, `FinalTheorem]

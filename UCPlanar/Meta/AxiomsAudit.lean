import UCPlanar.Frozen.Unconditional.LiouvilleOfPeriodic
import UCPlanar.Frozen.Unconditional.UniformlyBounded
import UCPlanar.Frozen.Unconditional.ZeroCase
import UCPlanar.Frozen.Unconditional.PolynomialApproximation
import UCPlanar.Frozen.Unconditional.ThreeBall
import UCPlanar.Frozen.Unconditional.PeriodicLowerBound
import UCPlanar.Proved.MoserEstimate
import UCPlanar.Proved.ZeroRemark
import UCPlanar.Proved.StepOne

/-!
# Axioms audit

Building this module prints the axiom dependencies of the four main theorems of
`UCPlanar/MainTheorems.lean`.  Each must report exactly the three standard foundational axioms
of Mathlib: `propext`, `Classical.choice`, `Quot.sound`.

The unconditional forms use the proved topology and Moser estimates. The remark after
Theorem 1.3 and Step 1 of its proof are reported as well.

This file is not imported by the library root; the report runs when it is built explicitly
(`lake build UCPlanar.Meta.AxiomsAudit`), as continuous integration does on every push.
-/

#print axioms UCPlanar.liouville
#print axioms UCPlanar.uniformlyBounded
#print axioms UCPlanar.zeroCase
#print axioms UCPlanar.counterexample

#print axioms UCPlanar.Support.edgeSplitting_holds
#print axioms UCPlanar.Support.unicoherence_holds
#print axioms UCPlanar.Proved.moserEstimate
#print axioms UCPlanar.Proved.liouville_of_periodic
#print axioms UCPlanar.Proved.uniformlyBounded
#print axioms UCPlanar.Proved.zeroCase
#print axioms UCPlanar.Proved.polynomialApproximation
#print axioms UCPlanar.Proved.threeBall
#print axioms UCPlanar.Proved.periodicLowerBound
#print axioms UCPlanar.Proved.zeroCase_of_sparseShell
#print axioms UCPlanar.Proved.eq_zero_of_sparseShells
#print axioms UCPlanar.Proved.stepOne_cutVertex
#print axioms UCPlanar.Proved.stepOne_twoExits

#print axioms UCPlanar.Frozen.liouville_of_periodic
#print axioms UCPlanar.Frozen.uniformlyBounded_unconditional
#print axioms UCPlanar.Frozen.zeroCase_unconditional
#print axioms UCPlanar.Frozen.polynomialApproximation_unconditional
#print axioms UCPlanar.Frozen.threeBall_unconditional
#print axioms UCPlanar.Frozen.periodicLowerBound_unconditional

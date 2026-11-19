import UCPlanar.Proved.MoserEstimate

/-!
# Axioms audit

Building this module prints the axiom dependencies of the four main theorems of
`UCPlanar/MainTheorems.lean`.  Each must report exactly the three standard foundational axioms
of Mathlib: `propext`, `Classical.choice`, `Quot.sound`.

The unconditional forms use the proved topology and Moser estimates.

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

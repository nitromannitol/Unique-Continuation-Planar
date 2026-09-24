import Audit.Support.Statements
import Audit.Liouville.Solution
import Audit.UniformlyBounded.Solution
import Audit.ZeroCase.Solution
import Audit.Counterexample.Solution

/-!
# Statement regression for the comparator solutions

For each audited theorem, checks that the type of the solution theorem is
exactly the proposition elaborated in the challenge environment
(`Audit/Support/Statements.lean`), and that it mentions no constant of the
repository namespace `UCPlanar` or of the libraries `LatticeProb` and
`Schoenflies`.  Building this module prints one line per theorem; any mismatch
is an error.  This is a local proxy for the statement-identity part of
`leanprover/comparator`.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (thm, stmt) in [
    (`UCPlanarAudit.liouville, `UCPlanarAudit.Statements.liouville),
    (`UCPlanarAudit.uniformlyBounded, `UCPlanarAudit.Statements.uniformlyBounded),
    (`UCPlanarAudit.zeroCase, `UCPlanarAudit.Statements.zeroCase),
    (`UCPlanarAudit.counterexample, `UCPlanarAudit.Statements.counterexample)] do
    let some ti := env.find? thm | throwError "missing theorem {thm}"
    let some si := env.find? stmt | throwError "missing statement {stmt}"
    let some v := si.value? | throwError "statement {stmt} has no value"
    unless ti.levelParams == si.levelParams do
      throwError "{thm}: universe parameters differ from the challenge statement"
    -- A `def` abstracts the proofs inside its value into auxiliary lemmas
    -- (`UCPlanarAudit.Statements.*._proof_i`, shared between declarations);
    -- put their proof terms back before comparing.
    let v := v.replace fun e => match e with
      | .const n ls =>
        if (`UCPlanarAudit.Statements).isPrefixOf n && n.isInternal then
          (env.find? n).bind fun ci => (ci.value? (allowOpaque := true)).map (·.instantiateLevelParams ci.levelParams ls)
        else none
      | _ => none
    let v ← liftCoreM (Core.betaReduce v)
    let ty ← liftCoreM (Core.betaReduce ti.type)
    unless ty == v do
      throwError "{thm}: the solution statement differs from the challenge statement"
    for c in ti.type.getUsedConstants do
      if (`UCPlanar).isPrefixOf c || (`LatticeProb).isPrefixOf c || (`Schoenflies).isPrefixOf c then
        throwError "{thm} mentions the repository or library constant {c}"
    logInfo m!"{thm}: identical to the challenge statement; no repository or library constant"

#print axioms UCPlanarAudit.liouville
#print axioms UCPlanarAudit.uniformlyBounded
#print axioms UCPlanarAudit.zeroCase
#print axioms UCPlanarAudit.counterexample

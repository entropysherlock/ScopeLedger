import Lean
import B01_twin_structure
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let target := "QuantumLean.FormalConjecturesWrappers.eqSystem8_no_solution_d3_trinary_int".toName
  let modIdx := env.getModuleIdx? `B01_twin_structure
  let mut seen : NameSet := {}
  let mut stack : List Name := [`SL004.bridge43]
  let mut found := false
  while !stack.isEmpty do
    let n := stack.head!
    stack := stack.tail!
    if seen.contains n then continue
    seen := seen.insert n
    if n == target then
      found := true
      break
    let some ci := env.find? n | continue
    unless n == `SL004.bridge43 || (modIdx.isSome && env.getModuleIdxFor? n == modIdx) do continue
    let used := ci.type.getUsedConstants ++ ((ci.value? (allowOpaque := true)).map Expr.getUsedConstants |>.getD #[])
    for c in used do
      stack := c :: stack
  IO.println s!"USES_CITED {found}"

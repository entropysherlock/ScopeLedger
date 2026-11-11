import Lean
import E_E1_twin_exact
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let target := "A397588.a_three_dvd".toName
  let modIdx := env.getModuleIdx? `E_E1_twin_exact
  let mut seen : NameSet := {}
  let mut stack : List Name := [`SL004.bridge_E1_twin_exact]
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
    unless n == `SL004.bridge_E1_twin_exact || (modIdx.isSome && env.getModuleIdxFor? n == modIdx) do continue
    let used := ci.type.getUsedConstants ++ ((ci.value? (allowOpaque := true)).map Expr.getUsedConstants |>.getD #[])
    for c in used do
      stack := c :: stack
  IO.println s!"USES_CITED {found}"

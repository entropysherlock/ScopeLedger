import Lean
import E_E3_convert_p0_k4
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let target := "Erdos1021.erdos_1021".toName
  let modIdx := env.getModuleIdx? `E_E3_convert_p0_k4
  let mut seen : NameSet := {}
  let mut stack : List Name := [`SL004.bridge_E3_convert_p0_k4]
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
    unless n == `SL004.bridge_E3_convert_p0_k4 || (modIdx.isSome && env.getModuleIdxFor? n == modIdx) do continue
    let used := ci.type.getUsedConstants ++ ((ci.value? (allowOpaque := true)).map Expr.getUsedConstants |>.getD #[])
    for c in used do
      stack := c :: stack
  IO.println s!"USES_CITED {found}"

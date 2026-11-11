import Lean
import B01_greatest
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let target := "Erdos581.erdos_581".toName
  let modIdx := env.getModuleIdx? `B01_greatest
  let mut seen : NameSet := {}
  let mut stack : List Name := [`SL004.bridge03]
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
    unless n == `SL004.bridge03 || (modIdx.isSome && env.getModuleIdxFor? n == modIdx) do continue
    let used := ci.type.getUsedConstants ++ ((ci.value? (allowOpaque := true)).map Expr.getUsedConstants |>.getD #[])
    for c in used do
      stack := c :: stack
  IO.println s!"USES_CITED {found}"

import Lean
import Bridge
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let target := "Erdos865.erdos865".toName
  let modIdx := env.getModuleIdx? `Bridge
  let mut seen : NameSet := {}
  let mut stack : List Name := [`SL004.bridge_main]
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
    unless n == `SL004.bridge_main || (modIdx.isSome && env.getModuleIdxFor? n == modIdx) do continue
    let used := ci.type.getUsedConstants ++ ((ci.value? (allowOpaque := true)).map Expr.getUsedConstants |>.getD #[])
    for c in used do
      stack := c :: stack
  IO.println s!"USES_CITED {found}"

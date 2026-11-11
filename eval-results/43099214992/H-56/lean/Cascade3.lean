import SL003Target

theorem SL003.cascade3 : SL003FC.Erdos1150.SL003.targetProp := by
  unfold SL003FC.Erdos1150.SL003.targetProp
  exact (@OAI.AsymptoticallyMinimalLittlewood.main).1

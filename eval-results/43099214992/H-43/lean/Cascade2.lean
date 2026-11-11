import SL003Target

theorem SL003.cascade2 : SL003FC.Erdos261.SL003.targetProp := by
  unfold SL003FC.Erdos261.SL003.targetProp
  simpa [Erdos261InfiniteRepresentation, Erdos261Prop] using @Erdos261.Palomar.borwein_loring

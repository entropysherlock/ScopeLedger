import SL003Target

theorem SL003.cascade2 : SL003FC.Erdos522.SL003.targetProp := by
  unfold SL003FC.Erdos522.SL003.targetProp
  simpa [numRootsInUnitDisk, polynomial, roots] using @E522.erdos_522_zero_one_solved

import SL003Target

theorem SL003.cascade2 : SL003FC.OeisA6697.SL003.targetProp := by
  unfold SL003FC.OeisA6697.SL003.targetProp
  simpa [a, finiteWord, infiniteWord, morphism, subwordAt, subwordsOfLength] using @conjecture

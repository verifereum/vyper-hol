(* One staging endpoint with separation between distinct descriptor positions. *)
Theory bodyIntCallStageDistinctEndpoint
Ancestors
  bodyIntCallStageSeparated bodyIntCallStageEndpoint bodyIntCallStageList
  bodyIntCallStageOwned bodyIntCallStageTransport bodyIntCallHeldArgs
  exprSimWordArgs exprLoweringProps fragGasFocus context exprLowering compileEnv
  venomMemDefs

Theorem staged_arg_tail_separation:
  staged_arg ce func es a mid t (ty,tv,v,flag,op) /\
  EVERY (staged_arg ce func es mid sn t) D /\ alloca_inv t ==>
  !i. i < LENGTH D ==>
  (\(ty',tv',v',flag',op'). ~flag /\ ~flag' ==>
    !w w'. eval_operand op t = SOME w /\ eval_operand op' t = SOME w' ==>
      compileEnv$regions_disjoint (w2n w) (type_memory_size tv)
        (w2n w') (type_memory_size tv') /\
      compileEnv$regions_disjoint (w2n w') (type_memory_size tv')
        (w2n w) (type_memory_size tv)) (EL i D)
Proof
  strip_tac >> rpt strip_tac >>
  `MEM (EL i D) D` by simp[listTheory.EL_MEM] >>
  `staged_arg ce func es mid sn t (EL i D)` by
    metis_tac[listTheory.EVERY_MEM] >>
  Cases_on `EL i D` >> rename1 `(ty',rest)` >>
  PairCases_on `rest` >> simp[] >> rpt strip_tac >> gvs[] >>
  drule_all staged_arg_intervals_disjoint >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[]
QED


(* Semantic package-entry boundaries for one list of staged descriptors. *)
Theory bodyIntCallStagePackage
Ancestors
  bodyIntCallStageOwned intCallCallee exprSimProps abiCallerAllocation
  tupleLoadProps venomExecProofs list pair finite_map

Theorem staged_args_operands_defined:
  EVERY (staged_arg ce func es a sm s) D ==>
  ?ws. eval_operands (MAP (\(ty,tv,v,flag,op). op) D) s = SOME ws
Proof
  strip_tac >>
  `IS_SOME (eval_operands (MAP (\(ty,tv,v,flag,op). op) D) s)` by
    (simp[eval_operands_IS_SOME_EVERY, EVERY_MAP, EVERY_MEM] >>
     rpt strip_tac >> rename1 `MEM d D` >> PairCases_on `d` >>
     fs[EVERY_MEM] >> first_x_assum drule >> simp[staged_arg_def] >>
     metis_tac[optionTheory.IS_SOME_DEF]) >>
  Cases_on `eval_operands (MAP (\(ty,tv,v,flag,op). op) D) s` >> gvs[]
QED

Theorem staged_arg_parameter:
  staged_arg caller func es a sm s (ty,tv,v,flag,op) /\
  alloca_inv s /\ evaluate_type tenv ty = SOME tv /\
  (flag ==> is_word_type ty) /\
  eval_operand op s = SOME w ==>
  val_wf tv v /\
  (if flag then
     32 <= type_memory_size tv /\
     !b m. mem_word_at b m = w ==> val_in_memory tv v b m
   else
     w2n w + type_memory_size tv <= s.vs_alloca_next /\
     val_in_memory tv v (w2n w) s.vs_memory)
Proof
  simp[staged_arg_def] >> strip_tac >> Cases_on `flag` >> gvs[]
  >- (conj_tac
      >- (drule_all word_tv_memory_size >> simp[]) >>
      metis_tac[val_in_memory_word]) >>
  metis_tac[abi_caller_allocation_end]
QED

Theorem staged_args_internal_rel:
  EVERY (staged_arg caller func es a sm s) D /\ alloca_inv s /\
  ALL_DISTINCT (MAP FST params) /\ FDOM env = set (MAP FST params) /\
  LENGTH params = LENGTH D /\ LENGTH (prefix ++ ws) < dimword(:256) /\
  eval_operands (MAP (\(ty,tv,v,flag,op). op) D) s = SOME ws /\
  (!i. i < LENGTH D ==>
    (\(ty,tv,v,flag,op).
      flag = SND (EL i params) /\ evaluate_type tenv ty = SOME tv /\
      (flag ==> is_word_type ty) /\
      FLOOKUP env (FST (EL i params)) =
        SOME <|assignable := T; type := tv; value := v; popped := []|> /\
      ?off. FLOOKUP ce.ce_vars (FST (EL i params)) =
        SOME (MemLoc off (type_memory_size tv))) (EL i D)) /\
  (!i j. i < LENGTH D /\ j < LENGTH D /\ i <> j ==>
    (\(ty,tv,v,flag,op) (ty',tv',v',flag',op').
      ~flag /\ ~flag' ==>
      !w w'. eval_operand op s = SOME w /\ eval_operand op' s = SOME w' ==>
      regions_disjoint (w2n w) (type_memory_size tv)
        (w2n w') (type_memory_size tv')) (EL i D) (EL j D)) ==>
  internal_args_rel ce params env (LENGTH prefix) (prefix ++ ws)
    s.vs_alloca_next s.vs_memory
Proof
  strip_tac >>
  `LENGTH ws = LENGTH D` by
    (drule eval_operands_length >> simp[]) >>
  simp[internal_args_rel_def] >> conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!i. i < LENGTH D ==> _`
        (qspec_then `i` mp_tac) >>
      (impl_tac >- simp[]) >> disch_tac >>
      Cases_on `EL i D` >> rename1 `(ty,rest)` >> PairCases_on `rest` >>
      fs[] >>
      `staged_arg caller func es a sm s (ty,rest0,rest1,rest2,rest3)` by
        (qpat_x_assum `EVERY _ D` mp_tac >>
         simp[EVERY_EL] >> disch_then (qspec_then `i` mp_tac) >> simp[]) >>
      `eval_operand rest3 s = SOME (EL i ws)` by
        (drule_at (Pat `eval_operands _ _ = _`) eval_operands_index >>
         disch_then (qspec_then `i` mp_tac) >> simp[EL_MAP]) >>
      drule_all staged_arg_parameter >> simp[EL_APPEND_EQN]) >>
  rpt strip_tac >>
  qpat_assum `!i j. _` (qspecl_then [`i`,`j`] mp_tac) >> simp[] >>
  qpat_assum `!i. i < LENGTH D ==> _` (qspec_then `i` mp_tac) >>
  qpat_assum `!i. i < LENGTH D ==> _` (qspec_then `j` mp_tac) >>
  Cases_on `EL i D` >> rename1 `(ti,di)` >> PairCases_on `di` >>
  Cases_on `EL j D` >> rename1 `(tj,dj)` >> PairCases_on `dj` >>
  simp[] >> rpt strip_tac >> gvs[] >>
  `eval_operand di3 s = SOME (EL i ws) /\
   eval_operand dj3 s = SOME (EL j ws)` by
    (conj_tac
     >- (drule eval_operands_index >>
         disch_then (qspec_then `i` mp_tac) >> simp[EL_MAP]) >>
     drule eval_operands_index >>
     disch_then (qspec_then `j` mp_tac) >> simp[EL_MAP]) >>
  fs[EL_APPEND_EQN] >>
  qpat_x_assum `!i j. _` (qspecl_then [`i`,`j`] mp_tac) >> simp[]
QED

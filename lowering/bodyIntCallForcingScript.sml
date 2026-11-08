(* Forcing preserves semantics and resources at one actual counted landing. *)
Theory bodyIntCallForcing
Ancestors
  bodyIntCallForcingCode bodyIntCallForcingStorage bodyIntCallForcingReadOnly
  bodyIntCallLiteralLanding context loweringPosts exprLoweringProps
  valueEncoding valueCopyBytes compileEnv venomState words finite_map
  fragGasMode vyperInterpreter vyperState

Theorem protected_value_forcing:
  unwrap_value ce vv sa = (op,sb) /\ vv_holds ce cx ty r vv es s /\
  read_result cx r es = (INL v,es) /\ 
  evaluate_type (get_tenv cx) ty = SOME tv /\
  type_memory_bytes ce ty = type_memory_size tv /\ type_memory_size tv < 2**64 /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sa /\
  fresh_vars_wrt sa s /\ allocas_above lo s /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sa x) /\
  (!q x. reserved q /\ q = Var x ==> not_fresh_at sa x) /\
  (!p k. P p k ==> p+k <= lo) /\
  (~is_word_type ty /\ ~is_bytestring_type ty /\
    (case vv of StackValue _ _ => T | LocatedValue _ p => p.ptr_location = LocMemory) ==>
    ?w a k. eval_operand (vv_operand vv) s = SOME w /\
      a <= w2n w /\ w2n w + type_memory_size tv <= a+k /\ a+k < dimword (:256) /\
      (lo <= a \/ ?b z. staged b z /\ b <= a /\ a+k <= b+z)) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    expr_val_rel cx ty v op u /\ stmt_state_rel ctx func ce cx es u /\
    allocas_above lo u /\ s.vs_alloca_next <= u.vs_alloca_next /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==> FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!p k. P p k ==> mem_bytes_at p k u.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (!q. reserved q ==> eval_operand q u = eval_operand q s) /\
    (!name b sz. local_region ce scopes u name b sz <=> local_region ce scopes s name b sz) /\
    (~is_word_type ty /\ ~is_bytestring_type ty ==>
      ?w a k. eval_operand op u = SOME w /\ a <= w2n w /\
        w2n w + type_memory_size tv <= a+k /\ a+k < dimword (:256) /\
        (lo <= a \/ ?b z. staged b z /\ b <= a /\ a+k <= b+z)) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  drule_all exprSimAggregateChildrenTheory.vv_holds_materialise >> strip_tac >>
  Cases_on `vv`
  >- (drule (SRULE [] protected_identity_value_forcing) >>
      disch_then drule >> simp[] >> strip_tac >>
      qexists_tac `s` >> fs[] >> metis_tac[]) >>
  rename1 `LocatedValue ann p` >>
  Cases_on `is_word_type ty`
  >- (drule_all protected_word_value_forcing >>
      disch_then (qspec_then `scopes` strip_assume_tac) >>
      `u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
       u.vs_alloca_next = s.vs_alloca_next` by
        (rpt conj_tac >> qpat_assum `u = _` (fn th => simp[Once th])) >>
      qexists_tac `u` >> fs[intCallFrameTheory.allocas_above_def] >> metis_tac[]) >>
  Cases_on `p.ptr_location = LocMemory`
  >- (drule protected_identity_value_forcing >> disch_then drule >>
      simp[] >> strip_tac >> qexists_tac `s` >> fs[] >> metis_tac[]) >>
  `ann = ty` by fs[vv_holds_def] >> gvs[] >>
  `p.ptr_location <> LocCalldata` by
    (Cases_on `p.ptr_location` >> fs[vv_holds_def]) >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sa x` by fs[vv_operand_def] >>
  Cases_on `p.ptr_location = LocCode`
  >- (drule protected_code_value_forcing >>
      disch_then (drule_at (Pat `vv_holds _ _ _ _ _ _ _`)) >>
      disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
      disch_then (drule_at (Pat `allocas_above _ _`)) >>
      disch_then (qspecl_then [`tv`, `scopes`, `reserved`, `P`] mp_tac) >>
      (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
      qexists_tac `u` >> simp[] >> rpt strip_tac >>
      qexistsl_tac [`w2n w`, `type_memory_size tv`] >> simp[]) >>
  `(p.ptr_location = LocStorage \/ p.ptr_location = LocTransient)` by
    (Cases_on `p.ptr_location` >> fs[]) >>
  drule protected_storage_value_forcing >>
  disch_then (drule_at (Pat `vv_holds _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `allocas_above _ _`)) >>
  disch_then (qspecl_then [`tv`, `scopes`, `reserved`, `P`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  qexists_tac `u` >> simp[] >> rpt strip_tac >>
  qexistsl_tac [`w2n w`, `type_memory_size tv`] >> simp[]
QED

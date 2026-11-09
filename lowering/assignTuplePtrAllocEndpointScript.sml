(* Compiler-facing allocation endpoint; both fresh and reused sites. *)
Theory assignTuplePtrAllocEndpoint
Ancestors
  assignTuplePtrAlloc allocationPtr localPtrsProps exprLoweringProps
  exprSimProps compileEnv venomState venomInst venomExecSemantics
  loweringHalt finite_map valueEncoding emitHelperProps loweringSlice
  bodyPtrDefs fragGasPathPtr ghostPcTransportPtr stmtFragPtr emitHelper
  normalizationAllocPtr

Theorem alloca_step_live_local_separated_ptr:
  !ctx func cenv cx es s id n out s1 b.
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
  not_local_ptr cenv es.scopes out /\ n < dimword(:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 /\
  FLOOKUP s1.vs_allocas id = SOME (b,n) ==>
  !name entry p sz w.
    lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w ==>
    w2n w + val_footprint entry.type entry.value <= b \/ b+n <= w2n w
Proof
  rpt gen_tac >> strip_tac >>
  `alloca_inv s /\ local_ptrs_rel func cenv es.scopes s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  rpt gen_tac >> strip_tac >>
  `w2n w + sz <= s.vs_alloca_next /\
   type_memory_size entry.type <= sz /\ val_wf entry.type entry.value` by
    (fs[local_ptrs_rel_def] >>
     qpat_x_assum `!name entry p sz. _` drule_all >> strip_tac >> gvs[]) >>
  `val_footprint entry.type entry.value <= sz` by
    metis_tac[val_footprint_le, arithmeticTheory.LESS_EQ_TRANS] >>
  Cases_on `FLOOKUP s.vs_allocas id`
  >- (drule step_alloca_fresh >> disch_then (qspec_then `n` mp_tac) >>
      simp[] >> disch_then (qspec_then `out` assume_tac) >>
      gvs[update_var_def, FLOOKUP_UPDATE] >> decide_tac) >>
  rename1 `FLOOKUP s.vs_allocas id = SOME site` >> PairCases_on `site` >>
  drule_all stmt_state_rel_alloca_site_bound >> strip_tac >> gvs[] >>
  drule reused_alloca_step >> disch_then (qspec_then `out` assume_tac) >>
  gvs[update_var_def] >>
  `local_region cenv es.scopes s name (w2n w) sz` by
    (simp[local_region_def] >> metis_tac[]) >>
  drule_at (Pat `MEM _ (fn_insts _)`) local_ptrs_rel_alloca_disjoint >>
  simp[mk_inst_def] >> disch_then drule_all >>
  simp[regions_disjoint_def] >> decide_tac
QED

Theorem emit_alloca_endpoint_ptr:
  !sx sm n p func ctx cenv cx es s d G tn D PG.
  emit_inst ALLOCA [Lit (n2w n)] [p] sx = ((),sm) /\
  fn_has_code sx sm func /\ stmt_state_rel ctx func cenv cx es s /\
  fn_inst_ids_distinct func /\ n < dimword(:256) /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sx.cs_current_bb /\
  s.vs_inst_idx = LENGTH sx.cs_current_insts /\ ~s.vs_halted /\
  ghost_inv d cenv cx es G tn s /\ not_local_ptr cenv es.scopes p /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> x <> p) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> x <> p) ==>
  ?t b G1 tn1.
    gas_path_ptr D 0 ctx func PG G tn s 0 G1 tn1 (OK t) /\
    ghost_inv d cenv cx es G1 tn1 t /\ stmt_state_rel ctx func cenv cx es t /\
    ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    FLOOKUP t.vs_allocas sx.cs_next_id = SOME (b,n) /\ b+n < dimword(:256) /\
    eval_operand (Var p) t = SOME (n2w b) /\ ptr_covers G1 tn1 p t n /\
    t.vs_memory = s.vs_memory /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!x. x <> p ==> lookup_var x t = lookup_var x s /\
      FLOOKUP G1 x = FLOOKUP G x /\ op_taint tn1 (Var x) = op_taint tn (Var x)) /\
    (!name entry q sz w. lookup_scopes name es.scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var q) sz) /\
      lookup_var q t = SOME w ==>
      w2n w + val_footprint entry.type entry.value <= b \/ b+n <= w2n w) /\
    (!ty tv se sa v op w.
      expr_val_at cenv cx ty se sa es v op s /\
      evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
      val_wf tv v /\ eval_operand op s = SOME w /\
      (sx.cs_next_id < se.cs_next_id \/ sa.cs_next_id <= sx.cs_next_id) /\
      (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
        val_in_memory tv v (w2n w) m) ==>
      !m. mem_agree_outside tn1.t_mem t.vs_memory m ==>
        val_in_memory tv v (w2n w) m)
Proof
  rpt gen_tac >> strip_tac >>
  `MEM (mk_inst sx.cs_next_id ALLOCA [Lit (n2w n)] [p]) (fn_insts func)` by
    (irule emit_inst_fn_member >> qexists `sm` >> simp[]) >>
  qspecl_then [`sx.cs_next_id`, `n2w n`, `p`, `s`]
    (qx_choosel_then [`w`, `s1`] strip_assume_tac) step_alloca_frame >>
  drule_all alloca_step_site >>
  disch_then (qx_choose_then `b` strip_assume_tac) >>
  drule_at (Pat `step_inst_base _ _ = _`) alloca_step_live_local_separated_ptr >>
  simp[] >> disch_tac >>
  `!name entry q sz w. lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var q) sz) /\
    lookup_var q s = SOME w ==>
    w2n w + val_footprint entry.type entry.value <= b \/ b+n <= w2n w` by
    (rpt strip_tac >> first_x_assum irule >> simp[] >> metis_tac[]) >>
  `ghost_inv d cenv cx es
     (step_prov PG G (mk_inst sx.cs_next_id ALLOCA [Lit (n2w n)] [p]) s1)
     (step_taint (mk_inst sx.cs_next_id ALLOCA [Lit (n2w n)] [p]) s s1 tn) s1` by
    (irule alloca_separated_ghost_inv_ptr >> simp[] >>
     conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
     conj_tac >- fs[not_local_ptr_def] >> conj_tac >- metis_tac[] >>
     qexistsl_tac [`ctx`, `func`] >> simp[]) >>
  drule_all emit_alloca_zero_path_ptr >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `ghost_inv d cenv cx es G1 tn1 s1` >>
  qexistsl_tac [`s1 with vs_inst_idx := SUC s.vs_inst_idx`, `b`, `G1`, `tn1`] >>
  simp[] >> suspend "post"
QED

Resume emit_alloca_endpoint_ptr[post]:
  `exec_alloca (mk_inst sx.cs_next_id ALLOCA [Lit (n2w n)] [p]) s (n2w n : bytes32) = OK s1` by
    (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
     simp[step_inst_base_opcode_eqs, mk_inst_def, eval_operands_def, eval_operand_def] >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  `stmt_state_rel ctx func cenv cx es s1` by
    (drule_at (Pat `exec_alloca _ _ _ = _`) stmt_state_rel_exec_alloca >>
     disch_then (mp_tac o cj 1) >>
     simp[GSYM mk_inst_def] >> metis_tac[]) >>
  simp[stmt_state_rel_inst_idx, lookup_var_def] >>
  conj_tac >- suspend "ghost_index" >>
  conj_tac >- suspend "nonhalt" >>
  `sx.cs_current_bb = sm.cs_current_bb /\
   SUC (LENGTH sx.cs_current_insts) = LENGTH sm.cs_current_insts` by
    (gvs[emit_inst_def, comp_bind_def, fresh_id_def, emit_def, LET_THM]) >> simp[] >>
  conj_tac >- suspend "allocation_map" >>
  conj_tac >- fs[lookup_var_def] >>
  conj_tac >- suspend "local_separation" >> suspend "source"
QED

Resume emit_alloca_endpoint_ptr[local_separation]:
  rpt gen_tac >> strip_tac >>
  `q <> p` by metis_tac[not_local_ptr_def] >>
  `lookup_var q s = SOME w'` by
    (fs[lookup_var_def] >> metis_tac[]) >> metis_tac[]
QED

Resume emit_alloca_endpoint_ptr[ghost_index]:
  mp_tac (Q.INST [`s` |-> `s1`, `p` |-> `s1.vs_prev_bb`,
    `G` |-> `G1`, `tn` |-> `tn1`,
    `l` |-> `s1.vs_current_bb`, `i` |-> `SUC (LENGTH sx.cs_current_insts)`]
    ghost_inv_jump_to) >>
  `s1 with <|vs_prev_bb := s1.vs_prev_bb; vs_current_bb := s1.vs_current_bb;
     vs_inst_idx := SUC (LENGTH sx.cs_current_insts)|> =
   s1 with vs_inst_idx := SUC (LENGTH sx.cs_current_insts)` by
    (simp[venom_state_component_equality]) >> simp[]
QED

Resume emit_alloca_endpoint_ptr[nonhalt]:
  qpat_x_assum `exec_alloca _ _ _ = _` mp_tac >>
  simp[exec_alloca_def, mk_inst_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[update_var_def]
QED

Resume emit_alloca_endpoint_ptr[allocation_map]:
  qpat_x_assum `exec_alloca _ _ _ = _` mp_tac >>
  Cases_on `FLOOKUP s.vs_allocas sx.cs_next_id`
  >- (simp[exec_alloca_def, mk_inst_def] >> strip_tac >>
      gvs[update_var_def] >> rpt gen_tac >> strip_tac >>
      Cases_on `aid = sx.cs_next_id` >> gvs[FLOOKUP_UPDATE]) >>
  rename1 `FLOOKUP s.vs_allocas sx.cs_next_id = SOME site` >>
  PairCases_on `site` >> simp[exec_alloca_def, mk_inst_def] >>
  strip_tac >> gvs[update_var_def]
QED

Resume emit_alloca_endpoint_ptr[source]:
  rpt gen_tac >> strip_tac >>
  qunabbrev_tac `tn1` >>
  drule_at (Pat `step_inst_base _ _ = _`) alloca_step_expr_robust_preserved >>
  simp[] >> disch_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum (drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> disch_then drule_all >> simp[]
QED

Finalise emit_alloca_endpoint_ptr

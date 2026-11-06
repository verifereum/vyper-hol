Theory bodyPtrIfExpAllocSource
Ancestors
  exprSimVVFrame exprSimProps exprSimDefs loweringPosts exprLoweringProps
  compileEnv venomState finite_map exprLowering context
  bodyPtrIfExpAllocFrame allocationPtr exprSimAlloc loweringHalt fragExec
  bodyPtrDefs decoderGhostFramePtr ptrDiscipline venomInst venomMemDefs

(* Allocation extends the site map, unlike the variable-only frame. *)
Theorem vv_at_alloc_map_frame:
  vv_at cenv cx ty sa sb es raw vv s /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
               FLOOKUP q.vs_allocas aid = SOME entry) /\
  eval_operand (vv_operand vv) q = eval_operand (vv_operand vv) s /\
  (!n b sz. local_region cenv es.scopes q n b sz <=>
            local_region cenv es.scopes s n b sz) /\
  sb.cs_next_id <= sm.cs_next_id ==>
  vv_at cenv cx ty sa sm es raw vv q
Proof
  Cases_on `vv` >>
  simp[vv_at_def, vv_operand_def, expr_val_at_def] >>
  rpt strip_tac >> gvs[]
  >>~- ([`FLOOKUP s.vs_allocas aid = SOME (b,sz)`],
        disj1_tac >> qexistsl_tac [`aid`, `b`, `sz`] >> simp[] >>
        rpt strip_tac >>
        qpat_x_assum `!n lb lsz. local_region _ _ s _ _ _ ==> _` drule >> simp[])
  >>~- ([`local_region cenv es.scopes s n b sz`],
        disj2_tac >> disj1_tac >> qexistsl_tac [`n`, `b`, `sz`] >> simp[])
  >> metis_tac[]
QED

Theorem vv_post_alloc_map_frame:
  vv_post ctx fn cenv cx e es sa sb s0 es' raw vv s /\
  stmt_state_rel ctx fn cenv cx es' q /\
  q.vs_memory = s.vs_memory /\
  contract_storage q = contract_storage s /\
  contract_transient q = contract_transient s /\
  eval_operand (vv_operand vv) q = eval_operand (vv_operand vv) s /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
               FLOOKUP q.vs_allocas aid = SOME entry) /\
  (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s) /\
  (!n b sz. local_region cenv es'.scopes q n b sz <=>
            local_region cenv es'.scopes s n b sz) /\
  sb.cs_next_id <= sc.cs_next_id ==>
  vv_post ctx fn cenv cx e es sa sc s0 es' raw vv q
Proof
  strip_tac >>
  `vv_holds cenv cx (expr_type e) raw vv es' q` by
    (irule vv_holds_vars_frame >> simp[] >> qexists_tac `s` >> gvs[vv_post_def]) >>
  `vv_at cenv cx (expr_type e) sa sc es' raw vv q` by
    (irule vv_at_alloc_map_frame >> simp[] >>
     qexistsl_tac [`s`, `sb`] >> gvs[vv_post_def]) >>
  gvs[vv_post_def, locals_kept_def] >> rpt strip_tac >> metis_tac[]
QED

Theorem alloca_step_contracts:
  n < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u ==>
  contract_storage u = contract_storage s /\
  contract_transient u = contract_transient s /\
  u.vs_accounts = s.vs_accounts /\ u.vs_call_ctx = s.vs_call_ctx /\
  u.vs_transient = s.vs_transient /\
  u.vs_halted = s.vs_halted /\ u.vs_current_bb = s.vs_current_bb
Proof
  strip_tac >> Cases_on `FLOOKUP s.vs_allocas id`
  >- (drule step_alloca_fresh >> disch_then (qspec_then `n` mp_tac) >>
      simp[] >> disch_then (qspec_then `out` assume_tac) >>
      gvs[update_var_def, contract_storage_def, contract_transient_def]) >>
  rename1 `SOME site` >> PairCases_on `site` >>
  drule reused_alloca_memory_effects >>
  disch_then (qspecl_then [`n`, `out`, `tn`] strip_assume_tac) >>
  gvs[update_var_def, contract_storage_def, contract_transient_def]
QED

Theorem compile_alloc_buffer_raw_resources:
  !ctx fn cenv cx es sb n buf sc s out u.
    stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
    local_ptrs_reserved cenv sb /\
    compile_alloc_buffer n sb = (buf,sc) /\ fn_has_code sb sc fn /\
    buf.buf_operand = Var out /\ n < dimword (:256) /\
    step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) s = OK u ==>
    stmt_state_rel ctx fn cenv cx es u /\ u.vs_memory = s.vs_memory /\
    (!x. not_fresh_at sb x ==> lookup_var x u = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
                 FLOOKUP u.vs_allocas aid = SOME entry)
Proof
  rpt strip_tac >> drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  drule compile_alloc_buffer_insts >> strip_tac >>
  gvs[emitted_insts_def, listTheory.DROP_APPEND, run_inst_seq_def]
QED

Theorem compile_alloc_buffer_vv_post:
  !ctx fn cenv cx e es sa sb s0 es' raw vv s n buf sc out u.
    vv_post ctx fn cenv cx e es sa sb s0 es' raw vv s /\
    fn_inst_ids_distinct fn /\ local_ptrs_reserved cenv sa /\
    sa.cs_next_var <= sb.cs_next_var /\
    (!x. vv_operand vv = Var x ==> not_fresh_at sb x) /\
    compile_alloc_buffer n sb = (buf,sc) /\ fn_has_code sb sc fn /\
    buf.buf_operand = Var out /\ n < dimword (:256) /\
    step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) s = OK u ==>
    vv_post ctx fn cenv cx e es sa sc s0 es' raw vv u
Proof
  rpt strip_tac >>
  `stmt_state_rel ctx fn cenv cx es' s` by gvs[vv_post_def] >>
  `local_ptrs_reserved cenv sb` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  drule_all compile_alloc_buffer_raw_resources >> strip_tac >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `eval_operand (vv_operand vv) u = eval_operand (vv_operand vv) s` by
    (irule alloca_step_operand_preserved >> simp[] >>
     rpt strip_tac >> metis_tac[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s` by
    metis_tac[stmtFragPtrTheory.not_fresh_at_mono] >>
  `!name b sz. local_region cenv es'.scopes u name b sz <=>
                local_region cenv es'.scopes s name b sz` by
    (rpt gen_tac >> eq_tac
     >- (strip_tac >> irule local_region_frame >>
         conj_tac
         >- (qexists_tac `fn` >> gvs[stmt_state_rel_def, state_rel_def]) >>
         qexistsl_tac [`sa`, `es'.scopes`, `u`] >> simp[]) >>
     strip_tac >> irule local_region_frame_fwd >>
     qexistsl_tac [`s`, `sa`, `es'.scopes`] >> simp[]) >>
  drule_all alloca_step_contracts >> strip_tac >>
  irule vv_post_alloc_map_frame >> simp[] >>
  qexistsl_tac [`s`, `sb`] >> simp[]
QED

Theorem vv_at_memory_footprint:
  !ctx fn cenv cx ty sa sb es raw vv s v tv w.
    stmt_state_rel ctx fn cenv cx es s /\
    vv_at cenv cx ty sa sb es raw vv s /\
    (!t p. vv = LocatedValue t p ==> p.ptr_location = LocMemory) /\
    read_result cx raw es = (INL v,es) /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
    eval_operand (vv_operand vv) s = SOME w ==>
    val_wf tv v /\
    (!i. w2n w <= i /\ i < w2n w + val_footprint tv v ==> i < s.vs_alloca_next)
Proof
  rpt strip_tac >>
  `expr_val_at cenv cx ty sa sb es v (vv_operand vv) s` by
    (Cases_on `vv` >>
     gvs[vv_at_def, vv_operand_def, expr_val_at_def] >>
     metis_tac[])
  >- gvs[expr_val_at_def] >>
  irule expr_val_at_below_frontier >> simp[] >> metis_tac[]
QED

Theorem alloca_step_source_buffer:
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u /\
  (!x. op = Var x ==> x <> out) /\ ptr_buf_ok cenv e op G s ==>
  ptr_buf_ok cenv e op
    (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) u) u
Proof
  strip_tac >> drule_all alloca_step_operand_preserved >> strip_tac >>
  simp[ptr_buf_ok_def] >> rpt strip_tac >>
  qpat_x_assum `ptr_buf_ok _ _ _ _ _` mp_tac >>
  simp[ptr_buf_ok_def] >> strip_tac >>
  qexistsl_tac [`x`, `b`, `sz`] >>
  simp[step_prov_other_output, mk_inst_def]
QED

Theorem alloca_step_source_memory:
  n < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u /\
  (!x. op = Var x ==> x <> out) /\
  ptr_mem_ok cx ty v op G tn s /\
  (!tv w. evaluate_type (get_tenv cx) ty = SOME tv /\
     eval_operand op s = SOME w ==> val_wf tv v /\
     (!i. w2n w <= i /\ i < w2n w + val_footprint tv v ==>
           i < s.vs_alloca_next)) ==>
  ptr_mem_ok cx ty v op
    (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) u)
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn) u
Proof
  strip_tac >> drule_all alloca_step_operand_preserved >> strip_tac >>
  simp[ptr_mem_ok_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `ptr_mem_ok _ _ _ _ _ _ _` mp_tac >>
  simp[ptr_mem_ok_def] >> strip_tac >>
  `val_wf tv v /\
   (!i. w2n w <= i /\ i < w2n w + val_footprint tv v ==>
         i < s.vs_alloca_next)` by metis_tac[] >>
  conj_tac
  >- (rpt strip_tac >> irule alloca_step_robust_below_frontier >>
      simp[] >> metis_tac[]) >>
  strip_tac >> first_x_assum drule >> strip_tac >>
  qexistsl_tac [`x`, `b`, `sz`] >>
  simp[step_prov_other_output, mk_inst_def]
QED

Theorem located_vv_at_memory_footprint:
  stmt_state_rel ctx fn cenv cx es s /\
  vv_at cenv cx ty sa sb es raw (LocatedValue t p) s /\
  p.ptr_location = LocMemory /\ read_result cx raw es = (INL v,es) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  eval_operand p.ptr_operand s = SOME w ==>
  val_wf tv v /\
  (!i. w2n w <= i /\ i < w2n w + val_footprint tv v ==> i < s.vs_alloca_next)
Proof
  strip_tac >> gvs[vv_at_def] >> rpt strip_tac
  >- (fs[stmt_state_rel_def, alloca_inv_def, alloca_next_valid_def] >>
      first_x_assum drule >> decide_tac) >>
  fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def, local_region_def] >>
  first_x_assum drule_all >> strip_tac >> gvs[] >> decide_tac
QED

Theorem alloca_step_operand_taint:
  (!x. op = Var x ==> x <> out) ==>
  op_taint (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn) op =
  op_taint tn op
Proof
  Cases_on `op` >>
  simp[op_taint_def, step_taint_def, set_var_taint_def, mk_inst_def,
       FLOOKUP_UPDATE]
QED

Theorem alloca_step_operand_prov:
  (!x. op = Var x ==> x <> out) ==>
  op_prov (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) u) op =
  op_prov G op
Proof
  Cases_on `op` >> simp[op_prov_def, step_prov_other_output, mk_inst_def]
QED

Theorem alloca_step_source_vv:
  stmt_state_rel ctx fn cenv cx es s /\
  vv_at cenv cx ty sa sb es raw vv s /\
  n < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u /\
  (!x. vv_operand vv = Var x ==> x <> out) /\
  ptr_vv_ok cx ty raw vv es G tn s ==>
  ptr_vv_ok cx ty raw vv es
    (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) u)
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn) u
Proof
  strip_tac >> Cases_on `vv`
  >- (gvs[ptr_vv_ok_def, vv_operand_def] >>
      gvs[ptr_val_ok_def] >>
      conj_tac >- metis_tac[alloca_step_operand_taint] >>
      conj_tac >- metis_tac[alloca_step_operand_prov] >>
      strip_tac >> irule alloca_step_source_memory >> simp[] >>
      rpt gen_tac >> disch_tac >>
      qpat_assum `vv_at _ _ _ _ _ _ _ _ _`
        (mp_then Any mp_tac vv_at_memory_footprint) >>
      simp[vv_operand_def] >> metis_tac[]) >>
  gvs[vv_operand_def] >>
  `eval_operand p.ptr_operand u = eval_operand p.ptr_operand s` by
    (irule alloca_step_operand_preserved >> simp[] >> metis_tac[]) >>
  drule_all alloca_step_contracts >> strip_tac >>
  gvs[ptr_vv_ok_def] >> conj_tac
  >- metis_tac[alloca_step_operand_taint] >> conj_tac
  >- (strip_tac >> gvs[] >>
      irule alloca_step_source_memory >> simp[] >>
      rpt gen_tac >> disch_tac >>
      qpat_assum `vv_at _ _ _ _ _ _ _ _ _`
        (mp_then Any mp_tac located_vv_at_memory_footprint) >>
      simp[] >> metis_tac[]) >>
  gvs[GSYM contract_storage_def, GSYM contract_transient_def,
      step_taint_nonmemory_frame, mk_inst_def]
QED

Theorem ptr_vv_ok_inst_idx[simp]:
  ptr_vv_ok cx ty raw vv es G tn (s with vs_inst_idx := k) <=>
  ptr_vv_ok cx ty raw vv es G tn s
Proof
  Cases_on `vv` >>
  simp[ptr_vv_ok_def, ptr_val_ok_def, ptr_mem_ok_def, eval_operand_def,
       lookup_var_def]
QED

Theorem ptr_buf_ok_inst_idx[simp]:
  ptr_buf_ok cenv e op G (s with vs_inst_idx := k) <=> ptr_buf_ok cenv e op G s
Proof
  simp[ptr_buf_ok_def, eval_operand_def, lookup_var_def]
QED

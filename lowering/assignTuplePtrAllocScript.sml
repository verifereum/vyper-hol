(* Allocation interfaces for counted tuple staging, including reused sites. *)
Theory assignTuplePtrAlloc
Ancestors
  assignTuplePtrPrefix allocationPtr loweringHalt fragExecPtr
  bodyPtrDefs robustCopyTransportPtr exprLoweringProps
  venomInst venomState venomExecSemantics ptrDiscipline finite_map
  valueEncoding compileEnv loweringStateRelDefs

Theorem alloca_step_exterior_ghost_ptr:
  stmt_state_rel ctx func cenv cx es s /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
  n < dimword(:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 /\
  FLOOKUP s1.vs_allocas id = SOME (b,n) ==>
  s1.vs_memory = s.vs_memory /\
  (!p. p <> out ==> lookup_var p s1 = lookup_var p s /\
    FLOOKUP (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) s1) p =
      FLOOKUP G p /\
    op_taint (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn)
      (Var p) = op_taint tn (Var p)) /\
  (!i. ~(b <= i /\ i < b+n) ==>
    (i IN (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn).t_mem
      <=> i IN tn.t_mem))
Proof
  strip_tac >> Cases_on `FLOOKUP s.vs_allocas id`
  >- (drule_all fresh_alloca_ghost >>
      disch_then (qspecl_then [`PG`, `G`, `tn`] strip_assume_tac) >>
      drule step_alloca_fresh >> disch_then (qspec_then `n` mp_tac) >>
      simp[] >> disch_then (qspec_then `out` assume_tac) >>
      gvs[update_var_def, FLOOKUP_UPDATE, lookup_var_def, op_taint_def]) >>
  rename1 `FLOOKUP s.vs_allocas id = SOME site` >> PairCases_on `site` >>
  drule_all stmt_state_rel_alloca_site_bound >> strip_tac >> gvs[] >>
  drule reused_alloca_step >> disch_then (qspec_then `out` assume_tac) >> gvs[] >>
  drule reused_alloca_ghost >>
  disch_then (qspecl_then [`out`, `PG`, `G`, `tn`] strip_assume_tac) >>
  gvs[update_var_def, FLOOKUP_UPDATE, lookup_var_def, op_taint_def]
QED

Theorem alloca_separated_ghost_inv_ptr:
  stmt_state_rel ctx func cenv cx es s /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
  n < dimword(:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 /\
  FLOOKUP s1.vs_allocas id = SOME (b,n) /\ ghost_inv d cenv cx es G tn s /\
  (!name entry p sz. lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==> p <> out) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> x <> out) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> x <> out) /\
  (!name entry p sz w. lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w ==>
    w2n w + val_footprint entry.type entry.value <= b \/ b+n <= w2n w) ==>
  ghost_inv d cenv cx es
    (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) s1)
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn) s1
Proof
  strip_tac >> drule_all alloca_step_exterior_ghost_ptr >>
  disch_then (qspecl_then [`tn`, `PG`, `G`] strip_assume_tac) >>
  qmatch_goalsub_abbrev_tac `ghost_inv d cenv cx es G1 tf s1` >>
  gvs[ghost_inv_def] >> conj_tac >- suspend "locals" >>
  conj_tac >- suspend "return_buffer" >>
  conj_tac >- suspend "return_pc" >>
  simp[Abbr `tf`] >> irule alloca_step_stor_taint_ok >> simp[] >>
  metis_tac[]
QED

Resume alloca_separated_ghost_inv_ptr[return_pc]:
  rpt strip_tac >> `x <> out` by metis_tac[] >> metis_tac[]
QED

Resume alloca_separated_ghost_inv_ptr[return_buffer]:
  Cases_on `d` >- simp[return_buf_ptr_def] >>
  rename1 `return_buf_ptr (SOME pair)` >> PairCases_on `pair` >>
  gvs[return_buf_ptr_def] >>
  `x <> out` by metis_tac[] >>
  gvs[ptr_covers_def] >> metis_tac[]
QED

Resume alloca_separated_ghost_inv_ptr[locals]:
  rpt gen_tac >> strip_tac >>
  `p <> out` by metis_tac[] >>
  qpat_x_assum `!name entry p sz. _ ==> ptr_covers _ _ _ _ _ /\ _`
    (drule_all_then strip_assume_tac) >>
  conj_tac >- (gvs[ptr_covers_def] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  `lookup_var p s = SOME w` by metis_tac[] >>
  `val_wf entry.type entry.value` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >> metis_tac[]) >>
  irule robust_val_in_memory_exterior_frame >> conj_tac >- simp[] >>
  qexistsl_tac [`s.vs_memory`, `s1.vs_memory`, `tn.t_mem`, `tf.t_mem`,
    `{i | b <= i /\ i < b+n}`] >>
  simp[] >> conj_tac >- (rpt strip_tac >> metis_tac[]) >>
  qpat_x_assum `!name entry p sz w. _` drule_all >> decide_tac
QED

Finalise alloca_separated_ghost_inv_ptr

Theorem emit_alloca_zero_path_ptr:
  emit_inst ALLOCA [Lit (n2w n)] [out] sa = ((),sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  stmt_state_rel ctx func cenv cx es s /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
  n < dimword(:256) /\
  step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out]) s = OK s1 /\
  FLOOKUP s1.vs_allocas sa.cs_next_id = SOME (b,n) ==>
  gas_path_ptr D 0 ctx func PG G tn s 0
    (step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out]) s1)
    (step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out]) s s1 tn)
    (OK (s1 with vs_inst_idx := SUC s.vs_inst_idx)) /\
  ptr_covers
    (step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out]) s1)
    (step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out]) s s1 tn)
    out s1 n /\
  (!p. p <> out ==>
    FLOOKUP (step_prov PG G
      (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out]) s1) p = FLOOKUP G p /\
    op_taint (step_taint
      (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out]) s s1 tn) (Var p) =
      op_taint tn (Var p))
Proof
  strip_tac >> conj_tac
  >- (irule emit_inst_zero_path_ptr >> simp[is_terminator_def] >>
      irule ptr_inst_ok_alloca >> simp[]) >>
  conj_tac >- (irule alloca_step_ptr_covers >> metis_tac[]) >>
  drule_all alloca_step_exterior_ghost_ptr >>
  disch_then (qspecl_then [`tn`, `PG`, `G`] strip_assume_tac) >> simp[]
QED

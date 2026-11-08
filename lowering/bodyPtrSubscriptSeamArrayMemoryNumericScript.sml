Theory bodyPtrSubscriptSeamArrayMemoryNumeric
Ancestors
  bodyPtrSubscriptNumeric bodyPtrAttributeAdd ptrDiscipline ptrSafeRun
  bodyPtrDefs venomInst venomState venomExecSemantics finite_map
  decoderGhostFramePtr list codegenRel contextCodegenRel
  emitHelperProps emitHelper compileEnv exprLoweringProps fragGasPathPtr
  bodyPtrSubscriptNamedTuplePostBoundary

(* Literal comparisons and multiplication do not consume pointer provenance. *)
Theorem literal_numeric_inst_check:
  MEM opc [MUL; LT; SLT] /\ op_taint tn arg = {} /\
  ~ctx_has_dalloca ctx /\
  step_inst_base (mk_inst id opc [arg;Lit b] [out]) s = OK t /\
  t.vs_requests = s.vs_requests ==>
  ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id opc [arg;Lit b] [out]) s
Proof
  strip_tac >> gvs[] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def,
       op_taint_def] >>
  simp[GSYM mk_inst_def, step_inst_non_invoke] >>
  rpt strip_tac >> gvs[] >> gvs[op_taint_def] >>
  Cases_on `op = arg` >> simp[] >> Cases_on `op = Lit b` >> gvs[]
QED

Theorem literal_numeric_ghost_frame:
  MEM opc [MUL; LT; SLT] /\ op_taint tn arg = {} /\
  t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp ==>
  step_prov PG G (mk_inst id opc [arg;Lit b] [out]) t =
    DRESTRICT G (COMPL {out}) /\
  step_taint (mk_inst id opc [arg;Lit b] [out]) s t tn =
    (tn with t_var := tn.t_var |+ (out,{}))
Proof
  strip_tac >>
  `new_site_bytes s t = {}` by
    simp[new_site_bytes_def, FLOOKUP_DEF, pred_setTheory.EXTENSION, SF CONJ_ss] >>
  gvs[] >>
  simp[step_prov_def, set_prov_def, out_prov_def, mk_inst_def,
       step_taint_def, set_var_taint_def, mem_taint_def, step_writes_def,
       source_memory_write_ranges_def, written_taint_def, store_taint_def,
       adopt_reset_def, imm_taint_def, range_bytes_def,
       taint_component_equality, DRESTRICT_UNIV, out_taint_def, op_taint_def] >>
  gvs[op_taint_def] >> Cases_on `eval_operand arg s` >> simp[]
QED

Theorem emit_literal_numeric_counted:
  MEM opc [MUL; LT; SLT] /\
  emit_op opc [arg;Lit b] sa = (Var out,sb) /\ fn_has_code sa sb func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ op_taint tn arg = {} /\
  (!dst. step_inst_base (mk_inst sa.cs_next_id opc [arg;Lit b] [dst]) s =
         OK (update_var dst w s)) ==>
  gas_path_ptr D 0 ctx func PG G tn s 0
    (DRESTRICT G (COMPL {out})) (tn with t_var := tn.t_var |+ (out,{}))
    (OK ((update_var out w s) with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  sb.cs_current_bb = sa.cs_current_bb /\
  (!p. not_fresh_at sa p ==> p <> out)
Proof
  strip_tac >>
  `!dst. ptr_inst_ok D 0 0 ctx func G tn
     (mk_inst sa.cs_next_id opc [arg;Lit b] [dst]) s` by
    (gen_tac >> irule literal_numeric_inst_check >> simp[update_var_def] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `opc <> INVOKE /\ opc <> GAS /\ ~is_terminator opc` by
    (gvs[] >> simp[is_terminator_def]) >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def,
        fresh_var_def, fresh_id_def, emit_def, comp_return_def] >>
  drule emitted_insts_emit_op >> strip_tac >> gnvs[] >>
  drule_all attribute_emit_op_path_ptr >>
  `step_prov PG G (mk_inst sa.cs_next_id opc [arg;Lit b]
      [STRING #"%" (toString sa.cs_next_var)])
      (update_var (STRING #"%" (toString sa.cs_next_var)) w s) =
      DRESTRICT G (COMPL {STRING #"%" (toString sa.cs_next_var)}) /\
   step_taint (mk_inst sa.cs_next_id opc [arg;Lit b]
      [STRING #"%" (toString sa.cs_next_var)]) s
      (update_var (STRING #"%" (toString sa.cs_next_var)) w s) tn =
      (tn with t_var := tn.t_var |+ (STRING #"%" (toString sa.cs_next_var),{}))` by
    (irule literal_numeric_ghost_frame >> simp[update_var_def]) >>
  simp[] >> strip_tac >> simp[] >> rpt strip_tac >> gvs[not_fresh_at_def] >>
  qpat_x_assum `!PG'. gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`
    (qspec_then `PG` mp_tac) >> simp[arithmeticTheory.ADD1]
QED

Theorem literal_numeric_counted_read_only:
  MEM opc [MUL; LT; SLT] /\
  emit_op opc [arg;Lit b] sa = (Var out,sb) /\ fn_has_code sa sb func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ op_taint tn arg = {} /\
  (!dst. step_inst_base (mk_inst sa.cs_next_id opc [arg;Lit b] [dst]) s =
         OK (update_var dst w s)) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var out sf = SOME w /\ op_taint tnf (Var out) = {} /\
    op_prov Gf (Var out) = NONE /\
    sf.vs_memory = s.vs_memory /\ sf.vs_allocas = s.vs_allocas /\
    sf.vs_fmp = s.vs_fmp /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    sf.vs_requests = s.vs_requests /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    (!cenv cx es. stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa ==>
      stmt_state_rel ctx func cenv cx es sf)
Proof
  strip_tac >> drule_all emit_literal_numeric_counted >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  qexistsl_tac [`DRESTRICT G (COMPL {out})`,
    `tn with t_var := tn.t_var |+ (out,{})`,
    `update_var out w s with vs_inst_idx := LENGTH sb.cs_current_insts`] >>
  simp[numeric_endpoint_observations] >> conj_tac
  >- (rpt strip_tac >> `p <> out` by metis_tac[] >>
      simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_taint_def]) >>
  rpt strip_tac >> irule fresh_add_stmt_state_rel >> simp[] >> qexists_tac `sa` >>
  simp[] >> metis_tac[]
QED

(* The signed comparison is pure, but remains an actual counted edge. *)
Theory bodyPtrSubscriptSignedEdge
Ancestors
  bodyPtrSubscriptNumeric bodyPtrAttributeAdd bodyPtrDefs ptrSafeRun
  ptrDiscipline venomInst venomExecSemantics venomState finite_map
  emitHelperProps emitHelper compileEnv exprLoweringProps fragExec
  decoderGhostFramePtr words integer_word codegenRel contextCodegenRel
  bodyPtrSubscriptNamedTuplePostBoundary loweringPosts

Theorem slt_step:
  eval_operand left s = SOME a /\ eval_operand right s = SOME b ==>
  step_inst_base (mk_inst id SLT [left;right] [out]) s =
    OK (update_var out (bool_to_word (word_lt a b)) s)
Proof
  strip_tac >> simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def]
QED

Theorem slt_inst_check:
  (!op. MEM op ops ==> op_taint tn op = {}) /\ ~ctx_has_dalloca ctx /\
  step_inst_base (mk_inst id SLT ops [out]) s = OK t /\
  t.vs_requests = s.vs_requests ==>
  ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id SLT ops [out]) s
Proof
  strip_tac >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def] >>
  simp[GSYM mk_inst_def, step_inst_non_invoke, GSYM IMP_DISJ_THM]
QED

Theorem slt_ghost_frame:
  t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp ==>
  step_prov PG G (mk_inst id SLT [left;right] [out]) t =
    DRESTRICT G (COMPL {out}) /\
  step_taint (mk_inst id SLT [left;right] [out]) s t tn =
    (tn with t_var := tn.t_var |+ (out,{}))
Proof
  strip_tac >>
  `new_site_bytes s t = {}` by
    simp[new_site_bytes_def, FLOOKUP_DEF, pred_setTheory.EXTENSION, SF CONJ_ss] >>
  simp[step_prov_def, set_prov_def, out_prov_def, mk_inst_def,
       step_taint_def, set_var_taint_def, mem_taint_def, step_writes_def,
       source_memory_write_ranges_def, written_taint_def, store_taint_def,
       adopt_reset_def, imm_taint_def, range_bytes_def,
       taint_component_equality, DRESTRICT_UNIV, out_taint_def] >>
  Cases_on `eval_operand left s` >> simp[]
QED

Theorem emit_slt_counted:
  emit_op SLT [left;right] sa = (Var out,sb) /\ fn_has_code sa sb func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  (!dst. step_inst_base (mk_inst sa.cs_next_id SLT [left;right] [dst]) s =
         OK (update_var dst w s)) ==>
  gas_path_ptr D 0 ctx func PG G tn s 0
    (DRESTRICT G (COMPL {out})) (tn with t_var := tn.t_var |+ (out,{}))
    (OK ((update_var out w s) with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  sb.cs_current_bb = sa.cs_current_bb /\
  (!p. not_fresh_at sa p ==> p <> out)
Proof
  strip_tac >>
  `!dst. ptr_inst_ok D 0 0 ctx func G tn
      (mk_inst sa.cs_next_id SLT [left;right] [dst]) s` by
    (gen_tac >> irule slt_inst_check >> simp[update_var_def] >>
     rpt strip_tac >> gvs[]) >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def,
        fresh_var_def, fresh_id_def, emit_def, comp_return_def] >>
  drule emitted_insts_emit_op >> strip_tac >> gnvs[] >>
  `SLT <> INVOKE /\ SLT <> GAS /\ ~is_terminator SLT` by
    simp[is_terminator_def] >>
  drule_all attribute_emit_op_path_ptr >>
  disch_then (qspec_then `PG` mp_tac) >>
  simp[slt_ghost_frame, update_var_def, arithmeticTheory.ADD1] >>
  strip_tac >> simp[] >> rpt strip_tac >>
  gvs[not_fresh_at_def, step_prov_def, out_prov_def, set_prov_def, mk_inst_def]
QED

Theorem slt_counted_read_only:
  emit_op SLT [left;right] sa = (Var out,sb) /\ fn_has_code sa sb func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  (!dst. step_inst_base (mk_inst sa.cs_next_id SLT [left;right] [dst]) s =
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
  strip_tac >> drule_all emit_slt_counted >>
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

Theorem slt_nonnegative_index_step:
  eval_operand idx s = SOME w /\ 0 <= w2i w ==>
  step_inst_base (mk_inst id SLT [idx;Lit 0w] [out]) s =
    OK (update_var out 0w s)
Proof
  strip_tac >> drule slt_step >>
  disch_then (qspecl_then [`Lit 0w`, `out`, `id`, `0w`] mp_tac) >>
  simp[eval_operand_def, WORD_LTi, word_0_w2i, bool_to_word_def] >>
  `~(w2i w < 0)` by intLib.ARITH_TAC >> simp[]
QED

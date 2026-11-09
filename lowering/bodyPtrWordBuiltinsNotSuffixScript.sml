(* Not's word suffix accepts arbitrary input provenance.  The ghost
   transport below reuses the existing temporary-frame boundary. *)
Theory bodyPtrWordBuiltinsNotSuffix
Ancestors bodyPtrWordBuiltinsNegSuffix bodyPtrWordBuiltinsArithmeticSteps
  bodyPtrWordBuiltinsIntervalGhost bodyPtrDefs ptrSafeRun ptrDiscipline
  venomExecSemantics venomInst venomState venomExecProofs finite_map list
  exprLowering emitHelper compileEnv contextCodegenRel codegenRel
  fragGasSeqPtr fragGasPathPtr gasSummary vyperState emitHelperProps
  fragGasFresh fragGasSeqAbort freshWrites exprLoweringProps fragExec

Theorem word_not_ptr_safe_step:
  (!op. MEM op inst.inst_operands ==> op_taint tn op = {}) /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  MEM inst.inst_opcode [ISZERO; NOT; XOR] ==>
  ptr_safe_step D lo fuel ctx fn PG G tn inst s
Proof
  simp[MEM] >> strip_tac >>
  gvs[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
      source_memory_write_ranges_def, source_memory_read_ranges_def] >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac bool_ss [venomInstTheory.mk_inst_def, step_inst_base_opcode_eqs, venomInstTheory.instruction_accessors, venomInstTheory.instruction_accfupds, combinTheory.K_THM] >>
  asm_rewrite_tac[] >> pure_rewrite_tac[opcode_case_def] >>
  simp[exec_pure1_def, exec_pure2_def, AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem word_not_out_taint:
  MEM inst.inst_opcode [ISZERO; NOT; XOR] ==>
  out_taint tn inst s = {}
Proof
  simp[MEM] >> strip_tac >>
  (namedCases_on `inst.inst_operands` ["", "a rest"]
  >- simp[out_taint_def] >>
  namedCases_on `rest` ["", "b more"]
  >- (Cases_on `eval_operand a s` >> gvs[out_taint_def]) >>
  namedCases_on `more` ["", "c tail"]
  >- (Cases_on `eval_operand a s` >> gvs[out_taint_def]) >>
  Cases_on `tail` >> simp[out_taint_def])
QED

Theorem word_not_ghost_step:
  MEM opc [ISZERO; NOT; XOR] /\ new_site_bytes s t = {} ==>
  step_prov PG G (mk_inst id opc args [x]) t = set_prov G [x] NONE /\
  step_taint (mk_inst id opc args [x]) s t tn =
    tn with t_var := set_var_taint tn.t_var [x] {}
Proof
  strip_tac >>
  `out_taint tn (mk_inst id opc args [x]) s = {}` by
    (irule word_not_out_taint >> gvs[mk_inst_def]) >>
  gvs[MEM] >>
  simp[step_prov_def, mk_inst_def, out_prov_def, set_prov_def,
       step_taint_def, mem_taint_def, store_taint_def,
       adopt_reset_def, imm_taint_def, taint_component_equality,
       step_writes_def, source_memory_write_ranges_def, range_bytes_def] >>
  namedCases_on `args` ["", "a rest"] >> simp[written_taint_def] >>
  namedCases_on `rest` ["", "b more"] >> simp[written_taint_def] >>
  namedCases_on `more` ["", "c tail"] >> simp[written_taint_def] >>
  Cases_on `tail` >> simp[written_taint_def]
QED

Theorem word_not_output_frame:
  MEM opc [ISZERO; NOT; XOR] /\ ghost_inv d cenv cx es G tn s /\
  ghost_kept cenv es0 sc G0 tn0 s0 G tn /\
  (!n p sz. FLOOKUP cenv.ce_vars n = SOME (PtrVar (Var p) sz) ==> p <> x) /\
  (!p sz. d <> NONE /\ cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> p <> x) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> p <> x) /\
  (!p. not_fresh_at sc p ==> p <> x) ==>
  ghost_inv d cenv cx es
    (step_prov PG G (mk_inst id opc args [x]) (update_var x w s))
    (step_taint (mk_inst id opc args [x]) s (update_var x w s) tn)
    (update_var x w s) /\
  ghost_kept cenv es0 sc G0 tn0 s0
    (step_prov PG G (mk_inst id opc args [x]) (update_var x w s))
    (step_taint (mk_inst id opc args [x]) s (update_var x w s) tn) /\
  op_taint (step_taint (mk_inst id opc args [x]) s (update_var x w s) tn)
    (Var x) = {} /\
  op_prov (step_prov PG G (mk_inst id opc args [x]) (update_var x w s))
    (Var x) = NONE
Proof
  strip_tac >>
  `new_site_bytes s (update_var x w s) = {}` by
    simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF,
         pred_setTheory.EXTENSION, SF CONJ_ss] >>
  simp[word_not_ghost_step, step_prov_def, out_prov_def, mk_inst_def] >> conj_tac
  >- (irule word_neg_temp_ghost_inv >> simp[] >> metis_tac[]) >>
  conj_tac
  >- (irule word_neg_temp_ghost_kept >> simp[] >> metis_tac[]) >>
  simp[op_taint_def, set_var_taint_def, FLOOKUP_UPDATE,
    op_prov_def, set_prov_def, FLOOKUP_DRESTRICT] >>
  gvs[MEM] >> simp[FLOOKUP_DRESTRICT]
QED

Theorem word_not_normal_update:
  MEM opc [ISZERO; NOT; XOR] /\
  step_inst_base (mk_inst id opc args [x]) s = OK t ==>
  ?w. t = update_var x w s
Proof
  simp[MEM] >> strip_tac >>
  gvs[mk_inst_def] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[step_inst_base_opcode_eqs] >>
  simp[exec_pure1_def, exec_pure2_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >> metis_tac[]
QED

Theorem word_not_counted_step:
  MEM opc [ISZERO; NOT; XOR] /\
  (!arg. MEM arg args ==> op_taint tn arg = {}) /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id opc args [x]) /\
  step_inst_base (mk_inst id opc args [x]) s = OK t ==>
  gas_path_ptr D lo ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id opc args [x]) t)
    (step_taint (mk_inst id opc args [x]) s t tn)
    (OK (t with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `ptr_safe_step D lo 0 ctx fn PG G tn (mk_inst id opc args [x]) s` by
    (irule word_not_ptr_safe_step >> gvs[mk_inst_def, MEM]) >>
  `ptr_inst_ok D lo 0 ctx fn G tn (mk_inst id opc args [x]) s` by
    gvs[ptr_safe_step_def] >>
  `~t.vs_halted` by
    (drule_all word_not_normal_update >> strip_tac >> simp[update_var_def]) >>
  `gas_path_ptr D lo ctx fn PG
    (step_prov PG G (mk_inst id opc args [x]) t)
    (step_taint (mk_inst id opc args [x]) s t tn)
    (t with vs_inst_idx := SUC s.vs_inst_idx) 0
    (step_prov PG G (mk_inst id opc args [x]) t)
    (step_taint (mk_inst id opc args [x]) s t tn)
    (OK (t with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule (cj 1 gas_path_ptr_rules) >> simp[]) >>
  `opc <> INVOKE /\ ~is_terminator opc /\ opc <> GAS` by
    gvs[MEM, is_terminator_def] >>
  drule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`) gas_path_ptr_step >>
  simp[mk_inst_def] >> disch_then irule >> simp[GSYM mk_inst_def] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem word_not_counted_frame:
  MEM opc [ISZERO; NOT; XOR] /\
  (!arg. MEM arg args ==> op_taint tn arg = {}) /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id opc args [x]) /\
  step_inst_base (mk_inst id opc args [x]) s = OK t /\
  ghost_inv d cenv cx es G tn s /\ ghost_kept cenv es0 sc G0 tn0 s0 G tn /\
  (!n p sz. FLOOKUP cenv.ce_vars n = SOME (PtrVar (Var p) sz) ==> p <> x) /\
  (!p sz. d <> NONE /\ cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> p <> x) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> p <> x) /\
  (!p. not_fresh_at sc p ==> p <> x) ==>
  ?G' tn'. gas_path_ptr D lo ctx fn PG G tn s 0 G' tn'
    (OK (t with vs_inst_idx := SUC s.vs_inst_idx)) /\
    ghost_inv d cenv cx es G' tn' (t with vs_inst_idx := SUC s.vs_inst_idx) /\
    ghost_kept cenv es0 sc G0 tn0 s0 G' tn' /\ op_taint tn' (Var x) = {} /\
    op_prov G' (Var x) = NONE
Proof
  strip_tac >> drule_all word_not_counted_step >> strip_tac >>
  drule_all word_not_normal_update >>
  disch_then (qx_choose_then `w` SUBST_ALL_TAC) >>
  drule_all word_not_output_frame >>
  disch_then (qspecl_then [`w`, `id`, `args`, `PG`] strip_assume_tac) >>
  simp[word_interval_ghost_inv_index] >> metis_tac[]
QED

(* H retains the semantic post on this very runtime endpoint; it is not
   an erased-path witness.  A pure source suffix has no gas observations. *)
Theorem word_not_step_outcome:
  MEM opc [ISZERO; NOT; XOR] /\
  (!arg. MEM arg args ==> op_taint tn arg = {}) /\
  allocas_from 0 s /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id opc args [x]) /\
  step_inst_base (mk_inst id opc args [x]) s = OK t /\
  ghost_inv d cenv cx es G tn s /\ ghost_kept cenv es0 sc G0 tn0 s0 G tn /\
  (!n p sz. FLOOKUP cenv.ce_vars n = SOME (PtrVar (Var p) sz) ==> p <> x) /\
  (!p sz. d <> NONE /\ cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> p <> x) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> p <> x) /\
  (!p. not_fresh_at sc p ==> p <> x) /\
  (!tail. source (es with gas_obs := tail) = (res,es with gas_obs := tail)) /\
  H res (es with gas_obs := []) (t with vs_inst_idx := SUC s.vs_inst_idx) ==>
  gas_outcome_ptr D tops (ctx,fn) PG source (es,s,G,tn)
    (\r ee G' tn' u. H r ee u /\
      ghost_inv d cenv cx es G' tn' u /\
      ghost_kept cenv es0 sc G0 tn0 s0 G' tn' /\ op_taint tn' (Var x) = {} /\
    op_prov G' (Var x) = NONE) R
Proof
  strip_tac >> drule_all word_not_counted_frame >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  simp[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_ptr_at_def, gas_explicit_def] >>
  qexistsl_tac [`res`, `es`, `G'`, `tn'`,
    `OK (t with vs_inst_idx := SUC s.vs_inst_idx)`] >> simp[]
QED

Theorem word_not_emit_cursor:
  MEM opc [ISZERO; NOT; XOR] /\ emit_op opc args sa = (op,sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME
      (mk_inst sa.cs_next_id opc args [STRING #"%" (toString sa.cs_next_var)]) /\
    SUC s.vs_inst_idx = LENGTH sb.cs_current_insts /\
    sb.cs_current_bb = sa.cs_current_bb /\
    op = Var (STRING #"%" (toString sa.cs_next_var))
Proof
  strip_tac >>
  `straight_fresh (emit_op opc args)` by
    (irule straight_fresh_emit_op >> gvs[fresh_write_op_def, MEM]) >>
  drule_all straight_fresh_code_prefix >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  qpat_x_assum `isPREFIX _ _` mp_tac >> asm_rewrite_tac[] >>
  disch_then (strip_assume_tac o MATCH_MP instruction_prefix_cursor) >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    (gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
         comp_ignore_bind_def, comp_return_def, emit_def]) >>
  qexists_tac `bb` >> simp[]
QED

Theorem word_not_emit_outcome:
  MEM opc [ISZERO; NOT; XOR] /\ emit_op opc args sa = (op,sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!arg. MEM arg args ==> op_taint tn arg = {}) /\
  allocas_from 0 s /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  step_inst_base
    (mk_inst sa.cs_next_id opc args [STRING #"%" (toString sa.cs_next_var)]) s = OK t /\
  ghost_inv d cenv cx es G tn s /\ ghost_kept cenv es0 sc G0 tn0 s0 G tn /\
  local_ptrs_reserved cenv sc /\ sc.cs_next_var <= sa.cs_next_var /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sc p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sc p) /\
  (!tail. source (es with gas_obs := tail) = (res,es with gas_obs := tail)) /\
  H res (es with gas_obs := []) (t with vs_inst_idx := LENGTH sb.cs_current_insts) ==>
  gas_outcome_ptr D tops (ctx,fn) PG source (es,s,G,tn)
    (\r ee G' tn' u. H r ee u /\
      ghost_inv d cenv cx es G' tn' u /\
      ghost_kept cenv es0 sc G0 tn0 s0 G' tn' /\ op_taint tn' op = {} /\
      op_prov G' op = NONE) R
Proof
  strip_tac >> drule_all word_not_emit_cursor >> strip_tac >>
  asm_rewrite_tac[] >> irule word_not_step_outcome >> simp[] >>
  fs[local_ptrs_reserved_def, not_fresh_at_def, MEM] >> metis_tac[]
QED

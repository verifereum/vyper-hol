(* Modular suffixes clear provenance, even for operands carrying provenance. *)
Theory bodyPtrWordBuiltinsModular
Ancestors bodyPtrWordBuiltinsArithmeticSteps bodyPtrWordBuiltinsNegSuffix
  bodyPtrWordBuiltinsAbsSequence exprSimWordBuiltins builtinMath
  exprLoweringProps compileEnv emitHelper fragGasSeqPtr
  venomExecSemantics venomInst venomState ptrDiscipline ptrSafeRun
  list rich_list finite_map bodyPtrDefs venomExecProofs decoderGhostFramePtr codegenRel
  bodyPtrWordBuiltinsIntervalGhost instIdxIndep fragExec fragGasPathPtr gasSummary
  exprSimDefs

Theorem word_pow_emitted_insts:
  compile_pow_mod256 a b sa = (op,sb) ==>
  emitted_insts sa sb =
    [mk_inst sa.cs_next_id Exp [a;b]
      [STRING #"%" (toString sa.cs_next_var)]] /\
  op = Var (STRING #"%" (toString sa.cs_next_var))
Proof
  simp[compile_pow_mod256_def, emit_op_def, comp_bind_def, comp_ignore_bind_def,
       fresh_id_def, fresh_var_def, emit_def, comp_return_def] >>
  strip_tac >> gvs[emitted_insts_def] >> simp[DROP_LENGTH_APPEND]
QED

Theorem word_modular_emitted_insts:
  (if is_mul then compile_mulmod else compile_addmod) a b c sa = (op,sb) ==>
  emitted_insts sa sb =
    [mk_inst sa.cs_next_id ASSERT [c] [];
     mk_inst (sa.cs_next_id + 1) (if is_mul then MULMOD else ADDMOD) [a;b;c]
       [STRING #"%" (toString sa.cs_next_var)]] /\
  op = Var (STRING #"%" (toString sa.cs_next_var))
Proof
  Cases_on `is_mul` >>
  simp[compile_addmod_def, compile_mulmod_def, emit_op_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, fresh_id_def, fresh_var_def,
       emit_def, comp_return_def] >>
  strip_tac >> gvs[emitted_insts_def] >> simp[DROP_LENGTH_APPEND]
QED

Theorem word_modular_inst_ok:
  MEM inst.inst_opcode [Exp; ADDMOD; MULMOD; ASSERT] /\
  (!arg. MEM arg inst.inst_operands ==> op_taint tn arg = {}) /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D lo 0 ctx fn G tn inst s
Proof
  strip_tac >>
  `ptr_safe_step D lo 0 ctx fn PG G tn inst s` by
    (irule word_arithmetic_ptr_safe_step >> gvs[MEM]) >>
  gvs[ptr_safe_step_def]
QED

Theorem word_pow_emitted_checked:
  compile_pow_mod256 a b sa = (op,sb) /\
  op_taint tn a = {} /\ op_taint tn b = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  ?G' tn'. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s G' tn'
Proof
  strip_tac >> drule word_pow_emitted_insts >> strip_tac >>
  asm_rewrite_tac[] >>
  `ptr_inst_ok D lo 0 ctx fn G tn
    (mk_inst sa.cs_next_id Exp [a;b] [STRING #"%" (toString sa.cs_next_var)]) s` by
    (irule word_modular_inst_ok >> simp[mk_inst_def] >> metis_tac[]) >>
  simp[Once inst_seq_ptr_def] >>
  Cases_on `step_inst_base
    (mk_inst sa.cs_next_id Exp [a;b] [STRING #"%" (toString sa.cs_next_var)]) s` >>
  simp[inst_seq_ptr_def]
QED

Theorem word_modular_emitted_checked:
  (if is_mul then compile_mulmod else compile_addmod) a b c sa = (op,sb) /\
  op_taint tn a = {} /\ op_taint tn b = {} /\ op_taint tn c = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  ?G' tn'. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s G' tn'
Proof
  strip_tac >> drule word_modular_emitted_insts >> strip_tac >>
  asm_rewrite_tac[] >>
  `ptr_inst_ok D lo 0 ctx fn G tn (mk_inst sa.cs_next_id ASSERT [c] []) s` by
    (irule word_modular_inst_ok >> simp[mk_inst_def]) >>
  simp[Once inst_seq_ptr_def] >>
  Cases_on `step_inst_base (mk_inst sa.cs_next_id ASSERT [c] []) s` >> simp[] >>
  `v = s /\ step_prov PG G (mk_inst sa.cs_next_id ASSERT [c] []) v = G /\
   step_taint (mk_inst sa.cs_next_id ASSERT [c] []) s v tn = tn` by
    (irule word_abs_assert_normal >> simp[mk_inst_def]) >>
  gvs[] >>
  `ptr_inst_ok D lo 0 ctx fn G tn
    (mk_inst (sa.cs_next_id + 1) (if is_mul then MULMOD else ADDMOD) [a;b;c]
      [STRING #"%" (toString sa.cs_next_var)]) (s with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule word_modular_inst_ok >> Cases_on `is_mul` >>
     gvs[mk_inst_def, allocas_from_def] >> metis_tac[]) >>
  simp[Once inst_seq_ptr_def] >>
  Cases_on `step_inst_base
    (mk_inst (sa.cs_next_id + 1) (if is_mul then MULMOD else ADDMOD) [a;b;c]
      [STRING #"%" (toString sa.cs_next_var)]) (s with vs_inst_idx := SUC s.vs_inst_idx)` >>
  simp[inst_seq_ptr_def]
QED

Theorem word_pow_emitted_shape:
  compile_pow_mod256 a b sa = (op,sb) ==>
  LENGTH (emitted_insts sa sb) = 1 /\
  FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = [] /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)
Proof
  strip_tac >> drule word_pow_emitted_insts >> strip_tac >>
  simp[mk_inst_def, is_terminator_def]
QED

Theorem word_modular_emitted_shape:
  (if is_mul then compile_mulmod else compile_addmod) a b c sa = (op,sb) ==>
  LENGTH (emitted_insts sa sb) = 2 /\
  FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = [] /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)
Proof
  strip_tac >> drule word_modular_emitted_insts >> strip_tac >>
  Cases_on `is_mul` >> simp[mk_inst_def, is_terminator_def]
QED

Theorem word_pow_counted_normal:
  compile_pow_mod256 a b sa = (op,sb) /\
  eval_operand a s = SOME va /\ eval_operand b s = SOME vb /\
  op_taint tn a = {} /\ op_taint tn b = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t G' tn'.
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s G' tn' /\
    gas_path_ptr D lo ctx fn PG G tn s 0 G' tn'
      (OK (t with vs_inst_idx := s.vs_inst_idx + 1)) /\
    eval_operand op t = SOME (word_exp va vb)
Proof
  strip_tac >> drule_all compile_pow_mod256_run >> strip_tac >>
  drule_all word_pow_emitted_checked >>
  disch_then (qspecl_then [`fn`, `PG`, `G`, `D`] strip_assume_tac) >>
  drule word_pow_emitted_shape >> strip_tac >>
  drule_all run_inst_seq_gas_path_ptr >> simp[] >> metis_tac[]
QED

Theorem word_modular_counted_normal:
  (if is_mul then compile_mulmod else compile_addmod) a b c sa = (op,sb) /\
  eval_operand a s = SOME va /\ eval_operand b s = SOME vb /\
  eval_operand c s = SOME vc /\ vc <> 0w /\
  op_taint tn a = {} /\ op_taint tn b = {} /\ op_taint tn c = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t G' tn'.
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s G' tn' /\
    gas_path_ptr D lo ctx fn PG G tn s 0 G' tn'
      (OK (t with vs_inst_idx := s.vs_inst_idx + 2)) /\
    eval_operand op t = SOME ((if is_mul then mulmod else addmod) va vb vc)
Proof
  strip_tac >> drule_all compile_modular_run >> simp[] >> strip_tac >>
  drule_all word_modular_emitted_checked >>
  disch_then (qspecl_then [`fn`, `PG`, `G`, `D`] strip_assume_tac) >>
  drule word_modular_emitted_shape >> strip_tac >>
  drule_all run_inst_seq_gas_path_ptr >> simp[] >> metis_tac[]
QED

Theorem word_modular_counted_abort:
  (if is_mul then compile_mulmod else compile_addmod) a b c sa = (op,sb) /\
  eval_operand a s = SOME va /\ eval_operand b s = SOME vb /\
  eval_operand c s = SOME 0w /\
  op_taint tn a = {} /\ op_taint tn b = {} /\ op_taint tn c = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t G' tn' n. gas_path_ptr D lo ctx fn PG G tn s n G' tn'
    (Abort Revert_abort t)
Proof
  strip_tac >> drule_all compile_modular_run >> simp[] >> strip_tac >>
  drule_all word_modular_emitted_checked >>
  disch_then (qspecl_then [`fn`, `PG`, `G`, `D`] strip_assume_tac) >>
  drule word_modular_emitted_shape >> strip_tac >>
  drule_all run_inst_seq_abort_gas_path_ptr >> metis_tac[]
QED

Theorem word_modular_ghost_step:
  MEM opc [Exp; ADDMOD; MULMOD] /\ new_site_bytes s t = {} ==>
  step_prov PG G (mk_inst id opc args [x]) t = set_prov G [x] NONE /\
  step_taint (mk_inst id opc args [x]) s t tn =
    tn with t_var := set_var_taint tn.t_var [x] {}
Proof
  strip_tac >>
  `out_taint tn (mk_inst id opc args [x]) s = {}` by
    (irule word_arithmetic_out_taint >> gvs[mk_inst_def, MEM]) >>
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

Theorem word_modular_normal_update:
  MEM opc [Exp; ADDMOD; MULMOD] /\
  step_inst_base (mk_inst id opc args [x]) s = OK t ==>
  ?w. t = update_var x w s
Proof
  simp[MEM] >> strip_tac >>
  gvs[mk_inst_def] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  pure_rewrite_tac[instruction_accfupds, instruction_accessors, combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure2_def, exec_pure3_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >> metis_tac[]
QED

Theorem word_modular_output_frame:
  MEM opc [Exp; ADDMOD; MULMOD] /\
  step_inst_base (mk_inst id opc args [x]) s = OK t /\
  ghost_inv d cenv cx es G tn s /\ ghost_kept cenv es0 sc G0 tn0 s0 G tn /\
  (!n p sz. FLOOKUP cenv.ce_vars n = SOME (PtrVar (Var p) sz) ==> p <> x) /\
  (!p sz. d <> NONE /\ cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> p <> x) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> p <> x) /\
  (!p. not_fresh_at sc p ==> p <> x) ==>
  ghost_inv d cenv cx es (step_prov PG G (mk_inst id opc args [x]) t)
    (step_taint (mk_inst id opc args [x]) s t tn) t /\
  ghost_kept cenv es0 sc G0 tn0 s0 (step_prov PG G (mk_inst id opc args [x]) t)
    (step_taint (mk_inst id opc args [x]) s t tn) /\
  op_taint (step_taint (mk_inst id opc args [x]) s t tn) (Var x) = {} /\
  op_prov (step_prov PG G (mk_inst id opc args [x]) t) (Var x) = NONE
Proof
  strip_tac >> drule_all word_modular_normal_update >>
  disch_then (qx_choose_then `w` SUBST_ALL_TAC) >>
  `new_site_bytes s (update_var x w s) = {}` by
    simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF,
         pred_setTheory.EXTENSION, SF CONJ_ss] >>
  simp[word_modular_ghost_step, step_prov_def, out_prov_def, mk_inst_def] >>
  conj_tac
  >- (irule word_neg_temp_ghost_inv >> simp[] >> metis_tac[]) >>
  conj_tac
  >- (irule word_neg_temp_ghost_kept >> simp[] >> metis_tac[]) >>
  simp[op_taint_def, set_var_taint_def, FLOOKUP_UPDATE,
       op_prov_def, set_prov_def, FLOOKUP_DRESTRICT] >>
  gvs[MEM] >> simp[FLOOKUP_DRESTRICT]
QED

Theorem word_modular_single_frame:
  MEM opc [Exp; ADDMOD; MULMOD] /\
  inst_seq_ptr D lo ctx fn PG G tn [mk_inst id opc args [x]] s G' tn' /\
  run_inst_seq [mk_inst id opc args [x]] s = OK t /\
  ghost_inv d cenv cx es G tn s /\ ghost_kept cenv es0 sc G0 tn0 s0 G tn /\
  (!n p sz. FLOOKUP cenv.ce_vars n = SOME (PtrVar (Var p) sz) ==> p <> x) /\
  (!p sz. d <> NONE /\ cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> p <> x) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> p <> x) /\
  (!p. not_fresh_at sc p ==> p <> x) ==>
  ghost_inv d cenv cx es G' tn' t /\
  ghost_kept cenv es0 sc G0 tn0 s0 G' tn' /\
  op_taint tn' (Var x) = {} /\ op_prov G' (Var x) = NONE
Proof
  strip_tac >>
  `~is_terminator opc` by gvs[MEM, is_terminator_def] >>
  qpat_x_assum `run_inst_seq _ _ = OK t` mp_tac >>
  simp[Once run_inst_seq_def] >>
  Cases_on `step_inst_base (mk_inst id opc args [x]) s` >>
  simp[run_inst_seq_def] >> strip_tac >>
  gvs[Once inst_seq_ptr_def] >>
  gvs[inst_seq_ptr_def] >>
  simp[word_interval_ghost_inv_index] >>
  irule word_modular_output_frame >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem word_modular_pair_frame:
  MEM opc [ADDMOD; MULMOD] /\
  inst_seq_ptr D lo ctx fn PG G tn
    [mk_inst id ASSERT [c] []; mk_inst (id + 1) opc args [x]] s G' tn' /\
  run_inst_seq [mk_inst id ASSERT [c] []; mk_inst (id + 1) opc args [x]] s = OK t /\
  ghost_inv d cenv cx es G tn s /\ ghost_kept cenv es0 sc G0 tn0 s0 G tn /\
  (!n p sz. FLOOKUP cenv.ce_vars n = SOME (PtrVar (Var p) sz) ==> p <> x) /\
  (!p sz. d <> NONE /\ cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> p <> x) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> p <> x) /\
  (!p. not_fresh_at sc p ==> p <> x) ==>
  ghost_inv d cenv cx es G' tn' t /\
  ghost_kept cenv es0 sc G0 tn0 s0 G' tn' /\
  op_taint tn' (Var x) = {} /\ op_prov G' (Var x) = NONE
Proof
  strip_tac >>
  qpat_x_assum `run_inst_seq _ _ = OK t` mp_tac >>
  simp[Once run_inst_seq_def] >>
  Cases_on `step_inst_base (mk_inst id ASSERT [c] []) s` >> simp[] >> strip_tac >>
  `v = s /\ step_prov PG G (mk_inst id ASSERT [c] []) v = G /\
   step_taint (mk_inst id ASSERT [c] []) s v tn = tn` by
    (irule word_abs_assert_normal >> simp[mk_inst_def]) >>
  gnvs[] >>
  qpat_x_assum `inst_seq_ptr _ _ _ _ _ _ _ (_::_) _ _ _` mp_tac >>
  simp[Once inst_seq_ptr_def] >> strip_tac >>
  `run_inst_seq [mk_inst (id + 1) opc args [x]]
     (s with vs_inst_idx := SUC s.vs_inst_idx) =
     OK (t with vs_inst_idx := SUC s.vs_inst_idx)` by
    ( `EVERY (\i. ~is_terminator i.inst_opcode) [mk_inst (id + 1) opc args [x]]` by
        gvs[mk_inst_def, is_terminator_def] >>
      simp[run_inst_seq_inst_idx, exec_result_map_def]) >>
  `ghost_inv d cenv cx es G' tn' (t with vs_inst_idx := SUC s.vs_inst_idx) /\
   ghost_kept cenv es0 sc G0 tn0 s0 G' tn' /\
   op_taint tn' (Var x) = {} /\ op_prov G' (Var x) = NONE` by
    (irule word_modular_single_frame >> simp[] >>
     goal_assum (drule_at Any) >> simp[word_interval_ghost_inv_index] >> metis_tac[]) >>
  gvs[word_interval_ghost_inv_index]
QED

(* H is a post of this actual run, not of an independently erased path. *)
Theorem word_pow_suffix_outcome:
  (?bb va vb res. compile_pow_mod256 a b sa = (op,sb) /\
  eval_operand a s = SOME va /\ eval_operand b s = SOME vb /\
  op_taint tn a = {} /\ op_taint tn b = {} /\
  allocas_from 0 s /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  ghost_inv d cenv cx es G tn s /\ ghost_kept cenv es0 sc G0 tn0 s0 G tn /\
  (!n p sz. FLOOKUP cenv.ce_vars n = SOME (PtrVar (Var p) sz) ==>
    p <> STRING #"%" (toString sa.cs_next_var)) /\
  (!p sz. d <> NONE /\ cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==>
    p <> STRING #"%" (toString sa.cs_next_var)) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==>
    p <> STRING #"%" (toString sa.cs_next_var)) /\
  (!p. not_fresh_at sc p ==> p <> STRING #"%" (toString sa.cs_next_var)) /\
  (!tail. source (es with gas_obs := tail) = (res,es with gas_obs := tail)) /\
  (!t. run_inst_seq (emitted_insts sa sb) s = OK t ==>
    H res (es with gas_obs := []) (t with vs_inst_idx := s.vs_inst_idx + 1))) ==>
  gas_outcome_ptr D tops (ctx,fn) PG source (es,s,G,tn)
    (\r ee G' tn' u. H r ee u /\ ghost_inv d cenv cx es G' tn' u /\
      ghost_kept cenv es0 sc G0 tn0 s0 G' tn' /\
      op_taint tn' op = {} /\ op_prov G' op = NONE) R
Proof
  strip_tac >> drule_all word_pow_counted_normal >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  drule word_pow_emitted_insts >> strip_tac >>
  `ghost_inv d cenv cx es G' tn' t /\
   ghost_kept cenv es0 sc G0 tn0 s0 G' tn' /\
   op_taint tn' op = {} /\ op_prov G' op = NONE` by
    (gnvs[] >> irule word_modular_single_frame >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  simp[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_ptr_at_def, gas_explicit_def] >>
  qexistsl_tac [`res`, `es`, `G'`, `tn'`,
    `OK (t with vs_inst_idx := s.vs_inst_idx + 1)`] >>
  gvs[word_interval_ghost_inv_index]
QED

Theorem word_modular_suffix_outcome:
  (?bb va vb vc res. (if is_mul then compile_mulmod else compile_addmod) a b c sa = (op,sb) /\
  eval_operand a s = SOME va /\ eval_operand b s = SOME vb /\
  eval_operand c s = SOME vc /\ vc <> 0w /\
  op_taint tn a = {} /\ op_taint tn b = {} /\ op_taint tn c = {} /\
  allocas_from 0 s /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  ghost_inv d cenv cx es G tn s /\ ghost_kept cenv es0 sc G0 tn0 s0 G tn /\
  (!n p sz. FLOOKUP cenv.ce_vars n = SOME (PtrVar (Var p) sz) ==>
    p <> STRING #"%" (toString sa.cs_next_var)) /\
  (!p sz. d <> NONE /\ cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==>
    p <> STRING #"%" (toString sa.cs_next_var)) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==>
    p <> STRING #"%" (toString sa.cs_next_var)) /\
  (!p. not_fresh_at sc p ==> p <> STRING #"%" (toString sa.cs_next_var)) /\
  (!tail. source (es with gas_obs := tail) = (res,es with gas_obs := tail)) /\
  (!t. run_inst_seq (emitted_insts sa sb) s = OK t ==>
    H res (es with gas_obs := []) (t with vs_inst_idx := s.vs_inst_idx + 2))) ==>
  gas_outcome_ptr D tops (ctx,fn) PG source (es,s,G,tn)
    (\r ee G' tn' u. H r ee u /\ ghost_inv d cenv cx es G' tn' u /\
      ghost_kept cenv es0 sc G0 tn0 s0 G' tn' /\
      op_taint tn' op = {} /\ op_prov G' op = NONE) R
Proof
  strip_tac >> drule_all word_modular_counted_normal >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  drule word_modular_emitted_insts >> strip_tac >>
  `ghost_inv d cenv cx es G' tn' t /\
   ghost_kept cenv es0 sc G0 tn0 s0 G' tn' /\
   op_taint tn' op = {} /\ op_prov G' op = NONE` by
    (gnvs[] >> irule word_modular_pair_frame >> simp[] >>
     goal_assum (drule_at Any) >> Cases_on `is_mul` >> simp[] >> metis_tac[]) >>
  simp[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_ptr_at_def, gas_explicit_def] >>
  qexistsl_tac [`res`, `es`, `G'`, `tn'`,
    `OK (t with vs_inst_idx := s.vs_inst_idx + 2)`] >>
  gvs[word_interval_ghost_inv_index]
QED

Theorem word_modular_abort_outcome:
  (?bb va vb msg. (if is_mul then compile_mulmod else compile_addmod) a b c sa = (op,sb) /\
  eval_operand a s = SOME va /\ eval_operand b s = SOME vb /\
  eval_operand c s = SOME 0w /\
  op_taint tn a = {} /\ op_taint tn b = {} /\ op_taint tn c = {} /\
  allocas_from 0 s /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  (!tail. source (es with gas_obs := tail) =
    (INR (Error (RuntimeError msg)), es with gas_obs := tail))) ==>
  gas_outcome_ptr D tops (ctx,fn) PG source (es,s,G,tn)
    Q (\res fin gt r. expr_exit res r)
Proof
  strip_tac >> drule_all word_modular_counted_abort >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  simp[gas_outcome_ptr_def] >> qexists_tac `REPLICATE n F` >> disj1_tac >>
  simp[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INR (Error (RuntimeError msg))`, `es`, `G'`, `tn'`,
    `Abort Revert_abort t`] >>
  simp[expr_exit_def, exit_result_def]
QED

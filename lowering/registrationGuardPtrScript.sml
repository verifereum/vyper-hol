(* The calldata pointer guard (LT; ISZERO; ASSERT) of a dynamic argument,
   on the pointer side: when it passes it only defines its two fresh test
   variables, with clean ghosts, and pointer safety of the run after it
   gives pointer safety of the run through it. *)
Theory registrationGuardPtr
Ancestors
  calldataClampPtr calldataRegistrationExec moduleLowering abiDecoderLoopRegisters
  emitHelperProps
  abiDecoderClamp abiEncoder compileEnv loweringStateRelDefs emitHelper exprLoweringProps
  fragExec venomInst list arithmetic words bodyPtrDefs decoderGhostFramePtr
  ptrDiscipline ptrSafeRun venomState venomExecSemantics entryDispatchPtr
  fragExecPtr ghostPcTransportPtr finite_map pred_set codegenRel instIdxIndep contextCodegenRel

(* ===== Clean scalar steps, with LT ===== *)

Theorem guard_scalar_step_safe[local]:
  MEM opc [LT; ISZERO; ASSERT] /\
  EVERY (\op. op_taint tn op = {} /\ op_prov G op = NONE) ops /\
  step_inst fuel ctx (mk_inst id opc ops outs) s = OK t /\
  t.vs_requests = s.vs_requests /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  ptr_safe_step D lo fuel ctx fn PG G tn (mk_inst id opc ops outs) s
Proof
  strip_tac >>
  `!op. MEM op ops ==> op_taint tn op = {}` by gvs[EVERY_MEM] >>
  `!u. MEM (Var u) ops ==> u NOTIN FDOM G` by
    (gvs[EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `!op. MEM op ops ==> op_prov G op = NONE`
       (qspec_then `Var u` mp_tac) >>
     simp[op_prov_def, FLOOKUP_DEF]) >>
  fs[MEM] >>
  gvs[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
      mk_inst_def, source_memory_write_ranges_def,
      source_memory_read_ranges_def] >> metis_tac[MEM]
QED

Theorem guard_scalar_out_taint[local]:
  MEM opc [LT; ISZERO; ASSERT] /\
  EVERY (\op. op_taint tn op = {}) ops ==>
  out_taint tn (mk_inst id opc ops outs) s = {}
Proof
  strip_tac >> fs[MEM] >>
  (namedCases_on `ops` ["", "a rest"]
  >- simp[out_taint_def, mk_inst_def] >>
  namedCases_on `rest` ["", "b more"]
  >- (Cases_on `eval_operand a s` >> gvs[out_taint_def, mk_inst_def]) >>
  namedCases_on `more` ["", "c tail"]
  >- (Cases_on `eval_operand a s` >>
      gvs[out_taint_def, mk_inst_def, shift_taint_def, EXTENSION]) >>
  Cases_on `tail` >> simp[out_taint_def, mk_inst_def])
QED

Theorem guard_scalar_output_ghost[local]:
  MEM opc [LT; ISZERO; ASSERT] /\
  EVERY (\op. op_taint tn op = {}) ops ==>
  op_prov (step_prov PG G (mk_inst id opc ops [out]) t) (Var out) = NONE /\
  op_taint (step_taint (mk_inst id opc ops [out]) s t tn) (Var out) = {}
Proof
  strip_tac >> drule_all guard_scalar_out_taint >> strip_tac >>
  simp[op_taint_def, step_taint_def, mk_inst_def, set_var_taint_def,
       FLOOKUP_UPDATE] >>
  fs[MEM] >> simp[op_prov_def, step_prov_def, out_prov_def,
    set_prov_def, mk_inst_def, FLOOKUP_DRESTRICT]
QED

Theorem guard_scalar_state_frame[local]:
  MEM opc [LT; ISZERO; ASSERT] /\
  step_inst_base (mk_inst id opc ops outs) s = OK t ==>
  ?vars. t = s with vs_vars := vars
Proof
  strip_tac >> fs[MEM] >> gvs[] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [mk_inst_def] >>
  simp_tac bool_ss [step_inst_base_opcode_eqs, instruction_accessors,
                    instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure2_def, exec_pure1_def, AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[] >> simp[venom_state_component_equality]
QED

Theorem guard_scalar_taint_frame[local]:
  MEM opc [LT; ISZERO; ASSERT] /\
  step_inst_base (mk_inst id opc ops outs) s = OK t ==>
  (step_taint (mk_inst id opc ops outs) s t tn).t_mem = tn.t_mem /\
  (step_taint (mk_inst id opc ops outs) s t tn).t_stor = tn.t_stor /\
  (step_taint (mk_inst id opc ops outs) s t tn).t_trans = tn.t_trans /\
  (step_taint (mk_inst id opc ops outs) s t tn).t_imm = tn.t_imm
Proof
  strip_tac >> drule_all guard_scalar_state_frame >> strip_tac >>
  gvs[] >> fs[MEM] >>
  simp[step_taint_def, mem_taint_def, new_site_bytes_def,
       step_writes_def, written_taint_def, mk_inst_def,
       source_memory_write_ranges_def, adopt_reset_def,
       store_taint_def, imm_taint_def, range_bytes_def, FLOOKUP_DEF,
       EXTENSION, SF CONJ_ss] >>
  namedCases_on `ops` ["", "a rest"] >> simp[] >>
  namedCases_on `rest` ["", "b more"] >> simp[] >>
  namedCases_on `more` ["", "c tail"] >> simp[] >>
  Cases_on `tail` >> simp[]
QED

Theorem guard_scalar_continuation[local]:
  MEM opc [LT; ISZERO; ASSERT] /\
  EVERY (\op. op_taint tn op = {} /\ op_prov G op = NONE) ops /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id opc ops outs) /\
  step_inst_base (mk_inst id opc ops outs) s = OK t /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  (!fuel. ptr_safe_run D lo fuel ctx fn PG
    (step_prov PG G (mk_inst id opc ops outs) t)
    (step_taint (mk_inst id opc ops outs) s t tn)
    (t with vs_inst_idx := SUC s.vs_inst_idx)) ==>
  !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s
Proof
  strip_tac >>
  `?vars. t = s with vs_vars := vars` by metis_tac[guard_scalar_state_frame] >>
  `opc <> INVOKE /\ ~is_terminator opc` by (fs[MEM, is_terminator_def]) >>
  `!fuel. step_inst fuel ctx (mk_inst id opc ops outs) s = OK t` by
    simp[step_inst_non_invoke, mk_inst_def] >>
  gen_tac >> irule ptr_safe_run_scalar_continuation >>
  qexistsl_tac [`bb`, `mk_inst id opc ops outs`, `t`] >>
  simp[mk_inst_def] >>
  irule (SRULE [mk_inst_def] guard_scalar_step_safe) >>
  simp[GSYM mk_inst_def] >> fs[MEM]
QED

Theorem guard_scalar_indexed_continuation[local]:
  MEM opc [LT; ISZERO; ASSERT] /\
  EVERY (\op. op_taint tn op = {} /\ op_prov G op = NONE) ops /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb n = SOME (mk_inst id opc ops outs) /\
  step_inst_base (mk_inst id opc ops outs) s = OK t /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  (!fuel. ptr_safe_run D lo fuel ctx fn PG
    (step_prov PG G (mk_inst id opc ops outs) t)
    (step_taint (mk_inst id opc ops outs) s t tn)
    (t with vs_inst_idx := SUC n)) ==>
  !fuel. ptr_safe_run D lo fuel ctx fn PG G tn (s with vs_inst_idx := n)
Proof
  strip_tac >>
  `opc <> INVOKE /\ ~is_terminator opc` by fs[MEM, is_terminator_def] >>
  `~is_terminator (mk_inst id opc ops outs).inst_opcode` by simp[mk_inst_def] >>
  `step_inst_base (mk_inst id opc ops outs) (s with vs_inst_idx := n) =
     OK (t with vs_inst_idx := n)` by
    simp[step_inst_inst_idx_indep, exec_result_map_def] >>
  irule guard_scalar_continuation >>
  simp_tac (srw_ss()) [allocas_from_def] >>
  asm_rewrite_tac[GSYM allocas_from_def] >>
  goal_assum $ drule_at (Pat `get_instruction`) >>
  qexists_tac `t with vs_inst_idx := n` >>
  simp[step_prov_inst_idx, step_taint_inst_idx] >>
  fs[MEM]
QED

(* ===== The guard ===== *)

Theorem registration_ptr_guard_insts[local]:
  compile_abi_arg_ptr_guard CALLDATALOAD src (Lit 4w) sa = ((),sb) ==>
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_next_var = sa.cs_next_var + 2 /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  emitted_insts sa sb =
    [mk_inst sa.cs_next_id LT [src; Lit 4w] ["%" ++ toString sa.cs_next_var];
     mk_inst (sa.cs_next_id + 1) ISZERO [Var ("%" ++ toString sa.cs_next_var)]
       ["%" ++ toString (sa.cs_next_var + 1)];
     mk_inst (sa.cs_next_id + 2) ASSERT
       [Var ("%" ++ toString (sa.cs_next_var + 1))] []]
Proof
  simp[compile_abi_arg_ptr_guard_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, emit_inst_def,
       fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def, APPEND_ASSOC, DROP_PREFIX]
QED

(* A passing guard, run from the end of its code's predecessor. *)
Theorem registration_ptr_guard_ptr_frame:
  compile_abi_arg_ptr_guard CALLDATALOAD src (Lit 4w) sa = ((),sb) /\
  eval_operand src s = SOME w /\ ~(w <+ 4w) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  op_taint tn src = {} /\ op_prov G src = NONE /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\ fresh_vars_wrt sa s /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?vars G' tn'.
    fresh_vars_wrt sb (s with vs_vars := vars) /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP vars x = FLOOKUP s.vs_vars x /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG G' tn'
        (s with <|vs_vars := vars; vs_inst_idx := LENGTH sb.cs_current_insts|>)) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >> drule registration_ptr_guard_insts >> strip_tac >>
  qabbrev_tac `v0 = "%" ++ toString sa.cs_next_var` >>
  qabbrev_tac `v1 = "%" ++ toString (sa.cs_next_var + 1)` >>
  qabbrev_tac `i0 = mk_inst sa.cs_next_id LT [src; Lit 4w] [v0]` >>
  qabbrev_tac `i1 = mk_inst (sa.cs_next_id + 1) ISZERO [Var v0] [v1]` >>
  qabbrev_tac `i2 = mk_inst (sa.cs_next_id + 2) ASSERT [Var v1] []` >>
  `~(w2n w < w2n (4w:bytes32))` by metis_tac[WORD_LO] >>
  qabbrev_tac `s1 = update_var v0 0w s` >>
  qabbrev_tac `s2 = update_var v1 1w s1` >>
  `step_inst_base i0 s = OK s1` by
    (qpat_x_assum `~(w2n w < w2n _)` mp_tac >>
     qspecl_then [`src`, `Lit 4w`, `w`, `4w`, `sa.cs_next_id`, `v0`, `s`]
       mp_tac step_LT >>
     simp[eval_operand_def, bool_to_word_def, Abbr `i0`, Abbr `s1`]) >>
  `step_inst_base i1 s1 = OK s2` by
    (qspecl_then [`Var v0`, `0w`, `sa.cs_next_id + 1`, `v1`, `s1`]
       mp_tac step_ISZERO >>
     simp[eval_operand_def, bool_to_word_def, Abbr `i1`, Abbr `s2`, Abbr `s1`,
          lookup_var_update_var]) >>
  `step_inst_base i2 s2 = OK s2` by
    (simp[Abbr `i2`] >> irule step_ASSERT_ok >> qexists_tac `1w` >>
     simp[eval_operand_def, Abbr `s2`, lookup_var_update_var]) >>
  `src <> Var v0 /\ src <> Var v1` by
    (rpt strip_tac >> qpat_x_assum `!x. src = Var x ==> _` drule >>
     simp[not_fresh_at_def, Abbr `v0`, Abbr `v1`]) >>
  `!x. not_fresh_at sa x ==> x <> v0 /\ x <> v1` by
    (simp[not_fresh_at_def, Abbr `v0`, Abbr `v1`] >>
     metis_tac[LESS_EQ_REFL, arithmeticTheory.LESS_EQ_ADD]) >>
  qabbrev_tac `G1 = step_prov PG G i0 s1` >>
  qabbrev_tac `tn1 = step_taint i0 s s1 tn` >>
  qabbrev_tac `G2 = step_prov PG G1 i1 s2` >>
  qabbrev_tac `tn2 = step_taint i1 s1 s2 tn1` >>
  qabbrev_tac `G3 = step_prov PG G2 i2 s2` >>
  qabbrev_tac `tn3 = step_taint i2 s2 s2 tn2` >>
  suspend "ghosts"
QED

Resume registration_ptr_guard_ptr_frame[ghosts]:
  `op_prov G1 (Var v0) = NONE /\ op_taint tn1 (Var v0) = {}` by
    (simp[Abbr `tn1`, Abbr `G1`, Abbr `i0`] >>
     irule guard_scalar_output_ghost >> simp[op_taint_def]) >>
  `op_prov G2 (Var v1) = NONE /\ op_taint tn2 (Var v1) = {}` by
    (simp_tac (srw_ss()) [Abbr `tn2`, Abbr `G2`, Abbr `i1`] >>
     irule guard_scalar_output_ghost >> simp[]) >>
  `tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
   tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm` by
    (simp_tac (srw_ss()) [Abbr `tn1`, Abbr `i0`] >>
     irule guard_scalar_taint_frame >> fs[]) >>
  `tn2.t_mem = tn1.t_mem /\ tn2.t_stor = tn1.t_stor /\
   tn2.t_trans = tn1.t_trans /\ tn2.t_imm = tn1.t_imm` by
    (simp_tac (srw_ss()) [Abbr `tn2`, Abbr `i1`] >>
     irule guard_scalar_taint_frame >> fs[]) >>
  `tn3.t_mem = tn2.t_mem /\ tn3.t_stor = tn2.t_stor /\
   tn3.t_trans = tn2.t_trans /\ tn3.t_imm = tn2.t_imm` by
    (simp_tac (srw_ss()) [Abbr `tn3`, Abbr `i2`] >>
     irule guard_scalar_taint_frame >> fs[]) >>
  `?bb. lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH sa.cs_current_insts) = SOME i0 /\
    get_instruction bb (LENGTH sa.cs_current_insts + 1) = SOME i1 /\
    get_instruction bb (LENGTH sa.cs_current_insts + 2) = SOME i2` by
    (drule_all fn_has_code_same_block >> strip_tac >>
     qexists_tac `bb` >> simp[] >>
     first_x_assum (fn th => map_every (fn n => mp_tac (Q.SPEC n th))
       [`0`, `1`, `2`]) >> simp[Abbr `i0`, Abbr `i1`, Abbr `i2`]) >>
  qexistsl_tac [`s2.vs_vars`, `G3`, `tn3`] >>
  `s with vs_vars := s2.vs_vars = s2` by
    simp[Abbr `s2`, Abbr `s1`, update_var_def, venom_state_component_equality] >>
  simp[] >>
  suspend "parts"
QED

Resume registration_ptr_guard_ptr_frame[parts]:
  qunabbrev_tac `s2` >> qunabbrev_tac `s1` >>
  rpt conj_tac
  >- (qunabbrev_tac `v1` >> qunabbrev_tac `v0` >> simp[] >>
      irule abi_decoder_generated_update_fresh >> simp[] >>
      irule abi_decoder_generated_update_fresh >> simp[] >>
      irule fresh_vars_wrt_mono >> qexists_tac `sa` >> simp[])
  >- (rpt gen_tac >> strip_tac >>
      `x <> v0 /\ x <> v1` by metis_tac[] >>
      simp[update_var_def, FLOOKUP_UPDATE,
        Abbr `G3`, Abbr `G2`, Abbr `G1`, Abbr `tn3`, Abbr `tn2`, Abbr `tn1`,
        Abbr `i0`, Abbr `i1`, Abbr `i2`, mk_inst_def,
        step_prov_other_output, step_taint_other_output]) >>
  gen_tac >> strip_tac >>
  `!fuel. ptr_safe_run D lo fuel ctx fn PG G2 tn2
     ((update_var v1 1w (update_var v0 0w s)) with vs_inst_idx := LENGTH sa.cs_current_insts + 2)` by
    (qunabbrev_tac `i2` >>
     irule guard_scalar_indexed_continuation >>
     conj_tac >- asm_rewrite_tac[] >>
     reverse conj_tac >-
       (qpat_x_assum `allocas_from lo s` mp_tac >>
        simp[allocas_from_def, update_var_def]) >>
     goal_assum $ drule_at (Pat `get_instruction`) >>
     qexists_tac `(update_var v1 1w (update_var v0 0w s))` >>
     simp[Abbr `G3`, Abbr `tn3`] >>
     qpat_x_assum `!fuel. ptr_safe_run _ _ _ _ _ _ G3 tn3 _` mp_tac >>
     simp[arithmeticTheory.ADD1, update_var_def]) >>
  `!fuel. ptr_safe_run D lo fuel ctx fn PG G1 tn1
     ((update_var v0 0w s) with vs_inst_idx := LENGTH sa.cs_current_insts + 1)` by
    (qunabbrev_tac `i1` >>
     irule guard_scalar_indexed_continuation >>
     conj_tac >- asm_rewrite_tac[] >>
     reverse conj_tac >-
       (qpat_x_assum `allocas_from lo s` mp_tac >>
        simp[allocas_from_def, update_var_def]) >>
     goal_assum $ drule_at (Pat `get_instruction`) >>
     qexists_tac `(update_var v1 1w (update_var v0 0w s))` >>
     simp[Abbr `G2`, Abbr `tn2`] >>
     qpat_x_assum `!fuel. ptr_safe_run _ _ _ _ _ _ G2 tn2 _` mp_tac >>
     fs[arithmeticTheory.ADD1, update_var_def]) >>
  `!fuel. ptr_safe_run D lo fuel ctx fn PG G tn
     (s with vs_inst_idx := LENGTH sa.cs_current_insts)` by
    (qunabbrev_tac `i0` >>
     irule guard_scalar_indexed_continuation >>
     conj_tac >- asm_rewrite_tac[] >>
     reverse conj_tac >- asm_rewrite_tac[] >>
     goal_assum $ drule_at (Pat `get_instruction`) >>
     qexists_tac `(update_var v0 0w s)` >>
     simp[Abbr `G1`, Abbr `tn1`, op_taint_def, op_prov_def] >>
     qpat_x_assum `!fuel. ptr_safe_run _ _ _ _ _ _ G1 tn1 _` mp_tac >>
     fs[arithmeticTheory.ADD1, update_var_def]) >>
  qpat_x_assum `!fuel. ptr_safe_run _ _ _ _ _ _ G tn (s with vs_inst_idx := _)` mp_tac >>
  qpat_x_assum `s.vs_inst_idx = _` (fn th => rewrite_tac[GSYM th]) >>
  simp[]
QED

Finalise registration_ptr_guard_ptr_frame

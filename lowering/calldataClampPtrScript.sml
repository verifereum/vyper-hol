(* Clean scalar validation fragments used by calldata decoders. *)
Theory calldataClampPtr
Ancestors abiDecoderClamp abiEncoder compileEnv emitHelper exprLoweringProps
  fragExec venomInst list arithmetic words bodyPtrDefs decoderGhostFramePtr
  ptrDiscipline ptrSafeRun venomState venomExecSemantics entryDispatchPtr
  fragExecPtr ghostPcTransportPtr finite_map pred_set codegenRel instIdxIndep contextCodegenRel

Theorem calldata_clamp_instructions:
  compile_abi_clamp_basetype op clamp sa = ((),sb) ==>
  sb.cs_current_bb = sa.cs_current_bb /\ sb.cs_blocks = sa.cs_blocks /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  (emitted_insts sa sb = [] \/
   ?opc shift signed.
     MEM opc [SIGNEXTEND; SHR; SHL] /\
     emitted_insts sa sb =
       [mk_inst sa.cs_next_id opc [Lit shift; op]
          ["%" ++ toString sa.cs_next_var];
        mk_inst (sa.cs_next_id + 1) (if signed then EQ else ISZERO)
          (if signed then [op; Var ("%" ++ toString sa.cs_next_var)]
           else [Var ("%" ++ toString sa.cs_next_var)])
          ["%" ++ toString (sa.cs_next_var + 1)];
        mk_inst (sa.cs_next_id + 2) ASSERT
          [Var ("%" ++ toString (sa.cs_next_var + 1))] []])
Proof
  Cases_on `clamp`
  >- simp[compile_abi_clamp_basetype_def, comp_return_def, emitted_insts_def] >>
  TRY (rename1 `IntClamp bits signed` >> Cases_on `signed`) >>
  simp[compile_abi_clamp_basetype_def, compile_abi_int_clamp_def,
       compile_abi_bytes_clamp_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, emit_inst_def,
       fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def, APPEND_ASSOC, DROP_PREFIX] >>
  metis_tac[]
QED

(* A clean scalar is not necessarily provenance-free.  Signed validation
   compares two variables, and therefore needs a provenance side condition. *)
Theorem clamp_comparison_unmatched_provenance:
  FLOOKUP G u <> NONE /\ FLOOKUP G v = NONE ==>
  ~access_ok lo G fn (mk_inst id EQ [Var u; Var v] [out]) s
Proof
  simp[access_ok_def, mk_inst_def, FLOOKUP_DEF] >> metis_tac[]
QED

Theorem clamp_scalar_step_safe:
  MEM opc [SIGNEXTEND; SHR; SHL; EQ; ISZERO; ASSERT] /\
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

Theorem clamp_scalar_out_taint:
  MEM opc [SIGNEXTEND; SHR; SHL; EQ; ISZERO; ASSERT] /\
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

Theorem clamp_scalar_output_ghost:
  MEM opc [SIGNEXTEND; SHR; SHL; EQ; ISZERO; ASSERT] /\
  EVERY (\op. op_taint tn op = {}) ops ==>
  op_prov (step_prov PG G (mk_inst id opc ops [out]) t) (Var out) = NONE /\
  op_taint (step_taint (mk_inst id opc ops [out]) s t tn) (Var out) = {}
Proof
  strip_tac >> drule_all clamp_scalar_out_taint >> strip_tac >>
  simp[op_taint_def, step_taint_def, mk_inst_def, set_var_taint_def,
       FLOOKUP_UPDATE] >>
  fs[MEM] >> simp[op_prov_def, step_prov_def, out_prov_def,
    set_prov_def, mk_inst_def, FLOOKUP_DRESTRICT]
QED

Theorem clamp_scalar_state_frame:
  MEM opc [SIGNEXTEND; SHR; SHL; EQ; ISZERO; ASSERT] /\
  step_inst_base (mk_inst id opc ops outs) s = OK t ==>
  ?vars. t = s with vs_vars := vars
Proof
  strip_tac >> fs[MEM] >> gvs[] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [mk_inst_def] >>
  simp_tac bool_ss [Once step_inst_base_def, instruction_accessors,
                    instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure2_def, exec_pure1_def, AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[] >> simp[venom_state_component_equality]
QED

Theorem clamp_scalar_taint_frame:
  MEM opc [SIGNEXTEND; SHR; SHL; EQ; ISZERO; ASSERT] /\
  step_inst_base (mk_inst id opc ops outs) s = OK t ==>
  (step_taint (mk_inst id opc ops outs) s t tn).t_mem = tn.t_mem /\
  (step_taint (mk_inst id opc ops outs) s t tn).t_stor = tn.t_stor /\
  (step_taint (mk_inst id opc ops outs) s t tn).t_trans = tn.t_trans /\
  (step_taint (mk_inst id opc ops outs) s t tn).t_imm = tn.t_imm
Proof
  strip_tac >> drule_all clamp_scalar_state_frame >> strip_tac >>
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

Theorem clamp_scalar_continuation:
  MEM opc [SIGNEXTEND; SHR; SHL; EQ; ISZERO; ASSERT] /\
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
  `?vars. t = s with vs_vars := vars` by metis_tac[clamp_scalar_state_frame] >>
  `opc <> INVOKE /\ ~is_terminator opc` by (fs[MEM, is_terminator_def]) >>
  `!fuel. step_inst fuel ctx (mk_inst id opc ops outs) s = OK t` by
    simp[step_inst_non_invoke, mk_inst_def] >>
  gen_tac >> irule ptr_safe_run_scalar_continuation >>
  qexistsl_tac [`bb`, `mk_inst id opc ops outs`, `t`] >>
  simp[mk_inst_def] >>
  irule (SRULE [mk_inst_def] clamp_scalar_step_safe) >>
  simp[GSYM mk_inst_def] >> fs[MEM]
QED

Theorem clamp_scalar_indexed_continuation:
  MEM opc [SIGNEXTEND; SHR; SHL; EQ; ISZERO; ASSERT] /\
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
  irule clamp_scalar_continuation >>
  simp_tac (srw_ss()) [allocas_from_def] >>
  asm_rewrite_tac[GSYM allocas_from_def] >>
  goal_assum $ drule_at (Pat `get_instruction`) >>
  qexists_tac `t with vs_inst_idx := n` >>
  simp[step_prov_inst_idx, step_taint_inst_idx] >>
  fs[MEM]
QED

Theorem clamp_scalar_lookup_frame:
  MEM opc [SIGNEXTEND; SHR; SHL; EQ; ISZERO; ASSERT] /\
  step_inst_base (mk_inst id opc ops outs) s = OK t /\ ~MEM x outs ==>
  lookup_var x t = lookup_var x s
Proof
  strip_tac >> fs[MEM] >> gvs[] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [mk_inst_def] >>
  simp_tac bool_ss [Once step_inst_base_def, instruction_accessors,
                    instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure2_def, exec_pure1_def, AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem calldata_clamp_overwrite_prefix_uniform:
  compile_abi_clamp_basetype op clamp sa = ((),sb) /\
  eval_operand op s = SOME w /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  op_taint tn op = {} /\ op_prov G op = NONE /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?s' G' tn'.
    run_inst_seq (emitted_insts sa sb) s =
      OK (s' with vs_inst_idx := s.vs_inst_idx) /\
    ~s'.vs_halted /\ s'.vs_current_bb = sb.cs_current_bb /\
    s'.vs_inst_idx = LENGTH sb.cs_current_insts /\
    s'.vs_memory = s.vs_memory /\ s'.vs_allocas = s.vs_allocas /\
    s'.vs_alloca_next = s.vs_alloca_next /\
    s' = t with vs_inst_idx := LENGTH sb.cs_current_insts /\
    (!a v. (!x. a = Var x ==> not_fresh_at sa x) /\
      eval_operand a s = SOME v ==> eval_operand a s' = SOME v) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG G' tn' s') ==>
     !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >>
  drule calldata_clamp_instructions >> strip_tac
  >- (gvs[run_inst_seq_def] >>
      qexistsl_tac [`G`, `tn`] >>
      `s with vs_inst_idx := LENGTH sa.cs_current_insts = s` by
        simp[venom_state_component_equality] >> simp[]) >>
  qabbrev_tac `v0 = "%" ++ toString sa.cs_next_var` >>
  qabbrev_tac `v1 = "%" ++ toString (sa.cs_next_var + 1)` >>
  qabbrev_tac `i0 = mk_inst sa.cs_next_id opc [Lit shift; op] [v0]` >>
  qabbrev_tac `i1 = mk_inst (sa.cs_next_id + 1) (if signed then EQ else ISZERO)
    (if signed then [op; Var v0] else [Var v0]) [v1]` >>
  qabbrev_tac `i2 = mk_inst (sa.cs_next_id + 2) ASSERT [Var v1] []` >>
  `emitted_insts sa sb = [i0;i1;i2]` by
    simp[Abbr `i0`, Abbr `i1`, Abbr `i2`, Abbr `v0`, Abbr `v1`] >>
  `?s1 s2. step_inst_base i0 s = OK s1 /\
     step_inst_base i1 s1 = OK s2 /\ step_inst_base i2 s2 = OK t` by
    (qpat_x_assum `run_inst_seq _ s = OK t` mp_tac >>
     simp[run_inst_seq_def, AllCaseEqs()] >> metis_tac[]) >>
  `?vars0. s1 = s with vs_vars := vars0` by
    (irule clamp_scalar_state_frame >>
     qexistsl_tac [`sa.cs_next_id`, `opc`, `[Lit shift;op]`, `[v0]`] >>
     simp[Abbr `i0`] >> fs[MEM]) >>
  `?vars1. s2 = s1 with vs_vars := vars1` by
    (irule clamp_scalar_state_frame >>
     qexistsl_tac [`sa.cs_next_id + 1`, `if signed then EQ else ISZERO`,
       `if signed then [op;Var v0] else [Var v0]`, `[v1]`] >>
     simp[Abbr `i1`] >> Cases_on `signed` >> simp[]) >>
  `?vars2. t = s2 with vs_vars := vars2` by
    (irule clamp_scalar_state_frame >>
     qexistsl_tac [`sa.cs_next_id + 2`, `ASSERT`, `[Var v1]`, `[]:string list`] >>
     simp[Abbr `i2`]) >>
  `op <> Var v0` by
    (strip_tac >>
     qpat_x_assum `!x. op = Var x ==> _` drule >>
     simp[not_fresh_at_def, Abbr `v0`]) >>
  qabbrev_tac `G1 = step_prov PG G i0 s1` >>
  qabbrev_tac `tn1 = step_taint i0 s s1 tn` >>
  qabbrev_tac `G2 = step_prov PG G1 i1 s2` >>
  qabbrev_tac `tn2 = step_taint i1 s1 s2 tn1` >>
  qabbrev_tac `G3 = step_prov PG G2 i2 t` >>
  qabbrev_tac `tn3 = step_taint i2 s2 t tn2` >>
  suspend "ghost_frames"
QED

Resume calldata_clamp_overwrite_prefix_uniform[ghost_frames]:
  `op_taint tn1 op = {} /\ op_prov G1 op = NONE` by
    (Cases_on `op` >>
     gvs[Abbr `tn1`, Abbr `G1`, Abbr `i0`, op_prov_def,
       op_taint_def, step_prov_other_output, step_taint_other_output, mk_inst_def]) >>
  `op_prov G1 (Var v0) = NONE /\ op_taint tn1 (Var v0) = {}` by
    (simp[Abbr `tn1`, Abbr `G1`, Abbr `i0`] >>
     irule clamp_scalar_output_ghost >>
     simp[op_taint_def] >> fs[MEM]) >>
  `op_prov G2 (Var v1) = NONE /\ op_taint tn2 (Var v1) = {}` by
    (simp_tac (srw_ss()) [Abbr `tn2`, Abbr `G2`, Abbr `i1`] >>
     irule clamp_scalar_output_ghost >> Cases_on `signed` >> simp[]) >>
  `tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
   tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm` by
    (simp_tac (srw_ss()) [Abbr `tn1`, Abbr `i0`] >>
     irule clamp_scalar_taint_frame >>
     fs[MEM]) >>
  `tn2.t_mem = tn1.t_mem /\ tn2.t_stor = tn1.t_stor /\
   tn2.t_trans = tn1.t_trans /\ tn2.t_imm = tn1.t_imm` by
    (simp_tac (srw_ss()) [Abbr `tn2`, Abbr `i1`] >>
     irule clamp_scalar_taint_frame >> Cases_on `signed` >> fs[]) >>
  `tn3.t_mem = tn2.t_mem /\ tn3.t_stor = tn2.t_stor /\
   tn3.t_trans = tn2.t_trans /\ tn3.t_imm = tn2.t_imm` by
    (simp_tac (srw_ss()) [Abbr `tn3`, Abbr `i2`] >>
     irule clamp_scalar_taint_frame >> fs[]) >>
  `!x. not_fresh_at sa x ==> x <> v0 /\ x <> v1` by
    (simp[not_fresh_at_def, Abbr `v0`, Abbr `v1`] >>
     metis_tac[LESS_EQ_REFL, arithmeticTheory.LESS_EQ_ADD]) >>
  `!x. not_fresh_at sa x ==> FLOOKUP G3 x = FLOOKUP G x /\
     op_taint tn3 (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> simp[Abbr `G3`, Abbr `G2`, Abbr `G1`,
       Abbr `tn3`, Abbr `tn2`, Abbr `tn1`, Abbr `i0`, Abbr `i1`, Abbr `i2`,
       mk_inst_def, step_prov_other_output, step_taint_other_output]) >>
  suspend "endpoint"
QED

Resume calldata_clamp_overwrite_prefix_uniform[endpoint]:
  `?bb. lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH sa.cs_current_insts) = SOME i0 /\
    get_instruction bb (LENGTH sa.cs_current_insts + 1) = SOME i1 /\
    get_instruction bb (LENGTH sa.cs_current_insts + 2) = SOME i2` by
    (drule_all fn_has_code_same_block >> strip_tac >>
     qexists_tac `bb` >> simp[] >>
     first_x_assum (fn th => map_every (fn n => mp_tac (Q.SPEC n th))
       [`0`, `1`, `2`]) >> simp[]) >>
  `(!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG G3 tn3
      (t with vs_inst_idx := LENGTH sa.cs_current_insts + 3)) ==>
    !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)` by
    suspend "continuation" >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH sb.cs_current_insts`, `G3`, `tn3`] >>
  `t with vs_inst_idx := LENGTH sa.cs_current_insts = t` by
    simp[venom_state_component_equality] >>
  simp[eval_op_inst_idx] >>
  conj_tac >- simp[venom_state_component_equality] >>
  rpt strip_tac >> Cases_on `a`
  >- fs[eval_operand_def]
  >- (rename1 `eval_operand (Var x) s = SOME v` >>
  `not_fresh_at sa x` by
    (qpat_x_assum `!y. Var x = Var y ==> _` (qspec_then `x` mp_tac) >> simp[]) >>
  `x <> v0 /\ x <> v1` by metis_tac[] >>
  `lookup_var x s1 = lookup_var x s` by
    (irule clamp_scalar_lookup_frame >>
     qexistsl_tac [`sa.cs_next_id`, `opc`, `[Lit shift;op]`, `[v0]`] >>
     simp[Abbr `i0`] >> fs[MEM]) >>
  `lookup_var x s2 = lookup_var x s1` by
    (irule clamp_scalar_lookup_frame >>
     qexistsl_tac [`sa.cs_next_id + 1`, `if signed then EQ else ISZERO`,
       `if signed then [op;Var v0] else [Var v0]`, `[v1]`] >>
     simp[Abbr `i1`] >> Cases_on `signed` >> simp[]) >>
  `lookup_var x t = lookup_var x s2` by
    (irule clamp_scalar_lookup_frame >>
     qexistsl_tac [`sa.cs_next_id + 2`, `ASSERT`, `[Var v1]`, `[]:string list`] >>
     simp[Abbr `i2`]) >>
  qpat_x_assum `lookup_var x t = _` mp_tac >>
  qpat_x_assum `eval_operand (Var x) s = _` mp_tac >>
  simp[eval_operand_def]) >>
  fs[eval_operand_def]
QED

Resume calldata_clamp_overwrite_prefix_uniform[continuation]:
  gen_tac >> strip_tac >>
  `!fuel. ptr_safe_run D lo fuel ctx fn PG G2 tn2
     (s2 with vs_inst_idx := LENGTH sa.cs_current_insts + 2)` by
    (qunabbrev_tac `i2` >>
     irule clamp_scalar_indexed_continuation >>
     conj_tac >- asm_rewrite_tac[] >>
     reverse conj_tac >-
       (qpat_x_assum `allocas_from lo s` mp_tac >> simp[allocas_from_def]) >>
     goal_assum $ drule_at (Pat `get_instruction`) >>
     qexists_tac `t` >>
     simp[Abbr `G3`, Abbr `tn3`, allocas_from_def] >>
     qpat_x_assum `!fuel. ptr_safe_run _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[arithmeticTheory.ADD1]) >>
  `!fuel. ptr_safe_run D lo fuel ctx fn PG G1 tn1
     (s1 with vs_inst_idx := LENGTH sa.cs_current_insts + 1)` by
    (qunabbrev_tac `i1` >>
     irule clamp_scalar_indexed_continuation >>
     conj_tac >- asm_rewrite_tac[] >>
     reverse conj_tac >-
       (qpat_x_assum `allocas_from lo s` mp_tac >> simp[allocas_from_def]) >>
     goal_assum $ drule_at (Pat `get_instruction`) >>
     qexists_tac `s2` >>
     simp[Abbr `G2`, Abbr `tn2`] >>
     conj_tac
     >- (qpat_x_assum `!fuel. ptr_safe_run _ _ _ _ _ _ G2 tn2 _` mp_tac >>
         simp[arithmeticTheory.ADD1]) >>
     Cases_on `signed` >> simp[]) >>
  `!fuel. ptr_safe_run D lo fuel ctx fn PG G tn
     (s with vs_inst_idx := LENGTH sa.cs_current_insts)` by
    (qunabbrev_tac `i0` >>
     irule clamp_scalar_indexed_continuation >>
     conj_tac >- asm_rewrite_tac[] >>
     reverse conj_tac >- asm_rewrite_tac[] >>
     goal_assum $ drule_at (Pat `get_instruction`) >>
     qexists_tac `s1` >>
     simp[Abbr `G1`, Abbr `tn1`, op_taint_def, op_prov_def] >>
     conj_tac
     >- (qpat_x_assum `!fuel. ptr_safe_run _ _ _ _ _ _ G1 tn1 _` mp_tac >>
         simp[arithmeticTheory.ADD1]) >>
     fs[MEM]) >>
  qpat_x_assum `!fuel. ptr_safe_run _ _ _ _ _ _ G tn (s with vs_inst_idx := _)` mp_tac >>
  qpat_x_assum `s.vs_inst_idx = _` (fn th => rewrite_tac[GSYM th]) >>
  simp[]
QED

Finalise calldata_clamp_overwrite_prefix_uniform

Theorem evaluated_operand_not_fresh:
  fresh_vars_wrt sa s /\ eval_operand a s = SOME z /\ a = Var x ==>
  not_fresh_at sa x
Proof
  rpt strip_tac >> fs[not_fresh_at_def] >> rpt strip_tac >>
  gvs[eval_operand_def, lookup_var_def, FLOOKUP_DEF, fresh_vars_wrt_def] >>
  metis_tac[]
QED

Theorem calldata_clamp_prefix_framed_uniform:
  compile_abi_clamp_basetype op clamp sa = ((),sb) /\
  eval_operand op s = SOME w /\ abi_decoder_clamp_valid clamp w /\
  fresh_vars_wrt sa s /\ op_taint tn op = {} /\ op_prov G op = NONE /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?s' G' tn'.
    run_inst_seq (emitted_insts sa sb) s =
      OK (s' with vs_inst_idx := s.vs_inst_idx) /\
    ~s'.vs_halted /\ s'.vs_current_bb = sb.cs_current_bb /\
    s'.vs_inst_idx = LENGTH sb.cs_current_insts /\
    s'.vs_memory = s.vs_memory /\ s'.vs_allocas = s.vs_allocas /\
    s'.vs_alloca_next = s.vs_alloca_next /\
    (!a v. eval_operand a s = SOME v ==> eval_operand a s' = SOME v) /\
    fresh_vars_wrt sb s' /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG G' tn' s') ==>
     !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >>
  `!x. op = Var x ==> not_fresh_at sa x` by
    (rpt strip_tac >> irule evaluated_operand_not_fresh >>
     goal_assum $ drule_at (Pat `eval_operand`) >> simp[]) >>
  drule_all abi_decoder_clamp_sequence >> strip_tac >>
  drule_all calldata_clamp_overwrite_prefix_uniform >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl_tac [`s'`, `G'`, `tn'`] >>
  simp[fresh_vars_wrt_def, eval_op_inst_idx] >> fs[fresh_vars_wrt_def]
QED

Theorem calldata_clamp_overwrite_prefix:
  compile_abi_clamp_basetype op clamp sa = ((),sb) /\
  eval_operand op s = SOME w /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  op_taint tn op = {} /\ op_prov G op = NONE /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?s' G' tn'.
    run_inst_seq (emitted_insts sa sb) s =
      OK (s' with vs_inst_idx := s.vs_inst_idx) /\
    ~s'.vs_halted /\ s'.vs_current_bb = sb.cs_current_bb /\
    s'.vs_inst_idx = LENGTH sb.cs_current_insts /\
    s'.vs_memory = s.vs_memory /\ s'.vs_allocas = s.vs_allocas /\
    s'.vs_alloca_next = s.vs_alloca_next /\
    s' = t with vs_inst_idx := LENGTH sb.cs_current_insts /\
    (!a v. (!x. a = Var x ==> not_fresh_at sa x) /\
      eval_operand a s = SOME v ==> eval_operand a s' = SOME v) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    ((!fuel. ptr_safe_run D lo fuel ctx fn PG G' tn' s') ==>
     !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >> drule_all calldata_clamp_overwrite_prefix_uniform >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl_tac [`s'`, `G'`, `tn'`] >> simp[]
QED

Theorem calldata_clamp_prefix_framed:
  compile_abi_clamp_basetype op clamp sa = ((),sb) /\
  eval_operand op s = SOME w /\ abi_decoder_clamp_valid clamp w /\
  fresh_vars_wrt sa s /\ op_taint tn op = {} /\ op_prov G op = NONE /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?s' G' tn'.
    run_inst_seq (emitted_insts sa sb) s =
      OK (s' with vs_inst_idx := s.vs_inst_idx) /\
    ~s'.vs_halted /\ s'.vs_current_bb = sb.cs_current_bb /\
    s'.vs_inst_idx = LENGTH sb.cs_current_insts /\
    s'.vs_memory = s.vs_memory /\ s'.vs_allocas = s.vs_allocas /\
    s'.vs_alloca_next = s.vs_alloca_next /\
    (!a v. eval_operand a s = SOME v ==> eval_operand a s' = SOME v) /\
    fresh_vars_wrt sb s' /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    ((!fuel. ptr_safe_run D lo fuel ctx fn PG G' tn' s') ==>
     !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >> drule_all calldata_clamp_prefix_framed_uniform >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl_tac [`s'`, `G'`, `tn'`] >> simp[]
QED

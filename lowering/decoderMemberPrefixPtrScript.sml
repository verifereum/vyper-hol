(* Direct Error-inclusive safety transport for member address navigation. *)
Theory decoderMemberPrefixPtr
Ancestors decoderNavigationPtr calldataOverwritePtr calldataClampPtr entryDispatchPtr
  decoderGhostFramePtr fragExecPtr ptrSafeRun ptrDiscipline bodyPtrDefs
  venomExecSemantics venomInst venomState compileEnv emitHelper fragExec
  words finite_map pred_set list arithmetic codegenRel instIdxIndep contextCodegenRel
  emitHelperProps exprLoweringProps abiDecoderLoop

Theorem member_navigation_state_frame[local]:
  MEM opc [ADD; CALLDATALOAD] /\
  step_inst_base (mk_inst id opc ops outs) s = OK t ==>
  ?vars. t = s with vs_vars := vars
Proof
  strip_tac >> fs[MEM] >> gvs[] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [mk_inst_def] >>
  simp_tac bool_ss [Once step_inst_base_def, instruction_accessors,
    instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure2_def, exec_read1_def, AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[] >> simp[venom_state_component_equality]
QED

Theorem member_navigation_taint_frame[local]:
  MEM opc [ADD; CALLDATALOAD] /\
  step_inst_base (mk_inst id opc ops outs) s = OK t ==>
  (step_taint (mk_inst id opc ops outs) s t tn).t_mem = tn.t_mem /\
  (step_taint (mk_inst id opc ops outs) s t tn).t_stor = tn.t_stor /\
  (step_taint (mk_inst id opc ops outs) s t tn).t_trans = tn.t_trans /\
  (step_taint (mk_inst id opc ops outs) s t tn).t_imm = tn.t_imm
Proof
  strip_tac >> drule_all member_navigation_state_frame >> strip_tac >>
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

Theorem member_navigation_step_safe[local]:
  MEM opc [ADD; CALLDATALOAD] /\
  EVERY (\op. op_taint tn op = {}) ops /\
  step_inst fuel ctx (mk_inst id opc ops outs) s = OK t /\
  t.vs_requests = s.vs_requests /\
  allocas_from lower s /\ ~ctx_has_dalloca ctx ==>
  ptr_safe_step D lower fuel ctx func PG G tn (mk_inst id opc ops outs) s
Proof
  strip_tac >> fs[MEM] >>
  gvs[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
    mk_inst_def, source_memory_write_ranges_def,
    source_memory_read_ranges_def, EVERY_MEM] >> metis_tac[]
QED

Theorem member_navigation_step_continuation:
  MEM opc [ADD; CALLDATALOAD] /\
  EVERY (\op. op_taint tn op = {}) ops /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id opc ops outs) /\
  step_inst_base (mk_inst id opc ops outs) s = OK t /\
  allocas_from lower s /\ ~ctx_has_dalloca ctx /\
  (!fuel. ptr_safe_run D lower fuel ctx func PG
    (step_prov PG G (mk_inst id opc ops outs) t)
    (step_taint (mk_inst id opc ops outs) s t tn)
    (t with vs_inst_idx := SUC s.vs_inst_idx)) ==>
  !fuel. ptr_safe_run D lower fuel ctx func PG G tn s
Proof
  strip_tac >>
  drule_all member_navigation_state_frame >> strip_tac >>
  `opc <> INVOKE /\ ~is_terminator opc` by fs[MEM, is_terminator_def] >>
  `!fuel. step_inst fuel ctx (mk_inst id opc ops outs) s = OK t` by
    simp[step_inst_non_invoke, mk_inst_def] >>
  gen_tac >> irule ptr_safe_run_scalar_continuation >>
  qexistsl_tac [`bb`, `mk_inst id opc ops outs`, `t`] >>
  simp[mk_inst_def] >>
  irule (SRULE [mk_inst_def] member_navigation_step_safe) >>
  simp[GSYM mk_inst_def] >> fs[MEM]
QED

(* Supplied ordinary endpoints, including stale output registers.  The ghost
   expressions are exposed so that scalar and pointer ADD use the same step. *)
Theorem member_navigation_emit_continuation:
  MEM opc [ADD; CALLDATALOAD] /\ emit_op opc ops sa = (out,sb) /\
  EVERY (\op. op_taint tn op = {}) ops /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?x. out = Var x /\
    (step_taint (mk_inst sa.cs_next_id opc ops [x]) s t tn).t_mem = tn.t_mem /\
    (step_taint (mk_inst sa.cs_next_id opc ops [x]) s t tn).t_stor = tn.t_stor /\
    (step_taint (mk_inst sa.cs_next_id opc ops [x]) s t tn).t_trans = tn.t_trans /\
    (step_taint (mk_inst sa.cs_next_id opc ops [x]) s t tn).t_imm = tn.t_imm /\
    ((!fuel. ptr_safe_run D lower fuel ctx func PG
      (step_prov PG G (mk_inst sa.cs_next_id opc ops [x]) t)
      (step_taint (mk_inst sa.cs_next_id opc ops [x]) s t tn)
      (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
     !fuel. ptr_safe_run D lower fuel ctx func PG G tn s)
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  qabbrev_tac `x = "%" ++ toString sa.cs_next_var` >>
  `step_inst_base (mk_inst sa.cs_next_id opc ops [x]) s = OK t` by
    gvs[run_inst_seq_def, AllCaseEqs()] >>
  drule_all member_navigation_taint_frame >> strip_tac >>
  `same_blocks sa sb` by metis_tac[emit_op_same_blocks] >>
  `?bb. lookup_block sa.cs_current_bb func.fn_blocks = SOME bb /\
    !k. k < LENGTH [mk_inst sa.cs_next_id opc ops [x]] ==>
      get_instruction bb (LENGTH sa.cs_current_insts + k) =
        SOME (EL k [mk_inst sa.cs_next_id opc ops [x]])` by
    (irule fn_has_code_same_block >> qexists_tac `sb` >> fs[same_blocks_def]) >>
  `get_instruction bb s.vs_inst_idx = SOME (mk_inst sa.cs_next_id opc ops [x])` by
    (qpat_x_assum `!k. k < LENGTH _ ==> _` (qspec_then `0` mp_tac) >> simp[]) >>
  qexists_tac `x` >> (conj_tac >- simp[Abbr `x`]) >>
  simp[] >> strip_tac >>
  irule member_navigation_step_continuation >>
  simp[] >>
  qexistsl_tac [`sa.cs_next_id`, `opc`, `ops`, `[x]`, `t`] >>
  gvs[ADD1]
QED

(* The same computed ghosts carry cleanliness, live-variable frames, and the
   Error-inclusive continuation; no fresh-register assumption on s is used. *)
Theorem member_navigation_emit_endpoint:
  MEM opc [ADD; CALLDATALOAD] /\ emit_op opc ops sa = (out,sb) /\
  EVERY (\op. op_taint tn op = {}) ops /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?x H u. out = Var x /\
    H = step_prov PG G (mk_inst sa.cs_next_id opc ops [x]) t /\
    u = step_taint (mk_inst sa.cs_next_id opc ops [x]) s t tn /\
    op_taint u out = {} /\
    (EVERY (\op. op_prov G op = NONE) ops ==> op_prov H out = NONE) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_allocas = s.vs_allocas /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!q. not_fresh_at sa q ==> lookup_var q t = lookup_var q s /\
      FLOOKUP H q = FLOOKUP G q /\ op_taint u (Var q) = op_taint tn (Var q)) /\
    ((!fuel. ptr_safe_run D lower fuel ctx func PG H u
      (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
     !fuel. ptr_safe_run D lower fuel ctx func PG G tn s)
Proof
  strip_tac >> drule_all member_navigation_emit_continuation >>
  disch_then (qspecl_then [`PG`, `G`, `D`] (qx_choose_then `x` strip_assume_tac)) >>
  drule emitted_insts_emit_op >> strip_tac >>
  `step_inst_base (mk_inst sa.cs_next_id opc ops [x]) s = OK t` by
    gvs[run_inst_seq_def, AllCaseEqs()] >>
  drule_all member_navigation_state_frame >> strip_tac >>
  qabbrev_tac `ins = mk_inst sa.cs_next_id opc ops [x]` >>
  qexistsl_tac [`x`, `step_prov PG G ins t`, `step_taint ins s t tn`] >>
  (conj_tac >- gvs[]) >>
  (conj_tac >- simp[Abbr `ins`]) >>
  (conj_tac >- simp[Abbr `ins`]) >>
  `op_taint (step_taint ins s t tn) (Var x) = {}` by
    (fs[MEM] >> gvs[Abbr `ins`] >>
     simp[op_taint_def, step_taint_def, set_var_taint_def, mk_inst_def,
       FLOOKUP_UPDATE, out_taint_def] >>
     namedCases_on `ops` ["", "left rest"] >> simp[] >>
     Cases_on `eval_operand left s` >> simp[] >>
     namedCases_on `rest` ["", "right tail"] >> simp[] >>
     Cases_on `tail` >> simp[]) >>
  (conj_tac >- gvs[Abbr `ins`]) >>
  simp[Abbr `ins`] >>
  conj_tac >-
    (strip_tac >>
     `first_prov G ops = NONE` by
       (qpat_x_assum `EVERY (\op. op_prov G op = NONE) ops` mp_tac >>
        POP_ASSUM_LIST kall_tac >>
        Induct_on `ops` >> simp[first_prov_def]) >>
     fs[MEM] >>
     simp[step_prov_def, op_prov_def, out_prov_def,
       set_prov_def, mk_inst_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]) >>
  rpt strip_tac >>
  `x = "%" ++ toString sa.cs_next_var` by gvs[] >>
  `q <> x` by
    (gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >>
  simp[step_prov_other_output, step_taint_other_output, mk_inst_def] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >> fs[MEM] >>
  simp_tac (srw_ss()) [mk_inst_def] >>
  simp_tac bool_ss [Once step_inst_base_def, instruction_accessors,
    instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure2_def, exec_read1_def, AllCaseEqs(), update_var_def,
    lookup_var_def, FLOOKUP_UPDATE] >> rpt strip_tac >>
  gvs[venom_state_component_equality, FLOOKUP_UPDATE] >>
  simp[step_prov_other_output, step_taint_other_output, instruction_accessors]
QED

Theorem member_navigation_emit_pointer:
  emit_op ADD [Var root; offset] sa = (out,sb) /\
  lookup_var root s = SOME a /\ ptr_covers G tn root s cap /\
  eval_operand offset s = SOME (n2w off) /\
  op_taint tn offset = {} /\ op_prov G offset = NONE /\
  off + n <= cap /\ w2n a + off < dimword(:256) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?x H u. out = Var x /\
    H = step_prov PG G (mk_inst sa.cs_next_id ADD [Var root; offset] [x]) t /\
    u = step_taint (mk_inst sa.cs_next_id ADD [Var root; offset] [x]) s t tn /\
    lookup_var x t = SOME (n2w (w2n a + off)) /\
    ptr_covers H u x t n /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_allocas = s.vs_allocas /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!q. not_fresh_at sa q ==> lookup_var q t = lookup_var q s /\
      FLOOKUP H q = FLOOKUP G q /\ op_taint u (Var q) = op_taint tn (Var q)) /\
    ((!fuel. ptr_safe_run D lower fuel ctx func PG H u
      (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
     !fuel. ptr_safe_run D lower fuel ctx func PG G tn s)
Proof
  strip_tac >>
  `EVERY (\op. op_taint tn op = {}) [Var root; offset]` by
    gvs[ptr_covers_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`] member_navigation_emit_endpoint)) >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  `t = update_var x (a + n2w off) s` by
    (drule emitted_insts_emit_op >> strip_tac >>
     gvs[run_inst_seq_def, step_inst_base_def, mk_inst_def, exec_pure2_def,
       eval_operand_def]) >>
  qexistsl_tac [`x`,
    `step_prov PG G (mk_inst sa.cs_next_id ADD [Var root; offset] [x]) t`,
    `step_taint (mk_inst sa.cs_next_id ADD [Var root; offset] [x]) s t tn`] >>
  simp[] >>
  (conj_tac >-
    simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE,
      GSYM word_add_n2w, WORD_ADD_COMM, ADD_COMM]) >>
  gvs[ptr_covers_def] >>
  `off < dimword(:256)` by decide_tac >>
  simp[step_prov_def, set_prov_def, out_prov_def, first_prov_def,
    op_prov_def, mk_inst_def, FLOOKUP_UPDATE, lookup_var_def, update_var_def,
    eval_operand_def, w2n_add_2, w2n_n2w, LESS_MOD] >> decide_tac
QED

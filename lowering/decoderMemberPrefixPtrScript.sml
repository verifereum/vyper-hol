(* Direct Error-inclusive safety transport for member address navigation. *)
Theory decoderMemberPrefixPtr
Ancestors decoderNavigationPtr calldataOverwritePtr calldataClampPtr entryDispatchPtr
  decoderGhostFramePtr fragExecPtr ptrSafeRun ptrDiscipline bodyPtrDefs
  venomExecSemantics venomInst venomState compileEnv loweringStateRelDefs emitHelper fragExec
  words finite_map pred_set list arithmetic codegenRel instIdxIndep contextCodegenRel
  emitHelperProps exprLoweringProps abiDecoderLoop ghostPcTransportPtr exprLowering abiEncoder decoderArraySetupPtr
  abiDecoderMemberSetup abiDecoderReentryPointer abiDecoderReentry

(* The calldata address step: base Lit 0w adds no instruction. *)
val calldata_pos_addr = prove(
  ``compile_abi_dec_addr (Lit 0w) pos st = (pos,st)``,
  simp[abiEncoderTheory.compile_abi_dec_addr_def, compileEnvTheory.comp_return_def]);

(* The calldata instance of trunk's position-form decoder lemmas: the source
   base operand is Lit 0w and the numeric base is 0. *)
val calldata_pos_live_lit = prove(
  ``!n w. abiDecoderReentry$abi_decoder_operand_live n (Lit w)``,
  simp[abiDecoderReentryTheory.abi_decoder_operand_live_def]);
fun calldata_pos th =
  SIMP_RULE bool_ss
    [cj 1 venomStateTheory.eval_operand_def, cj 1 arithmeticTheory.ADD_CLAUSES,
     cj 2 arithmeticTheory.ADD_CLAUSES, calldata_pos_live_lit]
    (Q.INST [`base_op` |-> `Lit 0w`, `B` |-> `0:num`, `src_base` |-> `0:num`] th);

Theorem member_navigation_state_frame[local]:
  MEM opc [ADD; CALLDATALOAD] /\
  step_inst_base (mk_inst id opc ops outs) s = OK t ==>
  ?vars. t = s with vs_vars := vars
Proof
  strip_tac >> fs[MEM] >> gvs[] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [mk_inst_def] >>
  simp_tac bool_ss [step_inst_base_opcode_eqs, instruction_accessors,
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
  simp_tac bool_ss [step_inst_base_opcode_eqs, instruction_accessors,
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
     gvs[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
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


Theorem member_navigation_emit_state_frame[local]:
  MEM opc [ADD; CALLDATALOAD] /\ emit_op opc ops sa = (out,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  t.vs_current_bb = s.vs_current_bb
Proof
  strip_tac >> drule_all emitted_insts_emit_op >> strip_tac >>
  `step_inst_base (mk_inst sa.cs_next_id opc ops ["%" ++ toString sa.cs_next_var]) s = OK t` by
    gvs[run_inst_seq_def, AllCaseEqs()] >>
  drule_all member_navigation_state_frame >> strip_tac >> simp[]
QED


(* The scalar endpoint exposes its ghost formulas, so its witnesses can be
   selected independently of the dead-byte set. *)
Theorem member_navigation_emit_endpoint_uniform:
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
    (!D. (!fuel. ptr_safe_run D lower fuel ctx func PG H u
      (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
     !fuel. ptr_safe_run D lower fuel ctx func PG G tn s)
Proof
  strip_tac >>
  drule_all member_navigation_emit_endpoint >>
  disch_then (qspecl_then [`PG`, `G`, `ARB`] strip_assume_tac) >>
  qexistsl_tac [`x`, `H`, `u`] >> simp[] >>
  rpt strip_tac >>
  drule_all member_navigation_emit_endpoint >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  gvs[]
QED

Theorem member_navigation_emit_pointer_uniform:
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
    (!D. (!fuel. ptr_safe_run D lower fuel ctx func PG H u
      (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
     !fuel. ptr_safe_run D lower fuel ctx func PG G tn s)
Proof
  strip_tac >> drule_all member_navigation_emit_pointer >>
  disch_then (qspecl_then [`PG`, `ARB`] strip_assume_tac) >>
  qexistsl_tac [`x`, `H`, `u`] >> simp[] >> rpt strip_tac >>
  drule_all member_navigation_emit_pointer >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >> gvs[]
QED

Theorem member_navigation_emit_endpoint_pc_uniform:
  MEM opc [ADD; CALLDATALOAD] /\ emit_op opc ops sa = (out,sb) /\
  EVERY (\op. op_taint tn op = {}) ops /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb ==>
  ?x H u. out = Var x /\ op_taint u out = {} /\
    (EVERY (\op. op_prov G op = NONE) ops ==> op_prov H out = NONE) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_allocas = s.vs_allocas /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!q. not_fresh_at sa q ==> lookup_var q t = lookup_var q s /\
      FLOOKUP H q = FLOOKUP G q /\ op_taint u (Var q) = op_taint tn (Var q)) /\
    (!D. (!fuel. ptr_safe_run D lower fuel ctx func PG H u
      (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
     !fuel. ptr_safe_run D lower fuel ctx func PG G tn
      (s with vs_inst_idx := LENGTH sa.cs_current_insts))
Proof
  strip_tac >>
  `~is_terminator opc` by fs[MEM, is_terminator_def] >>
  `run_inst_seq (emitted_insts sa sb)
      (s with vs_inst_idx := LENGTH sa.cs_current_insts) =
      OK (t with vs_inst_idx := LENGTH sa.cs_current_insts)` by
    (drule_all emit_op_run_pc >>
     disch_then (qspecl_then [`s`,`LENGTH sa.cs_current_insts`] mp_tac) >>
     simp[exec_result_map_def]) >>
  `allocas_from lower (s with vs_inst_idx := LENGTH sa.cs_current_insts)` by
    (fs[allocas_from_def] >> metis_tac[]) >>
  `(s with vs_inst_idx := LENGTH sa.cs_current_insts).vs_current_bb = sa.cs_current_bb /\
   (s with vs_inst_idx := LENGTH sa.cs_current_insts).vs_inst_idx = LENGTH sa.cs_current_insts` by simp[] >>
  drule_all member_navigation_emit_endpoint_uniform >>
  disch_then (qspecl_then [`PG`,`G`] (qx_choose_then `x` strip_assume_tac)) >>
  qexistsl_tac [`x`,`H`,`u`] >> gvs[lookup_var_def]
QED

Theorem member_navigation_emit_pointer_pc_uniform:
  emit_op ADD [Var root; offset] sa = (out,sb) /\
  lookup_var root s = SOME a /\ ptr_covers G tn root s cap /\
  eval_operand offset s = SOME (n2w off) /\
  op_taint tn offset = {} /\ op_prov G offset = NONE /\
  off + n <= cap /\ w2n a + off < dimword(:256) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb ==>
  ?x H u. out = Var x /\
    lookup_var x t = SOME (n2w (w2n a + off)) /\ ptr_covers H u x t n /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_allocas = s.vs_allocas /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!q. not_fresh_at sa q ==> lookup_var q t = lookup_var q s /\
      FLOOKUP H q = FLOOKUP G q /\ op_taint u (Var q) = op_taint tn (Var q)) /\
    (!D. (!fuel. ptr_safe_run D lower fuel ctx func PG H u
      (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
     !fuel. ptr_safe_run D lower fuel ctx func PG G tn
      (s with vs_inst_idx := LENGTH sa.cs_current_insts))
Proof
  strip_tac >>
  `run_inst_seq (emitted_insts sa sb)
      (s with vs_inst_idx := LENGTH sa.cs_current_insts) =
      OK (t with vs_inst_idx := LENGTH sa.cs_current_insts)` by
    (drule emit_op_run_pc >> simp[is_terminator_def] >>
     disch_then (qspecl_then [`s`,`LENGTH sa.cs_current_insts`] mp_tac) >>
     simp[exec_result_map_def]) >>
  `allocas_from lower (s with vs_inst_idx := LENGTH sa.cs_current_insts)` by
    (fs[allocas_from_def] >> metis_tac[]) >>
  `lookup_var root (s with vs_inst_idx := LENGTH sa.cs_current_insts) = SOME a /\
   ptr_covers G tn root (s with vs_inst_idx := LENGTH sa.cs_current_insts) cap /\
   eval_operand offset (s with vs_inst_idx := LENGTH sa.cs_current_insts) = SOME (n2w off)` by
    (gvs[ptr_covers_def, lookup_var_def] >> Cases_on `offset` >> gvs[eval_operand_def, lookup_var_def]) >>
  `(s with vs_inst_idx := LENGTH sa.cs_current_insts).vs_current_bb = sa.cs_current_bb /\
   (s with vs_inst_idx := LENGTH sa.cs_current_insts).vs_inst_idx = LENGTH sa.cs_current_insts` by simp[] >>
  drule_all member_navigation_emit_pointer_uniform >>
  disch_then (qspec_then `PG` (qx_choose_then `x` strip_assume_tac)) >>
  qexistsl_tac [`x`,`H`,`u`] >> gvs[ptr_covers_def, lookup_var_def]
QED

Theorem member_navigation_source_endpoint_uniform:
  compile_getelemptr_abi src dyn ao CALLDATALOAD (Lit 0w) (Lit 0w) sa = (ep,sb) /\
  (!q. src = Var q ==> not_fresh_at sa q) /\
  op_taint tn src = {} /\ op_prov G src = NONE /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb ==>
  ?H u. op_taint u ep = {} /\ op_prov H ep = NONE /\
  t.vs_current_bb = s.vs_current_bb /\
  t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\ t.vs_allocas = s.vs_allocas /\
  u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
  (!q. not_fresh_at sa q ==> lookup_var q t = lookup_var q s /\
    FLOOKUP H q = FLOOKUP G q /\ op_taint u (Var q) = op_taint tn (Var q)) /\
  (!D. (!fuel. ptr_safe_run D lower fuel ctx func PG H u (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
   !fuel. ptr_safe_run D lower fuel ctx func PG G tn (s with vs_inst_idx := LENGTH sa.cs_current_insts))
Proof
  Cases_on `dyn`
  >- suspend "dynamic"
  >> simp[compile_getelemptr_abi_def, calldata_pos_addr, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  `MEM ADD [ADD; CALLDATALOAD] /\
   EVERY (\op. op_taint tn op = {}) [src; Lit (n2w ao)]` by
    simp[op_taint_def] >>
  drule_all member_navigation_emit_endpoint_pc_uniform >>
  disch_then (qspecl_then [`PG`,`G`] strip_assume_tac) >>
  `t.vs_current_bb = s.vs_current_bb` by
    (drule_all member_navigation_emit_state_frame >> simp[]) >>
  qexistsl_tac [`H`,`u`] >> simp[op_prov_def]
QED

Resume member_navigation_source_endpoint_uniform[dynamic]:
  simp[compile_getelemptr_abi_def, calldata_pos_addr, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rename1 `emit_op ADD [src; Lit (n2w ao)] sa = (head,c1)` >>
  rename1 `emit_op CALLDATALOAD [head] c1 = (off,c2)` >>
  pairarg_tac >> gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  `inst_extends sa c1 /\ inst_extends c1 c2 /\ inst_extends c2 cs'` by
    metis_tac[inst_extends_emit_op] >>
  `inst_extends c1 cs'` by metis_tac[inst_extends_trans] >>
  `emitted_insts sa cs' = emitted_insts sa c1 ++ emitted_insts c1 cs' /\
   emitted_insts c1 cs' = emitted_insts c1 c2 ++ emitted_insts c2 cs'` by
    (conj_tac >> irule emitted_insts_append >> fs[inst_extends_def]) >>
  `?s1. run_inst_seq (emitted_insts sa c1) s = OK s1 /\
         run_inst_seq (emitted_insts c1 cs') s1 = OK t` by
    (irule run_inst_seq_append_ok >> gvs[]) >>
  `?s2. run_inst_seq (emitted_insts c1 c2) s1 = OK s2 /\
         run_inst_seq (emitted_insts c2 cs') s2 = OK t` by
    (irule run_inst_seq_append_ok >> gvs[]) >>
  `cs_extends sa c1 /\ cs_extends c1 c2 /\ cs_extends c2 cs'` by
    metis_tac[ci_mono_emit_op, ci_mono_def, pairTheory.SND] >>
  `cs_extends c1 cs'` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa c1 func /\ fn_has_code c1 c2 func /\ fn_has_code c2 cs' func` by
    metis_tac[fn_has_code_split] >>
  `MEM ADD [ADD; CALLDATALOAD] /\
   EVERY (\op. op_taint tn op = {}) [src; Lit (n2w ao)]` by simp[op_taint_def] >>
  drule_all member_navigation_emit_endpoint_pc_uniform >>
  disch_then (qspecl_then [`PG`,`G`] strip_assume_tac) >>
  rename1 `op_taint u1 head = {}` >> rename1 `FLOOKUP H1 _ = FLOOKUP G _` >>
  `op_prov H1 head = NONE` by fs[op_prov_def] >>
  `?vars. s1 = s with vs_vars := vars` by
    (qpat_assum `emit_op ADD [src; Lit (n2w ao)] sa = _`
       (mp_tac o MATCH_MP emitted_insts_emit_op) >> strip_tac >>
     `step_inst_base (mk_inst sa.cs_next_id ADD [src; Lit (n2w ao)] [x]) s = OK s1` by
       gvs[run_inst_seq_def, AllCaseEqs()] >>
     drule_all member_navigation_state_frame >> simp[]) >>
  `allocas_from lower s1 /\ s1.vs_current_bb = c1.cs_current_bb` by
    (gvs[allocas_from_def] >> metis_tac[emit_op_same_blocks, same_blocks_def]) >>
  `MEM CALLDATALOAD [ADD; CALLDATALOAD] /\
   EVERY (\op. op_taint u1 op = {}) [head]` by simp[] >>
  drule_all member_navigation_emit_endpoint_pc_uniform >>
  disch_then (qspecl_then [`PG`,`H1`] strip_assume_tac) >>
  rename1 `op_taint u2 off = {}` >> rename1 `FLOOKUP H2 _ = FLOOKUP H1 _` >>
  `op_prov H2 off = NONE` by fs[] >>
  `?vars. s2 = s1 with vs_vars := vars` by
    (qpat_assum `emit_op CALLDATALOAD [head] c1 = _`
       (mp_tac o MATCH_MP emitted_insts_emit_op) >> strip_tac >>
     `step_inst_base (mk_inst c1.cs_next_id CALLDATALOAD [head] [x']) s1 = OK s2` by
       gvs[run_inst_seq_def, AllCaseEqs()] >>
     drule_all member_navigation_state_frame >> simp[]) >>
  `allocas_from lower s2 /\ s2.vs_current_bb = c2.cs_current_bb` by
    (gvs[allocas_from_def] >> metis_tac[emit_op_same_blocks, same_blocks_def]) >>
  `sa.cs_next_var <= c1.cs_next_var /\ c1.cs_next_var <= c2.cs_next_var` by
    metis_tac[ci_mono_emit_op, ci_mono_def, pairTheory.SND] >>
  `!q. not_fresh_at sa q ==> not_fresh_at c1 q /\ not_fresh_at c2 q` by
    (simp[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `op_taint u2 src = {} /\ op_prov H2 src = NONE` by
    (Cases_on `src` >> gvs[op_taint_def, op_prov_def] >> metis_tac[]) >>
  qpat_x_assum `run_inst_seq (emitted_insts sa cs') _ = _` kall_tac >>
  qpat_x_assum `run_inst_seq (emitted_insts c1 cs') _ = _` kall_tac >>
  qpat_x_assum `emitted_insts sa cs' = _` kall_tac >>
  qpat_x_assum `emitted_insts c1 cs' = _` kall_tac >>
  `EVERY (\op. op_taint u2 op = {}) [src; off]` by simp[] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`] member_navigation_emit_endpoint_pc_uniform)) >>
  disch_then (qspecl_then [`PG`,`H2`] strip_assume_tac) >>
  `t.vs_current_bb = s2.vs_current_bb` by
    (drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`] member_navigation_emit_state_frame)) >> simp[]) >>
  qexistsl_tac [`H`,`u`] >> simp[] >> gvs[]
QED

Finalise member_navigation_source_endpoint_uniform

Theorem calldata_member_setup_endpoint_ptr_uniform:
  abi_decode_member_setup (Var root) src CALLDATALOAD (Lit 0w) (Lit 0w) dyn ao vo sa = (ops,sb) /\
  lookup_var root s = SOME a /\ not_fresh_at sa root /\
  (!q. src = Var q ==> not_fresh_at sa q) /\
  ptr_covers G tn root s cap /\ op_taint tn src = {} /\ op_prov G src = NONE /\
  vo + n <= cap /\ w2n a + vo < dimword(:256) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb ==>
  ?H u q. SND ops = Var q /\
  lookup_var q t = SOME (n2w (w2n a + vo)) /\ ptr_covers H u q t n /\
  op_taint u (FST ops) = {} /\ op_prov H (FST ops) = NONE /\
  t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\ t.vs_allocas = s.vs_allocas /\
  u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
    FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
  (!D. (!fuel. ptr_safe_run D lower fuel ctx func PG H u (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
   !fuel. ptr_safe_run D lower fuel ctx func PG G tn (s with vs_inst_idx := LENGTH sa.cs_current_insts))
Proof
  strip_tac >>
  qpat_assum `abi_decode_member_setup _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [abi_decode_member_setup_def, comp_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `compile_getelemptr_abi src dyn ao CALLDATALOAD (Lit 0w) (Lit 0w) sa = (ep,mid)` >>
  rename1 `emit_op ADD [Var root; Lit (n2w vo)] mid = (dst,sb)` >>
  `inst_extends sa mid /\ same_blocks sa mid` by
    (Cases_on `dyn` >>
     qpat_x_assum `compile_getelemptr_abi _ _ _ _ _ _ _ = _` mp_tac >>
     simp[compile_getelemptr_abi_def, calldata_pos_addr, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
     (conj_tac >- metis_tac[inst_extends_emit_op, inst_extends_trans]) >>
     imp_res_tac emit_op_same_blocks >> fs[same_blocks_def]) >>
  `inst_extends mid sb /\ same_blocks mid sb` by
    metis_tac[inst_extends_emit_op, emit_op_same_blocks] >>
  `cs_extends sa mid /\ cs_extends mid sb` by
    (conj_tac >> irule cs_extends_same_block >> fs[inst_extends_def, same_blocks_def]) >>
  `fn_has_code sa mid func /\ fn_has_code mid sb func` by metis_tac[fn_has_code_split] >>
  `emitted_insts sa sb = emitted_insts sa mid ++ emitted_insts mid sb` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `?prepared. run_inst_seq (emitted_insts sa mid) s = OK prepared /\
              run_inst_seq (emitted_insts mid sb) prepared = OK t` by
    (irule run_inst_seq_append_ok >> gvs[]) >>
  drule_all member_navigation_source_endpoint_uniform >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  rename1 `op_taint u1 ep = {}` >> rename1 `op_prov H1 ep = NONE` >>
  `lookup_var root prepared = SOME a /\ ptr_covers H1 u1 root prepared cap` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  `allocas_from lower prepared /\ prepared.vs_current_bb = mid.cs_current_bb` by
    (gvs[allocas_from_def, same_blocks_def] >> metis_tac[]) >>
  `eval_operand (Lit (n2w vo)) prepared = SOME (n2w vo) /\
   op_taint u1 (Lit (n2w vo)) = {} /\ op_prov H1 (Lit (n2w vo)) = NONE` by
    simp[eval_operand_def, op_taint_def, op_prov_def] >>
  `vo + n <= cap /\ w2n a + vo < dimword(:256)` by decide_tac >>
  drule_all member_navigation_emit_pointer_pc_uniform >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `!x. not_fresh_at sa x ==> not_fresh_at mid x` by
    (drule (calldata_pos abi_decoder_member_pointer_counters) >> strip_tac >>
     Cases_on `dyn` >> gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS, LESS_EQ_ADD]) >>
  `!x. ep = Var x ==> not_fresh_at mid x` by
    (drule (calldata_pos abi_decoder_member_pointer_counters) >> strip_tac >>
     Cases_on `ep` >> gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
  `op_taint u ep = {} /\ op_prov H ep = NONE` by
    (Cases_on `ep` >> gvs[op_taint_def, op_prov_def] >> metis_tac[]) >>
  qexistsl_tac [`H`,`u`,`x`] >> simp[ADD_COMM] >> metis_tac[]
QED

(* Compatibility projections of the uniform endpoints. *)
Theorem member_navigation_emit_endpoint_pc:
  MEM opc [ADD; CALLDATALOAD] /\ emit_op opc ops sa = (out,sb) /\
  EVERY (\op. op_taint tn op = {}) ops /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb ==>
  ?x H u. out = Var x /\ op_taint u out = {} /\
    (EVERY (\op. op_prov G op = NONE) ops ==> op_prov H out = NONE) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_allocas = s.vs_allocas /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!q. not_fresh_at sa q ==> lookup_var q t = lookup_var q s /\
      FLOOKUP H q = FLOOKUP G q /\ op_taint u (Var q) = op_taint tn (Var q)) /\
    ((!fuel. ptr_safe_run D lower fuel ctx func PG H u
      (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
     !fuel. ptr_safe_run D lower fuel ctx func PG G tn
      (s with vs_inst_idx := LENGTH sa.cs_current_insts))
Proof
  strip_tac >> drule_all member_navigation_emit_endpoint_pc_uniform >>
  disch_then (qspecl_then [`PG`,`G`] strip_assume_tac) >>
  qexistsl_tac [`x`,`H`,`u`] >> simp[]
QED

Theorem member_navigation_emit_pointer_pc:
  emit_op ADD [Var root; offset] sa = (out,sb) /\
  lookup_var root s = SOME a /\ ptr_covers G tn root s cap /\
  eval_operand offset s = SOME (n2w off) /\
  op_taint tn offset = {} /\ op_prov G offset = NONE /\
  off + n <= cap /\ w2n a + off < dimword(:256) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb ==>
  ?x H u. out = Var x /\
    lookup_var x t = SOME (n2w (w2n a + off)) /\ ptr_covers H u x t n /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_allocas = s.vs_allocas /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!q. not_fresh_at sa q ==> lookup_var q t = lookup_var q s /\
      FLOOKUP H q = FLOOKUP G q /\ op_taint u (Var q) = op_taint tn (Var q)) /\
    ((!fuel. ptr_safe_run D lower fuel ctx func PG H u
      (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
     !fuel. ptr_safe_run D lower fuel ctx func PG G tn
      (s with vs_inst_idx := LENGTH sa.cs_current_insts))
Proof
  strip_tac >> drule_all member_navigation_emit_pointer_pc_uniform >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl_tac [`x`,`H`,`u`] >> simp[]
QED

Theorem member_navigation_source_endpoint:
  compile_getelemptr_abi src dyn ao CALLDATALOAD (Lit 0w) (Lit 0w) sa = (ep,sb) /\
  (!q. src = Var q ==> not_fresh_at sa q) /\
  op_taint tn src = {} /\ op_prov G src = NONE /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb ==>
  ?H u. op_taint u ep = {} /\ op_prov H ep = NONE /\
  t.vs_current_bb = s.vs_current_bb /\
  t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\ t.vs_allocas = s.vs_allocas /\
  u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
  (!q. not_fresh_at sa q ==> lookup_var q t = lookup_var q s /\
    FLOOKUP H q = FLOOKUP G q /\ op_taint u (Var q) = op_taint tn (Var q)) /\
  ((!fuel. ptr_safe_run D lower fuel ctx func PG H u (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
   !fuel. ptr_safe_run D lower fuel ctx func PG G tn (s with vs_inst_idx := LENGTH sa.cs_current_insts))
Proof
  strip_tac >> drule_all member_navigation_source_endpoint_uniform >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl_tac [`H`,`u`] >> simp[]
QED

Theorem calldata_member_setup_endpoint_ptr:
  abi_decode_member_setup (Var root) src CALLDATALOAD (Lit 0w) (Lit 0w) dyn ao vo sa = (ops,sb) /\
  lookup_var root s = SOME a /\ not_fresh_at sa root /\
  (!q. src = Var q ==> not_fresh_at sa q) /\
  ptr_covers G tn root s cap /\ op_taint tn src = {} /\ op_prov G src = NONE /\
  vo + n <= cap /\ w2n a + vo < dimword(:256) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb ==>
  ?H u q. SND ops = Var q /\
  lookup_var q t = SOME (n2w (w2n a + vo)) /\ ptr_covers H u q t n /\
  op_taint u (FST ops) = {} /\ op_prov H (FST ops) = NONE /\
  t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\ t.vs_allocas = s.vs_allocas /\
  u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
    FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
  ((!fuel. ptr_safe_run D lower fuel ctx func PG H u (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
   !fuel. ptr_safe_run D lower fuel ctx func PG G tn (s with vs_inst_idx := LENGTH sa.cs_current_insts))
Proof
  strip_tac >> drule_all calldata_member_setup_endpoint_ptr_uniform >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl_tac [`H`,`u`,`q`] >> simp[]
QED

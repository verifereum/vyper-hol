(* Pointer-safe scalar/control-flow transport for entry dispatch. *)
Theory entryDispatchPtr
Ancestors ptrSafeRun ptrDiscipline moduleLoweringProps moduleLowering
  fragExec venomExecSemantics venomInst venomState list finite_map words
  contextCodegenRel codegenRel compileEnv emitHelperProps exprLoweringProps typedCopyArrayPtr

Theorem ptr_safe_jump_continuation:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id JMP [Label lbl] []) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!G' tn'. ptr_safe_blocks D lo fuel ctx fn PG G' tn' (jump_to lbl s)) ==>
  ptr_safe_run D lo fuel ctx fn PG G tn s
Proof
  strip_tac >>
  simp[ptr_safe_run_def, Once ptr_safe_block_def] >>
  conj_tac
  >- (simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
           mk_inst_def, source_memory_write_ranges_def,
           source_memory_read_ranges_def, step_inst_non_invoke,
           step_inst_base_def, jump_to_def, op_taint_def]) >>
  simp[step_inst_non_invoke, step_inst_base_def, mk_inst_def,
       is_terminator_def]
QED

Theorem ptr_safe_cond_jump_continuation:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id JNZ [op; Label yes; Label no] []) /\
  eval_operand op s = SOME v /\ op_taint tn op = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ptr_safe_blocks D lo fuel ctx fn PG
    (entry_prov fn (jump_to (if v <> 0w then yes else no) s) G)
    (entry_taint_vars fn (jump_to (if v <> 0w then yes else no) s) tn)
    (jump_to (if v <> 0w then yes else no) s) ==>
  ptr_safe_run D lo fuel ctx fn PG G tn s
Proof
  strip_tac >>
  simp[ptr_safe_run_def, Once ptr_safe_block_def] >>
  conj_tac
  >- (simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
           mk_inst_def, source_memory_write_ranges_def,
           source_memory_read_ranges_def, step_inst_non_invoke,
           step_inst_base_def, jump_to_def, op_taint_def] >>
      Cases_on `v = 0w` >> simp[jump_to_def] >>
      rpt strip_tac >> Cases_on `op'` >> gvs[op_taint_def] >>
      strip_tac >> gvs[]) >>
  simp[step_inst_non_invoke, step_inst_base_def, mk_inst_def,
       is_terminator_def] >>
  Cases_on `v = 0w` >> gvs[]
QED

Theorem ptr_safe_dispatch_scalar_step:
  MEM opc [CALLDATASIZE; CALLDATALOAD; LT; EQ; ISZERO; SHR] /\
  EVERY (\op. op_taint tn op = {}) ops /\
  (!u v. ops <> [Var u; Var v]) /\
  step_inst fuel ctx (mk_inst id opc ops outs) s = OK t /\
  t.vs_requests = s.vs_requests /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ptr_safe_step D lo fuel ctx fn PG G tn (mk_inst id opc ops outs) s
Proof
  strip_tac >>
  fs[MEM] >>
  gvs[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
      mk_inst_def, source_memory_write_ranges_def,
      source_memory_read_ranges_def, EVERY_MEM] >>
  metis_tac[]
QED

Theorem dispatch_scalar_out_taint:
  MEM opc [CALLDATASIZE; CALLDATALOAD; LT; EQ; ISZERO; SHR] /\
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
      gvs[out_taint_def, mk_inst_def, shift_taint_def,
          pred_setTheory.EXTENSION]) >>
  Cases_on `tail` >> simp[out_taint_def, mk_inst_def])
QED

Theorem dispatch_scalar_output_clean:
  MEM opc [CALLDATASIZE; CALLDATALOAD; LT; EQ; ISZERO; SHR] /\
  EVERY (\op. op_taint tn op = {}) ops ==>
  op_taint (step_taint (mk_inst id opc ops [out]) s t tn) (Var out) = {}
Proof
  strip_tac >> drule_all dispatch_scalar_out_taint >> strip_tac >>
  simp[op_taint_def, step_taint_def, mk_inst_def, set_var_taint_def,
       FLOOKUP_UPDATE]
QED

Theorem step_taint_single_output_preserves_other_operand:
  op <> Var out ==>
  op_taint (step_taint (mk_inst id opc ops [out]) s t tn) op = op_taint tn op
Proof
  Cases_on `op` >> simp[op_taint_def, step_taint_def, mk_inst_def,
                        set_var_taint_def, FLOOKUP_UPDATE]
QED

Theorem ptr_safe_run_scalar_continuation:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  step_inst fuel ctx inst s = OK t /\
  ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  t.vs_current_bb = s.vs_current_bb /\
  ptr_safe_step D lo fuel ctx fn PG G tn inst s /\
  ptr_safe_run D lo fuel ctx fn PG (step_prov PG G inst t)
    (step_taint inst s t tn) (t with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ptr_safe_run D lo fuel ctx fn PG G tn s
Proof
  strip_tac >>
  fs[ptr_safe_run_def] >>
  once_rewrite_tac[ptr_safe_block_def] >> simp[ghost_step_def] >> gvs[]
QED

Theorem compile_selector_checks_cons_layout:
  compile_selector_checks mid ((sel,lbl)::sels) st = ((),st') /\
  fn_has_code st st' fn ==>
  ?tail match next bb mb.
    compile_selector_checks mid sels tail = ((),st') /\
    fn_has_code tail st' fn /\
    tail.cs_current_bb = next /\ tail.cs_current_insts = [] /\
    tail.cs_next_var = st.cs_next_var + 1 /\
    lookup_block st.cs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH st.cs_current_insts) =
      SOME (mk_inst st.cs_next_id EQ [mid; Lit (n2w sel)]
        [STRING #"%" (toString st.cs_next_var)]) /\
    get_instruction bb (SUC (LENGTH st.cs_current_insts)) =
      SOME (mk_inst (st.cs_next_id + 1) JNZ
        [Var (STRING #"%" (toString st.cs_next_var)); Label match; Label next] []) /\
    lookup_block match fn.fn_blocks = SOME mb /\
    mb.bb_instructions = [mk_inst (st.cs_next_id + 2) JMP [Label lbl] []]
Proof
  simp[compile_selector_checks_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> fs[]) >> strip_tac >>
  rename1 `new_block next_lbl s6 = (_, s7)` >>
  rename1 `emit_inst JMP _ _ s5 = (_, s6)` >>
  rename1 `new_block match_lbl s4 = (_, s5)` >>
  rename1 `emit_inst JNZ _ _ s3 = (_, s4)` >>
  rename1 `fresh_label "next" s2 = (_, s3)` >>
  rename1 `fresh_label "match" s1 = (_, s2)` >>
  rename1 `emit_op EQ _ st = (_, s1)` >>
  `cs_extends st s1 /\ cs_extends s1 s2 /\ cs_extends s2 s3 /\
   cs_extends s3 s4 /\ cs_extends s4 s5 /\ cs_extends s5 s6 /\
   cs_extends s6 s7 /\ cs_extends s7 st'` by
    (rpt conj_tac >> metis_tac[cs_appends_def, cs_appends_emit_helpers,
       cs_appends_prims, compile_selector_checks_appends]) >>
  `fn_has_code s4 s5 fn /\ fn_has_code s6 s7 fn /\
   fn_has_code s7 st' fn` by
    (rpt conj_tac >> metis_tac[fn_has_code_mid, fn_has_code_split,
                             cs_extends_trans]) >>
  `lookup_block s4.cs_current_bb fn.fn_blocks =
     SOME <| bb_label := s4.cs_current_bb;
             bb_instructions := s4.cs_current_insts |> /\
   lookup_block s6.cs_current_bb fn.fn_blocks =
     SOME <| bb_label := s6.cs_current_bb;
             bb_instructions := s6.cs_current_insts |>` by
    metis_tac[fn_has_code_new_block] >>
  imp_res_tac new_block_props >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac emit_op_extends >>
  imp_res_tac emit_inst_extends >> imp_res_tac fresh_label_props >>
  fs[same_blocks_def] >>
  qmatch_asmsub_abbrev_tac
    `lookup_block st.cs_current_bb fn.fn_blocks = SOME blk` >>
  `get_instruction blk (LENGTH st.cs_current_insts) =
     SOME (mk_inst st.cs_next_id EQ [mid; Lit (n2w sel)]
       [STRING #"%" (toString st.cs_next_var)]) /\
   get_instruction blk (SUC (LENGTH st.cs_current_insts)) =
     SOME (mk_inst (st.cs_next_id + 1) JNZ
       [Var (STRING #"%" (toString st.cs_next_var));
        Label match_lbl; Label next_lbl] [])` by
    simp[Abbr `blk`, get_instruction_def, EL_APPEND_EQN,
         arithmeticTheory.ADD1] >>
  qexistsl_tac [`s7`, `match_lbl`] >>
  simp[] >> metis_tac[]
QED

Theorem ptr_safe_blocks_from_phi_free_run:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  phi_prefix_length bb.bb_instructions = 0 /\ s.vs_inst_idx = 0 /\
  (!fuel. ptr_safe_run D lo fuel ctx fn PG G tn s) ==>
  !fuel. ptr_safe_blocks D lo fuel ctx fn PG G tn s
Proof
  strip_tac >> Cases >> simp[Once ptr_safe_blocks_def] >>
  `eval_phis s bb.bb_instructions = OK s` by
    (Cases_on `bb.bb_instructions` >>
     gvs[eval_phis_def, phi_prefix_length_def, AllCaseEqs()]) >>
  simp[] >>
  qpat_x_assum `!fuel. _` (qspec_then `n` mp_tac) >>
  simp[ptr_safe_run_def] >>
  `s with vs_inst_idx := 0 = s` by
    (Cases_on `s` >> gvs[]) >> simp[]
QED

Theorem compile_selector_checks_phi_free:
  compile_selector_checks mid sels st = ((),st') /\
  fn_has_code st st' fn /\ st.cs_current_insts = [] /\
  (st'.cs_current_insts = [] ==>
    ?bb. lookup_block st'.cs_current_bb fn.fn_blocks = SOME bb /\
         phi_prefix_length bb.bb_instructions = 0) ==>
  ?bb. lookup_block st.cs_current_bb fn.fn_blocks = SOME bb /\
       phi_prefix_length bb.bb_instructions = 0
Proof
  Cases_on `sels`
  >- (simp[compile_selector_checks_def, comp_return_def] >>
      rpt strip_tac >> gvs[]) >>
  PairCases_on `h` >> strip_tac >>
  drule_all compile_selector_checks_cons_layout >> strip_tac >>
  qexists_tac `bb` >> simp[] >>
  qpat_x_assum `get_instruction _ (LENGTH _) = _` mp_tac >>
  Cases_on `bb.bb_instructions` >>
  simp[get_instruction_def, phi_prefix_length_def, mk_inst_def] >>
  strip_tac >> gvs[phi_prefix_length_def, mk_inst_def]
QED

Theorem compile_selector_checks_ptr_continuation:
  !sels mid st st'.
    compile_selector_checks mid sels st = ((), st') ==>
    !ctx fn ss m D lo PG.
      fn_has_code st st' fn /\ eval_operand mid ss = SOME m /\
      fresh_vars_wrt st ss /\ ~ss.vs_halted /\
      ss.vs_current_bb = st.cs_current_bb /\
      ss.vs_inst_idx = LENGTH st.cs_current_insts /\
      allocas_from lo ss /\ (ctx_has_dalloca ctx ==> allocas_below_fmp ss) /\
      (st'.cs_current_insts = [] ==>
        ?bb. lookup_block st'.cs_current_bb fn.fn_blocks = SOME bb /\
             phi_prefix_length bb.bb_instructions = 0) /\
      (!tt G' tn' fuel. vars_pc_only ss tt ==>
        case selector_hit m sels of
          SOME lbl => tt.vs_current_bb = lbl /\ tt.vs_inst_idx = 0 ==>
            ptr_safe_blocks D lo fuel ctx fn PG G' tn' tt
        | NONE => tt.vs_current_bb = st'.cs_current_bb /\
                  tt.vs_inst_idx = LENGTH st'.cs_current_insts ==>
            ptr_safe_run D lo fuel ctx fn PG G' tn' tt) ==>
      !G tn fuel. op_taint tn mid = {} ==>
        ptr_safe_run D lo fuel ctx fn PG G tn ss
Proof
  Induct
  >- (simp[compile_selector_checks_def, comp_return_def, selector_hit_def] >>
      rpt strip_tac >> first_x_assum irule >> simp[vars_pc_only_refl]) >>
  Cases >> rename1 `(sel, lbl)` >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  drule_all compile_selector_checks_cons_layout >> strip_tac >>
  qpat_x_assum `compile_selector_checks mid ((sel,lbl)::sels) _ = _` kall_tac >>
  qpat_x_assum `fn_has_code st st' fn` kall_tac >>
  qabbrev_tac `out = STRING #"%" (toString st.cs_next_var)` >>
  qabbrev_tac `v = bool_to_word (m = n2w sel)` >>
  qabbrev_tac `u = update_var out v ss with vs_inst_idx := SUC ss.vs_inst_idx` >>
  `mid <> Var out` by
    (simp[Abbr `out`] >> strip_tac >> gvs[] >>
     qpat_x_assum `fresh_vars_wrt st ss`
       (qspec_then `st.cs_next_var` mp_tac o REWRITE_RULE [fresh_vars_wrt_def]) >>
     gvs[eval_operand_def, lookup_var_def, TO_FLOOKUP]) >>
  `vars_pc_only ss u` by
    simp[Abbr `u`, vars_pc_only_inst_idx, vars_pc_only_update_var,
         vars_pc_only_refl] >>
  `fresh_vars_wrt tail u` by
    (simp[Abbr `u`, control_moves_keep_vars] >>
     irule fresh_vars_wrt_advance >>
     qexistsl_tac [`st.cs_next_var`, `st`] >> simp[Abbr `out`]) >>
  `eval_operand mid u = SOME m` by
    (simp[Abbr `u`, control_moves_keep_vars] >>
     irule eval_operand_update_fresh >> simp[] >>
     qexistsl_tac [`st.cs_next_var`, `st`] >> simp[Abbr `out`]) >>
  `?nb. lookup_block next fn.fn_blocks = SOME nb /\
        phi_prefix_length nb.bb_instructions = 0` by
    (drule_all compile_selector_checks_phi_free >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  qmatch_asmsub_abbrev_tac `get_instruction bb (LENGTH _) = SOME eqi` >>
  `step_inst fuel ctx eqi ss = OK (update_var out v ss)` by
    simp[Abbr `eqi`, Abbr `v`, step_inst_non_invoke, mk_inst_def,
         step_inst_base_def, exec_pure2_def, eval_operand_def] >>
  irule ptr_safe_run_scalar_continuation >>
  qexistsl_tac [`bb`, `eqi`, `update_var out v ss`] >>
  simp[Abbr `eqi`, is_terminator_def, mk_inst_def, update_var_def] >>
  reverse conj_tac
  >- (irule (REWRITE_RULE [mk_inst_def] ptr_safe_dispatch_scalar_step) >>
      simp[MEM, op_taint_def] >>
      qexists_tac `update_var out v ss` >>
      gvs[mk_inst_def, update_var_def]) >>
  suspend "selector_branch"
QED

Resume compile_selector_checks_ptr_continuation[selector_branch]:
  qpat_x_assum `eval_operand mid ss = _` kall_tac >>
  qpat_x_assum `fresh_vars_wrt st ss` kall_tac >>
  qpat_x_assum `tail.cs_next_var = _` kall_tac >>
  qmatch_goalsub_abbrev_tac `ptr_safe_run D lo fuel ctx fn PG G1 tn1 u` >>
  `op_taint tn1 (Var out) = {}` by
    (simp[Abbr `tn1`] >>
     irule (REWRITE_RULE [mk_inst_def] dispatch_scalar_output_clean) >>
     simp[op_taint_def]) >>
  `op_taint tn1 mid = {}` by
    simp[Abbr `tn1`, GSYM mk_inst_def,
         step_taint_single_output_preserves_other_operand] >>
  `u.vs_current_bb = st.cs_current_bb /\
   u.vs_inst_idx = SUC (LENGTH st.cs_current_insts) /\
   eval_operand (Var out) u = SOME v /\
   allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u)` by
    (fs[Abbr `u`, update_var_def, eval_operand_def, lookup_var_def,
        FLOOKUP_UPDATE, allocas_from_def, allocas_below_fmp_def] >>
     metis_tac[]) >>
  irule ptr_safe_cond_jump_continuation >> simp[] >>
  qexistsl_tac [`st.cs_next_id + 1`, `next`, `Var out`, `v`, `match`] >>
  simp[] >>
  Cases_on `m = n2w sel`
  >- (fs[Abbr `v`, bool_to_word_def, selector_hit_def] >>
      qpat_x_assum `!mid st st'. compile_selector_checks mid sels st = _ ==> _` kall_tac >>
      qpat_x_assum `Abbrev (G1 = _)` kall_tac >>
      qpat_x_assum `Abbrev (tn1 = _)` kall_tac >>
      irule ptr_safe_blocks_from_phi_free_run >>
      reverse conj_tac
      >- simp[jump_to_def, phi_prefix_length_def, mk_inst_def] >>
      gen_tac >> irule ptr_safe_jump_continuation >> simp[jump_to_def] >>
      reverse conj_tac
      >- (fs[allocas_from_def, allocas_below_fmp_def, jump_to_def] >> metis_tac[]) >>
      simp[jump_to_def] >>
      qexistsl_tac [`st.cs_next_id + 2`, `lbl`] >>
      simp[get_instruction_def] >> rpt gen_tac >>
      qpat_x_assum `!tt G' tn' fuel. _` irule >>
      simp[] >>
      qpat_x_assum `vars_pc_only ss u` mp_tac >>
      simp[vars_pc_only_def, jump_to_def, venom_state_component_equality]) >>
  fs[Abbr `v`, bool_to_word_def, selector_hit_def] >>
  `entry_prov fn (jump_to next u) G1 = G1 /\
   entry_taint_vars fn (jump_to next u) tn1 = tn1` by
    (irule entry_ghost_no_phi >> simp[jump_to_def] >> metis_tac[]) >>
  simp[] >> irule ptr_safe_blocks_from_phi_free_run >>
  reverse conj_tac
  >- simp[jump_to_def] >>
  gen_tac >>
  qpat_x_assum `!mid st st'. compile_selector_checks mid sels st = _ ==> _`
    (drule_then mp_tac) >>
  disch_then irule >>
  simp[jump_to_def, control_moves_keep_vars] >>
  conj_tac
  >- simp[Abbr `u`, update_var_def] >>
  reverse conj_tac
  >- (fs[allocas_from_def, allocas_below_fmp_def] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!tt G' tn' fuel. vars_pc_only ss tt ==> _` irule >>
  irule vars_pc_only_trans >> qexists_tac `u` >> simp[] >>
  qpat_x_assum `vars_pc_only _ tt` mp_tac >>
  simp[vars_pc_only_def, venom_state_component_equality]
QED

Finalise compile_selector_checks_ptr_continuation

Theorem compile_selector_dispatch_linear_layout:
  compile_selector_dispatch_linear selectors fallback st = ((),st') /\
  fn_has_code st st' fn ==>
  ?d q r b0 bd br.
    compile_selector_checks (Var (STRING #"%" (toString (st.cs_next_var + 4))))
      selectors q = ((),r) /\ fn_has_code q r fn /\
    q.cs_current_bb = d /\ LENGTH q.cs_current_insts = 2 /\
    q.cs_next_var = st.cs_next_var + 5 /\
    lookup_block st.cs_current_bb fn.fn_blocks = SOME b0 /\
    get_instruction b0 (LENGTH st.cs_current_insts) =
      SOME (mk_inst st.cs_next_id CALLDATASIZE []
        [STRING #"%" (toString st.cs_next_var)]) /\
    get_instruction b0 (SUC (LENGTH st.cs_current_insts)) =
      SOME (mk_inst (st.cs_next_id + 1) LT
        [Var (STRING #"%" (toString st.cs_next_var)); Lit 4w]
        [STRING #"%" (toString (st.cs_next_var + 1))]) /\
    get_instruction b0 (SUC (SUC (LENGTH st.cs_current_insts))) =
      SOME (mk_inst (st.cs_next_id + 2) ISZERO
        [Var (STRING #"%" (toString (st.cs_next_var + 1)))]
        [STRING #"%" (toString (st.cs_next_var + 2))]) /\
    get_instruction b0 (SUC (SUC (SUC (LENGTH st.cs_current_insts)))) =
      SOME (mk_inst (st.cs_next_id + 3) JNZ
        [Var (STRING #"%" (toString (st.cs_next_var + 2))); Label d; Label fallback] []) /\
    lookup_block d fn.fn_blocks = SOME bd /\
    get_instruction bd 0 = SOME (mk_inst (st.cs_next_id + 4) CALLDATALOAD
      [Lit 0w] [STRING #"%" (toString (st.cs_next_var + 3))]) /\
    get_instruction bd 1 = SOME (mk_inst (st.cs_next_id + 5) SHR
      [Lit 224w; Var (STRING #"%" (toString (st.cs_next_var + 3)))]
      [STRING #"%" (toString (st.cs_next_var + 4))]) /\
    phi_prefix_length bd.bb_instructions = 0 /\
    lookup_block r.cs_current_bb fn.fn_blocks = SOME br /\
    get_instruction br (LENGTH r.cs_current_insts) =
      SOME (mk_inst r.cs_next_id JMP [Label fallback] []) /\
    (r.cs_current_insts = [] ==> phi_prefix_length br.bb_instructions = 0)
Proof
  simp[compile_selector_dispatch_linear_def, comp_bind_def,
       comp_ignore_bind_def] >>
  rpt (pairarg_tac >> fs[]) >> strip_tac >>
  rename1 `emit_inst JMP _ _ a9 = (_, st')` >>
  rename1 `compile_selector_checks _ _ a8 = (_, a9)` >>
  rename1 `emit_op SHR _ a7 = (_, a8)` >>
  rename1 `emit_op CALLDATALOAD _ a6 = (_, a7)` >>
  rename1 `new_block dispatch_lbl a5 = (_, a6)` >>
  rename1 `emit_inst JNZ _ _ a4 = (_, a5)` >>
  rename1 `fresh_label "dispatch" a3 = (_, a4)` >>
  rename1 `emit_op ISZERO _ a2 = (_, a3)` >>
  rename1 `emit_op LT _ a1 = (_, a2)` >>
  rename1 `emit_op CALLDATASIZE _ st = (_, a1)` >>
  `cs_extends st a1 /\ cs_extends a1 a2 /\ cs_extends a2 a3 /\
   cs_extends a3 a4 /\ cs_extends a4 a5 /\ cs_extends a5 a6 /\
   cs_extends a6 a7 /\ cs_extends a7 a8 /\ cs_extends a8 a9 /\
   cs_extends a9 st'` by
    (rpt conj_tac >> metis_tac[cs_appends_def, cs_appends_emit_helpers,
      cs_appends_prims, compile_selector_checks_appends]) >>
  `fn_has_code a5 a6 fn /\ fn_has_code a6 a8 fn /\
   fn_has_code a8 a9 fn /\ fn_has_code a9 st' fn` by
    (rpt conj_tac >> metis_tac[fn_has_code_mid, fn_has_code_split,
                             cs_extends_trans]) >>
  `lookup_block a5.cs_current_bb fn.fn_blocks =
   SOME <|bb_label := a5.cs_current_bb;
          bb_instructions := a5.cs_current_insts|>` by
    metis_tac[fn_has_code_new_block] >>
  imp_res_tac new_block_props >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac emit_op_extends >>
  imp_res_tac emit_inst_extends >> imp_res_tac fresh_label_props >>
  fs[same_blocks_def] >>
  `?bd. lookup_block dispatch_lbl fn.fn_blocks = SOME bd /\
     get_instruction bd 0 = SOME (mk_inst (st.cs_next_id + 4) CALLDATALOAD
       [Lit 0w] [STRING #"%" (toString (st.cs_next_var + 3))]) /\
     get_instruction bd 1 = SOME (mk_inst (st.cs_next_id + 5) SHR
       [Lit 224w; Var (STRING #"%" (toString (st.cs_next_var + 3)))]
       [STRING #"%" (toString (st.cs_next_var + 4))])` by
    (qspecl_then [`a6`, `a8`, `fn`,
       `emitted_insts a6 a7 ++ emitted_insts a7 a8`]
       mp_tac fn_has_code_same_block >>
     (impl_tac >- fs[]) >> strip_tac >>
     rename1 `lookup_block a6.cs_current_bb fn.fn_blocks = SOME bd` >>
     first_assum (qspec_then `0` mp_tac) >>
     first_x_assum (qspec_then `1` mp_tac) >>
     simp[] >> rpt strip_tac >> qexists_tac `bd` >> gvs[]) >>
  `?br. lookup_block a9.cs_current_bb fn.fn_blocks = SOME br /\
     get_instruction br (LENGTH a9.cs_current_insts) =
       SOME (mk_inst a9.cs_next_id JMP [Label fallback] [])` by
    (qspecl_then [`a9`, `st'`, `fn`,
       `[mk_inst a9.cs_next_id JMP [Label fallback] []]`]
       mp_tac fn_has_code_same_block >>
     (impl_tac >- fs[]) >> strip_tac >>
     first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  qmatch_asmsub_abbrev_tac
    `lookup_block st.cs_current_bb fn.fn_blocks = SOME blk` >>
  `phi_prefix_length bd.bb_instructions = 0` by
    (qpat_x_assum `get_instruction bd 0 = _` mp_tac >>
     Cases_on `bd.bb_instructions` >>
     simp[get_instruction_def, phi_prefix_length_def, mk_inst_def] >>
     strip_tac >> gvs[phi_prefix_length_def, mk_inst_def]) >>
  `a9.cs_current_insts = [] ==> phi_prefix_length br.bb_instructions = 0` by
    (strip_tac >> qpat_x_assum `get_instruction br _ = _` mp_tac >>
     Cases_on `br.bb_instructions` >>
     simp[get_instruction_def, phi_prefix_length_def, mk_inst_def] >>
     strip_tac >> gvs[phi_prefix_length_def, mk_inst_def]) >>
  qexistsl_tac [`a8`, `a9`] >>
  gvs[Abbr `blk`, get_instruction_def, EL_APPEND_EQN,
       arithmeticTheory.ADD1]
QED

(* Continuation boundaries for memory-free entry control flow. *)
Theory entryDispatchMem
Ancestors
  memSafeRun venomExecSemantics venomExecProofs venomState venomInst
  instMemFrontier fragExecMem list moduleLoweringProps emitHelperProps
  compileEnv moduleLowering stateEquiv finite_map fragExec exprLoweringProps
  emitHelper rich_list freshWrites

Theorem mem_safe_run_terminator_intro[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  is_terminator inst.inst_opcode /\ mem_safe_step fuel ctx inst s /\
  (!t. step_inst fuel ctx inst s = OK t /\ ~t.vs_halted ==>
       mem_safe_blocks fuel ctx fn t) ==>
  mem_safe_run fuel ctx fn s
Proof
  strip_tac >> simp[mem_safe_run_def, Once mem_safe_block_def,
    Once exec_block_def] >>
  Cases_on `step_inst fuel ctx inst s` >> simp[] >>
  rename1 `OK t` >> Cases_on `t.vs_halted` >> simp[]
QED

Theorem mem_safe_blocks_no_phi:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  eval_phis s bb.bb_instructions = OK s /\
  phi_prefix_length bb.bb_instructions = 0 /\
  (!n. mem_safe_run n ctx fn (s with vs_inst_idx := 0)) ==>
  !n. mem_safe_blocks n ctx fn s
Proof
  strip_tac >> Cases
  >- simp[Once mem_safe_blocks_def] >>
  drule_all mem_safe_blocks_run >> simp[]
QED

Theorem mem_safe_run_jmp[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id JMP [Label lbl] []) /\
  (!n. mem_safe_blocks n ctx fn (jump_to lbl s)) ==>
  !n. mem_safe_run n ctx fn s
Proof
  strip_tac >> gen_tac >> irule mem_safe_run_terminator_intro >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  simp[mk_inst_def, is_terminator_def, mem_safe_step_non_invoke,
    step_inst_non_invoke, step_jmp_behavior] >>
  irule below_frontier_no_ranges >> simp[mk_inst_def]
QED

Theorem mem_safe_run_jnz[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id JNZ [cond; Label yes; Label no] []) /\
  eval_operand cond s = SOME w /\
  (!n. mem_safe_blocks n ctx fn (jump_to (if w <> 0w then yes else no) s)) ==>
  !n. mem_safe_run n ctx fn s
Proof
  strip_tac >> gen_tac >> irule mem_safe_run_terminator_intro >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  simp[mk_inst_def, is_terminator_def, mem_safe_step_non_invoke,
    step_inst_non_invoke] >>
  reverse conj_tac
  >- (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  drule step_jnz_behavior >> Cases_on `w = 0w` >> gvs[]
QED

Theorem selector_eq_state_invariants[local]:
  fresh_vars_wrt st ss /\ eval_operand mid ss = SOME m /\
  st.cs_next_var < st'.cs_next_var ==>
  let tt = update_var (STRING #"%" (toString st.cs_next_var)) w ss
             with vs_inst_idx := SUC ss.vs_inst_idx in
    vars_pc_only ss tt /\ fresh_vars_wrt st' tt /\
    (!x. not_fresh_at st x ==> lookup_var x tt = lookup_var x ss) /\
    eval_operand mid tt = SOME m
Proof
  strip_tac >> simp[LET_THM, control_moves_keep_vars] >> conj_tac
  >- (irule vars_pc_only_inst_idx >> irule vars_pc_only_update_var >>
      irule vars_pc_only_refl) >> conj_tac
  >- (irule fresh_vars_wrt_advance >>
      qexistsl_tac [`st.cs_next_var`, `st`] >> simp[]) >> conj_tac
  >- (rw[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
      gvs[not_fresh_at_def]) >>
  irule eval_operand_update_fresh >> simp[] >>
  qexists_tac `st` >> simp[]
QED

Theorem selector_clause_code[local]:
  emit_op EQ [mid; Lit (n2w sel)] st = (op, s1) /\
  fresh_label "match" s1 = (yes, s2) /\
  fresh_label "next" s2 = (no, s3) /\
  emit_inst JNZ [op; Label yes; Label no] [] s3 = ((), s4) /\
  new_block yes s4 = (old, s5) /\
  emit_inst JMP [Label lbl] [] s5 = ((), s6) /\
  new_block no s6 = (old', s7) /\ fn_has_code st s7 fn ==>
  op = Var (STRING #"%" (toString st.cs_next_var)) /\
  s7.cs_next_var = st.cs_next_var + 1 /\
  s7.cs_current_bb = no /\ s7.cs_current_insts = [] /\
  lookup_block st.cs_current_bb fn.fn_blocks = SOME
    <| bb_label := st.cs_current_bb; bb_instructions :=
       st.cs_current_insts ++
       [mk_inst st.cs_next_id EQ [mid; Lit (n2w sel)]
          [STRING #"%" (toString st.cs_next_var)];
        mk_inst (st.cs_next_id + 1) JNZ [op; Label yes; Label no] []] |> /\
  lookup_block yes fn.fn_blocks = SOME
    <| bb_label := yes; bb_instructions :=
       [mk_inst (st.cs_next_id + 2) JMP [Label lbl] []] |>
Proof
  strip_tac >>
  imp_res_tac (SRULE [cs_appends_def] cs_appends_emit_helpers) >>
  imp_res_tac (SRULE [cs_appends_def] cs_appends_prims) >>
  `fn_has_code s4 s5 fn /\ fn_has_code s6 s7 fn` by
    (conj_tac >> irule fn_has_code_mid >>
     goal_assum (drule_at Any) >> metis_tac[cs_extends_trans, cs_extends_refl]) >>
  imp_res_tac fn_has_code_new_block >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac emit_op_extends >>
  imp_res_tac fresh_label_props >> imp_res_tac emit_inst_extends >>
  imp_res_tac new_block_props >> gvs[same_blocks_def, arithmeticTheory.ADD1]
QED

Theorem selector_eq_safe[local]:
  lookup_block ss.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb ss.vs_inst_idx =
    SOME (mk_inst id EQ [mid; Lit (n2w sel)] [name]) /\
  eval_operand mid ss = SOME m /\
  (!n. mem_safe_run n ctx fn
    (update_var name (bool_to_word (m = n2w sel)) ss
      with vs_inst_idx := SUC ss.vs_inst_idx)) ==>
  !n. mem_safe_run n ctx fn ss
Proof
  strip_tac >> gen_tac >>
  `step_inst n ctx (mk_inst id EQ [mid; Lit (n2w sel)] [name]) ss =
     OK (update_var name (bool_to_word (m = n2w sel)) ss)` by
    (simp[step_inst_non_invoke, mk_inst_def] >>
     irule (SRULE [mk_inst_def] step_EQ) >> simp[eval_operand_def]) >>
  `mem_safe_run n ctx fn ss <=>
     (revert_forward_at bb ss.vs_inst_idx \/
       mem_safe_step n ctx (mk_inst id EQ [mid; Lit (n2w sel)] [name]) ss) /\
     mem_safe_run n ctx fn
       (update_var name (bool_to_word (m = n2w sel)) ss
         with vs_inst_idx := SUC ss.vs_inst_idx)` by
    (irule mem_safe_run_step >> goal_assum (drule_at Any) >>
     simp[mk_inst_def, is_terminator_def]) >>
  gvs[] >> disj2_tac >> simp[mem_safe_step_non_invoke, mk_inst_def] >>
  irule below_frontier_no_ranges >> simp[]
QED

Theorem selector_clause_safe_control[local]:
  lookup_block ss.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb ss.vs_inst_idx =
    SOME (mk_inst id EQ [mid; Lit (n2w sel)] [name]) /\
  get_instruction bb (SUC ss.vs_inst_idx) =
    SOME (mk_inst (id + 1) JNZ [Var name; Label yes; Label no] []) /\
  lookup_block yes fn.fn_blocks = SOME
    <| bb_label := yes; bb_instructions := [mk_inst jid JMP [Label lbl] []] |> /\
  eval_operand mid ss = SOME m /\
  tt = (update_var name (bool_to_word (m = n2w sel)) ss
          with vs_inst_idx := SUC ss.vs_inst_idx) /\
  (m = n2w sel ==> !n. mem_safe_blocks n ctx fn
      (jump_to lbl (jump_to yes tt))) /\
  (m <> n2w sel ==> !n. mem_safe_blocks n ctx fn (jump_to no tt)) ==>
  !n. mem_safe_run n ctx fn ss
Proof
  strip_tac >> irule selector_eq_safe >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >>
  qpat_assum `tt = _` (fn th => rewrite_tac[GSYM th]) >>
  irule mem_safe_run_jnz >> qexists_tac `bb` >>
  `tt.vs_current_bb = ss.vs_current_bb /\
   tt.vs_inst_idx = SUC ss.vs_inst_idx /\
   eval_operand (Var name) tt = SOME (bool_to_word (m = n2w sel))` by
    simp[update_var_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
  simp[mk_inst_def] >> Cases_on `m = n2w sel` >> gvs[bool_to_word_def] >>
  irule mem_safe_blocks_no_phi >> reverse conj_tac
  >- (qexists_tac `<| bb_label := yes;
        bb_instructions := [mk_inst jid JMP [Label lbl] []] |>` >>
      simp[jump_to_def, eval_phis_def, phi_prefix_length_def, mk_inst_def]) >>
  irule mem_safe_run_jmp >>
  qexists_tac `<| bb_label := yes;
    bb_instructions := [mk_inst jid JMP [Label lbl] []] |>` >>
  gvs[get_instruction_def, jump_to_def, mk_inst_def]
QED

Theorem selector_clause_mem_safe[local]:
  emit_op EQ [mid; Lit (n2w sel)] st = (op, s1) /\
  fresh_label "match" s1 = (yes, s2) /\
  fresh_label "next" s2 = (no, s3) /\
  emit_inst JNZ [op; Label yes; Label no] [] s3 = ((), s4) /\
  new_block yes s4 = (old, s5) /\
  emit_inst JMP [Label lbl] [] s5 = ((), s6) /\
  new_block no s6 = (old', s7) /\ fn_has_code st s7 fn /\
  fresh_vars_wrt st ss /\ eval_operand mid ss = SOME m /\ ~ss.vs_halted /\
  ss.vs_current_bb = st.cs_current_bb /\
  ss.vs_inst_idx = LENGTH st.cs_current_insts /\
  (!t. vars_pc_only ss t /\ fresh_vars_wrt s7 t /\
       (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x ss) /\
       eval_operand mid t = SOME m /\ ~t.vs_halted /\
       t.vs_current_bb = (if m = n2w sel then lbl else s7.cs_current_bb) /\
       t.vs_inst_idx = 0 ==>
       !n. mem_safe_blocks n ctx fn t) ==>
  !n. mem_safe_run n ctx fn ss
Proof
  strip_tac >> drule_all selector_clause_code >> strip_tac >>
  qabbrev_tac `tt = update_var (STRING #"%" (toString st.cs_next_var))
    (bool_to_word (m = n2w sel)) ss with vs_inst_idx := SUC ss.vs_inst_idx` >>
  `vars_pc_only ss tt /\ fresh_vars_wrt s7 tt /\
   (!x. not_fresh_at st x ==> lookup_var x tt = lookup_var x ss) /\
   eval_operand mid tt = SOME m` by
    (mp_tac (Q.INST [`st'` |-> `s7`,
       `w` |-> `bool_to_word (m = n2w sel)`] selector_eq_state_invariants) >>
     simp[LET_THM, Abbr `tt`]) >>
  `~tt.vs_halted` by (simp[Abbr `tt`, update_var_def]) >>
  irule selector_clause_safe_control >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  simp[get_instruction_def, EL_APPEND_EQN, arithmeticTheory.ADD1,
       mk_inst_def] >>
  qexists_tac `sel` >> simp[] >>
  conj_tac >> strip_tac >> gvs[Abbr `tt`, control_moves_keep_vars] >>
  first_x_assum irule >>
  simp[control_moves_keep_vars, vars_pc_only_jump_to,
       vars_pc_only_inst_idx, vars_pc_only_update_var, vars_pc_only_refl] >>
  simp[jump_to_def]
QED

Theorem selector_checks_entry_no_phi[local]:
  !mid sel lbl rest st st' fn.
  compile_selector_checks mid ((sel,lbl)::rest) st = ((),st') /\
  fn_has_code st st' fn /\ st.cs_current_insts = [] ==>
  ?bb. lookup_block st.cs_current_bb fn.fn_blocks = SOME bb /\
       (!t. eval_phis t bb.bb_instructions = OK t) /\
       phi_prefix_length bb.bb_instructions = 0
Proof
  rpt gen_tac >>
  simp[Once compile_selector_checks_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> fs[]) >> strip_tac >>
  rename1 `new_block next s6 = (_, s7)` >>
  rename1 `emit_inst JMP _ _ s5 = (_, s6)` >>
  rename1 `new_block yes s4 = (_, s5)` >>
  rename1 `emit_inst JNZ _ _ s3 = (_, s4)` >>
  rename1 `fresh_label "next" s2 = (_, s3)` >>
  rename1 `fresh_label "match" s1 = (_, s2)` >>
  rename1 `emit_op EQ _ st = (_, s1)` >>
  imp_res_tac (SRULE [cs_appends_def] cs_appends_emit_helpers) >>
  imp_res_tac (SRULE [cs_appends_def] cs_appends_prims) >>
  imp_res_tac (SRULE [cs_appends_def] compile_selector_checks_appends) >>
  `fn_has_code st s7 fn` by
    (irule fn_has_code_mid >> conj_tac
     >- metis_tac[cs_extends_trans] >>
     qexistsl_tac [`st'`, `st`] >> simp[cs_extends_refl]) >>
  drule_all selector_clause_code >> strip_tac >>
  goal_assum (drule_at Any) >>
  simp[eval_phis_def, phi_prefix_length_def, mk_inst_def]
QED

Theorem selector_checks_entry_safe[local]:
  compile_selector_checks mid ((sel,lbl)::rest) st = ((),st') /\
  fn_has_code st st' fn /\ st.cs_current_insts = [] /\
  ss.vs_current_bb = st.cs_current_bb /\ ss.vs_inst_idx = 0 /\
  (!n. mem_safe_run n ctx fn ss) ==>
  !n. mem_safe_blocks n ctx fn ss
Proof
  strip_tac >> drule_all selector_checks_entry_no_phi >> strip_tac >>
  irule mem_safe_blocks_no_phi >> reverse conj_tac
  >- (goal_assum (drule_at Any) >> simp[]) >>
  qpat_x_assum `ss.vs_inst_idx = 0` (fn th =>
    simp[GSYM th, venom_state_component_equality])
QED

Theorem compile_selector_checks_mem_safe[local]:
  !sels mid st st' fn ss m ctx.
  compile_selector_checks mid sels st = ((), st') /\
  fn_has_code st st' fn /\ eval_operand mid ss = SOME m /\
  fresh_vars_wrt st ss /\ ~ss.vs_halted /\
  ss.vs_current_bb = st.cs_current_bb /\
  ss.vs_inst_idx = LENGTH st.cs_current_insts /\
  (!t. vars_pc_only ss t /\ fresh_vars_wrt st' t /\
       (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x ss) /\
       eval_operand mid t = SOME m /\ ~t.vs_halted ==>
       case selector_hit m sels of
         SOME lbl => (t.vs_current_bb = lbl /\ t.vs_inst_idx = 0 ==>
                       !n. mem_safe_blocks n ctx fn t)
       | NONE => (t.vs_current_bb = st'.cs_current_bb /\
                  t.vs_inst_idx = LENGTH st'.cs_current_insts ==>
                  ((!n. mem_safe_run n ctx fn t) /\
                   (st'.cs_current_insts = [] ==>
                      !n. mem_safe_blocks n ctx fn t)))) ==>
  (!n. mem_safe_run n ctx fn ss) /\
  (st.cs_current_insts = [] ==> !n. mem_safe_blocks n ctx fn ss)
Proof
  Induct
  >- (simp[compile_selector_checks_def, comp_return_def, selector_hit_def] >>
      rpt strip_tac >> first_x_assum (qspec_then `ss` mp_tac) >>
      simp[vars_pc_only_refl]) >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >> strip_tac >>
  `(!n. mem_safe_run n ctx fn ss)` suffices_by
    (strip_tac >> simp[] >> strip_tac >>
     `ss.vs_inst_idx = 0` by simp[] >>
     drule_all selector_checks_entry_safe >> simp[]) >>
  qpat_x_assum `compile_selector_checks _ _ _ = _` mp_tac >>
  simp[Once compile_selector_checks_def, comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `new_block next s6 = (_, s7)` >>
  rename1 `emit_inst JMP _ _ s5 = (_, s6)` >>
  rename1 `new_block yes s4 = (_, s5)` >>
  rename1 `emit_inst JNZ _ _ s3 = (_, s4)` >>
  rename1 `fresh_label "next" s2 = (_, s3)` >>
  rename1 `fresh_label "match" s1 = (_, s2)` >>
  rename1 `emit_op EQ _ st = (_, s1)` >>
  rename1 `emit_inst JNZ _ _ s3 = (u, s4)` >> Cases_on `u` >>
  rename1 `emit_inst JMP _ _ s5 = (u, s6)` >> Cases_on `u` >>
  imp_res_tac (SRULE [cs_appends_def] cs_appends_emit_helpers) >>
  imp_res_tac (SRULE [cs_appends_def] cs_appends_prims) >>
  imp_res_tac (SRULE [cs_appends_def] compile_selector_checks_appends) >>
  imp_res_tac (SRULE [cs_appends_def] (cj 1 cs_appends_emit_helpers)) >>
  `cs_extends st s7` by
    (irule cs_extends_trans >> qexists_tac `s1` >> simp[] >>
     irule cs_extends_trans >> qexists_tac `s2` >> simp[] >>
     irule cs_extends_trans >> qexists_tac `s3` >> simp[] >>
     irule cs_extends_trans >> qexists_tac `s4` >> simp[] >>
     irule cs_extends_trans >> qexists_tac `s5` >> simp[] >>
     irule cs_extends_trans >> qexists_tac `s6` >> simp[]) >>
  `fn_has_code st s7 fn /\ fn_has_code s7 st' fn` by
    metis_tac[fn_has_code_split] >>
  drule selector_clause_mem_safe >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then (fn th => gen_tac >> irule th) >> asm_rewrite_tac [] >>
  qexists_tac `m` >> asm_rewrite_tac [] >>
  gen_tac >> strip_tac >>
  suspend "clause_cont"
QED

Resume compile_selector_checks_mem_safe[clause_cont]:
  Cases_on `m = n2w h0`
  >- (qpat_x_assum `!t. vars_pc_only ss t /\ _ ==> _` (qspec_then `t` mp_tac) >>
      `fresh_vars_wrt st' t` by
        (irule fresh_vars_wrt_mono >> qexists_tac `s7` >>
         asm_rewrite_tac [] >> drule compile_selector_checks_next_var >> simp[]) >>
      asm_rewrite_tac [selector_hit_def, optionTheory.option_case_def] >>
      BETA_TAC >> rewrite_tac []) >>
  `s7.cs_current_insts = []` by
    (drule new_block_props >> simp[]) >>
  qpat_x_assum `!mid st st' fn ss m ctx. _` drule >>
  disch_then (qspecl_then [`fn`, `t`, `m`, `ctx`] mp_tac) >>
  asm_rewrite_tac [] >>
  rewrite_tac [LENGTH] >> impl_tac
  >- (gen_tac >> strip_tac >> suspend "miss_cont") >>
  simp[]
QED
Resume compile_selector_checks_mem_safe[miss_cont]:
  `vars_pc_only ss t'` by metis_tac[vars_pc_only_trans] >>
  `!x. not_fresh_at st x ==> lookup_var x t' = lookup_var x ss` by
    (rpt strip_tac >>
     `not_fresh_at s7 x` by
       (irule not_fresh_at_mono >> qexists_tac `st` >>
        imp_res_tac emitted_insts_emit_op >> imp_res_tac emit_inst_extends >>
        imp_res_tac fresh_label_props >> imp_res_tac new_block_props >> simp[]) >>
     metis_tac[]) >>
  qpat_x_assum `!t. vars_pc_only ss t /\ _ ==> _` (qspec_then `t'` mp_tac) >>
  asm_rewrite_tac [selector_hit_def] >> BETA_TAC >> simp[]
QED
Finalise compile_selector_checks_mem_safe

Theorem linear_dispatch_decompose[local]:
  compile_selector_dispatch_linear sels fallback st = ((), st') ==>
  ?cds small cond dispatch raw mid a1 a2 a3 a4 a5 a6 a7 a8 a9 old.
    emit_op CALLDATASIZE [] st = (cds,a1) /\
    emit_op LT [cds; Lit 4w] a1 = (small,a2) /\
    emit_op ISZERO [small] a2 = (cond,a3) /\
    fresh_label "dispatch" a3 = (dispatch,a4) /\
    emit_inst JNZ [cond; Label dispatch; Label fallback] [] a4 = ((),a5) /\
    new_block dispatch a5 = (old,a6) /\
    emit_op CALLDATALOAD [Lit 0w] a6 = (raw,a7) /\
    emit_op SHR [Lit 224w; raw] a7 = (mid,a8) /\
    compile_selector_checks mid sels a8 = ((),a9) /\
    emit_inst JMP [Label fallback] [] a9 = ((),st')
Proof
  simp[compile_selector_dispatch_linear_def, comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> strip_tac >>
  rpt (goal_assum (drule_at Any))
QED

Theorem linear_size_prefix_code[local]:
  emit_op CALLDATASIZE [] st = (cds,a1) /\
  emit_op LT [cds; Lit 4w] a1 = (small,a2) /\
  emit_op ISZERO [small] a2 = (cond,a3) /\
  fresh_label "dispatch" a3 = (dispatch,a4) /\
  emit_inst JNZ [cond; Label dispatch; Label fallback] [] a4 = ((),a5) /\
  new_block dispatch a5 = (old,a6) /\ fn_has_code st a6 fn ==>
  lookup_block st.cs_current_bb fn.fn_blocks = SOME
    <| bb_label := st.cs_current_bb; bb_instructions := st.cs_current_insts ++
       emitted_insts st a3 ++
       [mk_inst (st.cs_next_id + 3) JNZ
          [cond; Label dispatch; Label fallback] []] |> /\
  emitted_insts st a3 =
    [mk_inst st.cs_next_id CALLDATASIZE []
       [STRING #"%" (toString st.cs_next_var)];
     mk_inst (st.cs_next_id + 1) LT [cds; Lit 4w]
       [STRING #"%" (toString (st.cs_next_var + 1))];
     mk_inst (st.cs_next_id + 2) ISZERO [small]
       [STRING #"%" (toString (st.cs_next_var + 2))]] /\
  LENGTH (emitted_insts st a3) = 3 /\
  a3.cs_current_bb = st.cs_current_bb /\
  a3.cs_current_insts = st.cs_current_insts ++ emitted_insts st a3 /\
  a3.cs_next_var = st.cs_next_var + 3 /\
  a3.cs_next_id = st.cs_next_id + 3 /\
  a6.cs_current_bb = dispatch /\ a6.cs_current_insts = [] /\
  a6.cs_next_var = a3.cs_next_var /\ a6.cs_next_id = a3.cs_next_id + 1
Proof
  strip_tac >>
  imp_res_tac (SRULE [cs_appends_def] cs_appends_emit_helpers) >>
  imp_res_tac (SRULE [cs_appends_def] cs_appends_prims) >>
  `fn_has_code a5 a6 fn` by
    (irule fn_has_code_mid >> reverse conj_tac
     >- (qexistsl_tac [`a6`, `st`] >> simp[cs_extends_refl] >>
         metis_tac[cs_extends_trans]) >> simp[]) >>
  drule_all fn_has_code_new_block >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac emit_op_extends >>
  imp_res_tac emit_inst_extends >> imp_res_tac fresh_label_props >>
  imp_res_tac new_block_props >>
  `emitted_insts st a3 = emitted_insts st a1 ++
     emitted_insts a1 a2 ++ emitted_insts a2 a3` by
    (simp[SimpLHS, emitted_insts_def, APPEND_ASSOC,
          rich_listTheory.DROP_LENGTH_APPEND] >> simp[]) >>
  fs[same_blocks_def] >> simp[APPEND_ASSOC]
QED

Theorem linear_method_prefix_code[local]:
  emit_op CALLDATALOAD [Lit 0w] a6 = (raw,a7) /\
  emit_op SHR [Lit 224w; raw] a7 = (mid,a8) ==>
  emitted_insts a6 a8 =
    [mk_inst a6.cs_next_id CALLDATALOAD [Lit 0w]
       [STRING #"%" (toString a6.cs_next_var)];
     mk_inst (a6.cs_next_id + 1) SHR [Lit 224w; raw]
       [STRING #"%" (toString (a6.cs_next_var + 1))]] /\
  a8.cs_current_bb = a6.cs_current_bb /\
  a8.cs_current_insts = a6.cs_current_insts ++ emitted_insts a6 a8 /\
  a8.cs_next_var = a6.cs_next_var + 2 /\
  a8.cs_next_id = a6.cs_next_id + 2 /\
  mid = Var (STRING #"%" (toString (a6.cs_next_var + 1)))
Proof
  strip_tac >> imp_res_tac emitted_insts_emit_op >>
  imp_res_tac emit_op_extends >>
  `emitted_insts a6 a8 = emitted_insts a6 a7 ++ emitted_insts a7 a8` by
    (irule emitted_insts_append >> simp[]) >>
  fs[same_blocks_def] >> simp[APPEND_ASSOC]
QED

Theorem linear_fallback_code[local]:
  emit_inst JMP [Label fallback] [] a9 = ((),st') /\
  fn_has_code a9 st' fn ==>
  ?bb. lookup_block a9.cs_current_bb fn.fn_blocks = SOME bb /\
       get_instruction bb (LENGTH a9.cs_current_insts) =
         SOME (mk_inst a9.cs_next_id JMP [Label fallback] [])
Proof
  strip_tac >> imp_res_tac emit_inst_extends >>
  drule_all fn_has_code_same_block >> strip_tac >>
  qexists_tac `bb` >> simp[] >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[]
QED

Theorem linear_dispatch_tail_slices[local]:
  emit_op CALLDATALOAD [Lit 0w] a6 = (raw,a7) /\
  emit_op SHR [Lit 224w; raw] a7 = (mid,a8) /\
  compile_selector_checks mid sels a8 = ((),a9) /\
  emit_inst JMP [Label fallback] [] a9 = ((),st') /\
  fn_has_code a6 st' fn ==>
  fn_has_code a6 a8 fn /\ fn_has_code a8 a9 fn /\
  fn_has_code a9 st' fn /\
  a8.cs_next_var <= a9.cs_next_var /\
  st'.cs_next_var = a9.cs_next_var
Proof
  strip_tac >>
  imp_res_tac (SRULE [cs_appends_def] cs_appends_emit_helpers) >>
  imp_res_tac (SRULE [cs_appends_def] compile_selector_checks_appends) >>
  imp_res_tac (SRULE [cs_appends_def] cs_appends_prims) >>
  `cs_extends a6 a8 /\ cs_extends a8 st'` by
    metis_tac[cs_extends_trans] >>
  `fn_has_code a6 a8 fn /\ fn_has_code a8 st' fn` by
    metis_tac[fn_has_code_split] >>
  `fn_has_code a8 a9 fn /\ fn_has_code a9 st' fn` by
    metis_tac[fn_has_code_split] >>
  drule compile_selector_checks_next_var >>
  imp_res_tac emit_inst_extends >> simp[]
QED

Theorem linear_method_entry_no_phi[local]:
  emit_op CALLDATALOAD [Lit 0w] a6 = (raw,a7) /\
  emit_op SHR [Lit 224w; raw] a7 = (mid,a8) /\
  a6.cs_current_insts = [] /\ fn_has_code a6 a8 fn ==>
  ?bb. lookup_block a6.cs_current_bb fn.fn_blocks = SOME bb /\
       (!t. eval_phis t bb.bb_instructions = OK t) /\
       phi_prefix_length bb.bb_instructions = 0
Proof
  strip_tac >> drule_all linear_method_prefix_code >> strip_tac >>
  gvs[fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND] >>
  simp[eval_phis_def, phi_prefix_length_def, mk_inst_def]
QED

Theorem linear_size_entry_no_phi[local]:
  emit_op CALLDATASIZE [] st = (cds,a1) /\
  emit_op LT [cds; Lit 4w] a1 = (small,a2) /\
  emit_op ISZERO [small] a2 = (cond,a3) /\
  fresh_label "dispatch" a3 = (dispatch,a4) /\
  emit_inst JNZ [cond; Label dispatch; Label fallback] [] a4 = ((),a5) /\
  new_block dispatch a5 = (old,a6) /\ fn_has_code st a6 fn /\
  st.cs_current_insts = [] ==>
  ?bb. lookup_block st.cs_current_bb fn.fn_blocks = SOME bb /\
       (!t. eval_phis t bb.bb_instructions = OK t) /\
       phi_prefix_length bb.bb_instructions = 0
Proof
  strip_tac >> drule_all linear_size_prefix_code >> strip_tac >>
  goal_assum (drule_at Any) >>
  simp[eval_phis_def, phi_prefix_length_def, mk_inst_def]
QED

Theorem linear_size_ops_eval[local]:
  LENGTH ss.vs_call_ctx.cc_calldata < dimword(:256) ==>
  ?u. run_inst_seq
       [mk_inst id CALLDATASIZE [] [x];
        mk_inst (id+1) LT [Var x; Lit 4w] [y];
        mk_inst (id+2) ISZERO [Var y] [z]] ss = OK u /\
      u = update_var z (bool_to_word (4 <= LENGTH ss.vs_call_ctx.cc_calldata))
            (update_var y (bool_to_word (LENGTH ss.vs_call_ctx.cc_calldata < 4))
              (update_var x (n2w (LENGTH ss.vs_call_ctx.cc_calldata)) ss)) /\
      eval_operand (Var z) u =
        SOME (bool_to_word (4 <= LENGTH ss.vs_call_ctx.cc_calldata))
Proof
  strip_tac >>
  qabbrev_tac `u1 = update_var x (n2w (LENGTH ss.vs_call_ctx.cc_calldata)) ss` >>
  qabbrev_tac `w = bool_to_word
     (w2n (n2w (LENGTH ss.vs_call_ctx.cc_calldata):bytes32) < w2n (4w:bytes32))` >>
  qabbrev_tac `u2 = update_var y w u1` >>
  qabbrev_tac `u3 = update_var z (bool_to_word (w = 0w)) u2` >>
  `step_inst_base (mk_inst id CALLDATASIZE [] [x]) ss = OK u1` by
    simp[step_CALLDATASIZE, Abbr `u1`] >>
  `step_inst_base (mk_inst (id+1) LT [Var x; Lit 4w] [y]) u1 = OK u2` by
    (qunabbrev_tac `u2` >> qunabbrev_tac `w` >> irule step_LT >>
     simp[Abbr `u1`, eval_operand_update_var, eval_operand_lit]) >>
  `step_inst_base (mk_inst (id+2) ISZERO [Var y] [z]) u2 = OK u3` by
    (simp[Abbr `u3`] >> irule step_ISZERO >>
     simp[Abbr `u2`, eval_operand_update_var]) >>
  qexists_tac `u3` >> conj_tac
  >- simp[run_inst_seq_def] >> conj_tac
  >- (simp[Abbr `u3`, Abbr `u2`, Abbr `u1`, Abbr `w`, wordsTheory.dimword_def] >>
      Cases_on `LENGTH ss.vs_call_ctx.cc_calldata < 4` >> simp[bool_to_word_def]) >>
  simp[Abbr `u3`, eval_operand_update_var] >>
  simp[Abbr `w`, wordsTheory.dimword_def] >>
  Cases_on `LENGTH ss.vs_call_ctx.cc_calldata < 4` >> simp[bool_to_word_def]
QED

Theorem linear_method_ops_eval[local]:
  4 <= LENGTH ss.vs_call_ctx.cc_calldata ==>
  ?u. run_inst_seq
       [mk_inst id CALLDATALOAD [Lit 0w] [x];
        mk_inst (id+1) SHR [Lit 224w; Var x] [y]] ss = OK u /\
      u = update_var y (calldata_method_id ss.vs_call_ctx.cc_calldata)
            (update_var x (word_of_bytes T (0w:bytes32)
              (TAKE 32 (ss.vs_call_ctx.cc_calldata ++ REPLICATE 32 0w))) ss) /\
      eval_operand (Var y) u = SOME (calldata_method_id ss.vs_call_ctx.cc_calldata)
Proof
  strip_tac >>
  qabbrev_tac `w = word_of_bytes T (0w:bytes32)
     (TAKE 32 (ss.vs_call_ctx.cc_calldata ++ REPLICATE 32 0w))` >>
  qabbrev_tac `u1 = update_var x w ss` >>
  qabbrev_tac `u2 = update_var y (w >>> w2n (224w:bytes32)) u1` >>
  `step_inst_base (mk_inst id CALLDATALOAD [Lit 0w] [x]) ss = OK u1` by
    (qunabbrev_tac `u1` >> qunabbrev_tac `w` >>
     qspec_then `Lit 0w` mp_tac step_CALLDATALOAD >>
     simp[eval_operand_lit]) >>
  `step_inst_base (mk_inst (id+1) SHR [Lit 224w; Var x] [y]) u1 = OK u2` by
    (qunabbrev_tac `u2` >>
     irule step_SHR >> simp[Abbr `u1`, eval_operand_update_var, eval_operand_lit]) >>
  qexists_tac `u2` >> conj_tac
  >- simp[run_inst_seq_def] >>
  simp[Abbr `u2`, Abbr `u1`, eval_operand_update_var, Abbr `w`,
       wordsTheory.dimword_def, calldataload_0_shr_224]
QED

Theorem linear_size_ops_mem[local]:
  let code = [mk_inst id CALLDATASIZE [] [x];
              mk_inst (id+1) LT [Var x; Lit 4w] [y];
              mk_inst (id+2) ISZERO [Var y] [z]] in
    run_inst_seq_mem_ok code ss /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code
Proof
  simp[LET_THM, mk_inst_def, is_terminator_def] >>
  irule run_inst_seq_mem_ok_every >> simp[EVERY_DEF] >>
  rpt conj_tac >> gen_tac >> irule below_frontier_no_ranges >> simp[mk_inst_def]
QED

Theorem linear_method_ops_mem[local]:
  let code = [mk_inst id CALLDATALOAD [Lit 0w] [x];
              mk_inst (id+1) SHR [Lit 224w; Var x] [y]] in
    run_inst_seq_mem_ok code ss /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code
Proof
  simp[LET_THM, mk_inst_def, is_terminator_def] >>
  irule run_inst_seq_mem_ok_every >> simp[EVERY_DEF] >>
  rpt conj_tac >> gen_tac >> irule below_frontier_no_ranges >> simp[mk_inst_def]
QED

Theorem linear_size_prefix_eval[local]:
  emit_op CALLDATASIZE [] st = (cds,a1) /\
  emit_op LT [cds; Lit 4w] a1 = (small,a2) /\
  emit_op ISZERO [small] a2 = (cond,a3) /\
  fresh_vars_wrt st ss /\ LENGTH ss.vs_call_ctx.cc_calldata < dimword(:256) ==>
  ?u. run_inst_seq (emitted_insts st a3) ss = OK u /\
      eval_operand cond u = SOME (bool_to_word (4 <= LENGTH ss.vs_call_ctx.cc_calldata)) /\
      vars_pc_only ss u /\ fresh_vars_wrt a3 u /\
      (!x. not_fresh_at st x ==> lookup_var x u = lookup_var x ss) /\
      u.vs_current_bb = ss.vs_current_bb /\ u.vs_halted = ss.vs_halted /\
      u.vs_inst_idx = ss.vs_inst_idx
Proof
  strip_tac >> imp_res_tac emitted_insts_emit_op >> imp_res_tac emit_op_extends >>
  `emitted_insts st a3 = emitted_insts st a1 ++
     emitted_insts a1 a2 ++ emitted_insts a2 a3` by
    (simp[SimpLHS, emitted_insts_def, APPEND_ASSOC,
          rich_listTheory.DROP_LENGTH_APPEND] >> simp[]) >>
  drule linear_size_ops_eval >>
  disch_then (qspecl_then [`STRING #"%" (toString (st.cs_next_var+2))`,
     `STRING #"%" (toString (st.cs_next_var+1))`,
     `STRING #"%" (toString st.cs_next_var)`, `st.cs_next_id`] mp_tac) >>
  strip_tac >> qexists_tac `u` >> conj_tac
  >- simp[APPEND_ASSOC] >> conj_tac
  >- simp[eval_operand_update_var] >> conj_tac
  >- (simp[] >> rpt (irule vars_pc_only_update_var) >> irule vars_pc_only_refl) >>
  conj_tac
  >- (simp[] >> irule fresh_vars_wrt_advance >>
      qexistsl_tac [`st.cs_next_var+2`, `st with cs_next_var := st.cs_next_var+2`] >>
      simp[] >> irule fresh_vars_wrt_advance >>
      qexistsl_tac [`st.cs_next_var+1`, `st with cs_next_var := st.cs_next_var+1`] >>
      simp[] >> irule fresh_vars_wrt_advance >>
      qexistsl_tac [`st.cs_next_var`, `st`] >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
      gvs[not_fresh_at_def]) >>
  simp[update_var_def]
QED

Theorem linear_method_prefix_eval[local]:
  emit_op CALLDATALOAD [Lit 0w] a6 = (raw,a7) /\
  emit_op SHR [Lit 224w; raw] a7 = (mid,a8) /\
  fresh_vars_wrt a6 ss /\ 4 <= LENGTH ss.vs_call_ctx.cc_calldata ==>
  ?u. run_inst_seq (emitted_insts a6 a8) ss = OK u /\
      eval_operand mid u = SOME (calldata_method_id ss.vs_call_ctx.cc_calldata) /\
      vars_pc_only ss u /\ fresh_vars_wrt a8 u /\
      (!x. not_fresh_at a6 x ==> lookup_var x u = lookup_var x ss) /\
      u.vs_current_bb = ss.vs_current_bb /\ u.vs_halted = ss.vs_halted /\
      u.vs_inst_idx = ss.vs_inst_idx
Proof
  strip_tac >> drule_all linear_method_prefix_code >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >>
  drule linear_method_ops_eval >>
  disch_then (qspecl_then [`STRING #"%" (toString (a6.cs_next_var+1))`,
     `STRING #"%" (toString a6.cs_next_var)`, `a6.cs_next_id`] mp_tac) >>
  strip_tac >> qexists_tac `u` >> conj_tac
  >- simp[] >> conj_tac
  >- simp[eval_operand_update_var] >> conj_tac
  >- (simp[] >> rpt (irule vars_pc_only_update_var) >> irule vars_pc_only_refl) >>
  conj_tac
  >- (simp[] >> irule fresh_vars_wrt_advance >>
      qexistsl_tac [`a6.cs_next_var+1`, `a6 with cs_next_var := a6.cs_next_var+1`] >>
      simp[] >> irule fresh_vars_wrt_advance >>
      qexistsl_tac [`a6.cs_next_var`, `a6`] >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
      gvs[not_fresh_at_def]) >>
  simp[update_var_def]
QED

Theorem linear_fallback_mem_safe[local]:
  emit_inst JMP [Label fallback] [] a9 = ((),st') /\
  fn_has_code a9 st' fn /\
  ss.vs_current_bb = a9.cs_current_bb /\
  ss.vs_inst_idx = LENGTH a9.cs_current_insts /\
  (!n. mem_safe_blocks n ctx fn (jump_to fallback ss)) ==>
  (!n. mem_safe_run n ctx fn ss) /\
  (a9.cs_current_insts = [] ==> !n. mem_safe_blocks n ctx fn ss)
Proof
  strip_tac >> drule_all linear_fallback_code >> strip_tac >>
  `!n. mem_safe_run n ctx fn ss` by
    (irule mem_safe_run_jmp >> qexists_tac `bb` >> simp[] >>
     qexistsl_tac [`a9.cs_next_id`, `fallback`] >> simp[]) >>
  simp[] >> strip_tac >>
  `ss with vs_inst_idx := 0 = ss` by
    (gvs[] >> metis_tac[venom_state_component_equality]) >>
  irule mem_safe_blocks_no_phi >> simp[] >> gvs[] >>
  `?rest. bb.bb_instructions = mk_inst a9.cs_next_id JMP [Label fallback] [] :: rest` by
    (Cases_on `bb.bb_instructions` >> gvs[get_instruction_def]) >>
  simp[eval_phis_def, phi_prefix_length_def, mk_inst_def]
QED

Theorem linear_method_prefix_mem_safe[local]:
  emit_op CALLDATALOAD [Lit 0w] a6 = (raw,a7) /\
  emit_op SHR [Lit 224w; raw] a7 = (mid,a8) /\
  fn_has_code a6 a8 fn /\ fresh_vars_wrt a6 ss /\
  4 <= LENGTH ss.vs_call_ctx.cc_calldata /\
  ss.vs_current_bb = a6.cs_current_bb /\
  ss.vs_inst_idx = LENGTH a6.cs_current_insts /\
  (!t. eval_operand mid t = SOME (calldata_method_id ss.vs_call_ctx.cc_calldata) /\
       vars_pc_only ss t /\ fresh_vars_wrt a8 t /\
       (!x. not_fresh_at a6 x ==> lookup_var x t = lookup_var x ss) /\
       t.vs_current_bb = a8.cs_current_bb /\ t.vs_halted = ss.vs_halted /\
       t.vs_inst_idx = LENGTH a8.cs_current_insts ==>
       !n. mem_safe_run n ctx fn t) ==>
  !n. mem_safe_run n ctx fn ss
Proof
  strip_tac >> drule_all linear_method_prefix_eval >> strip_tac >>
  drule_all linear_method_prefix_code >> strip_tac >>
  `?bb. lookup_block ss.vs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts a6 a8) (DROP ss.vs_inst_idx bb.bb_instructions)` by
    (gvs[fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC] >>
     pure_rewrite_tac[rich_listTheory.DROP_LENGTH_APPEND, APPEND] >>
     qexists_tac `l` >> REFL_TAC) >>
  `run_inst_seq_mem_ok (emitted_insts a6 a8) ss /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts a6 a8)` by
    (imp_res_tac emitted_insts_emit_op >> simp[is_terminator_def] >>
     irule (SRULE [LET_THM, is_terminator_def] linear_method_ops_mem)) >>
  `!n. mem_safe_run n ctx fn (u with vs_inst_idx := LENGTH a8.cs_current_insts)` by
    (first_x_assum irule >> simp[control_moves_keep_vars] >>
     irule vars_pc_only_inst_idx >> simp[]) >>
  gen_tac >> drule_all mem_safe_run_inst_seq >>
  disch_then (qspecl_then [`n`, `ctx`] mp_tac) >> gvs[]
QED

Theorem linear_size_prefix_mem_safe[local]:
  emit_op CALLDATASIZE [] st = (cds,a1) /\
  emit_op LT [cds; Lit 4w] a1 = (small,a2) /\
  emit_op ISZERO [small] a2 = (cond,a3) /\
  fresh_label "dispatch" a3 = (dispatch,a4) /\
  emit_inst JNZ [cond; Label dispatch; Label fallback] [] a4 = ((),a5) /\
  new_block dispatch a5 = (old,a6) /\ fn_has_code st a6 fn /\
  fresh_vars_wrt st ss /\ LENGTH ss.vs_call_ctx.cc_calldata < dimword(:256) /\
  ss.vs_current_bb = st.cs_current_bb /\
  ss.vs_inst_idx = LENGTH st.cs_current_insts /\
  (!t. eval_operand cond t = SOME (bool_to_word (4 <= LENGTH ss.vs_call_ctx.cc_calldata)) /\
       vars_pc_only ss t /\ fresh_vars_wrt a3 t /\
       (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x ss) /\
       t.vs_current_bb = a3.cs_current_bb /\ t.vs_halted = ss.vs_halted /\
       t.vs_inst_idx = LENGTH a3.cs_current_insts ==>
       !n. mem_safe_run n ctx fn t) ==>
  !n. mem_safe_run n ctx fn ss
Proof
  strip_tac >> drule_all linear_size_prefix_eval >> strip_tac >>
  drule_all linear_size_prefix_code >> strip_tac >>
  `?bb. lookup_block ss.vs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts st a3) (DROP ss.vs_inst_idx bb.bb_instructions)` by
    (simp[] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
     pure_rewrite_tac[rich_listTheory.DROP_LENGTH_APPEND, APPEND] >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts st a3) ss /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts st a3)` by
    (imp_res_tac emitted_insts_emit_op >> imp_res_tac emit_op_extends >>
     simp[is_terminator_def] >>
     irule (SRULE [LET_THM, is_terminator_def] linear_size_ops_mem)) >>
  `!n. mem_safe_run n ctx fn (u with vs_inst_idx := LENGTH a3.cs_current_insts)` by
    (first_x_assum irule >> simp[control_moves_keep_vars] >>
     irule vars_pc_only_inst_idx >> simp[]) >>
  gen_tac >> drule_all mem_safe_run_inst_seq >>
  disch_then (qspecl_then [`n`, `ctx`] mp_tac) >> gvs[]
QED

Theorem linear_selector_tail_mem_safe[local]:
  compile_selector_checks mid sels a8 = ((),a9) /\
  emit_inst JMP [Label fallback] [] a9 = ((),st') /\
  fn_has_code a8 st' fn /\ eval_operand mid ss = SOME m /\
  fresh_vars_wrt a8 ss /\ ~ss.vs_halted /\
  ss.vs_current_bb = a8.cs_current_bb /\
  ss.vs_inst_idx = LENGTH a8.cs_current_insts /\
  (!t. vars_pc_only ss t /\ fresh_vars_wrt st' t /\
       (!x. not_fresh_at a8 x ==> lookup_var x t = lookup_var x ss) /\
       ~t.vs_halted /\
       t.vs_current_bb = (case selector_hit m sels of SOME l => l | NONE => fallback) /\
       t.vs_inst_idx = 0 ==> !n. mem_safe_blocks n ctx fn t) ==>
  (!n. mem_safe_run n ctx fn ss) /\
  (a8.cs_current_insts = [] ==> !n. mem_safe_blocks n ctx fn ss)
Proof
  strip_tac >> imp_res_tac emit_inst_extends >>
  imp_res_tac (SRULE [cs_appends_def] cs_appends_emit_helpers) >>
  imp_res_tac (SRULE [cs_appends_def] compile_selector_checks_appends) >>
  `fn_has_code a8 a9 fn /\ fn_has_code a9 st' fn` by
    metis_tac[fn_has_code_split] >>
  drule compile_selector_checks_next_var >> strip_tac >>
  drule compile_selector_checks_mem_safe >>
  disch_then (qspecl_then [`fn`, `ss`, `m`, `ctx`] mp_tac) >>
  asm_rewrite_tac[] >> impl_tac
  >- (gen_tac >> strip_tac >>
      `fresh_vars_wrt st' t` by
        (irule fresh_vars_wrt_mono >> qexists_tac `a9` >> simp[]) >>
      Cases_on `selector_hit m sels` >> simp[]
      >- (strip_tac >> irule linear_fallback_mem_safe >>
          goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
          qexistsl_tac [`fallback`, `st'`] >> asm_rewrite_tac[] >>
          `vars_pc_only ss (jump_to fallback t)` by
            (irule vars_pc_only_jump_to >> simp[]) >>
          gen_tac >> first_x_assum irule >>
          simp[control_moves_keep_vars, jump_to_def]) >>
      strip_tac >> first_x_assum irule >> simp[]) >>
  simp[]
QED

Theorem linear_dispatch_method_mem_safe[local]:
  emit_op CALLDATALOAD [Lit 0w] a6 = (raw,a7) /\
  emit_op SHR [Lit 224w; raw] a7 = (mid,a8) /\
  compile_selector_checks mid sels a8 = ((),a9) /\
  emit_inst JMP [Label fallback] [] a9 = ((),st') /\
  fn_has_code a6 st' fn /\
  EVERY (\(sel,lbl). sel < 2 ** 32) sels /\
  fresh_vars_wrt a6 ss /\ ~ss.vs_halted /\
  4 <= LENGTH ss.vs_call_ctx.cc_calldata /\
  ss.vs_current_bb = a6.cs_current_bb /\
  ss.vs_inst_idx = LENGTH a6.cs_current_insts /\
  (!t. vars_pc_only ss t /\ fresh_vars_wrt st' t /\
       (!x. not_fresh_at a6 x ==> lookup_var x t = lookup_var x ss) /\
       ~t.vs_halted /\
       t.vs_current_bb = linear_dispatch_target ss.vs_call_ctx.cc_calldata sels fallback /\
       t.vs_inst_idx = 0 ==> !n. mem_safe_blocks n ctx fn t) ==>
  !n. mem_safe_run n ctx fn ss
Proof
  strip_tac >> drule_all linear_dispatch_tail_slices >> strip_tac >>
  drule_all linear_method_prefix_code >> strip_tac >>
  imp_res_tac (SRULE [cs_appends_def] cs_appends_emit_helpers) >>
  imp_res_tac (SRULE [cs_appends_def] compile_selector_checks_appends) >>
  `cs_extends a6 a8 /\ cs_extends a8 st'` by metis_tac[cs_extends_trans] >>
  `fn_has_code a8 st' fn` by metis_tac[fn_has_code_split] >>
  irule linear_method_prefix_mem_safe >> asm_rewrite_tac[] >>
  qexistsl_tac [`a6`, `a7`, `a8`, `mid`, `raw`] >> asm_rewrite_tac[] >>
  gen_tac >> strip_tac >>
  drule linear_selector_tail_mem_safe >> disch_then drule >>
  disch_then (irule o cj 1) >> asm_rewrite_tac[] >>
  qexists_tac `calldata_method_id ss.vs_call_ctx.cc_calldata` >>
  asm_rewrite_tac[] >> gen_tac >> strip_tac >>
  `vars_pc_only ss t'` by metis_tac[vars_pc_only_trans] >>
  `!x. not_fresh_at a6 x ==> lookup_var x t' = lookup_var x ss` by
    (rpt strip_tac >>
     `not_fresh_at a8 x` by
       (irule not_fresh_at_mono >> qexists_tac `a6` >> simp[]) >>
     metis_tac[]) >>
  first_x_assum irule >>
  drule_all linear_dispatch_target_selector_hit >> simp[]
QED

Theorem linear_dispatch_front_mem_safe[local]:
  emit_op CALLDATASIZE [] st = (cds,a1) /\
  emit_op LT [cds; Lit 4w] a1 = (small,a2) /\
  emit_op ISZERO [small] a2 = (cond,a3) /\
  fresh_label "dispatch" a3 = (dispatch,a4) /\
  emit_inst JNZ [cond; Label dispatch; Label fallback] [] a4 = ((),a5) /\
  new_block dispatch a5 = (old,a6) /\ fn_has_code st a6 fn /\
  fresh_vars_wrt st ss /\ ~ss.vs_halted /\
  LENGTH ss.vs_call_ctx.cc_calldata < dimword(:256) /\
  ss.vs_current_bb = st.cs_current_bb /\
  ss.vs_inst_idx = LENGTH st.cs_current_insts /\
  (!t. vars_pc_only ss t /\ fresh_vars_wrt a3 t /\
       (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x ss) /\
       ~t.vs_halted /\ t.vs_inst_idx = 0 /\
       t.vs_current_bb = (if 4 <= LENGTH ss.vs_call_ctx.cc_calldata
                          then dispatch else fallback) ==>
       !n. mem_safe_blocks n ctx fn t) ==>
  (!n. mem_safe_run n ctx fn ss) /\
  (st.cs_current_insts = [] ==> !n. mem_safe_blocks n ctx fn ss)
Proof
  strip_tac >> drule_all linear_size_prefix_code >> strip_tac >>
  `!n. mem_safe_run n ctx fn ss` by
    (drule linear_size_prefix_mem_safe >> disch_then drule >> disch_then drule >>
     disch_then drule >> disch_then drule >> disch_then drule >>
     disch_then irule >> asm_rewrite_tac[] >> gen_tac >> strip_tac >>
     irule mem_safe_run_jnz >>
     qexists_tac `<| bb_label := st.cs_current_bb; bb_instructions :=
       st.cs_current_insts ++ emitted_insts st a3 ++
       [mk_inst (st.cs_next_id + 3) JNZ [cond; Label dispatch; Label fallback] []] |>` >>
     asm_rewrite_tac[] >>
     qexistsl_tac [`cond`, `st.cs_next_id+3`, `fallback`,
                   `bool_to_word (4 <= LENGTH ss.vs_call_ctx.cc_calldata)`, `dispatch`] >>
     simp[get_instruction_def, EL_APPEND2] >>
     Cases_on `4 <= LENGTH ss.vs_call_ctx.cc_calldata` >> simp[bool_to_word_def] >>
     `!lbl. vars_pc_only ss (jump_to lbl t)` by
       (gen_tac >> irule vars_pc_only_jump_to >> simp[]) >>
     first_x_assum irule >> simp[control_moves_keep_vars, jump_to_def]) >>
  simp[] >> strip_tac >>
  `ss with vs_inst_idx := 0 = ss` by
    (gvs[] >> metis_tac[venom_state_component_equality]) >>
  drule_all linear_size_entry_no_phi >> strip_tac >>
  irule mem_safe_blocks_no_phi >> simp[]
QED

Theorem compile_selector_dispatch_linear_mem_safe:
  compile_selector_dispatch_linear sels fallback st = ((),st') /\
  fn_has_code st st' fn /\ EVERY (\(sel,lbl). sel < 2 ** 32) sels /\
  LENGTH ss.vs_call_ctx.cc_calldata < dimword(:256) /\
  fresh_vars_wrt st ss /\ ~ss.vs_halted /\
  ss.vs_current_bb = st.cs_current_bb /\
  ss.vs_inst_idx = LENGTH st.cs_current_insts /\
  (!t. vars_pc_only ss t /\ fresh_vars_wrt st' t /\
       (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x ss) /\
       ~t.vs_halted /\
       t.vs_current_bb = linear_dispatch_target ss.vs_call_ctx.cc_calldata sels fallback /\
       t.vs_inst_idx = 0 ==> !n. mem_safe_blocks n ctx fn t) ==>
  (!n. mem_safe_run n ctx fn ss) /\
  (st.cs_current_insts = [] ==> !n. mem_safe_blocks n ctx fn ss)
Proof
  strip_tac >> drule linear_dispatch_decompose >> strip_tac >>
  imp_res_tac (SRULE [cs_appends_def] cs_appends_emit_helpers) >>
  imp_res_tac (SRULE [cs_appends_def] cs_appends_prims) >>
  imp_res_tac (SRULE [cs_appends_def] compile_selector_checks_appends) >>
  `cs_extends st a3` by
    (irule cs_extends_trans >> qexists_tac `a1` >> simp[] >>
     irule cs_extends_trans >> qexists_tac `a2` >> simp[]) >>
  `cs_extends st a6` by
    (irule cs_extends_trans >> qexists_tac `a3` >> simp[] >>
     irule cs_extends_trans >> qexists_tac `a4` >> simp[] >>
     irule cs_extends_trans >> qexists_tac `a5` >> simp[]) >>
  `cs_extends a6 st'` by
    (irule cs_extends_trans >> qexists_tac `a7` >> simp[] >>
     irule cs_extends_trans >> qexists_tac `a8` >> simp[] >>
     irule cs_extends_trans >> qexists_tac `a9` >> simp[]) >>
  `fn_has_code st a6 fn /\ fn_has_code a6 st' fn` by
    metis_tac[fn_has_code_split] >>
  drule_all linear_size_prefix_code >> strip_tac >>
  drule_all linear_dispatch_tail_slices >> strip_tac >>
  drule_all linear_method_prefix_code >> strip_tac >>
  drule linear_dispatch_front_mem_safe >> disch_then drule >> disch_then drule >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then irule >> asm_rewrite_tac[] >> gen_tac >> strip_tac >>
  suspend "dispatch_cont"
QED

Resume compile_selector_dispatch_linear_mem_safe[dispatch_cont]:
  rpt (qpat_x_assum `cs_extends _ _` kall_tac) >>
  rpt (qpat_x_assum `emitted_insts _ _ = _` kall_tac) >>
  qpat_x_assum `LENGTH (emitted_insts _ _) = _` kall_tac >>
  qpat_x_assum `lookup_block _ _ = _` kall_tac >>
  qpat_x_assum `compile_selector_dispatch_linear _ _ _ = _` kall_tac >>
  qpat_x_assum `emit_op CALLDATASIZE _ _ = _` kall_tac >>
  qpat_x_assum `emit_op LT _ _ = _` kall_tac >>
  qpat_x_assum `emit_op ISZERO _ _ = _` kall_tac >>
  qpat_x_assum `fresh_label _ _ = _` kall_tac >>
  qpat_x_assum `emit_inst JNZ _ _ _ = _` kall_tac >>
  qpat_x_assum `new_block _ _ = _` kall_tac >>
  `fresh_vars_wrt a6 t` by
    (irule fresh_vars_wrt_mono >> qexists_tac `a3` >> simp[]) >>
  `fresh_vars_wrt st' t` by
    (irule fresh_vars_wrt_mono >> qexists_tac `a6` >> simp[]) >>
  drule vars_pc_only_fields >> strip_tac >>
  Cases_on `4 <= LENGTH ss.vs_call_ctx.cc_calldata`
  >- suspend "method_cont" >>
  first_x_assum irule >> simp[linear_dispatch_target_short]
QED

Resume compile_selector_dispatch_linear_mem_safe[method_cont]:
  `t with vs_inst_idx := 0 = t` by
    simp[venom_state_component_equality] >>
  drule_all linear_method_entry_no_phi >> strip_tac >>
  irule mem_safe_blocks_no_phi >> simp[] >>
  reverse conj_tac >- (qexists_tac `bb` >> gvs[]) >>
  drule linear_dispatch_method_mem_safe >> disch_then drule >>
  disch_then drule >> disch_then drule >> disch_then irule >>
  simp[] >> gen_tac >> strip_tac >>
  `vars_pc_only ss t'` by metis_tac[vars_pc_only_trans] >>
  `!x. not_fresh_at st x ==> lookup_var x t' = lookup_var x ss` by
    (rpt strip_tac >>
     `not_fresh_at a6 x` by
       (irule not_fresh_at_mono >> qexists_tac `st` >> simp[]) >>
     metis_tac[]) >>
  qpat_x_assum `!t. vars_pc_only ss t /\ _ ==> _` irule >> simp[]
QED
Finalise compile_selector_dispatch_linear_mem_safe

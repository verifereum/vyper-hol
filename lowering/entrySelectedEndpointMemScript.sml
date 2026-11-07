(* Joint endpoint boundaries for memory-free selected entry control. *)
Theory entrySelectedEndpointMem
Ancestors
  entryDispatchMem memSafeRun venomExecSemantics venomExecProofs
  venomState venomInst instMemFrontier fragExecMem moduleLoweringProps
  emitHelperProps compileEnv moduleLowering stateEquiv fragExec
  exprLoweringProps emitHelper freshWrites rich_list

Theorem entry_terminator_endpoint_safe[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  step_inst_base inst s = OK t /\ ~t.vs_halted /\
  inst_mem_below_frontier inst s /\ inst_dload_in_section inst s /\
  (!n. mem_safe_blocks n ctx fn t) ==>
  !n. mem_safe_run n ctx fn s
Proof
  strip_tac >> gen_tac >>
  simp[mem_safe_run_def, Once mem_safe_block_def, Once exec_block_def,
       step_inst_non_invoke, mem_safe_step_non_invoke]
QED

Theorem entry_operation_endpoint_safe[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  step_inst_base inst s = OK t /\
  inst_mem_below_frontier inst s /\ inst_dload_in_section inst s /\
  (!n. mem_safe_run n ctx fn (t with vs_inst_idx := SUC s.vs_inst_idx)) ==>
  !n. mem_safe_run n ctx fn s
Proof
  strip_tac >> gen_tac >>
  `step_inst n ctx inst s = OK t` by simp[step_inst_non_invoke] >>
  drule_all mem_safe_run_step >>
  simp[mem_safe_step_non_invoke]
QED


Theorem entry_jnz_endpoint_safe[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id JNZ [cond; Label yes; Label no] []) /\
  eval_operand cond s = SOME w /\ ~s.vs_halted ==>
  let t = jump_to (if w <> 0w then yes else no) s in
    vars_pc_only s t /\ ~t.vs_halted /\ t.vs_inst_idx = 0 /\
    t.vs_current_bb = (if w <> 0w then yes else no) /\
    ((!n. mem_safe_blocks n ctx fn t) ==> !n. mem_safe_run n ctx fn s)
Proof
  strip_tac >> simp_tac bool_ss [LET_THM] >> BETA_TAC >>
  conj_tac >- simp[vars_pc_only_jump_to, vars_pc_only_refl] >>
  simp[jump_to_def] >> strip_tac >> gen_tac >>
  irule entry_terminator_endpoint_safe >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  simp[mk_inst_def, is_terminator_def, inst_dload_in_section_def,
       step_jnz_behavior, jump_to_def] >>
  conj_tac
  >- (drule step_jnz_behavior >>
      disch_then (qspecl_then [`yes`, `no`, `id`] mp_tac) >>
      Cases_on `w = 0w` >> simp[jump_to_def]) >>
  irule below_frontier_no_ranges >> simp[]
QED

Theorem entry_selector_clause_endpoint[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id EQ [mid; Lit (n2w sel)] [name]) /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst (id + 1) JNZ [Var name; Label yes; Label no] []) /\
  lookup_block yes fn.fn_blocks = SOME
    <|bb_label := yes; bb_instructions := [mk_inst jid JMP [Label lbl] []]|> /\
  eval_operand mid s = SOME m /\ ~s.vs_halted ==>
  let q = update_var name (bool_to_word (m = n2w sel)) s
            with vs_inst_idx := SUC s.vs_inst_idx in
  let t = if m = n2w sel then jump_to lbl (jump_to yes q)
          else jump_to no q in
    vars_pc_only s t /\ ~t.vs_halted /\ t.vs_inst_idx = 0 /\
    t.vs_current_bb = (if m = n2w sel then lbl else no) /\
    ((!n. mem_safe_blocks n ctx fn t) ==> !n. mem_safe_run n ctx fn s)
Proof
  strip_tac >> simp_tac bool_ss [LET_THM] >> BETA_TAC >>
  qabbrev_tac `q = update_var name (bool_to_word (m = n2w sel)) s
                     with vs_inst_idx := SUC s.vs_inst_idx` >>
  conj_tac
  >- (Cases_on `m = n2w sel` >>
      simp[Abbr `q`, vars_pc_only_jump_to, vars_pc_only_inst_idx,
           vars_pc_only_update_var, vars_pc_only_refl]) >>
  `~q.vs_halted /\ q.vs_current_bb = s.vs_current_bb /\
   q.vs_inst_idx = SUC s.vs_inst_idx /\
   eval_operand (Var name) q = SOME (bool_to_word (m = n2w sel))` by
    simp[Abbr `q`, update_var_def, eval_operand_def, lookup_var_def,
         finite_mapTheory.FLOOKUP_UPDATE] >>
  ntac 3 (conj_tac >-
    (Cases_on `m = n2w sel` >> simp[jump_to_def, Abbr `q`, update_var_def])) >>
  strip_tac >> gen_tac >>
  irule entry_operation_endpoint_safe >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  qexists_tac `update_var name (bool_to_word (m = n2w sel)) s` >>
  suspend "operation"
QED

Resume entry_selector_clause_endpoint[operation]:
  conj_tac >- suspend "branch" >>
  simp[mk_inst_def, is_terminator_def, inst_dload_in_section_def] >>
  conj_tac
  >- (irule (SRULE [mk_inst_def] step_EQ) >> simp[eval_operand_def]) >>
  irule below_frontier_no_ranges >> simp[]
QED

Resume entry_selector_clause_endpoint[branch]:
  qpat_x_assum `Abbrev _` (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_assum `q = _` (fn th => rewrite_tac[GSYM th]) >>
  `lookup_block q.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb q.vs_inst_idx =
     SOME (mk_inst (id + 1) JNZ [Var name; Label yes; Label no] [])` by simp[] >>
  drule_all entry_jnz_endpoint_safe >>
  simp_tac bool_ss [LET_THM] >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  first_x_assum irule >>
  Cases_on `m = n2w sel` >> gvs[bool_to_word_def] >>
  suspend "match_jump"
QED

Resume entry_selector_clause_endpoint[match_jump]:
  irule mem_safe_blocks_no_phi >>
  reverse conj_tac
  >- (qexists_tac `<|bb_label := yes;
         bb_instructions := [mk_inst jid JMP [Label lbl] []]|>` >>
      simp[jump_to_def, eval_phis_def, phi_prefix_length_def, mk_inst_def]) >>
  simp[jump_to_def] >> gen_tac >>
  irule entry_terminator_endpoint_safe >>
  qexistsl_tac [`<|bb_label := yes;
      bb_instructions := [mk_inst jid JMP [Label lbl] []]|>`,
      `mk_inst jid JMP [Label lbl] []`] >>
  simp[mk_inst_def, get_instruction_def, is_terminator_def,
       step_jmp_behavior, inst_dload_in_section_def, jump_to_def] >>
  reverse conj_tac
  >- (irule below_frontier_no_ranges >> simp[]) >>
  gvs[jump_to_def]
QED

Finalise entry_selector_clause_endpoint

Theorem entry_compiled_selector_clause_endpoint[local]:
  emit_op EQ [mid; Lit (n2w sel)] st = (op, s1) /\
  fresh_label "match" s1 = (yes, s2) /\
  fresh_label "next" s2 = (no, s3) /\
  emit_inst JNZ [op; Label yes; Label no] [] s3 = ((), s4) /\
  new_block yes s4 = (old, s5) /\
  emit_inst JMP [Label lbl] [] s5 = ((), s6) /\
  new_block no s6 = (old', s7) /\ fn_has_code st s7 fn /\
  fresh_vars_wrt st ss /\ eval_operand mid ss = SOME m /\ ~ss.vs_halted /\
  ss.vs_current_bb = st.cs_current_bb /\
  ss.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. vars_pc_only ss t /\ fresh_vars_wrt s7 t /\
      (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x ss) /\
      eval_operand mid t = SOME m /\ ~t.vs_halted /\
      t.vs_current_bb = (if m = n2w sel then lbl else s7.cs_current_bb) /\
      t.vs_inst_idx = 0 /\
      ((!n. mem_safe_blocks n ctx fn t) ==> !n. mem_safe_run n ctx fn ss)
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
  imp_res_tac new_block_props >> gvs[same_blocks_def, arithmeticTheory.ADD1] >>
  suspend "joint"
QED

Resume entry_compiled_selector_clause_endpoint[joint]:
  qmatch_asmsub_abbrev_tac `lookup_block st.cs_current_bb _ = SOME bb` >>
  `lookup_block ss.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb ss.vs_inst_idx = SOME
     (mk_inst st.cs_next_id EQ [mid; Lit (n2w sel)]
       [STRING #"%" (toString st.cs_next_var)]) /\
   get_instruction bb (SUC ss.vs_inst_idx) = SOME
     (mk_inst (st.cs_next_id + 1) JNZ
       [Var (STRING #"%" (toString st.cs_next_var));
        Label s6.cs_current_bb; Label s7.cs_current_bb] [])` by
    simp[Abbr `bb`, get_instruction_def, listTheory.EL_APPEND_EQN,
         arithmeticTheory.ADD1] >>
  drule_all entry_selector_clause_endpoint >>
  simp_tac bool_ss [LET_THM] >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  suspend "resources"
QED

Resume entry_compiled_selector_clause_endpoint[resources]:
  qmatch_asmsub_abbrev_tac `vars_pc_only ss t` >>
  qexists_tac `t` >> simp[] >>
  suspend "fresh"
QED

Resume entry_compiled_selector_clause_endpoint[fresh]:
  Cases_on `m = n2w sel` >>
  simp[Abbr `t`, control_moves_keep_vars] >>
  (conj_tac
   >- (irule fresh_vars_wrt_advance >>
       qexistsl_tac [`st.cs_next_var`, `st`] >> simp[]) >>
   conj_tac
   >- (rw[lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
       gvs[not_fresh_at_def]) >>
   irule eval_operand_update_fresh >> simp[] >>
   qexists_tac `st` >> simp[])
QED

Finalise entry_compiled_selector_clause_endpoint

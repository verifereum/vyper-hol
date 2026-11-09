(* Joint endpoint boundaries for memory-free selected entry control. *)
Theory entrySelectedEndpointMem
Ancestors
  entryDispatchMem memSafeRun venomExecSemantics venomExecProofs loweringStateRelDefs
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
      ((!n. mem_safe_blocks n ctx fn t) ==> !n. mem_safe_run n ctx fn ss) /\
      (st.cs_current_insts = [] ==>
       (!n. mem_safe_blocks n ctx fn t) ==> !n. mem_safe_blocks n ctx fn ss)
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
  conj_tac >- suspend "fresh" >>
  conj_tac >- suspend "old_vars" >>
  conj_tac >- suspend "selector" >>
  suspend "blocks"
QED

Resume entry_compiled_selector_clause_endpoint[fresh]:
  Cases_on `m = n2w sel` >>
  simp[Abbr `t`, control_moves_keep_vars] >>
  irule fresh_vars_wrt_advance >>
  qexistsl_tac [`st.cs_next_var`, `st`] >> simp[]
QED

Resume entry_compiled_selector_clause_endpoint[old_vars]:
  Cases_on `m = n2w sel` >>
  simp[Abbr `t`, control_moves_keep_vars] >>
  rw[lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  gvs[not_fresh_at_def]
QED

Resume entry_compiled_selector_clause_endpoint[selector]:
  Cases_on `m = n2w sel` >>
  simp[Abbr `t`, control_moves_keep_vars] >>
  irule eval_operand_update_fresh >> simp[] >>
  qexists_tac `st` >> simp[]
QED

Resume entry_compiled_selector_clause_endpoint[blocks]:
  rpt strip_tac >>
  irule mem_safe_blocks_no_phi >>
  reverse conj_tac
  >- (qexists_tac `bb` >>
      simp[Abbr `bb`, eval_phis_def, phi_prefix_length_def, mk_inst_def]) >>
  simp[]
QED

Finalise entry_compiled_selector_clause_endpoint

Theorem entry_selector_checks_endpoint[local]:
  !sels mid st st' fn ss m ctx.
  compile_selector_checks mid sels st = ((), st') /\
  fn_has_code st st' fn /\ eval_operand mid ss = SOME m /\
  fresh_vars_wrt st ss /\ ~ss.vs_halted /\
  ss.vs_current_bb = st.cs_current_bb /\
  ss.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. vars_pc_only ss t /\ fresh_vars_wrt st' t /\
      (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x ss) /\
      eval_operand mid t = SOME m /\ ~t.vs_halted /\
      (case selector_hit m sels of
         SOME lbl => t.vs_current_bb = lbl /\ t.vs_inst_idx = 0
       | NONE => t.vs_current_bb = st'.cs_current_bb /\
                 t.vs_inst_idx = LENGTH st'.cs_current_insts) /\
      ((case selector_hit m sels of
          SOME lbl => (!n. mem_safe_blocks n ctx fn t)
        | NONE => ((!n. mem_safe_run n ctx fn t) /\
                   (st'.cs_current_insts = [] ==> !n. mem_safe_blocks n ctx fn t))) ==>
       (!n. mem_safe_run n ctx fn ss) /\
       (st.cs_current_insts = [] ==> !n. mem_safe_blocks n ctx fn ss))
Proof
  Induct
  >- (simp[compile_selector_checks_def, comp_return_def, selector_hit_def] >>
      rpt strip_tac >> qexists_tac `ss` >> simp[vars_pc_only_refl]) >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_selector_checks _ _ _ = _` mp_tac >>
  simp[Once compile_selector_checks_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> fs[]) >> strip_tac >>
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
  `cs_extends st s7` by metis_tac[cs_extends_trans] >>
  `fn_has_code st s7 fn /\ fn_has_code s7 st' fn` by
    metis_tac[fn_has_code_split] >>
  drule_all entry_compiled_selector_clause_endpoint >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  suspend "selected"
QED

Resume entry_selector_checks_endpoint[selected]:
  Cases_on `m = n2w h0`
  >- (qexists_tac `t` >> simp[selector_hit_def] >>
      irule fresh_vars_wrt_mono >> qexists_tac `s7` >> simp[] >>
      drule compile_selector_checks_next_var >> simp[]) >>
  `s7.cs_current_insts = []` by (drule new_block_props >> simp[]) >>
  qpat_x_assum `!mid st st' fn ss m ctx. _` drule >>
  disch_then (qspecl_then [`fn`, `t`, `m`, `ctx`] mp_tac) >>
  simp[] >> strip_tac >>
  suspend "miss"
QED

Resume entry_selector_checks_endpoint[miss]:
  `vars_pc_only ss t'` by metis_tac[vars_pc_only_trans] >>
  `!x. not_fresh_at st x ==> lookup_var x t' = lookup_var x ss` by
    (rpt strip_tac >>
     `not_fresh_at s7 x` by
       (irule not_fresh_at_mono >> qexists_tac `st` >>
        imp_res_tac emitted_insts_emit_op >> imp_res_tac emit_inst_extends >>
        imp_res_tac fresh_label_props >> imp_res_tac new_block_props >> simp[]) >>
     metis_tac[]) >>
  qexists_tac `t'` >> simp[selector_hit_def] >>
  strip_tac >>
  `!n. mem_safe_blocks n ctx fn t` by metis_tac[] >>
  simp[]
QED

Finalise entry_selector_checks_endpoint

Theorem entry_selector_tail_endpoint[local]:
  compile_selector_checks mid sels a8 = ((),a9) /\
  emit_inst JMP [Label fallback] [] a9 = ((),st') /\
  fn_has_code a8 st' fn /\ eval_operand mid ss = SOME m /\
  fresh_vars_wrt a8 ss /\ ~ss.vs_halted /\
  ss.vs_current_bb = a8.cs_current_bb /\
  ss.vs_inst_idx = LENGTH a8.cs_current_insts ==>
  ?t. vars_pc_only ss t /\ fresh_vars_wrt st' t /\
      (!x. not_fresh_at a8 x ==> lookup_var x t = lookup_var x ss) /\
      ~t.vs_halted /\
      t.vs_current_bb = (case selector_hit m sels of SOME l => l | NONE => fallback) /\
      t.vs_inst_idx = 0 /\
      ((!n. mem_safe_blocks n ctx fn t) ==>
       (!n. mem_safe_run n ctx fn ss) /\
       (a8.cs_current_insts = [] ==> !n. mem_safe_blocks n ctx fn ss))
Proof
  strip_tac >> imp_res_tac emit_inst_extends >>
  imp_res_tac (SRULE [cs_appends_def] cs_appends_emit_helpers) >>
  imp_res_tac (SRULE [cs_appends_def] compile_selector_checks_appends) >>
  `fn_has_code a8 a9 fn /\ fn_has_code a9 st' fn` by
    metis_tac[fn_has_code_split] >>
  drule_all entry_selector_checks_endpoint >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `fresh_vars_wrt st' t` by
    (irule fresh_vars_wrt_mono >> qexists_tac `a9` >> simp[]) >>
  Cases_on `selector_hit m sels`
  >- suspend "fallback" >>
  qexists_tac `t` >> gvs[]
QED

Resume entry_selector_tail_endpoint[fallback]:
  qexists_tac `jump_to fallback t` >>
  simp[control_moves_keep_vars, vars_pc_only_jump_to, jump_to_def] >>
  strip_tac >> fs[] >>
  qpat_x_assum `(_ /\ _) ==> _` irule >>
  suspend "fallback_safety"
QED

Resume entry_selector_tail_endpoint[fallback_safety]:
  qpat_x_assum `fn_has_code a9 st' fn` mp_tac >>
  simp[fn_has_code_def, IS_PREFIX_APPEND] >> strip_tac >>
  `get_instruction bb t.vs_inst_idx =
    SOME (mk_inst a9.cs_next_id JMP [Label fallback] [])` by
    simp[get_instruction_def, listTheory.EL_APPEND_EQN, listTheory.APPEND_ASSOC] >>
  `!n. mem_safe_run n ctx fn t` by
    (gen_tac >> irule entry_terminator_endpoint_safe >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     simp[mk_inst_def, is_terminator_def, step_jmp_behavior,
          inst_dload_in_section_def, jump_to_def] >>
     irule below_frontier_no_ranges >> simp[]) >>
  simp[] >> strip_tac >>
  irule mem_safe_blocks_no_phi >> reverse conj_tac
  >- (qexists_tac `bb` >>
      simp[eval_phis_def, phi_prefix_length_def, mk_inst_def]) >>
  `t with vs_inst_idx := 0 = t` by
    simp[venom_state_component_equality] >> simp[]
QED

Finalise entry_selector_tail_endpoint

Theorem entry_emitted_operation_endpoint[local]:
  emit_op opc ops st = (op,st') /\ fn_has_code st st' fn /\
  fresh_vars_wrt st ss /\ ss.vs_current_bb = st.cs_current_bb /\
  ss.vs_inst_idx = LENGTH st.cs_current_insts /\
  ~is_terminator opc /\ opc <> INVOKE /\
  step_inst_base (mk_inst st.cs_next_id opc ops
    [STRING #"%" (toString st.cs_next_var)]) ss =
    OK (update_var (STRING #"%" (toString st.cs_next_var)) w ss) /\
  inst_mem_below_frontier (mk_inst st.cs_next_id opc ops
    [STRING #"%" (toString st.cs_next_var)]) ss /\
  inst_dload_in_section (mk_inst st.cs_next_id opc ops
    [STRING #"%" (toString st.cs_next_var)]) ss ==>
  ?t. vars_pc_only ss t /\ fresh_vars_wrt st' t /\
      (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x ss) /\
      eval_operand op t = SOME w /\ t.vs_halted = ss.vs_halted /\
      t.vs_current_bb = st'.cs_current_bb /\
      t.vs_inst_idx = LENGTH st'.cs_current_insts /\
      ((!n. mem_safe_run n ctx fn t) ==> !n. mem_safe_run n ctx fn ss)
Proof
  strip_tac >> imp_res_tac emitted_insts_emit_op >>
  imp_res_tac emit_op_extends >>
  imp_res_tac (SRULE [cs_appends_def] cs_appends_emit_helpers) >>
  fs[same_blocks_def] >>
  qexists_tac `update_var (STRING #"%" (toString st.cs_next_var)) w ss
    with vs_inst_idx := SUC ss.vs_inst_idx` >>
  conj_tac >- simp[vars_pc_only_inst_idx, vars_pc_only_update_var, vars_pc_only_refl] >>
  conj_tac >- (simp[control_moves_keep_vars] >> irule fresh_vars_wrt_advance >>
    qexistsl_tac [`st.cs_next_var`, `st`] >> simp[]) >>
  conj_tac >- (rw[lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
    gvs[not_fresh_at_def]) >>
  simp[eval_operand_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE,
       control_moves_keep_vars, update_var_def, same_blocks_def] >>
  strip_tac >>
  `?bb. lookup_block st.cs_current_bb fn.fn_blocks = SOME bb /\
     get_instruction bb (LENGTH st.cs_current_insts) = SOME
       (mk_inst st.cs_next_id opc ops [STRING #"%" (toString st.cs_next_var)])` by
    (drule_all fn_has_code_same_block >> simp[] >> strip_tac >>
     qexists_tac `bb` >> first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  gen_tac >> irule entry_operation_endpoint_safe >>
  qexistsl_tac [`bb`,
    `mk_inst st.cs_next_id opc ops [STRING #"%" (toString st.cs_next_var)]`,
    `update_var (STRING #"%" (toString st.cs_next_var)) w ss`] >>
  simp[mk_inst_def, update_var_def]
QED

Theorem entry_method_endpoint[local]:
  emit_op CALLDATALOAD [Lit 0w] a6 = (raw,a7) /\
  emit_op SHR [Lit 224w; raw] a7 = (mid,a8) /\
  fn_has_code a6 a8 fn /\ fresh_vars_wrt a6 ss /\
  4 <= LENGTH ss.vs_call_ctx.cc_calldata /\
  ss.vs_current_bb = a6.cs_current_bb /\
  ss.vs_inst_idx = LENGTH a6.cs_current_insts ==>
  ?t. vars_pc_only ss t /\ fresh_vars_wrt a8 t /\
      (!x. not_fresh_at a6 x ==> lookup_var x t = lookup_var x ss) /\
      eval_operand mid t = SOME (calldata_method_id ss.vs_call_ctx.cc_calldata) /\
      t.vs_halted = ss.vs_halted /\ t.vs_current_bb = a8.cs_current_bb /\
      t.vs_inst_idx = LENGTH a8.cs_current_insts /\
      ((!n. mem_safe_run n ctx fn t) ==> !n. mem_safe_run n ctx fn ss)
Proof
  strip_tac >> imp_res_tac (SRULE [cs_appends_def] cs_appends_emit_helpers) >>
  `fn_has_code a6 a7 fn /\ fn_has_code a7 a8 fn` by
    metis_tac[fn_has_code_split] >>
  qabbrev_tac `w = word_of_bytes T (0w:bytes32)
    (TAKE 32 (ss.vs_call_ctx.cc_calldata ++ REPLICATE 32 0w))` >>
  `step_inst_base (mk_inst a6.cs_next_id CALLDATALOAD [Lit 0w]
     [STRING #"%" (toString a6.cs_next_var)]) ss =
     OK (update_var (STRING #"%" (toString a6.cs_next_var)) w ss)` by
    (simp[Abbr `w`] >> qspec_then `Lit 0w` mp_tac step_CALLDATALOAD >>
     simp[eval_operand_lit]) >>
  `inst_mem_below_frontier (mk_inst a6.cs_next_id CALLDATALOAD [Lit 0w]
     [STRING #"%" (toString a6.cs_next_var)]) ss` by
    (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  `~is_terminator CALLDATALOAD /\ CALLDATALOAD <> INVOKE /\
   inst_dload_in_section (mk_inst a6.cs_next_id CALLDATALOAD [Lit 0w]
     [STRING #"%" (toString a6.cs_next_var)]) ss` by
    simp[is_terminator_def, inst_dload_in_section_def, mk_inst_def] >>
  drule_all entry_emitted_operation_endpoint >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  suspend "shift"
QED

Resume entry_method_endpoint[shift]:
  `step_inst_base (mk_inst a7.cs_next_id SHR [Lit 224w; raw]
    [STRING #"%" (toString a7.cs_next_var)]) t =
    OK (update_var (STRING #"%" (toString a7.cs_next_var)) (w >>> 224) t)` by
    (irule (SRULE [wordsTheory.dimword_def]
       (Q.SPECL [`Lit 224w`, `raw`, `(224w:bytes32)`] step_SHR)) >>
     simp[eval_operand_lit]) >>
  `inst_mem_below_frontier (mk_inst a7.cs_next_id SHR [Lit 224w; raw]
    [STRING #"%" (toString a7.cs_next_var)]) t` by
    (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  `~is_terminator SHR /\ SHR <> INVOKE /\
   inst_dload_in_section (mk_inst a7.cs_next_id SHR [Lit 224w; raw]
     [STRING #"%" (toString a7.cs_next_var)]) t` by
    simp[is_terminator_def, inst_dload_in_section_def, mk_inst_def] >>
  drule_all entry_emitted_operation_endpoint >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t'` >> simp[Abbr `w`, calldataload_0_shr_224] >>
  conj_tac >- metis_tac[vars_pc_only_trans] >>
  rpt strip_tac >>
  `not_fresh_at a7 x` by
    (irule not_fresh_at_mono >> qexists_tac `a6` >>
     imp_res_tac emitted_insts_emit_op >> simp[]) >> metis_tac[]
QED

Finalise entry_method_endpoint

Theorem entry_method_tail_endpoint[local]:
  emit_op CALLDATALOAD [Lit 0w] a6 = (raw,a7) /\
  emit_op SHR [Lit 224w; raw] a7 = (mid,a8) /\
  compile_selector_checks mid sels a8 = ((),a9) /\
  emit_inst JMP [Label fallback] [] a9 = ((),st') /\
  fn_has_code a6 st' fn /\ fresh_vars_wrt a6 ss /\ ~ss.vs_halted /\
  4 <= LENGTH ss.vs_call_ctx.cc_calldata /\
  ss.vs_current_bb = a6.cs_current_bb /\
  ss.vs_inst_idx = LENGTH a6.cs_current_insts ==>
  ?t. vars_pc_only ss t /\ fresh_vars_wrt st' t /\
      (!x. not_fresh_at a6 x ==> lookup_var x t = lookup_var x ss) /\
      ~t.vs_halted /\
      t.vs_current_bb = (case selector_hit
        (calldata_method_id ss.vs_call_ctx.cc_calldata) sels of
         SOME l => l | NONE => fallback) /\ t.vs_inst_idx = 0 /\
      ((!n. mem_safe_blocks n ctx fn t) ==>
       (!n. mem_safe_run n ctx fn ss) /\
       (a6.cs_current_insts = [] ==> !n. mem_safe_blocks n ctx fn ss))
Proof
  strip_tac >>
  imp_res_tac (SRULE [cs_appends_def] cs_appends_emit_helpers) >>
  imp_res_tac (SRULE [cs_appends_def] compile_selector_checks_appends) >>
  `cs_extends a6 a8 /\ cs_extends a8 st'` by metis_tac[cs_extends_trans] >>
  `fn_has_code a6 a8 fn /\ fn_has_code a8 st' fn` by
    metis_tac[fn_has_code_split] >>
  drule_all entry_method_endpoint >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `~t.vs_halted` by simp[] >>
  drule_all entry_selector_tail_endpoint >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t'` >> simp[] >>
  conj_tac >- metis_tac[vars_pc_only_trans] >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at a8 x` by
        (irule not_fresh_at_mono >> qexists_tac `a6` >>
         imp_res_tac emitted_insts_emit_op >> simp[]) >> metis_tac[]) >>
  suspend "blocks"
QED

Resume entry_method_tail_endpoint[blocks]:
  rpt strip_tac >> irule mem_safe_blocks_no_phi >>
  reverse conj_tac
  >- (imp_res_tac emitted_insts_emit_op >> imp_res_tac emit_op_extends >>
      `a8.cs_current_bb = a6.cs_current_bb /\
       a8.cs_current_insts = a6.cs_current_insts ++ emitted_insts a6 a8` by
        (fs[same_blocks_def, emitted_insts_def] >>
         simp[rich_listTheory.DROP_LENGTH_APPEND, APPEND_ASSOC]) >>
      drule_all fn_has_code_same_block >> strip_tac >>
      qexists_tac `bb` >> simp[] >>
      first_x_assum (qspec_then `0` mp_tac) >> simp[] >> strip_tac >>
      suspend "no_phi") >>
  simp[]
QED

Resume entry_method_tail_endpoint[no_phi]:
  `emitted_insts a6 a8 =
    [mk_inst a6.cs_next_id CALLDATALOAD [Lit 0w]
       [STRING #"%" (toString a6.cs_next_var)];
     mk_inst a7.cs_next_id SHR [Lit 224w; raw]
       [STRING #"%" (toString a7.cs_next_var)]]` by
    gvs[] >>
  fs[] >> Cases_on `bb.bb_instructions` >>
  gvs[get_instruction_def, eval_phis_def, phi_prefix_length_def, mk_inst_def]
QED

Finalise entry_method_tail_endpoint

Theorem entry_size_endpoint[local]:
  emit_op CALLDATASIZE [] st = (cds,a1) /\
  emit_op LT [cds; Lit 4w] a1 = (small,a2) /\
  emit_op ISZERO [small] a2 = (cond,a3) /\
  fn_has_code st a3 fn /\ fresh_vars_wrt st ss /\
  LENGTH ss.vs_call_ctx.cc_calldata < dimword(:256) /\
  ss.vs_current_bb = st.cs_current_bb /\
  ss.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. vars_pc_only ss t /\ fresh_vars_wrt a3 t /\
      (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x ss) /\
      eval_operand cond t = SOME (bool_to_word (4 <= LENGTH ss.vs_call_ctx.cc_calldata)) /\
      t.vs_halted = ss.vs_halted /\ t.vs_current_bb = a3.cs_current_bb /\
      t.vs_inst_idx = LENGTH a3.cs_current_insts /\
      ((!n. mem_safe_run n ctx fn t) ==> !n. mem_safe_run n ctx fn ss)
Proof
  strip_tac >> imp_res_tac (SRULE [cs_appends_def] cs_appends_emit_helpers) >>
  `cs_extends st a2` by metis_tac[cs_extends_trans] >>
  `fn_has_code st a1 fn /\ fn_has_code a1 a2 fn /\ fn_has_code a2 a3 fn` by
    metis_tac[fn_has_code_split] >>
  `step_inst_base (mk_inst st.cs_next_id CALLDATASIZE []
     [STRING #"%" (toString st.cs_next_var)]) ss =
     OK (update_var (STRING #"%" (toString st.cs_next_var))
          (n2w (LENGTH ss.vs_call_ctx.cc_calldata)) ss)` by
    simp[step_CALLDATASIZE] >>
  `inst_mem_below_frontier (mk_inst st.cs_next_id CALLDATASIZE []
     [STRING #"%" (toString st.cs_next_var)]) ss` by
    (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  `~is_terminator CALLDATASIZE /\ CALLDATASIZE <> INVOKE /\
   inst_dload_in_section (mk_inst st.cs_next_id CALLDATASIZE []
     [STRING #"%" (toString st.cs_next_var)]) ss` by
    simp[is_terminator_def, inst_dload_in_section_def, mk_inst_def] >>
  drule_all entry_emitted_operation_endpoint >>
  disch_then (qspec_then `ctx` strip_assume_tac) >> suspend "lt"
QED

Resume entry_size_endpoint[lt]:
  `step_inst_base (mk_inst a1.cs_next_id LT [cds; Lit 4w]
     [STRING #"%" (toString a1.cs_next_var)]) t =
     OK (update_var (STRING #"%" (toString a1.cs_next_var))
          (bool_to_word (LENGTH ss.vs_call_ctx.cc_calldata < 4)) t)` by
    (drule step_LT >> disch_then (qspec_then `Lit 4w` mp_tac) >>
     simp[eval_operand_lit, wordsTheory.dimword_def]) >>
  `inst_mem_below_frontier (mk_inst a1.cs_next_id LT [cds; Lit 4w]
     [STRING #"%" (toString a1.cs_next_var)]) t` by
    (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  `~is_terminator LT /\ LT <> INVOKE /\
   inst_dload_in_section (mk_inst a1.cs_next_id LT [cds; Lit 4w]
     [STRING #"%" (toString a1.cs_next_var)]) t` by
    simp[is_terminator_def, inst_dload_in_section_def, mk_inst_def] >>
  drule_all entry_emitted_operation_endpoint >>
  disch_then (qspec_then `ctx` strip_assume_tac) >> suspend "iszero"
QED

Resume entry_size_endpoint[iszero]:
  `step_inst_base (mk_inst a2.cs_next_id ISZERO [small]
     [STRING #"%" (toString a2.cs_next_var)]) t' =
     OK (update_var (STRING #"%" (toString a2.cs_next_var))
          (bool_to_word (4 <= LENGTH ss.vs_call_ctx.cc_calldata)) t')` by
    (drule step_ISZERO >> simp[bool_to_word_def] >>
     Cases_on `LENGTH ss.vs_call_ctx.cc_calldata < 4` >> simp[bool_to_word_def]) >>
  `inst_mem_below_frontier (mk_inst a2.cs_next_id ISZERO [small]
     [STRING #"%" (toString a2.cs_next_var)]) t'` by
    (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  `~is_terminator ISZERO /\ ISZERO <> INVOKE /\
   inst_dload_in_section (mk_inst a2.cs_next_id ISZERO [small]
     [STRING #"%" (toString a2.cs_next_var)]) t'` by
    simp[is_terminator_def, inst_dload_in_section_def, mk_inst_def] >>
  drule_all entry_emitted_operation_endpoint >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t''` >> simp[] >>
  conj_tac >- metis_tac[vars_pc_only_trans] >>
  rpt strip_tac >>
  `not_fresh_at a1 x /\ not_fresh_at a2 x` by
    (imp_res_tac emitted_insts_emit_op >>
     conj_tac >> irule not_fresh_at_mono >> qexists_tac `st` >> simp[]) >>
  metis_tac[]
QED

Finalise entry_size_endpoint

Theorem entry_compiled_jnz_endpoint[local]:
  fresh_label "dispatch" a3 = (dispatch,a4) /\
  emit_inst JNZ [cond; Label dispatch; Label fallback] [] a4 = ((),a5) /\
  new_block dispatch a5 = (old,a6) /\ fn_has_code a3 a6 fn /\
  fresh_vars_wrt a3 ss /\ eval_operand cond ss = SOME w /\ ~ss.vs_halted /\
  ss.vs_current_bb = a3.cs_current_bb /\
  ss.vs_inst_idx = LENGTH a3.cs_current_insts ==>
  ?t. vars_pc_only ss t /\ fresh_vars_wrt a6 t /\
      (!x. lookup_var x t = lookup_var x ss) /\ ~t.vs_halted /\
      t.vs_current_bb = (if w <> 0w then a6.cs_current_bb else fallback) /\
      t.vs_inst_idx = 0 /\
      ((!n. mem_safe_blocks n ctx fn t) ==> !n. mem_safe_run n ctx fn ss)
Proof
  strip_tac >>
  imp_res_tac (SRULE [cs_appends_def] cs_appends_emit_helpers) >>
  imp_res_tac (SRULE [cs_appends_def] cs_appends_prims) >>
  `fn_has_code a5 a6 fn` by
    (irule fn_has_code_mid >> goal_assum (drule_at Any) >>
     metis_tac[cs_extends_trans, cs_extends_refl]) >>
  drule_all fn_has_code_new_block >> strip_tac >>
  imp_res_tac fresh_label_props >> imp_res_tac emit_inst_extends >>
  imp_res_tac new_block_props >> gvs[same_blocks_def] >>
  qmatch_asmsub_abbrev_tac `lookup_block a3.cs_current_bb _ = SOME bb` >>
  `lookup_block ss.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb ss.vs_inst_idx = SOME
    (mk_inst a3.cs_next_id JNZ [cond; Label a6.cs_current_bb; Label fallback] [])` by
    simp[Abbr `bb`, get_instruction_def, listTheory.EL_APPEND_EQN] >>
  drule_all entry_jnz_endpoint_safe >> simp_tac bool_ss [LET_THM] >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `jump_to (if w <> 0w then a6.cs_current_bb else fallback) ss` >>
  simp[control_moves_keep_vars] >>
  irule fresh_vars_wrt_mono >> qexists_tac `a3` >> simp[]
QED

Theorem compile_selector_dispatch_linear_endpoint:
  compile_selector_dispatch_linear sels fallback st = ((),st') /\
  fn_has_code st st' fn /\ fresh_vars_wrt st ss /\ ~ss.vs_halted /\
  EVERY (\(sel,lbl). sel < 2 ** 32) sels /\
  LENGTH ss.vs_call_ctx.cc_calldata < dimword(:256) /\
  ss.vs_current_bb = st.cs_current_bb /\
  ss.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. vars_pc_only ss t /\ fresh_vars_wrt st' t /\
      (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x ss) /\
      ~t.vs_halted /\
      t.vs_current_bb = linear_dispatch_target ss.vs_call_ctx.cc_calldata sels fallback /\
      t.vs_inst_idx = 0 /\
      ((!n. mem_safe_blocks n ctx fn t) ==>
       (!n. mem_safe_run n ctx fn ss) /\
       (st.cs_current_insts = [] ==> !n. mem_safe_blocks n ctx fn ss))
Proof
  strip_tac >> qpat_x_assum `compile_selector_dispatch_linear _ _ _ = _` mp_tac >>
  simp[compile_selector_dispatch_linear_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> fs[]) >> strip_tac >>
  rename1 `emit_op CALLDATASIZE [] st = (cds,a1)` >>
  rename1 `emit_op LT _ a1 = (small,a2)` >>
  rename1 `emit_op ISZERO _ a2 = (cond,a3)` >>
  rename1 `fresh_label "dispatch" a3 = (dispatch,a4)` >>
  rename1 `emit_inst JNZ _ _ a4 = (_,a5)` >>
  rename1 `new_block dispatch a5 = (_,a6)` >>
  rename1 `emit_op CALLDATALOAD _ a6 = (raw,a7)` >>
  rename1 `emit_op SHR _ a7 = (mid,a8)` >>
  rename1 `compile_selector_checks _ _ a8 = (_,a9)` >>
  rename1 `emit_inst JNZ _ _ a4 = (u,a5)` >> Cases_on `u` >>
  rename1 `compile_selector_checks _ _ a8 = (u,a9)` >> Cases_on `u` >>
  imp_res_tac (SRULE [cs_appends_def] cs_appends_emit_helpers) >>
  imp_res_tac (SRULE [cs_appends_def] cs_appends_prims) >>
  imp_res_tac (SRULE [cs_appends_def] compile_selector_checks_appends) >>
  `cs_extends st a3 /\ cs_extends a3 a6 /\ cs_extends a6 st'` by
    metis_tac[cs_extends_trans] >>
  `cs_extends st a6` by metis_tac[cs_extends_trans] >>
  qspecl_then [`st`, `a6`, `st'`, `fn`] mp_tac fn_has_code_split >>
  simp[] >> strip_tac >>
  qspecl_then [`st`, `a3`, `a6`, `fn`] mp_tac fn_has_code_split >>
  simp[] >> strip_tac >>
  drule_all entry_size_endpoint >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `~t.vs_halted` by simp[] >>
  drule_all entry_compiled_jnz_endpoint >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `st.cs_current_insts = [] ==>
   ?bb. lookup_block ss.vs_current_bb fn.fn_blocks = SOME bb /\
        eval_phis ss bb.bb_instructions = OK ss /\
        phi_prefix_length bb.bb_instructions = 0` by suspend "no_phi" >>
  suspend "branch"
QED

Resume compile_selector_dispatch_linear_endpoint[branch]:
  imp_res_tac new_block_props >>
  Cases_on `4 <= LENGTH ss.vs_call_ctx.cc_calldata`
  >- suspend "long" >>
  qexists_tac `t'` >>
  fs[bool_to_word_def] >>
  `linear_dispatch_target ss.vs_call_ctx.cc_calldata sels fallback = fallback` by
    (irule linear_dispatch_target_short >> simp[]) >> simp[] >>
  conj_tac >- metis_tac[vars_pc_only_trans] >>
  conj_tac
  >- (irule fresh_vars_wrt_mono >> qexists_tac `a6` >> simp[] >>
      imp_res_tac emitted_insts_emit_op >>
      imp_res_tac fresh_label_props >> imp_res_tac new_block_props >>
      imp_res_tac emit_inst_extends >>
      imp_res_tac compile_selector_checks_next_var >> simp[]) >>
  suspend "short_input_safety"
QED

Resume compile_selector_dispatch_linear_endpoint[long]:
  `t'.vs_call_ctx = ss.vs_call_ctx` by
    metis_tac[vars_pc_only_fields] >>
  `t'.vs_current_bb = a6.cs_current_bb` by fs[bool_to_word_def] >>
  `t'.vs_inst_idx = LENGTH a6.cs_current_insts` by simp[] >>
  `4 <= LENGTH t'.vs_call_ctx.cc_calldata` by simp[] >>
  drule_all entry_method_tail_endpoint >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t''` >> fs[linear_dispatch_target_selector_hit] >>
  conj_tac >- metis_tac[vars_pc_only_trans] >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at a6 x` by
        (irule not_fresh_at_mono >> qexists_tac `st` >>
         imp_res_tac emitted_insts_emit_op >> imp_res_tac fresh_label_props >>
         imp_res_tac emit_inst_extends >> imp_res_tac new_block_props >> simp[]) >>
      metis_tac[]) >> suspend "long_input_safety"
QED

Resume compile_selector_dispatch_linear_endpoint[short_input_safety]:
  `(!n. mem_safe_blocks n ctx fn t') ==> !n. mem_safe_run n ctx fn ss` by metis_tac[] >>
  rpt strip_tac >>
  `!n. mem_safe_run n ctx fn ss` by metis_tac[] >>
  simp[] >>
  irule mem_safe_blocks_no_phi >> gvs[]
QED

Resume compile_selector_dispatch_linear_endpoint[long_input_safety]:
  `(!n. mem_safe_blocks n ctx fn t') ==> !n. mem_safe_run n ctx fn ss` by metis_tac[] >>
  rpt strip_tac >>
  `!n. mem_safe_run n ctx fn ss` by metis_tac[] >>
  simp[] >>
  irule mem_safe_blocks_no_phi >> gvs[]
QED

Resume compile_selector_dispatch_linear_endpoint[no_phi]:
  strip_tac >>
  `cs_extends a1 a3` by metis_tac[cs_extends_trans] >>
  qspecl_then [`st`, `a1`, `a3`, `fn`] mp_tac fn_has_code_split >>
  simp[] >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac emit_op_extends >>
  `a1.cs_current_bb = st.cs_current_bb` by fs[same_blocks_def] >>
  qspecl_then [`st`, `a1`, `fn`, `emitted_insts st a1`]
    mp_tac fn_has_code_same_block >>
  simp[] >> strip_tac >>
  qexists_tac `bb` >> simp[] >>
  Cases_on `bb.bb_instructions` >>
  gvs[get_instruction_def, eval_phis_def, phi_prefix_length_def, mk_inst_def]
QED

Finalise compile_selector_dispatch_linear_endpoint

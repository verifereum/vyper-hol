(* Interpret the supplied caller traversal, without choosing a new execution. *)
Theory createSizeSlotTraversal
Ancestors
  slotCopyExecution copyExecution fragGasOrigin fragExec fragBlockPath
  createSourceCallback venomInstProofs1 venomExecSemantics venomInst
  exprLoweringProps instIdxIndep venomState relation list arithmetic words
  exprPtrUnwrapRuntimeFrame

Theorem slot_actual_nonterm_edge[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
  step_inst_base inst s = OK mid /\
  gas_origin_edge F explicit ctx fn s marks (OK u) ==>
  u = (mid with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  simp[gas_origin_edge_def, step_inst_non_invoke, exit_result_def] >>
  rpt strip_tac >> gvs[step_inst_non_invoke, exit_result_def]
QED

Theorem slot_actual_jump_edge[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode <> INVOKE /\ is_terminator inst.inst_opcode /\
  step_inst_base inst s = OK mid /\
  lookup_block mid.vs_current_bb fn.fn_blocks = SOME target /\
  phi_prefix_length target.bb_instructions = 0 /\ mid.vs_inst_idx = 0 /\
  gas_origin_edge F explicit ctx fn s marks (OK u) ==> u = mid
Proof
  simp[gas_origin_edge_def, exit_result_def] >> rpt strip_tac >>
  gvs[step_inst_non_invoke, exit_result_def, eval_phis_no_phi,
      venom_state_component_equality]
QED

Theorem slot_actual_peel_straight[local]:
  !xs s mid rest bb.
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) xs /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    DROP s.vs_inst_idx bb.bb_instructions = xs ++ rest /\
    (s.vs_current_bb <> t.vs_current_bb \/ t.vs_inst_idx < s.vs_inst_idx) /\
    run_inst_seq xs s = OK mid /\
    (!u v. R u v ==> ?ms. gas_origin_edge F explicit ctx fn u ms (OK v)) /\
    RTC R s t ==>
    RTC R (mid with vs_inst_idx := s.vs_inst_idx + LENGTH xs) t /\
    mid.vs_current_bb = s.vs_current_bb
Proof
  Induct >- (simp[run_inst_seq_def] >> rpt strip_tac >> gvs[] >>
             `mid with vs_inst_idx := mid.vs_inst_idx = mid` by simp[] >> simp[]) >>
  rpt gen_tac >> simp[Once run_inst_seq_def, AllCaseEqs()] >> strip_tac >>
  rename1 `step_inst_base h s = OK next` >>
  `s <> t` by (strip_tac >> gvs[]) >>
  qpat_x_assum `RTC R s t` (strip_assume_tac o ONCE_REWRITE_RULE[RTC_CASES1]) >>
  drule DROP_EQ_CONS >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME h` by simp[get_instruction_def] >>
  rename1 `R s u` >>
  `u = (next with vs_inst_idx := SUC s.vs_inst_idx)` by
    metis_tac[slot_actual_nonterm_edge] >>
  `next.vs_current_bb = s.vs_current_bb` by
    metis_tac[step_inst_base_preserves_all] >>
  `u.vs_current_bb <> t.vs_current_bb \/ t.vs_inst_idx < u.vs_inst_idx` by
    (simp[] >> strip_tac >> res_tac >> decide_tac) >>
  `run_inst_seq xs u = OK (mid with vs_inst_idx := u.vs_inst_idx)` by
    (`EVERY (\i. ~is_terminator i.inst_opcode) xs` by fs[EVERY_MEM] >>
     simp[run_inst_seq_inst_idx, exec_result_map_def]) >>
  first_x_assum (qspecl_then [`u`, `mid with vs_inst_idx := u.vs_inst_idx`, `rest`, `bb`] mp_tac) >>
  gvs[ADD_CLAUSES]
QED

Theorem slot_actual_jump_cursor[local]:
  ((?id l. j = mk_inst id JMP [Label l] []) \/
   (?id c l r. j = mk_inst id JNZ [c; Label l; Label r] [])) ==>
  is_terminator j.inst_opcode /\ j.inst_opcode <> INVOKE /\
  !s k. step_inst_base j (s with vs_inst_idx := k) = step_inst_base j s
Proof
  strip_tac >> simp[mk_inst_def, is_terminator_def,
    step_inst_base_opcode_eqs, jump_to_def] >>
  rpt gen_tac >> Cases_on `c` >> simp[eval_operand_def, lookup_var_def]
QED

Theorem slot_actual_peel_block[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  DROP s.vs_inst_idx bb.bb_instructions = xs ++ [j] /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) xs /\
  is_terminator j.inst_opcode /\ j.inst_opcode <> INVOKE /\
  (!s k. step_inst_base j (s with vs_inst_idx := k) = step_inst_base j s) /\
  run_inst_seq (xs ++ [j]) s = OK mid /\
  lookup_block mid.vs_current_bb fn.fn_blocks = SOME target /\
  phi_prefix_length target.bb_instructions = 0 /\ mid.vs_inst_idx = 0 /\
  (s.vs_current_bb <> t.vs_current_bb \/ t.vs_inst_idx < s.vs_inst_idx) /\
  (!u v. R u v ==> ?ms. gas_origin_edge F explicit ctx fn u ms (OK v)) /\
  RTC R s t ==> RTC R mid t
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `?v. run_inst_seq xs s = OK v` by
    (spose_not_then assume_tac >> drule run_inst_seq_append_err >> metis_tac[]) >>
  `step_inst_base j v = OK mid` by
    (drule run_inst_seq_append >> disch_then (qspec_then `[j]` mp_tac) >>
     simp[run_inst_seq_def, AllCaseEqs()]) >>
  drule_all slot_actual_peel_straight >> strip_tac >>
  qabbrev_tac `u = v with vs_inst_idx := s.vs_inst_idx + LENGTH xs` >>
  `u.vs_current_bb = s.vs_current_bb` by simp[Abbr `u`] >>
  `u <> t` by (strip_tac >> gvs[Abbr `u`] >> decide_tac) >>
  qpat_x_assum `RTC R u t` (strip_assume_tac o ONCE_REWRITE_RULE[RTC_CASES1]) >>
  `get_instruction bb u.vs_inst_idx = SOME j` by
    (simp[Abbr `u`] >> metis_tac[get_instruction_suffix_last, ADD_COMM]) >>
  `is_terminator j.inst_opcode /\ j.inst_opcode <> INVOKE /\
   step_inst_base j u = OK mid` by
    simp[Abbr `u`] >>
  `?ms. gas_origin_edge F explicit ctx fn u ms (OK u')` by metis_tac[] >>
  `lookup_block u.vs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
  drule_all slot_actual_jump_edge >> strip_tac >> gvs[]
QED

(* All blocks in this loop are straight-line up to one literal-label jump. *)
Theorem slot_actual_jump_block[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  DROP s.vs_inst_idx bb.bb_instructions = code /\ code <> [] /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (FRONT code) /\
  ((?id l. LAST code = mk_inst id JMP [Label l] []) \/
   (?id c l r. LAST code = mk_inst id JNZ [c;Label l;Label r] [])) /\
  run_inst_seq code s = OK mid /\
  lookup_block mid.vs_current_bb fn.fn_blocks = SOME target /\
  phi_prefix_length target.bb_instructions = 0 /\ mid.vs_inst_idx = 0 /\
  (s.vs_current_bb <> t.vs_current_bb \/ t.vs_inst_idx < s.vs_inst_idx) /\
  (!u v. R u v ==> ?ms. gas_origin_edge F explicit ctx fn u ms (OK v)) /\
  RTC R s t ==> RTC R mid t
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `code = FRONT code ++ [LAST code]` by simp[APPEND_FRONT_LAST] >>
  `is_terminator (LAST code).inst_opcode /\ (LAST code).inst_opcode <> INVOKE /\
   !v k. step_inst_base (LAST code) (v with vs_inst_idx := k) =
         step_inst_base (LAST code) v` by metis_tac[slot_actual_jump_cursor] >>
  qpat_x_assum `code = _` (fn th =>
    qpat_x_assum `run_inst_seq code s = _` (assume_tac o ONCE_REWRITE_RULE[th]) >>
    qpat_x_assum `DROP _ _ = code` (assume_tac o ONCE_REWRITE_RULE[th])) >>
  drule_all slot_actual_peel_block >> simp[]
QED

Theorem slot_actual_phi_targets[local]:
  fn_has_code cs (slot_copy_final cs src dst n load) fn /\
  lookup_block (slot_copy_exit cs) fn.fn_blocks = SOME exit /\
  phi_prefix_length exit.bb_instructions = 0 ==>
  !lbl. MEM lbl [slot_copy_cond cs; slot_copy_body cs; slot_copy_exit cs] ==>
    ?bb. lookup_block lbl fn.fn_blocks = SOME bb /\
         phi_prefix_length bb.bb_instructions = 0
Proof
  strip_tac >> drule slot_copy_lookup >> strip_tac >>
  simp[DISJ_IMP_THM, FORALL_AND_THM, slot_copy_body_insts_def,
       slot_copy_cond_insts_def, phi_prefix_length_def, mk_inst_def] >> gvs[]
QED

Theorem slot_actual_init[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = cs.cs_current_insts ++ slot_copy_init_insts cs /\
  s.vs_inst_idx = LENGTH cs.cs_current_insts /\
  (s.vs_current_bb <> t.vs_current_bb \/ t.vs_inst_idx < s.vs_inst_idx) /\
  (!lbl. MEM lbl [slot_copy_cond cs; slot_copy_body cs; slot_copy_exit cs] ==>
         ?bb. lookup_block lbl fn.fn_blocks = SOME bb /\
              phi_prefix_length bb.bb_instructions = 0) /\
  (!u v. R u v ==> ?ms. gas_origin_edge F explicit ctx fn u ms (OK v)) /\
  RTC R s t ==> RTC R (slot_copy_initial cs s) t
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `DROP s.vs_inst_idx bb.bb_instructions = slot_copy_init_insts cs` by simp[rich_listTheory.DROP_LENGTH_APPEND] >>
  `run_inst_seq (slot_copy_init_insts cs) s = OK (slot_copy_initial cs s)` by
    simp[slot_copy_initial_def, slot_copy_init_insts_def, run_inst_seq_def,
         step_inst_base_opcode_eqs, mk_inst_def, eval_operand_def] >>
  `?target. lookup_block (slot_copy_initial cs s).vs_current_bb fn.fn_blocks = SOME target /\
        phi_prefix_length target.bb_instructions = 0` by
    simp[slot_copy_initial_def, jump_to_def] >>
  ` (slot_copy_initial cs s).vs_inst_idx = 0` by simp[slot_copy_initial_def, jump_to_def] >>
  drule_at (Pat `run_inst_seq _ _ = _`) slot_actual_jump_block >>
  disch_then irule >>
  simp[slot_copy_init_insts_def, mk_inst_def, is_terminator_def] >>
  qexistsl_tac [`bb`, `ctx`, `explicit`, `fn`, `target`] >>
  fs[slot_copy_init_insts_def, mk_inst_def, rich_listTheory.DROP_LENGTH_APPEND]
QED

Theorem slot_actual_cond[local]:
  fn_has_code cs (slot_copy_final cs src dst n load) fn /\
  lookup_block (slot_copy_exit cs) fn.fn_blocks = SOME exit /\
  phi_prefix_length exit.bb_instructions = 0 /\
  slot_copy_inv cs load original p d n [] i s /\
  s.vs_current_bb = slot_copy_cond cs /\ s.vs_inst_idx = 0 /\
  t.vs_current_bb = slot_copy_exit cs /\
  (!u v. R u v ==> ?ms. gas_origin_edge F explicit ctx fn u ms (OK v)) /\
  RTC R s t ==> RTC R (slot_copy_cond_result cs n i s) t
Proof
  strip_tac >> drule slot_copy_lookup >> strip_tac >>
  drule slot_actual_phi_targets >> gvs[] >> strip_tac >>
  `run_inst_seq (slot_copy_cond_insts cs n) s = OK (slot_copy_cond_result cs n i s)` by
    (irule slot_copy_condition_execution >> fs[slot_copy_inv_def] >> decide_tac) >>
  `?target. lookup_block (slot_copy_cond_result cs n i s).vs_current_bb fn.fn_blocks = SOME target /\
            phi_prefix_length target.bb_instructions = 0` by
    (simp[slot_copy_cond_frame] >> IF_CASES_TAC >> simp[]) >>
  drule_at (Pat `run_inst_seq _ _ = _`) slot_actual_jump_block >> disch_then irule >>
  simp[slot_copy_cond_insts_def, mk_inst_def, is_terminator_def,
       slot_copy_cond_frame, slot_copy_labels_distinct] >>
  qexistsl_tac [`<|bb_label := slot_copy_cond cs; bb_instructions := slot_copy_cond_insts cs n|>`,
                `ctx`, `explicit`, `fn`, `target`] >>
  fs[slot_copy_cond_insts_def, mk_inst_def, slot_copy_cond_frame]
QED

Theorem slot_actual_body[local]:
  fn_has_code cs (slot_copy_final cs src dst n load) fn /\
  lookup_block (slot_copy_exit cs) fn.fn_blocks = SOME exit /\
  phi_prefix_length exit.bb_instructions = 0 /\
  slot_copy_inv cs load original p d n [] i s /\
  slot_copy_external cs src /\ slot_copy_external cs dst /\
  eval_operand src original = SOME p /\ eval_operand dst original = SOME d /\
  (load = SLOAD \/ load = TLOAD) /\
  s.vs_current_bb = slot_copy_body cs /\ s.vs_inst_idx = 0 /\
  t.vs_current_bb = slot_copy_exit cs /\
  (!u v. R u v ==> ?ms. gas_origin_edge F explicit ctx fn u ms (OK v)) /\
  RTC R s t ==> RTC R (slot_copy_body_result cs p d load i s) t
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule slot_actual_phi_targets >> simp[] >> strip_tac >>
  drule slot_copy_lookup >> strip_tac >>
  `run_inst_seq (slot_copy_body_insts cs src dst load) s =
       OK (slot_copy_body_result cs p d load i s)` by
    (irule slot_copy_body_execution >> gvs[slot_copy_inv_def]) >>
  `?target. lookup_block (slot_copy_body_result cs p d load i s).vs_current_bb fn.fn_blocks = SOME target /\
            phi_prefix_length target.bb_instructions = 0` by simp[slot_copy_body_counter] >>
  drule_at (Pat `run_inst_seq _ _ = _`) slot_actual_jump_block >> disch_then irule >>
  `~is_terminator load /\ load <> INVOKE` by
    (qpat_x_assum `load = SLOAD \/ load = TLOAD` strip_assume_tac >>
     gvs[is_terminator_def]) >>
  simp[slot_copy_body_insts_def, mk_inst_def, is_terminator_def,
       slot_copy_body_counter, slot_copy_labels_distinct] >>
  qexistsl_tac [`<|bb_label := slot_copy_body cs; bb_instructions := slot_copy_body_insts cs src dst load|>`,
               `ctx`, `explicit`, `fn`, `target`] >>
  fs[slot_copy_body_insts_def, mk_inst_def, slot_copy_body_counter]
QED

Theorem slot_actual_counted[local]:
  !k i s.
    n = i + k /\
    fn_has_code cs (slot_copy_final cs src dst n load) fn /\
    lookup_block (slot_copy_exit cs) fn.fn_blocks = SOME exit /\
    phi_prefix_length exit.bb_instructions = 0 /\
    slot_copy_external cs src /\ slot_copy_external cs dst /\
    eval_operand src original = SOME p /\ eval_operand dst original = SOME d /\
    (load = SLOAD \/ load = TLOAD) /\
    slot_copy_inv cs load original p d n [] i s /\
    slot_copy_runtime_frame cs d i original s /\ w2n d + 32*n < 2**256 /\
    s.vs_current_bb = slot_copy_cond cs /\ s.vs_inst_idx = 0 /\
    t.vs_current_bb = slot_copy_exit cs /\ t.vs_inst_idx = 0 /\
    (!u v. R u v ==> (u.vs_current_bb <> slot_copy_exit cs \/ u.vs_inst_idx <> 0) /\
                     ?ms. gas_origin_edge F explicit ctx fn u ms (OK v)) /\
    RTC R s t ==>
    slot_copy_inv cs load original p d n [] n t /\
    slot_copy_runtime_frame cs d n original t
Proof
  Induct >> rpt gen_tac >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac)
  >- (`i = n` by decide_tac >> qpat_x_assum `i = n` SUBST_ALL_TAC >>
      qabbrev_tac `b = slot_copy_cond_result cs n n s` >>
      `!u v. R u v ==> ?ms. gas_origin_edge F explicit ctx fn u ms (OK v)` by metis_tac[] >>
      `RTC R b t` by (simp_tac bool_ss [Abbr `b`] >> drule_all slot_actual_cond >> simp[]) >>
      `b.vs_current_bb = slot_copy_exit cs /\ b.vs_inst_idx = 0` by
        simp[Abbr `b`, slot_copy_cond_frame] >>
      `b = t` by
        (qpat_x_assum `RTC R b t` (strip_assume_tac o ONCE_REWRITE_RULE[RTC_CASES1]) >>
         metis_tac[]) >>
      qpat_x_assum `b = t` (SUBST_ALL_TAC o SYM) >>
      simp[Abbr `b`, slot_copy_condition_invariant, slot_copy_runtime_frame_condition]) >>
  `i < n` by decide_tac >>
  qabbrev_tac `b = slot_copy_cond_result cs n i s` >>
  qabbrev_tac `u = slot_copy_body_result cs p d load i b` >>
  `!u v. R u v ==> ?ms. gas_origin_edge F explicit ctx fn u ms (OK v)` by metis_tac[] >>
  `RTC R b t` by (simp_tac bool_ss [Abbr `b`] >> drule_all slot_actual_cond >> simp[]) >>
  `b.vs_current_bb = slot_copy_body cs /\ b.vs_inst_idx = 0` by
    simp[Abbr `b`, slot_copy_cond_frame] >>
  `slot_copy_inv cs load original p d n [] i b` by
    simp[Abbr `b`, slot_copy_condition_invariant] >>
  `RTC R u t` by (simp_tac bool_ss [Abbr `u`] >> drule_all slot_actual_body >> simp[]) >>
  `slot_copy_inv cs load original p d n [] (i+1) u` by
    simp[Abbr `u`, slot_copy_body_invariant] >>
  `slot_copy_runtime_frame cs d i original b` by
    simp[Abbr `b`, slot_copy_runtime_frame_condition] >>
  `slot_copy_runtime_frame cs d (i+1) original u` by
    (simp_tac bool_ss [Abbr `u`] >> irule slot_copy_runtime_frame_body >>
     conj_tac >- (qexists_tac `n` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     first_assum ACCEPT_TAC) >>
  qpat_x_assum `!i s. n = i + k /\ _ ==> _`
    (qspecl_then [`i+1`, `u`] mp_tac) >>
  simp[Abbr `u`, slot_copy_body_counter, ADD_CLAUSES] >> metis_tac[]
QED

Theorem create_slot_copy_actual_exit_frame:
  fn_has_code cs (slot_copy_final cs src dst n load) fn /\
  (load = SLOAD \/ load = TLOAD) /\
  slot_copy_external cs src /\ slot_copy_external cs dst /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME d /\
  n < 2**256 /\ w2n d + 32*n < 2**256 /\
  (cs.cs_current_bb <> slot_copy_exit cs \/ 0 < LENGTH cs.cs_current_insts) /\
  lookup_block (slot_copy_exit cs) fn.fn_blocks = SOME exit /\
  phi_prefix_length exit.bb_instructions = 0 /\
  s.vs_current_bb = cs.cs_current_bb /\ s.vs_inst_idx = LENGTH cs.cs_current_insts /\
  t.vs_current_bb = slot_copy_exit cs /\ t.vs_inst_idx = 0 /\
  RTC (\u v. (u.vs_current_bb <> slot_copy_exit cs \/ u.vs_inst_idx <> 0) /\
             ?ms. gas_origin_edge F explicit ctx fn u ms (OK v)) s t ==>
  slot_copy_inv cs load s p d n [] n t /\ eval_operand dst t = SOME d /\
  slot_copy_runtime_frame cs d n s t
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qabbrev_tac `R = \u v. (u.vs_current_bb <> slot_copy_exit cs \/ u.vs_inst_idx <> 0) /\
                         ?ms. gas_origin_edge F explicit ctx fn u ms (OK v)` >>
  `!u v. R u v ==> (u.vs_current_bb <> slot_copy_exit cs \/ u.vs_inst_idx <> 0) /\
                   ?ms. gas_origin_edge F explicit ctx fn u ms (OK v)` by simp[Abbr `R`] >>
  `!u v. R u v ==> ?ms. gas_origin_edge F explicit ctx fn u ms (OK v)` by metis_tac[] >>
  drule slot_actual_phi_targets >> simp[] >> strip_tac >>
  drule slot_copy_lookup >> strip_tac >>
  qabbrev_tac `u = slot_copy_initial cs s` >>
  `u.vs_current_bb = slot_copy_cond cs /\ u.vs_inst_idx = 0` by
    simp[Abbr `u`, slot_copy_initial_def, jump_to_def] >>
  `RTC R u t` by
    (simp_tac bool_ss [Abbr `u`] >> irule slot_actual_init >>
     simp[] >> reverse conj_tac >- fs[] >>
     qexistsl_tac [`<|bb_label := cs.cs_current_bb;
                   bb_instructions := cs.cs_current_insts ++ slot_copy_init_insts cs|>`,
                   `ctx`, `explicit`, `fn`] >> simp[] >> first_assum ACCEPT_TAC) >>
  `slot_copy_inv cs load s p d n [] 0 u` by
    (simp_tac bool_ss [Abbr `u`] >> irule slot_copy_initial_invariant >>
     simp[create_memory_snapshot_def]) >>
  `slot_copy_runtime_frame cs d 0 s u` by simp[Abbr `u`, slot_copy_runtime_frame_initial] >>
  `slot_copy_inv cs load s p d n [] n t /\ slot_copy_runtime_frame cs d n s t` by
    (drule_at (Pat `RTC _ _ _`) slot_actual_counted >>
     disch_then irule >> simp[] >> conj_tac
     >- (qexistsl_tac [`ctx`, `dst`, `exit`, `explicit`, `fn`, `src`] >>
         simp[] >> metis_tac[optionTheory.SOME_11]) >>
     qexistsl_tac [`0`, `n`] >> simp[]) >>
  simp[] >> fs[slot_copy_inv_def] >> metis_tac[]
QED

Theorem create_slot_copy_actual_exit:
  fn_has_code cs (slot_copy_final cs src dst n load) fn /\
  (load = SLOAD \/ load = TLOAD) /\
  slot_copy_external cs src /\ slot_copy_external cs dst /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME d /\
  n < 2**256 /\ w2n d + 32*n < 2**256 /\
  (cs.cs_current_bb <> slot_copy_exit cs \/ 0 < LENGTH cs.cs_current_insts) /\
  lookup_block (slot_copy_exit cs) fn.fn_blocks = SOME exit /\
  phi_prefix_length exit.bb_instructions = 0 /\
  s.vs_current_bb = cs.cs_current_bb /\ s.vs_inst_idx = LENGTH cs.cs_current_insts /\
  t.vs_current_bb = slot_copy_exit cs /\ t.vs_inst_idx = 0 /\
  RTC (\u v. (u.vs_current_bb <> slot_copy_exit cs \/ u.vs_inst_idx <> 0) /\
             ?ms. gas_origin_edge F explicit ctx fn u ms (OK v)) s t ==>
  slot_copy_inv cs load s p d n [] n t /\ eval_operand dst t = SOME d
Proof
  disch_then (mp_tac o MATCH_MP (SPEC_ALL create_slot_copy_actual_exit_frame)) >> simp[]
QED

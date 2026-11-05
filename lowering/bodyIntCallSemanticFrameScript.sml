Theory bodyIntCallSemanticFrame
Ancestors
  fragExec exprLoweringProps venomCallOracleDefs venomState venomExecSemantics list rich_list
  loweringSlice venomExecProofs valueEncoding emitHelperProps compileEnv venomInst
  localPtrsProps stmtSim exprLowering emitHelper finite_map freshWrites varsExt exprSim

Theorem run_inst_seq_observation:
  !insts s t obs.
    EVERY (\i. !s t. step_inst_base i s = OK t ==> obs t = obs s) insts /\
    run_inst_seq insts s = OK t ==> obs t = obs s
Proof
  Induct >> simp[run_inst_seq_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem frag_exec_run_inst_seq_observation:
  sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
  isPREFIX sa.cs_current_insts sb.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  EVERY (\i. !s t. step_inst_base i s = OK t ==> obs t = obs s)
    (emitted_insts sa sb) /\
  (!s n. obs (s with vs_inst_idx := n) = obs s) /\
  (!s. P s ==> ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    Q (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
  frag_exec ctx sa sb (\s. P s /\ obs s = saved)
    (\t. Q t /\ obs t = saved) (\r. F)
Proof
  strip_tac >> irule frag_exec_run_inst_seq >> simp[] >>
  rpt strip_tac >>
  qpat_x_assum `!s. P s ==> _` drule >> strip_tac >>
  first_assum (irule_at Any) >> simp[] >>
  drule_all run_inst_seq_observation >> simp[]
QED

Theorem frag_exec_run_inst_seq_storage_frame:
  sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
  isPREFIX sa.cs_current_insts sb.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  EVERY (\i. !s t. step_inst_base i s = OK t ==>
    contract_storage t = contract_storage s /\
    contract_transient t = contract_transient s) (emitted_insts sa sb) /\
  (!s. P s ==> ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    Q (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
  frag_exec ctx sa sb
    (\s. P s /\ (contract_storage s,contract_transient s) = saved)
    (\t. Q t /\ (contract_storage t,contract_transient t) = saved) (\r. F)
Proof
  strip_tac >>
  ho_match_mp_tac frag_exec_run_inst_seq_observation >>
  simp[contract_storage_def, contract_transient_def] >>
  gvs[EVERY_MEM, contract_storage_def, contract_transient_def] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in
    if null axioms andalso null (Thm.hyp th) andalso
       List.all (fn oracle => oracle = "DISK_THM") oracles then ()
    else raise Fail "Semantic frame probe has unproved dependencies"
  end) [run_inst_seq_observation, frag_exec_run_inst_seq_observation,
        frag_exec_run_inst_seq_storage_frame];

Theorem frag_exec_observation_then:
  cs_extends sa sm /\ cs_extends sm sb /\
  frag_exec ctx sa sm P (\m. A m /\ obs m = saved) (\r. F) /\
  (!m. A m ==> frag_exec ctx sm sb (\s. s = m)
    (\t. B m t /\ obs t = obs m) (\r. F)) ==>
  frag_exec ctx sa sb P (\t. (?m. A m /\ B m t) /\ obs t = saved) (\r. F)
Proof
  strip_tac >> drule frag_exec_then >> disch_then irule >> simp[] >>
  rpt strip_tac >> qpat_x_assum `!m. A m ==> _` drule >>
  strip_tac >> irule frag_exec_weaken >>
  first_assum (irule_at Any) >> simp[] >>
  metis_tac[]
QED

val () =
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag frag_exec_observation_then)
  in
    if null axioms andalso null (Thm.hyp frag_exec_observation_then) andalso
       List.all (fn oracle => oracle = "DISK_THM") oracles then ()
    else raise Fail "Observation composition has unproved dependencies"
  end;

Theorem frag_exec_jnz_arm_observation:
  frag_exec ctx bs bn (\s. s = jump_to bl tt)
    (\u. Q u /\ obs u = obs (jump_to bl tt)) R /\
  obs tt = saved /\
  (!l s. obs (jump_to l s) = obs s) /\
  eval_operand cond_op tt = SOME (val_to_w256 (BoolV bv)) /\
  emit_inst JNZ [cond_op; Label tl; Label el] [] s5 = ((), s6) /\
  new_block tl s6 = (x6, s7) /\
  emit_inst JMP [Label xl] [] bn = ((), bo) /\
  new_block lbl bo = (bx, bp) /\
  (if bv then tl else el) = bl /\ bs.cs_current_bb = bl /\
  bs.cs_current_insts = [] /\
  s5.cs_current_bb = s1.cs_current_bb /\
  s5.cs_current_insts = s1.cs_current_insts /\
  sb.cs_current_bb = xl /\ sb.cs_current_insts = [] /\
  cs_extends s1 s6 /\ cs_extends s6 s7 /\ cs_extends s7 sb /\
  cs_extends s1 bs /\ cs_extends bs bn /\ cs_extends bs bp /\
  cs_extends bp sb ==>
  frag_exec ctx s1 sb (\s. s = tt)
    (\t. (?u. Q u /\ t = jump_to xl u) /\ obs t = saved) R
Proof
  strip_tac >> imp_res_tac emit_inst_extends >>
  PURE_REWRITE_TAC[frag_exec_def] >> BETA_TAC >> rpt strip_tac >>
  qpat_x_assum `_ = tt` SUBST_ALL_TAC >>
  `step_inst_base (mk_inst s5.cs_next_id JNZ [cond_op; Label tl; Label el] [])
     tt = OK (jump_to bl tt)` by
    (qpat_x_assum `(if _ then _ else _) = bl` (SUBST_ALL_TAC o SYM) >>
     simp[venomInstTheory.mk_inst_def] >> drule step_jnz_behavior >>
     disch_then (fn th => simp[th]) >> Cases_on `bv` >> simp[val_to_w256_def]) >>
  qabbrev_tac `jnz = mk_inst s5.cs_next_id JNZ [cond_op; Label tl; Label el] []` >>
  qabbrev_tac `jbb = <| bb_label := s6.cs_current_bb;
                        bb_instructions := s6.cs_current_insts |>` >>
  `fn_has_code s6 s7 fn` by
    (irule fn_has_code_mid >> metis_tac[]) >>
  `fn_has_code bs bp fn` by
    (irule fn_has_code_mid >> metis_tac[cs_extends_trans]) >>
  `lookup_block tt.vs_current_bb fn.fn_blocks = SOME jbb` by
    (simp[Abbr `jbb`] >> metis_tac[fn_has_code_new_block]) >>
  `get_instruction jbb tt.vs_inst_idx = SOME jnz` by
    fs[Abbr `jbb`, get_instruction_def, EL_LENGTH_APPEND] >>
  `is_terminator jnz.inst_opcode /\ jnz.inst_opcode <> INVOKE` by
    simp[Abbr `jnz`, venomInstTheory.mk_inst_def, is_terminator_def] >>
  `(?u. (Q u /\ obs u = obs (jump_to bl tt)) /\ ~u.vs_halted /\
      !fuel r. run_from fuel ctx fn (jump_to xl u) = r /\
        (!e. r <> Error e) ==> ?fuel'. run_from fuel' ctx fn tt = r) \/
   (?fuel r. run_from fuel ctx fn tt = r /\ exit_result r /\ R r)` by
    (ho_match_mp_tac if_branch_to_exit >>
     goal_assum (drule_at (Pat `frag_exec _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `lookup_block _ _ = _`)) >>
     goal_assum (drule_at (Pat `get_instruction _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_inst JMP _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `new_block _ _ = _`)) >> simp[] >> metis_tac[])
  >- (disj1_tac >> qexists_tac `jump_to xl u` >>
      simp[] >> conj_tac >- metis_tac[] >>
      simp[jump_to_def] >> metis_tac[jump_to_def]) >>
  disj2_tac >> metis_tac[]
QED

val () =
  let val th = frag_exec_jnz_arm_observation
      val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in
    if null axioms andalso null (Thm.hyp th) andalso
       List.all (fn oracle => oracle = "DISK_THM") oracles then ()
    else raise Fail "Selected branch observation has unproved dependencies"
  end;

Theorem emit_op_storage_frame_frag:
  !ctx func cenv cx es opc args sa op sb s0 w R.
    emit_op opc args sa = (op, sb) /\ local_ptrs_reserved cenv sa /\
    opc <> INVOKE /\ ~is_terminator opc /\
    (stmt_state_rel ctx func cenv cx es s0 ==>
     !out. step_inst_base (mk_inst sa.cs_next_id opc args [out]) s0 =
           OK (update_var out w s0)) ==>
    frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
      (\s. stmt_state_rel ctx func cenv cx es s /\ eval_operand op s = SOME w /\
           (!x w'. not_fresh_at sa x /\ lookup_var x s0 = SOME w' ==>
                   lookup_var x s = SOME w') /\
           (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                    FLOOKUP s.vs_allocas aid = SOME b) /\
           s.vs_memory = s0.vs_memory /\
           contract_storage s = contract_storage s0 /\
           contract_transient s = contract_transient s0) R
Proof
  rpt strip_tac >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac emit_op_extends >>
  qabbrev_tac `out = STRING #"%" (toString sa.cs_next_var)` >>
  `!x. not_fresh_at sa x ==> x <> out` by
    (simp[not_fresh_at_def, Abbr `out`] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `not_local_ptr cenv es.scopes out` by
    (qunabbrev_tac `out` >> irule local_ptrs_reserved_fresh >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb)` by simp[venomInstTheory.mk_inst_def] >>
  irule frag_exec_run_inst_seq >>
  fs[same_blocks_def, IS_PREFIX_APPEND3] >>
  rpt strip_tac >> disj1_tac >> gvs[] >>
  qexists_tac `update_var out w s0` >>
  asm_simp_tac (srw_ss()) [run_inst_seq_def, stmt_state_rel_inst_idx] >>
  conj_tac >- (irule stmt_state_rel_update_var >> simp[]) >>
  simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       contract_storage_def, contract_transient_def] >>
  rpt strip_tac >> Cases_on `out = x` >> gvs[lookup_var_def]
QED

val () =
  let val th = emit_op_storage_frame_frag
      val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in
    if null axioms andalso null (Thm.hyp th) andalso
       List.all (fn oracle => oracle = "DISK_THM") oracles then ()
    else raise Fail "Instruction storage frame has unproved dependencies"
  end;

Theorem stmt_state_rel_fresh_vars:
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  (!x. not_fresh_at sa x ==> FLOOKUP V x = FLOOKUP s.vs_vars x) ==>
  stmt_state_rel ctx func cenv cx es (s with vs_vars := V)
Proof
  strip_tac >> irule stmt_state_rel_vars_frame >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sa p` by
        (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
      simp[lookup_var_def]) >>
  rpt strip_tac >>
  `not_fresh_at sa p` by
    (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  simp[lookup_var_def]
QED

Theorem writes_fresh_run_storage_frame_post:
  writes_fresh sa insts /\ run_inst_seq insts s0 = OK t /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s0 /\
  eval_operand op t = SOME w ==>
  stmt_state_rel ctx func cenv cx es (t with vs_inst_idx := n) /\
  eval_operand op (t with vs_inst_idx := n) = SOME w /\
  (!x w'. not_fresh_at sa x /\ lookup_var x s0 = SOME w' ==>
    lookup_var x (t with vs_inst_idx := n) = SOME w') /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
    FLOOKUP (t with vs_inst_idx := n).vs_allocas aid = SOME b) /\
  (t with vs_inst_idx := n).vs_memory = s0.vs_memory /\
  contract_storage (t with vs_inst_idx := n) = contract_storage s0 /\
  contract_transient (t with vs_inst_idx := n) = contract_transient s0
Proof
  strip_tac >> drule_all run_inst_seq_writes_fresh >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es (s0 with vs_vars := t.vs_vars)` by
    (irule stmt_state_rel_fresh_vars >> simp[] >> qexists_tac `sa` >> simp[]) >>
  qpat_x_assum `t = _` SUBST_ALL_TAC >>
  simp[stmt_state_rel_inst_idx, eval_operand_def, lookup_var_def,
       contract_storage_def, contract_transient_def] >>
  rpt strip_tac >> gvs[lookup_var_def] >>
  Cases_on `op` >> gvs[eval_operand_def, lookup_var_def]
QED

Theorem writes_fresh_success_restore:
  writes_fresh sa insts /\ P s0 /\
  (!s. P s ==> P (drop_fresh sa s)) /\
  (!s. fresh_vars_wrt sa s /\ P s ==>
    ?t. run_inst_seq insts s = OK t /\ eval_operand op t = SOME w) ==>
  ?t. run_inst_seq insts s0 = OK t /\ eval_operand op t = SOME w
Proof
  strip_tac >>
  `fresh_vars_wrt sa (drop_fresh sa s0) /\ P (drop_fresh sa s0)` by
    simp[fresh_vars_wrt_drop_fresh] >>
  qpat_x_assum `!s. fresh_vars_wrt _ _ /\ _ ==> _` drule_all >> strip_tac >>
  qspecl_then [`insts`, `drop_fresh sa s0`, `s0`] mp_tac run_inst_seq_vars_ext >>
  (impl_tac >- (simp[vars_ext_drop_fresh] >>
    gvs[writes_fresh_def, EVERY_MEM] >> metis_tac[fresh_write_op_simple])) >>
  simp[vars_ext_result_def] >> strip_tac >>
  goal_assum (drule_at Any) >>
  gvs[vars_ext_def] >> rename1 `partial.vs_vars SUBMAP full.vs_vars` >>
  drule eval_operand_vars_ext >>
  disch_then (qspec_then `op` mp_tac) >> simp[] >>
  qpat_x_assum `full = _` SUBST1_TAC >> simp[]
QED

Theorem frag_exec_straight_fresh_storage_frame_success:
  straight_fresh m /\ m sa = (op,sb) /\ local_ptrs_reserved cenv sa /\
  (!s. P s ==> P (drop_fresh sa s)) /\
  (!s. fresh_vars_wrt sa s /\ P s ==>
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\ eval_operand op t = SOME w) ==>
  frag_exec ctx sa sb
    (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s /\ P s)
    (\s. stmt_state_rel ctx func cenv cx es s /\ eval_operand op s = SOME w /\
      (!x w'. not_fresh_at sa x /\ lookup_var x s0 = SOME w' ==>
        lookup_var x s = SOME w') /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
        FLOOKUP s.vs_allocas aid = SOME b) /\
      s.vs_memory = s0.vs_memory /\
      contract_storage s = contract_storage s0 /\
      contract_transient s = contract_transient s0) R
Proof
  strip_tac >>
  qpat_x_assum `straight_fresh _` (mp_tac o REWRITE_RULE [straight_fresh_def]) >>
  disch_then drule >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)` by
    (gvs[writes_fresh_def, EVERY_MEM] >> metis_tac[fresh_write_op_simple]) >>
  irule frag_exec_run_inst_seq >> simp[IS_PREFIX_APPEND3] >>
  rpt strip_tac >> gvs[] >> disj1_tac >>
  `?t. run_inst_seq (emitted_insts sa sb) s0 = OK t /\ eval_operand op t = SOME w` by
    (irule writes_fresh_success_restore >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[]) >>
  goal_assum (drule_at Any) >>
  drule_all writes_fresh_run_storage_frame_post >>
  disch_then (qspec_then `LENGTH sb.cs_current_insts` mp_tac) >> simp[]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in
    if null axioms andalso null (Thm.hyp th) andalso
       List.all (fn oracle => oracle = "DISK_THM") oracles then ()
    else raise Fail "Straight-fresh storage frame has unproved dependencies"
  end) [stmt_state_rel_fresh_vars, writes_fresh_run_storage_frame_post,
        writes_fresh_success_restore, frag_exec_straight_fresh_storage_frame_success];

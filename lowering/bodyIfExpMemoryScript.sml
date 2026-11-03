Theory bodyIfExpMemory
Ancestors
  exprSimIfExp fragExec fragExecMem instMemFrontier allocaHistoryFragment
  emitHelper emitHelperProps compileEnv venomState venomInst
  list rich_list loweringSlice venomExecSemantics venomExecProofs exprLoweringProps
  bodyMemoryDefs exprSim vyperAST vyperInterpreter memSafeRun allocaHistory

Theorem frag_exec_assign_mem:
  !ctx st st' src out P Q R.
    emit_inst ASSIGN [src] [out] st = ((), st') /\
    (!s. P s ==> ?w. eval_operand src s = SOME w /\
                     Q ((update_var out w s) with
                          vs_inst_idx := LENGTH st'.cs_current_insts)) ==>
    frag_exec_mem ctx st st' P Q R
Proof
  rpt strip_tac >> imp_res_tac emit_inst_extends >>
  irule frag_exec_mem_run_inst_seq >>
  `emitted_insts st st' = [mk_inst st.cs_next_id ASSIGN [src] [out]]` by
    simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[venomInstTheory.mk_inst_def, is_terminator_def] >> gen_tac >> disch_tac >>
  first_x_assum drule >> strip_tac >>
  conj_tac
  >- (simp[GSYM mk_inst_def, run_inst_seq_mem_ok_last] >>
      irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  disj1_tac >>
  simp[run_inst_seq_def, step_inst_base_def, exec_pure1_def, comp_bind_def,
       comp_return_def] >> gvs[]
QED

Theorem assign_history[local]:
  emit_inst ASSIGN [src] [out] st = ((),st') /\ fn_has_code st st' func /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  eval_operand src s = SOME w ==>
  alloca_history func ((update_var out w s) with
                       vs_inst_idx := LENGTH st'.cs_current_insts)
Proof
  rpt strip_tac >> imp_res_tac emit_inst_extends >>
  `emitted_insts st st' = [mk_inst st.cs_next_id ASSIGN [src] [out]]` by
    simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
  `run_inst_seq (emitted_insts st st') s = OK (update_var out w s)` by
    simp[run_inst_seq_def, mk_inst_def, step_inst_base_def, exec_pure1_def,
         comp_bind_def, comp_return_def] >>
  `(?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
      DROP s.vs_inst_idx bb.bb_instructions = emitted_insts st st' ++ rest) /\
    s.vs_inst_idx + LENGTH (emitted_insts st st') = LENGTH st'.cs_current_insts /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st st')` by
    (gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
     simp[DROP_APPEND, DROP_LENGTH_TOO_LONG, mk_inst_def, is_terminator_def]) >>
  drule_all alloca_history_run_inst_seq >> simp[]
QED

Theorem frag_exec_assign_mem_at:
  emit_inst ASSIGN [src] [out] st = ((),st') /\
  fn_has_code st st' func /\ fn_inst_ids_distinct func /\
  alloca_history func entry /\ alloca_inv entry /\
  eval_operand src entry = SOME w ==>
  frag_exec_mem ctx st st' (\s. s = entry)
    (\s. s = ((update_var out w entry) with
                vs_inst_idx := LENGTH st'.cs_current_insts) /\
         alloca_history func s /\
         s.vs_alloca_next = entry.vs_alloca_next) R
Proof
  rpt strip_tac >>
  qabbrev_tac `P = \s. s = entry /\ ~s.vs_halted /\
     s.vs_current_bb = st.cs_current_bb /\
     s.vs_inst_idx = LENGTH st.cs_current_insts` >>
  `frag_exec_mem ctx st st' P
    (\s. s = ((update_var out w entry) with
                vs_inst_idx := LENGTH st'.cs_current_insts) /\
         alloca_history func s /\
         s.vs_alloca_next = entry.vs_alloca_next) R` suffices_by
    (simp[frag_exec_mem_def, Abbr `P`] >> metis_tac[]) >>
  irule frag_exec_assign_mem >> qexistsl_tac [`out`, `src`] >> simp[] >>
  gen_tac >> strip_tac >> gvs[Abbr `P`] >>
  drule_all assign_history >> simp[update_var_def]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_IFEXP_ASSIGN_MEMORY_AUDIT OK\n"
     else raise Fail "ifexp assignment memory inherited admission"
  end) [frag_exec_assign_mem, assign_history, frag_exec_assign_mem_at];

Theorem ifexp_arm_frag_mem:
  !ctx func cenv cx ty e es1 res es' bs bm bn eop rv tt lbl.
    expr_sim_mem ctx func cenv cx ty e es1 /\
    lower_value compile_expr cenv ty e bs = (eop, bm) /\
    emit_inst ASSIGN [eop] [rv] bm = ((), bn) /\
    (do result <- eval_expr cx e; read_result cx result od) es1 = (res, es') /\
    expr_res_ok res /\ fn_has_code bs bn func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv bs /\ stmt_state_rel ctx func cenv cx es1 tt /\
    cs_extends bs bm /\ alloca_history func (jump_to lbl tt) /\
    res <> INR (Error (RuntimeError "convert empty bytes to signed")) ==>
    frag_exec_mem ctx bs bn (\s. s = jump_to lbl tt)
      (\s. (?v u w. res = INL v /\
             expr_post ctx func cenv cx e es1 bs bm (jump_to lbl tt) es' v eop u /\
             eval_operand eop u = SOME w /\
             s = (update_var rv w u) with
                   vs_inst_idx := LENGTH bn.cs_current_insts) /\
           alloca_history func s /\
           (jump_to lbl tt).vs_alloca_next <= s.vs_alloca_next)
      (expr_exit res)
Proof
  rpt strip_tac >>
  `cs_extends bm bn` by metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  `fn_has_code bs bm func /\ fn_has_code bm bn func` by
    metis_tac[fn_has_code_mid, cs_extends_refl] >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
  disch_then (qspecl_then [`bs`, `bm`, `eop`, `res`, `es'`, `jump_to lbl tt`]
                mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (mp_tac o MATCH_MP frag_exec_mem_pre_exit_c) >>
  disch_then (qspecl_then [`\s. s = jump_to lbl tt`, `expr_exit res`] mp_tac) >>
  (impl_tac >- simp[stmt_state_rel_jump_to]) >>
  disch_then (fn th => irule (MATCH_MP frag_exec_mem_then th)) >>
  simp[] >> rpt strip_tac >>
  `?w. eval_operand eop t = SOME w` by
    (gvs[expr_post_def, expr_val_rel_def] >> metis_tac[]) >>
  `alloca_inv t` by gvs[expr_post_def, stmt_state_rel_def] >>
  drule_all frag_exec_assign_mem_at >>
  disch_then (qspecl_then [`ctx`, `expr_exit res`] mp_tac) >>
  disch_then (mp_tac o MATCH_MP frag_exec_mem_weaken) >>
  disch_then irule >> simp[] >>
  strip_tac >> qexistsl_tac [`t`, `w`] >> simp[]
QED

val () =
  let val th = ifexp_arm_frag_mem
      val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_IFEXP_ARM_MEMORY_AUDIT OK\n"
     else raise Fail "ifexp arm memory inherited admission"
  end;

Theorem ifexp_jump_result_mem[local]:
  !fuel ctx fn s bb inst lbl r.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
    step_inst_base inst s = OK (jump_to lbl s) /\ ~s.vs_halted /\
    inst_mem_below_frontier inst s /\
    run_from fuel ctx fn (jump_to lbl s) = r /\ (!e. r <> Error e) ==>
    ?fuel'. run_from fuel' ctx fn s = r /\
      (mem_safe_run fuel ctx fn (jump_to lbl s) ==>
       mem_safe_run fuel' ctx fn s)
Proof
  rpt strip_tac >> qexists_tac `SUC fuel` >> conj_tac
  >- (irule run_from_jump_result >> metis_tac[]) >>
  strip_tac >>
  Cases_on `lookup_block lbl fn.fn_blocks`
  >- gvs[run_from_def, jump_to_def] >>
  rename1 `lookup_block lbl _ = SOME bb'` >>
  Cases_on `phi_prefix_length bb'.bb_instructions = 0`
  >- (`eval_phis (jump_to lbl s) bb'.bb_instructions = OK (jump_to lbl s)` by
        (Cases_on `bb'.bb_instructions` >> gvs[phi_prefix_length_def] >>
         rename1 `h.inst_opcode` >> Cases_on `h.inst_opcode = PHI` >>
         gvs[phi_prefix_length_def, eval_phis_def]) >>
      simp[mem_safe_run_def, Once mem_safe_block_def,
           mem_safe_step_non_invoke, step_inst_non_invoke,
           Once exec_block_def, jump_to_def] >>
      mp_tac mem_safe_blocks_run >>
      disch_then (qspecl_then [`fuel`, `ctx`, `fn`, `jump_to lbl s`,
                             `bb'`, `jump_to lbl s`] mp_tac) >>
      simp[jump_to_def] >> gvs[jump_to_def]) >>
  `?phi rest. bb'.bb_instructions = phi :: rest /\ phi.inst_opcode = PHI` by
    (Cases_on `bb'.bb_instructions` >> gvs[phi_prefix_length_def] >>
     rename1 `h.inst_opcode` >> Cases_on `h.inst_opcode = PHI` >> gvs[]) >>
  qpat_x_assum `run_from _ _ _ _ = _` mp_tac >>
  simp[run_from_def, jump_to_def, Once exec_block_def, get_instruction_def,
       step_inst_non_invoke, step_inst_base_def]
QED

Theorem ifexp_branch_to_exit_mem:
  !ctx fn s0 sc jbb jnz sa sb sx sd lbl lbl' x P Q R.
    lookup_block sc.vs_current_bb fn.fn_blocks = SOME jbb /\
    get_instruction jbb sc.vs_inst_idx = SOME jnz /\
    is_terminator jnz.inst_opcode /\ jnz.inst_opcode <> INVOKE /\
    step_inst_base jnz sc = OK (jump_to sa.cs_current_bb sc) /\
    ~sc.vs_halted /\ inst_mem_below_frontier jnz sc /\
    (!fuel r. run_from fuel ctx fn sc = r /\ (!e. r <> Error e) ==>
              ?fuel'. run_from fuel' ctx fn s0 = r /\
                (mem_safe_run fuel ctx fn sc ==> mem_safe_run fuel' ctx fn s0)) /\
    sa.cs_current_insts = [] /\ P (jump_to sa.cs_current_bb sc) /\
    frag_exec_mem ctx sa sb P Q R /\ cs_extends sa sb /\
    emit_inst JMP [Label lbl] [] sb = ((), sx) /\
    new_block lbl' sx = (x, sd) /\ fn_has_code sa sd fn ==>
    (?s'. Q s' /\ ~s'.vs_halted /\
          !fuel r. run_from fuel ctx fn (jump_to lbl s') = r /\
                   (!e. r <> Error e) ==>
                   ?fuel'. run_from fuel' ctx fn s0 = r /\
                     (mem_safe_run fuel ctx fn (jump_to lbl s') ==>
                      mem_safe_run fuel' ctx fn s0)) \/
    (?fuel r. run_from fuel ctx fn s0 = r /\ exit_result r /\ R r /\
              mem_safe_run fuel ctx fn s0)
Proof
  rpt strip_tac >>
  `cs_extends sb sx /\ cs_extends sx sd` by
    metis_tac[cs_appends_emit_helpers, cs_appends_def, cs_extends_new_block] >>
  `fn_has_code sa sb fn /\ fn_has_code sx sd fn` by
    metis_tac[fn_has_code_mid, cs_extends_refl, cs_extends_trans] >>
  qpat_x_assum `frag_exec_mem _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [frag_exec_mem_def]) >>
  disch_then (qspecl_then [`fn`, `jump_to sa.cs_current_bb sc`] mp_tac) >>
  (impl_tac >- simp[jump_to_def]) >>
  strip_tac
  >- (disj1_tac >> qexists_tac `s'` >> simp[] >> rpt strip_tac >>
      imp_res_tac emit_inst_extends >>
      qabbrev_tac `j = mk_inst sb.cs_next_id JMP [Label lbl] []` >>
      qabbrev_tac `jb = <| bb_label := sx.cs_current_bb;
                           bb_instructions := sx.cs_current_insts |>` >>
      `lookup_block s'.vs_current_bb fn.fn_blocks = SOME jb` by
        metis_tac[fn_has_code_new_block] >>
      `get_instruction jb s'.vs_inst_idx = SOME j` by
        simp[Abbr `jb`, get_instruction_def, EL_LENGTH_APPEND] >>
      `j.inst_opcode = JMP /\ step_inst_base j s' = OK (jump_to lbl s')` by
        simp[Abbr `j`, mk_inst_def, step_jmp_behavior] >>
      `is_terminator j.inst_opcode /\ j.inst_opcode <> INVOKE /\
       inst_mem_below_frontier j s'` by
        (simp[is_terminator_def] >> irule below_frontier_no_ranges >>
         simp[Abbr `j`, mk_inst_def]) >>
      `?fuel'. run_from fuel' ctx fn s' = run_from fuel ctx fn (jump_to lbl s') /\
         (mem_safe_run fuel ctx fn (jump_to lbl s') ==>
          mem_safe_run fuel' ctx fn s')` by
        (irule ifexp_jump_result_mem >> metis_tac[]) >>
      qpat_x_assum `!fuel r. run_from fuel ctx fn s' = r /\ _ ==> _`
        drule_all >> strip_tac >>
      drule_all ifexp_jump_result_mem >> strip_tac >>
      metis_tac[]) >>
  disj2_tac >>
  `!e. r <> Error e` by metis_tac[exit_result_not_error] >>
  drule_all ifexp_jump_result_mem >> strip_tac >>
  metis_tac[]
QED

Theorem ifexp_history_jump[local]:
  alloca_history func s ==> alloca_history func (jump_to lbl s)
Proof
  strip_tac >> irule alloca_history_jump >> simp[jump_to_def] >>
  qexists_tac `s` >> simp[]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_IFEXP_BRANCH_MEMORY_AUDIT OK\n"
     else raise Fail "ifexp branch memory inherited admission"
  end) [ifexp_jump_result_mem, ifexp_branch_to_exit_mem, ifexp_history_jump];

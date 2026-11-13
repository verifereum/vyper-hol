(* Memory-instrumented counted rounds for immutable array iteration. *)
Theory bodyImmRoundsMemory
Ancestors
  whitelistForIterImmLoop stmtForArrayMemoryRounds stmtForArrayControlMemory
  stmtForArrayMemoryRoundSupport stmtSimForArrayLoop stmtSimProps
  exprLoweringProps fragGasSeqMem fragGasPathMem fragGasMode fragExecMem
  allocaHistory venomInstProofs venomExecSemantics venomState compileEnv
  loweringPosts loweringStateRelDefs vyperState words arithmetic list finite_map venomInst
  venomExecProps memSafeRun instMemFrontier gasCount exprSimDefs
  gasOutcome gasSummary gasContext vyperInterpreter stmtSimDefs stmtFragPtr
Libs
  monadsyntax

Theorem immutable_condition_boundary_mem:
  lookup_block cond func.fn_blocks =
    SOME <|bb_label := cond; bb_instructions :=
      [mk_inst j1 EQ [Var idx; lvo] [dv];
       mk_inst j2 JNZ [Var dv; Label exit; Label bod] []]|> /\
  array_loop_inv ctx func cenv cx P vs id idx saved_arr_base arr_base p dst sz
    ainst cond caller k es s /\
  eval_operand lvo s = SOME (n2w (LENGTH vs)) /\ LENGTH vs < dimword (:256) /\
  not_local_ptr cenv es.scopes dv /\ dv <> idx /\ dv <> p /\
  (!x. saved_arr_base = Var x ==> x <> dv) /\
  alloca_history func s ==>
  let t = jump_to (if k = LENGTH vs then exit else bod)
    (update_var dv (bool_to_word (k = LENGTH vs)) s) in
  array_loop_inv ctx func cenv cx P vs id idx saved_arr_base arr_base p dst sz
    ainst (if k = LENGTH vs then exit else bod) caller k es t /\
  gas_marked_path T ctx func s 0 (OK t) /\
  (!x. x <> dv ==> lookup_var x t = lookup_var x s) /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  alloca_history func t
Proof
  strip_tac >> simp[] >>
  conj_tac >- suspend "invariant" >>
  conj_tac >- suspend "path" >>
  conj_tac >- simp[jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  conj_tac >- simp[jump_to_def, update_var_def] >>
  conj_tac >- simp[jump_to_def, update_var_def] >>
  irule alloca_history_jump >> simp[jump_to_def, update_var_def] >>
  qexists_tac `s` >> simp[]
QED

Resume immutable_condition_boundary_mem[invariant]:
  fs[array_loop_inv_def] >>
  `stmt_state_rel ctx func cenv cx es
    (update_var dv (bool_to_word (k = LENGTH vs)) s)` by
    (irule stmt_state_rel_update_var >> simp[]) >>
  `eval_operand saved_arr_base (update_var dv (bool_to_word (k = LENGTH vs)) s) = SOME arr_base` by
    (irule eval_operand_update_other_local >> simp[]) >>
  simp[array_loop_inv_def, stmt_state_rel_jump_to, ret_pc_ok_jump_to] >>
  simp[jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE, ret_pc_ok_def] >>
  gvs[update_var_def, lookup_var_def, ret_pc_ok_def] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >> simp[] >>
  Cases_on `dv = x` >> simp[] >> metis_tac[]
QED

Resume immutable_condition_boundary_mem[path]:
  fs[array_loop_inv_def] >>
  `k < dimword (:256)` by decide_tac >>
  `((n2w k:bytes32) = n2w (LENGTH vs)) = (k = LENGTH vs)` by simp[n2w_11] >>
  `step_inst_base (mk_inst j1 EQ [Var idx; lvo] [dv]) s =
    OK (update_var dv (bool_to_word (k = LENGTH vs)) s)` by
    simp[step_inst_base_opcode_eqs, exec_pure2_def, mk_inst_def, eval_operand_def] >>
  `gas_path_mem_edge ctx func s 0
    (OK ((update_var dv (bool_to_word (k = LENGTH vs)) s) with vs_inst_idx := 1))` by
    (drule_at (Pat `step_inst_base _ _ = _`) straight_line_mem_edge >>
     simp[mk_inst_def, get_instruction_def, is_terminator_def, inst_dload_in_section_def] >>
     disch_then irule >>
     conj_tac >- (goal_assum (drule_at Any) >> simp[mk_inst_def]) >>
     irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  qmatch_asmsub_abbrev_tac `gas_path_mem_edge ctx func s 0 (OK mid)` >>
  `eval_operand (Var dv) mid = SOME (bool_to_word (k = LENGTH vs))` by
    simp[Abbr `mid`, update_var_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
  `step_inst_base (mk_inst j2 JNZ [Var dv; Label exit; Label bod] []) mid =
    OK (jump_to (if k = LENGTH vs then exit else bod) mid)` by
    (drule step_jnz_behavior >>
     disch_then (qspecl_then [`exit`, `bod`, `j2`] mp_tac) >>
     Cases_on `k = LENGTH vs` >> simp[bool_to_word_def, mk_inst_def]) >>
  `mid.vs_current_bb = cond /\ mid.vs_inst_idx = 1 /\ ~mid.vs_halted` by
    simp[Abbr `mid`, update_var_def] >>
  `gas_path_mem_edge ctx func mid 0
    (OK (jump_to (if k = LENGTH vs then exit else bod) mid))` by
    (simp[gas_path_mem_edge_def] >> qexists_tac `0` >>
     qexists_tac `mk_inst j2 JNZ [Var dv; Label exit; Label bod] []` >>
     simp[get_instruction_def, gas_count_step_def, mem_safe_step_non_invoke,
          step_inst_non_invoke, is_terminator_def, inst_dload_in_section_def] >>
     conj_tac >- (disj2_tac >> irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
     disj2_tac >> disj1_tac >>
     qexists_tac `if k = LENGTH vs then exit else bod` >> simp[]) >>
  `~(jump_to (if k = LENGTH vs then exit else bod) mid).vs_halted` by
    simp[jump_to_def, Abbr `mid`, update_var_def] >>
  `jump_to (if k = LENGTH vs then exit else bod) mid =
    jump_to (if k = LENGTH vs then exit else bod)
      (update_var dv (bool_to_word (k = LENGTH vs)) s)` by
    simp[Abbr `mid`, jump_to_def, update_var_def] >>
  simp[gas_marked_path_def] >> metis_tac[gas_path_mem_rules, ADD_CLAUSES]
QED
Finalise immutable_condition_boundary_mem

(* The cutoff state selects only live registers, not the address temporaries. *)
Theorem immutable_body_finish_mem:
  array_round_inv d ctx func cenv cx P vs id idx (Lit (n2w off)) (n2w off)
    p dst sz ainst bod caller orig k es s /\
  array_body_post_mem d ctx func cx (InLoop exit incr) bc bc' sb0 sb1 s_body r ee t /\
  cenv_top_ext cenv bc ei.scopes /\ bc.ce_return_buf = cenv.ce_return_buf /\
  eval_stmts cx stmts ei = (r,ee) /\ ee.scopes = sc :: rest /\
  (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
  ((r = INL () \/ r = INR ContinueException) ==>
    P (ee with scopes := rest) /\ lookup_scopes id rest = NONE) /\
  caller.cs_next_var <= cut.cs_next_var /\ cut.cs_next_var <= sb0.cs_next_var /\
  not_fresh_at cut idx /\ not_fresh_at cut p /\
  (!x. not_fresh_at cut x ==> not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep) /\
  (!x. not_fresh_at caller x ==> x <> idx /\ x <> nv) /\
  s_body.vs_allocas = s.vs_allocas /\ s_body.vs_alloca_next = s.vs_alloca_next /\
  (!x. not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep ==>
    lookup_var x s_body = lookup_var x s) /\
  (~block_is_terminated sb1 ==>
    sj.cs_blocks = sb1.cs_blocks /\ sj.cs_current_bb = sb1.cs_current_bb /\
    sj.cs_current_insts = sb1.cs_current_insts ++
      [mk_inst sb1.cs_next_id JMP [Label incr] []] /\ fn_has_code sb1 sj func) /\
  lookup_block incr func.fn_blocks =
    SOME <|bb_label := incr; bb_instructions :=
      [mk_inst i1 ADD [Var idx; Lit 1w] [nv];
       mk_inst i2 ASSIGN [Var nv] [idx];
       mk_inst i3 JMP [Label cond] []]|> /\
  (!scopes. not_local_ptr cenv scopes idx /\ not_local_ptr cenv scopes nv) /\
  p <> idx /\ p <> nv /\ fn_inst_ids_distinct func /\ k < LENGTH vs ==>
  ?b u.
    (case r of INL x => INL F
       | INR e => if e = ContinueException then INL F
                  else if e = BreakException then INL T else INR e) = INL b /\
    gas_marked_path T ctx func t 0 (OK u) /\
    (b ==> array_round_done d ctx func cenv cx caller orig exit
      (ee with scopes := rest) u) /\
    (~b ==> array_round_inv d ctx func cenv cx P vs id idx (Lit (n2w off)) (n2w off)
      p dst sz ainst cond caller orig (SUC k) (ee with scopes := rest) u)
Proof
  strip_tac >>
  `!x. not_fresh_at caller x ==> not_fresh_at cut x` by
    (fs[not_fresh_at_def] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
  `(!x. not_fresh_at caller x ==> x <> ov /\ x <> ep) /\
   idx <> ov /\ idx <> ep /\ p <> ov /\ p <> ep /\
   (!x. not_fresh_at cut x /\ x <> ov /\ x <> ep ==>
     lookup_var x s_body = lookup_var x s)` by metis_tac[] >>
  drule_all (array_body_round_restore_mem |>
    Q.INST [`sa` |-> `cut`, `saved_base` |-> `Lit (n2w off)`] |> SRULE []) >>
  simp[eval_operand_def] >> strip_tac >>
  Cases_on `r = INR BreakException`
  >- (qexistsl_tac [`T`, `t`] >> simp[gas_marked_path_def] >>
      irule (cj 1 gas_path_mem_rules) >> simp[]) >>
  `r = INL () \/ r = INR ContinueException` by fs[stmt_lands_def] >>
  `?u. gas_marked_path T ctx func t 0 (OK u) /\
    array_round_inv d ctx func cenv cx P vs id idx (Lit (n2w off)) (n2w off)
      p dst sz ainst incr caller orig k (ee with scopes := rest) u` by
    (irule array_round_postbody_entry >> simp[] >>
     qexistsl_tac [`exit`, `r`, `sb1`, `sj`] >> simp[]) >>
  qpat_x_assum `!scopes. _` (qspec_then `rest` strip_assume_tac) >>
  drule array_round_increment >> simp[eval_operand_def] >>
  disch_then drule >> simp[] >> strip_tac >>
  rename1 `gas_marked_path T ctx func u 0 (OK fin)` >>
  qexists_tac `fin` >> simp[] >>
  drule_all gas_marked_path_then >> simp[]
QED

Theorem immutable_prepared_one_round_mem:
  lookup_block cond func.fn_blocks =
    SOME <|bb_label := cond; bb_instructions :=
      [mk_inst j1 EQ [Var idx; lvo] [dv];
       mk_inst j2 JNZ [Var dv; Label exit; Label bod] []]|> /\
  lookup_block incr func.fn_blocks =
    SOME <|bb_label := incr; bb_instructions :=
      [mk_inst i1 ADD [Var idx; Lit 1w] [nv];
       mk_inst i2 ASSIGN [Var nv] [idx];
       mk_inst i3 JMP [Label cond] []]|> /\
  stmts_env bc (InLoop exit incr) ty stmts sb0 = (bc',sb1) /\
  fn_has_code sb0 sb1 func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved bc sb0 /\ ~block_is_terminated sb0 /\
  (~block_is_terminated sb1 ==>
    sj.cs_blocks = sb1.cs_blocks /\ sj.cs_current_bb = sb1.cs_current_bb /\
    sj.cs_current_insts = sb1.cs_current_insts ++
      [mk_inst sb1.cs_next_id JMP [Label incr] []] /\ fn_has_code sb1 sj func) /\
  (!scopes. not_local_ptr cenv scopes idx /\ not_local_ptr cenv scopes nv /\
    not_local_ptr cenv scopes dv) /\
  dv <> idx /\ dv <> p /\ p <> idx /\ p <> nv /\
  (!x. not_fresh_at caller x ==> x <> dv /\ x <> idx /\ x <> nv) /\
  caller.cs_next_var <= cut.cs_next_var /\ cut.cs_next_var <= sb0.cs_next_var /\
  not_fresh_at cut idx /\ not_fresh_at cut p /\
  (!x. not_fresh_at cut x ==> not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep) /\
  array_round_inv d ctx func cenv cx P vs id idx (Lit (n2w off)) (n2w off)
    p dst sz ainst cond caller orig k es s /\
  eval_operand lvo s = SOME (n2w (LENGTH vs)) /\
  k < LENGTH vs /\ LENGTH vs < dimword (:256) /\
  (!live. array_round_inv d ctx func cenv cx P vs id idx (Lit (n2w off)) (n2w off)
      p dst sz ainst bod caller orig k es live ==>
    ?s_body. s_body.vs_current_bb = sb0.cs_current_bb /\
      s_body.vs_inst_idx = LENGTH sb0.cs_current_insts /\ ~s_body.vs_halted /\
      stmt_state_rel ctx func bc cx
        (es with scopes := (FEMPTY |+ (id,
          <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: es.scopes) s_body /\
      ret_pc_ok bc sb0 s_body /\ gas_marked_path T ctx func live 0 (OK s_body) /\
      s_body.vs_allocas = live.vs_allocas /\ s_body.vs_alloca_next = live.vs_alloca_next /\
      alloca_history func s_body /\ return_buf_frame d bc sb0 s_body /\
      (!x. not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep ==>
        lookup_var x s_body = lookup_var x live)) /\
  cenv_top_ext cenv bc ((FEMPTY |+ (id,
    <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: es.scopes) /\
  stmt_frag_mem d ctx func cx (InLoop exit incr) RetQ bc
    (stmts_env bc (InLoop exit incr) ty stmts) (eval_stmts cx stmts)
    (es with scopes := (FEMPTY |+ (id,
      <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: es.scopes) /\
  (!gs r ee. eval_stmts cx stmts
    (es with <|scopes := (FEMPTY |+ (id,
      <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: es.scopes;
      gas_obs := gs|>) = (r,ee) ==>
    stmt_res_ok (InLoop exit incr) r /\
    ?sc rest. ee.scopes = sc :: rest /\
      (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
      ((r = INL () \/ r = INR ContinueException) ==>
        P (ee with scopes := rest) /\ lookup_scopes id rest = NONE)) ==>
  gas_outcome T (cx_tops cx) (ctx,func)
    (do push_scope_with_var id tv (EL k vs);
        finally (try (do eval_stmts cx stmts; return F od) handle_loop_exception)
          pop_scope od) (es,s)
    (\res ee t. ?b. res = INL b /\
      (b ==> array_round_done d ctx func cenv cx caller orig exit ee t) /\
      (~b ==> array_round_inv d ctx func cenv cx P vs id idx (Lit (n2w off)) (n2w off)
        p dst sz ainst cond caller orig (SUC k) ee t))
    (\res ee rr. ?e. res = INR e /\
      !tail. stmt_exit RetQ (ee with gas_obs := tail) (INR e) rr)
Proof
  strip_tac >>
  `array_loop_inv ctx func cenv cx P vs id idx (Lit (n2w off)) (n2w off)
      p dst sz ainst cond caller k es s /\ alloca_history func s` by
    fs[array_round_inv_def, array_round_frame_def] >>
  `not_local_ptr cenv es.scopes dv` by metis_tac[] >>
  drule_all (immutable_condition_boundary_mem |>
    Q.INST [`saved_arr_base` |-> `Lit (n2w off)`] |> SRULE []) >>
  simp[] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_marked_path T ctx func s 0 (OK live)` >>
  `array_round_inv d ctx func cenv cx P vs id idx (Lit (n2w off)) (n2w off)
    p dst sz ainst bod caller orig k es live` by suspend "live" >>
  qpat_x_assum `!live. _` drule >> strip_tac >>
  `gas_admissible (eval_stmts cx stmts) (stmt_res_ok (InLoop exit incr))
    (es with scopes := (FEMPTY |+ (id,
      <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: es.scopes)` by
    (simp[gas_admissible_def, evaluation_state_fn_updates] >> metis_tac[]) >>
  `gas_outcome T (cx_tops cx) (ctx,func) (eval_stmts cx stmts)
    (es with scopes := (FEMPTY |+ (id,
      <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: es.scopes, s_body)
    (array_body_post_mem d ctx func cx (InLoop exit incr) bc bc' sb0 sb1 s_body)
    (\r ee rr. !tail. stmt_exit RetQ (ee with gas_obs := tail) r rr)` by suspend "body_outcome" >>
  irule array_round_outcome_prefix_mem >>
  goal_assum (drule_at (Pat `gas_marked_path _ _ _ s _ _`)) >>
  irule array_round_outcome_prefix_mem >>
  goal_assum (drule_at (Pat `gas_marked_path _ _ _ live _ _`)) >>
  ho_match_mp_tac (array_body_round_outcome_mem |> Q.INST
    [`B` |-> `array_body_post_mem d ctx func cx (InLoop exit incr) bc bc' sb0 sb1 s_body`,
     `E` |-> `\r ee rr. !tail. stmt_exit RetQ (ee with gas_obs := tail) r rr`]) >>
  simp[] >> conj_tac >- suspend "scopes" >>
  conj_tac >- suspend "finish" >> suspend "exit"
QED

Resume immutable_prepared_one_round_mem[live]:
  simp[array_round_inv_def] >>
  irule array_round_frame_transport >> simp[] >> qexists_tac `s` >>
  fs[array_round_inv_def, Abbr `live`, lookup_var_def, jump_to_def, update_var_def,
     FLOOKUP_UPDATE] >> metis_tac[]
QED
Resume immutable_prepared_one_round_mem[body_outcome]:
  qhdtm_x_assum `stmt_frag_mem` mp_tac >>
  rewrite_tac[stmt_frag_mem_def] >>
  disch_then (qspecl_then [`sb0`, `sb1`, `s_body`, `bc'`] mp_tac) >>
  simp[GSYM array_body_post_mem_def, SF ETA_ss]
QED
Resume immutable_prepared_one_round_mem[scopes]:
  rpt strip_tac >> qpat_x_assum `!gs r ee. _` drule >> metis_tac[]
QED
Resume immutable_prepared_one_round_mem[finish]:
  rpt strip_tac >> qpat_x_assum `!gs r ee. _` drule >> strip_tac >>
  `bc.ce_return_buf = cenv.ce_return_buf` by
    metis_tac[stmtFragPtrTheory.cenv_top_ext_return_buf] >>
  `!scopes. not_local_ptr cenv scopes idx /\ not_local_ptr cenv scopes nv` by metis_tac[] >>
  `!x. not_fresh_at caller x ==> x <> idx /\ x <> nv` by metis_tac[] >>
  qmatch_asmsub_abbrev_tac `eval_stmts cx stmts ei = (r,ee)` >>
  `cenv_top_ext cenv bc ei.scopes` by simp[Abbr `ei`, evaluation_state_fn_updates] >>
  drule_all immutable_body_finish_mem >> strip_tac >>
  qexistsl_tac [`sc`, `rest`] >> simp[] >> metis_tac[]
QED
Resume immutable_prepared_one_round_mem[exit]:
  rpt strip_tac >> qpat_x_assum `!gs r ee. _` drule >> strip_tac >>
  gvs[stmt_res_ok_def] >>
  gvs[stmt_exit_def, expr_exit_def, evaluation_state_fn_updates] >>
  Cases_on `rr` >> gvs[expr_exit_def]
QED
Finalise immutable_prepared_one_round_mem

Theorem immutable_prepared_loop_outcome_mem:
  lookup_block cond func.fn_blocks =
    SOME <|bb_label := cond; bb_instructions :=
      [mk_inst j1 EQ [Var idx; lvo] [dv];
       mk_inst j2 JNZ [Var dv; Label exit; Label bod] []]|> /\
  lookup_block incr func.fn_blocks =
    SOME <|bb_label := incr; bb_instructions :=
      [mk_inst i1 ADD [Var idx; Lit 1w] [nv];
       mk_inst i2 ASSIGN [Var nv] [idx];
       mk_inst i3 JMP [Label cond] []]|> /\
  stmts_env bc (InLoop exit incr) ty stmts sb0 = (bc',sb1) /\
  fn_has_code sb0 sb1 func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved bc sb0 /\ ~block_is_terminated sb0 /\
  (~block_is_terminated sb1 ==>
    sj.cs_blocks = sb1.cs_blocks /\ sj.cs_current_bb = sb1.cs_current_bb /\
    sj.cs_current_insts = sb1.cs_current_insts ++
      [mk_inst sb1.cs_next_id JMP [Label incr] []] /\ fn_has_code sb1 sj func) /\
  (!scopes. not_local_ptr cenv scopes idx /\ not_local_ptr cenv scopes nv /\
    not_local_ptr cenv scopes dv) /\
  dv <> idx /\ dv <> p /\ p <> idx /\ p <> nv /\
  (!x. not_fresh_at caller x ==> x <> dv /\ x <> idx /\ x <> nv) /\
  caller.cs_next_var <= cut.cs_next_var /\ cut.cs_next_var <= sb0.cs_next_var /\
  not_fresh_at cut idx /\ not_fresh_at cut p /\
  (!x. not_fresh_at cut x ==> not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep) /\
  LENGTH vs < dimword (:256) /\
  (!k ei t. k <= LENGTH vs /\
    array_round_inv d ctx func cenv cx P vs id idx (Lit (n2w off)) (n2w off)
      p dst sz ainst cond caller orig k ei t ==>
    eval_operand lvo t = SOME (n2w (LENGTH vs))) /\
  (!k ei live. k < LENGTH vs /\
    array_round_inv d ctx func cenv cx P vs id idx (Lit (n2w off)) (n2w off)
      p dst sz ainst bod caller orig k ei live ==>
    ?s_body. s_body.vs_current_bb = sb0.cs_current_bb /\
      s_body.vs_inst_idx = LENGTH sb0.cs_current_insts /\ ~s_body.vs_halted /\
      stmt_state_rel ctx func bc cx
        (ei with scopes := (FEMPTY |+ (id,
          <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: ei.scopes) s_body /\
      ret_pc_ok bc sb0 s_body /\ gas_marked_path T ctx func live 0 (OK s_body) /\
      s_body.vs_allocas = live.vs_allocas /\ s_body.vs_alloca_next = live.vs_alloca_next /\
      alloca_history func s_body /\ return_buf_frame d bc sb0 s_body /\
      (!x. not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep ==>
        lookup_var x s_body = lookup_var x live)) /\
  (!k ei. k < LENGTH vs /\ P ei /\ lookup_scopes id ei.scopes = NONE ==>
    cenv_top_ext cenv bc ((FEMPTY |+ (id,
      <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: ei.scopes) /\
    stmt_frag_mem d ctx func cx (InLoop exit incr) RetQ bc
      (stmts_env bc (InLoop exit incr) ty stmts) (eval_stmts cx stmts)
      (ei with scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: ei.scopes) /\
    (!gs r ee. eval_stmts cx stmts
      (ei with <|scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: ei.scopes;
        gas_obs := gs|>) = (r,ee) ==>
      stmt_res_ok (InLoop exit incr) r /\
      ?sc rest. ee.scopes = sc :: rest /\
        (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
        ((r = INL () \/ r = INR ContinueException) ==>
          P (ee with scopes := rest) /\ lookup_scopes id rest = NONE))) ==>
  !k es s. k <= LENGTH vs /\
    array_round_inv d ctx func cenv cx P vs id idx (Lit (n2w off)) (n2w off)
      p dst sz ainst cond caller orig k es s /\
    gas_admissible (eval_for cx tv id stmts (MAP Value (DROP k vs))) ok es ==>
    gas_outcome T (cx_tops cx) (ctx,func)
      (eval_for cx tv id stmts (MAP Value (DROP k vs))) (es,s)
      (\res ee t. res = INL () /\
        array_round_done d ctx func cenv cx caller orig exit ee t)
      (\res ee rr. ?ex. res = INR ex /\
        !tail. stmt_exit RetQ (ee with gas_obs := tail) (INR ex) rr)
Proof
  strip_tac >>
  ho_match_mp_tac stmtSimForRoundsTheory.eval_for_value_rounds >>
  conj_tac >- suspend "round" >> suspend "last"
QED

Resume immutable_prepared_loop_outcome_mem[round]:
  rpt strip_tac >>
  `P es /\ lookup_scopes id es.scopes = NONE` by
    fs[array_round_inv_def, array_loop_inv_def] >>
  qpat_x_assum `!k ei. _` drule_all >> strip_tac >>
  `k <= LENGTH vs` by simp[] >>
  `eval_operand lvo s = SOME (n2w (LENGTH vs))` by
    (qpat_x_assum `!k ei t. _` drule_all >> simp[]) >>
  qpat_x_assum `!k ei live. _`
    (qspecl_then [`k`, `es`] mp_tac) >> simp[] >> strip_tac >>
  drule_all immutable_prepared_one_round_mem >> simp[]
QED

Resume immutable_prepared_loop_outcome_mem[last]:
  rpt strip_tac >>
  `eval_operand lvo s = SOME (n2w (LENGTH vs))` by
    (qpat_x_assum `!k ei t. _ ==> eval_operand lvo t = _`
       (qspecl_then [`LENGTH vs`, `es`, `s`] mp_tac) >> simp[]) >>
  `array_loop_inv ctx func cenv cx P vs id idx (Lit (n2w off)) (n2w off)
    p dst sz ainst cond caller (LENGTH vs) es s /\ alloca_history func s` by
    fs[array_round_inv_def, array_round_frame_def] >>
  `not_local_ptr cenv es.scopes dv` by metis_tac[] >>
  drule_all (immutable_condition_boundary_mem |>
    Q.INST [`saved_arr_base` |-> `Lit (n2w off)`] |> SRULE []) >>
  simp[] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_marked_path T ctx func s 0 (OK t)` >>
  qexists_tac `t` >> simp[] >>
  `array_round_frame d func cenv caller orig t` by
    (irule array_round_frame_transport >> simp[] >> qexists_tac `s` >>
     fs[array_round_inv_def, Abbr `t`, lookup_var_def, jump_to_def, update_var_def,
       FLOOKUP_UPDATE] >> metis_tac[]) >>
  fs[array_round_done_def, array_loop_inv_def, state_rel_gas_obs]
QED
Finalise immutable_prepared_loop_outcome_mem

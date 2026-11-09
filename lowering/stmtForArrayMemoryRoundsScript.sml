Theory stmtForArrayMemoryRounds
Ancestors
  stmtForArrayControlMemory stmtForArrayMemoryRoundSupport
  stmtSimForArrayLoop stmtSimProps exprLoweringProps bodyMemoryDefs loweringPosts compileEnv
  venomState allocaHistory fragGasMode fragGasPathMem finite_map list arithmetic
  stmtForArrayMemoryCopy stmtForArrayMemoryBodyEntry rich_list emitHelper venomInst
  bodyDeclMemoryCounted stmtLowering venomMemDefs stmtSimDefs gasContext vyperState
Libs
  monadsyntax

Definition array_round_frame_def:
  array_round_frame d func cenv caller orig s <=>
    return_buf_frame d cenv caller s /\ alloca_history func s /\
    orig.vs_alloca_next <= s.vs_alloca_next /\
    (!x w. not_fresh_at caller x /\ lookup_var x orig = SOME w ==>
      lookup_var x s = SOME w) /\
    (!aid b. FLOOKUP orig.vs_allocas aid = SOME b ==>
      FLOOKUP s.vs_allocas aid = SOME b)
End

Definition array_round_inv_def:
  array_round_inv d ctx func cenv cx P vs id idx saved_base base p dst sz
    ainst cond caller orig k es s <=>
    array_loop_inv ctx func cenv cx P vs id idx saved_base base p dst sz
      ainst cond caller k es s /\
    array_round_frame d func cenv caller orig s
End

Definition array_round_done_def:
  array_round_done d ctx func cenv cx caller orig exit es s <=>
    s.vs_current_bb = exit /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
    stmt_state_rel ctx func cenv cx es s /\ ret_pc_ok cenv caller s /\
    array_round_frame d func cenv caller orig s
End

Theorem array_round_frame_transport:
  array_round_frame d func cenv caller orig s /\
  alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
  (!x w. not_fresh_at caller x /\ lookup_var x s = SOME w ==>
    lookup_var x t = SOME w) /\
  (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
    FLOOKUP t.vs_allocas aid = SOME b) ==>
  array_round_frame d func cenv caller orig t
Proof
  rw[array_round_frame_def]
  >- (irule return_buf_frame_frame >>
      qexistsl_tac [`cenv`, `s`, `caller`] >> simp[]) >>
  metis_tac[LESS_EQ_TRANS]
QED

Theorem array_round_last:
  !d ctx func cenv cx P vs id idx saved_base base p dst sz ainst cond caller
   orig es s dv j1 j2 exit stmts_lbl.
  lookup_block cond func.fn_blocks =
    SOME <|bb_label := cond; bb_instructions :=
      [mk_inst j1 EQ [Var idx; Lit (n2w (LENGTH vs))] [dv];
       mk_inst j2 JNZ [Var dv; Label exit; Label stmts_lbl] []]|> /\
  array_round_inv d ctx func cenv cx P vs id idx saved_base base p dst sz
    ainst cond caller orig (LENGTH vs) es s /\
  LENGTH vs < dimword (:256) /\
  not_local_ptr cenv es.scopes dv /\ dv <> idx /\ dv <> p /\
  (!x. saved_base = Var x ==> x <> dv) /\
  (!x. not_fresh_at caller x ==> x <> dv) /\
  fn_inst_ids_distinct func ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
      array_round_done d ctx func cenv cx caller orig exit
        (es with gas_obs := []) t
Proof
  rw[array_round_inv_def] >>
  `alloca_history func s` by fs[array_round_frame_def] >>
  drule array_condition_boundary_mem >>
  simp[Excl "typed_copy_lookup_var_jump"] >>
  disch_then drule >> simp[Excl "typed_copy_lookup_var_jump"] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_path_mem ctx func s 0 (OK t)` >>
  qexists_tac `t` >> conj_tac
  >- simp[gas_marked_path_def] >>
  `array_round_frame d func cenv caller orig t` by
    (irule array_round_frame_transport >> simp[] >> qexists_tac `s` >> simp[] >>
     rpt strip_tac >> fs[Abbr `t`, lookup_var_def, jump_to_def, update_var_def,
                           FLOOKUP_UPDATE] >> metis_tac[]) >>
  fs[array_round_done_def, array_loop_inv_def, state_rel_gas_obs]
QED

Theorem array_round_increment:
  !d ctx func cenv cx P vs id idx saved_base base p dst sz ainst cond caller
   orig k es s incr nv i1 i2 i3.
  lookup_block incr func.fn_blocks =
    SOME <|bb_label := incr; bb_instructions :=
      [mk_inst i1 ADD [Var idx; Lit 1w] [nv];
       mk_inst i2 ASSIGN [Var nv] [idx];
       mk_inst i3 JMP [Label cond] []]|> /\
  array_round_inv d ctx func cenv cx P vs id idx saved_base base p dst sz
    ainst incr caller orig k es s /\ k < LENGTH vs /\
  not_local_ptr cenv es.scopes idx /\ not_local_ptr cenv es.scopes nv /\
  p <> idx /\ p <> nv /\
  (!x. saved_base = Var x ==> x <> idx /\ x <> nv) /\
  (!x. not_fresh_at caller x ==> x <> idx /\ x <> nv) /\
  fn_inst_ids_distinct func ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
      array_round_inv d ctx func cenv cx P vs id idx saved_base base p dst sz
        ainst cond caller orig (SUC k) es t
Proof
  rw[array_round_inv_def] >>
  `alloca_history func s` by fs[array_round_frame_def] >>
  drule array_increment_boundary_mem >>
  simp[Excl "typed_copy_lookup_var_jump"] >>
  disch_then drule >> simp[Excl "typed_copy_lookup_var_jump"] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_path_mem ctx func s 0 (OK t)` >>
  qexists_tac `t` >> simp[gas_marked_path_def, ADD1] >>
  irule array_round_frame_transport >> simp[] >> qexists_tac `s` >> simp[] >>
  rpt strip_tac >> fs[Abbr `t`, lookup_var_def, jump_to_def, update_var_def,
                           FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem array_round_break:
  stmt_lands (InLoop exit incr) sb (INR BreakException) s /\
  ~s.vs_halted /\ stmt_state_rel ctx func cenv cx es s /\
  ret_pc_ok cenv caller s /\ array_round_frame d func cenv caller orig s ==>
  array_round_done d ctx func cenv cx caller orig exit es s
Proof
  simp[stmt_lands_def, array_round_done_def]
QED

Theorem array_round_postbody_entry:
  !d ctx func cenv cx P vs id idx saved_base base p dst sz ainst caller
   orig k es s exit incr sb sj r.
  stmt_lands (InLoop exit incr) sb r s /\
  (r = INL () \/ r = INR ContinueException) /\ ~s.vs_halted /\
  (r = INL () ==> ~block_is_terminated sb) /\
  (~block_is_terminated sb ==>
    sj.cs_blocks = sb.cs_blocks /\ sj.cs_current_bb = sb.cs_current_bb /\
    sj.cs_current_insts = sb.cs_current_insts ++
      [mk_inst sb.cs_next_id JMP [Label incr] []] /\ fn_has_code sb sj func) /\
  array_loop_inv ctx func cenv cx P vs id idx saved_base base p dst sz
    ainst incr caller k es (jump_to incr s) /\
  array_round_frame d func cenv caller orig s ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
    array_round_inv d ctx func cenv cx P vs id idx saved_base base p dst sz
      ainst incr caller orig k es t
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  Cases_on `r = INL ()`
  >- (qexists_tac `jump_to incr s` >> conj_tac
      >- (fs[stmt_lands_def] >> simp[gas_marked_path_def] >>
          irule emit_jump_zero_path_mem >> simp[] >>
          qexistsl_tac [`sb`, `sj`] >> simp[]) >>
      simp[array_round_inv_def] >>
      fs[array_round_frame_def, return_buf_frame_jump_to, jump_to_def,
         lookup_var_def, alloca_history_def]) >>
  qexists_tac `s` >> conj_tac
  >- (simp[gas_marked_path_def] >> irule (cj 1 gas_path_mem_rules) >> simp[]) >>
  fs[stmt_lands_def, array_round_inv_def, array_loop_inv_def,
     stmt_state_rel_jump_to, ret_pc_ok_jump_to, jump_to_def,
     eval_operand_def, lookup_var_def]
QED

Theorem array_round_live:
  !d ctx func cenv cx P vs id idx saved_base base p dst sz ainst cond caller
   orig k es s dv j1 j2 exit stmts_lbl.
  lookup_block cond func.fn_blocks =
    SOME <|bb_label := cond; bb_instructions :=
      [mk_inst j1 EQ [Var idx; Lit (n2w (LENGTH vs))] [dv];
       mk_inst j2 JNZ [Var dv; Label exit; Label stmts_lbl] []]|> /\
  array_round_inv d ctx func cenv cx P vs id idx saved_base base p dst sz
    ainst cond caller orig k es s /\ k < LENGTH vs /\
  LENGTH vs < dimword (:256) /\
  not_local_ptr cenv es.scopes dv /\ dv <> idx /\ dv <> p /\
  (!x. saved_base = Var x ==> x <> dv) /\
  (!x. not_fresh_at caller x ==> x <> dv) /\
  fn_inst_ids_distinct func ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
      array_round_inv d ctx func cenv cx P vs id idx saved_base base p dst sz
        ainst stmts_lbl caller orig k es t
Proof
  rw[array_round_inv_def] >>
  `alloca_history func s` by fs[array_round_frame_def] >>
  drule array_condition_boundary_mem >>
  simp[Excl "typed_copy_lookup_var_jump"] >>
  disch_then drule >> simp[Excl "typed_copy_lookup_var_jump"] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_path_mem ctx func s 0 (OK t)` >>
  qexists_tac `t` >> simp[gas_marked_path_def] >>
  irule array_round_frame_transport >> simp[] >> qexists_tac `s` >> simp[] >>
  rpt strip_tac >> fs[Abbr `t`, lookup_var_def, jump_to_def, update_var_def,
                           FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem array_iter_copy_no_gas[local]:
  compile_iter_elem_copy ce src dst stride LocMemory F ty ty sa = ((),sb) ==>
  EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)
Proof
  Cases_on `is_word_type ty`
  >- (gvs[compile_iter_elem_copy_def, emit_op_def, emit_void_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def,
          fresh_id_def, fresh_var_def, emit_def, LET_THM] >>
      strip_tac >> gvs[emitted_insts_def, mk_inst_def] >>
      rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]) >>
  simp[compile_iter_elem_copy_def] >> strip_tac >>
  irule compile_store_memory_same_no_gas >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem array_round_copy_entry:
  !ctx func cenv bc cx es s id p sz dst ainst tv v et tenv sa sb0
   idx saved_base arr_base k stride ov ep j3 j4 bb.
  compile_iter_elem_copy cenv (Var ep) (Var p) stride LocMemory F et et sa = ((),sb0) /\
  stride = type_memory_size tv /\ type_memory_bytes cenv et = stride /\
  evaluate_type tenv et = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  val_in_memory tv v (w2n arr_base + k * stride) s.vs_memory /\
  w2n arr_base + k * stride < dimword (:256) /\ stride + 64 < dimword (:256) /\
  w2n arr_base + k * stride + stride <= s.vs_alloca_next /\
  w2n dst + stride <= s.vs_alloca_next /\
  stmt_state_rel ctx func cenv cx es s /\
  cenv_top_ext cenv bc (FEMPTY :: es.scopes) /\ local_ptrs_reserved bc sa /\
  lookup_scopes id es.scopes = NONE /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) /\
  not_local_ptr bc (FEMPTY :: es.scopes) p /\
  not_local_ptr cenv es.scopes ov /\ not_local_ptr cenv es.scopes ep /\
  lookup_var idx s = SOME (n2w k) /\ eval_operand saved_base s = SOME arr_base /\
  lookup_var p s = SOME dst /\ p <> ov /\ p <> ep /\
  (!x. saved_base = Var x ==> x <> ov) /\ not_fresh_at sa ep /\ not_fresh_at sa p /\
  MEM ainst (fn_insts func) /\ ainst.inst_opcode = ALLOCA /\
  ainst.inst_outputs = [p] /\ fn_inst_ids_distinct func /\
  FLOOKUP s.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\ stride <= sz /\
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  sb0.cs_current_insts =
    [mk_inst j3 MUL [Var idx; Lit (n2w stride)] [ov];
     mk_inst j4 ADD [saved_base; Var ov] [ep]] ++ emitted_insts sa sb0 /\
  isPREFIX sb0.cs_current_insts bb.bb_instructions /\
  alloca_history func s /\ alloca_inv s ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\ alloca_history func t /\
    stmt_state_rel ctx func bc cx
      (es with scopes :=
        (FEMPTY |+ (id, <|assignable := F; type := tv; value := v; popped := []|>))
          :: es.scopes) t /\
    ~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
    t.vs_inst_idx = LENGTH sb0.cs_current_insts /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (!x. not_fresh_at sa x /\ x <> ov /\ x <> ep ==>
      lookup_var x t = lookup_var x s)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all array_for_body_entry_run >>
  disch_then (qspecl_then [`j3`, `j4`] strip_assume_tac) >>
  `run_inst_seq_mem_ok sb0.cs_current_insts s` by
    (`!x. x = ep \/ x = p ==> not_fresh_at sa x` by metis_tac[] >>
     drule_all array_body_prefix_mem_ok >>
     disch_then (qspecl_then [`j4`, `j3`] mp_tac) >> simp[]) >>
  `run_inst_seq sb0.cs_current_insts s = OK t` by gvs[] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    sb0.cs_current_insts` by simp[mk_inst_def, is_terminator_def] >>
  `EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb0)` by
    (irule array_iter_copy_no_gas >> goal_assum (drule_at Any)) >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) sb0.cs_current_insts) = 0` by
    (simp[mk_inst_def] >> fs[EVERY_FILTER, FILTER_EQ_NIL, EVERY_MEM]) >>
  `isPREFIX sb0.cs_current_insts (DROP s.vs_inst_idx bb.bb_instructions)`
    by (qpat_assum `s.vs_inst_idx = 0` (fn th => rewrite_tac[th, DROP_0]) >>
        first_assum ACCEPT_TAC) >>
  drule_all array_prefix_counted_history >> simp[] >> strip_tac >>
  qexists_tac `t with vs_inst_idx := LENGTH sb0.cs_current_insts` >>
  simp[gas_marked_path_def, stmt_state_rel_inst_idx] >>
  fs[venom_state_component_equality, lookup_var_def]
QED

(* Compiler packaging for the live copy boundary. *)
Theorem array_code_copy_entry_mem:
  array_for_code func cenv bc ty stmts id et tv (LENGTH vs) stride saved_base
    p sz ainst idx dv ov ep nv cond exit stmts_lbl incr
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj /\
  array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst stmts_lbl caller k es s /\
  k < LENGTH vs /\ evaluate_type (get_tenv cx) et = SOME tv /\
  value_has_type tv (EL k vs) /\ val_wf tv (EL k vs) /\
  val_in_memory tv (EL k vs) (w2n arr_base + k * stride) s.vs_memory /\
  w2n arr_base + k * stride < dimword (:256) /\
  w2n arr_base + LENGTH vs * stride <= s.vs_alloca_next /\
  not_local_ptr bc (FEMPTY :: es.scopes) p /\
  lookup_block stmts_lbl func.fn_blocks = SOME bb /\
  isPREFIX sb0.cs_current_insts bb.bb_instructions /\ alloca_history func s ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\ alloca_history func t /\
    stmt_state_rel ctx func bc cx
      (es with scopes :=
        (FEMPTY |+ (id, <|assignable := F; type := tv; value := EL k vs; popped := []|>))
          :: es.scopes) t /\
    ~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
    t.vs_inst_idx = LENGTH sb0.cs_current_insts /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (!x. not_fresh_at sa x /\ x <> ov /\ x <> ep ==>
      lookup_var x t = lookup_var x s)
Proof
  strip_tac >>
  `cenv_top_ext cenv bc (FEMPTY :: es.scopes)` by
    (irule array_for_code_scope_frame >> goal_assum (drule_at Any) >>
     fs[array_loop_inv_def]) >>
  `alloca_inv s` by fs[array_loop_inv_def, stmt_state_rel_def] >>
  `w2n dst + sz <= s.vs_alloca_next` by
    (fs[array_loop_inv_def, alloca_inv_def, alloca_next_valid_def] >>
     qpat_x_assum `!aid base sz. _` drule >> simp[ADD_COMM]) >>
  `k * stride + stride <= LENGTH vs * stride` by
    (`k + 1 <= LENGTH vs` by simp[] >>
     ` (k + 1) * stride <= LENGTH vs * stride` by
       simp[LE_MULT_RCANCEL] >>
     qpat_x_assum `(_ + 1) * stride <= _` mp_tac >>
     pure_rewrite_tac[RIGHT_ADD_DISTRIB, MULT_LEFT_1] >> decide_tac) >>
  drule array_for_code_prefix >> strip_tac >>
  qhdtm_assum `array_for_code` mp_tac >>
  pure_rewrite_tac[array_for_code_def] >> strip_tac >>
  qhdtm_assum `array_loop_inv`
    (strip_assume_tac o PURE_REWRITE_RULE [array_loop_inv_def]) >>
  `w2n arr_base + k * stride + stride <= s.vs_alloca_next` by decide_tac >>
  `w2n dst + stride <= s.vs_alloca_next` by decide_tac >>
  `not_local_ptr cenv es.scopes ov /\ not_local_ptr cenv es.scopes ep` by
    (qpat_x_assum `!scs. _` (qspec_then `es.scopes` strip_assume_tac) >> simp[]) >>
  `p <> ov /\ p <> ep /\ (!x. saved_base = Var x ==> x <> ov)` by
    (fs[ALL_DISTINCT] >> metis_tac[]) >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  `type_memory_bytes cenv et = stride` by simp[] >>
  drule_all array_round_copy_entry >> strip_tac >>
  qexists_tac `t` >> simp[]
QED

Definition array_body_post_mem_def:
  array_body_post_mem d ctx func cx lctx bc bc' sb0 sb1 s_body r ee t <=>
    ?ce. stmt_lands lctx sb1 r t /\ ~t.vs_halted /\
      (r = INL () ==> ~block_is_terminated sb1 /\ ce = bc') /\
      cenv_top_ext bc ce ee.scopes /\ stmt_state_rel ctx func ce cx ee t /\
      (!x w. not_fresh_at sb0 x /\ lookup_var x s_body = SOME w ==>
        lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s_body.vs_allocas aid = SOME b ==>
        FLOOKUP t.vs_allocas aid = SOME b) /\
      return_buf_frame d ce sb1 t /\ alloca_history func t /\
      s_body.vs_alloca_next <= t.vs_alloca_next
End

Theorem array_code_body_outcome_mem:
  array_for_code func cenv bc ty stmts id et tv (LENGTH vs) stride saved_base
    p sz ainst idx dv ov ep nv cond exit stmts_lbl incr
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj /\
  array_round_inv d ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst stmts_lbl caller orig k es s /\
  k < LENGTH vs /\ evaluate_type (get_tenv cx) et = SOME tv /\
  value_has_type tv (EL k vs) /\ val_wf tv (EL k vs) /\
  val_in_memory tv (EL k vs) (w2n arr_base + k * stride) s.vs_memory /\
  w2n arr_base + k * stride < dimword (:256) /\
  w2n arr_base + LENGTH vs * stride <= s.vs_alloca_next /\
  not_local_ptr bc (FEMPTY :: es.scopes) p /\
  lookup_block stmts_lbl func.fn_blocks = SOME bb /\
  isPREFIX sb0.cs_current_insts bb.bb_instructions /\
  caller.cs_next_var <= sa.cs_next_var /\ sa.cs_next_var <= sb0.cs_next_var /\
  (!x. not_fresh_at caller x ==> x <> ov /\ x <> ep) /\
  ei = es with scopes :=
    (FEMPTY |+ (id, <|assignable := F; type := tv; value := EL k vs; popped := []|>))
      :: es.scopes /\
  stmt_frag_mem d ctx func cx (InLoop exit incr) RetQ bc
    (stmts_env bc (InLoop exit incr) ty stmts) (eval_stmts cx stmts) ei /\
  gas_admissible (eval_stmts cx stmts) (stmt_res_ok (InLoop exit incr)) ei ==>
  ?s_body. gas_marked_path T ctx func s 0 (OK s_body) /\
    gas_outcome T (cx_tops cx) (ctx,func) (eval_stmts cx stmts) (ei,s_body)
      (array_body_post_mem d ctx func cx (InLoop exit incr) bc
        (FST (stmts_env bc (InLoop exit incr) ty stmts sb0)) sb0 sb1 s_body)
      (\r ee rr. !tail. stmt_exit RetQ (ee with gas_obs := tail) r rr) /\
    s_body.vs_allocas = s.vs_allocas /\ s_body.vs_alloca_next = s.vs_alloca_next /\
    (!x. not_fresh_at sa x /\ x <> ov /\ x <> ep ==>
      lookup_var x s_body = lookup_var x s)
Proof
  strip_tac >>
  `array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst stmts_lbl caller k es s /\ alloca_history func s /\
    return_buf_frame d cenv caller s` by
    fs[array_round_inv_def, array_round_frame_def] >>
  drule_all array_code_copy_entry_mem >> strip_tac >>
  `!x w. not_fresh_at caller x /\ lookup_var x s = SOME w ==>
    lookup_var x t = SOME w` by
    (rpt strip_tac >>
     `not_fresh_at sa x` by (fs[not_fresh_at_def] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
     metis_tac[]) >>
  drule array_for_code_stmts >> strip_tac >>
  `bc.ce_return_pc = cenv.ce_return_pc /\ bc.ce_return_buf = cenv.ce_return_buf` by
    (qhdtm_assum `array_for_code` mp_tac >>
     pure_rewrite_tac[array_for_code_def] >> strip_tac >>
     qpat_x_assum `_ = cenv` (mp_tac o AP_TERM
       ``\ce:compile_env. (ce.ce_return_pc,ce.ce_return_buf)``) >> simp[]) >>
  `ret_pc_ok bc sb0 t` by
    (irule ret_pc_ok_frame >> qexistsl_tac [`cenv`, `s`, `caller`] >>
     fs[array_loop_inv_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `return_buf_frame d bc sb0 t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`, `s`, `caller`] >>
     simp[] >> metis_tac[LESS_EQ_TRANS]) >>
  `stmts_env bc (InLoop exit incr) ty stmts sb0 =
     (FST (stmts_env bc (InLoop exit incr) ty stmts sb0),sb1)` by
    (Cases_on `stmts_env bc (InLoop exit incr) ty stmts sb0` >>
     gvs[compile_stmts_env]) >>
  `fn_inst_ids_distinct func /\ s.vs_current_bb = sb0.cs_current_bb` by
    fs[array_for_code_def, array_loop_inv_def] >>
  qexists_tac `t` >> simp[] >>
  qhdtm_x_assum `stmt_frag_mem` mp_tac >>
  rewrite_tac[stmt_frag_mem_def] >>
  disch_then (qspecl_then [`sb0`, `sb1`, `t`,
    `FST (stmts_env bc (InLoop exit incr) ty stmts sb0)`] mp_tac) >>
  simp[GSYM array_body_post_mem_def, SF ETA_ss]
QED

Theorem array_body_round_restore_mem:
  array_round_inv d ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst lbl caller orig k es s /\
  array_body_post_mem d ctx func cx (InLoop exit incr) bc bc' sb0 sb1 s_body r es2 t /\
  cenv_top_ext cenv bc ei.scopes /\ bc.ce_return_buf = cenv.ce_return_buf /\
  eval_stmts cx stmts ei = (r,es2) /\ es2.scopes = sc :: rest /\
  (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
  ((r = INL () \/ r = INR ContinueException) ==>
    P (es2 with scopes := rest) /\ lookup_scopes id rest = NONE) /\
  caller.cs_next_var <= sa.cs_next_var /\ sa.cs_next_var <= sb0.cs_next_var /\
  (!x. not_fresh_at caller x ==> x <> ov /\ x <> ep) /\
  not_fresh_at sa idx /\ idx <> ov /\ idx <> ep /\
  not_fresh_at sa p /\ p <> ov /\ p <> ep /\
  (!x. saved_base = Var x ==> not_fresh_at sa x /\ x <> ov /\ x <> ep) /\
  (!l. saved_base <> Label l) /\
  s_body.vs_allocas = s.vs_allocas /\ s_body.vs_alloca_next = s.vs_alloca_next /\
  (!x. not_fresh_at sa x /\ x <> ov /\ x <> ep ==>
    lookup_var x s_body = lookup_var x s) ==>
  array_round_frame d func cenv caller orig t /\ ret_pc_ok cenv caller t /\
  stmt_lands (InLoop exit incr) sb1 r t /\ ~t.vs_halted /\
  (r = INL () ==> ~block_is_terminated sb1) /\
  ((r = INL () \/ r = INR ContinueException) ==>
    array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
      ainst incr caller k (es2 with scopes := rest) (jump_to incr t)) /\
  (r = INR BreakException ==>
    array_round_done d ctx func cenv cx caller orig exit (es2 with scopes := rest) t)
Proof
  strip_tac >>
  `cenv.ce_return_buf = bc.ce_return_buf` by simp[] >>
  drule_all (PURE_REWRITE_RULE [GSYM array_body_post_mem_def]
    array_body_mem_post_projection) >> strip_tac >>
  `!x w. not_fresh_at sa x /\ x <> ov /\ x <> ep /\ lookup_var x s = SOME w ==>
    lookup_var x t = SOME w` by
    (rpt strip_tac >>
     `not_fresh_at sb0 x` by (fs[not_fresh_at_def] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
     metis_tac[]) >>
  `!x w. not_fresh_at caller x /\ lookup_var x s = SOME w ==>
    lookup_var x t = SOME w` by
    (rpt strip_tac >>
     `not_fresh_at sa x` by (fs[not_fresh_at_def] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
     metis_tac[]) >>
  `array_round_frame d func cenv caller orig t` by
    (irule array_round_frame_transport >> simp[] >> qexists_tac `s` >>
     fs[array_round_inv_def] >> metis_tac[]) >>
  `ret_pc_ok cenv caller t` by
    (irule ret_pc_ok_frame >> qexistsl_tac [`cenv`, `s`, `caller`] >>
     fs[array_round_inv_def, array_loop_inv_def]) >>
  `lookup_var idx t = SOME (n2w k) /\ lookup_var p t = SOME dst /\
    FLOOKUP t.vs_allocas ainst.inst_id = SOME (w2n dst,sz)` by
    (fs[array_round_inv_def, array_loop_inv_def] >> metis_tac[]) >>
  `eval_operand saved_base t = SOME arr_base` by
    (irule array_saved_operand_frame >> simp[] >> qexists_tac `s` >>
     fs[array_round_inv_def, array_loop_inv_def] >>
     rpt strip_tac >>
     Cases_on `lookup_var x s` >> fs[eval_operand_def] >> metis_tac[]) >>
  simp[] >> conj_tac
  >- (strip_tac >>
      fs[array_round_inv_def, array_loop_inv_def, stmt_state_rel_jump_to,
         ret_pc_ok_jump_to, jump_to_def, eval_operand_def, lookup_var_def]) >>
  strip_tac >> irule array_round_break >> simp[] >>
  qexistsl_tac [`incr`, `sb1`] >> gvs[]
QED

(* The normal body continuation includes both the scope restoration and the
   optional fallthrough jump followed by the counted increment. *)
Theorem array_code_body_finish_mem:
  array_for_code func cenv bc ty stmts id et tv (LENGTH vs) stride saved_base
    p sz ainst idx dv ov ep nv cond exit stmts_lbl incr
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj /\
  array_round_inv d ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst stmts_lbl caller orig k es s /\
  array_body_post_mem d ctx func cx (InLoop exit incr) bc bc' sb0 sb1 s_body r es2 t /\
  cenv_top_ext cenv bc ei.scopes /\
  eval_stmts cx stmts ei = (r,es2) /\ es2.scopes = sc :: rest /\
  (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
  ((r = INL () \/ r = INR ContinueException) ==>
    P (es2 with scopes := rest) /\ lookup_scopes id rest = NONE) /\
  caller.cs_next_var <= sa.cs_next_var /\ sa.cs_next_var <= sb0.cs_next_var /\
  (!x. not_fresh_at caller x ==> x <> idx /\ x <> dv /\ x <> ov /\ x <> ep /\ x <> nv) /\
  (!l. saved_base <> Label l) /\ k < LENGTH vs /\
  s_body.vs_allocas = s.vs_allocas /\ s_body.vs_alloca_next = s.vs_alloca_next /\
  (!x. not_fresh_at sa x /\ x <> ov /\ x <> ep ==>
    lookup_var x s_body = lookup_var x s) ==>
  ?b u.
    (case r of INL x => INL F
       | INR e => if e = ContinueException then INL F
                  else if e = BreakException then INL T else INR e) = INL b /\
    gas_marked_path T ctx func t 0 (OK u) /\
    (b ==> array_round_done d ctx func cenv cx caller orig exit
      (es2 with scopes := rest) u) /\
    (~b ==> array_round_inv d ctx func cenv cx P vs id idx saved_base arr_base p dst sz
      ainst cond caller orig (SUC k) (es2 with scopes := rest) u)
Proof
  strip_tac >>
  `bc.ce_return_buf = cenv.ce_return_buf` by
    (qhdtm_assum `array_for_code` mp_tac >>
     pure_rewrite_tac[array_for_code_def] >> strip_tac >>
     qpat_x_assum `_ = cenv` (mp_tac o AP_TERM
       ``\ce:compile_env. ce.ce_return_buf``) >> simp[]) >>
  `not_fresh_at sa idx /\ not_fresh_at sa p /\
    idx <> ov /\ idx <> ep /\ p <> ov /\ p <> ep /\ p <> idx /\ p <> nv /\
    (!x. saved_base = Var x ==> not_fresh_at sa x /\ x <> ov /\ x <> ep) /\
    (!x. saved_base = Var x ==> x <> idx /\ x <> nv) /\
    (!scs. not_local_ptr cenv scs idx /\ not_local_ptr cenv scs nv) /\
    fn_inst_ids_distinct func` by
    (fs[array_for_code_def, ALL_DISTINCT] >> metis_tac[]) >>
  `!x. not_fresh_at caller x ==> x <> ov /\ x <> ep` by metis_tac[] >>
  drule_all array_body_round_restore_mem >> strip_tac >>
  Cases_on `r = INR BreakException`
  >- (qexistsl_tac [`T`, `t`] >> simp[gas_marked_path_def] >>
      irule (cj 1 gas_path_mem_rules) >> simp[]) >>
  `r = INL () \/ r = INR ContinueException` by fs[stmt_lands_def] >>
  `~block_is_terminated sb1 ==>
    sj.cs_blocks = sb1.cs_blocks /\ sj.cs_current_bb = sb1.cs_current_bb /\
    sj.cs_current_insts = sb1.cs_current_insts ++
      [mk_inst sb1.cs_next_id JMP [Label incr] []] /\ fn_has_code sb1 sj func` by
    fs[array_for_code_def] >>
  `array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst incr caller k (es2 with scopes := rest) (jump_to incr t)` by simp[] >>
  `?u. gas_marked_path T ctx func t 0 (OK u) /\
    array_round_inv d ctx func cenv cx P vs id idx saved_base arr_base p dst sz
      ainst incr caller orig k (es2 with scopes := rest) u` by
    (irule array_round_postbody_entry >> simp[] >>
     qexistsl_tac [`exit`, `r`, `sb1`, `sj`] >> simp[]) >>
  rename1 `gas_marked_path T ctx func t 0 (OK u)` >>
  qpat_x_assum `!scs. _` (qspec_then `rest` strip_assume_tac) >>
  `!x. not_fresh_at caller x ==> x <> idx /\ x <> nv` by metis_tac[] >>
  drule array_for_code_increment >> strip_tac >>
  drule array_round_increment >> simp[] >>
  disch_then drule >> simp[] >> strip_tac >>
  rename1 `gas_marked_path T ctx func u 0 (OK fin)` >>
  qexists_tac `fin` >> simp[] >>
  drule_all gas_marked_path_then >> simp[]
QED

Theorem array_one_round_mem:
  array_for_code func cenv bc ty stmts id et tv (LENGTH vs) stride saved_base
    p sz ainst idx dv ov ep nv cond exit stmts_lbl incr
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj /\
  array_round_inv d ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst cond caller orig k es s /\
  k < LENGTH vs /\ LENGTH vs < dimword (:256) /\
  evaluate_type (get_tenv cx) et = SOME tv /\
  value_has_type tv (EL k vs) /\ val_wf tv (EL k vs) /\
  not_local_ptr bc (FEMPTY :: es.scopes) p /\
  lookup_block stmts_lbl func.fn_blocks = SOME bb /\
  isPREFIX sb0.cs_current_insts bb.bb_instructions /\
  caller.cs_next_var <= sa.cs_next_var /\ sa.cs_next_var <= sb0.cs_next_var /\
  (!x. not_fresh_at caller x ==> x <> idx /\ x <> dv /\ x <> ov /\ x <> ep /\ x <> nv) /\
  (!l. saved_base <> Label l) /\
  (!t. array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst stmts_lbl caller k es t ==>
    val_in_memory tv (EL k vs) (w2n arr_base + k * stride) t.vs_memory /\
    w2n arr_base + k * stride < dimword (:256) /\
    w2n arr_base + LENGTH vs * stride <= t.vs_alloca_next) /\
  stmt_frag_mem d ctx func cx (InLoop exit incr) RetQ bc
    (stmts_env bc (InLoop exit incr) ty stmts) (eval_stmts cx stmts)
    (es with scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tv; value := EL k vs; popped := []|>))
        :: es.scopes) /\
  (!gs r ee. eval_stmts cx stmts
    (es with <|scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tv; value := EL k vs; popped := []|>))
        :: es.scopes; gas_obs := gs|>) = (r,ee) ==>
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
      (~b ==> array_round_inv d ctx func cenv cx P vs id idx saved_base arr_base p dst sz
        ainst cond caller orig (SUC k) ee t))
    (\res ee rr. ?e. res = INR e /\
      !tail. stmt_exit RetQ (ee with gas_obs := tail) (INR e) rr)
Proof
  strip_tac >>
  drule array_for_code_condition >> strip_tac >>
  drule array_for_code_entry_static >> strip_tac >>
  drule array_for_code_iteration_static >> strip_tac >>
  `array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst cond caller k es s` by fs[array_round_inv_def] >>
  `not_local_ptr cenv es.scopes dv` by metis_tac[] >>
  `!x. not_fresh_at caller x ==> x <> dv` by metis_tac[] >>
  drule_all array_round_live >> strip_tac >>
  rename1 `gas_marked_path T ctx func s 0 (OK live)` >>
  `array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst stmts_lbl caller k es live` by fs[array_round_inv_def] >>
  `val_in_memory tv (EL k vs) (w2n arr_base + k * stride) live.vs_memory /\
    w2n arr_base + k * stride < dimword (:256) /\
    w2n arr_base + LENGTH vs * stride <= live.vs_alloca_next` by metis_tac[] >>
  `gas_admissible (eval_stmts cx stmts) (stmt_res_ok (InLoop exit incr))
    (es with scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tv; value := EL k vs; popped := []|>))
        :: es.scopes)` by
    (simp[gas_admissible_def, evaluation_state_fn_updates] >> metis_tac[]) >>
  `!x. not_fresh_at caller x ==> x <> ov /\ x <> ep` by metis_tac[] >>
  drule_at (Pat `stmt_frag_mem _ _ _ _ _ _ _ _ _`) array_code_body_outcome_mem >>
  disch_then drule >> disch_then drule >> simp[] >> strip_tac >>
  irule array_round_outcome_prefix_mem >>
  goal_assum (drule_at (Pat `gas_marked_path _ _ _ s _ _`)) >>
  irule array_round_outcome_prefix_mem >>
  goal_assum (drule_at (Pat `gas_marked_path _ _ _ live _ _`)) >>
  ho_match_mp_tac (array_body_round_outcome_mem |> Q.INST
    [`B` |-> `array_body_post_mem d ctx func cx (InLoop exit incr) bc
       (FST (stmts_env bc (InLoop exit incr) ty stmts sb0)) sb0 sb1 s_body`,
     `E` |-> `\r ee rr. !tail. stmt_exit RetQ (ee with gas_obs := tail) r rr`]) >>
  simp[] >> conj_tac
  >- suspend "nonhalt" >>
  conj_tac >- suspend "scopes" >>
  conj_tac >- suspend "body" >>
  suspend "exit"
QED

Resume array_one_round_mem[nonhalt]:
  qpat_x_assum `gas_marked_path _ _ _ live _ _` mp_tac >>
  simp[gas_marked_path_def] >> strip_tac >>
  drule gas_path_mem_exec >> simp[fragExecTheory.exit_result_def]
QED

Resume array_one_round_mem[scopes]:
  rpt strip_tac >>
  qpat_x_assum `!gs r ee. _` drule >> metis_tac[]
QED

Resume array_one_round_mem[body]:
  rpt strip_tac >>
  qpat_x_assum `!gs r ee. _` drule >> strip_tac >>
  `cenv_top_ext cenv bc (FEMPTY :: es.scopes)` by
    (irule array_for_code_scope_frame >> goal_assum (drule_at Any) >>
     fs[array_loop_inv_def]) >>
  `cenv_top_ext cenv bc
    (es with <|scopes := (FEMPTY |+ (id,
      <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: es.scopes;
      gas_obs := gs|>).scopes` by
    (qhdtm_assum `cenv_top_ext`
       (mp_tac o PURE_REWRITE_RULE [cenv_top_ext_def]) >>
     simp[cenv_top_ext_def] >> metis_tac[]) >>
  drule_all array_code_body_finish_mem >> strip_tac >>
  qexistsl_tac [`sc`, `rest`] >> simp[] >> metis_tac[]
QED

Resume array_one_round_mem[exit]:
  rpt strip_tac >>
  qpat_x_assum `!gs r ee. _` drule >> strip_tac >>
  gvs[stmt_res_ok_def] >>
  gvs[stmt_exit_def, exprSimDefsTheory.expr_exit_def,
      evaluation_state_fn_updates] >>
  Cases_on `rr` >> gvs[exprSimDefsTheory.expr_exit_def]
QED

Finalise array_one_round_mem

Theorem array_code_loop_outcome_mem:
  array_for_code func cenv bc ty stmts id et tv (LENGTH vs) stride saved_base
    p sz ainst idx dv ov ep nv cond exit stmts_lbl incr
    j1 j2 j3 j4 i1 i2 i3 sa sb0 sb1 sj /\
  LENGTH vs < dimword (:256) /\ evaluate_type (get_tenv cx) et = SOME tv /\
  lookup_block stmts_lbl func.fn_blocks = SOME bb /\
  isPREFIX sb0.cs_current_insts bb.bb_instructions /\
  caller.cs_next_var <= sa.cs_next_var /\ sa.cs_next_var <= sb0.cs_next_var /\
  (!x. not_fresh_at caller x ==> x <> idx /\ x <> dv /\ x <> ov /\ x <> ep /\ x <> nv) /\
  (!l. saved_base <> Label l) /\
  (!k. k < LENGTH vs ==> value_has_type tv (EL k vs) /\ val_wf tv (EL k vs)) /\
  (!k ei. k < LENGTH vs /\ P ei /\ lookup_scopes id ei.scopes = NONE ==>
    not_local_ptr bc (FEMPTY :: ei.scopes) p /\
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
          P (ee with scopes := rest) /\ lookup_scopes id rest = NONE))) /\
  (!k ei t. k < LENGTH vs /\
    array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
      ainst stmts_lbl caller k ei t ==>
    val_in_memory tv (EL k vs) (w2n arr_base + k * stride) t.vs_memory /\
    w2n arr_base + k * stride < dimword (:256) /\
    w2n arr_base + LENGTH vs * stride <= t.vs_alloca_next) ==>
  !k es s. k <= LENGTH vs /\
    array_round_inv d ctx func cenv cx P vs id idx saved_base arr_base p dst sz
      ainst cond caller orig k es s /\
    gas_admissible (eval_for cx tv id stmts (DROP k vs)) ok es ==>
    gas_outcome T (cx_tops cx) (ctx,func)
      (eval_for cx tv id stmts (DROP k vs)) (es,s)
      (\res ee t. res = INL () /\
        array_round_done d ctx func cenv cx caller orig exit ee t)
      (\res ee rr. ?ex. res = INR ex /\
        !tail. stmt_exit RetQ (ee with gas_obs := tail) (INR ex) rr)
Proof
  strip_tac >>
  ho_match_mp_tac stmtSimForRoundsTheory.eval_for_rounds >>
  conj_tac >- suspend "round" >>
  suspend "last"
QED

Resume array_code_loop_outcome_mem[round]:
  rpt strip_tac >>
  `P es /\ lookup_scopes id es.scopes = NONE` by
    fs[array_round_inv_def, array_loop_inv_def] >>
  qpat_x_assum `!k ei. _` drule_all >> strip_tac >>
  drule array_one_round_mem >> disch_then irule >>
  simp[] >> conj_tac >- metis_tac[] >>
  rpt strip_tac >> qpat_x_assum `!k ei t. _` drule_all >>
  simp[MULT_COMM]
QED

Resume array_code_loop_outcome_mem[last]:
  rpt strip_tac >>
  drule array_for_code_iteration_static >> strip_tac >>
  drule array_for_code_condition >> strip_tac >>
  drule array_for_code_entry_static >> strip_tac >>
  `not_local_ptr cenv es.scopes dv` by metis_tac[] >>
  `!x. not_fresh_at caller x ==> x <> dv` by metis_tac[] >>
  drule_all array_round_last >> simp[]
QED

Finalise array_code_loop_outcome_mem

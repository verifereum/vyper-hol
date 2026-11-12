Theory stmtForDynArrayMemoryRounds
Ancestors
  stmtForDynArrayMemoryControl stmtForDynArrayMemoryCopy
  stmtForArrayMemoryRounds stmtForArrayMemoryRoundSupport
  whitelistForIterDynLoop stmtSimForArrayLoop stmtSimProps exprLoweringProps
  bodyMemoryDefs loweringPosts compileEnv loweringStateRelDefs
  venomState allocaHistory fragGasMode fragGasPathMem finite_map list arithmetic
  rich_list emitHelper venomInst venomMemDefs bodyDeclMemoryCounted stmtLowering
  stmtSimDefs gasContext vyperState
Libs
  monadsyntax

(* Specialize the certified header-shifted copy to the loop invariant. *)
Theorem dynarray_code_copy_entry_mem[local]:
  dynarray_for_code func cenv bc ty stmts id et tv stride saved_base
    p sz ainst idx dv ov tot ep nv lv cond exit stmts_lbl incr
    j1 j2 j3 j4 j5 i1 i2 i3 sa sb0 sb1 sj /\
  array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst stmts_lbl caller k es s /\
  k < LENGTH vs /\ evaluate_type (get_tenv cx) et = SOME tv /\
  value_has_type tv (EL k vs) /\ val_wf tv (EL k vs) /\
  val_in_memory tv (EL k vs) (w2n arr_base + 32 + k * stride) s.vs_memory /\
  w2n arr_base + 32 + k * stride < dimword (:256) /\
  w2n arr_base + 32 + LENGTH vs * stride <= s.vs_alloca_next /\
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
    (!x. not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep ==>
      lookup_var x t = lookup_var x s)
Proof
  strip_tac >>
  `cenv_top_ext cenv bc (FEMPTY :: es.scopes)` by
    (irule dynarray_for_code_scope_frame >> goal_assum (drule_at Any) >>
     fs[array_loop_inv_def]) >>
  `alloca_inv s` by fs[array_loop_inv_def, stmt_state_rel_def] >>
  `w2n dst + sz <= s.vs_alloca_next` by
    (fs[array_loop_inv_def, alloca_inv_def, alloca_next_valid_def] >>
     qpat_x_assum `!aid base sz. _` drule >> simp[ADD_COMM]) >>
  `k * stride + stride <= LENGTH vs * stride` by
    (`k + 1 <= LENGTH vs` by simp[] >>
     ` (k + 1) * stride <= LENGTH vs * stride` by simp[LE_MULT_RCANCEL] >>
     qpat_x_assum `(_ + 1) * stride <= _` mp_tac >>
     pure_rewrite_tac[RIGHT_ADD_DISTRIB, MULT_LEFT_1] >> decide_tac) >>
  drule dynarray_for_code_entry_inputs >> strip_tac >>
  drule dynarray_for_code_iteration_static >> strip_tac >>
  qhdtm_assum `array_loop_inv`
    (strip_assume_tac o PURE_REWRITE_RULE [array_loop_inv_def]) >>
  `w2n arr_base + 32 + k * stride + stride <= s.vs_alloca_next /\
   w2n dst + stride <= s.vs_alloca_next` by decide_tac >>
  `not_local_ptr cenv es.scopes ov /\ not_local_ptr cenv es.scopes tot /\
   not_local_ptr cenv es.scopes ep` by metis_tac[] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  drule_all dynarray_round_copy_entry_mem >> strip_tac >>
  qexists_tac `t` >> simp[]
QED

(* The body boundary records concrete runtime facts, independent of how many
   scratch registers were used to calculate the element address. *)
Theorem dynarray_code_body_outcome_mem[local]:
  dynarray_for_code func cenv bc ty stmts id et tv stride saved_base
    p sz ainst idx dv ov tot ep nv lv cond exit stmts_lbl incr
    j1 j2 j3 j4 j5 i1 i2 i3 sa sb0 sb1 sj /\
  array_round_inv d ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst stmts_lbl caller orig k es s /\
  k < LENGTH vs /\ evaluate_type (get_tenv cx) et = SOME tv /\
  value_has_type tv (EL k vs) /\ val_wf tv (EL k vs) /\
  val_in_memory tv (EL k vs) (w2n arr_base + 32 + k * stride) s.vs_memory /\
  w2n arr_base + 32 + k * stride < dimword (:256) /\
  w2n arr_base + 32 + LENGTH vs * stride <= s.vs_alloca_next /\
  not_local_ptr bc (FEMPTY :: es.scopes) p /\
  lookup_block stmts_lbl func.fn_blocks = SOME bb /\
  isPREFIX sb0.cs_current_insts bb.bb_instructions /\
  caller.cs_next_var <= sa.cs_next_var /\ sa.cs_next_var <= sb0.cs_next_var /\
  (!x. not_fresh_at caller x ==> x <> ov /\ x <> tot /\ x <> ep) /\
  (!l. saved_base <> Label l) /\
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
    array_round_frame d func cenv caller orig s_body /\
    ret_pc_ok cenv caller s_body /\ ret_pc_ok bc sb0 s_body /\
    lookup_var idx s_body = SOME (n2w k) /\ lookup_var p s_body = SOME dst /\
    eval_operand saved_base s_body = SOME arr_base /\
    FLOOKUP s_body.vs_allocas ainst.inst_id = SOME (w2n dst,sz)
Proof
  strip_tac >>
  `array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst stmts_lbl caller k es s /\ alloca_history func s /\
    return_buf_frame d cenv caller s` by
    fs[array_round_inv_def, array_round_frame_def] >>
  drule_all dynarray_code_copy_entry_mem >> strip_tac >>
  `!x w. not_fresh_at caller x /\ lookup_var x s = SOME w ==>
    lookup_var x t = SOME w` by
    (rpt strip_tac >>
     `not_fresh_at sa x` by (fs[not_fresh_at_def] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
     metis_tac[]) >>
  `bc.ce_return_pc = cenv.ce_return_pc /\ bc.ce_return_buf = cenv.ce_return_buf` by
    (qhdtm_assum `dynarray_for_code` mp_tac >>
     pure_rewrite_tac[dynarray_for_code_def] >> strip_tac >>
     qpat_x_assum `_ = cenv` (mp_tac o AP_TERM
       ``\ce:compile_env. (ce.ce_return_pc,ce.ce_return_buf)``) >> simp[]) >>
  `ret_pc_ok bc sb0 t /\ ret_pc_ok cenv caller t` by
    (conj_tac >> irule ret_pc_ok_frame >> qexistsl_tac [`cenv`, `s`, `caller`] >>
     fs[array_loop_inv_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `return_buf_frame d bc sb0 t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`, `s`, `caller`] >>
     simp[] >> metis_tac[LESS_EQ_TRANS]) >>
  `array_round_frame d func cenv caller orig t` by
    (irule array_round_frame_transport >> simp[] >> qexists_tac `s` >>
     fs[array_round_inv_def]) >>
  drule dynarray_for_code_iteration_static >> strip_tac >>
  `lookup_var idx t = SOME (n2w k) /\ lookup_var p t = SOME dst /\
   eval_operand saved_base t = SOME arr_base /\
   FLOOKUP t.vs_allocas ainst.inst_id = SOME (w2n dst,sz)` by
    (fs[array_loop_inv_def] >>
     irule array_saved_operand_frame >> simp[] >> qexists_tac `s` >> simp[] >>
     rpt strip_tac >> Cases_on `lookup_var x s` >> fs[eval_operand_def] >> metis_tac[]) >>
  `stmts_env bc (InLoop exit incr) ty stmts sb0 =
     (FST (stmts_env bc (InLoop exit incr) ty stmts sb0),sb1)` by
    (Cases_on `stmts_env bc (InLoop exit incr) ty stmts sb0` >>
     fs[dynarray_for_code_def, compile_stmts_env]) >>
  `fn_inst_ids_distinct func /\ s.vs_current_bb = sb0.cs_current_bb` by
    fs[dynarray_for_code_def, array_loop_inv_def] >>
  qexists_tac `t` >> simp[] >>
  qhdtm_x_assum `stmt_frag_mem` mp_tac >> rewrite_tac[stmt_frag_mem_def] >>
  disch_then (qspecl_then [`sb0`, `sb1`, `t`,
    `FST (stmts_env bc (InLoop exit incr) ty stmts sb0)`] mp_tac) >>
  simp[GSYM array_body_post_mem_def, SF ETA_ss]
QED

(* Both live and final conditions preserve the old-register/allocation frame. *)
Theorem dynarray_round_condition_mem[local]:
  dynarray_for_code func cenv bc ty stmts id et tv stride saved_base
    p sz ainst idx dv ov tot ep nv lv cond exit stmts_lbl incr
    j1 j2 j3 j4 j5 i1 i2 i3 sa sb0 sb1 sj /\
  array_round_inv d ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst cond caller orig k es s /\
  LENGTH vs < dimword (:256) /\
  lookup_var lv orig = SOME (n2w (LENGTH vs)) /\ not_fresh_at caller lv /\
  (!x. not_fresh_at caller x ==> x <> dv) ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
    array_round_inv d ctx func cenv cx P vs id idx saved_base arr_base p dst sz
      ainst (if k = LENGTH vs then exit else stmts_lbl) caller orig k es t
Proof
  strip_tac >> drule dynarray_for_code_entry_static >> strip_tac >>
  `array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst cond caller k es s /\ alloca_history func s /\
    lookup_var lv s = SOME (n2w (LENGTH vs))` by
    (fs[array_round_inv_def, array_round_frame_def] >> metis_tac[]) >>
  `not_local_ptr cenv es.scopes dv` by metis_tac[] >>
  `fn_inst_ids_distinct func` by fs[dynarray_for_code_def] >>
  `saved_base <> Var dv` by metis_tac[] >>
  drule dynarray_condition_boundary_mem >> simp[] >>
  disch_then drule >> simp[] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_path_mem ctx func s 0 (OK t)` >>
  qexists_tac `t` >> simp[gas_marked_path_def, array_round_inv_def] >>
  irule array_round_frame_transport >> simp[] >> qexists_tac `s` >>
  fs[array_round_inv_def] >> rpt strip_tac >>
  fs[Abbr `t`, jump_to_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  metis_tac[]
QED

(* Scratch-independent restoration: apply the runtime frame at s_body. *)
Theorem dynarray_code_body_finish_mem[local]:
  dynarray_for_code func cenv bc ty stmts id et tv stride saved_base
    p sz ainst idx dv ov tot ep nv lv cond exit stmts_lbl incr
    j1 j2 j3 j4 j5 i1 i2 i3 sa sb0 sb1 sj /\
  array_body_post_mem d ctx func cx (InLoop exit incr) bc bc' sb0 sb1 s_body r es2 t /\
  array_round_frame d func cenv caller orig s_body /\
  ret_pc_ok cenv caller s_body /\ ret_pc_ok bc sb0 s_body /\
  lookup_var idx s_body = SOME (n2w k) /\ lookup_var p s_body = SOME dst /\
  eval_operand saved_base s_body = SOME arr_base /\
  FLOOKUP s_body.vs_allocas ainst.inst_id = SOME (w2n dst,sz) /\
  cenv_top_ext cenv bc ei.scopes /\
  eval_stmts cx stmts ei = (r,es2) /\ es2.scopes = sc :: rest /\
  (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
  ((r = INL () \/ r = INR ContinueException) ==>
    P (es2 with scopes := rest) /\ lookup_scopes id rest = NONE) /\
  caller.cs_next_var <= sa.cs_next_var /\ sa.cs_next_var <= sb0.cs_next_var /\
  (!x. not_fresh_at caller x ==> x <> idx /\ x <> nv) /\
  (!l. saved_base <> Label l) /\ k < LENGTH vs ==>
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
    (qhdtm_assum `dynarray_for_code` mp_tac >>
     pure_rewrite_tac[dynarray_for_code_def] >> strip_tac >>
     qpat_x_assum `_ = cenv` (mp_tac o AP_TERM
       ``\ce:compile_env. ce.ce_return_buf``) >> simp[]) >>
  `cenv.ce_return_buf = bc.ce_return_buf` by simp[] >>
  drule_all (PURE_REWRITE_RULE [GSYM array_body_post_mem_def]
    array_body_mem_post_projection) >> strip_tac >>
  drule dynarray_for_code_iteration_static >> strip_tac >>
  `not_fresh_at sb0 idx /\ not_fresh_at sb0 p /\
   (!x. saved_base = Var x ==> not_fresh_at sb0 x)` by
    (fs[not_fresh_at_def] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
  drule_all array_body_runtime_frame >> strip_tac >>
  `!x w. not_fresh_at caller x /\ lookup_var x s_body = SOME w ==>
    lookup_var x t = SOME w` by
    (rpt strip_tac >>
     `not_fresh_at sb0 x` by
       (fs[not_fresh_at_def] >> metis_tac[LESS_LESS_EQ_TRANS, LESS_EQ_TRANS]) >>
     metis_tac[]) >>
  `array_round_frame d func cenv caller orig t` by
    (irule array_round_frame_transport >> simp[] >> qexists_tac `s_body` >> simp[]) >>
  Cases_on `r = INR BreakException`
  >- (qexistsl_tac [`T`, `t`] >> simp[gas_marked_path_def] >> conj_tac
      >- (irule (cj 1 gas_path_mem_rules) >> simp[]) >>
      irule array_round_break >> metis_tac[]) >>
  `r = INL () \/ r = INR ContinueException` by fs[stmt_lands_def] >>
  `array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst incr caller k (es2 with scopes := rest) (jump_to incr t)` by
    fs[array_loop_inv_def, stmt_state_rel_jump_to, ret_pc_ok_jump_to,
       jump_to_def, eval_operand_def, lookup_var_def] >>
  `?u. gas_marked_path T ctx func t 0 (OK u) /\
    array_round_inv d ctx func cenv cx P vs id idx saved_base arr_base p dst sz
      ainst incr caller orig k (es2 with scopes := rest) u` by
    (irule array_round_postbody_entry >> simp[] >>
     qexistsl_tac [`exit`, `r`, `sb1`, `sj`] >>
     fs[dynarray_for_code_def]) >>
  rename1 `gas_marked_path T ctx func t 0 (OK u)` >>
  `not_local_ptr cenv rest idx /\ not_local_ptr cenv rest nv` by metis_tac[] >>
  drule array_round_increment >> simp[] >>
  disch_then drule >> simp[] >> strip_tac >>
  rename1 `gas_marked_path T ctx func u 0 (OK fin)` >>
  qexists_tac `fin` >> simp[] >>
  drule_all gas_marked_path_then >> simp[]
QED

Theorem dynarray_one_round_mem[local]:
  dynarray_for_code func cenv bc ty stmts id et tv stride saved_base
    p sz ainst idx dv ov tot ep nv lv cond exit stmts_lbl incr
    j1 j2 j3 j4 j5 i1 i2 i3 sa sb0 sb1 sj /\
  array_round_inv d ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst cond caller orig k es s /\
  k < LENGTH vs /\ LENGTH vs < dimword (:256) /\
  lookup_var lv orig = SOME (n2w (LENGTH vs)) /\ not_fresh_at caller lv /\
  evaluate_type (get_tenv cx) et = SOME tv /\
  value_has_type tv (EL k vs) /\ val_wf tv (EL k vs) /\
  not_local_ptr bc (FEMPTY :: es.scopes) p /\
  lookup_block stmts_lbl func.fn_blocks = SOME bb /\
  isPREFIX sb0.cs_current_insts bb.bb_instructions /\
  caller.cs_next_var <= sa.cs_next_var /\ sa.cs_next_var <= sb0.cs_next_var /\
  (!x. not_fresh_at caller x ==>
    x <> idx /\ x <> dv /\ x <> ov /\ x <> tot /\ x <> ep /\ x <> nv) /\
  (!l. saved_base <> Label l) /\
  (!t. array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst stmts_lbl caller k es t ==>
    val_in_memory tv (EL k vs) (w2n arr_base + 32 + k * stride) t.vs_memory /\
    w2n arr_base + 32 + k * stride < dimword (:256) /\
    w2n arr_base + 32 + LENGTH vs * stride <= t.vs_alloca_next) /\
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
  `!x. not_fresh_at caller x ==> x <> dv` by metis_tac[] >>
  drule_all dynarray_round_condition_mem >> strip_tac >>
  `k <> LENGTH vs` by decide_tac >> fs[] >>
  rename1 `gas_marked_path T ctx func s 0 (OK live)` >>
  `array_loop_inv ctx func cenv cx P vs id idx saved_base arr_base p dst sz
    ainst stmts_lbl caller k es live` by fs[array_round_inv_def] >>
  `val_in_memory tv (EL k vs) (w2n arr_base + 32 + k * stride) live.vs_memory /\
    w2n arr_base + 32 + k * stride < dimword (:256) /\
    w2n arr_base + 32 + LENGTH vs * stride <= live.vs_alloca_next` by
    (qpat_x_assum `!t. array_loop_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ==> _`
       drule >> simp[]) >>
  `gas_admissible (eval_stmts cx stmts) (stmt_res_ok (InLoop exit incr))
    (es with scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tv; value := EL k vs; popped := []|>))
        :: es.scopes)` by
    (simp[gas_admissible_def, evaluation_state_fn_updates] >> metis_tac[]) >>
  `!x. not_fresh_at caller x ==> x <> ov /\ x <> tot /\ x <> ep` by metis_tac[] >>
  drule_at (Pat `stmt_frag_mem _ _ _ _ _ _ _ _ _`) dynarray_code_body_outcome_mem >>
  disch_then drule >> disch_then drule >> simp[] >> strip_tac >>
  irule array_round_outcome_prefix_mem >>
  goal_assum (drule_at (Pat `gas_marked_path _ _ _ s _ _`)) >>
  irule array_round_outcome_prefix_mem >>
  goal_assum (drule_at (Pat `gas_marked_path _ _ _ live _ _`)) >>
  ho_match_mp_tac (array_body_round_outcome_mem |> Q.INST
    [`B` |-> `array_body_post_mem d ctx func cx (InLoop exit incr) bc
       (FST (stmts_env bc (InLoop exit incr) ty stmts sb0)) sb0 sb1 s_body`,
     `E` |-> `\r ee rr. !tail. stmt_exit RetQ (ee with gas_obs := tail) r rr`]) >>
  simp[] >> conj_tac >- suspend "nonhalt" >>
  conj_tac >- suspend "scopes" >>
  conj_tac >- suspend "body" >>
  suspend "exit"
QED

Resume dynarray_one_round_mem[nonhalt]:
  qpat_x_assum `gas_marked_path _ _ _ live _ _` mp_tac >>
  simp[gas_marked_path_def] >> strip_tac >>
  drule gas_path_mem_exec >> simp[fragExecTheory.exit_result_def]
QED

Resume dynarray_one_round_mem[scopes]:
  rpt strip_tac >>
  qpat_x_assum `!gs r ee. _` drule >> metis_tac[]
QED

Resume dynarray_one_round_mem[body]:
  rpt strip_tac >>
  qpat_x_assum `!gs r ee. _` drule >> strip_tac >>
  `cenv_top_ext cenv bc (FEMPTY :: es.scopes)` by
    (irule dynarray_for_code_scope_frame >> goal_assum (drule_at Any) >>
     fs[array_loop_inv_def]) >>
  `cenv_top_ext cenv bc
    (es with <|scopes := (FEMPTY |+ (id,
      <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: es.scopes;
      gas_obs := gs|>).scopes` by
    (qhdtm_assum `cenv_top_ext`
       (mp_tac o PURE_REWRITE_RULE [cenv_top_ext_def]) >>
     simp[cenv_top_ext_def] >> metis_tac[]) >>
  `!x. not_fresh_at caller x ==> x <> idx /\ x <> nv` by metis_tac[] >>
  drule_all dynarray_code_body_finish_mem >> strip_tac >>
  qexistsl_tac [`sc`, `rest`] >> simp[] >> metis_tac[]
QED

Resume dynarray_one_round_mem[exit]:
  rpt strip_tac >>
  qpat_x_assum `!gs r ee. _` drule >> strip_tac >>
  gvs[stmt_res_ok_def] >>
  gvs[stmt_exit_def, exprSimDefsTheory.expr_exit_def,
      evaluation_state_fn_updates] >>
  Cases_on `rr` >> gvs[exprSimDefsTheory.expr_exit_def]
QED

Finalise dynarray_one_round_mem

Theorem dynarray_code_loop_outcome_mem:
  dynarray_for_code func cenv bc ty stmts id et tv stride saved_base
    p sz ainst idx dv ov tot ep nv lv cond exit stmts_lbl incr
    j1 j2 j3 j4 j5 i1 i2 i3 sa sb0 sb1 sj /\
  LENGTH vs < dimword (:256) /\ evaluate_type (get_tenv cx) et = SOME tv /\
  lookup_var lv orig = SOME (n2w (LENGTH vs)) /\ not_fresh_at caller lv /\
  lookup_block stmts_lbl func.fn_blocks = SOME bb /\
  isPREFIX sb0.cs_current_insts bb.bb_instructions /\
  caller.cs_next_var <= sa.cs_next_var /\ sa.cs_next_var <= sb0.cs_next_var /\
  (!x. not_fresh_at caller x ==>
    x <> idx /\ x <> dv /\ x <> ov /\ x <> tot /\ x <> ep /\ x <> nv) /\
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
    val_in_memory tv (EL k vs) (w2n arr_base + 32 + k * stride) t.vs_memory /\
    w2n arr_base + 32 + k * stride < dimword (:256) /\
    w2n arr_base + 32 + LENGTH vs * stride <= t.vs_alloca_next) ==>
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

Resume dynarray_code_loop_outcome_mem[round]:
  rpt strip_tac >>
  `P es /\ lookup_scopes id es.scopes = NONE` by
    fs[array_round_inv_def, array_loop_inv_def] >>
  qpat_x_assum `!k ei. _` drule_all >> strip_tac >>
  drule dynarray_one_round_mem >> disch_then irule >>
  simp[] >> conj_tac >- metis_tac[] >>
  rpt strip_tac >> qpat_x_assum `!k ei t. _` drule_all >>
  simp[MULT_COMM]
QED

Resume dynarray_code_loop_outcome_mem[last]:
  rpt strip_tac >>
  `!x. not_fresh_at caller x ==> x <> dv` by metis_tac[] >>
  drule_all dynarray_round_condition_mem >> strip_tac >>
  qexists_tac `t` >> fs[array_round_inv_def, array_loop_inv_def,
    array_round_done_def, state_rel_gas_obs]
QED

Finalise dynarray_code_loop_outcome_mem

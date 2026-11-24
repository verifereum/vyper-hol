(* Selected evaluation of the word arguments shared by both raw-call layouts. *)
Theory entryCreateRawCallWords
Ancestors
  bodyFullWordArgs entryCreateReplayBind entryCreateScopedBind entryCreateBodyCut
  entryCreateCompositeFocus entryCreateIntervalLayout entryCreateRegionLift
  entryCreateNativeFirstExit entryCreatePendingScope createSizeCutCode
  exprSimFullBundleProps s1PrefixDefs vyperStorageFootprint
  vyperStorageTrace gasExemptCert vyperState vyperInterpreter exprSimWordArgs
  gasOutcomeFull gasSummary fragGasOriginPtr entryCreateCompletedCut gasStorage
  entryCreateFocusSpec entryCreateOperandReplay entryCreatePathScope
  createSizePrefixReplay createSizeCutRegion createSizeOperandCode compileEnv
  fragExec fragGasOrigin gasExplicitSites abiEncoderProps
  bodySim bodyFullShadowBodyInv bodyFullPreds bodyFullIfExpReach bodyMemoryDefs bodyPtrDefs
  exprSimSource exprSimHyps exprBodyPreProps exprSimPrecompiles wordArgsPtr
  exprLoweringProps loweringShapeDefs loweringPosts
  exprSimDefs gasShadowCompileStmtHelpers gasShadowState
  vyperEvalExprPreservesScopesDom venomState list arithmetic

Definition selected_word_args_post_def:
  selected_word_args_post (DF,lo,d,ctx,func) cenv cx
      (es,sa,sm,s0,todo,xs,G0,tn0) H (rr : value list + exception) mid G tn t <=>
    ?vs. rr = INL vs /\
      typed_args_post H ctx func cenv cx es sa s0 mid todo xs vs t /\
      expr_sim_full_endpoint func sm s0 t /\
      ghost_inv_at (DF H) lo d cenv cx mid G tn t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
      EVERY (\x. op_taint tn x = {}) xs
End

Definition selected_word_args_exit_def:
  selected_word_args_exit ctx cx H rr mid gt r <=>
    wb_args_exit rr r /\ halt_exit H cx mid rr r /\
    (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u)
End

Theorem words_cons_return[local]:
  ignore_bind (bind source (\vs. return (v::vs))) (return ()) =
  ignore_bind source (return ())
Proof
  simp[FUN_EQ_THM,ignore_bind_def,bind_def] >> gen_tac >>
  Cases_on `source x` >> qmatch_asmsub_rename_tac `source x = (result,st)` >>
  Cases_on `result` >> simp[return_def]
QED

(* Map only normal source results; the selected path, including an
   unfinished head or a terminal edge, is unchanged. *)
Theorem words_cons_map[local]:
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a b source (es,s,G,tn) Q R /\
  (!H vs ee G' tn' t obs. source (es with gas_obs := obs) = (INL vs,ee) /\
      valid_horizon cx st0 H ee.storage_trace /\ Q H (INL vs) ee G' tn' t ==>
      P H (INL (v::vs)) ee G' tn' t) /\
  (!H ee G' tn' t exc. ~Q H (INR exc) ee G' tn' t) /\
  (!H exc ee gt r. R H (INR exc) ee gt r ==> R2 H (INR exc) ee gt r) /\
  (!H ee gt r vs. ~R H (INL vs) ee gt r) ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a b
    (bind source (\vs. return (v::vs))) (es,s,G,tn) P R2
Proof
  strip_tac >>
  `!z. bind source (\vs. return (v::vs)) z =
       ((case FST (source z) of INL vs => INL (v::vs) | INR ex => INR ex),
         SND (source z))` by
    (gen_tac >> Cases_on `source z` >> qmatch_asmsub_rename_tac `source z = (res,st)` >>
     Cases_on `res` >> simp[bind_def,return_def]) >>
  qpat_x_assum `scoped_operand_outcome _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [scoped_operand_outcome_def]) >>
  rewrite_tac[scoped_operand_outcome_def] >> qexists_tac `marks`
  >- (disj1_tac >> fs[gas_bad_storage_at_def] >> metis_tac[])
  >- (disj2_tac >> disj1_tac >>
      qexistsl [`case res of INL vs => INL (v::vs) | INR ex => INR ex`,
                `ee`,`r`,`G'`,`tn'`] >> simp[] >>
      rpt strip_tac >>
      `source (es with gas_obs := gas_explicit marks s.vs_gas_readings) =
         (res,ee with gas_obs := [])` by metis_tac[APPEND_NIL] >>
      Cases_on `res` >> gvs[]
      >- (disj1_tac >>
          qpat_assum `!H'. valid_horizon _ _ H' _ ==> _`
            (qspec_then `H` (strip_assume_tac o UNDISCH)) >> gvs[] >>
          qpat_assum `!H vs ee G' tn' t obs. _ ==> _` irule >>
          simp[] >> metis_tac[]) >>
      metis_tac[]) >>
  disj2_tac >> disj2_tac >> simp[words_cons_return] >> metis_tac[]
QED

Theorem word_return_frame[local]:
  storage_trace_frame (bind (eval_exprs cx todo) (\vs. return (v::vs)))
Proof
  irule storage_trace_frame_bind_all >>
  simp[evaluate_storage_trace_frame,storage_trace_frame_return]
QED

Theorem word_head_frame[local]:
  storage_trace_frame (bind (eval_expr cx e) (read_result cx))
Proof
  irule storage_trace_frame_bind_all >>
  simp[evaluate_storage_trace_frame,storage_trace_frame_read_result]
QED

Theorem word_args_right_prefix[local]:
  a.cs_next_id <= m.cs_next_id /\ create_expr_prefix m b E C f t right u ==>
  create_expr_prefix a b E C f t right u
Proof
  strip_tac >> irule create_expr_prefix_mono >> first_assum (irule_at Any) >>
  simp[create_prefix_step_def,frag_ids_def] >> metis_tac[LESS_EQ_TRANS]
QED

Theorem word_args_prepend_full[local]:
  a.cs_next_id <= m.cs_next_id /\ create_expr_prefix a b E C f s left t /\
  create_operand_full_scope m b E C f t right r ==>
  create_operand_full_scope a b E C f s (left ++ right) r
Proof
  Cases_on `r` >> simp[create_operand_full_scope_def] >> strip_tac
  >- metis_tac[word_args_right_prefix,create_expr_prefix_append] >>
  rename1 `create_expr_prefix m b E C f t front stop` >>
  `create_expr_prefix a b E C f s (left ++ front) stop` by
    metis_tac[word_args_right_prefix,create_expr_prefix_append] >>
  metis_tac[APPEND_ASSOC]
QED

Theorem word_args_prepend_focus[local]:
  body_inv tops C ce cx /\ MEM f C.ctx_functions /\
  create_cut_code {} m b /\ fn_has_code m b f /\ a.cs_next_id <= m.cs_next_id /\
  create_operand_at m t /\ create_expr_prefix a b E C f s left t /\
  create_operand_focus_scope m b E C f t right ==>
  create_operand_focus_scope a b E C f s (left ++ right)
Proof
  simp[create_operand_focus_scope_def] >>
  disch_then (map_every strip_assume_tac o CONJUNCTS) >>
  rename1 `create_expr_prefix m b E C f t front stop` >>
  `create_expr_prefix a b E C f s (left ++ front) stop` by
    metis_tac[word_args_right_prefix,create_expr_prefix_append] >>
  qexistsl [`left ++ front`,`stop`,`pending`] >> simp[APPEND_ASSOC] >>
  `create_cut_region m b t` by
    (fs[create_operand_at_def] >> metis_tac[cj 1 create_cut_region_rules]) >>
  `create_cut_region m b stop` by metis_tac[create_expr_prefix_cut_region] >>
  disj2_tac >> rpt strip_tac >>
  qpat_assum `create_prefix_step a b E C f stop _ _`
    (strip_assume_tac o REWRITE_RULE [create_prefix_step_def]) >>
  qpat_assum `!right v. create_prefix_step m b E C f stop right v ==> _` irule >>
  qexists_tac `v` >> irule (cj 1 operand_cut_region_edge) >>
  simp[] >> metis_tac[]
QED

Theorem word_args_cons_scope[local]:
  body_inv tops C ce cx /\ MEM f C.ctx_functions /\
  create_cut_code {} a m /\ fn_has_code a m f /\
  create_cut_code {} m b /\ fn_has_code m b f /\ create_layout a b /\
  create_operand_at a s ==>
  (!marks. create_operand_focus_scope a m E C f s marks ==>
           create_operand_focus_scope a b E C f s marks) /\
  (!marks r. exit_result r /\ create_operand_full_scope a m E C f s marks r ==>
             create_operand_full_scope a b E C f s marks r) /\
  (!left t right. create_operand_full_scope a m E C f s left (OK t) /\
                  create_operand_focus_scope m b E C f t right ==>
                  create_operand_focus_scope a b E C f s (left ++ right)) /\
  (!left t right r. create_operand_full_scope a m E C f s left (OK t) /\
                    create_operand_full_scope m b E C f t right r ==>
                    create_operand_full_scope a b E C f s (left ++ right) r)
Proof
  strip_tac >>
  `create_cut_region a m s` by
    (fs[create_operand_at_def] >> metis_tac[cj 1 create_cut_region_rules]) >>
  `cs_extends a m /\ cs_extends m b /\
   a.cs_next_id <= m.cs_next_id /\ m.cs_next_id <= b.cs_next_id` by fs[create_cut_code_def] >>
  `!u. create_cut_region a m u /\ ~create_operand_at m u ==> ~create_operand_at b u` by
    metis_tac[create_layout_left_stop] >>
  conj_tac >- metis_tac[create_left_focus_lift_at] >>
  conj_tac >- metis_tac[create_left_terminal_lift_at] >>
  `!left t. create_operand_full_scope a m E C f s left (OK t) ==>
            create_operand_at m t /\ create_expr_prefix a b E C f s left t` by
    (simp[create_operand_full_scope_def, create_operand_at_def] >>
     metis_tac[create_left_prefix_lift_at,create_operand_at_def]) >>
  metis_tac[word_args_prepend_focus,word_args_prepend_full]
QED

(* The prefix equation at tail [] is enough to transfer the source-side
   readiness facts through the first operand. Keep that equation in its
   normal post so the native cut callback can also use it. *)
Definition word_head_post_def:
  word_head_post (DF,lo,d,C,f) ce cx e (es,a,m,s,x,G0,tn0) H r mid G tn t <=>
    expr_sim_full_post (DF,lo,d,C,f) ce cx e (es,a,m,s,x,G0,tn0) H r mid G tn t /\
    (?obs. bind (eval_expr cx e) (read_result cx) (es with gas_obs := obs) = (r,mid)) /\
    ~t.vs_halted /\ mid.gas_obs = []
End

Theorem word_head_scoped[local]:
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a m
    (bind (eval_expr cx e) (read_result cx)) (es,s,G0,tn0)
    (expr_sim_full_post (DF,lo,d,C,f) ce cx e (es,a,m,s,x,G0,tn0))
    (create_operand_exit_post C cx) ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a m
    (bind (eval_expr cx e) (read_result cx)) (es,s,G0,tn0)
    (word_head_post (DF,lo,d,C,f) ce cx e (es,a,m,s,x,G0,tn0))
    (\H r ee gt u. (?exc. r = INR exc) /\ selected_word_args_exit C cx H r ee gt u)
Proof
  simp[scoped_operand_outcome_def] >> disch_then (qx_choose_then `marks` assume_tac) >>
  qexists_tac `marks` >>
  qpat_x_assum `_ \/ _` (DISJ_CASES_THEN2 assume_tac
      (DISJ_CASES_THEN2 strip_assume_tac assume_tac)) >> simp[] >>
  disj2_tac >> disj1_tac >> qexistsl [`res`,`ee`,`r`,`G'`,`tn'`] >> simp[] >>
  rpt strip_tac >> res_tac >> simp[word_head_post_def] >>
  gvs[create_operand_exit_post_def,selected_word_args_exit_def,wb_args_exit_def] >>
  Cases_on `res` >> gvs[expr_sim_full_post_def,expr_exit_def,halt_exit_def] >>
  metis_tac[gas_origin_ptr_path_projections,fragGasSeqPtrTheory.gas_path_ptr_ok_not_halted]
QED

Theorem word_head_ready_tail[local]:
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre ce cx env e es /\
  valid_horizon cx st0 H0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    word_head_post (DF,lo,d,C,f) ce cx e (es,a,m,s,x,G0,tn0) H (INL v) mid G tn t) /\
  return_buf_frame d ce a s /\ a.cs_next_var <= m.cs_next_var ==>
  expr_sim_inv ce cx env mid /\ body_const_cells_agree [(NONE,tops)] cx env mid /\
  expr_sim_full_endpoint f m s t /\ ~t.vs_halted /\ mid.gas_obs = [] /\
  (ctx_has_dalloca C ==> allocas_below_fmp t) /\ return_buf_frame d ce m t /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==> valid_horizon cx st0 H es.storage_trace /\
    stmt_state_rel H C f ce cx mid t /\ storage_well_formed_on cx mid (FST H) /\
    ghost_inv_at (DF H) lo d ce cx mid G tn t)
Proof
  strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (drule_then (strip_assume_tac o BETA_RULE o REWRITE_RULE [word_head_post_def,expr_sim_full_post_def])) >>
  `expr_body_pre ce cx env e (es with gas_obs := obs)` by simp[] >>
  `expr_sim_inv ce cx env mid` by
    (drule_at (Pos last) (REWRITE_RULE [ETA_THM] expr_body_pre_eval) >>
     disch_then (qspec_then `ce` mp_tac) >> simp[]) >>
  `body_const_cells_agree [(NONE,tops)] cx env mid` by
    (`well_typed_expr env e` by metis_tac[expr_body_pre_static_facts] >>
     irule body_const_cells_agree_expr_read >>
     goal_assum (drule_at (Pat `bind (eval_expr _ _) _ _ = _`)) >> simp[]) >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (drule (SRULE [SF ETA_ss] forced_eval_expr_preserves_scopes_dom) >> simp[]) >>
  `return_buf_frame d ce m t` by
    (irule return_buf_frame_frame >> fs[expr_post_def,expr_sim_full_endpoint_def] >> metis_tac[]) >>
  simp[] >> rpt strip_tac
  >- (`valid_horizon cx st0 H (es with gas_obs := obs).storage_trace`
        suffices_by simp[] >> metis_tac[valid_horizon_frame,word_head_frame]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (drule_then (strip_assume_tac o BETA_RULE o REWRITE_RULE [word_head_post_def,expr_sim_full_post_def])) >>
  fs[expr_post_def]
QED

Theorem word_args_cons_landing[local]:
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    word_head_post (DF,lo,d,C,f) ce cx e (es,a,m,s,x,G0,tn0) H (INL v) mid G1 tn1 t) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H C f ce cx es s) /\
  local_ptrs_reserved ce a /\ MAP FDOM es.scopes = MAP FDOM mid.scopes /\
  a.cs_next_var <= m.cs_next_var /\ a.cs_next_id <= m.cs_next_id /\
  is_word_type (expr_type e) /\ evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  (!z. x = Var z ==> not_fresh_at m z) /\ (!l. x <> Label l) /\
  eval_exprs cx todo (mid with gas_obs := obs) = (INL vs, fin) /\
  valid_horizon cx st0 H fin.storage_trace /\
  selected_word_args_post (DF,lo,d,C,f) ce cx (mid,m,b,t,todo,xs,G1,tn1)
     H (INL vs) fin G tn u ==>
  selected_word_args_post (DF,lo,d,C,f) ce cx (es,a,b,s,e::todo,x::xs,G0,tn0)
     H (INL (v::vs)) fin G tn u
Proof
  strip_tac >>
  `valid_horizon cx st0 H mid.storage_trace` by
    (`valid_horizon cx st0 H (mid with gas_obs := obs).storage_trace`
       suffices_by simp[] >> metis_tac[valid_horizon_frame,evaluate_storage_trace_frame]) >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
    (drule_then (strip_assume_tac o BETA_RULE o REWRITE_RULE [word_head_post_def,expr_sim_full_post_def])) >>
  `valid_horizon cx st0 H es.storage_trace` by
    (rename1 `bind (eval_expr cx e) (read_result cx) (es with gas_obs := obs1) = _` >>
     `valid_horizon cx st0 H (es with gas_obs := obs1).storage_trace`
       suffices_by simp[] >> metis_tac[valid_horizon_frame,word_head_frame]) >>
  `stmt_state_rel H C f ce cx es s` by metis_tac[] >>
  `op_taint tn1 x = {}` by fs[bodyPtrDefsTheory.ptr_val_ok_def] >>
  fs[selected_word_args_post_def,expr_sim_full_endpoint_def] >>
  drule_all word_args_cons_post >> simp[] >> decide_tac
QED

Theorem word_args_cut_map[local]:
  create_operand_cut a b E C f tops cx st0 (eval_exprs cx todo) (es,s) ==>
  create_operand_cut a b E C f tops cx st0
    (bind (eval_exprs cx todo) (\vs. return (v::vs))) (es,s)
Proof
  simp[create_operand_cut_def] >> rpt strip_tac >>
  irule create_cut_bind_left >> simp[storage_trace_frame_return] >> metis_tac[]
QED

Theorem word_args_cons_cut[local]:
  body_inv tops C ce cx /\ MEM f C.ctx_functions /\
  create_cut_code {} a m /\ fn_has_code a m f /\
  create_cut_code {} m b /\ fn_has_code m b f /\ ~s.vs_halted /\
  create_operand_cut a m E C f tops cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s) /\
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a m
    (bind (eval_expr cx e) (read_result cx)) (es,s,G0,tn0)
    (word_head_post (DF,lo,d,C,f) ce cx e (es,a,m,s,x,G0,tn0)) R /\
  (!v mid G tn t.
    (?H0. valid_horizon cx st0 H0 mid.storage_trace) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      word_head_post (DF,lo,d,C,f) ce cx e (es,a,m,s,x,G0,tn0) H (INL v) mid G tn t) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      ?marks. gas_origin_ptr_path (DF H,lo,E,C,f,PG) (s,G0,tn0) marks (OK t,G,tn)) ==>
    create_operand_cut m b E C f tops cx st0 (eval_exprs cx todo) (mid,t)) ==>
  create_operand_cut a b E C f tops cx st0 (eval_exprs cx (e::todo)) (es,s)
Proof
  strip_tac >> simp[eval_exprs_cons_action] >> irule create_operand_cut_bind_replay >>
  `!bb. MEM bb f.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0`
    by metis_tac[body_inv_no_phi] >>
  drule_all scoped_outcome_completed_operand >> strip_tac >>
  first_assum (irule_at Any) >> first_assum (irule_at Any) >>
  simp[word_return_frame] >> rpt conj_tac
  >- (rpt strip_tac >> drule_all create_interior_visit_first_exit >> metis_tac[])
  >- (rpt strip_tac >> irule word_args_cut_map >>
      qpat_assum `!v mid G tn t. _ ==> create_operand_cut _ _ _ _ _ _ _ _ _ _`
        (qspecl_then [`v`,`mid with gas_obs := []`,`G`,`tn`,`t`] mp_tac) >> simp[] >>
      metis_tac[]) >>
  rpt strip_tac >> fs[word_head_post_def,expr_sim_full_post_def]
QED

Theorem word_args_code[local]:
  !todo a xs b. lower_word_args ce tyf todo a = (xs,b) ==> create_cut_code {} a b
Proof
  Induct >> simp[lower_word_args_nil] >> rpt gen_tac >> rw[lower_word_args_cons] >>
  metis_tac[cj 2 create_operand_cut_code, create_cut_code_join, pairTheory.SND]
QED

Theorem word_args_empty[local]:
  create_operand_at a s /\ ~s.vs_halted /\ alloca_history f s /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H C f ce cx es s /\ storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d ce cx es G tn s) ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a a (eval_exprs cx []) (es,s,G,tn)
    (selected_word_args_post (DF,lo,d,C,f) ce cx (es,a,a,s,[],[],G,tn))
    (selected_word_args_exit C cx) /\
  create_operand_cut a a E C f tops cx st0 (eval_exprs cx []) (es,s)
Proof
  strip_tac >> conj_tac
  >- (irule scoped_operand_pure >> simp[eval_exprs_nil] >>
      qexistsl [`es`,`INL []`] >> simp[] >> rpt strip_tac >>
      first_x_assum drule >> strip_tac >>
      `storage_well_formed_on cx (es with gas_obs := []) (FST H)` by
        (`storage_well_formed_on cx (es with gas_obs := []) (FST H) =
           storage_well_formed_on cx es (FST H)` suffices_by simp[] >>
         irule storage_well_formed_on_backends >> simp[]) >>
      `ghost_inv_at (DF H) lo d ce cx (es with gas_obs := []) G tn s` by
        (qpat_x_assum `ghost_inv_at _ _ _ _ _ _ _ _ _` mp_tac >>
         rewrite_tac[ghost_inv_at_def] >> strip_tac >> simp[] >> first_assum ACCEPT_TAC) >>
      fs[selected_word_args_post_def,typed_args_post_def,wb_frame_refl,
         expr_sim_full_endpoint_def,create_operand_at_def,ghost_kept_at_def]) >>
  simp[create_operand_cut_def] >> metis_tac[create_operand_empty_scope]
QED

Theorem word_head_for_bind[local]:
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a m
    (bind (eval_expr cx e) (read_result cx)) (es,s,G0,tn0)
    (word_head_post (DF,lo,d,C,f) ce cx e (es,a,m,s,x,G0,tn0))
    (\H r ee gt u. (?exc. r = INR exc) /\ selected_word_args_exit C cx H r ee gt u) ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a m
    (bind (eval_expr cx e) (read_result cx)) (es,s,G0,tn0)
    (\H r ee G tn t. ?v. r = INL v /\
      word_head_post (DF,lo,d,C,f) ce cx e (es,a,m,s,x,G0,tn0) H (INL v) ee G tn t /\
      ?ms. gas_origin_ptr_path (DF H,lo,E,C,f,PG) (s,G0,tn0) ms (OK t,G,tn))
    (\H r ee gt u. ?exc. r = INR exc /\
      selected_word_args_exit C cx H (INR exc : value list + exception) ee gt u)
Proof
  rewrite_tac[scoped_operand_outcome_def] >>
  disch_then (qx_choose_then `marks` strip_assume_tac) >> qexists_tac `marks`
  >- metis_tac[]
  >- (disj2_tac >> disj1_tac >> qexistsl [`res`,`ee`,`r`,`G'`,`tn'`] >> simp[] >>
      rpt strip_tac >> first_x_assum drule >> strip_tac >> simp[]
      >- (`?v. res = INL v` by fs[word_head_post_def,expr_sim_full_post_def] >>
          metis_tac[]) >>
      gvs[selected_word_args_exit_def,wb_args_exit_def,halt_exit_def]) >>
  metis_tac[]
QED

Theorem word_args_cons_outcome[local]:
  body_inv tops C ce cx /\ MEM f C.ctx_functions /\
  create_cut_code {} a m /\ fn_has_code a m f /\
  create_cut_code {} m b /\ fn_has_code m b f /\ create_layout a b /\
  create_operand_at a s /\
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a m
    (bind (eval_expr cx e) (read_result cx)) (es,s,G0,tn0)
    (word_head_post (DF,lo,d,C,f) ce cx e (es,a,m,s,x,G0,tn0))
    (\H r ee gt u. (?exc. r = INR exc) /\ selected_word_args_exit C cx H r ee gt u) /\
  (!v mid G tn t.
    (?H0. valid_horizon cx st0 H0 mid.storage_trace) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      word_head_post (DF,lo,d,C,f) ce cx e (es,a,m,s,x,G0,tn0) H (INL v) mid G tn t) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      ?marks. gas_origin_ptr_path (DF H,lo,E,C,f,PG) (s,G0,tn0) marks (OK t,G,tn)) ==>
    scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 m b
      (bind (eval_exprs cx todo) (\vs. return (v::vs))) (mid,t,G,tn)
      (selected_word_args_post (DF,lo,d,C,f) ce cx (es,a,b,s,e::todo,x::xs,G0,tn0))
      (selected_word_args_exit C cx)) ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a b (eval_exprs cx (e::todo))
    (es,s,G0,tn0) (selected_word_args_post (DF,lo,d,C,f) ce cx (es,a,b,s,e::todo,x::xs,G0,tn0))
    (selected_word_args_exit C cx)
Proof
  strip_tac >> drule_all word_args_cons_scope >> strip_tac >>
  drule_then assume_tac word_head_for_bind >>
  simp[eval_exprs_cons_action] >> irule scoped_operand_bind >>
  simp[word_head_frame,word_return_frame] >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (simp[stmtSimForcedTheory.ignore_bind_bind_value] >> rpt strip_tac >>
      irule gas_exempt_cert_bind_value >> qexistsl [`mid`,`t`,`v`] >> simp[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
  >- (simp[stmtSimForcedTheory.ignore_bind_bind_value] >> rpt strip_tac >>
      irule gas_exempt_cert_error_value >> simp[]) >>
  qexistsl [`\H v ee G tn t.
    word_head_post (DF,lo,d,C,f) ce cx e (es,a,m,s,x,G0,tn0) H (INL v) ee G tn t /\
    ?ms. gas_origin_ptr_path (DF H,lo,E,C,f,PG) (s,G0,tn0) ms (OK t,G,tn)`, `m`] >>
  simp[] >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!v mid G tn t. _ ==> scoped_operand_outcome _ _ _ _ _ _ _ _ _ _`
        irule >> simp[] >> fs[storage_trace_domain_def] >> metis_tac[]) >>
  rpt strip_tac >> metis_tac[]
QED

(* The guarded child supplier is used at the paired compilation split, not
   at an independently chosen run of the list or of its first argument. *)
Theorem raw_call_words_selected:
  !todo a b sa sb xs es s G0 tn0.
    (!e. tyf (gas_shadow_expr e) = tyf e) /\
    (!e ee. MEM e todo /\ expr_sim_inv ce cx env ee ==>
      expr_body_pre ce cx env e ee /\ is_word_type (expr_type e)) /\
    (!e ee. MEM e todo /\ expr_body_pre ce cx env e ee /\
      body_const_cells_agree [(NONE,tops)] cx env ee ==>
      !a m sa sm x t G tn.
        expr_sim_full_pre (DF,lo,d,C,shC,PG,f,shf) ce cx (tyf e) e ee
          (st0,a,m,sa,sm,x,t,G,tn) /\ create_layout a m ==>
        scoped_operand_outcome (DF,lo,gas_explicit_sites C shC,C,f,PG) tops cx st0 a m
          (bind (eval_expr cx e) (read_result cx)) (ee,t,G,tn)
          (expr_sim_full_post (DF,lo,d,C,f) ce cx e (ee,a,m,t,x,G,tn))
          (create_operand_exit_post C cx) /\
        create_operand_cut a m (gas_explicit_sites C shC) C f tops cx st0
          (bind (eval_expr cx e) (read_result cx)) (ee,t)) /\
    body_inv tops C ce cx /\ body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_sim_inv ce cx env es /\
    lower_word_args ce tyf todo a = (xs,b) /\
    lower_word_args (gas_shadow_env T ce) tyf (MAP gas_shadow_expr todo) sa = (xs,sb) /\
    expr_sim_full_code (C,shC,f,shf) (a,b,sa,sb) /\ create_layout a b /\
    local_ptrs_reserved ce a /\
    (!H. dead_lo_ok H (DF H) lo ce cx) /\
    (!z sz. ce.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at a z) /\
    (!z sz. ce.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at a z) /\
    return_buf_frame d ce a s /\ alloca_history f s /\
    (ctx_has_dalloca C ==> allocas_below_fmp s) /\
    (!fn inst s'. frag_reachable C f s fn inst s' ==> dalloca_fmp_headroom inst s') /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H C f ce cx es s /\ storage_well_formed_on cx es (FST H) /\
      ghost_inv_at (DF H) lo d ce cx es G0 tn0 s) /\
    ~s.vs_halted /\ create_operand_at a s ==>
  scoped_operand_outcome (DF,lo,gas_explicit_sites C shC,C,f,PG) tops cx st0 a b
    (eval_exprs cx todo) (es,s,G0,tn0)
    (selected_word_args_post (DF,lo,d,C,f) ce cx (es,a,b,s,todo,xs,G0,tn0))
    (selected_word_args_exit C cx) /\
  create_operand_cut a b (gas_explicit_sites C shC) C f tops cx st0 (eval_exprs cx todo) (es,s)
Proof
  Induct >- (simp[lower_word_args_nil] >> metis_tac[word_args_empty]) >>
  rpt gen_tac >> strip_tac >>
  rename1 `lower_word_args ce tyf (e::todo) a = (xs,b)` >>
  `expr_body_pre ce cx env e es /\ is_word_type (expr_type e)` by metis_tac[MEM] >>
  gvs[lower_word_args_cons,MAP] >>
  rename1 `lower_value compile_expr ce (tyf e) e a = (x,m)` >>
  rename1 `lower_value compile_expr (gas_shadow_env T ce) (tyf e) (gas_shadow_expr e) sa = (x,sm)` >>
  rename1 `lower_word_args ce tyf todo m = (xs,b)` >>
  `create_cut_code {} a m /\ create_cut_code {} m b /\
   create_cut_code {} sa sm /\ create_cut_code {} sm sb` by
    metis_tac[cj 2 create_operand_cut_code,word_args_code,pairTheory.SND] >>
  `cs_extends a m /\ cs_extends m b /\ cs_extends sa sm /\ cs_extends sm sb` by
    fs[create_cut_code_def] >>
  `create_layout a m /\ create_layout m b` by
    metis_tac[create_layout_subinterval,cs_extends_refl] >>
  `a.cs_next_var <= m.cs_next_var /\ a.cs_next_id <= m.cs_next_id /\
   (!z. x = Var z ==> not_fresh_at m z) /\ (!l. x <> Label l)` by
    metis_tac[expr_body_pre_lower_value_word_shape] >>
  `gas_shadow_state m sm` by
    (`gas_shadow_state (SND (lower_value compile_expr ce (tyf e) e a))
        (SND (lower_value compile_expr (gas_shadow_env T ce) (tyf e) (gas_shadow_expr e) sa))`
       suffices_by simp[] >>
     irule (cj 2 (REWRITE_RULE [gas_shadow_compiles_def] gas_shadow_stmt_lower_value_env)) >>
     fs[expr_sim_full_code_def]) >>
  `expr_sim_full_code (C,shC,f,shf) (a,m,sa,sm) /\
   expr_sim_full_code (C,shC,f,shf) (m,b,sm,sb)` by
    (fs[expr_sim_full_code_def] >> metis_tac[fn_has_code_mid,cs_extends_refl]) >>
  `expr_sim_full_pre (DF,lo,d,C,shC,PG,f,shf) ce cx (tyf e) e es
     (st0,a,m,sa,sm,x,s,G0,tn0)` by
    (fs[expr_sim_full_pre_def,expr_sim_full_code_def,create_operand_at_def] >>
     metis_tac[expr_body_pre_gas_admissible]) >>
  `expr_body_pre ce cx env e es` by metis_tac[] >>
  `scoped_operand_outcome (DF,lo,gas_explicit_sites C shC,C,f,PG) tops cx st0 a m
     (bind (eval_expr cx e) (read_result cx)) (es,s,G0,tn0)
     (expr_sim_full_post (DF,lo,d,C,f) ce cx e (es,a,m,s,x,G0,tn0))
     (create_operand_exit_post C cx) /\
   create_operand_cut a m (gas_explicit_sites C shC) C f tops cx st0
     (bind (eval_expr cx e) (read_result cx)) (es,s)` by
    (qpat_assum `!e' ee. _ ==> !a m sa sm x t G tn. _`
       (qspecl_then [`e`,`es`] mp_tac) >> simp[] >>
     disch_then irule >> simp[] >> qexistsl [`sa`,`sm`] >> simp[]) >>
  drule_then assume_tac word_head_scoped >>
  qabbrev_tac `E = gas_explicit_sites C shC` >>
  `MEM f C.ctx_functions /\ fn_has_code a m f /\ fn_has_code m b f` by
    fs[expr_sim_full_code_def] >>
  `!bb. MEM bb f.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0`
    by metis_tac[body_inv_no_phi] >>
  `?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv`
    by metis_tac[expr_body_pre_type_evaluates,optionTheory.IS_SOME_EXISTS] >>
  `!v mid G1 tn1 t.
     (?H0. valid_horizon cx st0 H0 mid.storage_trace) /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==>
       word_head_post (DF,lo,d,C,f) ce cx e (es,a,m,s,x,G0,tn0) H (INL v) mid G1 tn1 t) /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==>
       ?marks. gas_origin_ptr_path (DF H,lo,E,C,f,PG) (s,G0,tn0) marks (OK t,G1,tn1)) ==>
     scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 m b
       (bind (eval_exprs cx todo) (\vs. return (v::vs))) (mid,t,G1,tn1)
       (selected_word_args_post (DF,lo,d,C,f) ce cx (es,a,b,s,e::todo,x::xs,G0,tn0))
       (selected_word_args_exit C cx) /\
     create_operand_cut m b E C f tops cx st0 (eval_exprs cx todo) (mid,t)` by
    (rpt gen_tac >> strip_tac >> drule_all word_head_ready_tail >> strip_tac >>
     `!fn inst s'. frag_reachable C f t fn inst s' ==> dalloca_fmp_headroom inst s'` by
       (qpat_assum `!H. _ ==> ?marks. gas_origin_ptr_path _ _ _ _` (drule_then strip_assume_tac) >>
        drule gas_origin_ptr_path_dalloca_fmp_headroom >> simp[] >> metis_tac[]) >>
     `scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 m b
        (eval_exprs cx todo) (mid,t,G1,tn1)
        (selected_word_args_post (DF,lo,d,C,f) ce cx (mid,m,b,t,todo,xs,G1,tn1))
        (selected_word_args_exit C cx) /\
      create_operand_cut m b E C f tops cx st0 (eval_exprs cx todo) (mid,t)` by
       (`?sa' sb'. lower_word_args (gas_shadow_env T ce) tyf
               (MAP gas_shadow_expr todo) sa' = (xs,sb') /\
             expr_sim_full_code (C,shC,f,shf) (m,b,sa',sb')` by
          (qexistsl [`sm`,`sb`] >> simp[]) >>
        qpat_assum `!a b sa sb xs es s G tn. _ ==> _ /\ _` irule >>
        fs[expr_sim_full_endpoint_def,create_operand_at_def] >> rpt conj_tac >>
        metis_tac[local_ptrs_reserved_next_var,not_fresh_at_mono]) >>
     conj_tac >- (irule words_cons_map >>
       qpat_assum `scoped_operand_outcome _ _ _ _ m b (eval_exprs _ _) _ _ _` (irule_at Any) >>
       simp[selected_word_args_exit_def,wb_args_exit_def,halt_exit_def] >> rpt conj_tac
       >- simp[selected_word_args_post_def] >>
       rpt gen_tac >> strip_tac >>
       `!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H C f ce cx es s` by simp[] >>
       drule_all_then ACCEPT_TAC word_args_cons_landing) >>
     first_assum ACCEPT_TAC) >>
  conj_tac
  >- (irule word_args_cons_outcome >>
      qpat_assum `scoped_operand_outcome _ _ _ _ _ m _ _ (word_head_post _ _ _ _ _) _` (irule_at Any) >>
      simp[] >> metis_tac[]) >>
  irule word_args_cons_cut >>
  qpat_assum `scoped_operand_outcome _ _ _ _ _ m _ _ (word_head_post _ _ _ _ _) _` (irule_at Any) >>
  simp[] >> metis_tac[]
QED

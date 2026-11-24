(* Positional requests: the head snapshot is retained through the actual tail. *)
Theory entryCreateExtPosList
Ancestors
  createCtorSavedCons bodySingletonCallSupport
  entryCreateCompositeFocus entryCreateNativeFirstExit createSizeOperandCode
  createSizeConcreteSnapshots createSizeCutOpens gasShadowCompileStmtHelpers
  gasShadowCompileConvert fragGasPathFrameMem exprSimWordArgs
  entryCreateFocusSpec entryCreateCompletedCut createSizePrefixReplay
  bodyFullExtCallPosList vyperState vyperStorageFootprint vyperStorageTrace
  wordArgsPtr loweringPosts bodyPtrDefs exprLoweringProps exprLowering compileEnv
  createSizeCutCode fragGasOriginPtr fragGasOrigin fragGasPath gasStorage
  gasExemptCert gasSummary gasSummaryCompose venomExecSemantics
  bodyFullIfExpReach fragGasMode fragExec exprSimDefs stmtSimProps vyperInterpreter
  entryCreateBodyCut createExprSizeExitDefs list bodyFullPreds exprSimSource
  exprSimHypsDefs gasShadowState gasShadowCompile gasShadowCompileHelpers
  gasExplicitSites entryCreateExtPosConsScope

Theorem pos_list_empty[local]:
  expr_sim_inv ce cx env es /\ return_buf_frame d ce a s /\
  alloca_history f s /\ ~s.vs_halted /\ create_operand_at a s /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H C f ce cx es s /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d ce cx es G tn s) ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a a
    (eval_exprs cx []) (es,s,G,tn)
    (extcall_positional_post keep DF lo d C f ce cx env kw [] [] a a es s G tn)
    (create_operand_exit_post C cx) /\
  create_operand_cut a a E C f tops cx st0 (eval_exprs cx []) (es,s)
Proof
  strip_tac >> reverse conj_tac
  >- (simp[create_operand_cut_def] >> metis_tac[create_operand_empty_scope]) >>
  irule scoped_operand_pure >> simp[eval_exprs_nil, return_def] >>
  qexistsl_tac [`es`,`INL ([] : value list)`] >> simp[return_def] >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  `storage_well_formed_on cx (es with gas_obs := []) (FST H) <=>
   storage_well_formed_on cx es (FST H)` by
    (irule storage_well_formed_on_backends >> simp[]) >>
  fs[extcall_positional_post_def, create_operand_at_def, wb_frame_refl,
     ghost_kept_at_refl, ghost_inv_at_def, pure_frame_def] >> first_assum ACCEPT_TAC
QED

Theorem pos_list_layout[local]:
  compile_ext_call_args compile_expr ce kw (MAP (lowered_value_type ce) xs) xs a = (svs,b) ==>
  ci_mono a b /\ create_cut_code {} a b
Proof
  map_every qid_spec_tac [`b`,`a`,`svs`] >> Induct_on `xs`
  >- simp[compile_ext_call_args_def,comp_return_def,ci_mono_refl,create_cut_code_refl] >>
  rpt gen_tac >> simp[Once compile_ext_call_args_def,comp_bind_def,comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  rename1 `compile_expr ce (expr_type h) h a = (vv,i)` >>
  rename1 `compile_snapshot_vv _ _ _ i = (_,m)` >>
  `ci_mono a i /\ create_cut_code {} a i` by
    (qpat_assum `compile_expr _ _ _ a = _` mp_tac >>
     metis_tac[cj 1 compile_expr_ci_mono,cj 1 create_operand_cut_code,pairTheory.SND]) >>
  `ci_mono i m /\ create_cut_code {} i m` by
    (qpat_assum `compile_snapshot_vv _ _ _ i = _` mp_tac >>
     metis_tac[ci_mono_compile_snapshot_vv,create_vv_snapshot_cut_code,pairTheory.SND]) >>
  `ci_mono m b /\ create_cut_code {} m b` by metis_tac[] >>
  metis_tac[ci_mono_trans,create_cut_code_join]
QED

(* A source-only cons does not insert a target instruction or change marks.
   Keep the tail equation and label frame when strengthening its post. *)
Theorem pos_list_cons_source[local]:
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 m b
    (eval_exprs cx xs) (mid,t,G1,tn1) Q (create_operand_exit_post C cx) /\
  (!obs vs ee G2 tn2 u.
    eval_exprs cx xs (mid with gas_obs := obs) = (INL vs,ee with gas_obs := []) /\
    u.vs_labels = t.vs_labels /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
        Q H (INL vs) (ee with gas_obs := []) G2 tn2 u) ==>
    !H. valid_horizon cx st0 H ee.storage_trace ==>
       Q' H (INL (v::vs)) (ee with gas_obs := []) G2 tn2 u) /\
  (!H exc ee G2 tn2 u. ~Q H (INR exc) ee G2 tn2 u) ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 m b
    (bind (eval_exprs cx xs) (\vs. return (v::vs))) (mid,t,G1,tn1)
    Q' (create_operand_exit_post C cx)
Proof
  strip_tac >>
  `!x. bind (eval_exprs cx xs) (\vs. return (v::vs)) x =
       (sum$SUM_MAP (CONS v) I (FST (eval_exprs cx xs x)), SND (eval_exprs cx xs x))` by
    (gen_tac >> Cases_on `eval_exprs cx xs x` >> Cases_on `q` >>
     simp[bind_def,return_def,sumTheory.SUM_MAP_def]) >>
  `ignore_bind (bind (eval_exprs cx xs) (\vs. return (v::vs))) (return ()) =
   ignore_bind (eval_exprs cx xs) (return ())` by
    simp[ignore_bind_def,bind_assoc,bind_def,return_def,FUN_EQ_THM] >>
  qpat_x_assum `scoped_operand_outcome _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [scoped_operand_outcome_def]) >>
  rewrite_tac[scoped_operand_outcome_def] >> qexists_tac `marks`
  >- (disj1_tac >> simp[] >> conj_tac >- fs[gas_bad_storage_at_def] >>
      qexistsl_tac [`H`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish'`] >> simp[])
  >- (disj2_tac >> disj1_tac >>
      qexistsl_tac [`sum$SUM_MAP (CONS v) I res`,`ee`,`r`,`G'`,`tn'`] >>
      simp[] >>
      `!H. valid_horizon cx st0 H ee.storage_trace ==>
            gas_origin_ptr_path (DF H,lo,E,C,f,PG) (t,G1,tn1) marks (r,G',tn')` by
        (rpt strip_tac >> res_tac >> simp[]) >>
      Cases_on `r` >> gvs[exit_result_def] >>
      Cases_on `res` >> gvs[sumTheory.SUM_MAP_def] >>
      TRY (rpt strip_tac >> res_tac >>
        fs[create_operand_exit_post_def,expr_exit_def,halt_exit_def] >> NO_TAC) >>
      rpt strip_tac >> simp[] >>
      first_x_assum irule >>
      qpat_assum `!tail. eval_exprs cx xs _ = _` (qspec_then `[]` assume_tac) >>
      simp[] >> conj_tac
      >- (fs[create_operand_full_scope_def] >> metis_tac[create_prefix_labels]) >>
      qexists_tac `gas_explicit marks t.vs_gas_readings` >> fs[]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

Theorem pos_list_read_frame[local]:
  storage_trace_frame (bind (eval_expr cx e) (read_result cx)) /\
  storage_trace_frame (eval_exprs cx xs) /\
  storage_trace_frame (bind (eval_exprs cx xs) (\vs. return (v::vs)))
Proof
  simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
       storage_trace_frame_read_result, storage_trace_frame_return]
QED

Theorem pos_list_cut_right[local]:
  ~s.vs_halted /\ create_operand_at m t /\ before = front ++ back /\
  create_expr_prefix a m E C f s (create_cut_marks E front) t /\
  (!bb. MEM bb f.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a m
    (bind (eval_expr cx e) (read_result cx)) (es,s,G0,tn0) Q
    (create_operand_exit_post C cx) /\
  (!obs v mid G1 tn1.
    bind (eval_expr cx e) (read_result cx) (es with gas_obs := obs) =
      (INL v,mid with gas_obs := []) /\
    (?H. valid_horizon cx st0 H mid.storage_trace) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      Q H (INL v) (mid with gas_obs := []) G1 tn1 t /\
      gas_origin_ptr_path (DF H,lo,E,C,f,PG) (s,G0,tn0)
        (create_cut_marks E front) (OK t,G1,tn1)) ==>
    create_body_cut E tops cx st0 (eval_exprs cx xs) (mid with gas_obs := [],t) (back,hit)) /\
  (!H r ee G tn. Q H r ee G tn t ==> ?v. r = INL v) ==>
  create_body_cut E tops cx st0 (eval_exprs cx (e::xs)) (es,s) (before,hit)
Proof
  strip_tac >>
  drule_all scoped_completed_operand_landing >>
  simp[gas_completed_operand_def] >> strip_tac >>
  drule_all create_prefix_gas_path >>
  disch_then (assume_tac o Q.INST [`right` |-> `create_cut_marks E back`] o
              MATCH_MP gas_explicit_append_path) >>
  fs[create_operand_at_def] >>
  pure_rewrite_tac[create_body_cut_def,create_cut_marks_append,eval_exprs_cons_action] >>
  qpat_assum `gas_explicit _ _ = _` (fn th =>
    pure_rewrite_tac[th,GSYM APPEND_ASSOC]) >>
  simp_tac bool_ss [] >>
  rpt gen_tac >> disch_tac >> rpt gen_tac >>
  qabbrev_tac `obs = gas_explicit (create_cut_marks E front) s.vs_gas_readings` >>
  qabbrev_tac `suffix = gas_explicit (create_cut_marks E back) t.vs_gas_readings ++ tail` >>
  qabbrev_tac `head = bind (eval_expr cx e) (read_result cx)` >>
  Cases_on `head (es with gas_obs := obs ++ suffix)` >>
  rename1 `head _ = (rh,mid)` >>
  strip_tac >>
  `valid_horizon cx st0 H mid.storage_trace` by
    (qpat_assum `bind head _ _ = _` mp_tac >> pure_once_rewrite_tac[bind_def] >>
     Cases_on `rh` >> simp[] >> rpt strip_tac >> gvs[] >>
     drule_at Any valid_horizon_frame >> simp[pos_list_read_frame]) >>
  qpat_x_assum `!H0 marks t' tail res ee. _` (qspecl_then
    [`H`,`create_cut_marks E front`,`t`,`suffix`,`rh`,`mid`] mp_tac) >>
  simp[GSYM (markerTheory.Abbrev_def)] >>
  disch_then (DISJ_CASES_THEN2 (qx_choosel_then [`G1`,`tn1`] strip_assume_tac)
                              strip_assume_tac)
  >- (`?v. rh = INL v` by
        (qpat_assum `!K. valid_horizon cx st0 K mid.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
           (drule_then strip_assume_tac) >>
         qpat_assum `!H r ee G tn. Q H r ee G tn t ==> _` (drule_then ACCEPT_TAC)) >>
      pop_assum SUBST_ALL_TAC >>
      qpat_assum `!obs v mid G1 tn1. _` (qspecl_then [`obs`,`v`,`mid`,`G1`,`tn1`] mp_tac) >>
      (impl_tac >-
        (fs[Abbr `obs`] >> reverse conj_tac >- metis_tac[] >>
         qpat_assum `!K. valid_horizon _ _ K mid.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
           (drule_then strip_assume_tac) >>
         qpat_assum `!left. create_expr_prefix _ _ _ _ _ _ left _ ==> _`
           (drule_then strip_assume_tac) >>
         qpat_assum `!tail'. head _ = _`
           (qspec_then `[]` (ACCEPT_TAC o REWRITE_RULE [APPEND_NIL])))) >>
      simp[create_body_cut_def] >> disch_then (qspecl_then [`H`,`tail`] mp_tac) >>
      qpat_x_assum `bind head _ _ = _` mp_tac >>
      pure_once_rewrite_tac[bind_def] >> simp[Abbr `suffix`] >>
      `mid with gas_obs := gas_explicit (create_cut_marks E back) t.vs_gas_readings ++ tail = mid` by
        (qpat_assum `mid.gas_obs = _` (SUBST1_TAC o SYM) >> simp[]) >>
      simp[] >> rpt strip_tac >> Cases_on `eval_exprs cx xs mid` >> Cases_on `q` >>
      fs[bind_def,return_def,create_cut_failure_def] >> metis_tac[]) >>
  qpat_x_assum `bind head _ _ = _` mp_tac >>
  simp[bind_def,create_cut_failure_def] >> strip_tac >> gvs[] >> metis_tac[]
QED

Definition extcall_pos_entry_def:
  extcall_pos_entry DF lo d st0 C f ce cx env a es s G tn <=>
    expr_sim_inv ce cx env es /\ return_buf_frame d ce a s /\
    alloca_history f s /\ ~s.vs_halted /\ create_operand_at a s /\
    (!fn i u. frag_reachable C f s fn i u ==> dalloca_fmp_headroom i u) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H C f ce cx es s /\
      storage_well_formed_on cx es (FST H) /\
      ghost_inv_at (DF H) lo d ce cx es G tn s)
End

Definition extcall_pos_head_post_def:
  extcall_pos_head_post keep DF lo d C f ce cx env rest e sv a m es s G tn
    H (r : value + exception) ee G1 tn1 t <=>
    ?v. r = INL v /\ extcall_positional_post keep DF lo d C f ce cx env
      rest [e] [sv] a m es s G tn H (INL [v] : value list + exception) ee G1 tn1 t
End

(* Only a successful, horizon-valid head starts the tail. *)
Theorem pos_list_tail_entry[local]:
  extcall_pos_entry DF lo d st0 C f ce cx env a es s G tn /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  body_exprs_full_ok cx (e::xs) /\ expr_body_pre ce cx env e es /\
  (!bb. MEM bb f.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := obs) =
    (INL v,mid with gas_obs := []) /\
  (?H. valid_horizon cx st0 H mid.storage_trace) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    extcall_pos_head_post keep DF lo d C f ce cx env rest e sv a m es s G tn
      H (INL v) (mid with gas_obs := []) G1 tn1 t /\
    gas_origin_ptr_path (DF H,lo,E,C,f,PG) (s,G,tn) marks (OK t,G1,tn1)) ==>
  body_exprs_full_ok cx xs /\
  body_const_cells_agree [(NONE,tops)] cx env (mid with gas_obs := []) /\
  extcall_pos_entry DF lo d st0 C f ce cx env m (mid with gas_obs := []) t G1 tn1
Proof
  strip_tac >> rpt conj_tac
  >- (drule_then strip_assume_tac (REWRITE_RULE [ETA_AX] eval_expr_read_INL) >>
      fs[Once body_exprs_full_ok_def] >> metis_tac[])
  >- (irule body_const_cells_agree_expr_read >>
      qpat_assum `bind _ _ _ = (INL v,_)` (irule_at Any) >>
      fs[expr_body_pre_def]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
       return_buf_frame d ce m t /\ alloca_history f t /\
       expr_sim_inv ce cx env (mid with gas_obs := []) /\
       ~t.vs_halted /\ create_operand_at m t /\
       stmt_state_rel H C f ce cx (mid with gas_obs := []) t /\
       storage_well_formed_on cx (mid with gas_obs := []) (FST H) /\
       ghost_inv_at (DF H) lo d ce cx (mid with gas_obs := []) G1 tn1 t` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> extcall_pos_head_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then (strip_assume_tac o REWRITE_RULE [extcall_pos_head_post_def,extcall_positional_post_def])) >>
     fs[create_operand_at_def]) >>
  simp[extcall_pos_entry_def] >>
  `!fn i u. frag_reachable C f t fn i u ==> dalloca_fmp_headroom i u` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> extcall_pos_head_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     fs[extcall_pos_entry_def] >>
     rpt strip_tac >>
     drule_all gas_origin_ptr_path_dalloca_fmp_headroom >> simp[]) >>
  first_x_assum (drule_then strip_assume_tac) >> fs[] >> rpt strip_tac >> res_tac
QED

(* The geometry is the common binary scope introduction, at the two
   installed consecutive list intervals. No source or post is assumed. *)
Definition extcall_pos_scope_join_def:
  extcall_pos_scope_join E C f <=>
    !a m b s. create_cut_code {} a m /\ fn_has_code a m f /\
      create_cut_code {} m b /\ fn_has_code m b f /\ create_operand_at a s ==>
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
End

Theorem pos_list_shadow_head[local]:
  gas_shadow_state a sha /\
  compile_expr ce (expr_type e) e a = (vv,i) /\
  compile_snapshot_vv ce (exprs_can_mutate ce (xs ++ kw))
    (ext_call_arg_value (lowered_value_type ce e) vv) i = (sv,m) ==>
  ?shi shm.
    compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) sha = (vv,shi) /\
    compile_snapshot_vv ce (exprs_can_mutate ce (xs ++ kw))
       (ext_call_arg_value (lowered_value_type ce e) vv) shi = (sv,shm) /\
    gas_shadow_state i shi /\ gas_shadow_state m shm
Proof
  strip_tac >>
  `gas_shadow_compiles (compile_expr ce (expr_type e) e)
     (compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e))` by
    irule gas_shadow_stmt_compile_expr_env >>
  Cases_on `compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) sha` >>
  qpat_x_assum `gas_shadow_compiles _ _` (mp_tac o Q.SPECL [`a`,`sha`] o
    REWRITE_RULE [gas_shadow_compiles_def]) >> simp[] >> strip_tac >> gvs[] >>
  rename1 `gas_shadow_state i shi` >>
  rename1 `compile_expr ce (expr_type e) e a = (vv,i)` >>
  qabbrev_tac `snapshot = compile_snapshot_vv ce (exprs_can_mutate ce (xs ++ kw))
     (ext_call_arg_value (lowered_value_type ce e) vv)` >>
  `gas_shadow_compiles snapshot snapshot` by
    simp[Abbr `snapshot`,gas_shadow_compiles_snapshot_vv] >>
  Cases_on `snapshot shi` >>
  qpat_x_assum `gas_shadow_compiles snapshot snapshot` (mp_tac o Q.SPECL [`i`,`shi`] o
    REWRITE_RULE [gas_shadow_compiles_def]) >> simp[]
QED

Theorem pos_list_cons_post[local]:
  body_inv tops C ce cx /\ expr_body_pre ce cx env e es /\
  (!e' st. MEM e' xs /\ expr_sim_inv ce cx env st ==> expr_body_pre ce cx env e' st) /\
  local_ptrs_reserved ce a /\ local_ptrs_reserved ce m /\ ci_mono a m /\ ci_mono m b /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H C f ce cx es s) /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := obs0) = (INL v,mid) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    extcall_pos_head_post keep DF lo d C f ce cx env (xs ++ kw) e sv a m es s G tn
      H (INL v) mid G1 tn1 t) /\
  expr_sim_inv ce cx env mid /\
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 m b
    (eval_exprs cx xs) (mid,t,G1,tn1)
    (extcall_positional_post keep DF lo d C f ce cx env kw xs svs m b mid t G1 tn1)
    (create_operand_exit_post C cx) ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 m b
    (bind (eval_exprs cx xs) (\vs. return (v::vs))) (mid,t,G1,tn1)
    (extcall_positional_post keep DF lo d C f ce cx env kw (e::xs) (sv::svs) a b es s G tn)
    (create_operand_exit_post C cx)
Proof
  strip_tac >> irule pos_list_cons_source >> first_assum (irule_at Any) >>
  reverse conj_tac >- simp[extcall_positional_post_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  irule extcall_saved_rows_cons >> simp[] >> conj_tac
  >- (qexists_tac `tops` >> simp[bodyStorageCasesTheory.body_exprs_main_calls_every,EVERY_MEM] >>
      `!e'. MEM e' xs ==> expr_body_pre ce cx env e' mid` by simp[] >>
      rpt strip_tac >>
      qpat_assum `!e'. MEM e' xs ==> _` (drule_then assume_tac) >>
      drule_at (Pat `expr_body_pre _ _ _ e' mid`) body_inv_expr_pre_calls >>
      simp[EVERY_MEM] >> metis_tac[]) >>
  qexistsl_tac [`G1`,`m`,`mid`,`obs`,`[]`,`st0`,`t`,`tn1`] >> simp[] >>
  rpt conj_tac
  >- gvs[extcall_positional_post_INL]
  >- (rpt strip_tac >>
      qpat_assum `bind _ _ _ = (INL v,mid)` (mp_then Any mp_tac valid_horizon_frame) >>
      simp[pos_list_read_frame]) >>
  rpt strip_tac >> res_tac >> gvs[extcall_pos_head_post_def,extcall_positional_post_INL]
QED

Definition extcall_pos_row_rule_def:
  extcall_pos_row_rule allowed keep DF lo d C shC f shf PG tops cx st0 ce env <=>
    !e rest a i m sha shi shm es s G tn vv sv.
      allowed e /\ body_expr_full_ok cx e /\ expr_body_pre ce cx env e es /\
      body_const_cells_agree [(NONE,tops)] cx env es /\
      gas_shadow_state a sha /\ gas_shadow_state i shi /\ gas_shadow_state m shm /\
      compile_expr ce (expr_type e) e a = (vv,i) /\
      compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) sha = (vv,shi) /\
      compile_snapshot_vv ce (exprs_can_mutate ce rest)
        (ext_call_arg_value (lowered_value_type ce e) vv) i = (sv,m) /\
      compile_snapshot_vv ce (exprs_can_mutate ce rest)
        (ext_call_arg_value (lowered_value_type ce e) vv) shi = (sv,shm) /\
      fn_has_code a m f /\ fn_has_code sha shm shf /\ local_ptrs_reserved ce a /\
      (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
      (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
      extcall_pos_entry DF lo d st0 C f ce cx env a es s G tn ==>
      scoped_operand_outcome (DF,lo,gas_explicit_sites C shC,C,f,PG) tops cx st0 a m
        (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn)
        (extcall_pos_head_post keep DF lo d C f ce cx env rest e sv a m es s G tn)
        (create_operand_exit_post C cx) /\
      create_operand_cut a m (gas_explicit_sites C shC) C f tops cx st0
        (bind (eval_expr cx e) (read_result cx)) (es,s)
End

Definition extcall_pos_cons_rule_def:
  extcall_pos_cons_rule DF lo E C f PG tops cx st0 <=>
    !a m b e xs es s G tn P Q.
      (!marks. create_operand_focus_scope a m E C f s marks ==>
               create_operand_focus_scope a b E C f s marks) /\
      (!marks r. exit_result r /\ create_operand_full_scope a m E C f s marks r ==>
                 create_operand_full_scope a b E C f s marks r) /\
      (!left t right. create_operand_full_scope a m E C f s left (OK t) /\
          create_operand_focus_scope m b E C f t right ==>
          create_operand_focus_scope a b E C f s (left ++ right)) /\
      (!left t right r. create_operand_full_scope a m E C f s left (OK t) /\
          create_operand_full_scope m b E C f t right r ==>
          create_operand_full_scope a b E C f s (left ++ right) r) /\
      scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a m
        (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn) P (create_operand_exit_post C cx) /\
      (!H r ee G1 tn1 t. P H r ee G1 tn1 t ==> ?v. r = INL v) /\
      (!obs marks v mid G1 tn1 t.
        bind (eval_expr cx e) (read_result cx) (es with gas_obs := obs) =
          (INL v,mid with gas_obs := []) /\
        (?H. valid_horizon cx st0 H mid.storage_trace) /\
        (!H. valid_horizon cx st0 H mid.storage_trace ==>
          P H (INL v) (mid with gas_obs := []) G1 tn1 t /\
          gas_origin_ptr_path (DF H,lo,E,C,f,PG) (s,G,tn) marks (OK t,G1,tn1)) ==>
        scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 m b
          (bind (eval_exprs cx xs) (\vs. return (v::vs))) (mid with gas_obs := [],t,G1,tn1) Q
          (create_operand_exit_post C cx)) ==>
      scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a b
        (eval_exprs cx (e::xs)) (es,s,G,tn) Q (create_operand_exit_post C cx)
End

Theorem pos_list_cons_cut[local]:
  body_inv tops C ce cx /\ MEM f C.ctx_functions /\ ~s.vs_halted /\
  (!bb. MEM bb f.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  create_cut_code {} a m /\ fn_has_code a m f /\
  create_cut_code {} m b /\ fn_has_code m b f /\
  create_operand_cut a m E C f tops cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s) /\
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a m
    (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn) P (create_operand_exit_post C cx) /\
  (!H r ee G1 tn1 t. P H r ee G1 tn1 t ==> ?v. r = INL v) /\
  (!obs marks v mid G1 tn1 t.
    bind (eval_expr cx e) (read_result cx) (es with gas_obs := obs) =
      (INL v,mid with gas_obs := []) /\
    (?H. valid_horizon cx st0 H mid.storage_trace) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      P H (INL v) (mid with gas_obs := []) G1 tn1 t /\
      gas_origin_ptr_path (DF H,lo,E,C,f,PG) (s,G,tn) marks (OK t,G1,tn1)) ==>
    create_operand_cut m b E C f tops cx st0 (eval_exprs cx xs) (mid with gas_obs := [],t)) ==>
  create_operand_cut a b E C f tops cx st0 (eval_exprs cx (e::xs)) (es,s)
Proof
  strip_tac >> rewrite_tac[create_operand_cut_def] >> rpt gen_tac >> strip_tac >>
  drule_all create_interior_visit_first_exit >> strip_tac
  >- (irule create_cut_exprs_cons >> qexistsl_tac [`C`,`\h v ee g tn t. T`,`f`] >>
      disj1_tac >> fs[create_operand_cut_def] >> metis_tac[]) >>
  irule pos_list_cut_right >>
  qpat_assum `create_expr_prefix _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `scoped_operand_outcome _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >> reverse conj_tac >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  `create_operand_cut m b E C f tops cx st0 (eval_exprs cx xs) (mid with gas_obs := [],t)`
    by (first_x_assum irule >> conj_tac >- metis_tac[] >>
        qexistsl_tac [`G1`,`create_cut_marks E front`,`obs`,`tn1`,`v`] >> simp[]) >>
  fs[create_operand_cut_def] >> metis_tac[]
QED

Theorem pos_list_split[local]:
  gas_shadow_state a sha /\
  compile_ext_call_args compile_expr ce kw
    (MAP (lowered_value_type ce) (e::xs)) (e::xs) a = (svs,b) /\
  compile_ext_call_args compile_expr (gas_shadow_env T ce) (MAP gas_shadow_expr kw)
    (MAP (lowered_value_type ce) (MAP gas_shadow_expr (e::xs)))
    (MAP gas_shadow_expr (e::xs)) sha = (svs,shb) ==>
  ?vv i shi sv m shm rest.
    compile_expr ce (expr_type e) e a = (vv,i) /\
    compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) sha = (vv,shi) /\
    compile_snapshot_vv ce (exprs_can_mutate ce (xs ++ kw))
       (ext_call_arg_value (lowered_value_type ce e) vv) i = (sv,m) /\
    compile_snapshot_vv ce (exprs_can_mutate ce (xs ++ kw))
       (ext_call_arg_value (lowered_value_type ce e) vv) shi = (sv,shm) /\
    gas_shadow_state i shi /\ gas_shadow_state m shm /\ svs = sv::rest /\
    compile_ext_call_args compile_expr ce kw (MAP (lowered_value_type ce) xs) xs m = (rest,b) /\
    compile_ext_call_args compile_expr (gas_shadow_env T ce) (MAP gas_shadow_expr kw)
      (MAP (lowered_value_type ce) (MAP gas_shadow_expr xs))
      (MAP gas_shadow_expr xs) shm = (rest,shb)
Proof
  strip_tac >> Cases_on `compile_expr ce (expr_type e) e a` >>
  rename1 `compile_expr ce (expr_type e) e a = (vv,i)` >>
  Cases_on `compile_snapshot_vv ce (exprs_can_mutate ce (xs ++ kw))
     (ext_call_arg_value (lowered_value_type ce e) vv) i` >>
  rename1 `compile_snapshot_vv _ _ _ i = (sv,m)` >>
  drule_all pos_list_shadow_head >> strip_tac >>
  `exprs_can_mutate ce (MAP gas_shadow_expr xs ++ MAP gas_shadow_expr kw) =
    exprs_can_mutate ce (xs ++ kw)` by
      (pure_rewrite_tac[GSYM MAP_APPEND,gas_shadow_expr_can_mutate] >> REFL_TAC) >>
  qpat_x_assum `compile_ext_call_args _ ce _ _ (e::xs) a = _`
    (mp_tac o ONCE_REWRITE_RULE [compile_ext_call_args_def] o REWRITE_RULE [MAP]) >>
  qpat_x_assum `compile_ext_call_args _ _ _ _ _ sha = _`
    (mp_tac o ONCE_REWRITE_RULE [compile_ext_call_args_def] o REWRITE_RULE [MAP]) >>
  simp[comp_bind_def,comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem pos_list_head_code[local]:
  compile_expr ce (expr_type e) e a = (vv,i) /\
  compile_snapshot_vv ce copy (ext_call_arg_value (lowered_value_type ce e) vv) i = (sv,m) ==>
  ci_mono a m /\ create_cut_code {} a m
Proof
  strip_tac >>
  `ci_mono a i /\ create_cut_code {} a i` by
    (qpat_assum `compile_expr _ _ _ a = _` mp_tac >>
     metis_tac[cj 1 compile_expr_ci_mono,cj 1 create_operand_cut_code,pairTheory.SND]) >>
  `ci_mono i m /\ create_cut_code {} i m` by
    (qpat_assum `compile_snapshot_vv _ _ _ i = _` mp_tac >>
     metis_tac[ci_mono_compile_snapshot_vv,create_vv_snapshot_cut_code,pairTheory.SND]) >>
  metis_tac[ci_mono_trans,create_cut_code_join]
QED

Theorem pos_list_compile_mono[local]:
  (compile_expr c ty e a = (vv,i) /\ compile_snapshot_vv ce copy raw i = (sv,m) ==>
     ci_mono a m) /\
  (compile_ext_call_args compile_expr c kw tys xs m = (svs,b) ==> ci_mono m b)
Proof
  conj_tac
  >- (strip_tac >>
      `ci_mono a i` by metis_tac[cj 1 compile_expr_ci_mono,pairTheory.SND] >>
      `ci_mono i m` by metis_tac[ci_mono_compile_snapshot_vv,pairTheory.SND] >>
      metis_tac[ci_mono_trans]) >>
  strip_tac >>
  qspecl_then [`xs`,`tys`,`compile_expr`,`c`,`kw`,`m`] mp_tac ci_mono_compile_ext_call_args >>
  simp[cj 1 compile_expr_ci_mono]
QED

Theorem pos_list_cons_finish[local]:
  body_inv tops C ce cx /\ MEM f C.ctx_functions /\
  extcall_pos_scope_join E C f /\ extcall_pos_cons_rule DF lo E C f PG tops cx st0 /\
  local_ptrs_reserved ce a /\ local_ptrs_reserved ce m /\ ci_mono a m /\ ci_mono m b /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  body_exprs_full_ok cx (e::xs) /\ expr_body_pre ce cx env e es /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  (!e' st. MEM e' xs /\ expr_sim_inv ce cx env st ==> expr_body_pre ce cx env e' st) /\
  extcall_pos_entry DF lo d st0 C f ce cx env a es s G tn /\
  create_cut_code {} a m /\ fn_has_code a m f /\ create_cut_code {} m b /\ fn_has_code m b f /\
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a m
    (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn)
    (extcall_pos_head_post keep DF lo d C f ce cx env (xs ++ kw) e sv a m es s G tn)
    (create_operand_exit_post C cx) /\
  create_operand_cut a m E C f tops cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s) /\
  (!mid t G1 tn1. body_exprs_full_ok cx xs /\
    body_const_cells_agree [(NONE,tops)] cx env mid /\
    extcall_pos_entry DF lo d st0 C f ce cx env m mid t G1 tn1 ==>
    scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 m b
      (eval_exprs cx xs) (mid,t,G1,tn1)
      (extcall_positional_post keep DF lo d C f ce cx env kw xs svs m b mid t G1 tn1)
      (create_operand_exit_post C cx) /\
    create_operand_cut m b E C f tops cx st0 (eval_exprs cx xs) (mid,t)) ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a b
    (eval_exprs cx (e::xs)) (es,s,G,tn)
    (extcall_positional_post keep DF lo d C f ce cx env kw (e::xs) (sv::svs) a b es s G tn)
    (create_operand_exit_post C cx) /\
  create_operand_cut a b E C f tops cx st0 (eval_exprs cx (e::xs)) (es,s)
Proof
  strip_tac >>
  `!bb. MEM bb f.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[body_inv_no_phi] >>
  qabbrev_tac `P = extcall_pos_head_post keep DF lo d C f ce cx env (xs ++ kw) e sv a m es s G tn` >>
  `!obs marks v mid G1 tn1 t.
    bind (eval_expr cx e) (read_result cx) (es with gas_obs := obs) =
      (INL v,mid with gas_obs := []) /\
    (?H. valid_horizon cx st0 H mid.storage_trace) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      P H (INL v) (mid with gas_obs := []) G1 tn1 t /\
      gas_origin_ptr_path (DF H,lo,E,C,f,PG) (s,G,tn) marks (OK t,G1,tn1)) ==>
    scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 m b
      (bind (eval_exprs cx xs) (\vs. return (v::vs))) (mid with gas_obs := [],t,G1,tn1)
      (extcall_positional_post keep DF lo d C f ce cx env kw (e::xs) (sv::svs) a b es s G tn)
      (create_operand_exit_post C cx) /\
    create_operand_cut m b E C f tops cx st0 (eval_exprs cx xs) (mid with gas_obs := [],t)` by
    (rpt gen_tac >> strip_tac >>
     `body_exprs_full_ok cx xs /\ body_const_cells_agree [(NONE,tops)] cx env (mid with gas_obs := []) /\
      extcall_pos_entry DF lo d st0 C f ce cx env m (mid with gas_obs := []) t G1 tn1` by
      (irule pos_list_tail_entry >>
       qpat_assum `extcall_pos_entry _ _ _ _ _ _ _ _ _ a _ _ _ _` (irule_at Any) >>
       qpat_assum `bind _ _ _ = (INL v,_)` (irule_at Any) >>
       simp[] >> qexistsl_tac [`sv`,`xs ++ kw`,`marks`,`keep`,`PG`,`H`,`E`] >> fs[Abbr `P`]) >>
     qpat_assum `!mid t G1 tn1. _ ==> _ /\ create_operand_cut _ _ _ _ _ _ _ _ _ _`
        (drule_all_then strip_assume_tac) >> simp[] >>
     irule pos_list_cons_post >> simp[] >>
     qpat_assum `bind _ _ _ = (INL v,_)` (irule_at Any) >>
     fs[Abbr `P`,extcall_pos_entry_def]) >>
  `!H r ee G1 tn1 t. P H r ee G1 tn1 t ==> ?v. r = INL v` by
    (simp[Abbr `P`,extcall_pos_head_post_def] >> metis_tac[]) >>
  qunabbrev_tac `P` >> reverse conj_tac
  >- (irule pos_list_cons_cut >>
      qpat_assum `scoped_operand_outcome _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
      fs[extcall_pos_entry_def] >> qexists_tac `ce` >> simp[] >>
      reverse conj_tac >- first_assum ACCEPT_TAC >>
      rpt gen_tac >> strip_tac >>
      qpat_assum `!obs marks v mid G1 tn1 t. _ ==> _ /\ create_operand_cut _ _ _ _ _ _ _ _ _ _`
        (drule_at (Pat `bind _ _ _ = (INL _,_)`)) >>
      disch_then (qspecl_then [`marks`,`G1`,`tn1`,`t`] mp_tac) >> simp[] >> metis_tac[]) >>
  qpat_x_assum `extcall_pos_scope_join _ _ _`
    (qspecl_then [`a`,`m`,`b`,`s`] mp_tac o REWRITE_RULE [extcall_pos_scope_join_def]) >>
  simp[] >> impl_tac >- fs[extcall_pos_entry_def] >> strip_tac >>
  qpat_x_assum `extcall_pos_cons_rule _ _ _ _ _ _ _ _ _`
    (irule o REWRITE_RULE [extcall_pos_cons_rule_def]) >>
  qpat_assum `scoped_operand_outcome _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >> metis_tac[]
QED

Theorem extcall_pos_list_fold_given_cons:
  body_inv tops C ce cx /\ MEM f C.ctx_functions /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  extcall_pos_scope_join (gas_explicit_sites C shC) C f /\
  extcall_pos_cons_rule DF lo (gas_explicit_sites C shC) C f PG tops cx st0 /\
  extcall_pos_row_rule allowed keep DF lo d C shC f shf PG tops cx st0 ce env ==>
  !xs a b sha shb svs es s G tn.
    EVERY allowed xs /\ body_exprs_full_ok cx xs /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    (!e st. MEM e xs /\ expr_sim_inv ce cx env st ==> expr_body_pre ce cx env e st) /\
    compile_ext_call_args compile_expr ce kw (MAP (lowered_value_type ce) xs) xs a = (svs,b) /\
    compile_ext_call_args compile_expr (gas_shadow_env T ce) (MAP gas_shadow_expr kw)
      (MAP (lowered_value_type ce) (MAP gas_shadow_expr xs))
      (MAP gas_shadow_expr xs) sha = (svs,shb) /\
    gas_shadow_state a sha /\ gas_shadow_state b shb /\
    fn_has_code a b f /\ fn_has_code sha shb shf /\ local_ptrs_reserved ce a /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
    extcall_pos_entry DF lo d st0 C f ce cx env a es s G tn ==>
    scoped_operand_outcome (DF,lo,gas_explicit_sites C shC,C,f,PG) tops cx st0 a b
      (eval_exprs cx xs) (es,s,G,tn)
      (extcall_positional_post keep DF lo d C f ce cx env kw xs svs a b es s G tn)
      (create_operand_exit_post C cx) /\
    create_operand_cut a b (gas_explicit_sites C shC) C f tops cx st0 (eval_exprs cx xs) (es,s)
Proof
  strip_tac >> Induct_on `xs` >> rpt gen_tac >> strip_tac
  >- (gvs[compile_ext_call_args_def,comp_return_def] >>
      irule pos_list_empty >> fs[extcall_pos_entry_def]) >>
  rename1 `body_exprs_full_ok cx (e::xs)` >> drule_all pos_list_split >> strip_tac >> gvs[] >>
  `ci_mono a m /\ create_cut_code {} a m` by (drule_all pos_list_head_code >> simp[]) >>
  `ci_mono m b /\ create_cut_code {} m b` by (drule_then strip_assume_tac pos_list_layout >> simp[]) >>
  `fn_has_code a m f /\ fn_has_code m b f` by
    metis_tac[fn_has_code_split,ci_mono_def] >>
  `fn_has_code sha shm shf /\ fn_has_code shm shb shf` by
    (`ci_mono sha shm /\ ci_mono shm shb` by metis_tac[pos_list_compile_mono] >>
     metis_tac[fn_has_code_split,ci_mono_def]) >>
  `body_expr_full_ok cx e /\ expr_body_pre ce cx env e es` by
    fs[Once body_exprs_full_ok_def,extcall_pos_entry_def] >>
  qpat_x_assum `extcall_pos_row_rule _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [extcall_pos_row_rule_def]) >>
  disch_then (drule_at (Pat `compile_expr (gas_shadow_env T _) _ (gas_shadow_expr _) _ = _`)) >>
  disch_then (drule_at (Pat `gas_shadow_state _ sha`)) >>
  disch_then (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
  disch_then (qspecl_then [`xs ++ kw`] mp_tac) >>
  simp[] >> strip_tac >>
  `scoped_operand_outcome (DF,lo,gas_explicit_sites C shC,C,f,PG) tops cx st0 a m
     (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn)
     (extcall_pos_head_post keep DF lo d C f ce cx env (xs ++ kw) e sv a m es s G tn)
     (create_operand_exit_post C cx) /\
   create_operand_cut a m (gas_explicit_sites C shC) C f tops cx st0
     (bind (eval_expr cx e) (read_result cx)) (es,s)` by
    (qpat_assum `!es s G tn. _ ==> _ /\ create_operand_cut _ _ _ _ _ _ _ _ _ _`
      (qspecl_then [`es`,`s`,`G`,`tn`] mp_tac) >> simp[]) >>
  irule pos_list_cons_finish >>
  qpat_assum `scoped_operand_outcome _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >>
  `a.cs_next_var <= m.cs_next_var` by fs[ci_mono_def] >>
  `local_ptrs_reserved ce m` by metis_tac[local_ptrs_reserved_next_var] >>
  `(!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at m x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at m x)` by
    (rpt strip_tac >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  simp[] >> rpt gen_tac >> strip_tac >>
  qpat_assum `!a b sha shb svs es s G tn. _ ==> _ /\ create_operand_cut _ _ _ _ _ _ _ _ _ _`
    (drule_at (Pat `compile_ext_call_args _ _ _ _ (MAP gas_shadow_expr _) _ = _`)) >>
  disch_then (drule_at (Pat `compile_ext_call_args _ _ _ _ _ _ = _`)) >>
  simp[] >> metis_tac[]
QED

Theorem extcall_pos_list_scoped_cut_from_head:
  body_inv tops C ce cx /\ MEM f C.ctx_functions /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  extcall_pos_scope_join (gas_explicit_sites C shC) C f /\
  extcall_pos_row_rule allowed keep DF lo d C shC f shf PG tops cx st0 ce env ==>
  !xs a b sha shb svs es s G tn.
    EVERY allowed xs /\ body_exprs_full_ok cx xs /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    (!e st. MEM e xs /\ expr_sim_inv ce cx env st ==> expr_body_pre ce cx env e st) /\
    compile_ext_call_args compile_expr ce kw (MAP (lowered_value_type ce) xs) xs a = (svs,b) /\
    compile_ext_call_args compile_expr (gas_shadow_env T ce) (MAP gas_shadow_expr kw)
      (MAP (lowered_value_type ce) (MAP gas_shadow_expr xs))
      (MAP gas_shadow_expr xs) sha = (svs,shb) /\
    gas_shadow_state a sha /\ gas_shadow_state b shb /\
    fn_has_code a b f /\ fn_has_code sha shb shf /\ local_ptrs_reserved ce a /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
    extcall_pos_entry DF lo d st0 C f ce cx env a es s G tn ==>
    scoped_operand_outcome (DF,lo,gas_explicit_sites C shC,C,f,PG) tops cx st0 a b
      (eval_exprs cx xs) (es,s,G,tn)
      (extcall_positional_post keep DF lo d C f ce cx env kw xs svs a b es s G tn)
      (create_operand_exit_post C cx) /\
    create_operand_cut a b (gas_explicit_sites C shC) C f tops cx st0 (eval_exprs cx xs) (es,s)
Proof
  strip_tac >>
  `extcall_pos_cons_rule DF lo (gas_explicit_sites C shC) C f PG tops cx st0` by
    rw[extcall_pos_cons_rule_def] >>
    rpt gen_tac >> disch_tac >>
    ho_match_mp_tac (Q.INST [`a` |-> `a`, `m` |-> `m`, `b` |-> `b`,
      `E` |-> `gas_explicit_sites C shC`, `C` |-> `C`, `f` |-> `f`,
      `s` |-> `s`, `DF` |-> `DF`, `lo` |-> `lo`, `PG` |-> `PG`,
      `tops` |-> `tops`, `cx` |-> `cx`, `st0` |-> `st0`,
      `e` |-> `e`, `xs` |-> `xs`, `es` |-> `es`, `G` |-> `G`,
      `tn` |-> `tn`, `P` |-> `P`, `Q` |-> `Q`] pos_cons_scope_mixed) >>
    metis_tac[] >>
  irule extcall_pos_list_fold_given_cons >> simp[]
QED

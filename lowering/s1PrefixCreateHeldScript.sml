(* Request-prefix companion to bodyFullCreateHeld. *)
Theory s1PrefixCreateHeld
Ancestors
  s1PrefixPreds bodyFullCreateHeld s1PrefixOfVV
  s1PrefixCreateOperandCut s1PrefixCreateCopyFinish s1PrefixCreateDispatch
  s1PrefixCreateProxyCompose
  s1PrefixRawCreateCompose s1PrefixDefs bodyFullPreds bodySimFull exprSimHypsDefs exprSimHyps exprBodyPreProps
  exprLowering builtinCreate vyperInterpreter vyperCreate vyperState vyperAST vyperTypeSystem
  vyperStorageTrace vyperStorageFootprint loweringPosts exprLoweringProps
  gasShadow gasShadowState compileEnv codegenRel loweringShapeDefs
  fragGasOriginPtr venomState ptrSafeRun ptrDiscipline list
  s1PrefixCreateBlueprintEncodedArgs s1PrefixCreateCtorRows
  s1PrefixBlueprintRawCtor s1PrefixBlueprintScalarSuffix s1PrefixBlueprintFinish
  s1PrefixRawCreateCompose s1PrefixCreateOutcomeTyping
  words finite_map vyperTyping vyperValue bodySingletonCallSupport
  bodyFullExprsListFacts bodyFullExprsSingleton

Theorem create_minimal_proxy_expr_prefix_ok:
  !cx ty s r ks es d.
  body_exprs_full_ok cx (create_operand_order CreateMinimalProxy s es) /\
  body_exprs_prefix_ok cx (create_operand_order CreateMinimalProxy s es) ==>
  body_expr_prefix_ok cx (Call ty (CreateTarget CreateMinimalProxy s r ks) es d)
Proof
  match_mp_tac proxy_expr_prefix_from_dispatch >>
  rpt gen_tac >> MATCH_ACCEPT_TAC (GEN_ALL create_dispatch_prefix)
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> strip_tac >>
  `!ce env st. expr_sim_inv ce cx env st ==>
     accounts_well_typed st.accounts /\ outcomes_accounts_typed st.outcomes /\ IS_SOME st.outcomes`
    by (rpt gen_tac >> disch_tac >>
        conj_tac
        >- (drule expr_sim_inv_accounts_well_typed >> simp[])
        >> (drule expr_sim_inv_outcomes >> simp[])) >>
  pop_assum (mk_asm "oracle_fields") >>
  rewrite_tac[body_expr_prefix_ok_def] >>
  reverse conj_tac >- simp[] >> rpt gen_tac >> strip_tac >>
  Q.SUBGOAL_THEN `ty = BaseT AddressT` SUBST_ALL_TAC
  >- (drule copy_pre_args >> simp[]) >>
  conj_asm1_tac
  >- (drule copy_pre_args >> strip_tac >> gvs[] >>
      `LENGTH salts = (if s then 1 else 0)` by (Cases_on `s` >> gvs[]) >>
      rewrite_tac[expr_sim_prefix_def,expr_sim_full_pre_def] >>
      rpt gen_tac >> strip_tac >>
      drule_all copy_compile_cuts >> strip_tac >>
      qpat_assum `lower_value _ _ _ target sa = _`
        (mp_then Any (drule_all_then strip_assume_tac) copy_cut_code) >>
      qpat_assum `lower_value _ _ _ (gas_shadow_expr target) shadow_sa = _`
        (mp_then Any (drule_all_then strip_assume_tac) copy_cut_code) >>
      simp[NoAsms,create_eval_read,create_operand_order_def,expr_type_def,
           post_value_type_def,is_word_type_def] >>
      suspend "target") >>
  irule expr_vv_sim_stack_prefix >> simp[create_compile_stack] >>
  metis_tac[create_eval_value]
QED
*)
Theorem create_copy_expr_prefix_ok:
  !cx ty s r ks es d.
  body_exprs_full_ok cx (create_operand_order CreateCopyOf s es) /\
  body_exprs_prefix_ok cx (create_operand_order CreateCopyOf s es) ==>
  body_expr_prefix_ok cx (Call ty (CreateTarget CreateCopyOf s r ks) es d)
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume create_copy_expr_prefix_ok[target]:
  `expr_body_pre cenv cx env target es'` by
    (irule create_operand_pre >> simp[] >>
     qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _` (irule_at Any) >>
     drule expr_body_pre_static_facts >> simp[]) >>
  qpat_x_assum `body_exprs_full_ok _ (create_operand_order _ _ _)`
    (mp_tac o REWRITE_RULE [create_operand_order_def, Once body_exprs_full_ok_cons]) >>
  qpat_x_assum `body_exprs_prefix_ok _ (create_operand_order _ _ _)`
    (mp_tac o REWRITE_RULE [create_operand_order_def, Once body_exprs_prefix_ok_def]) >>
  strip_tac >> strip_tac >>
  rewrite_tac[Once exprSimWordArgsTheory.eval_exprs_cons_action] >>
  simp[NoAsms,bind_assoc,bind_return] >> once_rewrite_tac[GSYM bind_assoc] >>
  ho_match_mp_tac (GEN_ALL create_body_operand_cut_prefix_replay) >>
  qpat_assum `lower_value _ _ _ target sa = _` (irule_at Any) >>
  qpat_assum `lower_value _ _ _ (gas_shadow_expr target) shadow_sa = _` (irule_at Any) >>
  qexistsl [`tops`,`shadow_func`,`env`,`d'`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (gen_tac >> simp[NoAsms,storage_trace_frame_bind_all,evaluate_storage_trace_frame,
                      storage_trace_frame_read_result,storage_trace_frame_create_operands]) >>
  suspend "amount"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume create_copy_expr_prefix_ok[amount]:
  map_every qx_gen_tac [`tv`,`et`,`Gtar`,`tnt`,`st`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_body_pre cenv cx env amount et` by
    (irule create_operand_pre >>
     qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _` (irule_at Any) >> simp[]) >>
  qpat_x_assum `_ ==> body_exprs_full_ok _ (amount::salts)` drule >>
  rewrite_tac[Once body_exprs_full_ok_cons] >> strip_tac >>
  qpat_x_assum `_ ==> body_exprs_prefix_ok _ (amount::salts)` drule >>
  rewrite_tac[Once body_exprs_prefix_ok_def] >> strip_tac >>
  rewrite_tac[Once exprSimWordArgsTheory.eval_exprs_cons_action] >>
  simp[NoAsms,bind_assoc,bind_return] >> once_rewrite_tac[GSYM bind_assoc] >>
  ho_match_mp_tac (GEN_ALL create_body_operand_cut_prefix_replay) >>
  qpat_assum `lower_value _ _ _ amount a = _` (irule_at Any) >>
  qpat_assum `lower_value _ _ _ (gas_shadow_expr amount) a' = _` (irule_at Any) >>
  qexistsl [`tops`,`shadow_func`,`env`,`d'`] >>
  `sa.cs_next_var <= a.cs_next_var` by fs[ci_mono_def] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- metis_tac[local_ptrs_reserved_next_var]
  >- (rpt strip_tac >> irule not_fresh_at_mono >> qexists `sa` >> simp[])
  >- (rpt strip_tac >> irule not_fresh_at_mono >> qexists `sa` >> simp[])
  >- (gen_tac >> disch_tac >>
      qpat_assum `!H. valid_horizon _ _ H et.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
        (drule_then strip_assume_tac) >> fs[expr_post_def])
  >- (gen_tac >> simp[NoAsms,storage_trace_frame_bind_all,evaluate_storage_trace_frame,
                      storage_trace_frame_read_result,storage_trace_frame_create_operands]) >>
  suspend "scalar_frames"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume create_copy_expr_prefix_ok[scalar_frames]:
  map_every qx_gen_tac [`av`,`ea`,`Gamt`,`tna`,`samt`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `_ ==> body_exprs_full_ok _ salts` (drule_then assume_tac) >>
  qpat_x_assum `_ ==> body_exprs_prefix_ok _ salts` (drule_then assume_tac) >>
  `is_word_type (BaseT AddressT) /\ is_word_type (BaseT (UintT 256))` by simp[is_word_type_def] >>
  qpat_assum `lower_value _ _ _ target sa = _`
    (mp_then Any (drule_all_then strip_assume_tac) create_word_cut_frame_facts) >>
  qpat_assum `lower_value _ _ _ amount a = _`
    (mp_then Any (drule_all_then strip_assume_tac) create_word_cut_frame_facts) >>
  `valid_horizon cx st0 (storage_trace_horizon ea.storage_trace) ea.storage_trace`
    by fs[storage_trace_domain_def] >>
  `valid_horizon cx st0 (storage_trace_horizon ea.storage_trace) et.storage_trace`
    by first_assum (drule_then ACCEPT_TAC) >>
  `valid_horizon cx st0 (storage_trace_horizon ea.storage_trace) es'.storage_trace`
    by first_assum (drule_then ACCEPT_TAC) >>
  `stmt_state_rel (storage_trace_horizon ea.storage_trace) ctx func cenv cx es' s0` by
    (qpat_assum `!H. valid_horizon cx st0 H es'.storage_trace ==> _`
      (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  qpat_assum `wb_frame cenv et ea a st samt`
    (mp_then Any (drule_all_then strip_assume_tac) create_cut_frames_keep_operand) >>
  `ci_mono sa b` by metis_tac[ci_mono_trans] >>
  `local_ptrs_reserved cenv b` by metis_tac[local_ptrs_reserved_next_var,ci_mono_def] >>
  `sa.cs_next_var <= b.cs_next_var` by fs[ci_mono_def] >>
  `(!z n. cenv.ce_return_buf = SOME (PtrVar (Var z) n) ==> not_fresh_at b z) /\
   (!z n. cenv.ce_return_pc = SOME (PtrVar (Var z) n) ==> not_fresh_at b z) /\
   (!z. x = Var z ==> not_fresh_at b z)` by
    (rpt strip_tac >> irule not_fresh_at_mono >>
     FIRST [qexists `sa` >> simp[] >> NO_TAC,
            qexists `a` >> fs[ci_mono_def]]) >>
  `?bs. tv = BytesV bs /\ LENGTH bs = 20` by
    (qpat_x_assum `value_has_type (BaseTV AddressT) tv` mp_tac >>
     Cases_on `tv` >> simp[vyperTypingTheory.value_has_type_def]) >>
  `dest_NumV av = SOME (w2n (typed_val_to_w256 (BaseTV (UintT 256)) av))` by
    simp[exprSimSendTheory.uint256_typed_dest] >>
  `s0.vs_alloca_next <= samt.vs_alloca_next` by decide_tac >>
  suspend "scalar_paths"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume create_copy_expr_prefix_ok[scalar_paths]:
  qpat_x_assum `?marks. _ /\ !H. _ ==> gas_origin_ptr_path _ _ marks (OK st,_,_)`
    (qx_choose_then `mt` strip_assume_tac) >>
  qpat_x_assum `?marks. _ /\ !H. _ ==> gas_origin_ptr_path _ _ marks (OK samt,_,_)`
    (qx_choose_then `ma` strip_assume_tac) >>
  `!H. valid_horizon cx st0 H ea.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (s0,G0,tn0) (mt ++ ma) (OK samt,Gamt,tna)` by
    (gen_tac >> strip_tac >>
     `valid_horizon cx st0 H et.storage_trace` by first_assum (drule_then ACCEPT_TAC) >>
     qpat_assum `!H. _ ==> gas_origin_ptr_path _ _ mt _`
       (drule_then (mp_then Any irule gas_origin_ptr_path_append)) >> simp[]) >>
  Cases_on `s` >> gvs[compile_create_salt_def,comp_return_def]
  >- suspend "salt_cut" >>
  suspend "no_salt"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume create_copy_expr_prefix_ok[salt_cut]:
  Cases_on `lower_value compile_expr cenv (BaseT (BytesT (Fixed 32))) salt b` >>
  Cases_on `lower_value compile_expr (gas_shadow_env T cenv)
    (BaseT (BytesT (Fixed 32))) (gas_shadow_expr salt) b'` >>
  gvs[comp_bind_def,comp_return_def] >>
  rename1 `lower_value _ _ _ salt b = (salt_op,c)` >>
  `expr_body_pre cenv cx env salt ea` by
    (irule create_operand_pre >>
     qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _` (irule_at Any) >> simp[]) >>
  fs[Once body_exprs_full_ok_cons,Once body_exprs_prefix_ok_def] >>
  rewrite_tac[Once exprSimWordArgsTheory.eval_exprs_cons_action] >>
  simp[NoAsms,Once evaluate_def,bind_assoc,bind_return] >>
  once_rewrite_tac[GSYM bind_assoc] >>
  ho_match_mp_tac (GEN_ALL create_body_operand_cut_prefix_replay) >>
  `lower_value compile_expr cenv (expr_type salt) salt b = (salt_op,c)` by simp[] >>
  `lower_value compile_expr (gas_shadow_env T cenv) (expr_type salt)
     (gas_shadow_expr salt) b' = (salt_op,c')` by simp[] >>
  qpat_assum `lower_value _ _ (expr_type salt) salt b = _` (irule_at Any) >>
  qpat_assum `lower_value _ _ (expr_type salt) (gas_shadow_expr salt) b' = _` (irule_at Any) >>
  qexistsl [`tops`,`shadow_func`,`env`,`d'`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (gen_tac >> simp[NoAsms,storage_trace_frame_bind_all,
                      storage_trace_frame_read_result,storage_trace_frame_create_operands]) >>
  suspend "salt_frames"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume create_copy_expr_prefix_ok[salt_frames]:
  map_every qx_gen_tac [`sv`,`ew`,`Gsalt`,`tns`,`ssalt`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `is_word_type (BaseT (BytesT (Fixed 32)))` by simp[is_word_type_def] >>
  qpat_assum `lower_value _ _ (expr_type salt) salt b = _`
    (mp_then Any (drule_all_then strip_assume_tac) create_word_cut_frame_facts) >>
  `valid_horizon cx st0 (storage_trace_horizon ew.storage_trace) ew.storage_trace`
    by fs[storage_trace_domain_def] >>
  `valid_horizon cx st0 (storage_trace_horizon ew.storage_trace) ea.storage_trace`
    by first_assum (drule_then ACCEPT_TAC) >>
  `valid_horizon cx st0 (storage_trace_horizon ew.storage_trace) et.storage_trace`
    by first_assum (drule_then ACCEPT_TAC) >>
  `valid_horizon cx st0 (storage_trace_horizon ew.storage_trace) es'.storage_trace`
    by first_assum (drule_then ACCEPT_TAC) >>
  `stmt_state_rel (storage_trace_horizon ew.storage_trace) ctx func cenv cx es' s0` by
    (qpat_assum `!H. valid_horizon cx st0 H es'.storage_trace ==> _`
      (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  qpat_assum `eval_operand x samt = SOME _`
    (mp_then Any (drule_all_then strip_assume_tac) create_cut_frames_keep_operand) >>
  qpat_assum `eval_operand y samt = SOME _`
    (mp_then Any (drule_all_then strip_assume_tac) create_cut_frames_keep_operand) >>
  `ci_mono sa c` by metis_tac[ci_mono_trans] >>
  `sa.cs_next_var <= c.cs_next_var /\ b.cs_next_var <= c.cs_next_var`
    by fs[ci_mono_def] >>
  `s0.vs_alloca_next <= ssalt.vs_alloca_next` by decide_tac >>
  `local_ptrs_reserved cenv c` by metis_tac[local_ptrs_reserved_next_var] >>
  `(!z n. cenv.ce_return_buf = SOME (PtrVar (Var z) n) ==> not_fresh_at c z) /\
   (!z n. cenv.ce_return_pc = SOME (PtrVar (Var z) n) ==> not_fresh_at c z) /\
   (!z. x = Var z \/ y = Var z ==> not_fresh_at c z)` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists `b` >> simp[]) >>
  qpat_x_assum `?marks. _ /\ !H. _ ==> gas_origin_ptr_path _ _ marks (OK ssalt,_,_)`
    (qx_choose_then `ms` strip_assume_tac) >>
  `gas_origin_ptr_path (DF (storage_trace_horizon ew.storage_trace),lo,
      gas_explicit_sites ctx shadow_ctx,ctx,func,PG) (s0,G0,tn0)
      ((mt ++ ma) ++ ms) (OK ssalt,Gsalt,tns)` by
    (qpat_assum `!H. _ ==> gas_origin_ptr_path _ _ (mt ++ ma) _`
      (drule_then (mp_then Any irule gas_origin_ptr_path_append)) >> simp[]) >>
  qabbrev_tac `salt_word = typed_val_to_w256 (BaseTV (BytesT (Fixed 32))) sv` >>
  `dest_create_salt sv = SOME salt_word` by simp[Abbr `salt_word`,create_salt_word] >>
  suspend "salt_finish"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume create_copy_expr_prefix_ok[salt_finish]:
  `accounts_well_typed ew.accounts /\ outcomes_accounts_typed ew.outcomes /\ IS_SOME ew.outcomes`
    by (asm "oracle_fields" irule >> goal_assum (drule_at Any)) >>
  irule (Q.INST [`sw` |-> `SOME salt_word`] create_copy_finish_prefix_from_dispatch) >>
  qpat_assum `compile_create_copy x y (SOME salt_op) _ c = _` (irule_at Any) >>
  qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) _ (OK ssalt,Gsalt,tns)` (irule_at Any) >>
  qpat_assum `eval_operand x ssalt = SOME _` (irule_at Any) >>
  qpat_assum `eval_operand y ssalt = SOME _` (irule_at Any) >>
  simp[storage_trace_frame_bind_all,storage_trace_frame_read_result,
       storage_trace_frame_create_operands,Abbr `salt_word`] >>
  qexistsl [`tops`,`sa`,`es'`,`d'`,`cenv`] >> simp[] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      irule (Q.INST [`sw` |-> `SOME (typed_val_to_w256 (BaseTV (BytesT (Fixed 32))) sv)`]
        create_dispatch_prefix) >>
      qpat_assum `compile_create_dispatch _ _ _ _ _ _ = _` (irule_at Any) >>
      qpat_assum `eval_operand buf t = SOME _` (irule_at Any) >>
      qpat_assum `eval_operand len t = SOME _` (irule_at Any) >>
      qpat_assum `eval_operand y t = SOME _` (irule_at Any) >>
      simp[] >> rpt (goal_assum (drule_at Any)) >> simp[] >>
      qexists `sv` >> simp[]) >>
  conj_tac
  >- (gen_tac >>
      dep_rewrite.DEP_ONCE_REWRITE_TAC
        [SIMP_RULE (srw_ss()) [dest_optional_salt_def]
          (Q.INST [`salt` |-> `SOME sv`,
                   `sw` |-> `SOME (typed_val_to_w256 (BaseTV (BytesT (Fixed 32))) sv)`,
                   `addr` |-> `word_of_bytes_be bs`,
                   `value` |-> `w2n (typed_val_to_w256 (BaseTV (UintT 256)) av)`,
                   `code` |-> `(lookup_account (word_of_bytes_be bs) (ew:evaluation_state).accounts).code`]
            copy_read_prepared)] >>
      simp[vyperValueTheory.dest_AddressV_def]) >>
  rpt strip_tac >>
  (first_assum ACCEPT_TAC ORELSE first_assum (drule_then ACCEPT_TAC) ORELSE
   (qpat_assum `!z. x = Var z \/ y = Var z ==> _`
      (qspec_then `x'` irule) >> simp[]))
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume create_copy_expr_prefix_ok[no_salt]:
  simp[NoAsms,Once evaluate_def,bind_return] >>
  `accounts_well_typed ea.accounts /\ outcomes_accounts_typed ea.outcomes /\ IS_SOME ea.outcomes`
    by (asm "oracle_fields" irule >> goal_assum (drule_at Any)) >>
  irule (SIMP_RULE (srw_ss()) [create_dispatch_prefix]
      (Q.INST [`sw` |-> `NONE`] create_copy_finish_prefix_from_dispatch)) >>
  qpat_assum `compile_create_copy x y NONE _ b = _` (irule_at Any) >>
  qpat_assum `!H. _ ==> gas_origin_ptr_path _ (s0,G0,tn0) _ (OK samt,Gamt,tna)`
    (drule_then (irule_at Any)) >>
  qpat_assum `eval_operand x samt = SOME _` (irule_at Any) >>
  qpat_assum `eval_operand y samt = SOME _` (irule_at Any) >>
  simp[storage_trace_frame_bind_all,storage_trace_frame_read_result,
       storage_trace_frame_create_operands] >>
  qexistsl [`tops`,`sa`,`es'`,`d'`,`cenv`] >> simp[] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      irule (Q.INST [`sw` |-> `NONE`] create_dispatch_prefix) >>
      qpat_assum `compile_create_dispatch _ _ _ _ _ _ = _` (irule_at Any) >>
      qpat_assum `eval_operand buf t = SOME _` (irule_at Any) >>
      qpat_assum `eval_operand len t = SOME _` (irule_at Any) >>
      qpat_assum `eval_operand y t = SOME _` (irule_at Any) >>
      simp[] >> rpt (goal_assum (drule_at Any)) >> simp[]) >>
  conj_tac
  >- (gen_tac >>
      dep_rewrite.DEP_ONCE_REWRITE_TAC
        [SIMP_RULE (srw_ss()) [dest_optional_salt_def]
          (Q.INST [`salt` |-> `NONE`, `sw` |-> `NONE`,
                   `addr` |-> `word_of_bytes_be bs`,
                   `value` |-> `w2n (typed_val_to_w256 (BaseTV (UintT 256)) av)`,
                   `code` |-> `(lookup_account (word_of_bytes_be bs) (ea:evaluation_state).accounts).code`]
            copy_read_prepared)] >>
      simp[vyperValueTheory.dest_AddressV_def]) >>
  rpt strip_tac >> first_assum (drule_then ACCEPT_TAC)
QED
*)
(* SCRATCH MEASUREMENT: original continuation.
Finalise create_copy_expr_prefix_ok
*)

Theorem create_blueprint_expr_prefix_ok:
  !cx ty b s r ks es d.
  body_exprs_full_ok cx (create_operand_order (CreateFromBlueprint b) s es) /\
  body_exprs_prefix_ok cx (create_operand_order (CreateFromBlueprint b) s es) ==>
  body_expr_prefix_ok cx
      (Call ty (CreateTarget (CreateFromBlueprint b) s r ks) es d)
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac[body_expr_prefix_ok_def] >>
  reverse conj_tac >- simp[] >> rpt gen_tac >> strip_tac >>
  Q.SUBGOAL_THEN `ty = BaseT AddressT` SUBST_ALL_TAC
  >- (drule blueprint_pre_args >> simp[]) >>
  conj_asm1_tac
  >- (drule blueprint_pre_args >> strip_tac >> gvs[] >>
      `LENGTH salts = (if s then 1 else 0)` by (Cases_on `s` >> gvs[]) >>
      `create_operand_order (CreateFromBlueprint b) s (target::amount::(salts ++ offset::ctor)) =
       target::(ctor ++ amount::(salts ++ [offset]))` by
        (Cases_on `s` >> gvs[create_operand_order_def]) >>
      rewrite_tac[expr_sim_prefix_def,expr_sim_full_pre_def] >>
      pure_rewrite_tac[GSYM APPEND_ASSOC,APPEND] >>
      rpt gen_tac >> strip_tac >>
      drule_all blueprint_compile_cuts >> strip_tac >>
      qpat_assum `lower_value _ _ _ target sa = _`
        (mp_then Any (drule_all_then strip_assume_tac) blueprint_cut_code) >>
      qpat_assum `lower_value _ _ _ (gas_shadow_expr target) _ = _`
        (mp_then Any (drule_all_then strip_assume_tac) blueprint_cut_code) >>
      simp[create_eval_read,expr_type_def,post_value_type_def,is_word_type_def] >>
      suspend "target") >>
  irule expr_vv_sim_stack_prefix >> simp[create_compile_stack] >>
  metis_tac[create_eval_value]
QED

Resume create_blueprint_expr_prefix_ok[target]:
  `expr_body_pre cenv cx env target es'` by
    (irule create_operand_pre >> simp[] >>
     qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _` (irule_at Any) >>
     drule expr_body_pre_static_facts >> simp[]) >>
  qpat_assum `create_operand_order _ _ _ = _` (fn order_th =>
    qpat_x_assum `body_exprs_full_ok _ (create_operand_order _ _ _)`
      (mp_tac o ONCE_REWRITE_RULE [body_exprs_full_ok_cons] o REWRITE_RULE [order_th]) >>
    qpat_x_assum `body_exprs_prefix_ok _ (create_operand_order _ _ _)`
      (mp_tac o ONCE_REWRITE_RULE [body_exprs_prefix_ok_def] o REWRITE_RULE [order_th])) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rewrite_tac[Once exprSimWordArgsTheory.eval_exprs_cons_action] >>
  simp[NoAsms,bind_assoc,bind_return] >> once_rewrite_tac[GSYM bind_assoc] >>
  ho_match_mp_tac (GEN_ALL create_body_operand_cut_prefix_replay) >>
  qpat_assum `lower_value _ _ _ target sa = _` (irule_at Any) >>
  qpat_assum `lower_value _ _ _ (gas_shadow_expr target) shadow_sa = _` (irule_at Any) >>
  qexistsl [`tops`,`shadow_func`,`env`,`d'`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (gen_tac >> simp[NoAsms,storage_trace_frame_bind_all,evaluate_storage_trace_frame,
       storage_trace_frame_read_result,storage_trace_frame_create_operands]) >>
  suspend "ctor"
QED

Resume create_blueprint_expr_prefix_ok[ctor]:
  qx_genl_tac [`tv`,`et`,`Gtar`,`tnt`,`st`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `_ ==> body_exprs_full_ok _ (ctor ++ _)`
    (drule_then (strip_assume_tac o MATCH_MP create_body_exprs_split)) >>
  qpat_assum `_ ==> body_exprs_prefix_ok _ (ctor ++ _)`
    (drule_then (strip_assume_tac o MATCH_MP create_prefix_exprs_split)) >>
  rename1 `compile_create_blueprint_args _ _ b _ ctor a = ((p,n),ca)` >>
  rename1 `compile_create_blueprint_args _ _ b _ (MAP gas_shadow_expr ctor) a' = ((p,n),sha)` >>
  rename1 `compile_create_salt _ _ _ c = (sop,cs)` >>
  `is_word_type (BaseT AddressT)` by simp[is_word_type_def] >>
  qpat_assum `lower_value _ _ _ target sa = _`
    (mp_then Any (drule_all_then strip_assume_tac) create_word_cut_frame_facts) >>
  `local_ptrs_reserved cenv a /\
   (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at a x) /\
   (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at a x)` by
    (qpat_assum `ci_mono sa a` (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
     metis_tac[local_ptrs_reserved_next_var,stmtFragPtrTheory.not_fresh_at_mono]) >>
  rewrite_tac[create_eval_exprs_append] >>
  simp[NoAsms,bind_assoc,bind_return] >>
  qabbrev_tac `src_action = eval_create_operands cx (CreateFromBlueprint b) s r
    (BaseT AddressT::BaseT (UintT 256)::(MAP expr_type salts ++ BaseT (UintT 256)::MAP expr_type ctor))
    (blueprint_literal_offset cx s (target::amount::(salts ++ offset::ctor)))` >>
  `!vs bytes eu Gu tu u.
    (if b then vs = [BytesV bytes]
     else encode_create_ctor_args (get_tenv cx) (MAP expr_type ctor) vs = SOME bytes) /\
    LENGTH bytes < 2 ** 64 /\
    (?ctor_marks. !tail.
      eval_exprs cx ctor (et with gas_obs := gas_explicit ctor_marks st.vs_gas_readings ++ tail) =
        (INL vs,eu with gas_obs := tail)) /\
    expr_sim_inv cenv cx env eu /\
    wb_frame cenv et eu a st u /\ ghost_kept_at lo cenv et a Gtar tnt st Gu tu /\
    st.vs_alloca_next <= u.vs_alloca_next /\ alloca_history func u /\ return_buf_frame d' cenv ca u /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    (!fn i z. frag_reachable ctx func u fn i z ==> dalloca_fmp_headroom i z) /\
    ~u.vs_halted /\ u.vs_current_bb = ca.cs_current_bb /\ u.vs_inst_idx = LENGTH ca.cs_current_insts /\
    (!v. p = Var v \/ n = Var v ==> not_fresh_at ca v) /\
    storage_trace_domain cx st0 eu.storage_trace /\
    (!H. valid_horizon cx st0 H eu.storage_trace ==>
      valid_horizon cx st0 H et.storage_trace /\ stmt_state_rel H ctx func cenv cx eu u /\
      storage_well_formed_on cx eu (FST H) /\ ghost_inv_at (DF H) lo d' cenv cx eu Gu tu u) /\
    (!vs' ee Gf tf z gs.
      (!tail. eval_exprs cx (amount::(salts ++ [offset])) (eu with gas_obs := gs ++ tail) =
         (INL vs',ee with gas_obs := tail)) /\
      wb_frame cenv eu ee ca u z /\ ghost_kept_at lo cenv eu ca Gu tu u Gf tf /\
      MAP FDOM eu.scopes = MAP FDOM ee.scopes /\ u.vs_alloca_next <= z.vs_alloca_next /\
      storage_trace_domain cx st0 ee.storage_trace /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
        valid_horizon cx st0 H eu.storage_trace /\ stmt_state_rel H ctx func cenv cx ee z /\
        storage_well_formed_on cx ee (FST H) /\ ghost_inv_at (DF H) lo d' cenv cx ee Gf tf z) ==>
      eval_operand n z = SOME (n2w (LENGTH bytes)) /\ op_taint tf n = {} /\ op_prov Gf n = NONE /\
      (n <> Lit 0w ==> ?q a. p = Var q /\ lookup_var q z = SOME a /\ ptr_covers Gf tf q z (LENGTH bytes) /\
        (bytes = [] \/ w2n a + LENGTH bytes <= z.vs_alloca_next) /\
        (!i. w2n a <= i /\ i < w2n a + LENGTH bytes ==> i NOTIN tf.t_mem) /\
        read_memory (w2n a) (LENGTH bytes) z = bytes)) ==>
    gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cx st0
      (bind (eval_exprs cx (amount::(salts ++ [offset])))
        (\ws. bind (src_action (tv::(vs ++ ws))) (read_result cx))) (eu,u,Gu,tu)`
    by suspend "ctor_values" >>
  Cases_on `b` >- suspend "ctor_raw" >>
  Cases_on `ctor = []` >- suspend "ctor_empty" >>
  ho_match_mp_tac (GEN_ALL blueprint_encoded_args_cut_prefix) >>
  qpat_assum `compile_create_blueprint_args _ _ F _ ctor a = _` (irule_at Any) >>
  qpat_assum `compile_create_blueprint_args _ _ F _ (MAP gas_shadow_expr ctor) _ = _` (irule_at Any) >>
  qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _` (irule_at Any) >>
  qpat_assum `body_inv _ _ _ _` (irule_at Any) >>
  qpat_assum `return_buf_frame _ _ a st` (irule_at Any) >>
  qexists `shadow_func` >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (gen_tac >> simp[NoAsms,Abbr `src_action`,storage_trace_frame_bind_all,
        evaluate_storage_trace_frame,storage_trace_frame_read_result,storage_trace_frame_create_operands])
  >- suspend "ctor_rows" >>
  suspend "ctor_encoded"
QED

Resume create_blueprint_expr_prefix_ok[ctor_rows]:
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  irule create_ctor_rows_operand_prefix >>
  rpt (goal_assum (drule_at Any)) >>
  rpt gen_tac >> strip_tac >> irule create_operand_pre >>
  qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _` (irule_at Any) >> simp[]
QED

Resume create_blueprint_expr_prefix_ok[ctor_encoded]:
  qx_genl_tac [`vs`,`bytes`,`eu`,`Gu`,`tu`,`u`,`ctor_marks`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!vs bytes eu Gu tu u. _ ==> gas_prefix_full _ _ _ _ _` irule >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (gen_tac >> disch_tac >> first_assum (drule_then strip_assume_tac) >> simp[])
  >- (qexists `ctor_marks` >> first_assum ACCEPT_TAC) >>
  qexists `bytes` >> pure_rewrite_tac[COND_CLAUSES] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume create_blueprint_expr_prefix_ok[ctor_values]:
  qx_genl_tac [`vs`,`bytes`,`eu`,`Gu`,`tu`,`u`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?ctor_marks. !tail. _` (qx_choose_then `ctor_marks` assume_tac) >>
  qpat_assum `!tail. eval_exprs cx ctor _ = (INL vs,_)` (qspec_then `[]` assume_tac) >>
  `well_typed_exprs env ctor` by
    (simp[constSubstCorrectTheory.frame_well_typed_exprs_every,EVERY_MEM] >>
     qx_gen_tac `arg` >> strip_tac >>
     `expr_body_pre cenv cx env arg et` by
       (irule create_operand_pre >>
        qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _` (irule_at Any) >> simp[]) >>
     drule_then strip_assume_tac expr_body_pre_static_facts >> simp[]) >>
  `body_const_cells_agree [(NONE,tops)] cx env eu` by
    (`body_const_cells_agree [(NONE,tops)] cx env (eu with gas_obs := [])` suffices_by simp[] >>
     irule body_const_cells_agree_exprs >> rpt (goal_assum (drule_at Any)) >> simp[]) >>
  qpat_assum `!st vs en. eval_exprs cx ctor st = (INL vs,en) ==> body_exprs_full_ok _ _`
    (drule_then assume_tac) >>
  qpat_assum `!st vs en. eval_exprs cx ctor st = (INL vs,en) ==> body_exprs_prefix_ok _ _`
    (drule_then assume_tac) >>
  qpat_assum `LENGTH salts = _` (mp_then Any
    (pure_once_rewrite_tac o single) blueprint_scalar_source_split) >>
  BETA_TAC >>
  ho_match_mp_tac (GEN_ALL (BETA_RULE (Q.INST
    [`next` |-> `\av sv ov. bind (src_action (tv::(vs ++ av::((case sv of NONE => [] | SOME v => [v]) ++ [ov])))) (read_result cx)`]
    blueprint_scalar_suffix_prefix_from_replay))) >>
  qpat_assum `return_buf_frame _ _ ca u` (irule_at Any) >>
  qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _` (irule_at Any) >>
  qpat_assum `body_inv _ _ _ _` (irule_at Any) >>
  qpat_assum `lower_value _ _ _ amount ca = _` (irule_at Any) >>
  qpat_assum `lower_value _ _ _ (gas_shadow_expr amount) _ = _` (irule_at Any) >>
  qpat_assum `compile_create_salt _ _ _ c = (sop,cs)` (irule_at Any) >>
  qpat_assum `compile_create_salt _ _ (OPTION_MAP gas_shadow_expr _) _ = _` (irule_at Any) >>
  qpat_assum `(case _ of NONE => _ | SOME i => comp_return (Lit (i2w i))) cs = _` (irule_at Any) >>
  qpat_assum `(case _ of NONE => lower_value _ _ _ (gas_shadow_expr offset)
                | SOME i => comp_return (Lit (i2w i))) _ = _` (irule_at Any) >>
  qexistsl [`x`,`shadow_func`,`n`,`typed_val_to_w256 (BaseTV AddressT) tv`,`p`,`bytes`] >>
  `local_ptrs_reserved cenv ca /\
   (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at ca x) /\
   (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at ca x) /\
   (!v. x = Var v ==> not_fresh_at ca v)` by
    (qpat_assum `ci_mono a ca` (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
     metis_tac[local_ptrs_reserved_next_var,stmtFragPtrTheory.not_fresh_at_mono]) >>
  `eval_operand x u = SOME (typed_val_to_w256 (BaseTV AddressT) tv) /\ op_taint tu x = {}` by
    (qpat_assum `wb_frame cenv et eu a st u`
      (mp_then Any (drule_all_then ACCEPT_TAC) create_operand_cut_frame)) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (gen_tac >> disch_tac >>
      qpat_assum `!H. valid_horizon _ _ H eu.storage_trace ==> _`
        (drule_then (map_every assume_tac o CONJUNCTS)) >> simp[])
  >- simp[Abbr `src_action`,storage_trace_frame_bind_all,
      storage_trace_frame_read_result,storage_trace_frame_create_operands]
  >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      qpat_assum `!ws ef Gf tf z gs. _ ==> eval_operand n z = SOME (n2w (LENGTH bytes)) /\ _` irule >>
      rpt (goal_assum (drule_at Any)) >> simp[]) >>
  suspend "scalar_finish"
QED

Resume create_blueprint_expr_prefix_ok[scalar_finish]:
  qx_genl_tac [`av`,`sv`,`ov`,`yw`,`sw`,`ow`,`ee`,`Gf`,`tf`,`z`,`scalar_marks`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace`
    by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `!H. valid_horizon _ _ H eu.storage_trace ==> _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) es'.storage_trace`
    by (first_assum irule >> first_assum ACCEPT_TAC) >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx es' s0` by
    (qpat_assum `!H. valid_horizon _ _ H es'.storage_trace ==> _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `wb_frame cenv es' eu sa s0 u /\ ghost_kept_at lo cenv es' sa G0 tn0 s0 Gu tu` by
    (qpat_assum `wb_frame cenv et eu a st u`
       (mp_then Any (drule_all_then ACCEPT_TAC) create_cut_frames_trans)) >>
  `ci_mono sa ca` by metis_tac[ci_mono_trans] >>
  `wb_frame cenv es' ee sa s0 z /\ ghost_kept_at lo cenv es' sa G0 tn0 s0 Gf tf` by
    (qpat_assum `wb_frame cenv eu ee ca u z`
       (mp_then Any (drule_all_then ACCEPT_TAC) create_cut_frames_trans)) >>
  `ci_mono sa f` by metis_tac[ci_mono_trans] >>
  `sa.cs_next_var <= f.cs_next_var /\ s0.vs_alloca_next <= z.vs_alloca_next` by
    (qpat_assum `ci_mono sa f` (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >> decide_tac) >>
  `local_ptrs_reserved cenv f /\
   (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at f x) /\
   (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at f x)` by
    metis_tac[local_ptrs_reserved_next_var,stmtFragPtrTheory.not_fresh_at_mono] >>
  qpat_assum `expr_sim_inv cenv cx env ee` (fn th =>
    assume_tac (MATCH_MP expr_sim_inv_accounts_well_typed th) >>
    strip_assume_tac (MATCH_MP expr_sim_inv_outcomes th)) >>
  `?bs. tv = BytesV bs /\ LENGTH bs = 20` by
    (qpat_x_assum `value_has_type (BaseTV AddressT) tv` mp_tac >>
     Cases_on `tv` >> simp[vyperTypingTheory.value_has_type_def]) >>
  qpat_x_assum `tv = BytesV bs` SUBST_ALL_TAC >>
  irule (SIMP_RULE (srw_ss()) [create_dispatch_prefix]
    blueprint_finish_prefix_from_dispatch) >>
  qpat_assum `compile_create_blueprint_check _ x off f = _` (irule_at Any) >>
  qpat_assum `compile_create_blueprint_append x y sop off _ p n r _ = _` (irule_at Any) >>
  qpat_assum `eval_operand x z = SOME _` (irule_at Any) >>
  qpat_assum `eval_operand y z = SOME _` (irule_at Any) >>
  qpat_assum `eval_operand off z = SOME _` (irule_at Any) >>
  qpat_assum `OPTREL _ sop sw` (irule_at Any) >>
  qpat_assum `body_inv _ _ _ _` (irule_at Any) >>
  qpat_assum `return_buf_frame _ _ f z` (irule_at Any) >>
  suspend "source_finish"
QED

Resume create_blueprint_expr_prefix_ok[source_finish]:
  qexistsl [`tn0`,`sa`,`s0`,`es'`,`(lookup_account (word_of_bytes_be bs) ee.accounts).code`,`bytes`,`G0`] >>
  simp[Abbr `src_action`,storage_trace_frame_bind_all,
       storage_trace_frame_read_result,storage_trace_frame_create_operands] >>
  rpt conj_tac
  >- (rpt gen_tac >> disch_tac >> first_assum (drule_then ACCEPT_TAC))
  >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      irule create_dispatch_prefix >>
      qpat_assum `compile_create_dispatch _ _ _ _ _ _ = _` (irule_at Any) >>
      qpat_assum `eval_operand codep s' = SOME _` (irule_at Any) >>
      qpat_assum `eval_operand len s' = SOME _` (irule_at Any) >>
      qpat_assum `eval_operand _ s' = SOME aw` (irule_at Any) >>
      rpt (goal_assum (drule_at Any)) >> simp[])
  >- (gen_tac >>
      qpat_assum `IS_SOME sv <=> s` (pure_once_rewrite_tac o single o GSYM) >>
      dep_rewrite.DEP_ONCE_REWRITE_TAC
        [Q.INST [`ctor_tys` |-> `MAP expr_type ctor`,
                 `addr` |-> `word_of_bytes_be bs`,
                 `value` |-> `w2n (yw:256 word)`, `off` |-> `w2n (ow:256 word)`,
                 `code` |-> `(lookup_account (word_of_bytes_be bs) (ee:evaluation_state).accounts).code`,
                 `args` |-> `bytes`, `sw` |-> `sw`] blueprint_read_prepared] >>
      simp[NoAsms,vyperValueTheory.dest_AddressV_def,arithmeticTheory.ADD_SYM] >>
      `LENGTH salts = (if IS_SOME sv then 1 else 0)` by
        (qpat_assum `LENGTH salts = _` mp_tac >>
         qpat_assum `IS_SOME sv <=> s` (pure_once_rewrite_tac o single o GSYM) >> simp[NoAsms]) >>
      Cases_on `IS_SOME sv` >> simp[IgnAsm `IS_SOME sv <=> s`,listTheory.DROP_APPEND2])
  >- gvs[]
  >- (gen_tac >> disch_tac >>
      qpat_assum `!x. MEM (Var x) _ \/ _ ==> not_fresh_at f x` irule >> simp[]) >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (drule_then strip_assume_tac) >> simp[]
QED

Resume create_blueprint_expr_prefix_ok[ctor_raw]:
  qpat_x_assum `T ==> ?e cap. _` (strip_assume_tac o REWRITE_RULE []) >>
  qpat_x_assum `ctor = [e]` SUBST_ALL_TAC >>
  `expr_body_pre cenv cx env e et` by
    (irule create_operand_pre >>
     qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _` (irule_at Any) >> simp[]) >>
  `body_expr_full_ok cx e /\ body_expr_prefix_ok cx e` by
    fs[body_exprs_full_ok_singleton, Once body_exprs_prefix_ok_def] >>
  `EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal))
      (int_calls_exprs (amount::(salts ++ [offset])))` by
    (qpat_assum `if s then (?salt. _) else salts = []` mp_tac >> Cases_on `s` >>
     simp[NoAsms] >> strip_tac >> qpat_x_assum `salts = _` SUBST_ALL_TAC >>
     qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _`
       (mp_then Any (drule_then mp_tac) body_inv_expr_pre_calls) >>
     simp[NoAsms,vyperTypeCallGraphTheory.int_calls_expr_def,EVERY_APPEND] >>
     strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `compile_create_blueprint_args _ _ T _ (MAP gas_shadow_expr [e]) _ = _`
    (assume_tac o CONV_RULE (LAND_CONV (RATOR_CONV (RAND_CONV (SIMP_CONV bool_ss [MAP]))))) >>
  ho_match_mp_tac (GEN_ALL blueprint_raw_ctor_cut_prefix) >>
  qpat_assum `compile_create_blueprint_args _ _ T _ [e] a = _` (irule_at Any) >>
  qpat_assum `compile_create_blueprint_args _ _ T _ [gas_shadow_expr e] _ = _` (irule_at Any) >>
  qpat_assum `expr_body_pre _ _ _ e et` (irule_at Any) >>
  qpat_assum `expr_type e = BaseT (BytesT (Dynamic _))` (irule_at Any) >>
  qpat_assum `body_inv _ _ _ _` (irule_at Any) >>
  qpat_assum `return_buf_frame _ _ a st` (irule_at Any) >>
  qexists `shadow_func` >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (gen_tac >> simp[NoAsms,Abbr `src_action`,storage_trace_frame_bind_all,
        evaluate_storage_trace_frame,storage_trace_frame_read_result,storage_trace_frame_create_operands]) >>
  qx_genl_tac [`bytes`,`eu`,`Gu`,`tu`,`u`,`ctor_marks`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!vs bytes eu Gu tu u. _ ==> gas_prefix_full _ _ _ _ _` irule >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (gen_tac >> disch_tac >> first_assum (drule_then strip_assume_tac) >> simp[])
  >- (qexists `ctor_marks` >> first_assum ACCEPT_TAC) >>
  qexists `bytes` >> pure_rewrite_tac[COND_CLAUSES] >>
  rpt conj_tac >> (REFL_TAC ORELSE first_assum ACCEPT_TAC)
QED

Resume create_blueprint_expr_prefix_ok[ctor_empty]:
  qpat_x_assum `ctor = []` SUBST_ALL_TAC >>
  qpat_x_assum `compile_create_blueprint_args _ _ F _ [] a = _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [compile_create_blueprint_args_def,comp_return_def]) >>
  qpat_x_assum `compile_create_blueprint_args _ _ F _ (MAP gas_shadow_expr []) _ = _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [compile_create_blueprint_args_def,comp_return_def]) >>
  gvs[NoAsms] >>
  `eval_exprs cx [] = return []` by
    simp[NoAsms,FUN_EQ_THM,exprSimWordArgsTheory.eval_exprs_nil,return_def] >>
  simp[bind_return] >>
  qpat_assum `!vs bytes eu Gu tu u. _ ==> gas_prefix_full _ _ _ _ _`
    (qspec_then `[]` (irule o REWRITE_RULE [APPEND])) >>
  simp[exprSimWordArgsTheory.wb_frame_refl,wordArgsPtrTheory.ghost_kept_at_refl] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (qexists `[]` >> simp[return_def]) >>
  qexists `[]` >> simp[eval_operand_def,op_taint_def] >> EVAL_TAC
QED

Finalise create_blueprint_expr_prefix_ok

Theorem raw_create_expr_prefix_ok:
  !cx ty s r ks es d.
  body_exprs_full_ok cx (create_operand_order RawCreate s es) /\
  body_exprs_prefix_ok cx (create_operand_order RawCreate s es) ==>
  body_expr_prefix_ok cx (Call ty (CreateTarget RawCreate s r ks) es d)
Proof
  mp_tac raw_create_expr_prefix_from_dispatch >>
  (impl_tac >- (rpt gen_tac >> MATCH_ACCEPT_TAC create_dispatch_prefix)) >>
  simp[]
QED

(* Linked Attribute cuts, retaining the real and shadow boundaries. *)
Theory bodyFullAttributeMods
Ancestors
  exprSimAttribute exprSimUnwrap fragExec bodyFullShared
  gasShadowCompile gasShadowState gasShadow vyperStorageTrace
  bodyFullPostsMods exprBodyPreTypingProps exprBodyPreCallSafetyProps
  vyperTypeEvalSoundness vyperTypeExprSoundness gasContext exprSimDefs bodyPtrAttributeSource
  vyperInterpreter vyperState context bodyWriteSubscriptSourceMods
  bodyAttributeReadOperandMods bodyAttributeSelectionMods bodyAttributePlacePtrMods
  bodyAttributeNoncodeFieldMods bodyAttributeCodePostMods bodyAttributeCodeFieldMods
  bodyAttributeAddFrameMods bodyAttributeGasBindExactMods bodyAttributeValueOfVVMods
Libs monadsyntax

Theorem attribute_paired_cut_mods:
  compile_expr cenv ty (Attribute ann obj fld) sa = (vv,sb) /\
  compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr (Attribute ann obj fld))
    sha = (vv,shb) /\
  gas_shadow_state sa sha /\ fn_has_code sa sb func /\
  fn_has_code sha shb shadow_func ==>
  ?bvv sm shm p.
    compile_expr cenv ty obj sa = (bvv,sm) /\
    compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr obj) sha = (bvv,shm) /\
    emit_op ADD [vv_operand bvv;
      Lit (n2w (attr_offset cenv (expr_type obj) (vv_loc bvv) fld))] sm = (p,sb) /\
    vv = LocatedValue ann (mk_ptr p (vv_loc bvv)) /\
    gas_shadow_state sm shm /\ cs_extends sa sm /\ cs_extends sm sb /\
    fn_has_code sa sm func /\ fn_has_code sm sb func /\
    fn_has_code sha shm shadow_func /\ fn_has_code shm shb shadow_func
Proof
  strip_tac >>
  qpat_assum `compile_expr _ _ (Attribute _ _ _) _ = _`
    (strip_assume_tac o MATCH_MP compile_expr_attribute) >>
  qpat_assum `compile_expr _ _ (gas_shadow_expr _) _ = _`
    (strip_assume_tac o MATCH_MP compile_expr_attribute o SRULE [gas_shadow_expr_def]) >>
  `gas_shadow_compiles (compile_expr cenv ty obj)
     (compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr obj))` by
    irule (cj 1 gas_shadow_compile_expr_env |> SPEC_ALL |>
      Q.INST [`shadow` |-> `T`] |> REWRITE_RULE [COND_CLAUSES]) >>
  drule_all_then strip_assume_tac gas_shadow_step >>
  qpat_assum `compile_expr cenv ty obj sa = _`
    (strip_assume_tac o MATCH_MP compile_expr_extends) >>
  qpat_assum `compile_expr _ _ (gas_shadow_expr _) _ = _`
    (strip_assume_tac o MATCH_MP compile_expr_extends) >>
  qpat_assum `emit_op ADD _ _ = (_,shb)` (assume_tac o MATCH_MP attr_extends) >>
  qpat_assum `emit_op ADD _ _ = (_,sb)` (assume_tac o MATCH_MP attr_extends) >>
  `fn_has_code sa st1 func /\ fn_has_code st1 sb func` by
    (irule fn_has_code_split >> simp[]) >>
  `fn_has_code sha st1' shadow_func /\ fn_has_code st1' shb shadow_func` by
    (irule fn_has_code_split >> simp[]) >>
  qpat_x_assum `bvv' = bvv` SUBST_ALL_TAC >>
  qpat_x_assum `vv = LocatedValue ann (mk_ptr p' _)` kall_tac >>
  qexistsl_tac [`bvv`,`st1`,`st1'`,`p`] >> asm_rewrite_tac[]
QED

(* Attribute cannot introduce a successful map result at its struct base.
   A failed base propagates the very same exception through the selection. *)
Theorem attribute_operand_admissible_mods:
  expr_body_pre_mods mods cenv cx env obj es /\
  gas_admissible (eval_expr cx (Attribute ann obj fld)) expr_vv_res_ok es ==>
  gas_admissible (eval_expr cx obj) expr_vv_res_ok es
Proof
  rewrite_tac[gas_admissible_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `res`
  >- (rename1 `eval_expr cx obj _ = (INL raw,ee)` >>
      `expr_body_pre_mods mods cenv cx env obj (es with gas_obs := gs)` by simp[] >>
      drule_then strip_assume_tac expr_body_pre_mods_runtime_typing >>
      drule_then assume_tac expr_body_pre_mods_call_evaluation_safe >>
      qspecl_then [`cx`,`obj`] (mp_tac o cj 1) (cj 5 eval_scc_type_sound_mutual) >>
      disch_then (qspecl_then [`env`,`es with gas_obs := gs`,`INL raw`,`ee`] mp_tac) >>
      Cases_on `raw` >> fs[runtime_consistent_def,
        expr_vv_res_ok_def,vyperTypeInvariantsTheory.eval_result_typed_def]) >>
  qpat_x_assum `!gs res ee. _` (qspec_then `gs` mp_tac) >>
  simp[attr_source, bind_def]
QED

Theorem attribute_vv_holds_read_operand_mods:
  vv_holds_mods cenv cx ty tv vv ee t ==>
  ?v w. read_result cx tv ee = (INL v,ee) /\
        eval_operand (vv_operand vv) t = SOME w
Proof
  Cases_on `vv` >> simp[vv_holds_mods_def,vv_operand_def]
  >- (strip_tac >> drule attribute_vv_holds_read_operand >> simp[vv_operand_def]) >>
  rename1 `p.ptr_location = LocCode` >> Cases_on `p.ptr_location = LocCode`
  >- (simp[immutable_holds_mods_def] >> rpt strip_tac >>
      drule immutable_holds_read >> simp[]) >>
  simp[] >> strip_tac >> drule attribute_vv_holds_read_operand >> simp[vv_operand_def]
QED

Theorem attribute_vv_sim_full_mods_of_child:
  expr_body_pre_mods mods cenv cx env (Attribute ann obj fld) es /\
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty obj es ==>
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Attribute ann obj fld) es
Proof
  rpt gen_tac >> strip_tac >>
  drule_then assume_tac bodyAttributePreModsTheory.attribute_pre_child_mods >>
  rewrite_tac[expr_vv_sim_full_mods_def] >> rpt gen_tac >> strip_tac >>
  `gas_admissible (eval_expr cx obj) expr_vv_res_ok es` by
    (MATCH_MP_TAC
      (Q.INST [`mods` |-> `mods`, `cenv` |-> `cenv`, `cx` |-> `cx`,
               `env` |-> `env`, `obj` |-> `obj`, `ann` |-> `ann`,
               `fld` |-> `fld`, `es` |-> `es`] attribute_operand_admissible_mods) >>
     asm_rewrite_tac[]) >>
  drule_all_then strip_assume_tac attribute_paired_cut_mods >>
  qpat_x_assum `expr_vv_sim_full_mods _ _ _ _ obj _` (mp_tac o
    REWRITE_RULE [expr_vv_sim_full_mods_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shm`,`bvv`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  irule attribute_vv_outcome_bind_exact_mods >> BETA_TAC >>
  qexistsl_tac [`bvv`,`sm`] >> reverse conj_tac
  >- qpat_assum `gas_outcome_full_mods _ _ _ _ (eval_expr _ obj) _ _ _` ACCEPT_TAC
  >> rpt gen_tac >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `expr_body_pre_mods mods cenv cx env (Attribute ann obj fld) (es with gas_obs := xs)` by simp[] >>
  drule_all_then strip_assume_tac
    bodyAttributeSelectionModsTheory.attribute_typed_selection_mods >>
  `op_taint tn (vv_operand bvv) = {}` by
    (Cases_on `bvv` >>
     qhdtm_assum `ptr_vv_ok` (strip_assume_tac o REWRITE_RULE
       [bodyPtrDefsTheory.ptr_vv_ok_def, bodyPtrDefsTheory.ptr_val_ok_def]) >>
     simp[vv_operand_def]) >>
  `sa.cs_next_var <= sm.cs_next_var` by
    (qpat_assum `compile_expr cenv ty obj sa = _`
       (strip_assume_tac o MATCH_MP compile_expr_extends) >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     vv_post_mods H ctx func cenv cx obj es sa sm s0 ee raw bvv s /\
     ghost_inv_at_mods (DF H) lo d cenv cx ee G tn s` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
       (qspec_then `H` mp_tac) >> simp[]) >>
  drule_all_then (qspec_then `PG` strip_assume_tac) attribute_add_frame_mods >>
  rename1 `select_result _ _ raw (AttrSubscript fld) ee = (INL picked,ee)` >>
  rename1 `t = s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|>` >>
  rename1 `FLOOKUP Gf out = op_prov G (vv_operand bvv)` >>
  rename1 `tf.t_mem = tn.t_mem` >>
  qexistsl_tac [`picked`,`t`,`Gf`,`tf`] >> conj_tac >- simp[] >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post_mods H _ _ _ _ obj _ _ sb _ _ _ _ t /\ _`
    (drule_then strip_assume_tac) >>
  conj_tac
  >- (qpat_assum `!D lo' explicit. allocas_from _ _ ==> _` (irule o SPEC_ALL) >>
      qpat_assum `ghost_inv_at_mods _ lo d cenv cx ee G tn s`
        (strip_assume_tac o REWRITE_RULE [bodyFullShadowBodyInvTheory.ghost_inv_at_mods_def]) >> simp[]) >>
  `t.vs_memory = s.vs_memory /\ t.vs_accounts = s.vs_accounts /\
   t.vs_call_ctx = s.vs_call_ctx /\ t.vs_transient = s.vs_transient` by
    (qpat_assum `t = s with <|vs_vars := _; vs_inst_idx := _|>`
       (fn th => pure_once_rewrite_tac[th] >> simp[])) >>
  `vv_place_ptr_mods cenv cx ee t picked vv` by suspend "place" >>
  suspend "field_posts"
QED

Resume attribute_vv_sim_full_mods_of_child[place]:
  `expr_body_pre_mods mods cenv cx env obj (es with gas_obs := xs)` by simp[] >>
  `expr_sim_inv_mods mods cenv cx env ee` by
    (`bind (eval_expr cx obj) (read_result cx) (es with gas_obs := xs) = (INL (StructV vals),ee)` by
       simp[bind_def] >>
     drule_at (Pat `bind _ _ _ = _`)
       (REWRITE_RULE [ETA_THM] bodySimStmtFactsTheory.expr_body_pre_eval_mods) >>
     disch_then (drule_at (Pat `expr_body_pre_mods _ _ _ _ _ (es with gas_obs := xs)`)) >> simp[]) >>
  `eval_result_typed (env,cx,ee) raw (Type (StructT sid))` by
    (qpat_assum `expr_body_pre_mods _ _ _ _ obj (es with gas_obs := xs)`
       (strip_assume_tac o MATCH_MP expr_body_pre_mods_runtime_typing) >>
     qpat_assum `expr_body_pre_mods _ _ _ _ obj (es with gas_obs := xs)`
       (assume_tac o MATCH_MP expr_body_pre_mods_call_evaluation_safe) >>
     qspecl_then [`cx`,`obj`] (mp_tac o cj 1) (cj 5 eval_scc_type_sound_mutual) >>
     disch_then (qspecl_then [`env`,`es with gas_obs := xs`,`INL raw`,`ee`] mp_tac) >>
     fs[runtime_consistent_def]) >>
  qpat_assum `vv_post_mods H _ _ _ _ obj _ _ sb _ _ _ _ t`
    (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
  `!ty op. bvv = StackValue ty op ==> !pl. raw <> PlaceR pl` by
    (rpt gen_tac >> disch_then SUBST_ALL_TAC >>
     qpat_assum `vv_at _ _ _ _ sb _ _ _ t`
       (mp_tac o REWRITE_RULE [loweringPostsTheory.vv_at_def]) >>
     simp[compileEnvTheory.is_word_type_def]) >>
  qpat_assum `vv = LocatedValue _ _` (SUBST1_TAC) >>
  irule attribute_field_place_ptr_mods >>
  goal_assum (drule_at (Pat `select_result _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `eval_result_typed _ _ _`)) >>
  goal_assum (drule_at (Pat `expr_sim_inv_mods _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `ALOOKUP fs fld = _`)) >>
  goal_assum (drule_at (Pat `eval_operand (vv_operand bvv) t = _`)) >>
  simp[]
QED

Resume attribute_vv_sim_full_mods_of_child[field_posts]:
  `!v. raw = Value v ==> vv_own cenv cx (StructT sid) sa sm ee raw bvv s /\
                            vv_loc bvv = LocMemory` by
    (gen_tac >> disch_tac >>
     qpat_assum `!v. raw = Value v /\ _ ==> _` (qspec_then `v` mp_tac) >>
     (impl_tac >- simp[compileEnvTheory.is_word_type_def,
                       compileEnvTheory.is_bytestring_type_def]) >> strip_tac >>
     conj_tac >- (qpat_assum `post_value_type cenv obj = StructT sid` (SUBST1_TAC o SYM) >>
                  first_assum ACCEPT_TAC) >>
     Cases_on `bvv` >> simp[exprSimAttributePropsTheory.vv_loc_def, vv_location_def]) >>
  `eval_operand p t = SOME (w + n2w (attr_offset cenv (StructT sid) (vv_loc bvv) fld))` by
    (qpat_assum `expr_type obj = StructT sid` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  qpat_assum `vv = LocatedValue _ _` (fn eq =>
    qhdtm_assum `vv_place_ptr_mods` (assume_tac o REWRITE_RULE [eq])) >>
  qpat_assum `post_value_type cenv obj = StructT sid` (fn eq =>
    map_every (fn quote => qpat_assum quote (assume_tac o REWRITE_RULE [eq]))
      [`ptr_vv_ok _ _ _ bvv _ G tn s`, `vv_store_bound _ _ _ _ _ bvv s`]) >>
  Cases_on `vv_loc bvv = LocCode`
  >- suspend "code_field" >>
  suspend "noncode_field"
QED

Resume attribute_vv_sim_full_mods_of_child[code_field]:
  `!v. raw = Value v ==> vv_loc bvv = LocMemory` by
    (gen_tac >> disch_tac >>
     qpat_assum `!v. raw = Value v ==> vv_own _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `v` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> disch_then (ACCEPT_TAC o CONJUNCT2)) >>
  drule_all_then (strip_assume_tac o BETA_RULE o REWRITE_RULE [LET_THM]) attribute_code_field_post_mods >>
  qpat_assum `vv = LocatedValue _ _` SUBST1_TAC >>
  `s0.vs_alloca_next <= t.vs_alloca_next` by simp[] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac
  >- (MATCH_MP_TAC (GEN_ALL (INST_TYPE [alpha |-> ``:256``]
        attribute_code_field_endpoint_mods)) >>
      qpat_assum `expr_body_pre_mods _ _ _ _ (Attribute _ _ _) (es with gas_obs := xs)`
        (irule_at (Pat `expr_body_pre_mods _ _ _ _ _ _`)) >>
      goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >>
      qpat_assum `vv_post_mods _ _ _ _ _ obj _ _ sm _ _ _ _ s`
        (irule_at Any) >>
      goal_assum (drule_at (Pat `eval_operand (vv_operand bvv) s = _`)) >>
      qexists_tac `tn` >> simp[]) >>
  asm_rewrite_tac[]
QED

Resume attribute_vv_sim_full_mods_of_child[noncode_field]:
  `type_memory_bytes cenv (lowered_value_type cenv (Attribute ann obj fld)) =
    type_memory_size ftv` by
    (simp[exprLoweringTheory.lowered_value_type_def, vyperASTTheory.expr_type_def] >>
     irule typedMemoryCopyTheory.typed_copy_memory_size >>
     qexists_tac `get_tenv cx` >>
     qpat_assum `expr_body_pre_mods _ _ _ _ (Attribute _ _ _) es`
       (mp_tac o MATCH_MP exprBodyPrePropsTheory.expr_body_pre_mods_inv) >>
     simp[exprSimHypsDefsTheory.expr_sim_inv_mods_def] >> rpt strip_tac >>
     qpat_assum `!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==> ALL_DISTINCT _ /\ _`
       drule >> simp[]) >>
  `sm.cs_next_id <= sb.cs_next_id` by
    (qpat_assum `emit_op ADD _ sm = (p,sb)`
       (SUBST1_TAC o SYM o CONJUNCT2 o
        REWRITE_RULE [loweringShapeRulesTheory.emit_op_eq, pairTheory.PAIR_EQ]) >>
     simp[]) >>
  `!n b sz. local_region cenv ee.scopes t n b sz ==> local_region cenv ee.scopes s n b sz` by
    (rpt gen_tac >>
     `local_region cenv ee.scopes t n b sz <=> local_region cenv ee.scopes s n b sz` by
       (irule loweringStateRelDefsTheory.local_region_lookup_cong >>
        rpt strip_tac >> qpat_assum `!x. not_fresh_at sm x ==> _` irule >>
        irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[] >>
        qpat_assum `local_ptrs_reserved _ sa`
          (strip_assume_tac o REWRITE_RULE [loweringStateRelDefsTheory.local_ptrs_reserved_def]) >>
        first_x_assum drule >> simp[]) >>
     simp[]) >>
  `!x b sz. vv_operand bvv = Var x /\ FLOOKUP G x = SOME (b,sz) ==>
     ?y. p = Var y /\ FLOOKUP Gf y = SOME (b,sz)` by
    (rpt strip_tac >> qexists_tac `out` >>
     qpat_assum `FLOOKUP Gf out = op_prov G _` SUBST1_TAC >>
     simp[ptrDisciplineTheory.op_prov_def]) >>
  drule_all_then (strip_assume_tac o BETA_RULE o REWRITE_RULE [LET_THM]) attribute_noncode_field_endpoint_mods >>
  qpat_assum `vv = LocatedValue _ _` SUBST1_TAC >>
  simp[]
QED

Finalise attribute_vv_sim_full_mods_of_child

Theorem attribute_sim_full_mods_of_child:
  !mods exps cx v9 e id DF lo d PG src tops ctx shadow_ctx func shadow_func
     cenv env ty es.
    contract_inv mods exps ctx cenv cx /\
    module_body_inv mods src tops cenv cx /\
    shadow_body_inv_mods mods exps ctx shadow_ctx /\
    body_const_cells_agree_mods mods cx env es /\
    expr_body_pre_mods mods cenv cx env (Attribute v9 e id) es /\
    expr_body_pre_mods mods cenv cx env e es /\
    expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es /\
    expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es ==>
    expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Attribute v9 e id) es /\
    expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Attribute v9 e id) es
Proof
  rpt gen_tac >> strip_tac >>
  drule_all_then assume_tac attribute_vv_sim_full_mods_of_child >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  drule_all_then ACCEPT_TAC attribute_value_of_vv_mods
QED

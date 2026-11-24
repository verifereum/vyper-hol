(* Typed source array and machine key at a reached runtime-code selection. *)
Theory bodyArrayFramedCodeSelectTypedMods
Ancestors
  bodyArrayFramedCodeSelectInputsDefsMods bodyArrayFramedCodeBaseMods
  bodyArrayNoCopyCutsMods bodyArrayNoCopySourceMods bodySubscriptArrayRouteDefsMods
  bodyFullPostsMods bodySimStmtFacts exprBodyPreProps exprSimArith
  exprSimSubscriptArraySuffix targetSubscriptMemory
  arithmeticProps compileEnv loweringPosts valueEncoding vyperTypeConstantFold
  vyperTypeEvalCaseProofs vyperTypeExprResult vyperTypeExprSoundness
  vyperTypeSystem vyperTyping vyperValue vyperStorageFootprint words integer

(* The scalar part of the index post is independent of the linked frame. *)
Theorem framed_code_index_post_word[local]:
  is_int_type (expr_type idx) /\
  evaluate_type (get_tenv cx) (expr_type idx) = SOME tv /\ value_has_type tv key /\
  expr_post H ctx func cenv cx idx mid sm st2 s fin key iop it ==>
  ?i iw. key = IntV i /\ eval_operand iop it = SOME iw /\
    i = (if is_signed_type (expr_type idx) then w2i iw else &(w2n iw))
Proof
  strip_tac >>
  Cases_on `expr_type idx` >> gvs[is_int_type_def] >>
  rename1 `is_int_type (BaseT bt)` >> Cases_on `bt` >>
  gvs[is_int_type_def, evaluate_type_def, value_has_type_def, well_formed_type_def] >>
  Cases_on `key` >> gvs[value_has_type_def] >>
  fs[expr_post_def, expr_val_rel_def, evaluate_type_def, AllCaseEqs(),
     is_word_type_def, typed_val_to_w256_def, val_to_w256_def] >>
  qspecl_then [`expr_type idx`,`i`] mp_tac math_val_i2w >>
  gvs[math_val_def, is_signed_type_def, type_bits_def, within_int_bound_def]
QED

Theorem framed_code_index_runtime_type[local]:
  expr_body_pre_mods mods cenv cx env idx es /\
  bind (eval_expr cx idx) (read_result cx) es = (INL key,fin) ==>
  ?tv. evaluate_type (get_tenv cx) (expr_type idx) = SOME tv /\ value_has_type tv key
Proof
  strip_tac >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  drule_all_then strip_assume_tac (REWRITE_RULE [ETA_AX] expr_body_pre_eval_mods) >>
  fs[value_runtime_typed_def] >> qexists `tv` >>
  qpat_assum `env.type_defs = get_tenv cx` (SUBST1_TAC o SYM) >> simp[]
QED

Theorem framed_code_select_inputs_mods:
  linked_subscript_array_context_mods mods exps cx ann obj idx
    DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es et bd /\
  subscript_array_framed_code_case_mods cenv cx obj idx bd /\
  array_nocopy_cut_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty obj idx et bd st0
    (es,s0,G0,tn0) (sa,sm,st2,sb,bvv,iop,dst,loc)
    (shadow_sa,shadow_sm,shadow_st2,shadow_sb)
    (gs1,mid,raw,s,G1,tn1) (gs2,fin,key,it,Gi,tni) ==>
  ?p etv av i iw w. framed_code_select_inputs_mods cenv cx env ty obj idx ann et bd
    (es,s0,G0,tn0) (sa,sm,st2,sb,bvv,iop,dst,loc)
    (gs1,mid,raw,s,G1,tn1) (gs2,fin,key,it,Gi,tni) p etv av i iw w
Proof
  strip_tac >>
  drule_all_then (qx_choosel_then [`p`,`etv`,`av`,`w`] strip_assume_tac)
    framed_code_reached_base_mods >>
  `~subscript_reads_base cx obj idx` by fs[subscript_array_framed_code_case_mods_def] >>
  drule_all_then strip_assume_tac array_nocopy_base_inputs_mods >>
  `eval_expr cx obj (es with gas_obs := gs1) = (INL raw,mid) /\
   bind (eval_expr cx idx) (read_result cx) (mid with gas_obs := gs2) = (INL key,fin) /\
   storage_trace_domain cx st0 fin.storage_trace` by
    (qhdtm_assum `array_nocopy_cut_mods`
       (strip_assume_tac o REWRITE_RULE [array_nocopy_cut_mods_def]) >> simp[]) >>
  drule_all_then strip_assume_tac array_nocopy_index_inputs_mods >>
  qhdtm_x_assum `linked_subscript_array_context_mods`
    (strip_assume_tac o REWRITE_RULE [linked_subscript_array_context_mods_def]) >>
  `ann = et /\ is_int_type (expr_type idx)` by
    (qpat_assum `expr_body_pre_mods _ _ _ _ (Subscript _ _ _) _`
       (mp_then Any assume_tac expr_body_pre_mods_well_typed) >>
     drule_all constant_subscript_type_ok >> simp[subscript_type_ok_def]) >>
  `expr_body_pre_mods mods cenv cx env idx (mid with gas_obs := gs2)` by simp[] >>
  drule_all_then strip_assume_tac framed_code_index_runtime_type >>
  `valid_horizon cx st0 (storage_trace_horizon fin.storage_trace) fin.storage_trace` by
    fs[storage_trace_domain_def] >>
  drule_all_then strip_assume_tac array_nocopy_cut_posts_mods >>
  qhdtm_x_assum `expr_post_mods`
    (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
  drule_all_then (qx_choosel_then [`i`,`iw`] strip_assume_tac) framed_code_index_post_word >>
  drule_all_then assume_tac target_memory_array_length_bound >>
  qexistsl_tac [`p`,`etv`,`av`,`i`,`iw`,`w`] >>
  simp[framed_code_select_inputs_mods_def, array_index_word_bounds, contextTheory.vv_location_def]
QED

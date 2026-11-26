(* Type and operand facts at a reached immutable array key. *)
Theory bodyArrayReachedImmutableKeyMods
Ancestors
  bodyArrayNoCopyCutsMods bodyArrayNoCopySourceMods bodyArraySlotOperandFrameMods
  bodySubscriptArrayRouteDefsMods bodyFullPostsMods bodyAssignNameLinkedSetup
  bodySimStmtFacts exprBodyPreProps exprSimHypsDefs exprSimArith exprLowering exprSimWordArgs
  loweringPosts exprReasonOperand exprOperandVar arithmeticProps valueEncoding
  compileEnv context vyperTypeConstantFold vyperTypeExprSoundness
  vyperTypeEvalCaseProofs vyperTypeInvariants vyperInterpreter vyperState vyperAST
  vyperTypeSystem vyperTyping vyperValue vyperStorageFootprint words integer

Theorem reached_key_word[local]:
  is_int_type (expr_type idx) /\
  evaluate_type (get_tenv cx) (expr_type idx) = SOME tv /\
  value_has_type tv key /\
  expr_post_mods H ctx func cenv cx idx mid sm st2 s fin key iop it ==>
  ?i iw. key = IntV i /\
    eval_operand iop it = SOME iw /\
    i = (if is_signed_type (expr_type idx) then w2i iw else &(w2n iw))
Proof
  strip_tac >>
  Cases_on `expr_type idx` >> gvs[is_int_type_def] >>
  rename1 `is_int_type (BaseT bt)` >> Cases_on `bt` >>
  gvs[is_int_type_def, evaluate_type_def, value_has_type_def, well_formed_type_def] >>
  Cases_on `key` >> gvs[value_has_type_def] >>
  fs[expr_post_mods_def, expr_post_def, expr_val_rel_def, evaluate_type_def,
     AllCaseEqs(), is_word_type_def, typed_val_to_w256_def, val_to_w256_def] >>
  mp_tac math_val_i2w >>
  disch_then (qspec_then `expr_type idx` (qspec_then `i` mp_tac)) >>
  gvs[math_val_def, is_signed_type_def, type_bits_def, within_int_bound_def]
QED

Theorem reached_is_int_word[local]:
  is_int_type t ==> is_word_type t
Proof
  Cases_on `t` >> simp[is_int_type_def, is_word_type_def] >>
  rename1 `is_int_type (BaseT bt)` >> Cases_on `bt` >>
  simp[is_int_type_def, is_word_type_def]
QED

Theorem array_reached_immutable_key_mods:
  linked_subscript_array_context_mods mods exps cx ann obj idx
    DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es et bd /\
  ~subscript_reads_base cx obj idx /\
  array_nocopy_cut_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty obj idx et bd st0
    (es,s0,G0,tn0) (sa,sm,st2,sb,bvv,iop,dst,loc)
    (shadow_sa,shadow_sm,shadow_st2,shadow_sb)
    (gs1,mid,raw,s,G1,tn1) (gs2,fin,key,it,Gi,tni) ==>
  ann = et /\
  post_value_type cenv idx = expr_type idx /\
  is_word_type (expr_type idx) /\
  expr_sim_inv_mods mods cenv cx env fin /\
  (!l. iop <> Label l) /\
  (?i iw. key = IntV i /\ eval_operand iop it = SOME iw /\
    i = (if is_signed_type (expr_type idx) then w2i iw else &(w2n iw))) /\
  (!etv. evaluate_type (get_tenv cx) et = SOME etv ==>
     type_memory_bytes cenv et = type_memory_size etv) /\
  (!p w. bvv = LocatedValue (ArrayT et bd) p /\
    eval_operand p.ptr_operand s = SOME w ==>
      (!l. p.ptr_operand <> Label l) /\ eval_operand p.ptr_operand it = SOME w)
Proof
  strip_tac >>
  qhdtm_assum `array_nocopy_cut_mods`
    (strip_assume_tac o REWRITE_RULE [array_nocopy_cut_mods_def]) >>
  drule_all_then strip_assume_tac array_nocopy_base_inputs_mods >>
  drule_all_then strip_assume_tac array_nocopy_index_inputs_mods >>
  `expr_body_pre_mods mods cenv cx env idx (mid with gas_obs := gs2)` by simp[] >>
  qpat_assum `bind (eval_expr cx idx) _ (mid with gas_obs := gs2) = _`
    (mp_then (Pat `bind _ _ _ = _`) mp_tac (REWRITE_RULE [ETA_AX] expr_body_pre_eval_mods)) >>
  disch_then (drule_then strip_assume_tac) >>
  `value_runtime_typed env (expr_type idx) key` by simp[] >>
  qhdtm_assum `linked_subscript_array_context_mods`
    (strip_assume_tac o REWRITE_RULE [linked_subscript_array_context_mods_def]) >>
  `ann = et /\ is_int_type (expr_type idx)` by
    (qpat_assum `expr_body_pre_mods _ _ _ _ (Subscript _ _ _) _`
       (mp_then Any assume_tac expr_body_pre_mods_well_typed) >>
     drule_all constant_subscript_type_ok >> simp[subscript_type_ok_def]) >>
  drule_then assume_tac reached_is_int_word >>
  `?tv. evaluate_type (get_tenv cx) (expr_type idx) = SOME tv /\ value_has_type tv key` by
    (drule_then assume_tac expr_sim_inv_mods_env >>
     drule_then assume_tac env_consistent_type_defs_get_tenv >>
     fs[value_runtime_typed_def] >> qexists `tv` >>
     qpat_assum `env.type_defs = get_tenv cx` (SUBST1_TAC o SYM) >> simp[]) >>
  `valid_horizon cx st0 (storage_trace_horizon fin.storage_trace) fin.storage_trace` by
    fs[storage_trace_domain_def] >>
  drule_all_then strip_assume_tac array_nocopy_cut_posts_mods >>
  drule_all_then assume_tac reached_key_word >>
  `well_typed_expr env idx` by
    (qpat_assum `expr_body_pre_mods _ _ _ _ idx mid`
      (mp_then Any ACCEPT_TAC expr_body_pre_mods_well_typed)) >>
  `!id t. FLOOKUP env.var_types id = SOME t ==>
    ?q sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var q) sz)` by
    fs[expr_sim_inv_mods_def] >>
  `!l. iop <> Label l` by (drule_all_then ACCEPT_TAC lower_compile_expr_not_label) >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> drule_all_then ACCEPT_TAC assign_name_memory_bytes_mods) >>
  rpt gen_tac >> strip_tac >>
  `compile_expr cenv ty obj sa = (LocatedValue (ArrayT et bd) p,sm)` by simp[] >>
  `reason_uniform_shape compile_expr cenv ty obj` by
    (irule compile_expr_reason_uniform >> qexists `env` >> simp[]) >>
  `!l. p.ptr_operand <> Label l` by
    (qhdtm_x_assum `reason_uniform_shape`
       (strip_assume_tac o REWRITE_RULE [reason_uniform_shape_def]) >>
     first_x_assum drule >> simp[reason_result_shape_def]) >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sm x` by
    (qpat_assum `compile_expr cenv ty obj sa = (LocatedValue _ _,sm)`
       (mp_then Any mp_tac (cj 1 compiler_compile_var)) >> simp[vv_operand_def]) >>
  `wb_frame cenv mid fin sm s it` by
    (qhdtm_assum `expr_post_mods` (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
     drule_then ACCEPT_TAC expr_post_frame) >>
  simp[] >> drule_all_then ACCEPT_TAC array_slot_operand_frame_mods
QED

(* A rejected fixed-memory selection exits at the literal bounds check. *)
Theory bodyArrayFramedMemoryRejectMods
Ancestors
  bodySubscriptArrayRouteDefsMods bodyArrayNoCopyCutsMods
  bodyFullSubscriptArrayCodeBounds gasOutcomeFullPostMods
  exprSimSubscriptArraySuffix exprSimSubscriptArraySource exprSimArrayIndex
  exprLoweringProps exprBodyPreTypingProps exprBodyPreCallSafetyProps
  vyperTypeEvalSoundness vyperTypeEvalCaseProofs vyperTypeExprResult
  vyperTypeInvariants vyperTypeSystem vyperPlaceTyping vyperState
  bodyFullShadowBodyInv bodyPtrDefs fragExec exprSimDefs
  compileEnv pair vyperTypeExprSoundness exprBodyPreProps venomState ptrDiscipline
Libs
  monadsyntax

Theorem fixed_reject_check_code[local]:
  compile_array_subscript base_op idx F n ws sz sgn loader sa = (dst,sb) /\
  fn_has_code sa sb func ==>
  ?sc. array_bounds_check idx (Lit (n2w n)) sgn sa = ((),sc) /\
       fn_has_code sa sc func
Proof
  simp[compile_array_subscript_split, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[oneTheory.one] >>
  rename1 `array_bounds_check _ _ _ sa = ((),sc)` >>
  `ci_mono sa sc` by
    (qpat_assum `array_bounds_check _ _ _ _ = _`
       (SUBST1_TAC o SYM o PURE_REWRITE_RULE [SND] o Q.AP_TERM `SND`) >>
     Cases_on `sgn` >> simp[NoAsms, array_bounds_check_def, array_bounds_valid_def] >>
     rpt (FIRST [irule ci_mono_bind >> conj_tac,
                 gen_tac >> BETA_TAC, irule ci_mono_emit_op,
                 irule ci_mono_emit_void, irule ci_mono_comp_return])) >>
  `ci_mono sc sb` by
    (qpat_assum `array_elem_ptr _ _ _ _ _ _ = _`
       (SUBST1_TAC o SYM o PURE_REWRITE_RULE [SND] o Q.AP_TERM `SND`) >>
     simp[NoAsms, array_elem_ptr_def] >>
     rpt (FIRST [irule ci_mono_bind >> conj_tac,
                 gen_tac >> BETA_TAC, irule ci_mono_emit_op, irule ci_mono_comp_return])) >>
  metis_tac[fn_has_code_split, ci_mono_def]
QED

Theorem framed_memory_place_type_at_key[local]:
  expr_body_pre_mods mods cenv cx env obj es /\
  eval_expr cx obj es = (INL (PlaceR p),mid) /\
  evaluate_type (get_tenv cx) (expr_type obj) = SOME tv /\
  (!tr slot vt. p <> StoragePlace tr slot vt) /\
  fin.scopes = mid.scopes /\ fin.immutables = mid.immutables ==>
  runtime_place_typed cx fin p tv
Proof
  strip_tac >>
  drule_then strip_assume_tac expr_body_pre_mods_runtime_typing >>
  drule_then assume_tac expr_body_pre_mods_call_evaluation_safe >>
  fs[runtime_consistent_def] >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  `runtime_place_typed cx mid p tv` by
    (qspecl_then [`cx`,`obj`] (mp_tac o cj 1) (cj 5 eval_scc_type_sound_mutual) >>
     disch_then (qspecl_then [`env`,`es`,`INL (PlaceR p)`,`mid`] mp_tac) >>
     simp[eval_result_typed_def]) >>
  Cases_on `p` >> gvs[runtime_place_typed_memory] >>
  qpat_x_assum `runtime_place_typed _ mid _ _` mp_tac >>
  Cases_on `ALOOKUP mid.immutables cx.txn.target` >>
  simp[runtime_place_typed_immutable, get_immutables_def,
       get_address_immutables_def, bind_def, return_def, raise_def,
       lift_option_type_def, AllCaseEqs()]
QED

Theorem framed_memory_source_reject[local]:
  expr_body_pre_mods mods cenv cx env obj es /\
  eval_expr cx obj es = (INL raw,mid) /\
  expr_type obj = ArrayT et (Fixed n) /\
  evaluate_type (get_tenv cx) (ArrayT et (Fixed n)) = SOME (ArrayTV etv (Fixed n)) /\
  (!tr slot vt. raw <> PlaceR (StoragePlace tr slot vt)) /\
  fin.scopes = mid.scopes /\ fin.immutables = mid.immutables /\
  read_result cx raw fin = (INL (ArrayV av),fin) /\
  ~valid_index (ArrayTV etv (Fixed n)) av i ==>
  select_result cx (ArrayT et (Fixed n)) raw (ValueSubscript (IntV i)) fin =
    (INR (Error (RuntimeError "evaluate_subscripts array_index")),fin)
Proof
  strip_tac >>
  `evaluate_subscripts (ArrayTV etv (Fixed n)) (ArrayV av) [ValueSubscript (IntV i)] =
     INR (RuntimeError "evaluate_subscripts array_index")` by
    (irule evaluate_array_subscript_oob >> simp[]) >>
  Cases_on `raw`
  >~ [`Value v`] >-
    (gvs[read_result_def, return_def] >> drule_then (fn th => simp[th, bind_def, lift_sum_def, raise_def])
       select_value_result)
  >~ [`HashMapRef _ _ _ _`] >- gvs[read_result_def, raise_def] >>
  `!tr slot vt. p <> StoragePlace tr slot vt` by fs[] >>
  `evaluate_type (get_tenv cx) (expr_type obj) = SOME (ArrayTV etv (Fixed n))` by simp[] >>
  drule_all_then assume_tac framed_memory_place_type_at_key >>
  drule_all select_nonstorage_place_error >> simp[]
QED

Theorem framed_memory_index_word[local]:
  well_typed_expr env (Subscript ann obj idx) /\ expr_type obj = ArrayT et (Fixed n) ==>
  is_word_type (post_value_type cenv idx)
Proof
  strip_tac >>
  `is_int_type (expr_type idx)` by
    (qpat_x_assum `well_typed_expr _ (Subscript _ _ _)` mp_tac >>
     simp[Once well_typed_expr_def] >> strip_tac >> gvs[subscript_type_ok_def] >>
     drule type_place_expr_vtype_annotation >> strip_tac >> Cases_on `vt` >>
     gvs[vtype_annotation_ok_def, subscript_vtype_def, AllCaseEqs()]) >>
  `is_word_type (expr_type idx)` by
    (Cases_on `expr_type idx` >> gvs[is_int_type_def] >>
     rename1 `is_int_type (BaseT bt)` >> Cases_on `bt` >>
     gvs[is_int_type_def, is_word_type_def]) >> simp[]
QED

Theorem framed_memory_select_oob_mods:
  linked_subscript_array_context_mods mods exps cx ann obj idx
    DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es et (Fixed n) /\
  subscript_array_framed_memory_case_mods cenv cx obj idx et (Fixed n) /\
  array_nocopy_cut_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty obj idx et (Fixed n) st0
    (es,s0,G0,tn0) (sa,sm,st2,sb,bvv,iop,dst,loc)
    (shadow_sa,shadow_sm,shadow_st2,shadow_sb)
    (gs1,mid,raw,s,G1,tn1) (gs2,fin,IntV i,it,Gi,tni) /\
  expr_body_pre_mods mods cenv cx env obj (es with gas_obs := gs1) /\
  evaluate_type (get_tenv cx) (ArrayT et (Fixed n)) = SOME (ArrayTV etv (Fixed n)) /\
  fin.scopes = mid.scopes /\ fin.immutables = mid.immutables /\
  read_result cx raw fin = (INL (ArrayV av),fin) /\
  eval_operand iop it = SOME iw /\
  (valid_index (ArrayTV etv (Fixed n)) av i <=>
   idx_in_range (is_signed_type (expr_type idx)) iw (n2w n)) /\
  (!x. iop = Var x ==> not_fresh_at st2 x) /\ (!l. iop <> Label l) /\
  ~valid_index (ArrayTV etv (Fixed n)) av i ==>
  array_select_outcome_mods (DF,lo,d,ctx,shadow_ctx,PG,func)
    cenv cx ann obj idx et (Fixed n) st0
    (es,s0,G0,tn0) (sa,sb,dst,loc) (raw,IntV i) (fin,it,Gi,tni)
Proof
  rewrite_tac[linked_subscript_array_context_mods_def, array_nocopy_cut_mods_def] >> strip_tac >>
  qpat_x_assum `compile_array_subscript _ _ _ _ _ _ _ _ _ = _` mp_tac >> simp[] >> strip_tac >>
  drule_all_then strip_assume_tac fixed_reject_check_code >>
  `!tr slot vt. raw <> PlaceR (StoragePlace tr slot vt)` by
    (qpat_assum `subscript_array_framed_memory_case_mods _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [subscript_array_framed_memory_case_mods_def]) >>
     rpt strip_tac >> gvs[]) >>
  drule_all_then assume_tac framed_memory_source_reject >>
  `!tail. select_result cx (ArrayT et (Fixed n)) raw (ValueSubscript (IntV i))
               (fin with gas_obs := tail) =
             (INR (Error (RuntimeError "evaluate_subscripts array_index")),fin with gas_obs := tail)` by
    (gen_tac >>
     `SND (select_result cx (ArrayT et (Fixed n)) raw (ValueSubscript (IntV i)) fin) = fin` by simp[] >>
     drule_all select_result_nonstorage_gas_obs >> simp[]) >>
  `is_word_type (post_value_type cenv idx)` by
    (qpat_assum `expr_body_pre_mods _ _ _ _ (Subscript _ _ _) _`
       (assume_tac o MATCH_MP expr_body_pre_mods_well_typed) >>
     drule_all framed_memory_index_word >> simp[]) >>
  `op_taint tni iop = {} /\ op_prov Gi iop = NONE` by fs[ptr_val_ok_def] >>
  `eval_operand (Lit (n2w n)) it = SOME (n2w n) /\
   op_taint tni (Lit (n2w n)) = {} /\ op_prov Gi (Lit (n2w n)) = NONE /\
   (!x. iop = Var x \/ Lit (n2w n) = Var x ==> not_fresh_at st2 x) /\
   (!l. iop <> Label l /\ Lit (n2w n) <> Label l)` by
    simp[eval_operand_def, op_taint_def, op_prov_def] >>
  `~idx_in_range (is_signed_type (expr_type idx)) iw (n2w n)` by
    (qpat_assum `valid_index _ _ _ <=> _` (fn th => simp[GSYM th])) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp it)` by simp[] >>
  drule_all array_bounds_check_joint_oob_frame >>
  disch_then (qspec_then `PG` (qx_choosel_then [`Gf`,`tnf`,`sf`] strip_assume_tac)) >>
  simp[array_select_outcome_mods_def] >>
  irule gas_outcome_full_mods_exit >> simp[] >>
  qexistsl_tac [`Gf`,`fin`,`Abort Revert_abort sf`,
                `INR (Error (RuntimeError "evaluate_subscripts array_index"))`,`tnf`] >>
  simp[exit_result_def,expr_exit_def,halt_exit_def] >>
  gen_tac >> strip_tac >>
  `allocas_from lo it` by
    (qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> _`
       (drule_then (strip_assume_tac o REWRITE_RULE [ghost_inv_at_mods_def])) >> simp[]) >>
  first_x_assum irule >> simp[]
QED

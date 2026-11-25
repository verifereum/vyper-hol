(* Source-only field selection, independent of the compiled operand and its owner. *)
Theory bodyAttributeTypedSelectionMods
Ancestors
  exprSimAttribute exprSimAttributeFields exprSimFieldLayout exprSimHypsDefs
  bodySimStmtFacts exprBodyPreProps placeMemoryTypedBase typedMemoryCopy
  vyperTypeEvalCaseProofs vyperTypeExprSoundness valueEncodingTyping
  exprSimDefs exprLowering loweringPosts vyperInterpreter vyperState vyperValue vyperAST
  vyperTypeSystem vyperTypeInvariants compileEnv finite_map list pair
Libs monadsyntax

Theorem attribute_fields_zip[local]:
  !fields tvs.
    OPT_MMAP (evaluate_type tenv) (MAP (FST o SND) fields) = SOME tvs /\
    EVERY (\(nm,ty,sz). !tv. evaluate_type tenv ty = SOME tv ==>
                            sz = type_memory_size tv) fields ==>
    fields_layout fields (ZIP (MAP FST fields,tvs))
Proof
  Induct >> simp[fields_layout_def] >> PairCases >> rpt strip_tac >> gvs[fields_layout_def]
QED

Theorem attribute_fields_layout_mods[local]:
  expr_sim_inv_mods mods cenv cx env es /\
  evaluate_type (get_tenv cx) (StructT sid) = SOME tv ==>
  ?fs. tv = StructTV fs /\
       fields_layout (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fs
Proof
  strip_tac >>
  `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx)` by
    fs[expr_sim_inv_mods_def] >>
  drule_all_then strip_assume_tac typed_memory_struct_evaluation >>
  `fields_layout fields (ZIP (MAP FST fields,tvs))` by
    (irule attribute_fields_zip >> qexists_tac `get_tenv cx` >>
     conj_tac
     >- gvs[vyperValueTheory.evaluate_types_OPT_MMAP] >>
     fs[expr_sim_inv_mods_def] >> metis_tac[]) >>
  qexists_tac `ZIP (MAP FST fields,tvs)` >> simp[get_struct_fields_def] >>
  qpat_assum `MAP FST fields = MAP FST args` (SUBST1_TAC o SYM) >>
  first_assum ACCEPT_TAC
QED

Theorem attribute_struct_post_type_mods[local]:
  expr_sim_inv_mods mods cenv cx env es /\ well_typed_expr env obj /\
  expr_type obj = StructT sid ==>
  post_value_type cenv obj = StructT sid
Proof
  strip_tac >> Cases_on `?ty fid args drv. obj = Call ty (IntCall fid) args drv`
  >- (gvs[] >> rename1 `IntCall fid` >> PairCases_on `fid` >>
      gvs[expr_sim_inv_mods_def, well_typed_expr_def, post_value_type_def,
          lowered_value_type_def, expr_type_def, is_word_type_def, is_bytestring_type_def] >>
      drule typed_memory_struct_widening >> metis_tac[]) >>
  qpat_assum `expr_type obj = StructT sid` (SUBST1_TAC o SYM) >>
  irule post_value_type_not_int_call >> metis_tac[]
QED

Theorem attribute_typed_selection_mods:
  expr_body_pre_mods mods cenv cx env (Attribute ann obj fld) es0 /\
  expr_body_pre_mods mods cenv cx env obj es0 /\
  eval_expr cx obj es0 = (INL raw,ee) /\
  read_result cx raw ee = (INL v,ee) /\
  expr_vv_res_ok (FST (eval_expr cx (Attribute ann obj fld) es0)) ==>
  ?sid fs ftv vals fv raw'.
    expr_type obj = StructT sid /\ post_value_type cenv obj = StructT sid /\
    evaluate_type (get_tenv cx) (StructT sid) = SOME (StructTV fs) /\
    evaluate_type (get_tenv cx) ann = SOME ftv /\
    fields_layout (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fs /\
    v = StructV vals /\ value_has_type (StructTV fs) v /\
    struct_has_type fs vals /\ ALOOKUP fs fld = SOME ftv /\
    ALOOKUP vals fld = SOME fv /\ val_wf ftv fv /\
    read_result cx raw ee = (INL (StructV vals),ee) /\
    read_result cx raw' ee = (INL fv,ee) /\
    select_result cx (StructT sid) raw (AttrSubscript fld) ee = (INL raw',ee) /\
    type_memory_bytes cenv (lowered_value_type cenv (Attribute ann obj fld)) =
      type_memory_size ftv
Proof
  strip_tac >>
  `bind (eval_expr cx obj) (read_result cx) es0 = (INL v,ee)` by simp[bind_def] >>
  drule_all_then strip_assume_tac (REWRITE_RULE [ETA_THM] expr_body_pre_eval_mods) >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  `well_typed_expr env (Attribute ann obj fld)` by
    (irule expr_body_pre_mods_well_typed >> goal_assum (drule_at Any)) >>
  `?sid. expr_type obj = StructT sid /\
         attribute_type (get_tenv cx) (StructT sid) fld = SOME ann` by
    (fs[Once well_typed_expr_def, attribute_type_ok_def] >>
     Cases_on `expr_type obj` >> gvs[attribute_type_def]) >>
  `expr_sim_inv_mods mods cenv cx env es0 /\ well_typed_expr env obj` by
    fs[expr_body_pre_mods_def] >>
  drule_all_then assume_tac attribute_struct_post_type_mods >>
  `?tv. evaluate_type (get_tenv cx) (StructT sid) = SOME tv /\ value_has_type tv v` by
    (first_x_assum (qspec_then `v` mp_tac) >> simp[value_runtime_typed_def]) >>
  drule_all_then strip_assume_tac attribute_fields_layout_mods >> gvs[] >>
  drule_all_then strip_assume_tac attribute_type_evaluates >>
  drule_then strip_assume_tac struct_value_shape >> gvs[] >>
  `~popped_at_field raw fld ee` by
    (irule popped_keys_indexed_not_at_field >> fs[expr_sim_inv_mods_def]) >>
  Cases_on `select_result cx (StructT sid) raw (AttrSubscript fld) ee` >>
  rename1 `_ = (res,es2)` >>
  `eval_expr cx (Attribute ann obj fld) es0 = (res,es2)` by
    simp[eval_expr_attribute, bind_def] >>
  `!m. res <> INR (Error (TypeError m))` by
    (qpat_assum `expr_vv_res_ok _` mp_tac >>
     simp[expr_vv_res_ok_def] >> rpt strip_tac >> gvs[expr_vv_res_ok_def]) >>
  drule_all_then strip_assume_tac select_attr_read >> gvs[] >>
  rename1 `ALOOKUP fs fld = SOME ftv` >>
  `val_wf ftv fv` by
    (drule_then assume_tac (cj 5 valueEncodingTypingTheory.value_has_type_val_wf) >>
     irule fields_val_wf_field >> qexistsl_tac [`fs`,`fld`,`vals`] >> simp[]) >>
  `type_memory_bytes cenv ann = type_memory_size ftv` by
    (irule typed_copy_memory_size >> qexists_tac `get_tenv cx` >>
     fs[expr_sim_inv_mods_def] >> metis_tac[]) >>
  simp[lowered_value_type_def, expr_type_def]
QED

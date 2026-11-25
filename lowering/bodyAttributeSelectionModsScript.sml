(* Connect the source selector to the read at the linked machine endpoint. *)
Theory bodyAttributeSelectionMods
Ancestors
  bodyAttributeTypedSelectionMods bodyAttributePreMods bodyFullAttributeMods
  bodyFullPostsMods exprBodyPreTypingProps exprBodyPreCallSafetyProps
  exprSimDefs vyperTypeEvalSoundness vyperTypeExprSoundness vyperTypeInvariants
  vyperInterpreter vyperState vyperExprNoControl

Theorem attribute_result_admissible[local]:
  expr_body_pre_mods mods cenv cx env (Attribute ann obj fld) es /\
  eval_expr cx (Attribute ann obj fld) es = (res,ee) ==>
  expr_vv_res_ok res
Proof
  strip_tac >>
  drule_then strip_assume_tac expr_body_pre_mods_runtime_typing >>
  drule_then assume_tac expr_body_pre_mods_call_evaluation_safe >>
  qpat_x_assum `runtime_consistent _ _ _`
    (strip_assume_tac o REWRITE_RULE [runtime_consistent_def]) >>
  drule_all_then strip_assume_tac (cj 1 (cj 5 eval_scc_type_sound_mutual)) >>
  qpat_x_assum `well_typed_expr _ _ ==> _` (drule_then strip_assume_tac) >>
  Cases_on `res`
  >- (rename1 `eval_expr _ _ _ = (INL raw,_)` >> Cases_on `raw` >>
      gvs[eval_result_typed_def, expr_vv_res_ok_def]) >>
  drule (cj 1 eval_expr_no_control) >>
  rename1 `INR exc` >> Cases_on `exc` >>
  gvs[no_control_exc_def, no_type_error_result_def, expr_vv_res_ok_def] >>
  rename1 `Error err` >> Cases_on `err` >> gvs[]
QED

Theorem attribute_typed_selection_mods:
  expr_body_pre_mods mods cenv cx env (Attribute ann obj fld) es0 /\
  eval_expr cx obj es0 = (INL btv,ee) /\
  vv_post_mods H ctx func cenv cx obj es sa sm s0 ee btv bvv t ==>
  ?sid fs ftv vals fv tv' w.
    expr_type obj = StructT sid /\
    post_value_type cenv obj = StructT sid /\
    evaluate_type (get_tenv cx) (StructT sid) = SOME (StructTV fs) /\
    evaluate_type (get_tenv cx) ann = SOME ftv /\
    fields_layout (get_struct_fields cenv.ce_struct_fields
      (nsid_to_string sid)) fs /\
    struct_has_type fs vals /\
    ALOOKUP fs fld = SOME ftv /\
    ALOOKUP vals fld = SOME fv /\
    val_wf ftv fv /\
    read_result cx btv ee = (INL (StructV vals),ee) /\
    read_result cx tv' ee = (INL fv,ee) /\
    select_result cx (StructT sid) btv (AttrSubscript fld) ee =
      (INL tv',ee) /\
    eval_operand (vv_operand bvv) t = SOME w
Proof
  strip_tac >>
  drule_then assume_tac attribute_pre_child_mods >>
  qhdtm_assum `vv_post_mods`
    (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
  drule_then strip_assume_tac attribute_vv_holds_read_operand_mods >>
  `expr_vv_res_ok (FST (eval_expr cx (Attribute ann obj fld) es0))` by
    (Cases_on `eval_expr cx (Attribute ann obj fld) es0` >>
     simp[] >> drule_all_then ACCEPT_TAC attribute_result_admissible) >>
  drule_all_then strip_assume_tac bodyAttributeTypedSelectionModsTheory.attribute_typed_selection_mods >>
  qexistsl [`sid`,`fs`,`ftv`,`vals`,`fv`,`raw'`,`w`] >> simp[]
QED

Theory bodyPtrAttributeSource
Ancestors
  exprSimAttribute exprSimAttributeProps exprSimAttributeFields exprSimSource
  exprSimFieldLayout exprSimDefs exprSimHyps exprSimHypsDefs loweringPosts context
  exprLowering compileEnv vyperTypeExprSoundness vyperPlaceResultTyping
  exprSimProps valueEncoding valueEncodingTyping vyperValue vyperAST vyperState list finite_map

(* This value/place elimination boundary is independent of field selection. *)
Theorem attribute_vv_holds_read_operand:
  vv_holds cenv cx ty tv vv ee t ==>
  ?v w. read_result cx tv ee = (INL v,ee) /\
        eval_operand (vv_operand vv) t = SOME w
Proof
  Cases_on `vv`
  >- (simp[vv_holds_def, vv_operand_def, expr_val_rel_def] >> metis_tac[]) >>
  simp[vv_holds_def, vv_operand_def] >>
  rpt strip_tac >> rename1 `p.ptr_location` >> Cases_on `p.ptr_location` >>
  gvs[storage_holds_def, immutable_holds_def] >> metis_tac[]
QED

Theorem attribute_typed_selection:
  expr_body_pre cenv cx env (Attribute ann obj fld) es0 /\
  eval_expr cx obj es0 = (INL btv,ee) /\
  vv_post ctx func cenv cx obj es sa sm s0 ee btv bvv t ==>
  ?sid fs ftv vals fv tv' w.
    expr_type obj = StructT sid /\
    evaluate_type (get_tenv cx) (StructT sid) = SOME (StructTV fs) /\
    evaluate_type (get_tenv cx) ann = SOME ftv /\
    fields_layout (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fs /\
    struct_has_type fs vals /\ ALOOKUP fs fld = SOME ftv /\
    ALOOKUP vals fld = SOME fv /\ val_wf ftv fv /\
    read_result cx btv ee = (INL (StructV vals),ee) /\
    read_result cx tv' ee = (INL fv,ee) /\
    select_result cx (StructT sid) btv (AttrSubscript fld) ee = (INL tv',ee) /\
    eval_operand (vv_operand bvv) t = SOME w
Proof
  strip_tac >> drule attr_pre_base >> strip_tac >>
  drule_all expr_body_pre_runtime_typed >> strip_tac >> gvs[] >>
  `expr_sim_inv cenv cx env es0` by fs[expr_body_pre_def] >>
  drule_all struct_fields_layout >> strip_tac >> gvs[] >>
  drule_all attribute_type_evaluates >> strip_tac >>
  `vv_holds cenv cx (StructT sid) btv bvv ee t` by fs[vv_post_def] >>
  drule attribute_vv_holds_read_operand >> strip_tac >>
  `value_has_type (StructTV fs) v` by metis_tac[] >>
  drule struct_value_shape >> strip_tac >> gvs[] >>
  `~popped_at_field btv fld ee` by
    (irule popped_keys_indexed_not_at_field >>
     drule_all expr_body_pre_eval_result >> simp[expr_sim_inv_def]) >>
  Cases_on `select_result cx (StructT sid) btv (AttrSubscript fld) ee` >>
  rename1 `_ = (sres,es2)` >>
  `!m. sres <> INR (Error (TypeError m))` by
    (`eval_expr cx (Attribute ann obj fld) es0 = (sres,es2)` by
       simp[eval_expr_attribute, bind_def] >>
     drule_all (expr_body_pre_vv_res_ok |> SPEC_ALL |>
       Q.INST [`e` |-> `Attribute ann obj fld`]) >>
     simp[expr_vv_res_ok_def] >> rpt strip_tac >> gvs[]) >>
  drule_all select_attr_read >> strip_tac >> gvs[] >>
  `val_wf tv fv` by
    (irule fields_val_wf_field >> goal_assum (drule_at Any) >> simp[] >>
     metis_tac[cj 5 value_has_type_val_wf]) >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem attribute_field_memory_size:
  expr_body_pre cenv cx env (Attribute ann obj fld) es0 /\
  evaluate_type (get_tenv cx) ann = SOME ftv ==>
  type_memory_bytes cenv (lowered_value_type cenv (Attribute ann obj fld)) =
    type_memory_size ftv
Proof
  strip_tac >> simp[lowered_value_type_def, expr_type_def] >>
  irule expr_sim_inv_memory_size >> goal_assum (drule_at Any) >>
  fs[expr_body_pre_def] >> metis_tac[]
QED

Theorem attribute_memory_field_address:
  vv_post ctx func cenv cx obj es sa sm s0 ee btv bvv t /\
  expr_type obj = StructT sid /\ vv_loc bvv = LocMemory /\
  read_result cx btv ee = (INL (StructV vals),ee) /\
  evaluate_type (get_tenv cx) (StructT sid) = SOME (StructTV fs) /\
  eval_operand (vv_operand bvv) t = SOME w /\
  fields_layout fields fs /\ ALOOKUP fs fld = SOME ftv ==>
  w2n (w + n2w (struct_field_offset fields fld)) =
    w2n w + struct_field_offset fields fld
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx ee t` by fs[vv_post_def] >>
  `vv_at cenv cx (StructT sid) sa sm ee btv bvv t` by fs[vv_post_def] >>
  qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  drule stmt_state_rel_region_lt >> strip_tac >>
  drule_all struct_field_offset_le >> strip_tac >>
  Cases_on `bvv` >>
  gvs[vv_at_def, vv_loc_def, vv_location_def, vv_operand_def,
      expr_val_at_def, is_word_type_def, val_footprint_def, type_memory_size_def] >>
  first_x_assum drule >> strip_tac >>
  irule field_ptr_w2n >>
  qexistsl_tac [`type_memory_size ftv`, `type_memory_size_fields fs`] >>
  simp[] >> decide_tac
QED

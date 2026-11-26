(* Ordinary linked posts for a field in an immutable's code section. *)
Theory bodyAttributeCodePostMods
Ancestors
  bodyFullPostsMods exprSimAttributeProps exprSimFieldLayout exprSimMemDefs
  vyperAssignPreservesType vyperPlaceResultTyping ptrDiscipline
  loweringPosts valueEncoding valueEncodingDefs exprSimProps exprSimDefs
  vyperInterpreter venomState vyperAST supportedExprTraverse
  context compileEnv vyperState bodyPtrDefs

Theorem code_field_holds[local]:
  immutable_holds_mods cenv cx (StructT sid) raw w ee t /\
  evaluate_type (get_tenv cx) (StructT sid) = SOME (StructTV fs) /\
  evaluate_type (get_tenv cx) ann = SOME ftv /\
  fields_layout fields fs /\ struct_has_type fs vals /\
  ALOOKUP fs fld = SOME ftv /\ ALOOKUP vals fld = SOME fv /\
  read_result cx raw ee = (INL (StructV vals),ee) /\
  read_result cx raw' ee = (INL fv,ee) ==>
  immutable_holds_mods cenv cx ann raw'
    (w + n2w (struct_field_offset fields fld)) ee t
Proof
  strip_tac >>
  `value_has_type ftv fv` by
    (drule_all struct_field_has_type >> simp[]) >>
  `sub_layout (StructTV fs) (StructV vals) (struct_field_offset fields fld)
       ftv fv` by
    (simp[sub_layout_def, type_memory_size_def, val_in_memory_def] >>
     conj_tac >- (drule_all struct_field_offset_le >> simp[]) >>
     rpt strip_tac >> drule_all fields_in_memory_field >> simp[]) >>
  fs[immutable_holds_mods_def] >> qexistsl_tac [`src`,`tops`] >> simp[] >>
  irule immutable_holds_sub >> goal_assum (drule_at Any) >>
  qexistsl_tac [`StructT sid`,`raw`] >> simp[]
QED

Theorem code_field_at[local]:
  vv_loc bvv = LocCode /\ vv_at cenv cx (StructT sid) sa sb ee raw bvv t /\
  select_result cx (StructT sid) raw (AttrSubscript fld) ee = (INL raw',ee) ==>
  vv_at cenv cx ann sa sb ee raw' (LocatedValue ann (mk_ptr dst LocCode)) t
Proof
  strip_tac >>
  drule_then assume_tac select_result_memory_place >>
  simp[vv_at_def, mk_ptr_def] >> rpt strip_tac >>
  `?p. raw = PlaceR (MemoryPlace id p)` by metis_tac[] >>
  Cases_on `bvv` >> gvs[vv_at_def, vv_loc_def, vv_location_def, is_word_type_def]
QED

Theorem code_field_not_value[local]:
  select_result cx (StructT sid) raw (AttrSubscript fld) ee = (INL raw',ee) /\
  (!v. raw = Value v ==> vv_loc bvv = LocMemory) /\ vv_loc bvv = LocCode ==>
  !v. raw' <> Value v
Proof
  Cases_on `raw` >> simp[select_result_def, raise_def] >> rpt strip_tac >>
  gvs[] >> drule extend_place_result_shape >> simp[]
QED

Theorem code_field_ptr[local]:
  vv_loc bvv = LocCode /\ ptr_vv_ok cx (StructT sid) raw bvv ee G tn s /\
  dst = Var out /\ FLOOKUP G' out = op_prov G (vv_operand bvv) /\
  op_taint tn' dst = {} ==>
  ptr_vv_ok cx ann raw' (LocatedValue ann (mk_ptr dst LocCode)) ee G' tn' t
Proof
  Cases_on `bvv` >>
  simp[vv_loc_def, vv_location_def, vv_operand_def, ptr_vv_ok_def, mk_ptr_def, op_prov_def] >>
  strip_tac >> gvs[]
QED

Theorem attribute_code_field_post_mods:
  vv_loc bvv = LocCode /\
  vv_post_mods H ctx func cenv cx obj es sa sb s0 ee raw bvv t /\
  expr_type obj = StructT sid /\ post_value_type cenv obj = StructT sid /\
  evaluate_type (get_tenv cx) (StructT sid) = SOME (StructTV fs) /\
  evaluate_type (get_tenv cx) ann = SOME ftv /\
  fields_layout (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fs /\
  struct_has_type fs vals /\ ALOOKUP fs fld = SOME ftv /\ ALOOKUP vals fld = SOME fv /\
  read_result cx raw ee = (INL (StructV vals),ee) /\
  read_result cx raw' ee = (INL fv,ee) /\
  select_result cx (StructT sid) raw (AttrSubscript fld) ee = (INL raw',ee) /\
  vv_place_ptr_mods cenv cx ee t raw' (LocatedValue ann (mk_ptr dst (vv_loc bvv))) /\
  eval_operand (vv_operand bvv) t = SOME w /\
  eval_operand dst t = SOME (w + n2w (attr_offset cenv (StructT sid) (vv_loc bvv) fld)) /\
  ptr_vv_ok cx (StructT sid) raw bvv ee G tn s /\
  (!v. raw = Value v ==> vv_loc bvv = LocMemory) /\
  dst = Var out /\ FLOOKUP G' out = op_prov G (vv_operand bvv) /\
  op_taint tn' dst = {} ==>
  let vv = LocatedValue ann (mk_ptr dst (vv_loc bvv)) in
    vv_post_mods H ctx func cenv cx (Attribute ann obj fld) es sa sb s0 ee raw' vv t /\
    vv_store_bound cx (post_value_type cenv (Attribute ann obj fld))
      (lowered_value_type cenv (Attribute ann obj fld)) ee raw' vv t /\
    ptr_vv_ok cx (post_value_type cenv (Attribute ann obj fld)) raw' vv ee G' tn' t /\
    (!v. raw' = Value v /\ ~is_word_type (post_value_type cenv (Attribute ann obj fld)) /\
         ~is_bytestring_type (post_value_type cenv (Attribute ann obj fld)) ==>
       vv_own cenv cx (post_value_type cenv (Attribute ann obj fld)) sa sb ee raw' vv t /\
       (!t' p. vv = LocatedValue t' p ==> p.ptr_location = LocMemory)) /\
    (!t' op. vv = StackValue t' op /\ ~is_word_type (post_value_type cenv (Attribute ann obj fld)) ==>
             ptr_buf_ok cenv (Attribute ann obj fld) op G' t) /\
    (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
            ptr_buf_ok cenv (Attribute ann obj fld) p.ptr_operand G' t)
Proof
  strip_tac >> drule_all_then assume_tac code_field_not_value >>
  `ptr_vv_ok cx ann raw' (LocatedValue ann (mk_ptr dst LocCode)) ee G' tn' t` by
    (drule_all code_field_ptr >> simp[]) >>
  qpat_x_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
  qpat_assum `post_value_type cenv obj = StructT sid`
    (fn th => rule_assum_tac (REWRITE_RULE [th])) >>
  `vv_at cenv cx ann sa sb ee raw' (LocatedValue ann (mk_ptr dst LocCode)) t` by
    (drule_all code_field_at >> simp[]) >>
  `immutable_holds_mods cenv cx (StructT sid) raw w ee t` by
    (qpat_x_assum `vv_holds_mods _ _ _ _ _ _ _` mp_tac >>
     Cases_on `bvv` >> gvs[vv_holds_mods_def, vv_loc_def, vv_location_def, vv_operand_def]) >>
  drule_all_then assume_tac code_field_holds >>
  `eval_operand dst t = SOME (w + n2w (struct_field_offset
      (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld))` by
    fs[attr_offset_def] >>
  gvs[LET_THM, vv_post_mods_def, expr_type_def, vv_holds_mods_def,
      vv_store_bound_def, mk_ptr_def, expr_has_effect_def] >>
  first_assum ACCEPT_TAC
QED

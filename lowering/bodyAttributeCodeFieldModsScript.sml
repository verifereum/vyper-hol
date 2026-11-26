(* Restrict the constructor's robust memory guarantee at an Attribute ADD. *)
Theory bodyAttributeCodeFieldMods
Ancestors
  bodyAttributeSelectionMods bodyFullPostsMods bodyPtrAttributeFields
  exprSimAttributeProps exprSimFieldLayout exprSimDefs loweringPosts
  compileEnv exprLowering context valueEncoding valueEncodingDefs venomState words list

Theorem attribute_code_field_endpoint_mods:
  expr_body_pre_mods mods cenv cx env (Attribute ann obj fld) es0 /\
  eval_expr cx obj es0 = (INL btv,ee) /\
  vv_post_mods H ctx func cenv cx obj es sa sm s0 ee btv bvv s /\
  select_result cx (expr_type obj) btv (AttrSubscript fld) ee = (INL tv',ee) /\
  eval_operand (vv_operand bvv) s = SOME w /\
  eval_operand dst t = SOME (w + n2w (attr_offset cenv (expr_type obj)
    (vv_loc bvv) fld)) /\
  t.vs_memory = s.vs_memory /\
  tn'.t_mem = tn.t_mem /\
  (cenv.ce_is_ctor /\
   vv_location bvv = SOME LocCode ==>
   ?v. read_result cx btv ee = (INL v,ee) /\
     !rt a. evaluate_type (get_tenv cx) (post_value_type cenv obj) = SOME rt /\
       eval_operand (vv_operand bvv) s = SOME a ==>
       w2n a + type_memory_size rt <= lo /\
       (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory rt v (w2n a) mem)) ==>
  (cenv.ce_is_ctor /\
   vv_location (LocatedValue ann (mk_ptr dst (vv_loc bvv))) = SOME LocCode ==>
   ?v. read_result cx tv' ee = (INL v,ee) /\
     !rt a. evaluate_type (get_tenv cx)
       (post_value_type cenv (Attribute ann obj fld)) = SOME rt /\
       eval_operand (vv_operand (LocatedValue ann (mk_ptr dst (vv_loc bvv)))) t = SOME a ==>
       w2n a + type_memory_size rt <= lo /\
       (!mem. mem_agree_outside tn'.t_mem t.vs_memory mem ==>
         val_in_memory rt v (w2n a) mem))
Proof
  strip_tac >>
  drule_all_then strip_assume_tac attribute_typed_selection_mods >>
  gvs[] >>
  simp[vv_location_def, mk_ptr_def] >> strip_tac >>
  `vv_location bvv = SOME LocCode` by
    (Cases_on `bvv` >> gvs[vv_loc_def, vv_location_def]) >>
  `immutable_holds_mods cenv cx (StructT sid) btv w ee s` by
    (Cases_on `bvv` >>
     gvs[vv_post_mods_def, vv_holds_mods_def, vv_loc_def, vv_location_def,
         vv_operand_def]) >>
  qhdtm_x_assum `immutable_holds_mods`
    (strip_assume_tac o REWRITE_RULE [immutable_holds_mods_def]) >>
  `w2n w + type_memory_size (StructTV fs) < dimword (:256)` by
    (qhdtm_x_assum `immutable_holds`
       (strip_assume_tac o REWRITE_RULE [immutable_holds_def]) >>
     gvs[sub_layout_def] >>
     `off + k < dimword (:256)` by decide_tac >>
     simp[w2n_n2w, arithmeticTheory.LESS_MOD] >> decide_tac) >>
  qabbrev_tac `fields = get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)` >>
  `struct_field_offset fields fld + type_memory_size ftv <=
    type_memory_size (StructTV fs)` by
    (drule_all struct_field_offset_le >> simp[type_memory_size_def]) >>
  `w2n (w + n2w (struct_field_offset fields fld)) =
    w2n w + struct_field_offset fields fld` by
    (irule field_ptr_w2n >> goal_assum (drule_at Any) >> simp[]) >>
  qpat_x_assum `_ /\ vv_location bvv = SOME LocCode ==> _` mp_tac >>
  simp[] >> strip_tac >>
  fs[attr_offset_def, Abbr `fields`, vyperASTTheory.expr_type_def, vv_operand_def] >>
  rpt strip_tac >> irule struct_field_robust_memory >>
  goal_assum (drule_at Any) >> qexistsl_tac [`fs`, `vals`] >> simp[]
QED

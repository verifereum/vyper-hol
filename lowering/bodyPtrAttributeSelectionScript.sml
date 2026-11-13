Theory bodyPtrAttributeSelection
Ancestors
  bodyPtrAttributeSource bodyPtrAttributeStorage bodyPtrAttributeFields bodyPtrAttributeCase
  exprSimAttributeFields exprSimFieldLayout exprSimDefs exprSimAttributeProps
  exprSimAttribute exprSimSource exprSimProps vyperPlaceResultTyping
  compileEnv loweringPosts exprLowering context venomState bodyPtrDefs list

(* Discharge storage address side conditions at the original endpoint, before
   changing the destination variable. Code locations need no slot bound. *)
Theorem attribute_nonmemory_endpoint_ptr:
  vv_post H ctx func cenv cx obj es sa sm s0 ee btv bvv s /\
  post_value_type cenv obj = StructT sid /\ vv_loc bvv <> LocMemory /\
  ptr_vv_ok cx (StructT sid) btv bvv ee G tn s /\
  evaluate_type (get_tenv cx) (StructT sid) = SOME (StructTV fs) /\
  evaluate_type (get_tenv cx) ann = SOME ftv /\
  fields_layout (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fs /\
  ALOOKUP fs fld = SOME ftv /\ eval_operand (vv_operand bvv) s = SOME w /\
  eval_operand dst t = SOME (w + n2w (attr_offset cenv (StructT sid) (vv_loc bvv) fld)) /\
  t.vs_accounts = s.vs_accounts /\ t.vs_call_ctx = s.vs_call_ctx /\
  t.vs_transient = s.vs_transient /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
  op_taint tn' dst = {} /\ (vv_loc bvv = LocCode ==> op_prov HG dst = NONE) ==>
  ptr_vv_ok cx ann tv' (LocatedValue ann (mk_ptr dst (vv_loc bvv))) ee' HG tn' t
Proof
  strip_tac >> drule struct_field_slot_exists >> strip_tac >>
  drule_all struct_field_offset_slots_eq >> strip_tac >>
  reverse (Cases_on `vv_loc bvv = LocStorage \/ vv_loc bvv = LocTransient`)
  >- (irule ptr_vv_ok_nonmemory >> Cases_on `vv_loc bvv` >> gvs[mk_ptr_def]) >>
  `storage_holds cx (vv_loc bvv = LocTransient) (StructT sid) btv w ee s` by
    (Cases_on `bvv` >>
     gvs[vv_post_def, vv_holds_def, vv_loc_def, vv_location_def, vv_operand_def] >>
     Cases_on `p.ptr_location` >> gvs[] >> metis_tac[]) >>
  `attr_offset cenv (StructT sid) (vv_loc bvv) fld = off` by
    (Cases_on `vv_loc bvv` >> gvs[attr_offset_def]) >>
  `((vv_loc bvv = LocStorage \/ vv_loc bvv = LocTransient) /\
     0 < type_slot_size ftv ==> w2n (w + n2w off) = w2n w + off)` by
    (rpt strip_tac >> drule_all attribute_storage_field_address >> simp[]) >>
  metis_tac[attribute_nonmemory_field_ptr]
QED

(* Source selection and pointer restriction, independent of counted execution. *)
Theorem attribute_selected_ptr:
  expr_body_pre cenv cx env (Attribute ann obj fld) es0 /\
  eval_expr cx obj es0 = (INL btv,ee) /\
  vv_post H ctx func cenv cx obj es sa sm s0 ee btv bvv s /\
  ptr_vv_ok cx (expr_type obj) btv bvv ee G tn s /\
  eval_operand dst t = SOME (w + n2w (attr_offset cenv (expr_type obj) (vv_loc bvv) fld)) /\
  eval_operand (vv_operand bvv) s = SOME w /\
  t.vs_memory = s.vs_memory /\ t.vs_accounts = s.vs_accounts /\
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_transient = s.vs_transient /\
  tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
  op_taint tn' dst = {} /\ (vv_loc bvv = LocCode ==> op_prov HG dst = NONE) /\
  (!x b sz. vv_operand bvv = Var x /\ FLOOKUP G x = SOME (b,sz) ==>
     ?y. dst = Var y /\ FLOOKUP HG y = SOME (b,sz)) ==>
  ?tv'. select_result cx (expr_type obj) btv (AttrSubscript fld) ee = (INL tv',ee) /\
    ptr_vv_ok cx ann tv' (LocatedValue ann (mk_ptr dst (vv_loc bvv))) ee HG tn' t /\
    (vv_loc bvv = LocMemory ==> ptr_buf_ok cenv (Attribute ann obj fld) dst HG t)
Proof
  strip_tac >> drule_all attribute_typed_selection >> strip_tac >> gvs[] >>
  `post_value_type cenv obj = StructT sid` by
    (drule attr_pre_base >> strip_tac >> drule_all attr_post_value_type >> gvs[]) >>
  Cases_on `vv_loc bvv = LocMemory`
  >- (`w2n (w + n2w (struct_field_offset
        (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld)) =
        w2n w + struct_field_offset
        (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld` by
        (drule_all attribute_memory_field_address >> simp[]) >>
      `type_memory_bytes cenv (lowered_value_type cenv (Attribute ann obj fld)) =
        type_memory_size ftv` by
        (drule_all attribute_field_memory_size >> simp[]) >>
      gvs[attr_offset_def] >> drule_all attribute_memory_field_ptr >> simp[]) >>
  simp[] >> drule_all attribute_nonmemory_endpoint_ptr >> simp[]
QED

Theorem attribute_selected_vv_post:
  expr_body_pre cenv cx env (Attribute ann obj fld) es0 /\
  eval_expr cx obj es0 = (INL btv,ee) /\
  vv_post H ctx func cenv cx obj es sa sn s0 ee btv bvv t /\
  eval_operand (vv_operand bvv) t = SOME w /\
  eval_operand dst t = SOME (w + n2w (attr_offset cenv (expr_type obj) (vv_loc bvv) fld)) ==>
  ?tv'. select_result cx (expr_type obj) btv (AttrSubscript fld) ee = (INL tv',ee) /\
    vv_post H ctx func cenv cx (Attribute ann obj fld) es sa sn s0 ee tv'
      (LocatedValue ann (mk_ptr dst (vv_loc bvv))) t
Proof
  strip_tac >> drule_all attribute_typed_selection >> strip_tac >> gvs[] >>
  drule attr_pre_base >> strip_tac >>
  `post_value_type cenv obj = expr_type obj` by
    (drule_all attr_post_value_type >> simp[]) >>
  drule_all expr_body_pre_runtime_typed >> strip_tac >> gvs[] >>
  qpat_assum `select_result _ _ _ _ _ = _`
    (assume_tac o MATCH_MP exprSimPropsTheory.select_result_memory_place) >>
  irule attr_vv_post >> conj_tac >- gs[] >>
  goal_assum (drule_at Any) >> simp[] >>
  qexists_tac `btv` >> simp[] >> rpt strip_tac >> gvs[]
QED

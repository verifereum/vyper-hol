(* A saved code pointer still denotes its own module's immutable value. *)
Theory bodyExtSavedCodeEndpointMods
Ancestors
  bodyFullPostsMods exprSimMemDefs bodyPtrDefs ptrDiscipline
  loweringPosts vyperState venomState

Theorem ext_saved_code_endpoint_mods:
  p.ptr_location = LocCode /\
  (?raw. read_result cx raw mid = (INL v,mid) /\
    vv_holds_mods cenv cx ty raw (LocatedValue ty p) mid t /\
    ptr_vv_ok cx ty raw (LocatedValue ty p) mid G1 tn1 t) /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  ghost_kept_at lo cenv mid sm G1 tn1 t G2 tn2 /\
  (!x w. not_fresh_at sm x /\ lookup_var x t = SOME w ==> lookup_var x u = SOME w) /\
  u.vs_labels = t.vs_labels /\ ee.immutables = mid.immutables ==>
  (?raw. read_result cx raw ee = (INL v,ee) /\
    vv_holds_mods cenv cx ty raw (LocatedValue ty p) ee u /\
    vv_at cenv cx ty sa sb ee raw (LocatedValue ty p) u /\
    ptr_vv_ok cx ty raw (LocatedValue ty p) ee G2 tn2 u /\
    vv_store_bound cx ann ty ee raw (LocatedValue ty p) u) /\
  vv_storage_live H cx (LocatedValue ty p) ee u /\
  eval_operand p.ptr_operand u = eval_operand p.ptr_operand t
Proof
  strip_tac >>
  `?w. eval_operand p.ptr_operand t = SOME w /\
       immutable_holds_mods cenv cx ty raw w mid t` by
    gvs[vv_holds_mods_def] >>
  `eval_operand p.ptr_operand u = SOME w` by
    (Cases_on `p.ptr_operand` >> gvs[venomStateTheory.eval_operand_def]) >>
  `op_taint tn2 p.ptr_operand = {} /\ op_prov G2 p.ptr_operand = NONE` by
    (Cases_on `p.ptr_operand` >>
     gvs[ghost_kept_at_def, ptr_vv_ok_def, op_taint_def, op_prov_def] >>
     metis_tac[]) >>
  simp[] >> qexists_tac `Value v` >>
  simp[read_result_def, return_def, vv_holds_mods_def, vv_at_def,
       vv_store_bound_def, ptr_vv_ok_def] >>
  qpat_x_assum `immutable_holds_mods _ _ _ _ _ _ _` mp_tac >>
  (* The unfolded implication keeps the same module and layout witnesses. *)
  simp[immutable_holds_mods_def, immutable_holds_def, read_result_def, return_def]
QED

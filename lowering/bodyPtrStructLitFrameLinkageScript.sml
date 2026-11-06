(* Definition-level linkage diagnostic, not an inhabitance or simulation proof. *)
Theory bodyPtrStructLitFrameLinkage
Ancestors bodyPtrStructLitSupportedFrame bodyPtrPreds exprSimHypsDefs
  vyperTypeSystem vyperTypeInvariants vyperAST finite_map list

Theorem structlit_single_operand_boundary:
  (!ks. ks = MAP FST [(k,e)] ==>
    body_exprs_ptr_ok cx (MAP SND [(k,e)])) <=> body_expr_ptr_ok cx e
Proof
  simp[body_exprs_ptr_ok_def]
QED

Theorem structlit_candidate_typing:
  expr_body_pre cenv cx env structlit_supported_expr es ==>
  env.type_defs = get_tenv cx /\
  context_well_typed cx /\ functions_well_typed cx /\
  fn_sigs_consistent env.fn_sigs cx /\
  well_typed_expr env structlit_supported_call /\
  ?args. FLOOKUP env.type_defs (NONE,"S") = SOME (StructArgs args) /\
    MAP FST args = ["x"] /\ MAP SND args = [structlit_identity_type 1]
Proof
  simp[expr_body_pre_def, expr_sim_inv_def, env_consistent_def,
       env_context_consistent_def, structlit_supported_expr_def,
       well_typed_expr_def,
       expr_type_def, structlit_supported_call_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem structlit_candidate_call_linkage:
  expr_body_pre cenv cx env structlit_supported_expr es ==>
  ?sig ts fm nr params dflts body.
    FLOOKUP env.fn_sigs (NONE,"structlit_probe") = SOME sig /\
    get_module_code cx NONE = SOME ts /\
    lookup_callable_function cx.in_deploy "structlit_probe" ts =
      SOME (fm,nr,params,dflts,sig.ret_ty,body) /\
    type_widens_to (get_tenv cx) sig.ret_ty (structlit_identity_type 1) /\
    sig.param_types = MAP SND params /\ sig.num_defaults = LENGTH dflts /\
    LENGTH sig.param_types - sig.num_defaults = 0
Proof
  strip_tac >> drule structlit_candidate_typing >> strip_tac >>
  gvs[structlit_supported_call_def, well_typed_expr_def] >>
  qpat_x_assum `fn_sigs_consistent _ _` mp_tac >>
  simp[fn_sigs_consistent_def] >>
  disch_then drule >> strip_tac >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

(* This exact direction matters: an annotation of Bytes[1] cannot contain
   a declared Bytes[33] return under the actual call typing rule. *)
Theorem structlit_candidate_declared_mismatch:
  !tenv. ~type_widens_to tenv (structlit_identity_type 33)
    (structlit_identity_type 1)
Proof
  gen_tac >> EVAL_TAC
QED

Theorem structlit_candidate_declared_return_excluded:
  expr_body_pre cenv cx env structlit_supported_expr es /\
  get_module_code cx NONE = SOME ts /\
  lookup_callable_function cx.in_deploy "structlit_probe" ts =
    SOME (fm,nr,params,dflts,structlit_identity_type 33,stmts) ==> F
Proof
  strip_tac >> drule structlit_candidate_call_linkage >> strip_tac >>
  gvs[] >> metis_tac[structlit_candidate_declared_mismatch]
QED

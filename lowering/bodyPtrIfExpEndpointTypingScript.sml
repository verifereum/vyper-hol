Theory bodyPtrIfExpEndpointTyping
Ancestors
  exprSimHyps exprSimHypsDefs memoryLocalRhsProps vyperState
  vyperAST vyperInterpreter vyperTyping vyperTypeInvariants vyperTypeCallGraph
  vyperTypeExprSoundness vyperTypeEvalSoundness vyperTypeSystem exprSimDefs finite_map
  bodySim supportedDecls supportedProgram
Libs
  monadsyntax

Theorem ifexp_abi_encode_lowered_typed:
  !cx ce env ann ensure mid target args es raw ee v er.
    expr_body_pre ce cx env
      (TypeBuiltin ann (AbiEncode ensure mid) target args) es /\
    eval_expr cx (TypeBuiltin ann (AbiEncode ensure mid) target args) es = (INL raw,ee) /\
    read_result cx raw ee = (INL v,er) ==>
    ?sv. evaluate_type (get_tenv cx)
      (lowered_value_type ce (TypeBuiltin ann (AbiEncode ensure mid) target args)) = SOME sv /\
      value_has_type sv v
Proof
  rpt strip_tac >>
  `value_runtime_typed env
     (lowered_value_type ce (TypeBuiltin ann (AbiEncode ensure mid) target args)) v` by
    (irule memory_rhs_read_lowered_typed_unwidened >>
     conj_tac >- simp[] >>
     qexistsl [`cx`, `es`, `er`] >> simp[bind_def]) >>
  `expr_sim_inv ce cx env es` by gvs[expr_body_pre_def] >>
  drule_all memory_rhs_runtime_layout >> metis_tac[]
QED

(* The corresponding memoryLocalRhsProps helper is local, hence unavailable
   to pointer-case consumers. Export the frame boundary here. *)
Theorem ifexp_frame_signature_return_well_formed:
  !cenv cx env es id sig.
    expr_sim_inv cenv cx env es /\ FLOOKUP env.fn_sigs id = SOME sig ==>
    well_formed_type env.type_defs sig.ret_ty
Proof
  rpt strip_tac >>
  `env_consistent env cx es /\ functions_well_typed cx` by
    gvs[expr_sim_inv_def] >>
  `env.type_defs = get_tenv cx /\ fn_sigs_consistent env.fn_sigs cx` by
    (qpat_x_assum `env_consistent _ _ _` mp_tac >>
     simp[env_consistent_def, env_context_consistent_def]) >>
  Cases_on `id` >>
  qpat_assum `fn_sigs_consistent _ _` mp_tac >>
  pure_rewrite_tac[fn_sigs_consistent_def] >>
  disch_then drule >> strip_tac >>
  `IS_SOME (FLOOKUP env.fn_sigs (q,r))` by simp[] >>
  drule_all callable_body_typing_from_env_consistent >>
  simp[] >> strip_tac >> simp[well_formed_type_def]
QED

Theorem ifexp_internal_call_annotation_eval:
  !cx a b id args drv.
    eval_expr cx (Call a (IntCall id) args drv) =
    eval_expr cx (Call b (IntCall id) args drv)
Proof
  rpt gen_tac >> Cases_on `id` >> once_rewrite_tac[evaluate_def] >> REFL_TAC
QED

Theorem ifexp_internal_call_read_signature_typed:
  !cenv cx env es ann id args drv sig v es'.
    expr_body_pre cenv cx env (Call ann (IntCall id) args drv) es /\
    expr_sim_inv cenv cx env es /\ FLOOKUP env.fn_sigs id = SOME sig /\
    (do r <- eval_expr cx (Call ann (IntCall id) args drv);
        read_result cx r od) es = (INL v, es') ==>
    value_runtime_typed env sig.ret_ty v
Proof
  rpt strip_tac >>
  `well_formed_type env.type_defs sig.ret_ty` by
    (drule_all ifexp_frame_signature_return_well_formed >> simp[]) >>
  `well_typed_expr env (Call sig.ret_ty (IntCall id) args drv)` by
    (Cases_on `id` >>
     gvs[expr_body_pre_def, well_typed_expr_def, type_widens_to_def] >>
     metis_tac[]) >>
  `(do r <- eval_expr cx (Call sig.ret_ty (IntCall id) args drv);
       read_result cx r od) es = (INL v, es')` by
    metis_tac[ifexp_internal_call_annotation_eval] >>
  drule_at (Pat `bind _ _ _ = _`) eval_expr_read_type_sound >>
  disch_then (qspec_then `env` mp_tac) >>
  gvs[expr_body_pre_def, expr_sim_inv_def, int_calls_expr_def, expr_type_def]
QED

(* Actual-frame return-map probe reduced to:
   supported_program tops,
   ce.ce_func_return_type = build_func_return_type tops,
   get_module_code cx NONE = SOME tops,
   lookup_callable_function cx.in_deploy name tops =
     SOME (fm,nr,params,dflts,sig.ret_ty,body)
   ==> build_func_return_type tops (nsid_to_string (NONE,name)) = sig.ret_ty.
   The full body_inv, expr_body_pre and signature lookup remain available.
   This is not just an Internal declaration inversion: callable lookup may
   select Deploy, including the implicit default constructor. No compiler
   map/signature equality or final call endpoint is asserted here. *)

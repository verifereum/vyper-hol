Theory extRetStaticLoweredFramePtr
Ancestors extRetLoweredBytesFramePtr extRetTypedStaticConsumerPtr
  exprLowering vyperAST vyperTypeSystem compileEnv staticTypeFitsPtr

Theorem typed_static_lowered_value_type:
  well_typed_expr env e /\
  (!id sig. FLOOKUP env.fn_sigs id = SOME sig ==>
    cenv.ce_func_return_type (nsid_to_string id) = sig.ret_ty) /\
  ~is_abi_dynamic cenv.ce_struct_fields (expr_type e) ==>
  lowered_value_type cenv e = expr_type e
Proof
  strip_tac >> Cases_on `e` >>
  gvs[lowered_value_type_def, expr_type_def]
  >~ [`Literal t l`]
  >- (Cases_on `t` >> gvs[lowered_value_type_def, expr_type_def] >>
      rename1 `BaseT bt` >> Cases_on `bt` >>
      gvs[lowered_value_type_def, expr_type_def, is_abi_dynamic_def] >>
      Cases_on `l` >> gvs[lowered_value_type_def, expr_type_def] >>
      rename1 `BytesT bd` >> Cases_on `bd` >>
      gvs[lowered_value_type_def, expr_type_def, is_abi_dynamic_def]) >>
  all_tac
  >~ [`TypeBuiltin ty builtin tys args`]
  >- (Cases_on `builtin` >>
      gvs[lowered_value_type_def, expr_type_def, well_typed_expr_def,
          type_builtin_result_ok_def, is_abi_dynamic_def]) >>
  all_tac
  >~ [`Builtin ty builtin args`]
  >- (Cases_on `builtin` >>
      gvs[lowered_value_type_def, expr_type_def, well_typed_expr_def,
          well_typed_builtin_app_def, is_abi_dynamic_def]) >>
  rename1 `Call ty target args drv` >> Cases_on `target` >>
  gvs[lowered_value_type_def, expr_type_def] >>
  PairCases_on `p` >> gvs[well_typed_expr_def] >>
  first_x_assum drule >> disch_then SUBST1_TAC >>
  gvs[type_widens_to_def] >>
  metis_tac[cj 1 static_arg_type_fits]
QED

Theorem external_frame_typed_static_lowered_return:
  supported_program tops /\ source_deployment_rel tops am tx /\
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut, nr, rr, name, args, defaults, ret, fbody)) =
    (lbl, cenv0, pos, cds, payable, nr', key, ut, view, fbody', rt) /\
  compile_register_positional_args cenv0 pos off st = (cenv, sa) /\
  same_frame cenv next /\
  expr_sim_inv next
    (initial_evaluation_context am.sources am.layouts tx NONE) env es /\
  IS_SOME (type_stmt env ret (Return (SOME e))) /\
  ~is_abi_dynamic next.ce_struct_fields ret ==>
  lowered_value_type next e = ret
Proof
  strip_tac >>
  `expr_type e = ret` by
    (drule_all typed_abi_static_return_annotation >> simp[]) >>
  `well_typed_expr env e` by
    fs[typedCopyPtrTheory.type_stmt_return_some_iff] >>
  `lowered_value_type next e = expr_type e` suffices_by simp[] >>
  irule typed_static_lowered_value_type >> simp[] >>
  qexists_tac `env` >> simp[] >> rpt strip_tac >>
  irule extRetSignatureFramePtrTheory.external_frame_signature_return_map >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

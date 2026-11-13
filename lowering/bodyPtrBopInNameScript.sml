(* Universal local Name safety, using the zero-edge pointer boundary. *)
Theory bodyPtrBopInName
Ancestors
  bodyPtrBopInNameBoundary bodyPtrPreds bodyPtrDefs exprPtrUnwrap
  bodyPtrBopInOperandBoundary bodyPtrBopInCompareBoundary
  exprSimNameValue exprSimHypsDefs exprSimDefs exprSimProps
  fragGasPathPtr gasCount gasSummary stmtFragPtr loweringSlice
  exprLowering exprLoweringProps compileEnv context loweringPosts
  venomState venomInst vyperAST vyperInterpreter vyperState
  vyperTypeEnv vyperTypeSystem vyperTypeInvariants finite_map list

Theorem name_body_vv_sim_ptr:
  expr_body_pre cenv cx env (Name ann id) es ==>
  expr_vv_sim_ptr d ctx PG func cenv cx ty (Name ann id) es
Proof
  strip_tac >>
  `?entry. lookup_scopes id es.scopes = SOME entry /\
    evaluate_type (get_tenv cx) ann = SOME entry.type /\
    value_has_type entry.type entry.value` by
    (gvs[expr_body_pre_def, expr_sim_inv_def] >>
     drule_all well_typed_Name_lookup >> strip_tac >>
     gvs[env_consistent_def, env_context_consistent_def]) >>
  `?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)` by
    gvs[expr_body_pre_def, expr_sim_inv_def, well_typed_expr_def] >>
  `cenv.ce_var_type id = SOME ann` by
    gvs[expr_body_pre_def, expr_sim_inv_def, well_typed_expr_def] >>
  simp[expr_vv_sim_ptr_def] >> rpt strip_tac >>
  drule compile_name_value_ptr >>
  disch_then (qspecl_then [`ty`, `sa`, `ann`] assume_tac) >> gvs[] >>
  rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL (PlaceR (MemoryPlace id []))`, `es`, `G0`, `tn0`, `OK s0`] >>
  conj_tac
  >- simp[gas_explicit_def, Once evaluate_def, bind_def, get_scopes_def,
          return_def, type_check_def, assert_def, check_def, ignore_bind_def] >>
  conj_tac >- simp[gas_path_ptr_rules] >>
  disj1_tac >> simp[] >>
  drule_all local_name_body_ptr_boundary >> strip_tac >>
  `vv_post ctx func cenv cx (Name ann id) es sa sa s0
     (es with gas_obs := []) (PlaceR (MemoryPlace id []))
     (LocatedValue ann (mk_ptr (Var p) LocMemory)) s0` by
    (irule name_value_post >> simp[]) >>
  gvs[expr_type_def, ghost_inv_gas_obs, ghost_kept_refl, mk_ptr_def]
QED

Theorem body_name_ptr_ok:
  !cx ann id. body_expr_ptr_ok cx (Name ann id)
Proof
  rpt gen_tac >> simp[body_expr_ptr_ok_def] >> rpt strip_tac
  >- (irule expr_sim_ptr_of_vv >>
      conj_tac >- metis_tac[] >>
      irule name_body_vv_sim_ptr >> metis_tac[]) >>
  irule name_body_vv_sim_ptr >> metis_tac[]
QED

Theorem local_membership_operands_ptr_ok:
  !cx. body_exprs_ptr_ok cx
    [Name (BaseT (StringT 1)) "x";
     Builtin (ArrayT (BaseT (StringT 1)) (Fixed 1))
       (MakeArray (SOME (BaseT (StringT 1))) (Fixed 1))
       [Name (BaseT (StringT 1)) "y"]]
Proof
  gen_tac >> irule singleton_array_operands_ptr >> simp[body_name_ptr_ok]
QED

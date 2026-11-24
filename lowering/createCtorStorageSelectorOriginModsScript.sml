(* Storage origin for selector expressions in a linked constructor body. *)
Theory createCtorStorageSelectorOriginMods
Ancestors
  bodyFullAssign bodySimModsProps bodyInvSplit bodyInvCodeProps
  exprReasonOperand compileEnv exprLowering exprSimPopNestedBase targetPlaceSim bodyAugPlaceTarget
  vyperPlaceMutationSoundness vyperInterpreter vyperState vyperAST vyperValue
  finite_map alist list option context

Theorem ctor_storage_selector_expr_cases[local]:
  contract_inv mods exps ctx ce cx /\
  module_body_inv mods src tops ce cx /\
  compile_expr ce ty e sa = (LocatedValue t p,sb) /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) ==>
  (case e of TopLevelName _ _ => T | Pop _ _ => T |
     Attribute _ _ _ => T | Subscript _ _ _ => T | _ => F)
Proof
  disch_then (CONJUNCTS_THEN2 kall_tac
    (CONJUNCTS_THEN2 kall_tac
      (CONJUNCTS_THEN2 mp_tac assume_tac))) >>
  Cases_on `e` >> simp[] >>
  pure_once_rewrite_tac [CONJUNCT1 compile_expr_raw_def]
  >~ [`compile_expr_body _ _ _ _ _ (Literal _ _) _`] >-
    (simp[compile_expr_body_def, expr_type_def] >>
     disch_then (mp_tac o MATCH_MP reason_compile_literal) >>
     gvs[reason_result_shape_def])
  >~ [`compile_expr_body _ _ _ _ _ (IfExp _ _ _ _) _`] >-
    (disch_then (mp_tac o MATCH_MP reason_compile_ifexp) >>
     gvs[reason_result_shape_def])
  >~ [`compile_expr_body _ _ _ _ _ (StructLit _ _ _) _`] >-
    (disch_then (mp_tac o MATCH_MP reason_compile_structlit) >>
     gvs[reason_result_shape_def])
  >~ [`compile_expr_body _ _ _ _ _ (Call _ _ _ _) _`] >-
    (simp[compile_expr_body_def, expr_type_def] >>
     disch_then (mp_tac o MATCH_MP reason_compile_call) >>
     gvs[reason_result_shape_def])
  >~ [`compile_expr_body _ _ _ _ _ (Builtin _ _ _) _`] >- suspend "builtin"
  >~ [`compile_expr_body _ _ _ _ _ (TypeBuiltin _ _ _ _) _`] >- suspend "typebuiltin" >>
  simp[compile_expr_body_def, expr_type_def, compile_name_vv_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, mk_ptr_def, AllCaseEqs()] >>
  rename1 `FLOOKUP ce.ce_vars nm` >>
  (Cases_on `FLOOKUP ce.ce_vars nm`
   >- (gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
       rpt (pairarg_tac >> gvs[]))
   >> (rename1 `FLOOKUP _ _ = SOME binding` >> Cases_on `binding` >>
       gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def, mk_ptr_def] >>
       rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[]))
QED

Resume ctor_storage_selector_expr_cases[builtin]:
  disch_then (mp_tac o MATCH_MP reason_compile_expr_builtin_shape_classify) >>
  gvs[reason_result_shape_def] >>
  (simp[exprCallBoundsTheory.builtin_child_callback_def] >>
   pure_once_rewrite_tac [CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)] >>
   rename1 `compile_builtin_dispatch_body _ _ _ _ bi _ _` >>
   Cases_on `bi` >> strip_tac
   >~ [`Acc item`] >- suspend "acc"
   >~ [`AsWeiValue denom`] >- suspend "wei"
   >~ [`Len`] >- (drule reason_builtin_len >> gvs[reason_result_shape_def])
   >~ [`Bop bop`] >- (drule reason_builtin_bop >> gvs[reason_result_shape_def])
   >~ [`MakeArray et bd`] >- (drule reason_builtin_makearray >> gvs[reason_result_shape_def])
   >~ [`MethodId`] >- (drule reason_builtin_method_id >> gvs[reason_result_shape_def])
   >~ [`Keccak256`] >- (drule_at Any reason_builtin_hash >> simp[reason_result_shape_def])
   >~ [`Sha256`] >- (drule_at Any reason_builtin_hash >> simp[reason_result_shape_def])
   >~ [`CalldataSlice n`] >- (drule_at Any reason_builtin_fresh >> simp[reason_result_shape_def])
   >~ [`ECAdd`] >- (drule_at Any reason_builtin_fresh >> simp[reason_result_shape_def])
   >~ [`ECMul`] >- (drule_at Any reason_builtin_fresh >> simp[reason_result_shape_def])
   >~ [`Concat n`] >- (drule_at Any reason_builtin_fresh >> simp[reason_result_shape_def])
   >~ [`Slice n`] >- (drule_at Any reason_builtin_fresh >> simp[reason_result_shape_def])
   >~ [`Uint2Str n`] >- (drule_at Any reason_builtin_fresh >> simp[reason_result_shape_def])
   >~ [`NamedConst`] >-
     (gvs[compile_builtin_dispatch_body_def, LET_THM] >>
      pairarg_tac >> gvs[] >>
      gvs[AllCaseEqs(), as_stack_val_def, as_ptr_val_def, mk_ptr_def])
   >~ [`BoolChain _ _`] >-
     (gvs[compile_builtin_dispatch_body_def, LET_THM] >>
      rpt (pairarg_tac >> gvs[])) >>
   drule_at Any reason_builtin_scalar >> simp[reason_result_shape_def])
QED

Resume ctor_storage_selector_expr_cases[typebuiltin]:
  simp[compile_expr_body_def, expr_type_def] >>
  simp[exprCallBoundsTheory.type_child_callback_def] >>
  pure_once_rewrite_tac [CONJUNCT2 (CONJUNCT2 compile_expr_raw_def)] >>
  rename1 `compile_type_builtin_dispatch_body _ _ _ _ tb _ _ _` >>
  strip_tac >> Cases_on `tb` >> gvs[compile_type_builtin_dispatch_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[AllCaseEqs(), oneline as_stack_val_def, oneline as_ptr_val_def,
      mk_ptr_def, base_ptr_def] >>
  rpt strip_tac >> gvs[AllCaseEqs(), mk_ptr_def, base_ptr_def]
QED

Resume ctor_storage_selector_expr_cases[acc]:
  simp[markerTheory.resconj_def, markerTheory.suspendimp_def] >>
  rpt strip_tac >>
  gvs[compile_builtin_dispatch_body_def, oneline as_stack_val_def, AllCaseEqs()]
QED

Resume ctor_storage_selector_expr_cases[wei]:
  simp[markerTheory.resconj_def, markerTheory.suspendimp_def] >>
  rpt strip_tac >> gvs[compile_builtin_dispatch_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[AllCaseEqs(), oneline as_stack_val_def]
QED

Finalise ctor_storage_selector_expr_cases

Theorem ctor_storage_origin_from_base_mods:
  contract_inv mods exps ctx ce cx /\
  module_body_inv mods src tops ce cx /\
  (!e ty sa t p sb es pv es1.
    (case e of TopLevelName _ _ => T | Pop _ _ => T | _ => F) /\
    compile_expr ce ty e sa = (LocatedValue t p,sb) /\
    (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
    eval_expr cx e es = (INL pv,es1) ==>
    t = expr_type e /\ (!v. pv <> Value v)) ==>
  !e ty sa t p sb es pv es1.
    compile_expr ce ty e sa = (LocatedValue t p,sb) /\
    (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
    eval_expr cx e es = (INL pv,es1) ==>
    t = expr_type e /\ (!v. pv <> Value v)
Proof
  strip_tac >> measureInduct_on `expr_size e` >>
  rpt gen_tac >> disch_tac >>
  `case e of TopLevelName _ _ => T | Pop _ _ => T |
     Attribute _ _ _ => T | Subscript _ _ _ => T | _ => F` by
    metis_tac[ctor_storage_selector_expr_cases] >>
  Cases_on `case e of TopLevelName _ _ => T | Pop _ _ => T | _ => F`
  >- (qpat_x_assum `!e ty sa t p sb es pv es1. _` irule >>
      metis_tac[]) >>
  qpat_x_assum `!e ty sa t p sb es pv es1. _` kall_tac >>
  Cases_on `e` >> gnvs[] >>
  qpat_x_assum `_ /\\ _` (map_every assume_tac o CONJUNCTS)
  >- (qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
      simp[Once compile_expr_def] >> strip_tac >>
      `p.ptr_location <> LocMemory` by
        (Cases_on `p.ptr_location` >> gvs[]) >>
      drule_all body_assign_subscript_storage_origin >>
      simp[] >> strip_tac >>
      `~subscript_reads_base cx e' e0` by
        metis_tac[body_inv_copies_subscript_base_mods] >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, return_def, AllCaseEqs()] >>
      rpt strip_tac >>
      Cases_on `compile_expr ce ty e' sa` >> Cases_on `q` >>
      gvs[vv_location_def] >>
      qpat_x_assum `!y. expr_size y < _ ==> _`
        (qspec_then `e'` mp_tac) >>
      (impl_tac >- simp[]) >> disch_then drule >>
      disch_then assume_tac >>
      `!v. res <> Value v` by metis_tac[] >>
      metis_tac[body_assign_select_nonvalue])
  >- (qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
      simp[Once compile_expr_def] >> strip_tac >>
      `p.ptr_location <> LocMemory` by
        (Cases_on `p.ptr_location` >> gvs[]) >>
      drule_all body_assign_attribute_storage_origin >>
      simp[] >> strip_tac >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs()] >>
      rpt strip_tac >>
      Cases_on `compile_expr ce ty e' sa` >> Cases_on `q` >>
      gvs[vv_location_def] >>
      qpat_x_assum `!y. expr_size y < _ ==> _`
        (qspec_then `e'` mp_tac) >>
      (impl_tac >- simp[]) >> disch_then drule >>
      disch_then assume_tac >>
      `!v. res <> Value v` by metis_tac[] >>
      metis_tac[body_assign_select_nonvalue])
QED

(* Compiler/source origin boundaries for framed array selection. *)
Theory exprSimSubscriptArrayOrigin
Ancestors
  exprSimSubscriptArraySource exprLowering vyperState vyperInterpreter
  vyperAST vyperValue vyperMisc pair vyperTypeContract vyperTypeSystem
  compileEnv finite_map context exprSafeOperandBuiltins
  vyperStoragePlaceProvenance stmtSimForArrayFrame

Theorem extend_place_memory_origin:
  extend_place cx r sb s = (INL (PlaceR (MemoryPlace id path)),t) ==>
  ?path0. r = PlaceR (MemoryPlace id path0)
Proof
  Cases_on `r` >> simp[extend_place_def, raise_def]
  >- (Cases_on `p` >>
      simp[extend_place_def, extend_memory_place_def, bind_def,
           ignore_bind_def, return_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >>
      drule extend_storage_place_subregion >> simp[]) >>
  Cases_on `sb` >>
  simp[extend_place_def, bind_def, lift_option_type_def, return_def,
       raise_def, AllCaseEqs()] >>
  rpt strip_tac >>
  gvs[value_type_CASE_rator, return_def, raise_def, bind_def, AllCaseEqs()]
QED

Theorem select_result_memory_origin:
  select_result cx ty r sb s = (INL (PlaceR (MemoryPlace id path)),t) ==>
  ?path0. r = PlaceR (MemoryPlace id path0)
Proof
  Cases_on `r` >>
  simp[select_result_def, bind_def, lift_option_type_def, lift_sum_def,
       return_def, raise_def, AllCaseEqs()] >>
  strip_tac >> drule extend_place_memory_origin >> simp[]
QED

Theorem eval_base_place_memory_origin:
  !bt cx s id path t.
    eval_base_place cx bt s = (INL (PlaceR (MemoryPlace id path)),t) ==>
    ~toplevel_target bt
Proof
  completeInduct_on `base_assignment_target_size bt` >>
  Cases_on `bt` >> rpt strip_tac >>
  gvs[toplevel_target_def, Once evaluate_def, bind_def, AllCaseEqs()]
  >- (PairCases_on `p` >> gvs[Once evaluate_def] >>
      gvs[lookup_global_not_memory]) >>
  drule extend_place_memory_origin >> strip_tac >> gvs[] >>
  first_x_assum (qspec_then `base_assignment_target_size b` mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qspec_then `b` mp_tac) >> simp[] >> metis_tac[]
QED

Theorem compile_code_target_toplevel:
  !bt env vt cfn cenv st.
    type_place_target env bt = SOME vt /\
    (!id ty. FLOOKUP env.var_types id = SOME ty ==>
       ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)) /\
    FST (SND (FST (compile_get_target_ptr cfn cenv bt st))) = SOME LocCode ==>
    toplevel_target bt
Proof
  completeInduct_on `base_assignment_target_size bt` >>
  Cases_on `bt` >> rpt strip_tac >>
  gvs[toplevel_target_def]
  >- (gvs[Once well_typed_expr_def, AllCaseEqs()] >>
      first_x_assum drule >> strip_tac >>
      gvs[compile_get_target_ptr_def, comp_return_def]) >>
  gvs[Once well_typed_expr_def, AllCaseEqs()] >>
  rename1 `type_place_target env b = SOME root_vt` >>
  Cases_on `SND (SND (FST (compile_get_target_ptr cfn cenv b st)))` >>
  Cases_on `THE (SND (SND (FST (compile_get_target_ptr cfn cenv b st))))` >>
  gvs[Once compile_get_target_ptr_def, comp_bind_def, comp_return_def,
      LET_THM, UNCURRY] >>
  first_x_assum (qspec_then `base_assignment_target_size b` mp_tac) >>
  (impl_tac >- simp[]) >> disch_then (qspec_then `b` mp_tac) >>
  simp[] >> disch_then irule >> goal_assum (drule_at Any) >>
  qexistsl [`env`, `root_vt`] >> simp[]
QED

Theorem code_target_not_memory:
  type_place_target env bt = SOME vt /\
  (!id ty. FLOOKUP env.var_types id = SOME ty ==>
     ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)) /\
  FST (SND (FST (compile_get_target_ptr cfn cenv bt st))) = SOME LocCode /\
  eval_target_place cx bt s = (INL p,t) ==>
  !id path. p <> MemoryPlace id path
Proof
  strip_tac >> drule_all compile_code_target_toplevel >> strip_tac >>
  gvs[Once evaluate_def, bind_def, get_place_def, return_def, raise_def,
      AllCaseEqs()] >> rpt strip_tac >>
  Cases_on `pv` >> gvs[get_place_def, return_def, raise_def] >>
  drule eval_base_place_memory_origin >> simp[]
QED

Theorem type_place_expr_not_memory:
  !e env vt cx s r t.
    type_place_expr env e = SOME vt /\ eval_expr cx e s = (INL r,t) ==>
    !id path. r <> PlaceR (MemoryPlace id path)
Proof
  completeInduct_on `expr_size e` >> Cases_on `e` >> rpt strip_tac >>
  gvs[Once well_typed_expr_def, AllCaseEqs()]
  >- (PairCases_on `p` >> gvs[Once evaluate_def] >>
      gvs[lookup_global_not_memory]) >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs()] >>
  drule select_result_memory_origin >> strip_tac >> gvs[] >>
  rename1 `type_place_expr env obj = SOME obj_vt` >>
  first_x_assum (qspec_then `expr_size obj` mp_tac) >>
  (impl_tac >- simp[]) >> disch_then (qspec_then `obj` mp_tac) >>
  simp[] >> metis_tac[]
QED


Theorem compile_subscript_code_origin:
  vv_location (FST (compile_subscript f cenv rt ty obj idx sa)) = SOME LocCode ==>
  vv_location (FST (f cenv ty obj sa)) = SOME LocCode
Proof
  Cases_on `f cenv ty obj sa` >>
  Cases_on `vv_location q` >>
  Cases_on `place_type cenv obj` >>
  simp[compile_subscript_def, comp_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  simp[vv_location_def, mk_ptr_def] >>
  Cases_on `t` >> simp[comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> simp[vv_location_def, mk_ptr_def]
QED

Theorem compile_attribute_code_origin:
  vv_location (FST (compile_attribute f cenv rt ty obj fld sa)) = SOME LocCode ==>
  vv_location (FST (f cenv ty obj sa)) = SOME LocCode
Proof
  Cases_on `f cenv ty obj sa` >> Cases_on `vv_location q` >>
  simp[compile_attribute_def, comp_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> simp[vv_location_def, mk_ptr_def]
QED

Theorem compile_ifexp_not_code:
  vv_location (FST (compile_expr_body f g h cenv ty
    (IfExp ann cond th el) sa)) <> SOME LocCode
Proof
  simp[compile_expr_body_def, expr_type_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  simp[AllCaseEqs(), vv_location_def, mk_ptr_def] >>
  Cases_on `is_word_type ann` >> simp[vv_location_def, mk_ptr_def]
QED


Theorem compile_call_not_code:
  vv_location (FST (compile_call f cenv rt ty target args dflt sa)) <> SOME LocCode
Proof
  Cases_on `target`
  >~ [`RawCallTarget rcf`] >-
    (namedCases_on `args` ["", "addr tail"] >> simp[compile_call_def, LET_THM] >>
     rpt (pairarg_tac >> gvs[]) >> simp[vv_location_def] >>
     Cases_on `tail` >>
     simp[compile_call_def, LET_THM] >> rpt (pairarg_tac >> gvs[]) >>
     simp[vv_location_def] >>
     IF_CASES_TAC >> simp[vv_location_def, mk_ptr_def])
  >~ [`RawCallCalldataTarget rcf`] >-
    (Cases_on `args` >> simp[compile_call_def, LET_THM] >>
     rpt (pairarg_tac >> gvs[]) >> simp[vv_location_def] >>
     IF_CASES_TAC >> simp[vv_location_def, mk_ptr_def])
  >~ [`CreateTarget ck salted rof code`] >-
    (Cases_on `compile_create_call f cenv ck salted rof args sa` >>
     simp[compile_call_def, as_stack_val_def, vv_location_def]) >>
  simp[compile_call_def, LET_THM] >> rpt (pairarg_tac >> gvs[]) >>
  simp[vv_location_def, mk_ptr_def, base_ptr_def]
  >~ [`cenv.ce_func_info nm = _`] >-
    (Cases_on `returns_count > 0` >> Cases_on `return_buf` >>
     gvs[] >> rpt (pairarg_tac >> gvs[]) >> simp[vv_location_def])
  >~ [`ExtCall b b0 sig opts`] >-
    (PairCases_on `sig` >> Cases_on `args` >>
     simp[compile_call_def, LET_THM] >> rpt (pairarg_tac >> gvs[]) >>
     gvs[AllCaseEqs(), vv_location_def, mk_ptr_def] >>
     IF_CASES_TAC >> simp[vv_location_def]) >>
  namedCases_on `args` ["", "addr tail"] >> simp[vv_location_def] >>
  Cases_on `tail` >> simp[vv_location_def] >>
  gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >> simp[vv_location_def] >>
  IF_CASES_TAC >> simp[vv_location_def] >>
  rpt BasicProvers.TOP_CASE_TAC >> simp[vv_location_def]
QED

Theorem code_expr_not_memory:
  !e env cenv ty sa cx s r t.
    well_typed_expr env e /\
    (!id vt. FLOOKUP env.var_types id = SOME vt ==>
       ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)) /\
    vv_location (FST (compile_expr cenv ty e sa)) = SOME LocCode /\
    eval_expr cx e s = (INL r,t) ==>
    !id path. r <> PlaceR (MemoryPlace id path)
Proof
  completeInduct_on `expr_size e` >> Cases_on `e` >> rpt strip_tac
  >~ [`well_typed_expr env (Name ann nm)`] >-
    (qpat_x_assum `!m. m < _ ==> _` kall_tac >>
     gvs[Once well_typed_expr_def] >>
     qpat_x_assum `!id vt. _` drule >> strip_tac >>
     gvs[Once compile_expr_def, compile_expr_body_def, compile_name_vv_def,
         comp_return_def, vv_location_def, mk_ptr_def, expr_type_def])
  >~ [`eval_expr cx (TopLevelName ann nsid) _ = _`] >-
    (PairCases_on `nsid` >> gvs[Once evaluate_def] >>
     gvs[lookup_global_not_memory])
  >~ [`eval_expr cx (Literal ann lit) _ = _`] >-
    gvs[Once evaluate_def, return_def]
  >~ [`eval_expr cx (Subscript ann obj idx) _ = _`] >- suspend "subscript"
  >~ [`eval_expr cx (Attribute ann obj fld) _ = _`] >- suspend "attribute"
  >~ [`eval_expr cx (Pop ann bt) _ = _`] >- suspend "pop" >>
  qpat_x_assum `!m. m < _ ==> _` kall_tac
  >~ [`eval_expr cx (FlagMember ann nsid fld) _ = _`] >-
    gvs[Once compile_expr_def, compile_expr_body_def, expr_type_def,
        comp_return_def, vv_location_def]
  >~ [`eval_expr cx (IfExp ann cond th el) _ = _`] >-
    (qpat_x_assum `vv_location _ = _` mp_tac >>
     simp[Once (CONJUNCT1 compile_expr_raw_def), compile_ifexp_not_code])
  >~ [`eval_expr cx (Call ann dest args dflt) _ = _`] >-
    (qpat_x_assum `vv_location _ = _` mp_tac >>
     simp[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_def,
          compile_call_not_code]) >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def, return_def,
      raise_def, AllCaseEqs()] >>
  rename1 `StructLit ann nsid fields` >> PairCases_on `nsid` >>
  gvs[Once evaluate_def, bind_def, return_def, AllCaseEqs()]
QED

Resume code_expr_not_memory[subscript]:
  qpat_x_assum `vv_location _ = _` mp_tac >>
  pure_once_rewrite_tac [CONJUNCT1 compile_expr_raw_def] >>
  simp[compile_expr_body_def, expr_type_def] >>
  disch_then (mp_tac o MATCH_MP compile_subscript_code_origin) >>
  simp[exprCallBoundsTheory.expr_child_callback_def, expr_size_def] >>
  strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs()] >>
  drule select_result_memory_origin >> strip_tac >> gvs[] >>
  fs[Once well_typed_expr_def]
  >~ [`type_place_expr env obj = SOME vt`] >-
    (drule_all type_place_expr_not_memory >> simp[]) >>
  first_x_assum (qspec_then `expr_size obj` mp_tac) >>
  (impl_tac >- simp[]) >> disch_then (qspec_then `obj` mp_tac) >>
  disch_then (drule_all o SRULE []) >> simp[]
QED
Resume code_expr_not_memory[attribute]:
  qpat_x_assum `vv_location _ = _` mp_tac >>
  pure_once_rewrite_tac [CONJUNCT1 compile_expr_raw_def] >>
  simp[compile_expr_body_def, expr_type_def] >>
  disch_then (mp_tac o MATCH_MP compile_attribute_code_origin) >>
  simp[exprCallBoundsTheory.expr_child_callback_def, expr_size_def] >>
  strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs()] >>
  drule select_result_memory_origin >> strip_tac >> gvs[] >>
  fs[Once well_typed_expr_def] >>
  first_x_assum (qspec_then `expr_size obj` mp_tac) >>
  (impl_tac >- simp[]) >> disch_then (qspec_then `obj` mp_tac) >>
  disch_then (drule_all o SRULE []) >> simp[]
QED
Resume code_expr_not_memory[pop]:
  qpat_x_assum `!m. m < _ ==> _` kall_tac >>
  qpat_x_assum `vv_location _ = _` mp_tac >>
  pure_once_rewrite_tac [CONJUNCT1 compile_expr_raw_def] >>
  simp[compile_expr_body_def, expr_type_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  simp[vv_location_def, mk_ptr_def, AllCaseEqs()] >> strip_tac >>
  gvs[Once well_typed_expr_def, Once evaluate_def, bind_def, AllCaseEqs()] >>
  qmatch_asmsub_abbrev_tac `compile_get_target_ptr cb cenv bt sa` >>
  `FST (SND (FST (compile_get_target_ptr cb cenv bt sa))) = SOME LocCode`
    by simp[] >>
  drule_all code_target_not_memory >> strip_tac >>
  Cases_on `p` >> gvs[oneline pop_place_def, bind_def, ignore_bind_def,
    return_def, raise_def, AllCaseEqs()] >>
  rename1 `StoragePlace tr slot tv` >> Cases_on `tv` >>
  gvs[bind_def, ignore_bind_def, return_def, raise_def, AllCaseEqs()] >>
  rename1 `ArrayTV et bd` >> Cases_on `bd` >> gvs[bind_def, ignore_bind_def, return_def, raise_def,
    AllCaseEqs()]
QED
Finalise code_expr_not_memory

Theorem expr_body_pre_code_not_memory:
  expr_body_pre cenv cx env e es /\
  vv_location (FST (compile_expr cenv ty e sa)) = SOME LocCode /\
  eval_expr cx e s = (INL r,t) ==>
  !id path. r <> PlaceR (MemoryPlace id path)
Proof
  strip_tac >>
  irule code_expr_not_memory >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >>
  qexists_tac `env` >>
  gvs[exprSimHypsDefsTheory.expr_body_pre_def,
      exprSimHypsDefsTheory.expr_sim_inv_def]
QED


Theorem builtin_dispatch_not_code:
  compile_builtin_dispatch_body f cenv rt ty bi args sa = (vv,sb) ==>
  vv_location vv <> SOME LocCode
Proof
  Cases_on `bi` >>
  simp[compile_builtin_dispatch_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[AllCaseEqs(), oneline as_stack_val_def, oneline as_ptr_val_def,
      vv_location_def, mk_ptr_def, base_ptr_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rpt strip_tac >>
  FIRST [gvs[AllCaseEqs(), vv_location_def, mk_ptr_def, base_ptr_def]]
  >~ [`compile_literal_vv _ _ _ = _`] >-
    (Cases_on `rt` >> gvs[compile_literal_vv_def, comp_return_def, vv_location_def]
     >- (rename1 `BaseT bt` >> Cases_on `bt` >>
         gvs[compile_literal_vv_def, comp_return_def, vv_location_def] >>
         rename1 `BytesT bd` >> Cases_on `bd` >>
         gvs[compile_literal_vv_def, comp_return_def, comp_bind_def] >>
         rpt (pairarg_tac >> gvs[]) >>
         gvs[vv_location_def, base_ptr_def]) >>
     gvs[vv_location_def]) >>
  qpat_x_assum `_ = (vv,sb)` mp_tac >>
  rpt (pairarg_tac >> gvs[]) >>
  simp[AllCaseEqs(), vv_location_def] >>
  rpt strip_tac >> gvs[vv_location_def]
QED

Theorem type_builtin_dispatch_not_code:
  compile_type_builtin_dispatch_body f cenv vt ty tb rt args sa = (vv,sb) ==>
  vv_location vv <> SOME LocCode
Proof
  Cases_on `tb` >>
  simp[compile_type_builtin_dispatch_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[AllCaseEqs(), oneline as_stack_val_def, oneline as_ptr_val_def,
      vv_location_def, mk_ptr_def, base_ptr_def] >>
  rpt strip_tac >>
  gvs[AllCaseEqs(), vv_location_def, mk_ptr_def, base_ptr_def]
QED

Theorem builtin_array_not_label:
  well_typed_expr env (Builtin (ArrayT et bd) bi args) /\
  compile_builtin_dispatch_body f cenv rt ty bi args sa = (vv,sb) ==>
  !l. vv_operand vv <> Label l
Proof
  Cases_on `bi` >>
  simp[Once well_typed_expr_def, well_typed_builtin_app_def,
       is_numeric_type_def, is_bool_type_def, is_uint256_type_def,
       is_bytes32_type_def, is_flag_type_def]
  >~ [`well_typed_binop _ bop _ _`] >-
    (Cases_on `bop` >> simp[well_typed_binop_def, is_numeric_type_def,
       is_int_type_def, is_bool_type_def, is_flag_type_def])
  >~ [`env_item_type ei`] >- (Cases_on `ei` >> simp[env_item_type_def])
  >~ [`account_item_type ai`] >- (Cases_on `ai` >> simp[account_item_type_def])
  >~ [`MakeArray eo bnd`] >-
    (Cases_on `eo` >> simp[well_typed_builtin_app_def] >>
     rpt strip_tac >>
     gvs[compile_builtin_dispatch_body_def, LET_THM] >>
     rpt (pairarg_tac >> gvs[]) >>
     qmatch_asmsub_abbrev_tac `as_ptr_val _ _ res` >>
     Cases_on `res` >>
     gvs[as_ptr_val_def, vv_operand_def, mk_ptr_def, markerTheory.Abbrev_def] >>
     metis_tac[exprOperandVarTheory.compiler_make_array_result,
               exprSafeOperandTheory.alloc_buffer_not_label]) >>
  rpt strip_tac >>
  gvs[compile_builtin_dispatch_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  qmatch_asmsub_abbrev_tac `as_ptr_val _ _ res` >>
  Cases_on `res` >>
  gvs[as_ptr_val_def, vv_operand_def, mk_ptr_def, markerTheory.Abbrev_def] >>
  metis_tac[ec_arith_result_not_label]
QED

Theorem type_builtin_array_not_label:
  well_typed_expr env (TypeBuiltin (ArrayT et bd) tb target args) /\
  compile_type_builtin_dispatch_body f cenv vt ty tb target args sa = (vv,sb) ==>
  !l. vv_operand vv <> Label l
Proof
  Cases_on `tb` >>
  simp[Once well_typed_expr_def, type_builtin_result_ok_def,
       well_typed_type_builtin_args_def, is_numeric_type_def] >>
  rpt strip_tac >> gvs[is_numeric_type_def]
  >~ [`valid_conversion src (ArrayT _ _)`] >-
    (Cases_on `src` >> gvs[valid_conversion_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> gvs[valid_conversion_def] >>
     rename1 `BytesT bnd` >> Cases_on `bnd` >> gvs[valid_conversion_def]) >>
  rpt strip_tac >>
  gvs[compile_type_builtin_dispatch_body_def, is_word_type_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[])
  >~ [`compile_builtin_empty_complex _ _ _ = _`] >-
    (gvs[vv_operand_def, base_ptr_def] >>
     metis_tac[compile_empty_not_label]) >>
  qmatch_asmsub_abbrev_tac `as_ptr_val _ _ res` >>
  Cases_on `res` >>
  gvs[as_ptr_val_def, vv_operand_def, mk_ptr_def, markerTheory.Abbrev_def] >>
  metis_tac[lower_abi_decode_not_label]
QED

Theorem compile_array_pointer_not_label:
  compile_expr cenv ty e sa = (LocatedValue rt p,sb) /\
  expr_type e = ArrayT et bd /\ well_typed_expr env e /\
  (!id t. FLOOKUP env.var_types id = SOME t ==>
    ?q sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var q) sz)) /\
  (p.ptr_location = LocMemory \/ p.ptr_location = LocCode) ==>
  !l. p.ptr_operand <> Label l
Proof
  Cases_on `e` >> simp[expr_type_def] >> rpt strip_tac
  >>~- ([`well_typed_expr env (Subscript _ _ _)`],
    gvs[Once compile_expr_def, compile_expr_body_def, expr_type_def] >>
    drule compile_subscript_not_label >> simp[vv_operand_def])
  >>~- ([`well_typed_expr env (Attribute _ _ _)`],
    gvs[Once compile_expr_def, compile_expr_body_def, expr_type_def] >>
    drule compile_attribute_safe_operand >>
    simp[exprSafeOperandTheory.safe_operand_def, vv_operand_def])
  >>~- ([`well_typed_expr env (Builtin _ bi args)`],
    qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
    simp[Once compile_expr_def, compile_expr_body_def] >> strip_tac >>
    gvs[AllCaseEqs()]
     >>~- ([`compile_builtin_dispatch _ _ _ _ _ _ = _`],
       qpat_x_assum `compile_builtin_dispatch _ _ _ _ _ _ = _` mp_tac >>
       pure_once_rewrite_tac[cj 2 compile_expr_raw_def] >> strip_tac >>
       drule_all builtin_array_not_label >> simp[vv_operand_def]) >>
     gvs[Once well_typed_expr_def, well_typed_builtin_app_def]) >>
  all_tac
  >>~- ([`well_typed_expr env (Name _ _)`],
    gvs[Once well_typed_expr_def] >>
    first_x_assum drule >> strip_tac >>
    gvs[Once compile_expr_def, compile_expr_body_def, expr_type_def,
        compile_name_vv_def, comp_return_def, mk_ptr_def])
  >>~- ([`well_typed_expr env (TypeBuiltin _ _ _ _)`],
    gvs[] >> qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
    pure_once_rewrite_tac[cj 1 compile_expr_raw_def] >>
    simp[compile_expr_body_def, expr_type_def] >>
    pure_once_rewrite_tac[cj 3 compile_expr_raw_def] >> simp[] >>
    strip_tac >> drule_all type_builtin_array_not_label >> simp[vv_operand_def]) >>
  all_tac
  >>~- ([`well_typed_expr env (TopLevelName _ _)`],
    gvs[Once compile_expr_def, compile_expr_body_def, expr_type_def,
        AllCaseEqs(), mk_ptr_def] >>
    rpt (pairarg_tac >> gvs[]))
  >>~- ([`well_typed_expr env (IfExp _ _ _ _)`],
    gvs[Once compile_expr_def, compile_expr_body_def, expr_type_def] >>
    rpt (pairarg_tac >> gvs[]) >>
    gvs[is_word_type_def, mk_ptr_def])
  >>~- ([`well_typed_expr env (StructLit _ _ _)`],
    gvs[Once well_typed_expr_def])
  >>~- ([`well_typed_expr env (FlagMember _ _ _)`],
    gvs[Once compile_expr_def, compile_expr_body_def, expr_type_def])
  >>~- ([`well_typed_expr env (Literal _ lit)`],
    Cases_on `lit` >>
    gvs[Once well_typed_expr_def, well_typed_literal_def]) >>
  all_tac
  >>~- ([`well_typed_expr env (Pop _ _)`],
    gvs[Once compile_expr_def, compile_expr_body_def, expr_type_def] >>
    rpt (pairarg_tac >> gvs[]) >>
    gvs[mk_ptr_def] >>
    drule (cj 3 subscript_pop_not_label) >> simp[]) >>
  all_tac
  >>~- ([`well_typed_expr env (Call _ c _ _)`],
    Cases_on `c` >>
    gvs[Once well_typed_expr_def, raw_call_return_type_def] >>
    gvs[Once compile_expr_def, compile_expr_body_def, expr_type_def]
    >>~- ([`compile_call _ _ _ _ (IntCall _) _ _ _ = _`],
      drule compile_internal_call_not_label >> simp[vv_operand_def]) >>
    all_tac
    >>~- ([`ArrayT _ _ = if _ then _ else _`],
      gvs[AllCaseEqs()]) >>
    PairCases_on `p'` >>
    gvs[compile_call_def, AllCaseEqs()] >>
    rpt (pairarg_tac >> gvs[]) >>
    gvs[AllCaseEqs(), mk_ptr_def] >>
    drule compile_external_call_not_label >> simp[])
QED

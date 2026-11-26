(* Linked aggregate family rules at the evaluator's builtin boundaries. *)
Theory bodyBuiltinAggregateRoutesMods
Ancestors
  bodyFullPredsMods bodyAggregateArityMods bodyBuiltinArgBranchesMods
  bodyEmptyWordMods bodyEmptyBufferMods
  bodyConvertScalarMods bodyConvertDynamicMods bodyConvertBytesMods
  bodyMakeArrayRouteMods bodyMakeTupleRouteMods bodyMakeElementsMods
  bodyMakeBufferInitMods bodyMakeArrayCompletedMods
  bodyMembershipLiteralMods bodyMembershipOrdinaryMods bodyScalarStackVVMods
  bodyHashOperandMods bodyCalldataSliceRouteMods bodyConcatRouteMods
  bodyConcatCompactRouteMods
  bodySliceSelfRouteMods bodySliceOrdinaryRouteMods bodySliceExternalRouteMods
  bodyUint2StrRouteMods bodyECRecoverOperandsMods bodyECArithOperandsMods
  bodyAggregateReadMods
  exprBodyPreProps exprLoweringProps exprSimOperators
  vyperTypeSystem vyperContext vyperAST compileEnv vyperInterpreter

val _ = HolbuildProofRuntime.trace_all_ref := true (* trace 1 *)

Theorem empty_expr_full_ok_mods:
  !mods exps cx ann typ args.
    (!s x t. type_check (type_builtin_args_length_ok Empty (LENGTH args))
      "TypeBuiltin args" s = (INL x,t) ==> body_exprs_full_ok_mods mods exps cx args) ==>
    body_expr_full_ok_mods mods exps cx (TypeBuiltin ann Empty typ args)
Proof
  rpt gen_tac >> disch_tac >> Cases_on `is_word_type typ` >>
  simp[empty_word_full_ok_mods,empty_buffer_route_mods]
QED

Theorem convert_expr_full_ok_mods:
  !mods exps cx ann dst args.
    (!s x t. type_check (type_builtin_args_length_ok Convert (LENGTH args))
      "TypeBuiltin args" s = (INL x,t) ==> body_exprs_full_ok_mods mods exps cx args) ==>
    body_expr_full_ok_mods mods exps cx (TypeBuiltin ann Convert dst args)
Proof
  rpt gen_tac >> disch_then (assume_tac o MATCH_MP type_builtin_args_at_arity_mods) >>
  simp[Once body_expr_full_ok_mods_def] >> rpt gen_tac >> strip_tac >>
  `?e. args = [e]` by
    (drule expr_body_pre_mods_well_typed >>
     simp[Once well_typed_expr_def,well_typed_type_builtin_args_def,
          listTheory.LENGTH_EQ_NUM_compute]) >>
  gvs[] >>
  `body_expr_full_ok_mods mods exps cx e` by
    fs[type_builtin_args_length_ok_def,Once body_exprs_full_ok_mods_def] >>
  Cases_on `is_bytestring_type dst`
  >- (drule_all convert_bytes_route_mods >> simp[]) >>
  Cases_on `is_bytestring_type (expr_type e)`
  >- (drule_all convert_dynamic_route_mods >> simp[]) >>
  drule_all convert_scalar_route_mods >> simp[]
QED

Theorem make_array_expr_full_ok_mods:
  !mods exps cx ann t n args.
    (builtin_args_length_ok (MakeArray t n) (LENGTH args) ==>
       body_exprs_full_ok_mods mods exps cx args) ==>
    body_expr_full_ok_mods mods exps cx (Builtin ann (MakeArray t n) args)
Proof
  rpt gen_tac >> disch_tac >> simp[Once body_expr_full_ok_mods_def] >>
  rpt gen_tac >> strip_tac >>
  ONCE_REWRITE_TAC [CONJ_COMM] >> Cases_on `t` >>
  (irule make_tuple_route_from_elements_mods ORELSE
   irule make_array_route_from_elements_mods) >>
  pure_rewrite_tac [EQT_INTRO make_elements_from_transfer_mods,
    EQT_INTRO (GEN_ALL make_buffer_init_mods),
    EQT_INTRO (GEN_ALL (INST_TYPE [alpha |-> ``:256``] make_array_completed_mods)),
    AND_CLAUSES] >>
  map_every qexists_tac [`env`,`exps`,`mods`,`src`,`tops`] >> simp[]
QED

Theorem bop_in_expr_full_ok_mods:
  !mods exps cx ann bop args.
    (bop = In \/ bop = NotIn) /\
    (builtin_args_length_ok (Bop bop) (LENGTH args) ==>
      body_exprs_full_ok_mods mods exps cx args) ==>
    body_expr_full_ok_mods mods exps cx (Builtin ann (Bop bop) args)
Proof
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  simp[Once body_expr_full_ok_mods_def] >> rpt gen_tac >> strip_tac >>
  `?e1 e2. args = [e1;e2] /\ well_typed_binop ann bop (expr_type e1) (expr_type e2)` by
    (drule expr_body_pre_mods_well_typed >>
     simp[Once well_typed_expr_def,well_typed_builtin_app_def] >> strip_tac >>
     qpat_x_assum `LENGTH args = 2` mp_tac >>
     simp[listTheory.LENGTH_EQ_NUM_compute] >> strip_tac >> gvs[]) >>
  qpat_x_assum `args = [e1;e2]` SUBST_ALL_TAC >>
  `is_word_type (expr_type e1) /\ ann = BaseT BoolT` by
    gvs[well_typed_binop_def,membership_element_word_boundary,is_word_type_def] >>
  qpat_x_assum `ann = BaseT BoolT` SUBST_ALL_TAC >>
  `body_exprs_full_ok_mods mods exps cx [e1;e2]` by fs[builtin_args_length_ok_def] >>
  Cases_on `?a t n elems. e2 = Builtin a (MakeArray t n) elems`
  >- (pop_assum strip_assume_tac >> qpat_x_assum `e2 = Builtin _ _ _` SUBST_ALL_TAC >>
      qpat_assum `body_exprs_full_ok_mods _ _ _ [e1;_]`
        (strip_assume_tac o ONCE_REWRITE_RULE [body_exprs_full_ok_mods_def]) >>
      irule membership_literal_sim_mods >>
      qpat_assum `module_body_inv _ _ _ _ _` (irule_at Any) >>
      qpat_assum `body_const_cells_agree_mods _ _ _ _` (irule_at Any) >>
      qexists_tac `exps` >> simp[] >> strip_tac >>
      `body_exprs_full_ok_mods mods exps cx [Builtin a (MakeArray t n) elems]` by
        (first_x_assum irule >> metis_tac[]) >>
      fs[Once body_exprs_full_ok_mods_def]) >>
  conj_asm1_tac
  >- (irule membership_ordinary_value_mods >>
      qpat_assum `module_body_inv _ _ _ _ _` (irule_at Any) >>
      qpat_assum `body_const_cells_agree_mods _ _ _ _` (irule_at Any) >>
      qexists_tac `exps` >> simp[] >> metis_tac[]) >>
  irule scalar_stack_vv_sim_full_mods >>
  simp[expr_type_def,is_word_type_def,compile_bop_stack] >>
  rpt strip_tac >> drule_then ACCEPT_TAC eval_expr_builtin_value
QED


Theorem ecrecover_expr_full_ok_mods[local]:
  !mods exps cx ann args.
    (builtin_args_length_ok ECRecover (LENGTH args) ==>
      body_exprs_full_ok_mods mods exps cx args) ==>
    body_expr_full_ok_mods mods exps cx (Builtin ann ECRecover args)
Proof
  rpt gen_tac >> disch_tac >>
  simp[Once body_expr_full_ok_mods_def] >> rpt gen_tac >> strip_tac >>
  irule ecrecover_from_suffix_mods >> conj_tac
  >- (rpt strip_tac >> irule scalar_stack_vv_sim_full_mods >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  map_every qexists_tac [`env`,`exps`,`mods`,`src`,`tops`] >> simp[]
QED

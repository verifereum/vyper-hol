(* Lowered source capacity for the plain convert operand. *)
Theory bodyMemTbConvertLoweredSize
Ancestors exprSimIfExp exprSafeOperand exprSimHyps memoryLocalRhsProps
  exprSimSource exprSimHypsDefs
  vyperTypeSystem vyperValue vyperABI exprLowering context list compileEnv

Theorem convert_args_evaluate_types[local]:
  !args env acc.
    well_typed_exprs env args /\
    (!id t. FLOOKUP env.var_types id = SOME t ==>
            well_formed_type env.type_defs t) ==>
    ?tvs. evaluate_types env.type_defs (MAP expr_type args) acc = SOME tvs
Proof
  Induct >> simp[well_typed_expr_def, evaluate_type_def] >>
  rpt strip_tac >>
  `well_formed_type env.type_defs (expr_type h)` by
    metis_tac[well_typed_expr_type_well_formed] >>
  gvs[well_formed_type_def, optionTheory.IS_SOME_EXISTS] >>
  first_x_assum irule >> metis_tac[]
QED

Theorem convert_abi_encode_lowered_fits:
  !ce env ann ensure mid ty args.
    well_typed_expr env (TypeBuiltin ann (AbiEncode ensure mid) ty args) /\
    (!id t. FLOOKUP env.var_types id = SOME t ==>
            well_formed_type env.type_defs t) /\
    sfields_tenv_consistent ce.ce_struct_fields env.type_defs ==>
    is_bytestring_type ann /\
    is_bytestring_type (lowered_value_type ce
      (TypeBuiltin ann (AbiEncode ensure mid) ty args)) /\
    arg_type_fits (lowered_value_type ce
      (TypeBuiltin ann (AbiEncode ensure mid) ty args)) ann
Proof
  rpt gen_tac >> strip_tac >>
  gvs[well_typed_expr_def, type_builtin_result_ok_def] >>
  `?tvs. evaluate_types env.type_defs (MAP expr_type args) [] = SOME tvs` by
    metis_tac[convert_args_evaluate_types] >>
  qmatch_goalsub_abbrev_tac `lowered_value_type ce be` >>
  `abi_size_bound ce.ce_struct_fields
     (if LENGTH args = 1 /\ ~ensure then expr_type (HD args)
      else TupleT (MAP expr_type args)) <=
   vyper_abi_size_bound env.type_defs
     (if LENGTH args = 1 /\ ~ensure then expr_type (HD args)
      else TupleT (MAP expr_type args))` by
    (IF_CASES_TAC
     >- (gvs[LENGTH_EQ_NUM_compute, evaluate_type_def, AllCaseEqs()] >>
         irule ifexp_abi_size_bound_source >> metis_tac[]) >>
     irule ifexp_abi_tuple_size_bound_source >> metis_tac[]) >>
  gvs[Abbr `be`, lowered_value_type_def, is_bytestring_type_def,
      arg_type_fits_def, compatible_bound_def] >>
  `abi_encode_method_id_size mid = if IS_SOME mid then 4 else 0` by
    (Cases_on `mid` >>
     gvs[well_typed_type_builtin_args_def, abi_encode_method_id_size_def,
         vyperASTTheory.abi_encode_method_id_bytes_def]) >>
  qpat_x_assum `abi_encode_size_ok _ _ _ _ _` mp_tac >>
  simp[abi_encode_size_ok_def] >>
  Cases_on `args` >- gvs[well_typed_type_builtin_args_def] >>
  Cases_on `t` >> gvs[] >> Cases_on `ensure` >> gvs[] >> decide_tac
QED

Theorem convert_plain_lowered_type_compatible:
  !ce e env.
    well_typed_expr env e /\
    (!id t. FLOOKUP env.var_types id = SOME t ==>
            well_formed_type env.type_defs t) /\
    sfields_tenv_consistent ce.ce_struct_fields env.type_defs /\
    (!a f args d. e = Call a (IntCall f) args d ==>
       lowered_value_type ce e = expr_type e) ==>
    lowered_value_type ce e = expr_type e \/
    is_bytestring_type (expr_type e) /\
    is_bytestring_type (lowered_value_type ce e) /\
    arg_type_fits (lowered_value_type ce e) (expr_type e)
Proof
  ho_match_mp_tac lowered_value_type_ind >> rpt conj_tac
  >- (simp[lowered_value_type_def, vyperASTTheory.expr_type_def, well_typed_expr_def,
           well_typed_literal_def, is_bytestring_type_def, arg_type_fits_def,
           compatible_bound_def])
  >- (simp[lowered_value_type_def, vyperASTTheory.expr_type_def, well_typed_expr_def,
           well_typed_literal_def, is_bytestring_type_def, arg_type_fits_def,
           compatible_bound_def])
  >- (rpt strip_tac >> disj2_tac >>
      simp[lowered_value_type_def, vyperASTTheory.expr_type_def] >>
      irule ifexp_concat_lowered_fits >>
      gvs[well_typed_expr_def] >> metis_tac[])
  >- (rpt strip_tac >> disj2_tac >> simp[vyperASTTheory.expr_type_def] >>
      irule convert_abi_encode_lowered_fits >> metis_tac[])
  >- (rpt strip_tac >> disj1_tac >> first_x_assum irule >> simp[])
  >> simp[lowered_value_type_def]
QED

Theorem convert_plain_body_pre_lowered_size:
  !ce cx env e es tops.
    expr_body_pre ce cx env e es /\ supported_expr tops e /\
    (!a f args d. e = Call a (IntCall f) args d ==>
       lowered_value_type ce e = expr_type e) ==>
    type_memory_bytes ce (lowered_value_type ce e) <=
    type_memory_bytes ce (expr_type e)
Proof
  rpt gen_tac >> strip_tac >>
  drule expr_body_pre_var_types_well_formed >> strip_tac >>
  `well_typed_expr env e /\
   sfields_tenv_consistent ce.ce_struct_fields env.type_defs` by
    gvs[exprSimHypsDefsTheory.expr_body_pre_def,
        exprSimHypsDefsTheory.expr_sim_inv_def,
        vyperTypeInvariantsTheory.env_consistent_def,
        vyperTypeInvariantsTheory.env_context_consistent_def] >>
  drule_all convert_plain_lowered_type_compatible >> strip_tac >>
  irule lowered_value_type_memory_bound >> metis_tac[]
QED

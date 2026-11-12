(* Pure arms cannot select the internal-call layout alternative. *)
Theory bodyIntCallPureLayout
Ancestors
  exprSimIfExpCompat supportedExprs exprLowering vyperAST compileEnv
  exprSimAbiEncodeArgsPhysicalCapacity exprSafeOperand
  list vyperValue exprSimSource exprSimHyps

(* Purity excludes internal calls at the recursion boundary, so no agreement
   between source function signatures and compiler return layouts is needed.
   AbiEncode uses the argument IHs to compare physical and source capacities. *)
Theorem pure_expr_lowered_type_compatible:
  well_typed_expr env e /\
  (!id t. FLOOKUP env.var_types id = SOME t ==>
          well_formed_type env.type_defs t) /\
  sfields_tenv_consistent ce.ce_struct_fields env.type_defs /\
  supported_pure_expr tops e ==>
  lowered_value_type ce e = expr_type e \/
  (is_bytestring_type (expr_type e) /\
   is_bytestring_type (lowered_value_type ce e) /\
   arg_type_fits (lowered_value_type ce e) (expr_type e))
Proof
  map_every qid_spec_tac [`tops`, `env`, `e`, `ce`] >>
  ho_match_mp_tac lowered_value_type_ind >>
  simp[lowered_value_type_def, expr_type_def, supported_pure_expr_def,
       vyperTypeSystemTheory.well_typed_expr_def,
       vyperTypeSystemTheory.type_builtin_result_ok_def,
       is_bytestring_type_def] >>
  rpt strip_tac >> gvs[vyperTypeSystemTheory.well_typed_literal_def,
    vyperTypeSystemTheory.arg_type_fits_def, vyperValueTheory.compatible_bound_def]
  >~ [`concat_buffer_type ty _`]
  >- (disj2_tac >> irule ifexp_concat_lowered_fits >> goal_assum drule) >>
  suspend "abi_encode"
QED

Resume pure_expr_lowered_type_compatible[abi_encode]:
  `!xs. well_typed_exprs env xs ==>
         EVERY (well_formed_type env.type_defs o expr_type) xs` by
    (Induct >> simp[vyperTypeSystemTheory.well_typed_expr_def] >>
     rpt strip_tac >> irule well_typed_expr_type_well_formed >>
     goal_assum drule >> simp[]) >>
  `EVERY (well_formed_type env.type_defs o expr_type) args` by metis_tac[] >>
  `!xs acc. EVERY (well_formed_type env.type_defs o expr_type) xs ==>
     ?tvs. evaluate_types env.type_defs (MAP expr_type xs) acc = SOME tvs` by
    (Induct >> simp[evaluate_type_def, vyperTypeSystemTheory.well_formed_type_def] >>
     rpt strip_tac >> gvs[optionTheory.IS_SOME_EXISTS] >> simp[]) >>
  `?tvs. evaluate_types env.type_defs (MAP expr_type args) [] = SOME tvs` by metis_tac[] >>
  `abi_size_bound ce.ce_struct_fields
     (if LENGTH args = 1 /\ ~ensure then lowered_value_type ce (HD args)
      else TupleT (MAP (lowered_value_type ce) args)) <=
   abi_size_bound ce.ce_struct_fields
     (if LENGTH args = 1 /\ ~ensure then expr_type (HD args)
      else TupleT (MAP expr_type args))` by
    (IF_CASES_TAC
     >- (irule (cj 1 abi_args_fits_size_bound) >>
         gvs[LENGTH_EQ_NUM_compute, vyperTypeSystemTheory.well_typed_expr_def,
             supported_pure_expr_def] >>
         metis_tac[ifexp_arg_type_fits_refl]) >>
     simp[] >> irule (cj 2 abi_args_fits_size_bound) >>
     `!xs. EVERY (\e. arg_type_fits (lowered_value_type ce e) (expr_type e)) xs ==>
       arg_types_fit (MAP (lowered_value_type ce) xs) (MAP expr_type xs)` by
       (Induct >> simp[vyperTypeSystemTheory.arg_type_fits_def]) >>
     first_x_assum irule >> simp[EVERY_MEM] >> rpt strip_tac >>
     `well_typed_expr env e` by metis_tac[well_typed_exprs_member] >>
     `supported_pure_expr tops e` by
       metis_tac[supported_pure_exprs_every, EVERY_MEM] >>
     metis_tac[ifexp_arg_type_fits_refl]) >>
  suspend "abi_source_bound"
QED

Resume pure_expr_lowered_type_compatible[abi_source_bound]:
  qabbrev_tac `enc_ty = if LENGTH args = 1 /\ ~ensure then expr_type (HD args)
                       else TupleT (MAP expr_type args)` >>
  `abi_size_bound ce.ce_struct_fields enc_ty <= vyper_abi_size_bound env.type_defs enc_ty` by
    (simp[Abbr `enc_ty`] >> IF_CASES_TAC >-
       (`?tv. evaluate_type env.type_defs (expr_type (HD args)) = SOME tv` by
          (gvs[LENGTH_EQ_NUM_compute, combinTheory.o_DEF,
               evaluate_type_def, AllCaseEqs()]) >>
        irule ifexp_compat_abi_size_bound_source >> simp[] >> metis_tac[]) >>
     irule ifexp_compat_abi_tuple_size_bound_source >> simp[] >> metis_tac[]) >>
  `abi_encode_method_id_size method_id = if IS_SOME method_id then 4 else 0` by
    (Cases_on `method_id` >>
     gvs[vyperTypeSystemTheory.well_typed_type_builtin_args_def,
         vyperTypeSystemTheory.abi_encode_method_id_size_def,
         vyperASTTheory.abi_encode_method_id_bytes_def]) >>
  qpat_x_assum `abi_encode_size_ok _ _ _ _ _` mp_tac >>
  simp[vyperTypeSystemTheory.abi_encode_size_ok_def] >>
  Cases_on `args` >>
  gvs[vyperTypeSystemTheory.well_typed_type_builtin_args_def] >>
  simp[Abbr `enc_ty`, is_bytestring_type_def] >>
  qmatch_asmsub_rename_tac `well_typed_exprs env (head::rest)` >>
  Cases_on `ensure` >> Cases_on `rest` >>
  gvs[is_bytestring_type_def] >> strip_tac >> disj2_tac >>
  irule arithmeticTheory.LESS_EQ_TRANS >> goal_assum (drule_at Any) >>
  simp[] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Finalise pure_expr_lowered_type_compatible

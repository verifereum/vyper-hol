(*
 * The right-hand side of an Assign or AnnAssign to a memory-backed local
 * (#637): the facts about e that stmtSimAssignMem's and stmtSimDeclMem's
 * statement lemmas take, derived from e's typing and the allocation
 * check.
 *
 * TOP-LEVEL:
 *   lowered_value_type_shape, lowered_value_type_memory_bound — the type
 *                     e is lowered at, and its size below 2 ** 64
 *   memory_rhs_destination_bound, memory_rhs_read_destination_footprint —
 *                     e's value fits the local's buffer
 *   memory_rhs_read_lowered_typed, memory_rhs_read_destination_typed,
 *   memory_rhs_read_local_type — e's value (read through read_result) has
 *                     its lowered type and the local's
 *   memory_rhs_runtime_layout, memory_rhs_lowered_runtime_layout — the
 *                     types evaluate, at the sizes type_memory_bytes gives
 *   memory_rhs_empty_read_total, memory_rhs_empty_read_destination,
 *   memory_rhs_empty_eval_destination — an empty value reads as the
 *                     local type's default
 *)

Theory memoryLocalRhsProps
Ancestors
  compileEnv exprLowering stmtLowering vyperTypeSystem exprSimAggregates
  vyperAST vyperInterpreter vyperValue vyperState exprSim
  exprSimAggregateSource vyperValueOperation abiCallerAbiBound supportedTypes
  supportedExprs supportedExprForms vyperABI exprSimHyps
  vyperTypeEvalSoundness vyperTypeExprSoundness vyperTypeCallGraph
  valueTypingMemoryProps valueCopyBytes
Libs
  monadsyntax

(* Only the bytelike-producing branches change the runtime buffer type. *)
Theorem lowered_value_type_shape:
  !cenv e env.
    well_typed_expr env e ==>
    lowered_value_type cenv e = expr_type e \/
    is_bytestring_type (expr_type e) /\
    is_bytestring_type (lowered_value_type cenv e)
Proof
  ho_match_mp_tac lowered_value_type_ind >>
  simp[lowered_value_type_def, expr_type_def, is_bytestring_type_def,
       well_typed_expr_def, type_builtin_result_ok_def] >>
  rpt strip_tac >> gvs[is_bytestring_type_def]
QED

Theorem eval_empty_bytes_read:
  !cx ann es.
    (do r <- eval_expr cx (Literal ann (BytesL []));
        read_result cx r od) es = (INL (BytesV []), es)
Proof
  simp[Once evaluate_def, bind_def, read_result_def, return_def,
       vyperValueOperationTheory.evaluate_literal_def]
QED

Theorem eval_empty_dynamic_array_read:
  !cx ann et n tv es.
    evaluate_type (get_tenv cx) et = SOME tv ==>
    (do r <- eval_expr cx (Builtin ann (MakeArray (SOME et) (Dynamic n)) []);
        read_result cx r od) es =
    (INL (default_value (ArrayTV tv (Dynamic n))), es)
Proof
  rpt strip_tac >>
  `eval_expr cx (Builtin ann (MakeArray (SOME et) (Dynamic n)) []) es =
     (INL (Value (ArrayV (make_array_value tv (Dynamic n) []))), es)` by
    (simp[Once evaluate_def, vyperContextTheory.builtin_args_length_ok_def,
          type_check_def, assert_def, ignore_bind_def, bind_def, return_def,
          get_accounts_def, lift_sum_def, vyperContextTheory.evaluate_builtin_def] >>
     simp[Once evaluate_def, return_def, bind_def,
          compatible_bound_def]) >>
  simp[bind_def, read_result_def, return_def, default_value_def,
       make_array_value_def]
QED

Theorem allocation_limit_word_room:
  !sz. sz < 2 ** 64 ==> sz + 64 < dimword (:256)
Proof
  simp[wordsTheory.dimword_def] >> decide_tac
QED

Theorem bytestring_memory_bytes_positive:
  !cenv t. is_bytestring_type t ==> 0 < type_memory_bytes cenv t
Proof
  Cases_on `t` >> simp[is_bytestring_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >> simp[is_bytestring_type_def] >>
  TRY (rename1 `BytesT bd` >> Cases_on `bd`) >>
  simp[is_bytestring_type_def, type_memory_bytes_def]
QED

Theorem arg_type_fits_bytestring_memory_bytes:
  !cenv t u.
    is_bytestring_type t /\ arg_type_fits t u ==>
    type_memory_bytes cenv t <= type_memory_bytes cenv u
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `t` >> gvs[is_bytestring_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >> gvs[is_bytestring_type_def]
  >~ [`is_bytestring_type (BaseT (BytesT bd))`]
  >- (Cases_on `bd` >> gvs[is_bytestring_type_def] >>
      Cases_on `u` >> gvs[arg_type_fits_def] >>
      rename1 `arg_type_fits (BaseT (BytesT (Dynamic _))) (BaseT ub)` >>
      Cases_on `ub` >> gvs[arg_type_fits_def] >>
      rename1 `arg_type_fits _ (BaseT (BytesT ud))` >>
      Cases_on `ud` >> gvs[arg_type_fits_def] >>
      simp[type_memory_bytes_def] >>
      rename1 `n <= m` >>
      `(n + 31) DIV 32 <= (m + 31) DIV 32` by
        (irule arithmeticTheory.DIV_LE_MONOTONE >> simp[]) >> decide_tac) >>
  Cases_on `u` >> gvs[arg_type_fits_def] >>
  rename1 `arg_type_fits (BaseT (StringT _)) (BaseT ub)` >>
  Cases_on `ub` >> gvs[arg_type_fits_def] >>
  simp[type_memory_bytes_def] >> rename1 `n <= m` >>
  `(n + 31) DIV 32 <= (m + 31) DIV 32` by
    (irule arithmeticTheory.DIV_LE_MONOTONE >> simp[]) >> gvs[] >> decide_tac
QED

Theorem supported_tuple_abi_size_bound:
  !sf tenv t.
    supported_tuple_type t ==>
    abi_size_bound sf t = vyper_abi_size_bound tenv t
Proof
  rpt gen_tac >> Cases_on `t` >> simp[supported_tuple_type_def] >>
  rename1 `EVERY supported_scalar_type ts` >> strip_tac >>
  `EVERY (abi_caller_abi_bound sf tenv) ts` by
    (irule listTheory.EVERY_MONOTONIC >>
     qexists_tac `supported_scalar_type` >> simp[] >>
     Cases >> simp[supported_scalar_type_def, supported_word_type_def,
                   supported_string_type_def] >>
     simp[abi_caller_abi_bound_base]) >>
  drule abi_caller_abi_bound_tuple >> simp[abi_caller_abi_bound_def]
QED

Theorem lowered_value_type_arg_fits:
  !cenv e env tops.
    supported_expr tops e /\ well_typed_expr env e ==>
    lowered_value_type cenv e = expr_type e \/
    arg_type_fits (lowered_value_type cenv e) (expr_type e)
Proof
  ho_match_mp_tac lowered_value_type_ind >>
  simp[lowered_value_type_def, expr_type_def] >> rpt conj_tac
  >- simp[well_typed_expr_def, well_typed_literal_def, arg_type_fits_def]
  >- simp[well_typed_expr_def, well_typed_literal_def, arg_type_fits_def,
          compatible_bound_def]
  >- (rpt gen_tac >>
      simp[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def,
           supported_type_builtin_form_def] >>
      strip_tac >>
      Cases_on `args` >> gvs[] >>
      rename1 `supported_pure_exprs tops (a :: tail)` >> Cases_on `tail` >> gvs[] >>
      Cases_on `method_id` >> gvs[] >>
      gvs[well_typed_expr_def, type_builtin_result_ok_def,
          well_typed_type_builtin_args_def, abi_encode_size_ok_def,
          abi_encode_method_id_size_def, abi_encode_method_id_bytes_def] >>
      `abi_size_bound cenv.ce_struct_fields (expr_type a) =
       vyper_abi_size_bound env.type_defs (expr_type a)` by
        metis_tac[supported_tuple_abi_size_bound] >>
      simp[arg_type_fits_def]) >>
  simp[]
QED

Theorem lowered_value_type_memory_bound:
  !cenv e env tops.
    supported_expr tops e /\ well_typed_expr env e ==>
    type_memory_bytes cenv (lowered_value_type cenv e) <=
    type_memory_bytes cenv (expr_type e)
Proof
  rpt strip_tac >>
  `lowered_value_type cenv e = expr_type e \/
   is_bytestring_type (expr_type e) /\
   is_bytestring_type (lowered_value_type cenv e)` by
    metis_tac[lowered_value_type_shape]
  >- simp[] >>
  `lowered_value_type cenv e = expr_type e \/
   arg_type_fits (lowered_value_type cenv e) (expr_type e)` by
    metis_tac[lowered_value_type_arg_fits]
  >- simp[] >>
  irule arg_type_fits_bytestring_memory_bytes >> simp[]
QED

Theorem arg_type_fits_bytestring_source:
  !t u. is_bytestring_type u /\ arg_type_fits t u ==> is_bytestring_type t
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `u` >> gvs[is_bytestring_type_def] >>
  rename1 `BaseT ub` >> Cases_on `ub` >> gvs[is_bytestring_type_def]
  >~ [`is_bytestring_type (BaseT (BytesT bd))`]
  >- (Cases_on `bd` >> gvs[is_bytestring_type_def] >>
      Cases_on `t` >> gvs[arg_type_fits_def, is_bytestring_type_def] >>
      rename1 `arg_type_fits (BaseT tb) _` >> Cases_on `tb` >>
      gvs[arg_type_fits_def, is_bytestring_type_def] >>
      rename1 `arg_type_fits (BaseT (BytesT bd)) _` >> Cases_on `bd` >>
      gvs[arg_type_fits_def, is_bytestring_type_def]) >>
  Cases_on `t` >> gvs[arg_type_fits_def, is_bytestring_type_def] >>
  rename1 `arg_type_fits (BaseT tb) _` >> Cases_on `tb` >>
  gvs[arg_type_fits_def, is_bytestring_type_def] >>
  rename1 `arg_type_fits (BaseT (BytesT bd)) _` >> Cases_on `bd` >>
  gvs[arg_type_fits_def, is_bytestring_type_def]
QED

Theorem memory_rhs_destination_bound:
  !cenv e env tops ty tenv.
    supported_expr tops e /\ well_typed_expr env e /\
    type_widens_to tenv (expr_type e) ty /\
    (expr_type e = ty \/ is_bytestring_type ty) /\
    0 < type_memory_bytes cenv ty ==>
    0 < type_memory_bytes cenv (lowered_value_type cenv e) /\
    type_memory_bytes cenv (lowered_value_type cenv e) <=
      type_memory_bytes cenv ty
Proof
  rpt gen_tac >> strip_tac >>
  `type_memory_bytes cenv (lowered_value_type cenv e) <=
   type_memory_bytes cenv (expr_type e)` by
    metis_tac[lowered_value_type_memory_bound] >>
  `0 < type_memory_bytes cenv (expr_type e)` by
    metis_tac[bytestring_memory_bytes_positive,
              arg_type_fits_bytestring_source, type_widens_to_def] >>
  `0 < type_memory_bytes cenv (lowered_value_type cenv e)` by
    metis_tac[bytestring_memory_bytes_positive, lowered_value_type_shape] >>
  `type_memory_bytes cenv (expr_type e) <= type_memory_bytes cenv ty` by
    (Cases_on `expr_type e = ty` >- simp[] >>
     `is_bytestring_type (expr_type e) /\ arg_type_fits (expr_type e) ty` by
       metis_tac[type_widens_to_def, arg_type_fits_bytestring_source] >>
     irule arg_type_fits_bytestring_memory_bytes >> simp[]) >>
  simp[] >> decide_tac
QED

Theorem abi_encode_lowered_well_typed:
  !env a mid ty target sf.
    supported_tuple_type (expr_type a) /\ LENGTH mid = 4 /\
    well_typed_expr env (TypeBuiltin ty (AbiEncode F (SOME mid)) target [a]) ==>
    well_typed_expr env
      (TypeBuiltin
        (BaseT (BytesT (Dynamic (abi_size_bound sf (expr_type a) + 4))))
        (AbiEncode F (SOME mid)) target [a])
Proof
  rpt gen_tac >> strip_tac >>
  `abi_size_bound sf (expr_type a) =
   vyper_abi_size_bound env.type_defs (expr_type a)` by
    metis_tac[supported_tuple_abi_size_bound] >>
  gvs[well_typed_expr_def, type_builtin_result_ok_def,
      well_typed_type_builtin_args_def, well_formed_type_def,
      abi_encode_size_ok_def, abi_encode_method_id_size_def,
      abi_encode_method_id_bytes_def, evaluate_type_def] >>
  gvs[type_slot_size_def, vfmConstantsTheory.word_size_def] >>
  `((vyper_abi_size_bound env.type_defs (expr_type a) + 4) + 31) DIV 32 <=
    (n + 31) DIV 32` by
    (irule arithmeticTheory.DIV_LE_MONOTONE >> simp[]) >> gvs[] >> decide_tac
QED

Theorem word_size_monotone:
  !n m. n <= m ==> word_size n <= word_size m
Proof
  rpt strip_tac >> simp[vfmConstantsTheory.word_size_def] >>
  irule arithmeticTheory.DIV_LE_MONOTONE >> simp[]
QED

Theorem memory_rhs_read_annotation_typed:
  !cenv cx env e es v es'.
    expr_body_pre cenv cx env e es /\
    (do r <- eval_expr cx e; read_result cx r od) es = (INL v, es') ==>
    value_runtime_typed env (expr_type e) v
Proof
  rpt strip_tac >>
  drule_at (Pat `bind _ _ _ = _`) eval_expr_read_type_sound >>
  disch_then (qspec_then `env` mp_tac) >>
  gvs[expr_body_pre_def, expr_sim_inv_def]
QED

Theorem memory_rhs_read_lowered_typed:
  !cenv e env tops cx es v es'.
    expr_body_pre cenv cx env e es /\ supported_expr tops e /\
    (do r <- eval_expr cx e; read_result cx r od) es = (INL v, es') ==>
    value_runtime_typed env (lowered_value_type cenv e) v
Proof
  ho_match_mp_tac lowered_value_type_ind >> rpt conj_tac
  >- (rpt gen_tac >> simp[lowered_value_type_def] >> strip_tac >>
      gvs[Once evaluate_def, bind_def, return_def, read_result_def,
          evaluate_literal_def] >>
      gvs[expr_body_pre_def, well_typed_expr_def, well_typed_literal_def,
          well_formed_type_def, evaluate_type_def] >>
      simp[value_runtime_typed_def, evaluate_type_def,
           vyperTypingTheory.value_has_type_def, compatible_bound_def] >>
      gvs[type_slot_size_def, compatible_bound_def] >>
      imp_res_tac word_size_monotone >> decide_tac)
  >- (rpt gen_tac >> simp[lowered_value_type_def] >> strip_tac >>
      gvs[Once evaluate_def, bind_def, return_def, read_result_def,
          evaluate_literal_def] >>
      gvs[expr_body_pre_def, well_typed_expr_def, well_typed_literal_def,
          well_formed_type_def, evaluate_type_def] >>
      simp[value_runtime_typed_def, evaluate_type_def,
           vyperTypingTheory.value_has_type_def, compatible_bound_def] >>
      gvs[type_slot_size_def, compatible_bound_def] >>
      imp_res_tac word_size_monotone >> decide_tac)
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `supported_expr _ _` mp_tac >>
      simp[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def,
           supported_type_builtin_form_def] >> strip_tac >>
      Cases_on `args` >> gvs[] >>
      rename1 `supported_pure_exprs tops (a :: tail)` >> Cases_on `tail` >> gvs[] >>
      Cases_on `method_id` >> gvs[] >>
      gvs[lowered_value_type_def, expr_body_pre_def] >>
      rename1 `well_typed_expr env (TypeBuiltin ann (AbiEncode F (SOME mid)) target [a])` >>
      `supported_tuple_type (expr_type a)` by
        gvs[well_typed_expr_def, type_builtin_result_ok_def,
            well_typed_type_builtin_args_def] >>
      `well_typed_expr env
        (TypeBuiltin
          (BaseT (BytesT (Dynamic (abi_size_bound cenv.ce_struct_fields (expr_type a) + 4))))
          (AbiEncode F (SOME mid)) target [a])` by
        metis_tac[abi_encode_lowered_well_typed] >>
      metis_tac[type_builtin_read_annotation_typed]) >>
  rpt gen_tac >> strip_tac >> simp[lowered_value_type_def] >>
  metis_tac[memory_rhs_read_annotation_typed]
QED

Theorem memory_rhs_read_destination_typed:
  !cenv cx env e es v es' ty.
    expr_body_pre cenv cx env e es /\
    type_widens_to env.type_defs (expr_type e) ty /\
    (do r <- eval_expr cx e; read_result cx r od) es = (INL v, es') ==>
    value_runtime_typed env ty v
Proof
  rpt strip_tac >>
  drule_all memory_rhs_read_annotation_typed >>
  simp[value_runtime_typed_def] >> strip_tac >>
  simp[value_runtime_typed_def] >>
  metis_tac[vyperTypeArgFitsTheory.type_widens_to_value_has_type]
QED

Theorem memory_rhs_runtime_layout:
  !cenv cx env es ty v.
    expr_sim_inv cenv cx env es /\ value_runtime_typed env ty v ==>
    ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
         value_has_type tv v /\ type_memory_bytes cenv ty = type_memory_size tv
Proof
  rpt strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def,
        vyperTypeInvariantsTheory.env_context_consistent_def] >>
  gvs[value_runtime_typed_def] >>
  metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size]
QED

Theorem eval_empty_type_read:
  !cx ann t tv es.
    evaluate_type (get_tenv cx) t = SOME tv ==>
    (do r <- eval_expr cx (TypeBuiltin ann Empty t []);
        read_result cx r od) es = (INL (default_value tv), es)
Proof
  rpt strip_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, lift_sum_def,
       vyperContextTheory.type_builtin_args_length_ok_def] >>
  simp[Once evaluate_def, return_def,
       vyperContextTheory.evaluate_type_builtin_def, bind_def, read_result_def]
QED

Theorem memory_rhs_empty_read_total:
  !cx env e es.
    env.type_defs = get_tenv cx /\ well_typed_expr env e /\
    is_empty_value_expr e /\ has_length_word (expr_type e) ==>
    ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
         (do r <- eval_expr cx e; read_result cx r od) es =
         (INL (default_value tv), es)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `e` >> gvs[is_empty_value_expr_def]
  >~ [`Literal ann lit`]
  >- (Cases_on `lit` >> gvs[is_empty_value_expr_def] >>
      rename1 `Literal ann (BytesL bs)` >> Cases_on `bs` >>
      gvs[is_empty_value_expr_def, well_typed_expr_def, well_typed_literal_def] >>
      Cases_on `ann` >> gvs[well_typed_literal_def] >>
      rename1 `BaseT bt` >> Cases_on `bt` >> gvs[well_typed_literal_def] >>
      rename1 `BytesT bd` >> Cases_on `bd` >>
      gvs[has_length_word_def, is_bytestring_type_def, expr_type_def,
          eval_empty_bytes_read, well_formed_type_def, evaluate_type_def,
          default_value_def])
  >~ [`TypeBuiltin ann tb target args`]
  >- (Cases_on `tb` >> gvs[is_empty_value_expr_def] >>
      gvs[well_typed_expr_def, type_builtin_result_ok_def, expr_type_def,
          well_typed_type_builtin_args_def, well_formed_type_def,
          optionTheory.IS_SOME_EXISTS] >>
      simp[eval_empty_type_read]) >>
  rename1 `Builtin ann builtin args` >>
  Cases_on `builtin` >> gvs[is_empty_value_expr_def] >>
  rename1 `MakeArray et bd` >> Cases_on `et` >> gvs[is_empty_value_expr_def] >>
  Cases_on `args` >> gvs[is_empty_value_expr_def] >>
  gvs[well_typed_expr_def, well_typed_builtin_app_def, expr_type_def] >>
  Cases_on `bd` >> gvs[has_length_word_def, is_bytestring_type_def] >>
  gvs[well_formed_type_def, evaluate_type_def, optionTheory.IS_SOME_EXISTS,
      AllCaseEqs()] >>
  simp[eval_empty_dynamic_array_read]
QED

Theorem memory_rhs_empty_read_destination:
  !cx env e es ty tyv.
    env.type_defs = get_tenv cx /\ well_typed_expr env e /\
    is_empty_value_expr e /\ has_length_word (expr_type e) /\
    type_widens_to env.type_defs (expr_type e) ty /\
    evaluate_type (get_tenv cx) ty = SOME tyv ==>
    (do r <- eval_expr cx e; read_result cx r od) es =
    (INL (default_value tyv), es)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all memory_rhs_empty_read_total >>
  disch_then (qspec_then `es` strip_assume_tac) >>
  gvs[type_widens_to_def] >>
  drule_all (CONJUNCT1 vyperTypeArgFitsTheory.arg_type_fits_default_value) >>
  simp[]
QED

Theorem type_widens_to_has_length_word:
  !t u tenv.
    has_length_word t /\ type_widens_to tenv t u ==> has_length_word u
Proof
  rpt gen_tac >> strip_tac >> gvs[type_widens_to_def] >>
  Cases_on `t` >> gvs[has_length_word_def, is_bytestring_type_def]
  >~ [`arg_type_fits (ArrayT et bd) u`]
  >- (Cases_on `bd` >> gvs[has_length_word_def] >>
      Cases_on `u` >> gvs[arg_type_fits_def, has_length_word_def,
                            is_bytestring_type_def] >>
      rename1 `ArrayT _ ub` >> Cases_on `ub` >>
      gvs[arg_type_fits_def, has_length_word_def, is_bytestring_type_def]) >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  gvs[is_bytestring_type_def] >>
  Cases_on `u` >> gvs[arg_type_fits_def, has_length_word_def,
                       is_bytestring_type_def] >>
  rename1 `BaseT ub` >> Cases_on `ub` >>
  gvs[arg_type_fits_def, is_bytestring_type_def] >>
  rename1 `arg_type_fits (BaseT (BytesT sb)) (BaseT (BytesT db))` >>
  Cases_on `sb` >> Cases_on `db` >>
  gvs[arg_type_fits_def, is_bytestring_type_def]
QED

Theorem memory_rhs_read_destination_footprint:
  !cenv cx env e es tops ty tyv v es1.
    expr_body_pre cenv cx env e es /\ supported_expr tops e /\
    type_widens_to env.type_defs (expr_type e) ty /\
    (expr_type e = ty \/ is_bytestring_type ty) /\
    evaluate_type (get_tenv cx) ty = SOME tyv /\
    (do r <- eval_expr cx e; read_result cx r od) es = (INL v, es1) ==>
    value_has_type tyv v /\
    val_footprint tyv v <= type_memory_bytes cenv (lowered_value_type cenv e)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_sim_inv cenv cx env es /\ well_typed_expr env e` by
    fs[expr_body_pre_def] >>
  `value_runtime_typed env ty v` by
    metis_tac[memory_rhs_read_destination_typed] >>
  `value_runtime_typed env (lowered_value_type cenv e) v` by
    metis_tac[memory_rhs_read_lowered_typed] >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def,
        vyperTypeInvariantsTheory.env_context_consistent_def] >>
  `?ltv. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME ltv /\
          value_has_type ltv v /\
          type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size ltv` by
    metis_tac[memory_rhs_runtime_layout] >>
  `value_has_type tyv v` by
    gvs[value_runtime_typed_def] >>
  simp[] >>
  Cases_on `lowered_value_type cenv e = ty`
  >- (gvs[] >> irule val_footprint_le >> simp[value_has_type_memory_wf]) >>
  `is_bytestring_type ty /\ is_bytestring_type (lowered_value_type cenv e)` by
    metis_tac[lowered_value_type_shape, type_widens_to_def,
              arg_type_fits_bytestring_source] >>
  `val_footprint tyv v = val_footprint ltv v` by
    metis_tac[bytestring_val_footprint_eq] >>
  simp[] >> irule val_footprint_le >> simp[value_has_type_memory_wf]
QED

Theorem padded_bytes_bound_256[local]:
  !n. 32 * ((n + 31) DIV 32) + 32 < 2 ** 64 ==> n < dimword (:256)
Proof
  simp[wordsTheory.dimword_def] >> rpt strip_tac >>
  qspec_then `32` mp_tac arithmeticTheory.DIVISION >>
  (impl_tac >- decide_tac) >>
  disch_then (qspec_then `n + 31` strip_assume_tac) >> decide_tac
QED

Theorem bytestring_memory_bound_evaluates:
  !cenv tenv t.
    is_bytestring_type t /\ type_memory_bytes cenv t < 2 ** 64 ==>
    ?tv. evaluate_type tenv t = SOME tv
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `t` >> gvs[is_bytestring_type_def] >>
  rename1 `is_bytestring_type (BaseT bt)` >> Cases_on `bt` >>
  gvs[is_bytestring_type_def]
  >~ [`BytesT bd`]
  >- (Cases_on `bd` >> gvs[is_bytestring_type_def] >>
      gvs[type_memory_bytes_def, evaluate_type_def, type_slot_size_def,
          vfmConstantsTheory.word_size_def, wordsTheory.dimword_def] >>
      irule (SRULE[wordsTheory.dimword_def] padded_bytes_bound_256) >> simp[]) >>
  gvs[type_memory_bytes_def, evaluate_type_def, type_slot_size_def,
      vfmConstantsTheory.word_size_def, wordsTheory.dimword_def] >>
  irule (SRULE[wordsTheory.dimword_def] padded_bytes_bound_256) >> simp[]
QED

Theorem memory_rhs_lowered_runtime_layout:
  !cenv cx env e es.
    expr_body_pre cenv cx env e es /\
    type_memory_bytes cenv (lowered_value_type cenv e) < 2 ** 64 ==>
    ?ltv. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME ltv /\
          type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size ltv
Proof
  rpt strip_tac >>
  `well_typed_expr env e /\ expr_sim_inv cenv cx env es` by
    fs[expr_body_pre_def] >>
  `?ltv. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME ltv` by
    (drule lowered_value_type_shape >>
     disch_then (qspec_then `cenv` strip_assume_tac)
     >- metis_tac[expr_body_pre_type_evaluates, optionTheory.IS_SOME_EXISTS] >>
     metis_tac[bytestring_memory_bound_evaluates]) >>
  qexists_tac `ltv` >> simp[] >>
  metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size]
QED

Theorem type_widens_to_has_length_word_source:
  !tenv t u.
    type_widens_to tenv t u /\ has_length_word u ==> has_length_word t
Proof
  rpt gen_tac >> strip_tac >> gvs[type_widens_to_def] >>
  Cases_on `u` >> gvs[has_length_word_def, is_bytestring_type_def]
  >~ [`arg_type_fits t (ArrayT et bd)`]
  >- (Cases_on `bd` >> gvs[has_length_word_def] >>
      Cases_on `t` >> gvs[arg_type_fits_def, has_length_word_def,
                            is_bytestring_type_def] >>
      rename1 `arg_type_fits (ArrayT _ sb) _` >> Cases_on `sb` >>
      gvs[arg_type_fits_def, has_length_word_def, is_bytestring_type_def]) >>
  rename1 `BaseT bt` >> Cases_on `bt` >> gvs[is_bytestring_type_def] >>
  Cases_on `t` >> gvs[arg_type_fits_def, has_length_word_def, is_bytestring_type_def] >>
  rename1 `arg_type_fits (BaseT sb) _` >> Cases_on `sb` >>
  gvs[arg_type_fits_def, has_length_word_def, is_bytestring_type_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  gvs[arg_type_fits_def, has_length_word_def, is_bytestring_type_def] >>
  rename1 `arg_type_fits _ (BaseT (BytesT db))` >> Cases_on `db` >>
  gvs[arg_type_fits_def, has_length_word_def, is_bytestring_type_def]
QED

Theorem eval_empty_value_result:
  !cx e es r es1.
    is_empty_value_expr e /\ eval_expr cx e es = (INL r,es1) ==>
    ?v. r = Value v
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `e` >> gvs[is_empty_value_expr_def]
  >~ [`Literal ann lit`]
  >- (Cases_on `lit` >> gvs[is_empty_value_expr_def] >>
      rename1 `BytesL bs` >> Cases_on `bs` >> gvs[is_empty_value_expr_def] >>
      gvs[Once evaluate_def, vyperValueOperationTheory.evaluate_literal_def,
          bind_def, return_def])
  >~ [`TypeBuiltin ann tb target args`]
  >- (Cases_on `tb` >> gvs[is_empty_value_expr_def] >>
      gvs[Once evaluate_def, ignore_bind_def, bind_def, return_def, AllCaseEqs()]) >>
  rename1 `Builtin ann builtin args` >> Cases_on `builtin` >>
  gvs[is_empty_value_expr_def] >>
  rename1 `MakeArray et bd` >> Cases_on `et` >> gvs[is_empty_value_expr_def] >>
  Cases_on `args` >> gvs[is_empty_value_expr_def] >>
  gvs[Once evaluate_def, ignore_bind_def, bind_def, return_def, AllCaseEqs()]
QED

Theorem memory_rhs_empty_eval_destination:
  !cx env e es ty tyv r es1.
    env.type_defs = get_tenv cx /\ well_typed_expr env e /\
    is_empty_value_expr e /\ has_length_word ty /\
    type_widens_to env.type_defs (expr_type e) ty /\
    evaluate_type (get_tenv cx) ty = SOME tyv /\
    eval_expr cx e es = (INL r,es1) ==>
    r = Value (default_value tyv)
Proof
  rpt strip_tac >>
  `has_length_word (expr_type e)` by
    metis_tac[type_widens_to_has_length_word_source] >>
  drule_all eval_empty_value_result >> strip_tac >> gvs[] >>
  `(do raw <- eval_expr cx e; read_result cx raw od) es =
   (INL (default_value tyv), es)` by
    (irule memory_rhs_empty_read_destination >> simp[] >>
     qexistsl_tac [`env`, `ty`] >> simp[]) >>
  gvs[bind_def, read_result_def, return_def]
QED

Theorem memory_rhs_read_local_type:
  !cenv cx env e es ty id tyv v es1 entry.
    expr_body_pre cenv cx env e es /\
    FLOOKUP env.var_types id = SOME ty /\
    evaluate_type (get_tenv cx) ty = SOME tyv /\
    (do r <- eval_expr cx e; read_result cx r od) es = (INL v, es1) /\
    lookup_scopes id es1.scopes = SOME entry ==> entry.type = tyv
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `bind _ _ _ = _` mp_tac >>
  simp[NoAsms, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_result_state >> gvs[] >>
  qspecl_then [`cx`, `e`] (mp_tac o CONJUNCT1)
    (cj 5 eval_scc_type_sound_mutual) >>
  disch_then (drule_at (Pat `eval_expr _ _ _ = _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  impl_tac >- gvs[expr_body_pre_def, expr_sim_inv_def] >>
  strip_tac >>
  qpat_x_assum `well_typed_expr env e ==> _` mp_tac >>
  impl_tac >- gvs[expr_body_pre_def] >>
  simp[] >> strip_tac >>
  gvs[vyperTypeInvariantsTheory.env_consistent_def,
      vyperTypeInvariantsTheory.env_scopes_consistent_def] >>
  metis_tac[optionTheory.SOME_11]
QED

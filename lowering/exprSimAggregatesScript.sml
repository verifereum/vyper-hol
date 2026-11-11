(*
 * Expression simulation: aggregates and type builtins (#636, Aggregates
 * and type builtins)
 *
 * The case lemmas of compile_expr_sim (exprSimMain) for struct and array
 * literals and the type builtins but extract32.  Proved: struct and array
 * literals, empty(T), max_value, min_value, epsilon, and the conversions
 * exprSimConvert proves (which rest on the cheated lower_value_word_shape).
 * Struct and array literals store each child with unwrap_value_sim, so
 * they carry exprSimUnwrap's cheated constructor immutable cases.
 * The other conversions, abi_encode and abi_decode are re-exported from
 * their leaf theories (exprSimConvertOther, exprSimAbiEncode,
 * exprSimAbiDecode).
 *
 * TOP-LEVEL:
 *   compile_struct_lit_case, compile_make_array_case — StructLit, MakeArray
 *                           (lists and tuples), row 1, for compile_expr_sim
 *                           and the body simulation; compile_struct_lit_sim
 *                           and compile_make_array_sim follow
 *   compile_empty_case    — empty(T), row 2: compile_empty_word_sim, the
 *                           literal 0, for a word type;
 *                           compile_empty_memory_sim, a zeroed buffer, for
 *                           the rest
 *   compile_bound_builtin_case_sim, compile_bound_builtin_case — max_value,
 *                           min_value and epsilon of a numeric type
 *                           (row 2): a Lit of the bound.
 *                           compile_max_value_sim, compile_min_value_sim
 *                           and compile_epsilon_sim follow from it
 *   compile_convert_case  — convert, row 3: compile_convert_word_case
 *                           (exprSimConvert) between integer types, from
 *                           bool to an integer and from an integer to
 *                           bool; compile_convert_other_case for the rest
 *                           (#548)
 *   compile_abi_encode_case, compile_abi_decode_case — abi_encode (#551),
 *                           abi_decode with its validation aborts, row 4
 *
 * StructLit, MakeArray and empty(T) of a type that is not a word build
 * their value in a buffer of their own, an ALLOCA of type_memory_bytes
 * bytes, as exprSimLiteralBuffer's bytes literals do:
 *   - expr_sim_pre's alloc_limits_expr bounds the buffer below 2 ** 64, so
 *     the ALLOCA's literal size does not wrap, and stmt_state_rel's
 *     alloca_room keeps the buffer's end below 2 ** 256, so the stores at
 *     ADD buf off do not wrap either;
 *   - the buffer is a fresh allocation, disjoint from the live locals and
 *     every other allocation, so the stores keep stmt_state_rel and the
 *     memory expr_post's frame asks for;
 *   - expr_sim_inv's struct fields clauses make the lowering's layout the
 *     source's: type_memory_bytes is type_memory_size, and a struct's
 *     fields, from ce_struct_fields, are the declaration's in its order,
 *     which well_typed_expr makes the literal's (the StructLit case takes
 *     its layout from the literal's own struct, whatever the caller's ty:
 *     compile_expr_struct_lit_ty).
 *
 * The elements of a struct or array literal are lowered as
 * cfn ...; ADD ...; unwrap_value, then stored into the buffer before the
 * next element runs, so an element's value need not outlive the next
 * element's fragment; the buffer's stored elements do, by the next
 * element's expr_post frame (the buffer's allocation id is below the
 * element's start counter and its region misses the live locals).  An
 * element that is a storage or transient array evaluates to a captured storage place:
 * these lemmas use exprs_case's expr_vv_case of each element, not its
 * expr_sim_case.
 *)

Theory exprSimAggregates
Ancestors
  exprSimAggregatesAllocCounted
  exprSimAbiDecode
  exprSimAbiEncode
  exprSimConvertOther
  exprWordOperand
  exprSimSource
  exprSimProps
  exprSimHypsDefs
  exprSimDefs
  loweringPosts
  exprSimAlloc
  allocLimits
  list  exprSimHyps exprSimConvert exprLowering compileEnv loweringStateRelDefs
  exprSimValues gasNormalPrefix gasSummary gasOutcome gasContext
  fragGasMode fragGasPath fragGasSeq
  valueEncoding valueEncodingDefs vyperAST vyperInterpreter vyperState vyperContext
  vyperValueOperation vyperTypeSystem fragExec venomState
  exprSimBuffer exprSimBufferEmptyExec exprSimAggregateLayout
  exprSimAggregateSource exprSimAggregateLoops exprSimAggregateChildren
  exprLoweringProps

(* The allocation must be a generated ALLOCA, not merely a tracked map entry. *)
Theorem aggregate_alloca_immutable_sep:
  stmt_state_rel ctx func cenv cx es t /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = venomInst$ALLOCA /\
  FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) ==>
  cenv.ce_is_ctor ==>
  !name itv iv io.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) =
      SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name =
      SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) b sz
Proof
  rpt strip_tac >>
  qpat_x_assum `stmt_state_rel ctx _ _ _ _ _` mp_tac >>
  simp[stmt_state_rel_def, immutable_alloca_sep_def] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qpat_x_assum `!inst b sz. MEM inst _ /\ _ ==> regions_disjoint _ _ b sz` irule >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem aggregate_outcome_map[local]:
  gas_outcome memory tops (ctx,func) source (es,s) Q R /\
  (!res ee t. Q res ee t ==> Q' (SUM_MAP f I res) ee t) /\
  (!res ee r. R res ee r ==> R' (SUM_MAP f I res) ee r) ==>
  gas_outcome memory tops (ctx,func) (bind source (return o f)) (es,s) Q' R'
Proof
  strip_tac >>
  `ignore_bind (bind source (return o f)) (return ()) =
   ignore_bind source (return ())` by
    (simp[FUN_EQ_THM, ignore_bind_def, bind_def, return_def] >>
     gen_tac >> Cases_on `source x` >> Cases_on `q` >> simp[]) >>
  gvs[gas_outcome_def] >> qexists_tac `marks`
  >- (disj1_tac >>
      qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
      pure_rewrite_tac[gas_summary_at_def, gas_marked_exec_def] >> strip_tac >>
      qexistsl_tac [`SUM_MAP f I res`, `es_end`, `r`] >>
      simp[bind_def, return_def] >>
      Cases_on `res` >> gvs[] >> metis_tac[]) >>
  disj2_tac >> metis_tac[]
QED

Theorem aggregate_struct_action[local]:
  eval_expr cx (StructLit ann nsid fields) =
  bind (eval_exprs cx (MAP SND fields))
    (return o (\vs. Value (StructV (ZIP (MAP FST fields,vs)))))
Proof
  simp[FUN_EQ_THM] >> gen_tac >>
  Cases_on `eval_exprs cx (MAP SND fields) x` >>
  drule aggregate_eval_struct >>
  disch_then (qspecl_then [`nsid`,`ann`] mp_tac) >>
  Cases_on `q` >> simp[bind_def, return_def]
QED

Theorem aggregate_tuple_action[local]:
  compatible_bound bnd (LENGTH args) ==>
  eval_expr cx (Builtin ann (MakeArray NONE bnd) args) =
  bind (eval_exprs cx args) (return o (\vs. Value (ArrayV (TupleV vs))))
Proof
  strip_tac >> simp[FUN_EQ_THM] >> gen_tac >>
  Cases_on `eval_exprs cx args x` >>
  drule_all aggregate_eval_make_tuple >>
  disch_then (qspec_then `ann` mp_tac) >>
  Cases_on `q` >> simp[bind_def, return_def]
QED

Theorem aggregate_array_action[local]:
  compatible_bound bnd (LENGTH args) /\
  evaluate_type (get_tenv cx) et = SOME tv ==>
  eval_expr cx (Builtin ann (MakeArray (SOME et) bnd) args) =
  bind (eval_exprs cx args)
    (return o (\vs. Value (ArrayV (make_array_value tv bnd vs))))
Proof
  strip_tac >> simp[FUN_EQ_THM] >> gen_tac >>
  Cases_on `eval_exprs cx args x` >>
  drule_all aggregate_eval_make_array >>
  disch_then (qspec_then `ann` mp_tac) >>
  Cases_on `q` >> simp[bind_def, return_def]
QED

Theorem aggregate_outcome_source_run[local]:
  gas_outcome memory tops (ctx,func) source (es,s) Q R ==>
  gas_outcome memory tops (ctx,func) source (es,s)
    (\res ee t. Q res ee t /\
       ?gs. source (es with gas_obs := gs) = (res,ee)) R
Proof
  simp[gas_outcome_def] >> strip_tac >> qexists_tac `marks`
  >- (disj1_tac >>
      qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
      pure_rewrite_tac[gas_summary_at_def, gas_marked_exec_def] >> strip_tac >>
      qexistsl_tac [`res`, `es_end`, `r`] >> simp[] >>
      first_x_assum (qspec_then `[]` assume_tac) >>
      gvs[] >> metis_tac[]) >>
  disj2_tac >> metis_tac[]
QED

Theorem compile_struct_lit_vv_case:
  !nocalls ctx func cenv cx ann nsid fields.
    exprs_case nocalls ctx func cenv cx (MAP SND fields) /\
    (~nocalls ==> !e. MEM e (MAP SND fields) ==>
       int_calls_expr e = [] \/ lowered_value_type cenv e = expr_type e) ==>
    expr_vv_case nocalls ctx func cenv cx (StructLit ann nsid fields)
Proof
  rw[expr_vv_case_def, expr_vv_sim_def] >>
  drule compile_struct_literal_inv >> strip_tac >> gvs[] >>
  drule struct_literal_lookup_types >> strip_tac >>
  drule struct_literal_evaluated_layout >> strip_tac >>
  `expr_sim_inv cenv cx env es` by gvs[expr_body_pre_def] >>
  `!e st. MEM e (MAP SND fields) /\ expr_sim_inv cenv cx env st ==>
    expr_body_pre cenv cx env e st /\ (nocalls ==> int_calls_expr e = [])` by
    metis_tac[expr_body_pre_struct_field] >>
  `!e. MEM e (MAP SND fields) /\ nocalls ==> int_calls_expr e = []` by metis_tac[] >>

  `ci_mono sa sm` by metis_tac[ci_mono_compile_alloc_buffer, pairTheory.SND] >>
  `ci_mono sm sb` by
    metis_tac[ci_mono_compile_struct_lit_cfn, compile_expr_ci_mono, pairTheory.SND] >>
  `cs_extends sa sm /\ cs_extends sm sb` by gvs[ci_mono_def] >>
  drule_all fn_has_code_split >> strip_tac >>
  `SUM (MAP (SND o SND)
    (get_struct_fields cenv.ce_struct_fields (nsid_to_string nsid))) <
    dimword (:256)` by
    (gvs[expr_body_pre_def, alloc_limits_expr_def, type_memory_bytes_def] >>
     simp[wordsTheory.dimword_def] >> decide_tac) >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all buffer_alloc_counted >> strip_tac >>
  qmatch_asmsub_abbrev_tac `compile_alloc_buffer sz sa` >>
  gvs[] >>
  drule_at (Pat `compile_struct_lit _ _ _ _ _ _ _ = _`) aggregate_struct_fields_sim >>
  simp[] >> disch_then drule >> disch_then drule >>
  simp[] >> disch_then drule >>
  disch_then (drule_at (Pat `lookup_var _ _ = _`)) >>
  disch_then (drule_at (Pat `MEM _ (fn_insts _)`)) >>
  simp[] >>
  disch_then (qspecl_then [`ctx`, `nocalls`] mp_tac) >>
  (impl_tac >- (rpt strip_tac >> simp[] >>
    irule aggregate_alloca_immutable_sep >>
    goal_assum (drule_at (Pat `stmt_state_rel ctx _ _ _ _ _`)) >>
    qpat_x_assum `MEM inst (fn_insts func)` kall_tac >>
    goal_assum (drule_at (Pat `MEM _ (fn_insts _)`)) >>
    simp[venomInstTheory.mk_inst_def] >>
    goal_assum (drule_at Any) >> simp[])) >> strip_tac >> gvs[] >>
  irule stmtSimDeclComposeTheory.gas_outcome_zero_prefix >>
  goal_assum (drule_at Any) >>
  rewrite_tac[aggregate_struct_action] >>
  drule aggregate_outcome_source_run >> strip_tac >>
  irule aggregate_outcome_map >>
  goal_assum (drule_at Any) >>
  conj_tac >- (rpt strip_tac >> gvs[sumTheory.SUM_MAP]) >>
  rpt strip_tac >> gvs[sumTheory.SUM_MAP] >>
  rename1 `eval_exprs cx (MAP SND fields) (es with gas_obs := gs) = (INL vs,ee)` >>
  `eval_expr cx (StructLit ann nsid fields) (es with gas_obs := gs) =
    (INL (Value (StructV (ZIP (MAP FST fields,vs)))),ee)` by
    (drule aggregate_eval_struct >> simp[]) >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` kall_tac >>
  rename1 `stmt_state_rel ctx func cenv cx ee s` >>
  `expr_body_pre cenv cx env (StructLit ann nsid fields) (es with gas_obs := gs)` by simp[] >>
  `ann = StructT nsid` by
    gvs[expr_body_pre_def, vyperTypeSystemTheory.well_typed_expr_def] >>
  gvs[] >>
  `val_wf (StructTV (ZIP (MAP FST fields,tvs)))
    (StructV (ZIP (MAP FST fields,vs)))` by
    (irule aggregate_materialised_child_wf >>
     goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >>
     simp[expr_type_def, read_result_def, return_def] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `val_footprint (StructTV (ZIP (MAP FST fields,tvs)))
     (StructV (ZIP (MAP FST fields,vs))) <= type_memory_size_list tvs` by
    (drule val_footprint_le >> simp[type_memory_size_def] >>
     `LENGTH (MAP FST fields) = LENGTH tvs` by
       (drule vyperTypeABITheory.OPT_MMAP_LENGTH >> simp[]) >>
     simp[struct_layout_size_zip]) >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (drule vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom >> simp[]) >>
  `!nm lb len. local_region cenv ee.scopes s nm lb len ==>
     b + type_memory_size_list tvs <= lb \/ lb + len <= b` by
    (rpt strip_tac >> drule_all aggregate_buffer_clearance >> simp[]) >>
  `~expr_has_effect (StructLit (StructT nsid) nsid fields) ==>
     pure_frame cenv func es sa s0 s` by
    (rewrite_tac[expr_has_effect_thm] >> strip_tac >>
     qpat_x_assum `EVERY _ _ ==> _` mp_tac >>
     (impl_tac >- (qpat_x_assum `~EXISTS _ _` mp_tac >>
        simp_tac (srw_ss()) [listTheory.EVERY_MAP, listTheory.EXISTS_MAP,
                             combinTheory.o_DEF])) >>
     strip_tac >>
     qpat_assum `FLOOKUP t.vs_allocas _ = SOME (b,_)` (fn th =>
       qpat_assum `!aid a. FLOOKUP t.vs_allocas aid = SOME a ==> _` (fn th2 =>
         assume_tac (MATCH_MP th2 th))) >>
     irule (Q.SPECL [`cenv`, `func`, `es`, `sa`, `sm`, `s0`, `t`, `s`]
       aggregate_pure_frame_buffer) >>
     qpat_assum `MEM (mk_inst sa.cs_next_id ALLOCA _ _) _` (irule_at Any) >>
     qpat_assum `FLOOKUP s.vs_allocas _ = SOME (b,_)` (irule_at Any) >>
     qexistsl_tac [`s0`, `sm`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     TRY (rewrite_tac[] >> NO_TAC) >>
     TRY (qpat_x_assum `ci_mono sa sm` mp_tac >> rewrite_tac[ci_mono_def] >>
          strip_tac >> first_assum ACCEPT_TAC >> NO_TAC) >>
     rpt strip_tac >>
     qpat_x_assum `!p n. (n + p <= b \/ _) /\ _ ==> _` irule >>
     conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     TRY (qpat_x_assum `p + n <= b` mp_tac) >>
     TRY (qpat_x_assum `b + type_memory_size_list tvs <= p` mp_tac) >>
     rpt (pop_assum kall_tac) >> decide_tac) >>
  irule buffer_loop_memory_vv_post >>
  simp[expr_type_def, is_word_type_def, contextTheory.mk_ptr_def, contextTheory.base_ptr_def,
    eval_operand_def, val_in_memory_def] >>
  qexistsl [`b`,`sm`,`type_memory_size_list tvs`,`t`] >>
  simp[wordsTheory.dimword_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `!aid p n. FLOOKUP t.vs_allocas aid = SOME (p,n) /\ _ ==> _` mp_tac >>
  qpat_x_assum `_ ==> pure_frame _ _ _ _ _ _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem compile_make_array_vv_case:
  !nocalls ctx func cenv cx ann topt bnd args.
    exprs_case nocalls ctx func cenv cx args /\
    (~nocalls ==> !e. MEM e args ==>
       int_calls_expr e = [] \/ lowered_value_type cenv e = expr_type e) ==>
    expr_vv_case nocalls ctx func cenv cx (Builtin ann (MakeArray topt bnd) args)
Proof
  rpt gen_tac >> Cases_on `topt`
  >- suspend "tuple" >> suspend "array"
QED

Resume compile_make_array_vv_case[tuple]:
  rw[expr_vv_case_def, expr_vv_sim_def] >>
  drule compile_tuple_literal_inv >> strip_tac >> gvs[] >>
  drule make_tuple_evaluated_layout >> strip_tac >> gvs[] >>
  gvs[exprLoweringTheory.tuple_literal_types_def, listTheory.MAP_MAP_o] >>
  `expr_sim_inv cenv cx env es` by gvs[expr_body_pre_def] >>
  `!e st. MEM e args /\ expr_sim_inv cenv cx env st ==>
    expr_body_pre cenv cx env e st /\ (nocalls ==> int_calls_expr e = [])` by
    (`!n t b. MakeArray t b <> Slice n` by simp[] >>
     metis_tac[expr_body_pre_builtin_arg, int_calls_builtin_arg]) >>
  `!e. MEM e args /\ nocalls ==> int_calls_expr e = []` by metis_tac[] >>
  `compatible_bound bnd (LENGTH args)` by
    gvs[expr_body_pre_def, vyperTypeSystemTheory.well_typed_expr_def,
      vyperTypeSystemTheory.well_typed_builtin_app_def] >>

  `ci_mono sa sm` by metis_tac[ci_mono_compile_alloc_buffer, pairTheory.SND] >>
  `ci_mono sm sb` by
    metis_tac[ci_mono_compile_make_tuple_cfn, compile_expr_ci_mono, pairTheory.SND] >>
  `cs_extends sa sm /\ cs_extends sm sb` by gvs[ci_mono_def] >>
  drule_all fn_has_code_split >> strip_tac >>
  `SUM (MAP (type_memory_bytes cenv) tys) < dimword (:256)` by
    (gvs[expr_body_pre_def, alloc_limits_expr_def, type_alloc_ok_def,
         type_memory_bytes_def, is_word_type_def] >>
     simp[wordsTheory.dimword_def] >> decide_tac) >>
  `type_memory_size_list tvs < dimword (:256)` by metis_tac[] >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all buffer_alloc_counted >> strip_tac >> gvs[] >>
  drule_at (Pat `compile_make_tuple _ _ _ _ _ _ _ = _`) aggregate_make_tuple_fits_sim >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then (drule_at (Pat `lookup_var _ _ = _`)) >>
  disch_then (drule_at (Pat `MEM _ (fn_insts _)`)) >> simp[] >>
  disch_then (qspecl_then [`ctx`,`nocalls`] mp_tac) >> simp[] >>
  (impl_tac >- (rpt strip_tac >> simp[] >>
    irule aggregate_alloca_immutable_sep >>
    goal_assum (drule_at (Pat `stmt_state_rel ctx _ _ _ _ _`)) >>
    qpat_x_assum `MEM inst (fn_insts func)` kall_tac >>
    goal_assum (drule_at (Pat `MEM _ (fn_insts _)`)) >>
    simp[venomInstTheory.mk_inst_def] >>
    goal_assum (drule_at Any) >> simp[])) >> strip_tac >> gvs[] >>
  irule stmtSimDeclComposeTheory.gas_outcome_zero_prefix >>
  goal_assum (drule_at Any) >>
  simp[aggregate_tuple_action] >>
  drule aggregate_outcome_source_run >> strip_tac >>
  irule aggregate_outcome_map >> goal_assum (drule_at Any) >>
  conj_tac >- (rpt strip_tac >> gvs[sumTheory.SUM_MAP]) >>
  rpt strip_tac >> gvs[sumTheory.SUM_MAP] >>
  rename1 `eval_exprs cx args (es with gas_obs := gs) = (INL vs,ee)` >>
  `eval_expr cx (Builtin (TupleT tys) (MakeArray NONE bnd) args)
    (es with gas_obs := gs) = (INL (Value (ArrayV (TupleV vs))),ee)` by
    (drule_all aggregate_eval_make_tuple >> simp[]) >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` kall_tac >>
  rename1 `stmt_state_rel ctx func cenv cx ee s` >>
  `expr_body_pre cenv cx env
    (Builtin (TupleT tys) (MakeArray NONE bnd) args)
    (es with gas_obs := gs)` by simp[] >>
  `val_wf (TupleTV tvs) (ArrayV (TupleV vs))` by
    (irule aggregate_materialised_child_wf >>
     goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >>
     simp[expr_type_def, read_result_def, return_def] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `val_footprint (TupleTV tvs) (ArrayV (TupleV vs)) <= type_memory_size_list tvs` by
    (drule val_footprint_le >> simp[type_memory_size_def]) >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (drule vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom >> simp[]) >>
  `!nm lb len. local_region cenv ee.scopes s nm lb len ==>
     b + type_memory_size_list tvs <= lb \/ lb + len <= b` by
    (rpt strip_tac >> drule_all aggregate_buffer_clearance >> simp[]) >>
  `~expr_has_effect (Builtin (TupleT tys) (MakeArray NONE bnd) args) ==>
     pure_frame cenv func es sa s0 s` by
    (rewrite_tac[expr_has_effect_thm] >> strip_tac >>
     qpat_x_assum `EVERY _ _ ==> _` mp_tac >>
     (impl_tac >- (qpat_x_assum `~EXISTS _ _` mp_tac >>
        simp_tac (srw_ss()) [listTheory.EVERY_MAP, listTheory.EXISTS_MAP,
                             combinTheory.o_DEF])) >>
     strip_tac >>
     qpat_assum `FLOOKUP t.vs_allocas _ = SOME (b,_)` (fn th =>
       qpat_assum `!aid a. FLOOKUP t.vs_allocas aid = SOME a ==> _` (fn th2 =>
         assume_tac (MATCH_MP th2 th))) >>
     irule (Q.SPECL [`cenv`, `func`, `es`, `sa`, `sm`, `s0`, `t`, `s`]
       aggregate_pure_frame_buffer) >>
     qpat_assum `MEM (mk_inst sa.cs_next_id ALLOCA _ _) _` (irule_at Any) >>
     qpat_assum `FLOOKUP s.vs_allocas _ = SOME (b,_)` (irule_at Any) >>
     qexistsl_tac [`s0`, `sm`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     TRY (rewrite_tac[] >> NO_TAC) >>
     TRY (qpat_x_assum `ci_mono sa sm` mp_tac >> rewrite_tac[ci_mono_def] >>
          strip_tac >> first_assum ACCEPT_TAC >> NO_TAC) >>
     rpt strip_tac >>
     qpat_x_assum `!p n. (n + p <= b \/ _) /\ _ ==> _` irule >>
     conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     TRY (qpat_x_assum `p + n <= b` mp_tac) >>
     TRY (qpat_x_assum `b + _ <= p` mp_tac) >>
     rpt (pop_assum kall_tac) >> decide_tac) >>
  irule (buffer_loop_memory_vv_post |> Q.INST
    [`e` |-> `Builtin (TupleT tys) (MakeArray NONE bnd) args`]
    |> SIMP_RULE (srw_ss()) [expr_type_def]) >>
  simp[expr_type_def, is_word_type_def, contextTheory.mk_ptr_def, contextTheory.base_ptr_def,
    eval_operand_def, val_in_memory_def] >>
  qexistsl [`b`,`sm`,`type_memory_size_list tvs`,`t`] >>
  simp[wordsTheory.dimword_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `!aid p n. FLOOKUP t.vs_allocas aid = SOME (p,n) /\ _ ==> _` mp_tac >>
  qpat_x_assum `_ ==> pure_frame _ _ _ _ _ _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

Resume compile_make_array_vv_case[array]:
  rw[expr_vv_case_def, expr_vv_sim_def] >>
  drule compile_array_literal_inv >> strip_tac >> gvs[] >>
  drule make_array_evaluated_layout >> strip_tac >> gvs[] >>
  `expr_sim_inv cenv cx env es` by gvs[expr_body_pre_def] >>
  `!e st. MEM e args /\ expr_sim_inv cenv cx env st ==>
    expr_body_pre cenv cx env e st /\ (nocalls ==> int_calls_expr e = [])` by
    (`!n t b. MakeArray t b <> Slice n` by simp[] >>
     metis_tac[expr_body_pre_builtin_arg, int_calls_builtin_arg]) >>
  `!e. MEM e args /\ nocalls ==> int_calls_expr e = []` by metis_tac[] >>
  `compatible_bound bnd (LENGTH args)` by
    gvs[expr_body_pre_def, vyperTypeSystemTheory.well_typed_expr_def,
      vyperTypeSystemTheory.well_typed_builtin_app_def] >>

  `ci_mono sa sm` by metis_tac[ci_mono_compile_alloc_buffer, pairTheory.SND] >>
  `ci_mono sm sb` by
    metis_tac[ci_mono_compile_make_array_cfn, compile_expr_ci_mono, pairTheory.SND] >>
  `cs_extends sa sm /\ cs_extends sm sb` by gvs[ci_mono_def] >>
  drule_all fn_has_code_split >> strip_tac >>
  `type_memory_bytes cenv (ArrayT x bnd) < dimword (:256)` by
    (gvs[expr_body_pre_def, alloc_limits_expr_def] >>
     simp[wordsTheory.dimword_def] >> decide_tac) >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all buffer_alloc_counted >> strip_tac >> gvs[] >>
  drule_at (Pat `compile_make_array _ _ _ _ _ _ _ _ = _`) aggregate_make_array_sim >>
  disch_then drule >> disch_then drule >>
  disch_then (drule_at (Pat `lookup_var _ _ = _`)) >>
  disch_then (drule_at (Pat `MEM _ (fn_insts _)`)) >>
  simp[wordsTheory.dimword_def] >>
  disch_then (qspecl_then [`env`,`es`,`ctx`,`nocalls`] mp_tac) >> simp[] >>
  (impl_tac >- (rpt strip_tac >> simp[] >>
    `regions_disjoint io (type_memory_size itv) b
       (type_memory_bytes cenv (ArrayT x bnd))` by
      (irule aggregate_alloca_immutable_sep >>
       goal_assum (drule_at (Pat `stmt_state_rel ctx _ _ _ _ _`)) >>
       qpat_x_assum `MEM inst (fn_insts func)` kall_tac >>
       goal_assum (drule_at (Pat `MEM _ (fn_insts _)`)) >>
       simp[venomInstTheory.mk_inst_def] >>
       goal_assum (drule_at Any) >> simp[]) >>
    gvs[regions_disjoint_def] >>
    qpat_x_assum `_ <= type_memory_bytes _ _` mp_tac >> decide_tac)) >> strip_tac >> gvs[] >>
  irule stmtSimDeclComposeTheory.gas_outcome_zero_prefix >>
  goal_assum (drule_at Any) >>
  `eval_expr cx (Builtin (ArrayT x bnd) (MakeArray (SOME x) bnd) args) =
    bind (eval_exprs cx args) (return o (\vs. Value (ArrayV (make_array_value tv bnd vs))))` by
    (irule aggregate_array_action >> simp[]) >>
  qpat_assum `eval_expr _ _ = bind _ _` (fn th => once_rewrite_tac[th]) >>
  drule aggregate_outcome_source_run >> strip_tac >>
  irule aggregate_outcome_map >> goal_assum (drule_at Any) >>
  conj_tac >- (rpt strip_tac >> gvs[sumTheory.SUM_MAP]) >>
  rpt strip_tac >> gvs[sumTheory.SUM_MAP] >>
  rename1 `eval_exprs cx args (es with gas_obs := gs) = (INL vs,ee)` >>
  `eval_expr cx (Builtin (ArrayT x bnd) (MakeArray (SOME x) bnd) args)
    (es with gas_obs := gs) = (INL (Value (ArrayV (make_array_value tv bnd vs))),ee)` by
    (simp[bind_def, return_def]) >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` kall_tac >>
  rename1 `stmt_state_rel ctx func cenv cx ee s` >>
  `expr_body_pre cenv cx env
    (Builtin (ArrayT x bnd) (MakeArray (SOME x) bnd) args)
    (es with gas_obs := gs)` by simp[] >>
  `val_wf (ArrayTV tv bnd) (ArrayV (make_array_value tv bnd vs))` by
    (irule aggregate_materialised_child_wf >>
     goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >>
     simp[expr_type_def, read_result_def, return_def] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `val_footprint (ArrayTV tv bnd) (ArrayV (make_array_value tv bnd vs)) <=
    type_memory_bytes cenv (ArrayT x bnd)` by
    (drule val_footprint_le >>
     `type_memory_bytes cenv (ArrayT x bnd) = type_memory_size (ArrayTV tv bnd)` by
       metis_tac[expr_sim_inv_memory_size] >> simp[]) >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (drule vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom >> simp[]) >>
  `!nm lb len. local_region cenv ee.scopes s nm lb len ==>
     b + type_memory_bytes cenv (ArrayT x bnd) <= lb \/ lb + len <= b` by
    (rpt strip_tac >> drule_all aggregate_buffer_clearance >> simp[]) >>
  `~expr_has_effect (Builtin (ArrayT x bnd) (MakeArray (SOME x) bnd) args) ==>
     pure_frame cenv func es sa s0 s` by
    (rewrite_tac[expr_has_effect_thm] >> strip_tac >>
     qpat_x_assum `EVERY _ _ ==> _` mp_tac >>
     (impl_tac >- (qpat_x_assum `~EXISTS _ _` mp_tac >>
        simp_tac (srw_ss()) [listTheory.EVERY_MAP, listTheory.EXISTS_MAP,
                             combinTheory.o_DEF])) >>
     strip_tac >>
     qpat_assum `FLOOKUP t.vs_allocas _ = SOME (b,_)` (fn th =>
       qpat_assum `!aid a. FLOOKUP t.vs_allocas aid = SOME a ==> _` (fn th2 =>
         assume_tac (MATCH_MP th2 th))) >>
     irule (Q.SPECL [`cenv`, `func`, `es`, `sa`, `sm`, `s0`, `t`, `s`]
       aggregate_pure_frame_buffer) >>
     qpat_assum `MEM (mk_inst sa.cs_next_id ALLOCA _ _) _` (irule_at Any) >>
     qpat_assum `FLOOKUP s.vs_allocas _ = SOME (b,_)` (irule_at Any) >>
     qexistsl_tac [`s0`, `sm`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     TRY (rewrite_tac[] >> NO_TAC) >>
     TRY (qpat_x_assum `ci_mono sa sm` mp_tac >> rewrite_tac[ci_mono_def] >>
          strip_tac >> first_assum ACCEPT_TAC >> NO_TAC) >>
     rpt strip_tac >>
     qpat_x_assum `!p n. (n + p <= b \/ _) /\ _ ==> _` irule >>
     conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     TRY (qpat_x_assum `p + n <= b` mp_tac) >>
     TRY (qpat_x_assum `b + _ <= p` mp_tac) >>
     rpt (pop_assum kall_tac) >> decide_tac) >>
  irule (buffer_loop_memory_vv_post |> Q.INST
    [`e` |-> `Builtin (ArrayT x bnd) (MakeArray (SOME x) bnd) args`]
    |> SIMP_RULE (srw_ss()) [expr_type_def]) >>
  simp[expr_type_def, is_word_type_def, contextTheory.mk_ptr_def,
    eval_operand_def] >>
  qexistsl [`b`,`sm`,`type_memory_bytes cenv (ArrayT x bnd)`,`t`] >>
  simp[wordsTheory.dimword_def] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[arithmeticTheory.ADD_COMM] >>
  conj_tac >-
    (rpt gen_tac >>
     qpat_x_assum `!aid p n. FLOOKUP t.vs_allocas aid = SOME (p,n) /\ _ ==> _` mp_tac >>
     qpat_x_assum `!name p n. local_region cenv es.scopes t name p n <=> _` mp_tac >>
     qpat_x_assum `t.vs_memory = s0.vs_memory` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  `LENGTH vs = LENGTH args` by (drule eval_exprs_length >> simp[]) >>
  Cases_on `bnd`
  >- (gvs[vyperValueTheory.compatible_bound_def] >>
      irule exprSimAggregateEncodingTheory.fixed_array_from_dense >> simp[]) >>
  gvs[vyperValueTheory.make_array_value_def, val_in_memory_def]
QED

Finalise compile_make_array_vv_case

Theorem compile_struct_lit_case:
  !nocalls ctx func cenv cx ann nsid fields.
    exprs_case nocalls ctx func cenv cx (MAP SND fields) /\
    (~nocalls ==> !e. MEM e (MAP SND fields) ==>
       int_calls_expr e = [] \/ lowered_value_type cenv e = expr_type e) ==>
    expr_sim_case nocalls ctx func cenv cx (StructLit ann nsid fields) /\
    expr_vv_case nocalls ctx func cenv cx (StructLit ann nsid fields)
Proof
  rpt strip_tac >>
  `post_value_type cenv (StructLit ann nsid fields) = expr_type (StructLit ann nsid fields)` by simp[] >>
  metis_tac[compile_struct_lit_vv_case, expr_sim_case_of_vv]
QED

Theorem compile_make_array_case:
  !nocalls ctx func cenv cx ann topt bnd args.
    exprs_case nocalls ctx func cenv cx args /\
    (~nocalls ==> !e. MEM e args ==>
       int_calls_expr e = [] \/ lowered_value_type cenv e = expr_type e) ==>
    expr_sim_case nocalls ctx func cenv cx
      (Builtin ann (MakeArray topt bnd) args) /\
    expr_vv_case nocalls ctx func cenv cx
      (Builtin ann (MakeArray topt bnd) args)
Proof
  rpt strip_tac >>
  `post_value_type cenv (Builtin ann (MakeArray topt bnd) args) = expr_type (Builtin ann (MakeArray topt bnd) args)` by simp[] >>
  metis_tac[compile_make_array_vv_case, expr_sim_case_of_vv]
QED

Theorem compile_struct_lit_sim:
  !cenv ann nsid fields.
    expr_sim_below cenv (expr_size (StructLit ann nsid fields)) ==>
    expr_vv_ok cenv (StructLit ann nsid fields)
Proof
  rpt strip_tac >> simp[expr_vv_ok_case] >> rpt gen_tac >>
  irule compile_struct_lit_vv_case >> simp[] >> irule exprs_case_every_ok >>
  irule expr_sim_below_struct_fields >> metis_tac[]
QED

Theorem compile_make_array_sim:
  !cenv ann topt bnd args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (Builtin ann (MakeArray topt bnd) args)
Proof
  rpt strip_tac >> simp[expr_vv_ok_case] >> rpt gen_tac >>
  irule compile_make_array_vv_case >> simp[] >> irule exprs_case_every_ok >>
  irule expr_sim_below_args >> first_assum ACCEPT_TAC
QED


(* ===== empty(T) ===== *)

Theorem eval_expr_empty:
  !cx ann t args es res es'.
    (do r <- eval_expr cx (TypeBuiltin ann Empty t args); read_result cx r od) es = (res, es') /\
    expr_res_ok res ==>
    es' = es /\ args = [] /\
    ?tv. evaluate_type (get_tenv cx) t = SOME tv /\
         res = INL (default_value tv)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `bind _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, lift_sum_def,
       type_builtin_args_length_ok_def] >>
  Cases_on `args` >> simp[raise_def] >>
  simp[Once evaluate_def, return_def, evaluate_type_builtin_def] >>
  Cases_on `evaluate_type (get_tenv cx) t` >>
  simp[return_def, raise_def, bind_def, read_result_def] >>
  rw[] >> gvs[expr_res_ok_def]
QED

Theorem typed_val_to_w256_address_zero[local]:
  typed_val_to_w256 (BaseTV AddressT) (BytesV (word_to_bytes (0w:address) T)) =
  0w
Proof
  `LENGTH (word_to_bytes (0w:address) T) = 20` by
    simp_tac (srw_ss() ++ wordsLib.SIZES_ss)
      [byteTheory.LENGTH_word_to_bytes] >>
  mp_tac (INST [``a:address`` |-> ``0w:address``]
            valueEncodingProofsTheory.val_to_w256_address) >>
  simp[val_to_w256_def, typed_val_to_w256_def]
QED

(* The default value of a word type is the word 0 in its typed encoding. *)
Theorem typed_val_to_w256_default_word:
  !tenv t tv.
    is_word_type t /\ evaluate_type tenv t = SOME tv ==>
    typed_val_to_w256 tv (default_value tv) = 0w
Proof
  rpt strip_tac >>
  `(?n. t = BaseT (UintT n)) \/ (?n. t = BaseT (IntT n)) \/
   t = BaseT BoolT \/ t = BaseT AddressT \/ t = BaseT DecimalT \/
   (?m. t = BaseT (BytesT (Fixed m)) /\ m <= 32) \/ (?n. t = FlagT n)` by
    (Cases_on `t` >> fs[is_word_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> fs[is_word_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >> fs[is_word_type_def]) >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  simp[vyperValueTheory.default_value_def, typed_val_to_w256_address_zero] >>
  simp[typed_val_to_w256_def, val_to_w256_def, integer_wordTheory.i2w_def] >>
  simp[listTheory.PAD_RIGHT, GSYM rich_listTheory.REPLICATE_GENLIST,
       rich_listTheory.REPLICATE_APPEND] >>
  EVAL_TAC >> simp[]
QED

(* empty(T) reads no gas observation: once admissible, it has the same
   value whatever the observations. *)
Theorem empty_read_all_tails[local]:
  !cx ann t args es.
    gas_admissible (bind (eval_expr cx (TypeBuiltin ann Empty t args))
      (read_result cx)) expr_res_ok es ==>
    args = [] /\
    ?tv. evaluate_type (get_tenv cx) t = SOME tv /\
      !gs. bind (eval_expr cx (TypeBuiltin ann Empty t args)) (read_result cx)
             (es with gas_obs := gs) =
           (INL (default_value tv), es with gas_obs := gs)
Proof
  rpt gen_tac >> rewrite_tac[gas_admissible_def] >> strip_tac >>
  `!gs. args = [] /\ ?tv. evaluate_type (get_tenv cx) t = SOME tv /\
     bind (eval_expr cx (TypeBuiltin ann Empty t args)) (read_result cx)
       (es with gas_obs := gs) = (INL (default_value tv), es with gas_obs := gs)` by
    (gen_tac >>
     Cases_on `bind (eval_expr cx (TypeBuiltin ann Empty t args))
                 (read_result cx) (es with gas_obs := gs)` >>
     first_assum drule >> strip_tac >>
     drule_all (SRULE [SF ETA_ss] eval_expr_empty) >> strip_tac >> gvs[]) >>
  first_assum (qspec_then `[]` strip_assume_tac) >> simp[] >>
  gen_tac >> first_x_assum (qspec_then `gs` strip_assume_tac) >> gvs[]
QED

(* empty(T) of a word type: the literal 0, no code. *)
Theorem compile_empty_word_sim:
  !cenv ann t args.
    is_word_type t ==> expr_sim_ok cenv (TypeBuiltin ann Empty t args)
Proof
  rw[expr_sim_ok_def] >> irule expr_sim_values >> rpt gen_tac >> strip_tac >>
  drule empty_read_all_tails >> strip_tac >> gvs[] >>
  `ann = t` by
    gvs[expr_sim_pre_def, well_typed_expr_def, type_builtin_result_ok_def] >>
  gvs[] >>
  qexistsl_tac [`[]`, `default_value tv`, `es`, `s0`] >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) s0` by
    (drule msg_gas_state_frame >>
     disch_then (qspecl_then [`s0.vs_gas_readings`, `s0.vs_inst_idx`, `[]`]
       mp_tac) >> simp[NoAsms]) >>
  gvs[gas_value_prefix_def, gas_marked_exec_def, gas_marked_path_def,
      lower_value_def, compile_expr_type_builtin_dispatch, comp_bind_def] >>
  gvs[Once compile_expr_def, unwrap_value_def, comp_return_def] >>
  conj_tac >- (irule (cj 1 gas_path_rules) >> simp[]) >>
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def,
       vyperASTTheory.expr_type_def, eval_operand_def] >>
  metis_tac[typed_val_to_w256_default_word]
QED

Theorem compile_empty_word_case_sim:
  !cenv ann t args.
    is_word_type t ==> expr_ok cenv (TypeBuiltin ann Empty t args)
Proof
  rpt strip_tac >> irule expr_ok_stack >> rpt conj_tac
  >~ [`eval_expr`] >- metis_tac[eval_expr_type_builtin_value]
  >~ [`expr_sim_ok`] >- simp[compile_empty_word_sim] >>
  rpt gen_tac >>
  simp[compile_expr_type_builtin_dispatch, Once compile_expr_def]
QED

(* empty(T) of any other type: a buffer of its own, of type_memory_bytes
   bytes (a multiple of 32), with its length word zeroed for a bytestring
   or dynamic array, whose default is empty, and every word zeroed for the
   rest.  The default value of any type lies in zeroed memory: a word's
   typed encoding is 0 (typed_val_to_w256_default_word), and a nested
   bytestring or dynamic array is empty, its length word 0. *)
(* The value form of empty_read_all_tails, for the vv judgment. *)
Theorem empty_eval_all_tails[local]:
  !cx ann t args es.
    gas_admissible (eval_expr cx (TypeBuiltin ann Empty t args))
      expr_vv_res_ok es ==>
    args = [] /\
    ?tv. evaluate_type (get_tenv cx) t = SOME tv /\
      !gs. eval_expr cx (TypeBuiltin ann Empty t args)
             (es with gas_obs := gs) =
           (INL (Value (default_value tv)), es with gas_obs := gs)
Proof
  rpt gen_tac >> rewrite_tac[gas_admissible_def] >> strip_tac >>
  `!gs. args = [] /\ ?tv. evaluate_type (get_tenv cx) t = SOME tv /\
     eval_expr cx (TypeBuiltin ann Empty t args) (es with gas_obs := gs) =
       (INL (Value (default_value tv)), es with gas_obs := gs)` by
    (gen_tac >>
     Cases_on `eval_expr cx (TypeBuiltin ann Empty t args)
                 (es with gas_obs := gs)` >>
     first_assum drule >> strip_tac >>
     rename1 `eval_expr _ _ _ = (res,es')` >>
     reverse (Cases_on `res`)
     >- (rename1 `INR exc` >>
         `(do r <- eval_expr cx (TypeBuiltin ann Empty t args);
               read_result cx r od) (es with gas_obs := gs) = (INR exc,es')` by
           simp[bind_def] >>
         `expr_res_ok (INR exc)` by gvs[expr_vv_res_ok_def, expr_res_ok_def] >>
         drule_all eval_expr_empty >> simp[]) >>
     drule eval_expr_type_builtin_value >> strip_tac >> gvs[] >>
     `(do r <- eval_expr cx (TypeBuiltin ann Empty t args);
           read_result cx r od) (es with gas_obs := gs) = (INL v,es')` by
       simp[bind_def, read_result_def, return_def] >>
     drule eval_expr_empty >> simp[expr_res_ok_def] >> strip_tac >> gvs[]) >>
  first_assum (qspec_then `[]` strip_assume_tac) >> simp[] >>
  gen_tac >> first_x_assum (qspec_then `gs` strip_assume_tac) >> gvs[]
QED

Theorem zero_words_no_gas[local]:
  !n pop sa sb.
    compile_zero_words pop n sa = ((),sb) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)
Proof
  Induct_on `n`
  >- simp[builtinSimpleTheory.compile_zero_words_def, comp_return_def, emitted_insts_def] >>
  rpt gen_tac >>
  simp[Once builtinSimpleTheory.compile_zero_words_def, comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> rename1 `compile_zero_words pop n sa = (u,sm)` >>
  Cases_on `u` >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  gvs[emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_id_def, fresh_var_def, emit_def] >>
  qpat_x_assum `sm.cs_current_insts = _` (fn th => rewrite_tac[th]) >>
  `!a b:num. a - (a + b) = 0 /\ a - (a + b + 1) = 0` by decide_tac >>
  simp[emitted_insts_def, DROP_APPEND, EVERY_APPEND] >>
  fs[emitted_insts_def, venomInstTheory.mk_inst_def]
QED

(* empty(T)'s buffer code reads no gas: its run is a gas path of no
   readings. *)
Theorem empty_complex_gas_path[local]:
  !sz header sa buf sb ctx func s t.
    compile_builtin_empty_complex sz header sa = (buf,sb) /\
    fn_has_code sa sb func /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    run_inst_seq (emitted_insts sa sb) s = OK t ==>
    gas_path ctx func s 0
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    t.vs_current_bb = sb.cs_current_bb
Proof
  rpt gen_tac >> strip_tac >>
  drule compile_builtin_empty_complex_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)` by
    (qpat_x_assum `compile_builtin_empty_complex _ _ _ = _` mp_tac >>
     simp[builtinSimpleTheory.compile_builtin_empty_complex_def, comp_bind_def, comp_return_def] >>
     pairarg_tac >> rename1 `compile_alloc_buffer sz sa = (ba,sm)` >>
     simp[] >> Cases_on `header` >>
     simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     pairarg_tac >> rename1 `_ = (u,st)` >> Cases_on `u` >> simp[] >>
     strip_tac >> gvs[]
     >- (gvs[contextTheory.compile_alloc_buffer_def, emitHelperTheory.emit_op_def,
             emitHelperTheory.emit_void_def, comp_bind_def,
             comp_ignore_bind_def, comp_return_def, fresh_id_def,
             fresh_var_def, emit_def] >>
         simp[emitted_insts_def, DROP_APPEND1, venomInstTheory.mk_inst_def]) >>
     drule zero_words_no_gas >> strip_tac >>
     `sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm /\
      EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sm)` by
       (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
        simp[contextTheory.compile_alloc_buffer_def,
             emitHelperTheory.emit_op_def, comp_bind_def, comp_return_def,
             comp_ignore_bind_def, fresh_id_def, fresh_var_def, emit_def] >>
        strip_tac >> gvs[] >>
        simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND,
             venomInstTheory.mk_inst_def]) >>
     `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
       (irule emitted_insts_append >> simp[]) >>
     simp[EVERY_APPEND]) >>
  `t.vs_current_bb = s.vs_current_bb` by
    (irule (SRULE [] (Q.ISPEC `\s:venom_state. s.vs_current_bb`
      run_inst_seq_preserves_field)) >>
     qexists_tac `emitted_insts sa sb` >> simp[] >> rpt strip_tac >>
     fs[EVERY_MEM] >>
     metis_tac[venomInstProofsTheory.step_preserves_control_flow,
               venomExecSemanticsTheory.step_inst_non_invoke]) >>
  gvs[fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  `isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[emitted_insts_def, rich_listTheory.DROP_APPEND1] >>
  drule_all fragGasSeqTheory.tuple_run_inst_seq_gas_path >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb)) = 0` by
    (simp[FILTER_EQ_NIL] >> fs[EVERY_MEM]) >>
  simp[emitted_insts_def]
QED

Theorem compile_empty_memory_sim:
  !cenv ann t args.
    ~is_word_type t ==> expr_vv_ok cenv (TypeBuiltin ann Empty t args)
Proof
  rw[expr_vv_ok_def, expr_vv_sim_def] >>
  drule empty_eval_all_tails >> strip_tac >> gvs[] >>
  `ann = t` by
    gvs[expr_sim_pre_def, well_typed_expr_def, type_builtin_result_ok_def] >>
  gvs[compile_expr_type_builtin_dispatch, Once compile_expr_def,
      comp_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >>
  `expr_sim_inv cenv cx env es` by gvs[expr_sim_pre_def] >>
  `type_memory_bytes cenv ann < dimword (:256)` by
    (gvs[expr_sim_pre_def, alloc_limits_expr_def] >>
     simp[wordsTheory.dimword_def] >> decide_tac) >>
  drule_all empty_type_buffer_size >> strip_tac >>
  drule_all compile_builtin_empty_complex_run >> strip_tac >>
  drule_all empty_complex_gas_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := [])
     (t with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (drule msg_gas_state_frame >>
     disch_then (qspecl_then [`t.vs_gas_readings`,
       `LENGTH sb.cs_current_insts`, `[]`] mp_tac) >> simp[NoAsms]) >>
  simp[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INL (Value (default_value tv))`, `es`,
    `OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)`] >>
  conj_tac >- simp[gas_marked_exec_def, gas_marked_path_def] >>
  simp[] >>
  once_rewrite_tac[GSYM (Q.INST [`gs` |-> `[]`] vv_post_initial_gas)] >>
  drule_all empty_type_default_memory >> strip_tac >>
  irule (SRULE [vyperASTTheory.expr_type_def]
    (Q.INST [`e` |-> `TypeBuiltin ann Empty ann []`,
             `p` |-> `base_ptr buf`] (SPEC_ALL buffer_memory_vv_post))) >>
  goal_assum (drule_at Any) >>
  simp[contextTheory.base_ptr_def, valueEncodingProofsTheory.val_wf_default_value_proof] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!name b len. local_region _ _ _ _ _ _ ==> _ \/ _` drule >>
      strip_tac >> first_x_assum irule >> decide_tac) >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!aid b len. _ ==> regions_disjoint _ _ b len` drule >>
      simp[loweringStateRelDefsTheory.regions_disjoint_def] >> strip_tac >>
      first_x_assum irule >> decide_tac) >>
  drule_all expr_sim_inv_memory_size >> strip_tac >>
  simp[val_footprint_le, valueEncodingProofsTheory.val_wf_default_value_proof] >>
  rpt strip_tac >>
  `local_region cenv es.scopes s0 n lb lsz` by
    (irule exprSimPropsTheory.local_region_frame >> conj_tac
     >- (qexists_tac `func` >> gvs[stmt_state_rel_def, state_rel_def]) >>
     qexistsl [`sa`, `es.scopes`, `t`] >> simp[]) >>
  qpat_x_assum `!name b len. local_region _ _ s0 _ _ _ ==> _` drule >>
  simp[arithmeticTheory.ADD_COMM]
QED

Theorem compile_empty_case:
  !nocalls ctx func cenv cx ann t args.
    expr_vv_case nocalls ctx func cenv cx (TypeBuiltin ann Empty t args)
Proof
  rpt gen_tac >> irule expr_vv_case_nil >> conj_tac
  >- rw[expr_body_pre_def, well_typed_expr_def, well_typed_type_builtin_args_def,
        vyperTypeCallGraphTheory.int_calls_expr_def] >>
  Cases_on `is_word_type t`
  >- metis_tac[compile_empty_word_case_sim, expr_ok_def] >>
  simp[compile_empty_memory_sim]
QED

(* ===== max_value, min_value, epsilon ===== *)

Theorem eval_expr_bound_builtin:
  !cx ann tb t args es res es'.
    (do result <- eval_expr cx (TypeBuiltin ann tb t args); read_result cx result od) es = (res, es') /\
    expr_res_ok res /\ MEM tb [MaxValue; MinValue; Epsilon] ==>
    es' = es /\ args = [] /\
    ?v. res = INL v /\ evaluate_type_builtin cx tb t [] [] = INL v
Proof
  rpt gen_tac >> strip_tac >>
  `!n. type_builtin_args_length_ok tb n <=> n = 0` by
    (Cases_on `tb` >> gvs[type_builtin_args_length_ok_def]) >>
  `!y. evaluate_type_builtin cx tb t [] [] = INR y ==> ?m. y = TypeError m` by
    (Cases_on `tb` >> gvs[evaluate_type_builtin_def, AllCaseEqs()] >>
     Cases_on `t` >> gvs[evaluate_max_value_def, evaluate_min_value_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     gvs[evaluate_max_value_def, evaluate_min_value_def, AllCaseEqs()]) >>
  qpat_x_assum `(do result <- eval_expr _ _; read_result _ result od) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, read_result_def, return_def,
       ignore_bind_def, type_check_def, assert_def, raise_def, lift_sum_def] >>
  Cases_on `args` >> simp[raise_def] >>
  simp[Once evaluate_def, bind_def, read_result_def, return_def] >>
  Cases_on `evaluate_type_builtin cx tb t [] []` >>
  simp[read_result_def, return_def, raise_def] >> rw[] >> gvs[expr_res_ok_def]
QED

(* max_value, min_value and epsilon read no gas observation either. *)
Theorem bound_read_all_tails[local]:
  !cx ann tb t args es.
    gas_admissible (bind (eval_expr cx (TypeBuiltin ann tb t args))
      (read_result cx)) expr_res_ok es /\
    MEM tb [MaxValue; MinValue; Epsilon] ==>
    args = [] /\
    ?v. evaluate_type_builtin cx tb t [] [] = INL v /\
      !gs. bind (eval_expr cx (TypeBuiltin ann tb t args)) (read_result cx)
             (es with gas_obs := gs) = (INL v, es with gas_obs := gs)
Proof
  rpt gen_tac >> rewrite_tac[gas_admissible_def] >> strip_tac >>
  `!gs. args = [] /\ ?v. evaluate_type_builtin cx tb t [] [] = INL v /\
     bind (eval_expr cx (TypeBuiltin ann tb t args)) (read_result cx)
       (es with gas_obs := gs) = (INL v, es with gas_obs := gs)` by
    (gen_tac >>
     Cases_on `bind (eval_expr cx (TypeBuiltin ann tb t args))
                 (read_result cx) (es with gas_obs := gs)` >>
     first_assum drule >> strip_tac >>
     qspecl_then [`cx`, `ann`, `tb`, `t`, `args`, `es with gas_obs := gs`,
                  `q`, `r`] mp_tac eval_expr_bound_builtin >>
     impl_tac >- gvs[SF ETA_ss] >>
     strip_tac >> gvs[]) >>
  first_assum (qspec_then `[]` strip_assume_tac) >> simp[] >>
  gen_tac >> first_x_assum (qspec_then `gs` strip_assume_tac) >> gvs[]
QED

(* max_value, min_value and epsilon of a numeric type: a Lit of the bound,
   no code. *)
Theorem compile_bound_builtin_word_sim:
  !cenv ann tb t args.
    MEM tb [MaxValue; MinValue; Epsilon] ==>
    expr_sim_ok cenv (TypeBuiltin ann tb t args)
Proof
  rewrite_tac[expr_sim_ok_def] >> rpt strip_tac >>
  irule expr_sim_values >> rpt gen_tac >> strip_tac >>
  drule_all bound_read_all_tails >> strip_tac >> gvs[] >>
  `ann = t /\ is_numeric_type t` by
    gvs[expr_sim_pre_def, well_typed_expr_def, type_builtin_result_ok_def,
        well_typed_type_builtin_args_def] >>
  `(?n. t = BaseT (UintT n)) \/ (?n. t = BaseT (IntT n)) \/
   t = BaseT DecimalT` by
    (Cases_on `t` >> gvs[] >> rename1 `BaseT bt` >> Cases_on `bt` >> gvs[]) >>
  qexistsl_tac [`[]`, `v`, `es`, `s0`] >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) s0` by
    (drule msg_gas_state_frame >>
     disch_then (qspecl_then [`s0.vs_gas_readings`, `s0.vs_inst_idx`, `[]`]
       mp_tac) >> simp[NoAsms]) >>
  gvs[gas_value_prefix_def, gas_marked_exec_def, gas_marked_path_def] >>
  gvs[evaluate_type_builtin_def, evaluate_max_value_def,
      evaluate_min_value_def, AllCaseEqs()] >>
  gvs[lower_value_def, compile_expr_type_builtin_dispatch, comp_bind_def] >>
  gvs[Once compile_expr_def, unwrap_value_def, comp_return_def,
      type_bounds_def, type_bits_def, is_signed_type_def] >>
  (conj_tac >- (irule (cj 1 gas_path_rules) >> simp[])) >>
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def,
       vyperASTTheory.expr_type_def, eval_operand_def, is_word_type_def,
       typed_val_to_w256_def, val_to_w256_def] >>
  simp[integerTheory.INT_SUB] >>
  rw[vyperValueTheory.evaluate_type_def] >>
  (* Keep symbolic signed bounds opaque to word arithmetic conversions. *)
  PURE_REWRITE_TAC
    [typed_val_to_w256_def, val_to_w256_def,
     integer_wordTheory.i2w_0, integer_wordTheory.i2w_pos] >>
  REFL_TAC
QED

Theorem compile_bound_builtin_case_sim:
  !cenv ann tb t args.
    MEM tb [MaxValue; MinValue; Epsilon] ==>
    expr_ok cenv (TypeBuiltin ann tb t args)
Proof
  rpt strip_tac >> irule expr_ok_stack >> rpt conj_tac
  >~ [`eval_expr`] >- metis_tac[eval_expr_type_builtin_value]
  >~ [`expr_sim_ok`]
  >- (irule compile_bound_builtin_word_sim >> first_assum ACCEPT_TAC) >>
  Cases_on `tb` >> gvs[] >> rpt gen_tac >>
  simp[compile_expr_type_builtin_dispatch, Once compile_expr_def] >>
  Cases_on `type_bounds t` >> simp[]
QED

Theorem compile_bound_builtin_case:
  !nocalls ctx func cenv cx ann tb t args.
    MEM tb [MaxValue; MinValue; Epsilon] ==>
    expr_vv_case nocalls ctx func cenv cx (TypeBuiltin ann tb t args)
Proof
  rpt strip_tac >> irule expr_vv_case_nil >> conj_tac
  >- (qpat_x_assum `MEM _ _` mp_tac >>
      rw[expr_body_pre_def, well_typed_expr_def,
         well_typed_type_builtin_args_def,
         vyperTypeCallGraphTheory.int_calls_expr_def] >>
      gvs[well_typed_type_builtin_args_def,
          vyperTypeCallGraphTheory.int_calls_expr_def]) >>
  metis_tac[compile_bound_builtin_case_sim, expr_ok_def]
QED

Theorem compile_max_value_sim:
  !cenv ann t args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (TypeBuiltin ann MaxValue t args)
Proof
  metis_tac[compile_bound_builtin_case_sim, expr_ok_def, listTheory.MEM]
QED

Theorem compile_min_value_sim:
  !cenv ann t args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (TypeBuiltin ann MinValue t args)
Proof
  metis_tac[compile_bound_builtin_case_sim, expr_ok_def, listTheory.MEM]
QED

Theorem compile_epsilon_sim:
  !cenv ann t args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (TypeBuiltin ann Epsilon t args)
Proof
  metis_tac[compile_bound_builtin_case_sim, expr_ok_def, listTheory.MEM]
QED

(* The conversions exprSimConvert does not cover: those to or from
   decimal, address, bytesM, bytestrings and flags, in exprSimConvertOther
   (#548). *)
Theorem compile_convert_other_case = exprSimConvertOtherTheory.compile_convert_other_case

Theorem compile_convert_case:
  !nocalls ctx func cenv cx ann t args.
    exprs_case nocalls ctx func cenv cx args /\
    (~nocalls ==> !e1 a f cargs d. args = [e1] /\ e1 = Call a (IntCall f) cargs d ==>
       lowered_value_type cenv e1 = expr_type e1) ==>
    expr_vv_case nocalls ctx func cenv cx (TypeBuiltin ann Convert t args)
Proof
  rpt strip_tac >>
  Cases_on `?e1. args = [e1] /\ int_convert_pair (expr_type e1) t`
  >- (gvs[] >> irule compile_convert_word_case >> simp[]) >>
  irule compile_convert_other_case >> metis_tac[]
QED

Theorem compile_abi_encode_case = exprSimAbiEncodeTheory.compile_abi_encode_case

Theorem compile_abi_decode_case = exprSimAbiDecodeTheory.compile_abi_decode_case

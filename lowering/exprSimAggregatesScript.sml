(*
 * Expression simulation: aggregates and type builtins (#636, Aggregates
 * and type builtins)
 *
 * The case lemmas of compile_expr_sim (exprSimMain) for struct and array
 * literals and the type builtins but extract32.  Proved: struct and array
 * literals, empty(T), max_value, min_value, epsilon, and the conversions
 * exprSimConvert proves (which rest on the cheated lower_value_word_shape).
 * Struct and array literals store each child with unwrap_value_sim, so
 * they carry exprSimUnwrap's cheated storage, immutable and copy cases.
 * Cheated, for the later #636 PRs: the other conversions, abi_encode and
 * abi_decode.
 *
 * TOP-LEVEL:
 *   compile_struct_lit_sim, compile_make_array_sim — StructLit, MakeArray
 *                           (lists and tuples), row 1
 *   compile_empty_sim     — empty(T), row 2: compile_empty_word_sim, the
 *                           literal 0, for a word type;
 *                           compile_empty_memory_sim, a zeroed buffer, for
 *                           the rest
 *   compile_bound_builtin_case_sim — max_value, min_value and epsilon of
 *                           a numeric type (row 2): a Lit of the bound.
 *                           compile_max_value_sim, compile_min_value_sim
 *                           and compile_epsilon_sim follow from it
 *   compile_convert_sim   — convert, row 3: compile_convert_word_sim
 *                           (exprSimConvert) between integer types, from
 *                           bool to an integer and from an integer to
 *                           bool; compile_convert_other_sim for the rest
 *                           (#548)
 *   compile_abi_encode_sim, compile_abi_decode_sim — abi_encode (#551),
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
 * element that is a storage or transient array evaluates to an ArrayRef:
 * these lemmas use the induction hypothesis's expr_vv_ok of each element
 * (expr_sim_below_mem), not expr_sim_ok.
 *)

Theory exprSimAggregates
Ancestors
  list exprSim exprSimHyps exprSimConvert exprLowering compileEnv
  valueEncoding vyperAST vyperInterpreter vyperState vyperContext
  vyperValueOperation vyperTypeSystem fragExec venomState
  exprSimBuffer exprSimBufferEmptyExec exprSimAggregateLayout
  exprSimAggregateSource exprSimAggregateLoops exprSimAggregateChildren
  exprLoweringProps

Theorem compile_struct_lit_sim:
  !cenv ann nsid fields.
    expr_sim_below cenv (expr_size (StructLit ann nsid fields)) ==>
    expr_vv_ok cenv (StructLit ann nsid fields)
Proof
  rw[expr_vv_ok_def, expr_vv_sim_def] >>
  drule compile_struct_literal_inv >> strip_tac >> gvs[] >>
  drule struct_literal_lookup_types >> strip_tac >>
  drule struct_literal_evaluated_layout >> strip_tac >>
  `expr_sim_inv cenv cx env es` by gvs[expr_sim_pre_def] >>
  `!e st. MEM e (MAP SND fields) /\ expr_sim_inv cenv cx env st ==>
    expr_sim_pre cenv cx env e st` by metis_tac[expr_sim_pre_struct_field] >>
  `EVERY (expr_ok cenv) (MAP SND fields)` by
    (irule expr_sim_below_struct_fields >> simp[expr_size_def] >>
     qexistsl [`ann`, `nsid`] >> simp[]) >>
  Cases_on `eval_exprs cx (MAP SND fields) es` >>
  rename1 `eval_exprs cx (MAP SND fields) es = (rr,est)` >>
  drule aggregate_eval_struct >>
  disch_then (qspecl_then [`nsid`,`ann`] assume_tac) >> gvs[] >>
  `ci_mono sa sm` by metis_tac[ci_mono_compile_alloc_buffer, pairTheory.SND] >>
  `ci_mono sm sb` by
    metis_tac[ci_mono_compile_struct_lit_cfn, compile_expr_ci_mono, pairTheory.SND] >>
  `cs_extends sa sm /\ cs_extends sm sb` by gvs[ci_mono_def] >>
  drule_all fn_has_code_split >> strip_tac >>
  `SUM (MAP (SND o SND)
    (get_struct_fields cenv.ce_struct_fields (nsid_to_string nsid))) <
    dimword (:256)` by
    (gvs[expr_sim_pre_def, alloc_limits_expr_def, type_memory_bytes_def] >>
     simp[wordsTheory.dimword_def] >> decide_tac) >>
  qmatch_goalsub_abbrev_tac `expr_exit result` >>
  drule_all buffer_alloc_frag >>
  disch_then (qspecl_then [`s0`,`es`,`cx`,`ctx`,`expr_exit result`] strip_assume_tac) >>
  qpat_x_assum `frag_exec _ sa sm _ _ _` (mp_tac o MATCH_MP frag_exec_then) >>
  disch_then irule >> simp[] >> rpt strip_tac >>
  qpat_x_assum `expr_sim_below _ _` kall_tac >>
  qpat_x_assum `compile_expr _ _ _ _ = _` kall_tac >>
  qmatch_asmsub_abbrev_tac `compile_alloc_buffer sz sa` >>
  gvs[] >>
  drule_at (Pat `compile_struct_lit _ _ _ _ _ _ _ = _`) aggregate_struct_fields_sim >>
  simp[] >> disch_then drule >>
  simp[] >> disch_then drule >>
  disch_then (drule_at (Pat `lookup_var _ _ = _`)) >>
  disch_then (drule_at (Pat `MEM _ (fn_insts _)`)) >>
  simp[] >>
  disch_then (qspec_then `ctx` strip_assume_tac) >> gvs[] >>
  drule frag_exec_weaken >> disch_then irule >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> gvs[Abbr `result`]) >>
  rpt strip_tac >> gvs[Abbr `result`] >>
  qpat_x_assum `frag_exec _ _ _ _ _ _` kall_tac >>
  `ann = StructT nsid` by
    gvs[expr_sim_pre_def, vyperTypeSystemTheory.well_typed_expr_def] >>
  gvs[] >>
  `val_wf (StructTV (ZIP (MAP FST fields,tvs)))
    (StructV (ZIP (MAP FST fields,vs)))` by
    (irule aggregate_materialised_child_wf >>
     simp[expr_type_def, vyperStateTheory.materialise_def,
       vyperStateTheory.return_def] >>
     goal_assum (drule_at Any) >>
     simp[expr_type_def, vyperStateTheory.materialise_def,
       vyperStateTheory.return_def] >> metis_tac[]) >>
  `val_footprint (StructTV (ZIP (MAP FST fields,tvs)))
     (StructV (ZIP (MAP FST fields,vs))) <= type_memory_size_list tvs` by
    (drule val_footprint_le >> simp[type_memory_size_def] >>
     `LENGTH (MAP FST fields) = LENGTH tvs` by
       (drule vyperTypeABITheory.OPT_MMAP_LENGTH >> simp[]) >>
     simp[struct_layout_size_zip]) >>
  irule buffer_loop_memory_vv_post >>
  simp[expr_type_def, is_word_type_def, contextTheory.mk_ptr_def, contextTheory.base_ptr_def,
    eval_operand_def, val_in_memory_def] >>
  qexistsl [`b`,`sm`,`type_memory_size_list tvs`,`t`] >>
  simp[wordsTheory.dimword_def] >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem compile_make_array_sim:
  !cenv ann topt bnd args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (Builtin ann (MakeArray topt bnd) args)
Proof
  rpt gen_tac >> Cases_on `topt`
  >- suspend "tuple" >> suspend "array"
QED

Resume compile_make_array_sim[tuple]:
  rw[expr_vv_ok_def, expr_vv_sim_def] >>
  drule compile_tuple_literal_inv >> strip_tac >> gvs[] >>
  drule make_tuple_evaluated_layout >> strip_tac >> gvs[] >>
  `expr_sim_inv cenv cx env es` by gvs[expr_sim_pre_def] >>
  `!e st. MEM e args /\ expr_sim_inv cenv cx env st ==>
    expr_sim_pre cenv cx env e st` by metis_tac[expr_sim_pre_builtin_arg] >>
  `EVERY (expr_ok cenv) args` by metis_tac[expr_sim_below_args] >>
  `compatible_bound bnd (LENGTH args)` by
    gvs[expr_sim_pre_def, vyperTypeSystemTheory.well_typed_expr_def,
      vyperTypeSystemTheory.well_typed_builtin_app_def] >>
  Cases_on `eval_exprs cx args es` >>
  rename1 `eval_exprs cx args es = (rr,est)` >>
  drule_all aggregate_eval_make_tuple >>
  disch_then (qspec_then `TupleT (MAP expr_type args)` assume_tac) >> gvs[] >>
  `ci_mono sa sm` by metis_tac[ci_mono_compile_alloc_buffer, pairTheory.SND] >>
  `ci_mono sm sb` by
    metis_tac[ci_mono_compile_make_tuple_cfn, compile_expr_ci_mono, pairTheory.SND] >>
  `cs_extends sa sm /\ cs_extends sm sb` by gvs[ci_mono_def] >>
  drule_all fn_has_code_split >> strip_tac >>
  `SUM (MAP (type_memory_bytes cenv o expr_type) args) < dimword (:256)` by
    (gvs[expr_sim_pre_def, alloc_limits_expr_def] >>
     simp[wordsTheory.dimword_def] >> decide_tac) >>
  qmatch_goalsub_abbrev_tac `expr_exit result` >>
  `type_memory_size_list tvs < dimword (:256)` by metis_tac[] >>
  drule_all buffer_alloc_frag >>
  disch_then (qspecl_then [`s0`,`es`,`cx`,`ctx`,`expr_exit result`] strip_assume_tac) >>
  qpat_x_assum `frag_exec _ sa sm _ _ _` (mp_tac o MATCH_MP frag_exec_then) >>
  disch_then irule >> simp[] >> rpt strip_tac >>
  qpat_x_assum `expr_sim_below _ _` kall_tac >>
  qpat_x_assum `compile_expr _ _ _ _ = _` kall_tac >>
  gvs[] >>
  drule_at (Pat `compile_make_tuple _ _ _ _ _ _ = _`) aggregate_make_tuple_sim >>
  disch_then drule >> disch_then drule >>
  disch_then (drule_at (Pat `lookup_var _ _ = _`)) >>
  disch_then (drule_at (Pat `MEM _ (fn_insts _)`)) >> simp[] >>
  disch_then (qspecl_then [`env`,`ctx`] mp_tac) >> simp[] >> strip_tac >> gvs[] >>
  drule frag_exec_weaken >> disch_then irule >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> gvs[Abbr `result`]) >>
  rpt strip_tac >> gvs[Abbr `result`] >>
  qpat_x_assum `frag_exec _ _ _ _ _ _` kall_tac >>
  `val_wf (TupleTV tvs) (ArrayV (TupleV vs))` by
    (irule aggregate_materialised_child_wf >>
     simp[expr_type_def, vyperStateTheory.materialise_def,
       vyperStateTheory.return_def] >>
     goal_assum (drule_at Any) >>
     simp[expr_type_def, vyperStateTheory.materialise_def,
       vyperStateTheory.return_def] >> metis_tac[]) >>
  `val_footprint (TupleTV tvs) (ArrayV (TupleV vs)) <= type_memory_size_list tvs` by
    (drule val_footprint_le >> simp[type_memory_size_def]) >>
  irule (buffer_loop_memory_vv_post |> Q.INST
    [`e` |-> `Builtin (TupleT (MAP expr_type args)) (MakeArray NONE bnd) args`]
    |> SIMP_RULE (srw_ss()) [expr_type_def]) >>
  simp[expr_type_def, is_word_type_def, contextTheory.mk_ptr_def, contextTheory.base_ptr_def,
    eval_operand_def, val_in_memory_def] >>
  qexistsl [`b`,`sm`,`type_memory_size_list tvs`,`t`] >>
  simp[wordsTheory.dimword_def] >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

Resume compile_make_array_sim[array]:
  rw[expr_vv_ok_def, expr_vv_sim_def] >>
  drule compile_array_literal_inv >> strip_tac >> gvs[] >>
  drule make_array_evaluated_layout >> strip_tac >> gvs[] >>
  `expr_sim_inv cenv cx env es` by gvs[expr_sim_pre_def] >>
  `!e st. MEM e args /\ expr_sim_inv cenv cx env st ==>
    expr_sim_pre cenv cx env e st` by metis_tac[expr_sim_pre_builtin_arg] >>
  `EVERY (expr_ok cenv) args` by metis_tac[expr_sim_below_args] >>
  `compatible_bound bnd (LENGTH args)` by
    gvs[expr_sim_pre_def, vyperTypeSystemTheory.well_typed_expr_def,
      vyperTypeSystemTheory.well_typed_builtin_app_def] >>
  Cases_on `eval_exprs cx args es` >>
  rename1 `eval_exprs cx args es = (rr,est)` >>
  `eval_expr cx (Builtin (ArrayT x bnd) (MakeArray (SOME x) bnd) args) es =
    ((case rr of INL vs => INL (Value (ArrayV (make_array_value tv bnd vs)))
      | INR exc => INR exc),est)` by
    (irule aggregate_eval_make_array >> simp[]) >> gvs[] >>
  `ci_mono sa sm` by metis_tac[ci_mono_compile_alloc_buffer, pairTheory.SND] >>
  `ci_mono sm sb` by
    metis_tac[ci_mono_compile_make_array_cfn, compile_expr_ci_mono, pairTheory.SND] >>
  `cs_extends sa sm /\ cs_extends sm sb` by gvs[ci_mono_def] >>
  drule_all fn_has_code_split >> strip_tac >>
  `type_memory_bytes cenv (ArrayT x bnd) < dimword (:256)` by
    (gvs[expr_sim_pre_def, alloc_limits_expr_def] >>
     simp[wordsTheory.dimword_def] >> decide_tac) >>
  qmatch_goalsub_abbrev_tac `expr_exit result` >>
  drule_all buffer_alloc_frag >>
  disch_then (qspecl_then [`s0`,`es`,`cx`,`ctx`,`expr_exit result`] strip_assume_tac) >>
  qpat_x_assum `frag_exec _ sa sm _ _ _` (mp_tac o MATCH_MP frag_exec_then) >>
  disch_then irule >> simp[] >> rpt strip_tac >>
  qpat_x_assum `expr_sim_below _ _` kall_tac >>
  qpat_x_assum `compile_expr _ _ _ _ = _` kall_tac >>
  gvs[] >>
  drule_at (Pat `compile_make_array _ _ _ _ _ _ _ _ = _`) aggregate_make_array_sim >>
  disch_then (drule_at (Pat `eval_exprs _ _ _ = _`)) >>
  disch_then (drule_at (Pat `lookup_var _ _ = _`)) >>
  disch_then (drule_at (Pat `MEM _ (fn_insts _)`)) >>
  simp[wordsTheory.dimword_def] >>
  disch_then (qspecl_then [`env`,`ctx`] mp_tac) >> simp[] >>
  strip_tac >> gvs[] >>
  drule frag_exec_weaken >> disch_then irule >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> gvs[Abbr `result`]) >>
  rpt strip_tac >> gvs[Abbr `result`] >>
  qpat_x_assum `frag_exec _ _ _ _ _ _` kall_tac >>
  `val_wf (ArrayTV tv bnd) (ArrayV (make_array_value tv bnd vs))` by
    (irule aggregate_materialised_child_wf >>
     simp[expr_type_def, vyperStateTheory.materialise_def,
       vyperStateTheory.return_def] >>
     goal_assum (drule_at Any) >>
     simp[expr_type_def, vyperStateTheory.materialise_def,
       vyperStateTheory.return_def] >> metis_tac[]) >>
  `val_footprint (ArrayTV tv bnd) (ArrayV (make_array_value tv bnd vs)) <=
    type_memory_bytes cenv (ArrayT x bnd)` by
    (drule val_footprint_le >>
     `type_memory_bytes cenv (ArrayT x bnd) = type_memory_size (ArrayTV tv bnd)` by
       metis_tac[expr_sim_inv_memory_size] >> simp[]) >>
  irule (buffer_loop_memory_vv_post |> Q.INST
    [`e` |-> `Builtin (ArrayT x bnd) (MakeArray (SOME x) bnd) args`]
    |> SIMP_RULE (srw_ss()) [expr_type_def]) >>
  simp[expr_type_def, is_word_type_def, contextTheory.mk_ptr_def,
    eval_operand_def] >>
  qexistsl [`b`,`sm`,`type_memory_bytes cenv (ArrayT x bnd)`,`t`] >>
  simp[wordsTheory.dimword_def] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[arithmeticTheory.ADD_COMM] >>
  `LENGTH vs = LENGTH args` by (drule eval_exprs_length >> simp[]) >>
  Cases_on `bnd`
  >- (gvs[vyperValueTheory.compatible_bound_def] >>
      irule exprSimAggregateEncodingTheory.fixed_array_from_dense >> simp[]) >>
  gvs[vyperValueTheory.make_array_value_def, val_in_memory_def]
QED

Finalise compile_make_array_sim

(* ===== empty(T) ===== *)

Theorem eval_expr_empty:
  !cx ann t args es res es'.
    eval_expr cx (TypeBuiltin ann Empty t args) es = (res, es') /\
    expr_res_ok res ==>
    es' = es /\ args = [] /\
    ?tv. evaluate_type (get_tenv cx) t = SOME tv /\
         res = INL (Value (default_value tv))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, lift_sum_def,
       type_builtin_args_length_ok_def] >>
  Cases_on `args` >> simp[raise_def] >>
  simp[Once evaluate_def, return_def, evaluate_type_builtin_def] >>
  Cases_on `evaluate_type (get_tenv cx) t` >>
  simp[return_def, raise_def] >> rw[] >> gvs[expr_res_ok_def]
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

(* empty(T) of a word type: the literal 0, no code. *)
Theorem compile_empty_word_sim:
  !cenv ann t args.
    is_word_type t ==> expr_sim_ok cenv (TypeBuiltin ann Empty t args)
Proof
  rw[expr_sim_ok_def, expr_sim_def] >>
  drule_all eval_expr_empty >> strip_tac >> gvs[] >>
  `ann = t` by
    gvs[expr_sim_pre_def, well_typed_expr_def, type_builtin_result_ok_def] >>
  gvs[lower_value_def, compile_expr_type_builtin_dispatch, comp_bind_def] >>
  gvs[Once compile_expr_def, unwrap_value_def, comp_return_def] >>
  irule frag_exec_refl >>
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
Theorem compile_empty_memory_sim:
  !cenv ann t args.
    ~is_word_type t ==> expr_vv_ok cenv (TypeBuiltin ann Empty t args)
Proof
  rw[expr_vv_ok_def, expr_vv_sim_def] >>
  `expr_res_ok res` by
    (gvs[expr_vv_res_ok_def] >> drule eval_expr_type_builtin_value >>
     strip_tac >> gvs[expr_res_ok_def]) >>
  drule_all eval_expr_empty >> strip_tac >> gvs[] >>
  `ann = t` by
    gvs[expr_sim_pre_def, well_typed_expr_def, type_builtin_result_ok_def] >>
  gvs[compile_expr_type_builtin_dispatch, Once compile_expr_def,
      comp_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >>
  irule compile_builtin_empty_complex_frag >>
  reverse conj_tac >- (goal_assum (drule_at Any)) >>
  rpt strip_tac >> gvs[] >>
  `expr_sim_inv cenv cx env es` by gvs[expr_sim_pre_def] >>
  `type_memory_bytes cenv ann < dimword (:256)` by
    (gvs[expr_sim_pre_def, alloc_limits_expr_def] >>
     simp[wordsTheory.dimword_def] >> decide_tac) >>
  drule_all empty_type_buffer_size >> strip_tac >>
  drule_all compile_builtin_empty_complex_run >> strip_tac >>
  goal_assum (drule_at Any) >>
  drule_all empty_type_default_memory >> strip_tac >>
  irule (SRULE [vyperASTTheory.expr_type_def]
    (Q.INST [`e` |-> `TypeBuiltin ann Empty ann []`,
             `p` |-> `mk_ptr buf LocMemory`] (SPEC_ALL buffer_memory_vv_post))) >>
  goal_assum (drule_at Any) >>
  simp[contextTheory.mk_ptr_def, valueEncodingProofsTheory.val_wf_default_value_proof] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!aid b len. _ ==> regions_disjoint _ _ b len` drule >>
      simp[compileEnvTheory.regions_disjoint_def] >> strip_tac >>
      first_x_assum irule >> decide_tac) >>
  drule_all expr_sim_inv_memory_size >> strip_tac >>
  simp[val_footprint_le, valueEncodingProofsTheory.val_wf_default_value_proof]
QED

Theorem compile_empty_sim:
  !cenv ann t args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (TypeBuiltin ann Empty t args)
Proof
  rpt strip_tac >> Cases_on `is_word_type t`
  >- metis_tac[compile_empty_word_case_sim, expr_ok_def] >>
  simp[compile_empty_memory_sim]
QED

(* ===== max_value, min_value, epsilon ===== *)

Theorem eval_expr_bound_builtin:
  !cx ann tb t args es res es'.
    eval_expr cx (TypeBuiltin ann tb t args) es = (res, es') /\
    expr_res_ok res /\ MEM tb [MaxValue; MinValue; Epsilon] ==>
    es' = es /\ args = [] /\
    ?v. res = INL (Value v) /\ evaluate_type_builtin cx tb t [] [] = INL v
Proof
  rpt gen_tac >> strip_tac >>
  `!n. type_builtin_args_length_ok tb n <=> n = 0` by
    (Cases_on `tb` >> gvs[type_builtin_args_length_ok_def]) >>
  `!y. evaluate_type_builtin cx tb t [] [] = INR y ==> ?m. y = TypeError m` by
    (Cases_on `tb` >> gvs[evaluate_type_builtin_def, AllCaseEqs()] >>
     Cases_on `t` >> gvs[evaluate_max_value_def, evaluate_min_value_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     gvs[evaluate_max_value_def, evaluate_min_value_def, AllCaseEqs()]) >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, lift_sum_def] >>
  Cases_on `args` >> simp[raise_def] >>
  simp[Once evaluate_def, return_def] >>
  Cases_on `evaluate_type_builtin cx tb t [] []` >>
  simp[return_def, raise_def] >> rw[] >> gvs[expr_res_ok_def]
QED

(* max_value, min_value and epsilon of a numeric type: a Lit of the bound,
   no code. *)
Theorem compile_bound_builtin_word_sim:
  !cenv ann tb t args.
    MEM tb [MaxValue; MinValue; Epsilon] ==>
    expr_sim_ok cenv (TypeBuiltin ann tb t args)
Proof
  rw[expr_sim_ok_def, expr_sim_def] >>
  drule eval_expr_bound_builtin >> disch_then drule >> simp[] >>
  strip_tac >> gvs[] >>
  `ann = t /\ is_numeric_type t` by
    gvs[expr_sim_pre_def, well_typed_expr_def, type_builtin_result_ok_def,
        well_typed_type_builtin_args_def] >>
  `(?n. t = BaseT (UintT n)) \/ (?n. t = BaseT (IntT n)) \/
   t = BaseT DecimalT` by
    (Cases_on `t` >> gvs[] >> rename1 `BaseT bt` >> Cases_on `bt` >> gvs[]) >>
  gvs[] >>
  gvs[evaluate_type_builtin_def, evaluate_max_value_def,
      evaluate_min_value_def, AllCaseEqs()] >>
  gvs[lower_value_def, compile_expr_type_builtin_dispatch, comp_bind_def] >>
  gvs[Once compile_expr_def, unwrap_value_def, comp_return_def,
      type_bounds_def, type_bits_def, is_signed_type_def] >>
  irule frag_exec_refl >>
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
   decimal, address, bytesM, bytestrings and flags.  Cheated: for several
   of them the checker, the lowering and the semantics disagree (#548). *)
Theorem compile_convert_other_sim:
  !cenv ann t args.
    expr_sim_below cenv (list_size expr_size args) /\
    ~(?e1. args = [e1] /\ int_convert_pair (expr_type e1) t) ==>
    expr_vv_ok cenv (TypeBuiltin ann Convert t args)
Proof
  cheat
QED

Theorem compile_convert_sim:
  !cenv ann t args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (TypeBuiltin ann Convert t args)
Proof
  rpt strip_tac >>
  Cases_on `?e1. args = [e1] /\ int_convert_pair (expr_type e1) t`
  >- (gvs[] >> irule compile_convert_word_sim >> simp[]) >>
  irule compile_convert_other_sim >> metis_tac[]
QED

Theorem compile_abi_encode_sim:
  !cenv ann ensure mid t args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (TypeBuiltin ann (AbiEncode ensure mid) t args)
Proof
  cheat
QED

Theorem compile_abi_decode_sim:
  !cenv ann unwrap t args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (TypeBuiltin ann (AbiDecode unwrap) t args)
Proof
  cheat
QED

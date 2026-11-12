(*
 * Expression simulation: tuple subscripts (#636, Places row 1)
 *
 * A tuple's index is an integer literal (subscript_type_ok), so
 * compile_subscript emits no code for it: it lowers the base to its
 * value_vv, a pointer, and adds the element's offset, the sum of the
 * preceding elements' sizes in bytes (memory) or slots (storage and
 * transient storage), as compile_attribute does for a field.  The source
 * selects the element of the base's result (select_result), whose read is
 * the element of the tuple read at the base.
 *
 * TOP-LEVEL:
 *   tuple_offset              — the offset compile_subscript adds
 *   popped_at_elem            — the base's result is a local's place memory
 *                               no longer holds, with a popped snapshot at
 *                               the element itself
 *   tuple_popped_clash        — popped_at_elem of the evaluated base
 *   tuple_popped_clash_unreachable — never under expr_body_pre
 *   select_tuple_read         — the source's selection reads the element
 *   compile_subscript_tuple_sim — expr_vv_case of a tuple subscript from
 *                               its base's
 *
 * Helpers: values_have_types_el, tuple_val_wf_el,
 *   sum_take_el_le, compile_expr_tuple_subscript, map_elem_size_in_location,
 *   tuple_offset_memory, tuple_offset_code, tuple_offset_slots,
 *   tuple_in_memory_elem, decode_tuple_elem, read_storage_slot_tuple_elem,
 *   decode_tuple_length, read_storage_slot_tuple_length,
 *   read_storage_slot_array_not_tuple, evaluate_subscripts_snoc_tuple,
 *   read_popped_snoc_tuple, read_memory_path_snoc_tuple,
 *   select_tuple_read_immutable, evaluate_tuple_type, tuple_pre_base,
 *   eval_expr_tuple_subscript, base_vv_holds_loc, base_vv_at_mem,
 *   tuple_elem_ptr, tuple_vv_at_elem, sub_layout_tuple_elem,
 *   immutable_holds_tuple_elem, tuple_slots_in_range_el,
 *   tuple_elem_slots_in_range, tuple_prefix_el_bound,
 *   storage_range_agree_tuple_elem, tuple_vv_holds_elem, tuple_base_read,
 *   tuple_vv_post, lookup_scopes_popped_keys_indexed,
 *   tuple_memory_no_snapshot
 *
 * A base in code (an immutable, LocCode) points into an immutable's data:
 * immutable_holds places the base's value inside the immutable's layout
 * (sub_layout), and the element sits inside the base's at its byte offset,
 * as for attributes (exprSimAttribute).
 *
 * A popped snapshot recorded at the element itself (tuple_popped_clash)
 * would be read instead of the element of the base's snapshot.  It never
 * is: expr_sim_inv's popped_keys_indexed keys every snapshot at an index
 * into a dynamic array, and the element's path indexes a tuple
 * (tuple_popped_clash_unreachable).
 *)

Theory exprSimTuple
Ancestors
  exprSimAttributeProps exprSimFieldLayout
  exprSimSource
  exprSimProps
  exprSimHypsDefs
  exprSimDefs
  loweringPosts
  list rich_list finite_map pair
  fragExec  exprSimHyps exprSimUnwrap exprSimLen exprSimLeaves
  exprSimAggregateLayout exprSimAttributeFields exprSimAttribute
  placeTypingProps
  exprLowering exprLoweringProps compileEnv loweringStateRelDefs context
  valueEncoding valueEncodingDefs vyperAST vyperInterpreter vyperState vyperStorage vyperValue
  vyperValueOperation vyperTyping vyperTypeSystem vyperTypeExprSoundness
  vyperPlaceResultTyping valueEncodingProofs
  venomState venomInst
Libs
  pairLib

open gasContextTheory gasOutcomeTheory gasSummaryTheory gasSummaryComposeTheory
     gasExemptCertTheory fragGasModeTheory fragGasPathTheory;

(* ===== Lists ===== *)

Theorem values_have_types_el[local]:
  !tvs vs k.
    values_have_types tvs vs /\ k < LENGTH tvs ==>
    LENGTH vs = LENGTH tvs /\ value_has_type (EL k tvs) (EL k vs)
Proof
  Induct >> Cases_on `vs` >> simp[value_has_type_def] >>
  rpt gen_tac >> strip_tac >> imp_res_tac values_have_types_length >>
  Cases_on `k` >> gvs[]
QED

Theorem tuple_val_wf_el[local]:
  !vs tvs k.
    tuple_val_wf vs tvs /\ LENGTH vs = LENGTH tvs /\ k < LENGTH vs ==>
    val_wf (EL k tvs) (EL k vs)
Proof
  Induct >> Cases_on `tvs` >> simp[val_wf_def] >>
  rpt gen_tac >> strip_tac >> Cases_on `k` >> gvs[]
QED

Theorem sum_take_el_le[local]:
  !l k. k < LENGTH l ==> SUM (TAKE k l) + EL k l <= SUM l
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on `k` >> simp[] >>
  strip_tac >> first_x_assum drule >> simp[]
QED

(* ===== The lowering ===== *)

(* The offset compile_subscript adds to the base's pointer for element k
   of a tuple with element types tys: slots in storage and transient
   storage, bytes elsewhere. *)
Definition tuple_offset_def:
  tuple_offset cenv tys loc k =
    SUM (TAKE k (MAP (elem_size_in_location cenv loc) tys))
End

Theorem compile_expr_tuple_subscript[local]:
  !cenv ty ann obj idx tys st vv st'.
    compile_expr cenv ty (Subscript ann obj idx) st = (vv, st') /\
    place_type cenv obj = ValPT (TupleT tys) ==>
    ?bvv st1 p.
      compile_expr cenv ty obj st = (bvv, st1) /\
      emit_op ADD [vv_operand bvv;
                   Lit (n2w (tuple_offset cenv tys (vv_loc bvv)
                               (literal_int_index idx)))] st1 = (p, st') /\
      vv = LocatedValue ann (mk_ptr p (vv_loc bvv))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_expr _ _ (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_def,
       compile_subscript_def, compile_tuple_subscript_def, comp_bind_def,
       comp_return_def, vyperASTTheory.expr_size_def,
       vyperASTTheory.expr_type_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  gvs[comp_return_def, vv_loc_def, tuple_offset_def]
QED

Theorem map_elem_size_in_location[local]:
  !tys tvs cenv cx env es.
    expr_sim_inv cenv cx env es /\
    OPT_MMAP (evaluate_type (get_tenv cx)) tys = SOME tvs ==>
    MAP (elem_size_in_location cenv LocMemory) tys =
      MAP type_memory_size tvs /\
    MAP (elem_size_in_location cenv LocCode) tys =
      MAP type_memory_size tvs /\
    MAP (elem_size_in_location cenv LocStorage) tys =
      MAP type_slot_size tvs /\
    MAP (elem_size_in_location cenv LocTransient) tys =
      MAP type_slot_size tvs
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `evaluate_type (get_tenv cx) h` >> gvs[] >>
  Cases_on `OPT_MMAP (evaluate_type (get_tenv cx)) tys` >> gvs[] >>
  rename1 `evaluate_type _ h = SOME htv` >>
  `type_memory_bytes cenv h = type_memory_size htv` by
    (irule expr_sim_inv_memory_size >> metis_tac[]) >>
  first_x_assum drule_all >>
  simp[elem_size_in_location_def, is_slot_addressed_def,
       slot_count_of_memory_size]
QED

Theorem tuple_offset_memory[local]:
  !cenv cx env es tys tvs k.
    expr_sim_inv cenv cx env es /\
    OPT_MMAP (evaluate_type (get_tenv cx)) tys = SOME tvs ==>
    tuple_offset cenv tys LocMemory k = SUM (TAKE k (MAP type_memory_size tvs))
Proof
  rpt strip_tac >> drule_all map_elem_size_in_location >>
  simp[tuple_offset_def]
QED

Theorem tuple_offset_code[local]:
  !cenv cx env es tys tvs k.
    expr_sim_inv cenv cx env es /\
    OPT_MMAP (evaluate_type (get_tenv cx)) tys = SOME tvs ==>
    tuple_offset cenv tys LocCode k = SUM (TAKE k (MAP type_memory_size tvs))
Proof
  rpt strip_tac >> drule_all map_elem_size_in_location >>
  simp[tuple_offset_def]
QED

Theorem tuple_offset_slots[local]:
  !cenv cx env es tys tvs k loc.
    expr_sim_inv cenv cx env es /\
    OPT_MMAP (evaluate_type (get_tenv cx)) tys = SOME tvs /\
    (loc = LocStorage \/ loc = LocTransient) ==>
    tuple_offset cenv tys loc k = tuple_prefix_slot_size k tvs
Proof
  rpt strip_tac >> drule_all map_elem_size_in_location >>
  simp[tuple_offset_def, tuple_prefix_slot_size_sum, MAP_TAKE]
QED

(* ===== A tuple's element ===== *)

Theorem tuple_in_memory_elem[local]:
  !vs tvs off mem k.
    tuple_in_memory vs tvs off mem /\ LENGTH vs = LENGTH tvs /\
    k < LENGTH vs ==>
    val_in_memory (EL k tvs) (EL k vs)
      (off + SUM (TAKE k (MAP type_memory_size tvs))) mem
Proof
  Induct >> rpt gen_tac >> Cases_on `tvs` >> simp[val_in_memory_def] >>
  strip_tac >> Cases_on `k` >> gvs[] >>
  rename1 `j < LENGTH tvs'` >>
  rename1 `tuple_in_memory _ _ (off + type_memory_size tv) _` >>
  first_x_assum (qspecl_then [`tvs'`, `off + type_memory_size tv`, `mem`, `j`]
                   mp_tac) >>
  simp[]
QED

Theorem decode_tuple_elem[local]:
  !tvs storage off vs k.
    decode_tuple storage off tvs = SOME vs /\ k < LENGTH tvs ==>
    k < LENGTH vs /\
    decode_value storage (off + tuple_prefix_slot_size k tvs) (EL k tvs) =
      SOME (EL k vs)
Proof
  Induct >> simp[] >> rpt gen_tac >>
  simp[Once decode_value_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  Cases_on `k` >> gvs[tuple_prefix_slot_size_def] >>
  first_x_assum drule_all >> rewrite_tac[arithmeticTheory.ADD_ASSOC]
QED

Theorem read_storage_slot_tuple_elem[local]:
  !cx tr slot tvs es v es1 k.
    read_storage_slot cx tr slot (TupleTV tvs) es = (INL v, es1) /\
    k < LENGTH tvs ==>
    ?vs. v = ArrayV (TupleV vs) /\ k < LENGTH vs /\
         read_storage_slot cx tr (slot + n2w (tuple_prefix_slot_size k tvs))
           (EL k tvs) es = (INL (EL k vs), es1)
Proof
  rpt gen_tac >> Cases_on `tr` >>
  simp[read_storage_slot_def, get_storage_backend_def,
       get_transient_storage_def, get_accounts_def, bind_def, return_def] >>
  qmatch_goalsub_abbrev_tac `decode_value stor` >>
  simp[Once decode_value_def] >>
  Cases_on `decode_tuple stor (w2n slot) tvs` >>
  simp[lift_option_def, raise_def, return_def] >>
  rpt strip_tac >> gvs[] >>
  drule_all decode_tuple_elem >> strip_tac >> simp[] >>
  `decode_value stor (w2n (slot + n2w (tuple_prefix_slot_size k tvs)))
     (EL k tvs) =
   decode_value stor (w2n slot + tuple_prefix_slot_size k tvs) (EL k tvs)` by
    (irule (cj 1 decode_value_n2w) >>
     rewrite_tac[GSYM wordsTheory.word_add_n2w, wordsTheory.n2w_w2n]) >>
  simp[lift_option_def, return_def]
QED

Theorem decode_tuple_length[local]:
  !tvs storage off vs.
    decode_tuple storage off tvs = SOME vs ==> LENGTH vs = LENGTH tvs
Proof
  Induct >> simp[] >> rpt gen_tac >>
  simp[Once decode_value_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem read_storage_slot_tuple_length[local]:
  !cx tr slot tvs es v es1.
    read_storage_slot cx tr slot (TupleTV tvs) es = (INL v, es1) ==>
    ?vs. v = ArrayV (TupleV vs) /\ LENGTH vs = LENGTH tvs
Proof
  rpt gen_tac >> Cases_on `tr` >>
  simp[read_storage_slot_def, get_storage_backend_def,
       get_transient_storage_def, get_accounts_def, bind_def, return_def] >>
  qmatch_goalsub_abbrev_tac `decode_value stor` >>
  simp[Once decode_value_def] >>
  Cases_on `decode_tuple stor (w2n slot) tvs` >>
  simp[lift_option_def, raise_def, return_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[decode_tuple_length]
QED

(* An array decoded from storage is a static or dynamic array, never a
   tuple. *)
Theorem read_storage_slot_array_not_tuple[local]:
  !cx tr slot etv bd es vs es1.
    read_storage_slot cx tr slot (ArrayTV etv bd) es <>
      (INL (ArrayV (TupleV vs)), es1)
Proof
  rpt gen_tac >> Cases_on `tr` >>
  simp[read_storage_slot_def, get_storage_backend_def,
       get_transient_storage_def, get_accounts_def, bind_def, return_def] >>
  qmatch_goalsub_abbrev_tac `decode_value stor` >>
  (namedCases_on `bd` ["n", "max"]
  >- (simp[Once decode_value_def] >>
      Cases_on `decode_static_array stor (w2n slot) etv n` >>
      simp[lift_option_def, raise_def, return_def]) >>
  simp[Once decode_value_def] >>
  Cases_on `w2n (read_slot stor (w2n slot)) <= max` >>
  simp[lift_option_def, raise_def, return_def] >>
  Cases_on `decode_dyn_array stor (w2n slot + 1) etv
              (MIN (w2n (read_slot stor (w2n slot))) max)` >>
  simp[lift_option_def, raise_def, return_def])
QED

(* ===== The source's selection ===== *)

Theorem evaluate_subscripts_snoc_tuple[local]:
  !path tv a vs k.
    evaluate_subscripts tv a path = INL (ArrayV (TupleV vs)) /\
    k < LENGTH vs ==>
    evaluate_subscripts tv a (path ++ [ValueSubscript (IntV (&k))]) =
      INL (EL k vs)
Proof
  Induct
  >- (rw[evaluate_subscripts_def] >>
      simp[evaluate_subscripts_def, array_index_def, oEL_THM]) >>
  Cases >> TRY (rename1 `ValueSubscript x` >> Cases_on `x`) >>
  rpt gen_tac >>
  TRY (rename1 `AttrSubscript fname :: _` >> Cases_on `a`) >>
  simp[evaluate_subscripts_def] >> strip_tac >>
  gvs[AllCaseEqs()] >> res_tac >> simp[]
QED

Theorem read_popped_snoc_tuple[local]:
  !hist tv path vs k.
    read_popped tv path hist = SOME (ArrayV (TupleV vs)) /\
    k < LENGTH vs /\
    (!v'. ~MEM (path ++ [ValueSubscript (IntV (&k))], v') hist) ==>
    read_popped tv (path ++ [ValueSubscript (IntV (&k))]) hist =
      SOME (EL k vs)
Proof
  Induct >> simp[read_popped_def] >> PairCases >> rpt gen_tac >>
  simp[read_popped_def] >> strip_tac >>
  Cases_on `IS_PREFIX path h0` >> gvs[]
  >- (`IS_PREFIX (path ++ [ValueSubscript (IntV (&k))]) h0` by
        metis_tac[IS_PREFIX_TRANS, IS_PREFIX_APPEND3] >>
      `LENGTH h0 <= LENGTH path` by metis_tac[IS_PREFIX_LENGTH] >>
      simp[DROP_APPEND1] >>
      Cases_on `subscripts_type tv h0` >> gvs[] >>
      rename1 `evaluate_subscripts ptv h1 (DROP _ path)` >>
      Cases_on `evaluate_subscripts ptv h1 (DROP (LENGTH h0) path)` >> gvs[]
      >- (drule_all evaluate_subscripts_snoc_tuple >> simp[]) >>
      drule exprSimPopNestedLocalPathTheory.evaluate_subscripts_append_err >> simp[]) >>
  `~IS_PREFIX (path ++ [ValueSubscript (IntV (&k))]) h0` by
    (strip_tac >> gvs[GSYM SNOC_APPEND, isPREFIX_SNOC_EQ] >> metis_tac[]) >>
  simp[]
QED

Theorem read_memory_path_snoc_tuple[local]:
  !entry path vs k.
    read_memory_path entry path = INL (ArrayV (TupleV vs)) /\
    k < LENGTH vs /\
    (!err v'. evaluate_subscripts entry.type entry.value path = INR err ==>
              ~MEM (path ++ [ValueSubscript (IntV (&k))], v') entry.popped) ==>
    read_memory_path entry (path ++ [ValueSubscript (IntV (&k))]) =
      INL (EL k vs)
Proof
  rpt gen_tac >> simp[read_memory_path_def] >>
  Cases_on `evaluate_subscripts entry.type entry.value path` >> simp[] >>
  strip_tac >> gvs[]
  >- (drule_all evaluate_subscripts_snoc_tuple >> simp[]) >>
  gvs[AllCaseEqs()] >>
  drule exprSimPopNestedLocalPathTheory.evaluate_subscripts_append_err >> simp[] >> strip_tac >>
  drule_all read_popped_snoc_tuple >> simp[]
QED

(* The base's result is a local's place that memory no longer holds, so
   read_memory_path reads the element from the popped history, and that
   history has a snapshot exactly at the element: read_popped may read the
   snapshot there. *)
Definition popped_at_elem_def:
  popped_at_elem (PlaceR (MemoryPlace x path)) (k:num) (es:evaluation_state) =
    (?entry err v'. lookup_scopes x es.scopes = SOME entry /\
                    evaluate_subscripts entry.type entry.value path = INR err /\
                    MEM (path ++ [ValueSubscript (IntV (&k))], v')
                      entry.popped) /\
  popped_at_elem _ _ _ = F
End

Theorem select_tuple_read_immutable[local]:
  !cx ty src x path k es vs res es1.
    read_result cx (PlaceR (ImmutablePlace src x path)) es =
      (INL (ArrayV (TupleV vs)), es) /\ k < LENGTH vs /\
    select_result cx ty (PlaceR (ImmutablePlace src x path))
      (ValueSubscript (IntV (&k))) es = (res, es1) /\
    (!m. res <> INR (Error (TypeError m))) ==>
    es1 = es /\
    ?tv'. res = INL tv' /\ read_result cx tv' es = (INL (EL k vs), es)
Proof
  rpt gen_tac >>
  simp[read_result_def, read_place_def, select_result_def,
       extend_place_def, place_type_value_def,
       extend_memory_place_def, bind_def, ignore_bind_def, return_def,
       lift_option_type_def, lift_sum_def] >>
  Cases_on `get_immutables cx src es` >> rename1 `(ir, ies)` >>
  `ies = es` by metis_tac[vyperStatePreservationTheory.get_immutables_state] >>
  Cases_on `ir` >> simp[raise_def] >>
  rename1 `FLOOKUP imms x` >>
  Cases_on `FLOOKUP imms x` >> simp[raise_def, return_def] >>
  rename1 `FLOOKUP imms x = SOME tva` >>
  Cases_on `evaluate_subscripts (FST tva) (SND tva) path` >>
  simp[raise_def, return_def] >>
  Cases_on `subscripts_type (FST tva) path` >> simp[raise_def, return_def] >>
  simp[evaluate_subscripts_def, array_index_def, oEL_THM, return_def] >>
  rpt strip_tac >> gvs[return_def] >>
  drule_all evaluate_subscripts_snoc_tuple >>
  simp[read_result_def, read_place_def, bind_def, return_def,
       lift_option_type_def, lift_sum_def]
QED

(* Selecting element k of a result whose read is a tuple with more than k
   elements: unless the selection raises a type error, it succeeds without
   changing the state, and its read is the element. *)
Theorem select_tuple_read:
  !cx ty tv k es vs res es1.
    read_result cx tv es = (INL (ArrayV (TupleV vs)), es) /\
    k < LENGTH vs /\
    select_result cx ty tv (ValueSubscript (IntV (&k))) es = (res, es1) /\
    ~popped_at_elem tv k es /\
    (!m. res <> INR (Error (TypeError m))) ==>
    es1 = es /\
    ?tv'. res = INL tv' /\ read_result cx tv' es = (INL (EL k vs), es)
Proof
  rpt gen_tac >> Cases_on `tv`
  >~ [`Value v`]
  >- (simp[read_result_def, select_result_def, return_def, bind_def,
           lift_option_type_def, lift_sum_def] >>
      strip_tac >> gvs[] >>
      Cases_on `evaluate_type (get_tenv cx) ty` >>
      gvs[raise_def, return_def, evaluate_subscripts_def, array_index_def,
          oEL_THM, read_result_def])
  >~ [`HashMapRef`] >- simp[read_result_def, raise_def] >>
  rename1 `PlaceR p` >> Cases_on `p`
  >~ [`StoragePlace tr slot ptv`]
  >- (simp[read_result_def, read_place_def, select_result_def,
           extend_place_def, bind_def, return_def] >>
      strip_tac >>
      Cases_on `ptv` >> gvs[extend_storage_place_def, raise_def]
      >~ [`ArrayTV`] >- metis_tac[read_storage_slot_array_not_tuple] >>
      rename1 `TupleTV tvs` >>
      drule read_storage_slot_tuple_length >> strip_tac >> gvs[] >>
      gvs[check_def, assert_def, ignore_bind_def, bind_def, return_def,
          raise_def, lift_option_type_def, oEL_THM] >>
      simp[read_result_def, read_place_def] >>
      drule_all read_storage_slot_tuple_elem >> simp[])
  >~ [`MemoryPlace x path`]
  >- (simp[read_result_def, read_place_def, select_result_def,
           extend_place_def, place_type_value_def, get_scopes_def,
           extend_memory_place_def, bind_def, ignore_bind_def, return_def,
           lift_option_type_def, lift_sum_def, popped_at_elem_def] >>
      Cases_on `lookup_scopes x es.scopes` >> simp[raise_def] >>
      rename1 `lookup_scopes x es.scopes = SOME entry` >>
      Cases_on `read_memory_path entry path` >> simp[raise_def, return_def] >>
      Cases_on `subscripts_type entry.type path` >>
      simp[raise_def, return_def] >>
      simp[evaluate_subscripts_def, array_index_def, oEL_THM, return_def] >>
      rpt strip_tac >> gvs[return_def] >>
      drule_all read_memory_path_snoc_tuple >>
      simp[read_result_def, read_place_def, get_scopes_def, bind_def,
           return_def, lift_option_type_def, lift_sum_def]) >>
  rename1 `ImmutablePlace src x path` >> strip_tac >>
  drule_all select_tuple_read_immutable >> simp[]
QED

(* ===== Typing ===== *)

Theorem evaluate_tuple_type[local]:
  !tenv tys tvt.
    evaluate_type tenv (TupleT tys) = SOME tvt ==>
    ?tvs. tvt = TupleTV tvs /\ OPT_MMAP (evaluate_type tenv) tys = SOME tvs
Proof
  rw[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  gvs[vyperValueTheory.evaluate_types_OPT_MMAP]
QED

(* A well-typed subscript of a tuple-typed base: the base's own
   precondition, and an in-range integer literal index whose element type
   is the annotation.  A place-typed base (the other branch of
   well_typed_expr) is an array or a mapping, never a tuple. *)
Theorem tuple_pre_base[local]:
  !cenv cx env ann obj idx es tys.
    expr_body_pre cenv cx env (Subscript ann obj idx) es /\
    expr_type obj = TupleT tys ==>
    expr_body_pre cenv cx env obj es /\
    int_calls_expr (Subscript ann obj idx) = int_calls_expr obj /\
    ?ity k. idx = Literal ity (IntL (&k)) /\ k < LENGTH tys /\
            EL k tys = ann
Proof
  rpt gen_tac >> strip_tac >>
  `well_typed_expr env obj /\ subscript_type_ok (TupleT tys) idx ann` by
    (qpat_x_assum `expr_body_pre _ _ _ _ _` mp_tac >>
     simp[expr_body_pre_def, Once well_typed_expr_def] >>
     rpt strip_tac >> gvs[] >>
     drule type_place_expr_vtype_annotation >>
     Cases_on `vt` >> TRY (rename1 `Type t` >> Cases_on `t`) >>
     gvs[subscript_vtype_def, vtype_annotation_ok_def]) >>
  `?ity k. idx = Literal ity (IntL (&k)) /\ k < LENGTH tys /\ EL k tys = ann` by
    (gvs[subscript_type_ok_def] >>
     Cases_on `idx` >> gvs[] >> rename1 `Literal _ l` >> Cases_on `l` >> gvs[] >>
     rename1 `IntL n` >>
     qexists_tac `Num n` >> simp[integerTheory.INT_OF_NUM]) >>
  gvs[expr_body_pre_def, well_typed_expr_def,
      vyperTypeCallGraphTheory.int_calls_expr_def, byte_widths_expr_def,
      allocLimitsTheory.alloc_limits_expr_def,
      supportedExprTraverseTheory.expr_has_evm_run_thm] >>
  rpt strip_tac >>
  TRY (qpat_x_assum `~supported_expr_exists _ (Subscript _ _ _)` mp_tac >>
       simp[supportedExprTraverseTheory.supported_expr_exists_def] >> NO_TAC) >>
  qpat_x_assum `!target. supported_expr_exists _ (Subscript _ _ _) ==> _`
    (qspec_then `target` irule) >>
  simp[supportedExprTraverseTheory.supported_expr_exists_def]
QED

Theorem eval_expr_tuple_subscript[local]:
  !cx ann obj ity k es.
    eval_expr cx (Subscript ann obj (Literal ity (IntL (&k)))) es =
    (do r <- eval_expr cx obj;
        select_result cx (expr_type obj) r (ValueSubscript (IntV (&k))) od)
      es
Proof
  rpt gen_tac >> simp[Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx obj es` >> rename1 `_ = (rr, es1)` >>
  Cases_on `rr` >> simp[] >>
  simp[Once evaluate_def, evaluate_literal_def, return_def, read_result_def]
QED

(* ===== The value_vv of the element ===== *)

(* What a base's value_vv of a non-word type says of the value it holds,
   by location. *)
Theorem base_vv_holds_loc[local]:
  !cenv cx t tv vv es s tvt w.
    vv_holds cenv cx t tv vv es s /\ ~is_word_type t /\
    evaluate_type (get_tenv cx) t = SOME tvt /\
    eval_operand (vv_operand vv) s = SOME w ==>
    ?v. read_result cx tv es = (INL v, es) /\
        (vv_loc vv = LocMemory ==> val_in_memory tvt v (w2n w) s.vs_memory) /\
        (vv_loc vv = LocStorage ==>
           read_storage_slot cx F w tvt es = (INL v, es) /\
           slots_in_range (get_storage cx es F) (w2n w) tvt /\
           storage_range_agree (get_storage cx es F) (contract_storage s) w tvt) /\
        (vv_loc vv = LocTransient ==>
           read_storage_slot cx T w tvt es = (INL v, es) /\
           slots_in_range (get_storage cx es T) (w2n w) tvt /\
           storage_range_agree (get_storage cx es T) (contract_transient s) w tvt) /\
        (vv_loc vv = LocCode ==> immutable_holds cenv cx t tv w es s) /\
        vv_loc vv <> LocCalldata
Proof
  rpt gen_tac >> Cases_on `vv` >>
  simp[vv_holds_def, vv_loc_def, vv_location_def, vv_operand_def,
       expr_val_rel_def] >>
  rpt strip_tac >> gvs[] >>
  rename1 `p.ptr_location` >> Cases_on `p.ptr_location` >>
  gvs[storage_holds_def] >> metis_tac[immutable_holds_read]
QED

Theorem base_vv_at_mem[local]:
  !cenv cx t sa sb es tv vv s v tvt w.
    vv_at cenv cx t sa sb es tv vv s /\ ~is_word_type t /\
    read_result cx tv es = (INL v, es) /\
    evaluate_type (get_tenv cx) t = SOME tvt /\
    (!bt. tvt <> BaseTV bt) /\
    vv_loc vv = LocMemory /\ eval_operand (vv_operand vv) s = SOME w ==>
    val_wf tvt v /\
    ((?aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
                 sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
                 b <= w2n w /\ w2n w + val_footprint tvt v <= b + sz /\
                 (!n lb lsz. local_region cenv es.scopes s n lb lsz ==>
                              b + sz <= lb \/ lb + lsz <= b)) \/
     (?n b sz. local_region cenv es.scopes s n b sz /\
               b <= w2n w /\ w2n w + val_footprint tvt v <= b + sz /\
               local_path_at cenv cx n (w2n w - b) tvt /\
               local_place_at cenv cx n (w2n w - b) tvt tv) \/
     val_footprint tvt v = 0)
Proof
  rpt gen_tac >> Cases_on `vv` >>
  simp[vv_at_def, vv_loc_def, vv_location_def, vv_operand_def,
       expr_val_at_def, local_val_at_def] >>
  rpt strip_tac >> gvs[] >>
  TRY (first_x_assum drule_all >> strip_tac >> gvs[]) >>
  gvs[local_place_at_def] >> metis_tac[]
QED

(* The element's pointer in memory: the element lies inside the base's
   bytes, so its address does not wrap, and the base sits where vv_at says. *)
Theorem tuple_elem_ptr[local]:
  !func cenv cx env es sa sn es1 tv bvv q w tys tvs vs k ctx.
    stmt_state_rel ctx func cenv cx es1 q /\ expr_sim_inv cenv cx env es /\
    vv_at cenv cx (TupleT tys) sa sn es1 tv bvv q /\
    read_result cx tv es1 = (INL (ArrayV (TupleV vs)), es1) /\
    eval_operand (vv_operand bvv) q = SOME w /\ vv_loc bvv = LocMemory /\
    OPT_MMAP (evaluate_type (get_tenv cx)) tys = SOME tvs /\
    evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
    k < LENGTH tvs ==>
    tuple_offset cenv tys LocMemory k = SUM (TAKE k (MAP type_memory_size tvs)) /\
    tuple_offset cenv tys LocMemory k + type_memory_size (EL k tvs) <=
      type_memory_size_list tvs /\
    w2n (w + n2w (tuple_offset cenv tys LocMemory k)) =
      w2n w + tuple_offset cenv tys LocMemory k /\
    tuple_val_wf vs tvs /\
    ((?aid b sz. FLOOKUP q.vs_allocas aid = SOME (b,sz) /\
                 sa.cs_next_id <= aid /\ aid < sn.cs_next_id /\
                 b <= w2n w /\ w2n w + type_memory_size_list tvs <= b + sz /\
                 (!n lb lsz. local_region cenv es1.scopes q n lb lsz ==>
                              b + sz <= lb \/ lb + lsz <= b)) \/
     (?n b sz. local_region cenv es1.scopes q n b sz /\
               b <= w2n w /\ w2n w + type_memory_size_list tvs <= b + sz /\
               local_path_at cenv cx n (w2n w - b) (TupleTV tvs) /\
               local_place_at cenv cx n (w2n w - b) (TupleTV tvs) tv) \/
     type_memory_size_list tvs = 0)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all tuple_offset_memory >> disch_then (qspec_then `k` assume_tac) >>
  qspecl_then [`cenv`, `cx`, `TupleT tys`, `sa`, `sn`, `es1`, `tv`, `bvv`,
               `q`, `ArrayV (TupleV vs)`, `TupleTV tvs`, `w`] mp_tac
    base_vv_at_mem >>
  impl_tac >- simp[is_word_type_def] >> strip_tac >>
  gvs[val_footprint_def, type_memory_size_def, val_wf_def] >>
  `SUM (TAKE k (MAP type_memory_size tvs)) + type_memory_size (EL k tvs) <=
   type_memory_size_list tvs` by
    (qspecl_then [`MAP type_memory_size tvs`, `k`] mp_tac sum_take_el_le >>
     simp[EL_MAP, GSYM type_memory_size_list_sum]) >>
  drule stmt_state_rel_region_lt >> strip_tac >>
  `w2n (w + n2w (SUM (TAKE k (MAP type_memory_size tvs)))) =
   w2n w + SUM (TAKE k (MAP type_memory_size tvs))` by
    (irule field_ptr_w2n >>
     qexistsl [`type_memory_size (EL k tvs)`, `type_memory_size_list tvs`] >>
     simp[] >> res_tac >> DECIDE_TAC) >>
  simp[] >> metis_tac[]
QED

(* The element's placement in memory, from the base's. *)
Theorem tuple_vv_at_elem[local]:
  !func cenv cx env es sa sn es1 tv bvv q w dst tys tvs vs k tv' t ctx.
    stmt_state_rel ctx func cenv cx es1 q /\ expr_sim_inv cenv cx env es /\
    vv_at cenv cx (TupleT tys) sa sn es1 tv bvv q /\
    read_result cx tv es1 = (INL (ArrayV (TupleV vs)), es1) /\
    read_result cx tv' es1 = (INL (EL k vs), es1) /\
    eval_operand (vv_operand bvv) q = SOME w /\
    eval_operand dst q =
      SOME (w + n2w (tuple_offset cenv tys (vv_loc bvv) k)) /\
    OPT_MMAP (evaluate_type (get_tenv cx)) tys = SOME tvs /\
    evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
    LENGTH vs = LENGTH tvs /\ k < LENGTH tvs /\
    (!id path'. tv' = PlaceR (MemoryPlace id path') <=>
       ?path. path' = path ++ [ValueSubscript (IntV &k)] /\ tv = PlaceR (MemoryPlace id path)) ==>
    vv_at cenv cx (EL k tys) sa sn es1 tv'
      (LocatedValue t (mk_ptr dst (vv_loc bvv))) q
Proof
  rpt gen_tac >> strip_tac >>
  simp[vv_at_def, mk_ptr_def] >> conj_tac
  >- (rpt strip_tac >>
      `?p0. tv = PlaceR (MemoryPlace id p0)` by metis_tac[] >>
      qpat_x_assum `vv_at _ _ (TupleT _) _ _ _ _ _ _` mp_tac >>
      Cases_on `bvv` >>
      gvs[vv_at_def, vv_loc_def, vv_location_def, is_word_type_def]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  `evaluate_type (get_tenv cx) (EL k tys) = SOME (EL k tvs)` by
    (drule opt_mmap_el >> disch_then (qspec_then `k` mp_tac) >>
     impl_tac >- (drule vyperTypeABITheory.OPT_MMAP_LENGTH >> simp[]) >>
     simp[]) >>
  gvs[] >>
  drule_all tuple_elem_ptr >> strip_tac >> gvs[] >>
  `val_wf (EL k tvs) (EL k vs)` by (irule tuple_val_wf_el >> simp[]) >>
  `val_footprint (EL k tvs) (EL k vs) <= type_memory_size (EL k tvs)` by
    simp[val_footprint_le] >>
  simp[] >>
  all_tac
  >~ [`FLOOKUP q.vs_allocas aid = SOME (b,sz)`]
  >- (disj1_tac >> qexistsl [`aid`, `b`, `sz`] >> simp[] >>
      first_assum ACCEPT_TAC)
  >~ [`local_region cenv es1.scopes q n b sz`]
  >- (disj2_tac >> disj1_tac >> qexistsl [`n`, `b`, `sz`] >> simp[] >>
      `mem_step_offset (TupleTV tvs) (ValueSubscript (IntV &k)) =
       SOME (SUM (TAKE k (MAP type_memory_size tvs)), EL k tvs)` by
        simp[mem_step_offset_def, type_memory_size_list_sum, MAP_TAKE] >>
      `local_place_at cenv cx n
         (w2n w - b + SUM (TAKE k (MAP type_memory_size tvs))) (EL k tvs) tv'` by
        (irule local_place_at_step >> metis_tac[]) >>
      drule_all local_path_at_step >>
      `w2n w - b + SUM (TAKE k (MAP type_memory_size tvs)) =
       w2n w + SUM (TAKE k (MAP type_memory_size tvs)) - b` by decide_tac >>
      gvs[local_path_at_val_at] >> decide_tac) >>
  disj2_tac >> disj2_tac >> decide_tac
QED

(* A tuple's element sits inside the tuple's layout at its offset. *)
Theorem sub_layout_tuple_elem[local]:
  !itv iv k tvs vs j.
    sub_layout itv iv k (TupleTV tvs) (ArrayV (TupleV vs)) /\
    LENGTH vs = LENGTH tvs /\ j < LENGTH vs ==>
    sub_layout itv iv (k + SUM (TAKE j (MAP type_memory_size tvs)))
      (EL j tvs) (EL j vs)
Proof
  rw[sub_layout_def]
  >- (qspecl_then [`MAP type_memory_size tvs`, `j`] mp_tac sum_take_el_le >>
      gvs[EL_MAP, type_memory_size_def, type_memory_size_list_sum]) >>
  first_x_assum drule >> simp[val_in_memory_def] >> strip_tac >>
  drule_all tuple_in_memory_elem >> rewrite_tac[arithmeticTheory.ADD_ASSOC]
QED

(* The element of a tuple an immutable's code pointer holds: the pointer
   plus the element's offset. *)
Theorem immutable_holds_tuple_elem[local]:
  !cenv cx tys tvs tv w es s vs j tv'.
    immutable_holds cenv cx (TupleT tys) tv w es s /\
    read_result cx tv es = (INL (ArrayV (TupleV vs)), es) /\
    evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
    evaluate_type (get_tenv cx) (EL j tys) = SOME (EL j tvs) /\
    j < LENGTH tvs /\ read_result cx tv' es = (INL (EL j vs), es) ==>
    immutable_holds cenv cx (EL j tys) tv'
      (w + n2w (SUM (TAKE j (MAP type_memory_size tvs)))) es s
Proof
  rpt strip_tac >>
  `value_has_type (TupleTV tvs) (ArrayV (TupleV vs))` by
    (fs[immutable_holds_def] >> gvs[]) >>
  gvs[value_has_type_def] >>
  `LENGTH vs = LENGTH tvs /\ value_has_type (EL j tvs) (EL j vs)` by
    metis_tac[values_have_types_el] >>
  `sub_layout (TupleTV tvs) (ArrayV (TupleV vs))
     (SUM (TAKE j (MAP type_memory_size tvs))) (EL j tvs) (EL j vs)` by
    (qspecl_then [`TupleTV tvs`, `ArrayV (TupleV vs)`, `0`, `tvs`, `vs`, `j`]
       mp_tac sub_layout_tuple_elem >>
     simp[sub_layout_def]) >>
  irule immutable_holds_sub >>
  qexistsl [`EL j tvs`, `EL j vs`, `TupleTV tvs`, `ArrayV (TupleV vs)`,
            `TupleT tys`, `tv`] >>
  simp[]
QED

(* ===== A tuple element's slots in storage ===== *)

Theorem tuple_slots_in_range_el[local]:
  !tvs k off storage.
    tuple_slots_in_range storage off tvs /\ k < LENGTH tvs ==>
    slots_in_range storage (off + tuple_prefix_slot_size k tvs) (EL k tvs)
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `tuple_slots_in_range _ _ _` mp_tac >>
  simp[Once vyperLookupStorageTheory.slots_in_range_def] >> strip_tac >>
  Cases_on `k` >> gvs[tuple_prefix_slot_size_def] >>
  first_x_assum drule_all >> rewrite_tac[arithmeticTheory.ADD_ASSOC]
QED

Theorem tuple_elem_slots_in_range[local]:
  !storage w tvs k.
    slots_in_range storage (w2n (w:bytes32)) (TupleTV tvs) /\
    k < LENGTH tvs ==>
    slots_in_range storage
      (w2n (w + n2w (tuple_prefix_slot_size k tvs))) (EL k tvs)
Proof
  rpt strip_tac >>
  `slots_in_range storage (w2n w + tuple_prefix_slot_size k tvs) (EL k tvs)`
    by (irule tuple_slots_in_range_el >>
        gvs[Once vyperLookupStorageTheory.slots_in_range_def]) >>
  `slots_in_range storage (w2n w + tuple_prefix_slot_size k tvs) (EL k tvs) =
   slots_in_range storage (w2n (w + n2w (tuple_prefix_slot_size k tvs)))
     (EL k tvs)` by
    (irule (CONJUNCT1 vyperLookupStorageTheory.slots_in_range_offset_cong) >>
     `w + n2w (tuple_prefix_slot_size k tvs) =
      n2w (w2n w + tuple_prefix_slot_size k tvs)` by
       simp[GSYM wordsTheory.word_add_n2w] >>
     simp[wordsTheory.w2n_n2w]) >>
  gvs[]
QED

Theorem tuple_prefix_el_bound[local]:
  !tvs k.
    k < LENGTH tvs ==>
    tuple_prefix_slot_size k tvs + type_slot_size (EL k tvs) <=
    type_slot_size (TupleTV tvs)
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on `k` >>
  simp[tuple_prefix_slot_size_def, vyperValueTheory.type_slot_size_def] >>
  strip_tac >> first_x_assum drule >>
  simp[vyperValueTheory.type_slot_size_def]
QED


(* A tuple element of a value whose slots agree has its slots agree. *)
Theorem storage_range_agree_tuple_elem[local]:
  !st st' w tvs i.
    storage_range_agree st st' w (TupleTV tvs) /\ i < LENGTH tvs ==>
    storage_range_agree st st' (w + n2w (tuple_prefix_slot_size i tvs))
      (EL i tvs)
Proof
  rpt gen_tac >> strip_tac >>
  drule tuple_prefix_el_bound >> strip_tac >>
  Cases_on `type_slot_size (EL i tvs) = 0`
  >- (`w2n (w + n2w (tuple_prefix_slot_size i tvs)) <= dimword (:256)` by
        (irule arithmeticTheory.LESS_IMP_LESS_OR_EQ >>
         simp[wordsTheory.w2n_lt]) >>
      simp[accountsRelPropsTheory.storage_range_agree_def] >> rpt strip_tac >>
      `w2n (w + n2w (tuple_prefix_slot_size i tvs)) < w2n (w + n2w (tuple_prefix_slot_size i tvs))` by
        (irule arithmeticTheory.LESS_EQ_LESS_TRANS >>
         qexists_tac `w2n k` >> simp[]) >>
      gvs[]) >>
  gvs[accountsRelPropsTheory.storage_range_agree_def] >>
  `w2n w + tuple_prefix_slot_size i tvs < dimword (:256)` by decide_tac >>
  `w2n (w + n2w (tuple_prefix_slot_size i tvs)) =
   w2n w + tuple_prefix_slot_size i tvs` by
    (Cases_on `w` >> gvs[wordsTheory.word_add_n2w]) >>
  simp[] >> rpt strip_tac >>
  qpat_x_assum `!k b. _ ==> _` irule >> simp[] >> strip_tac >>
  `dead_bytes_list st (w2n w) tvs (w2n k) b` by
    (qpat_x_assum `dead_bytes _ _ (TupleTV _) _ _` mp_tac >>
     simp[Once dead_bytes_def]) >>
  drule accountsRelPropsTheory.dead_bytes_list_el >>
  disch_then (qspec_then `i` mp_tac) >> simp[]
QED

(* A tuple element of a value read live is read live. *)
Theorem storage_read_live_tuple_elem[local]:
  !cx tr st w tvs i.
    storage_read_live cx tr st w (TupleTV tvs) /\ i < LENGTH tvs ==>
    storage_read_live cx tr st (w + n2w (tuple_prefix_slot_size i tvs))
      (EL i tvs)
Proof
  rpt gen_tac >> strip_tac >>
  drule tuple_prefix_el_bound >> strip_tac >>
  Cases_on `type_slot_size (EL i tvs) = 0`
  >- (simp[storage_read_live_def] >>
      rpt strip_tac >>
      qspec_then `w + n2w (tuple_prefix_slot_size i tvs)` mp_tac
        wordsTheory.w2n_lt >>
      decide_tac) >>
  qpat_x_assum `storage_read_live _ _ _ _ _` mp_tac >>
  rewrite_tac[storage_read_live_def] >> strip_tac >>
  rpt gen_tac >> strip_tac >> first_x_assum drule >> strip_tac >>
  `w2n w + tuple_prefix_slot_size i tvs < dimword (:256)` by decide_tac >>
  `w2n (w + n2w (tuple_prefix_slot_size i tvs)) =
   w2n w + tuple_prefix_slot_size i tvs` by
    (Cases_on `w` >> gvs[wordsTheory.word_add_n2w]) >>
  simp[] >> strip_tac >>
  `dead_bytes_list st (w2n w) tvs j b` by
    (qpat_x_assum `_ ==> dead_bytes _ _ _ _ _` mp_tac >>
     simp[Once dead_bytes_def]) >>
  drule accountsRelPropsTheory.dead_bytes_list_el >>
  disch_then (qspec_then `i` mp_tac) >> simp[]
QED

(* The element's value_vv holds the element, from the base's. *)
Theorem tuple_vv_holds_elem[local]:
  !func cenv cx env es sa sn es1 tv bvv q w dst tys tvs vs k tv' ctx.
    stmt_state_rel ctx func cenv cx es1 q /\ expr_sim_inv cenv cx env es /\
    vv_holds cenv cx (TupleT tys) tv bvv es1 q /\
    vv_at cenv cx (TupleT tys) sa sn es1 tv bvv q /\
    read_result cx tv es1 = (INL (ArrayV (TupleV vs)), es1) /\
    values_have_types tvs vs /\
    read_result cx tv' es1 = (INL (EL k vs), es1) /\
    eval_operand (vv_operand bvv) q = SOME w /\
    eval_operand dst q =
      SOME (w + n2w (tuple_offset cenv tys (vv_loc bvv) k)) /\
    OPT_MMAP (evaluate_type (get_tenv cx)) tys = SOME tvs /\
    evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
    k < LENGTH tvs ==>
    vv_holds cenv cx (EL k tys) tv'
      (LocatedValue (EL k tys) (mk_ptr dst (vv_loc bvv))) es1 q
Proof
  rpt gen_tac >> strip_tac >>
  `evaluate_type (get_tenv cx) (EL k tys) = SOME (EL k tvs)` by
    (drule opt_mmap_el >> disch_then (qspec_then `k` mp_tac) >>
     impl_tac >- (drule vyperTypeABITheory.OPT_MMAP_LENGTH >> simp[]) >>
     simp[]) >>
  `LENGTH vs = LENGTH tvs /\ value_has_type (EL k tvs) (EL k vs)` by
    metis_tac[values_have_types_el] >>
  qspecl_then [`cenv`, `cx`, `TupleT tys`, `tv`, `bvv`, `es1`, `q`,
               `TupleTV tvs`, `w`] mp_tac base_vv_holds_loc >>
  impl_tac >- simp[is_word_type_def] >> strip_tac >> gvs[] >>
  simp[vv_holds_def, mk_ptr_def] >>
  Cases_on `vv_loc bvv` >> gvs[]
  >~ [`LocMemory`]
  >- (drule_all tuple_elem_ptr >> strip_tac >> gvs[wordsTheory.WORD_ADD_0] >>
      `val_in_memory (EL k tvs) (EL k vs)
         (SUM (TAKE k (MAP type_memory_size tvs)) + w2n w) q.vs_memory` by
        (once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
         irule tuple_in_memory_elem >> gvs[val_in_memory_def]) >>
      simp[wordsTheory.WORD_ADD_0] >> strip_tac >>
      qspecl_then [`get_tenv cx`, `EL k tys`, `EL k tvs`, `EL k vs`,
                   `SUM (TAKE k (MAP type_memory_size tvs)) + w2n w`,
                   `q.vs_memory`] mp_tac val_in_memory_word_type >>
      gvs[])
  >~ [`immutable_holds`]
  >- (drule_all tuple_offset_code >>
      disch_then (qspec_then `k` assume_tac) >> gvs[] >>
      irule immutable_holds_tuple_elem >> simp[] >>
      qexistsl [`tv`, `vs`] >> simp[]) >>
  `tuple_offset cenv tys (vv_loc bvv) k = tuple_prefix_slot_size k tvs` by
    (irule tuple_offset_slots >> simp[] >> metis_tac[]) >>
  simp[storage_holds_def] >>
  drule_all read_storage_slot_tuple_elem >> strip_tac >> gvs[] >>
  simp[tuple_elem_slots_in_range, storage_range_agree_tuple_elem]
QED

(* The base's read, a tuple of the element types. *)
Theorem tuple_base_read[local]:
  !func cenv cx obj es sa sb s0 es1 btv bvv s w tys tvs ctx.
    vv_post ctx func cenv cx obj es sa sb s0 es1 btv bvv s /\
    post_value_type cenv obj = TupleT tys /\
    expr_type obj = TupleT tys /\
    evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
    eval_operand (vv_operand bvv) s = SOME w /\
    (!v. read_result cx btv es1 = (INL v, es1) ==>
         value_has_type (TupleTV tvs) v) ==>
    ?vs. read_result cx btv es1 = (INL (ArrayV (TupleV vs)), es1) /\
         values_have_types tvs vs /\ LENGTH vs = LENGTH tvs
Proof
  rpt gen_tac >> strip_tac >>
  `?v. read_result cx btv es1 = (INL v, es1)` by
    (gvs[vv_post_def] >>
     `~is_word_type (TupleT tys)` by simp[is_word_type_def] >>
     drule_all base_vv_holds_loc >> simp[is_word_type_def] >>
     metis_tac[]) >>
  `value_has_type (TupleTV tvs) v` by metis_tac[] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def] >>
  metis_tac[values_have_types_length]
QED

(* The element's value_vv after the ADD, from the base's. *)
Theorem tuple_vv_post[local]:
  !func cenv cx env obj idx es sa sn s0 es1 tv bvv q w dst tys tvs vs k tv' ctx.
    vv_post ctx func cenv cx obj es sa sn s0 es1 tv bvv q /\
    post_value_type cenv obj = TupleT tys /\
    expr_sim_inv cenv cx env es /\
    eval_operand (vv_operand bvv) q = SOME w /\
    eval_operand dst q =
      SOME (w + n2w (tuple_offset cenv tys (vv_loc bvv) k)) /\
    expr_type obj = TupleT tys /\
    OPT_MMAP (evaluate_type (get_tenv cx)) tys = SOME tvs /\
    evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
    k < LENGTH tvs /\
    read_result cx tv es1 = (INL (ArrayV (TupleV vs)), es1) /\
    values_have_types tvs vs /\
    read_result cx tv' es1 = (INL (EL k vs), es1) /\
    (!id path'. tv' = PlaceR (MemoryPlace id path') <=>
       ?path. path' = path ++ [ValueSubscript (IntV &k)] /\ tv = PlaceR (MemoryPlace id path)) ==>
    vv_post ctx func cenv cx (Subscript (EL k tys) obj idx) es sa sn s0 es1 tv'
      (LocatedValue (EL k tys) (mk_ptr dst (vv_loc bvv))) q
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `vv_post _ _ _ _ obj _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [vv_post_def]) >>
  rewrite_tac[vv_post_def] >> gvs[vyperASTTheory.expr_type_def] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (strip_tac >>
       qpat_x_assum `~expr_has_effect obj ==> pure_frame _ _ _ _ _ _` irule >>
       first_assum ACCEPT_TAC >> NO_TAC)
  >- (irule tuple_vv_holds_elem >> simp[] >> metis_tac[]) >>
  `vv_at cenv cx (EL k tys) sa sn es1 tv'
     (LocatedValue (EL k tys) (mk_ptr dst (vv_loc bvv))) q` by
    (qspecl_then [`func`, `cenv`, `cx`, `env`, `es`, `sa`, `sn`, `es1`, `tv`,
                  `bvv`, `q`, `w`, `dst`, `tys`, `tvs`, `vs`, `k`, `tv'`,
                  `EL k tys`, `ctx`] mp_tac tuple_vv_at_elem >>
     imp_res_tac values_have_types_length >> simp[]) >>
  simp[] >> rpt strip_tac >>
  qpat_x_assum `~expr_has_effect obj ==> vv_storage_live _ _ _ _` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  `evaluate_type (get_tenv cx) (EL k tys) = SOME (EL k tvs)` by
    (drule opt_mmap_el >> disch_then (qspec_then `k` mp_tac) >>
     impl_tac >- (drule vyperTypeABITheory.OPT_MMAP_LENGTH >> simp[]) >>
     simp[]) >>
  Cases_on `bvv` >>
  gvs[mk_ptr_def, vv_loc_def, contextTheory.vv_location_def,
      contextTheory.vv_operand_def] >>
  rename1 `LocatedValue t p` >>
  `t = TupleT tys` by
    (qpat_x_assum `vv_holds _ _ _ _ (LocatedValue _ _) _ _` mp_tac >>
     simp[vv_holds_def, is_bytestring_type_def] >> rpt strip_tac >>
     simp[]) >>
  `tuple_offset cenv tys p.ptr_location k = tuple_prefix_slot_size k tvs` by
    (irule tuple_offset_slots >> simp[] >> metis_tac[]) >>
  gvs[] >> irule storage_read_live_tuple_elem >> simp[] >>
  first_x_assum irule >> simp[]
QED

(* ===== The simulation ===== *)

(* The base evaluates to a local's place memory no longer holds, with a
   popped snapshot at the element (popped_at_elem). *)
Definition tuple_popped_clash_def:
  tuple_popped_clash cx obj idx es <=>
    ?r es1. eval_expr cx obj es = (INL r, es1) /\
            popped_at_elem r (literal_int_index idx) es1
End

Theorem lookup_scopes_popped_keys_indexed[local]:
  !sc id entry. popped_keys_indexed sc /\
    lookup_scopes id sc = SOME entry ==>
    EVERY (\k. ?p i etv n. k = p ++ [ValueSubscript i] /\
      subscripts_type entry.type p = SOME (ArrayTV etv (Dynamic n)))
      (MAP FST entry.popped)
Proof
  Induct >> simp[lookup_scopes_def, popped_keys_indexed_def] >>
  rpt gen_tac >> Cases_on `FLOOKUP h id` >>
  simp[] >> rpt strip_tac >> gvs[] >> metis_tac[popped_keys_indexed_def]
QED

Theorem tuple_memory_no_snapshot[local]:
  popped_keys_indexed es.scopes /\
  runtime_place_typed cx es (MemoryPlace id path) (TupleTV tvs) /\
  lookup_scopes id es.scopes = SOME entry ==>
  ~MEM (path ++ [ValueSubscript i],v) entry.popped
Proof
  strip_tac >>
  drule_all lookup_scopes_popped_keys_indexed >>
  simp[EVERY_MEM, MEM_MAP] >> strip_tac >>
  gvs[vyperPlaceTypingTheory.runtime_place_typed_memory] >>
  strip_tac >>
  `?p j etv n. path ++ [ValueSubscript i] = p ++ [ValueSubscript j] /\
      subscripts_type entry.type p = SOME (ArrayTV etv (Dynamic n))` by
    (first_x_assum irule >> goal_assum (drule_at Any) >> simp[]) >>
  gvs[rich_listTheory.APPEND_11_LENGTH]
QED

(* Never under expr_body_pre: the base's place has its tuple type
   (eval_expr's type soundness), while expr_sim_inv's popped_keys_indexed
   keys every snapshot at an index into a dynamic array, which the clash's
   key path ++ [i] would make path's type. *)
Theorem tuple_popped_clash_unreachable:
  !cenv cx env ann obj idx es tys.
    expr_body_pre cenv cx env (Subscript ann obj idx) es /\
    expr_type obj = TupleT tys ==>
    ~tuple_popped_clash cx obj idx es
Proof
  rpt gen_tac >> strip_tac >>
  drule_all tuple_pre_base >> strip_tac >>
  simp[tuple_popped_clash_def] >> rpt strip_tac >>
  drule_all expr_body_pre_eval_result >> strip_tac >>
  `popped_keys_indexed es1.scopes` by gvs[expr_sim_inv_def] >>
  Cases_on `r` >> gvs[popped_at_elem_def] >>
  rename1 `PlaceR place` >> Cases_on `place` >> gvs[popped_at_elem_def] >>
  gvs[vyperTypeInvariantsTheory.eval_result_typed_def] >>
  drule evaluate_tuple_type >> strip_tac >> gvs[] >>
  drule_all tuple_memory_no_snapshot >> metis_tac[]
QED

(* The element's selection reads no gas observation. *)
Theorem tuple_select_gas_obs[local]:
  !cx ty tv i ee r.
    select_result cx ty tv (ValueSubscript (IntV i)) ee = (r, ee) ==>
    !tail. select_result cx ty tv (ValueSubscript (IntV i))
             (ee with gas_obs := tail) = (r, ee with gas_obs := tail)
Proof
  rpt gen_tac >> Cases_on `tv`
  >~ [`Value v`]
  >- (simp[select_result_def, bind_def, lift_option_type_def, lift_sum_def,
           return_def, raise_def] >>
      rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def]))
  >~ [`HashMapRef tr slot kt vt`]
  >- (Cases_on `vt` >>
      simp[select_result_def, extend_place_def, bind_def,
           lift_option_type_def, return_def, raise_def, LET_THM] >>
      rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def])) >>
  rename1 `PlaceR pl` >> Cases_on `pl`
  >~ [`StoragePlace tr slot ptv`]
  >- (Cases_on `ptv` >> TRY (Cases_on `b`) >> Cases_on `tr` >>
      simp[select_result_def, extend_place_def, extend_storage_place_def,
           resolve_array_element_def, vyperStoragePlaceProvenanceTheory.resolve_array_element_empty, check_def,
           assert_def, ignore_bind_def, get_storage_backend_def,
           get_accounts_def, get_transient_storage_def, bind_def,
           lift_option_type_def, return_def, raise_def, pairTheory.UNCURRY,
           LET_THM, vfmTypesTheory.option_CASE_rator, COND_RATOR, COND_RAND]
      >>~- ([`oEL (Num i) l`],
            Cases_on `0 <= i /\ Num i < LENGTH l` >> simp[] >>
            Cases_on `oEL (Num i) l` >> simp[]) >>
      rpt (BasicProvers.TOP_CASE_TAC >> simp[COND_RAND]) >> gvs[])
  >~ [`MemoryPlace id path`]
  >- (simp[select_result_def, extend_place_def, place_type_value_def,
           read_place_def, get_scopes_def, bind_def, ignore_bind_def,
           lift_option_type_def, lift_sum_def, return_def, raise_def] >>
      rpt (BasicProvers.FULL_CASE_TAC >> simp[bind_def, return_def, raise_def]) >>
      rpt strip_tac >> gvs[]) >>
  simp[select_result_def, extend_place_def, place_type_value_def,
       read_place_def, get_immutables_def, get_address_immutables_def,
       bind_def, ignore_bind_def, lift_option_type_def, lift_sum_def,
       return_def, raise_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> simp[bind_def, return_def, raise_def]) >>
  rpt strip_tac >> gvs[]
QED

Theorem tuple_source[local]:
  !cx ann obj ity k.
    eval_expr cx (Subscript ann obj (Literal ity (IntL (&k)))) =
    bind (eval_expr cx obj)
      (\r. select_result cx (expr_type obj) r (ValueSubscript (IntV (&k))))
Proof
  simp[FUN_EQ_THM, eval_expr_tuple_subscript]
QED

Theorem tuple_operand_admissible[local]:
  !cenv cx env e es.
    expr_body_pre cenv cx env e es ==>
    gas_admissible (eval_expr cx e) expr_vv_res_ok es
Proof
  rpt strip_tac >> simp[gas_admissible_def] >> rpt strip_tac >>
  `expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
  metis_tac[expr_body_pre_vv_res_ok]
QED

Theorem tuple_exempt_cert[local]:
  !memory tops p cx ann obj ity k start marks out endpoint.
    gas_exempt_cert memory tops p (ignore_bind (eval_expr cx obj) (return ()))
      start marks out endpoint ==>
    gas_exempt_cert memory tops p
      (ignore_bind (eval_expr cx (Subscript ann obj (Literal ity (IntL (&k)))))
        (return ()))
      start marks out endpoint
Proof
  rpt strip_tac >> simp[tuple_source] >>
  PairCases_on `p` >> PairCases_on `start` >>
  PairCases_on `out` >> PairCases_on `endpoint` >>
  qmatch_goalsub_abbrev_tac `bind (eval_expr cx obj) sel` >>
  `ignore_bind (bind (eval_expr cx obj) sel) (return ()) =
   bind (eval_expr cx obj) (\r. ignore_bind (sel r) (return ()))` by
    (simp[FUN_EQ_THM, ignore_bind_def, bind_def] >> gen_tac >>
     Cases_on `eval_expr cx obj x` >> Cases_on `q` >> simp[]) >>
  pop_assum SUBST1_TAC >> irule gas_exempt_cert_error_result >> simp[]
QED

(* The source facts at the base's actual end state. *)
Theorem tuple_base_facts[local]:
  !cenv cx env obj ity k es0 tys btv es1.
    expr_body_pre cenv cx env
      (Subscript (EL k tys) obj (Literal ity (IntL (&k)))) es0 /\
    expr_body_pre cenv cx env obj es0 /\ expr_type obj = TupleT tys /\
    eval_expr cx obj es0 = (INL btv, es1) ==>
    ?tvs.
      evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
      OPT_MMAP (evaluate_type (get_tenv cx)) tys = SOME tvs /\
      LENGTH tvs = LENGTH tys /\
      (!v. read_result cx btv es1 = (INL v, es1) ==>
           value_has_type (TupleTV tvs) v) /\
      ~popped_at_elem btv k es1 /\
      !res es2.
        select_result cx (TupleT tys) btv (ValueSubscript (IntV (&k))) es1 =
          (res, es2) ==> !m. res <> INR (Error (TypeError m))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all expr_body_pre_runtime_typed >> strip_tac >> gvs[] >>
  drule evaluate_tuple_type >> strip_tac >> gvs[] >>
  conj_tac >- (drule vyperTypeABITheory.OPT_MMAP_LENGTH >> simp[]) >>
  conj_tac
  >- (drule_all tuple_popped_clash_unreachable >>
      simp[tuple_popped_clash_def, literal_int_index_def] >> metis_tac[]) >>
  rpt strip_tac >>
  `eval_expr cx (Subscript (EL k tys) obj (Literal ity (IntL (&k)))) es0 =
     (res, es2)` by simp[eval_expr_tuple_subscript, bind_def] >>
  qspecl_then [`cenv`, `cx`, `env`,
               `Subscript (EL k tys) obj (Literal ity (IntL (&k)))`, `es0`,
               `res`, `es2`] mp_tac expr_body_pre_vv_res_ok >>
  simp[expr_vv_res_ok_def]
QED

(* A completed base execution: the ADD's path and the element's post. *)
Theorem tuple_summary_ok[local]:
  !ctx func cenv cx env ty obj ity k es tys sa sm p sb bvv s0 marks btv fe
   t R.
    expr_body_pre cenv cx env
      (Subscript (EL k tys) obj (Literal ity (IntL (&k)))) es /\
    expr_body_pre cenv cx env obj es /\ expr_type obj = TupleT tys /\
    post_value_type cenv obj = TupleT tys /\
    k < LENGTH tys /\
    compile_expr cenv ty obj sa = (bvv, sm) /\ local_ptrs_reserved cenv sa /\
    sa.cs_next_var <= sm.cs_next_var /\
    emit_op ADD [vv_operand bvv;
                 Lit (n2w (tuple_offset cenv tys (vv_loc bvv) k))]
      sm = (p, sb) /\
    fn_has_code sm sb func /\
    gas_marked_exec F (ctx,func) (eval_expr cx obj) (es,s0) marks
      (INL btv) fe (OK t) /\
    vv_post ctx func cenv cx obj es sa sm s0 (fe with gas_obs := []) btv bvv t /\
    t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    gas_summary_at F (ctx,func) marks
      (eval_expr cx (Subscript (EL k tys) obj (Literal ity (IntL (&k)))))
      (es,s0)
      (\res ee t. ?tv. res = INL tv /\
         vv_post ctx func cenv cx
           (Subscript (EL k tys) obj (Literal ity (IntL (&k)))) es sa sb s0
           ee tv (LocatedValue (EL k tys) (mk_ptr p (vv_loc bvv))) t /\
         t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts) R
Proof
  rpt strip_tac >>
  `eval_expr cx obj (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL btv, fe with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
     strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `~t.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  mp_tac (Q.SPECL [`cenv`,`cx`,`env`,`obj`,`ity`,`k`,
            `es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
            `tys`,`btv`,`fe with gas_obs := []`] tuple_base_facts) >>
  simp[] >> strip_tac >>
  drule_all attr_add_path >> strip_tac >>
  rename1 `gas_path ctx func t 0 (OK t1)` >>
  qspecl_then [`func`,`cenv`,`cx`,`obj`,`es`,`sa`,`sb`,`s0`,
               `fe with gas_obs := []`,`btv`,`bvv`,`t1`,`w`,`tys`,`tvs`,
               `ctx`] mp_tac tuple_base_read >>
  simp[] >> strip_tac >>
  Cases_on `select_result cx (TupleT tys) btv (ValueSubscript (IntV (&k)))
              (fe with gas_obs := [])` >>
  rename1 `_ = (sres, es2)` >>
  `!m. sres <> INR (Error (TypeError m))` by metis_tac[] >>
  qspecl_then [`cx`,`TupleT tys`,`btv`,`k`,`fe with gas_obs := []`,`vs`,
               `sres`,`es2`] mp_tac select_tuple_read >>
  simp[] >> strip_tac >> gvs[] >>
  rename1 `select_result _ _ _ _ _ = (INL tv2, _)` >>
  drule tuple_select_gas_obs >> simp[] >> strip_tac >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INL tv2`, `fe`, `OK t1`] >> simp[] >> conj_tac
  >- (rewrite_tac[tuple_source] >>
      irule (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal
               |> REWRITE_RULE [APPEND_NIL]) >>
      qexistsl_tac [`fe`,`t`,`btv`] >> simp[] >>
      simp[gas_marked_exec_def, gas_marked_path_def, gas_explicit_def]) >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  qpat_assum `select_result _ _ _ _ _ = (INL tv2, _)`
    (assume_tac o MATCH_MP select_result_memory_place) >>
  disj1_tac >> irule tuple_vv_post >> simp[] >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`btv`, `vs`] >> simp[]
QED

Theorem tuple_vv_sim[local]:
  !ctx func cenv cx env ty obj ity k es tys.
    expr_body_pre cenv cx env
      (Subscript (EL k tys) obj (Literal ity (IntL (&k)))) es /\
    expr_body_pre cenv cx env obj es /\ expr_type obj = TupleT tys /\
    post_value_type cenv obj = expr_type obj /\
    place_type cenv obj = ValPT (TupleT tys) /\ k < LENGTH tys /\
    expr_vv_sim ctx func cenv cx ty obj es ==>
    expr_vv_sim ctx func cenv cx ty
      (Subscript (EL k tys) obj (Literal ity (IntL (&k)))) es
Proof
  rpt gen_tac >> strip_tac >>
  simp[expr_vv_sim_def] >> rpt gen_tac >> strip_tac >>
  drule_all compile_expr_tuple_subscript >> strip_tac >>
  gvs[literal_int_index_def] >>
  rename1 `compile_expr cenv ty obj sa = (bvv, sm)` >>
  drule attr_extends >> strip_tac >>
  drule compile_expr_extends >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  `gas_admissible (eval_expr cx obj) expr_vv_res_ok es` by
    metis_tac[tuple_operand_admissible] >>
  qpat_x_assum `expr_vv_sim _ _ _ _ _ obj _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_def]) >>
  disch_then (qspecl_then [`sa`,`sm`,`bvv`,`s0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def]) >> gvs[]
      >- (drule_all tuple_summary_ok >> simp[]) >>
      Cases_on `res` >> gvs[] >>
      rename1 `gas_marked_exec _ _ _ _ marks (INR exn) fe fr` >>
      simp[gas_summary_at_def] >>
      qexistsl_tac [`INR exn`,`fe`,`fr`] >> simp[] >>
      rewrite_tac[tuple_source] >> irule gas_marked_exec_bind_exception >>
      simp[]) >>
  qexists_tac `marks` >> disj2_tac >> metis_tac[tuple_exempt_cert]
QED

Theorem compile_subscript_tuple_sim:
  !nocalls ctx func cenv cx ann obj idx tys.
    expr_vv_case nocalls ctx func cenv cx obj /\ expr_type obj = TupleT tys /\
    place_type cenv obj = ValPT (TupleT tys) /\
    (~nocalls ==> post_value_type cenv obj = expr_type obj) ==>
    expr_vv_case nocalls ctx func cenv cx (Subscript ann obj idx)
Proof
  rpt gen_tac >> strip_tac >> simp[expr_vv_case_def] >>
  rpt gen_tac >> strip_tac >>
  `post_value_type cenv obj = expr_type obj` by
    (Cases_on `nocalls` >> fs[vyperTypeCallGraphTheory.int_calls_expr_def] >>
     metis_tac[exprSimHypsTheory.post_value_type_no_calls]) >>
  drule_all tuple_pre_base >> strip_tac >> gvs[] >>
  `expr_vv_sim ctx func cenv cx ty obj es` by
    (qpat_x_assum `expr_vv_case _ _ _ _ _ obj` mp_tac >>
     simp[expr_vv_case_def] >> disch_then irule >> simp[] >>
     qexists_tac `env` >> simp[]) >>
  irule tuple_vv_sim >> simp[] >> metis_tac[]
QED

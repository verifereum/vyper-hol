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
 * Helpers: opt_mmap_el, values_have_types_el, tuple_val_wf_el,
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
 *   tuple_elem_slots_in_range, tuple_prefix_el_bound, dead_bytes_list_el,
 *   storage_read_live_tuple_elem, tuple_vv_holds_elem, tuple_base_read,
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
  list rich_list finite_map pair
  fragExec exprSim exprSimHyps exprSimUnwrap exprSimLen exprSimLeaves
  exprSimAggregateLayout exprSimAttributeFields exprSimAttribute
  placeTypingProps
  exprLowering exprLoweringProps compileEnv context
  valueEncoding vyperAST vyperInterpreter vyperState vyperStorage vyperValue
  vyperValueOperation vyperTyping vyperTypeSystem vyperTypeExprSoundness
  vyperPlaceResultTyping valueEncodingProofs
  venomState venomInst
Libs
  pairLib

(* ===== Lists ===== *)

Theorem opt_mmap_el[local]:
  !l l' k f.
    OPT_MMAP f l = SOME l' /\ k < LENGTH l ==>
    LENGTH l' = LENGTH l /\ f (EL k l) = SOME (EL k l')
Proof
  Induct >> simp[] >> rpt gen_tac >>
  Cases_on `f h` >> simp[] >> Cases_on `OPT_MMAP f l` >> simp[] >>
  strip_tac >> gvs[] >> rename1 `OPT_MMAP f l = SOME tl` >>
  first_x_assum (qspecl_then [`tl`, `PRE k`, `f`] mp_tac) >>
  Cases_on `k` >> gvs[] >> drule vyperTypeABITheory.OPT_MMAP_LENGTH >> simp[]
QED

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
  rpt gen_tac >> Cases_on `tr` >> Cases_on `bd` >>
  simp[read_storage_slot_def, get_storage_backend_def,
       get_transient_storage_def, get_accounts_def, bind_def, return_def] >>
  qmatch_goalsub_abbrev_tac `decode_value stor` >>
  simp[Once decode_value_def] >>
  rpt (CASE_TAC >> simp[lift_option_def, raise_def, return_def])
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
      drule evaluate_subscripts_append_err >> simp[]) >>
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
  drule evaluate_subscripts_append_err >> simp[] >> strip_tac >>
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
      alloc_limits_expr_def, supportedExprTraverseTheory.expr_has_evm_run_thm]
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
           storage_read_live cx F (get_storage cx es F) w tvt) /\
        (vv_loc vv = LocTransient ==>
           read_storage_slot cx T w tvt es = (INL v, es) /\
           slots_in_range (get_storage cx es T) (w2n w) tvt /\
           storage_read_live cx T (get_storage cx es T) w tvt) /\
        (vv_loc vv = LocCode ==> immutable_holds cenv cx t tv w es) /\
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
    ~dynarray_type t /\ read_result cx tv es = (INL v, es) /\
    evaluate_type (get_tenv cx) t = SOME tvt /\
    vv_loc vv = LocMemory /\ eval_operand (vv_operand vv) s = SOME w ==>
    val_wf tvt v /\
    ((?aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
                 sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
                 b <= w2n w /\ w2n w + val_footprint tvt v <= b + sz /\
                 (!n lb lsz. local_region cenv es.scopes s n lb lsz ==>
                              b + sz <= lb \/ lb + lsz <= b)) \/
     (?n b sz. local_region cenv es.scopes s n b sz /\
               b <= w2n w /\ w2n w + val_footprint tvt v <= b + sz /\
               (dynarray_local cenv n ==> b + 32 <= w2n w)) \/
     val_footprint tvt v = 0)
Proof
  rpt gen_tac >> Cases_on `vv` >>
  simp[vv_at_def, vv_loc_def, vv_location_def, vv_operand_def,
       expr_val_at_def] >>
  rpt strip_tac >> gvs[] >>
  TRY (first_x_assum drule_all >> strip_tac >> gvs[]) >> metis_tac[]
QED

(* The element's pointer in memory: the element lies inside the base's
   bytes, so its address does not wrap, and the base sits where vv_at says. *)
Theorem tuple_elem_ptr[local]:
  !func cenv cx env es sa sn es1 tv bvv q w tys tvs vs k.
    stmt_state_rel func cenv cx es1 q /\ expr_sim_inv cenv cx env es /\
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
               (dynarray_local cenv n ==> b + 32 <= w2n w)) \/
     type_memory_size_list tvs = 0)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all tuple_offset_memory >> disch_then (qspec_then `k` assume_tac) >>
  qspecl_then [`cenv`, `cx`, `TupleT tys`, `sa`, `sn`, `es1`, `tv`, `bvv`,
               `q`, `ArrayV (TupleV vs)`, `TupleTV tvs`, `w`] mp_tac
    base_vv_at_mem >>
  impl_tac >- simp[is_word_type_def, dynarray_type_def] >> strip_tac >>
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
  !func cenv cx env es sa sn es1 tv bvv q w dst tys tvs vs k tv' t.
    stmt_state_rel func cenv cx es1 q /\ expr_sim_inv cenv cx env es /\
    vv_at cenv cx (TupleT tys) sa sn es1 tv bvv q /\
    read_result cx tv es1 = (INL (ArrayV (TupleV vs)), es1) /\
    read_result cx tv' es1 = (INL (EL k vs), es1) /\
    eval_operand (vv_operand bvv) q = SOME w /\
    eval_operand dst q =
      SOME (w + n2w (tuple_offset cenv tys (vv_loc bvv) k)) /\
    OPT_MMAP (evaluate_type (get_tenv cx)) tys = SOME tvs /\
    evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
    LENGTH vs = LENGTH tvs /\ k < LENGTH tvs ==>
    vv_at cenv cx (EL k tys) sa sn es1 tv'
      (LocatedValue t (mk_ptr dst (vv_loc bvv))) q
Proof
  rpt gen_tac >> strip_tac >>
  simp[vv_at_def, mk_ptr_def] >> rpt gen_tac >> strip_tac >> gvs[] >>
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
      rpt strip_tac >> res_tac >> decide_tac) >>
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
  !cenv cx tys tvs tv w es vs j tv'.
    immutable_holds cenv cx (TupleT tys) tv w es /\
    read_result cx tv es = (INL (ArrayV (TupleV vs)), es) /\
    evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
    evaluate_type (get_tenv cx) (EL j tys) = SOME (EL j tvs) /\
    j < LENGTH tvs /\ read_result cx tv' es = (INL (EL j vs), es) ==>
    immutable_holds cenv cx (EL j tys) tv'
      (w + n2w (SUM (TAKE j (MAP type_memory_size tvs)))) es
Proof
  rw[immutable_holds_def] >> gvs[value_has_type_def] >>
  `LENGTH vs = LENGTH tvs /\ value_has_type (EL j tvs) (EL j vs)` by
    metis_tac[values_have_types_el] >>
  qexistsl [`name`, `off`, `itv`, `iv`,
            `k + SUM (TAKE j (MAP type_memory_size tvs))`] >>
  simp[wordsTheory.word_add_n2w] >>
  irule sub_layout_tuple_elem >> simp[]
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

Theorem dead_bytes_list_el[local]:
  !tvs k st base j b.
    dead_bytes_list st base tvs j b /\ k < LENGTH tvs /\
    base + tuple_prefix_slot_size k tvs <= j /\
    j < base + tuple_prefix_slot_size k tvs + type_slot_size (EL k tvs) ==>
    dead_bytes st (base + tuple_prefix_slot_size k tvs) (EL k tvs) j b
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `dead_bytes_list _ _ _ _ _` mp_tac >>
  simp[Once dead_bytes_def] >> strip_tac >>
  Cases_on `k` >> gvs[tuple_prefix_slot_size_def] >>
  imp_res_tac (cj 1 accountsRelPropsTheory.dead_bytes_range) >>
  imp_res_tac (cj 2 accountsRelPropsTheory.dead_bytes_range) >> gvs[] >>
  first_x_assum drule >> disch_then (qspec_then `n` mp_tac) >>
  impl_tac >- decide_tac >> rewrite_tac[arithmeticTheory.ADD_ASSOC]
QED

(* A tuple element of a value read live is read live. *)
Theorem storage_read_live_tuple_elem[local]:
  !cx tr st w tvs k.
    storage_read_live cx tr st w (TupleTV tvs) /\ k < LENGTH tvs ==>
    storage_read_live cx tr st (w + n2w (tuple_prefix_slot_size k tvs))
      (EL k tvs)
Proof
  rpt gen_tac >> strip_tac >>
  drule tuple_prefix_el_bound >> strip_tac >>
  Cases_on `type_slot_size (EL k tvs) = 0`
  >- (simp[storage_read_live_def] >> rpt strip_tac >>
      qspec_then `w + n2w (tuple_prefix_slot_size k tvs)` mp_tac
        wordsTheory.w2n_lt >>
      decide_tac) >>
  qpat_x_assum `storage_read_live _ _ _ _ _` mp_tac >>
  rewrite_tac[storage_read_live_def] >> strip_tac >>
  rpt gen_tac >> strip_tac >> first_x_assum drule >> strip_tac >>
  `w2n w + tuple_prefix_slot_size k tvs < dimword (:256)` by decide_tac >>
  `w2n w + tuple_prefix_slot_size k tvs + type_slot_size (EL k tvs) <=
   dimword (:256)` by decide_tac >>
  `w2n (w + n2w (tuple_prefix_slot_size k tvs)) =
   w2n w + tuple_prefix_slot_size k tvs` by
    (Cases_on `w` >> gvs[wordsTheory.word_add_n2w]) >>
  simp[] >> strip_tac >>
  `w2n w <= j /\ j < w2n w + type_slot_size (TupleTV tvs)` by decide_tac >>
  `dead_bytes_list st (w2n w) tvs j b` by
    (qpat_x_assum `_ ==> dead_bytes _ _ _ _ _` mp_tac >>
     simp[Once dead_bytes_def]) >>
  drule dead_bytes_list_el >>
  disch_then (qspec_then `k` mp_tac) >> simp[]
QED

(* The element's value_vv holds the element, from the base's. *)
Theorem tuple_vv_holds_elem[local]:
  !func cenv cx env es sa sn es1 tv bvv q w dst tys tvs vs k tv'.
    stmt_state_rel func cenv cx es1 q /\ expr_sim_inv cenv cx env es /\
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
  simp[tuple_elem_slots_in_range, storage_read_live_tuple_elem]
QED

(* The base's read, a tuple of the element types. *)
Theorem tuple_base_read[local]:
  !func cenv cx obj es sa sb s0 es1 btv bvv s w tys tvs.
    vv_post func cenv cx obj es sa sb s0 es1 btv bvv s /\
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
     qspecl_then [`cenv`, `cx`, `TupleT tys`, `btv`, `bvv`, `es1`, `s`,
                  `TupleTV tvs`, `w`] mp_tac base_vv_holds_loc >>
     simp[is_word_type_def] >> metis_tac[]) >>
  `value_has_type (TupleTV tvs) v` by metis_tac[] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def] >>
  metis_tac[values_have_types_length]
QED

(* The element's value_vv after the ADD, from the base's. *)
Theorem tuple_vv_post[local]:
  !func cenv cx env obj idx es sa sn s0 es1 tv bvv q w dst tys tvs vs k tv'.
    vv_post func cenv cx obj es sa sn s0 es1 tv bvv q /\
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
    read_result cx tv' es1 = (INL (EL k vs), es1) ==>
    vv_post func cenv cx (Subscript (EL k tys) obj idx) es sa sn s0 es1 tv'
      (LocatedValue (EL k tys) (mk_ptr dst (vv_loc bvv))) q
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `vv_post _ _ _ obj _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [vv_post_def]) >>
  rewrite_tac[vv_post_def] >> gvs[vyperASTTheory.expr_type_def] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
  >- (irule tuple_vv_holds_elem >> simp[] >> metis_tac[]) >>
  qspecl_then [`func`, `cenv`, `cx`, `env`, `es`, `sa`, `sn`, `es1`, `tv`,
               `bvv`, `q`, `w`, `dst`, `tys`, `tvs`, `vs`, `k`, `tv'`,
               `EL k tys`] mp_tac tuple_vv_at_elem >>
  imp_res_tac values_have_types_length >> simp[]
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

Theorem compile_subscript_tuple_sim:
  !nocalls ctx func cenv cx ann obj idx tys.
    expr_vv_case nocalls ctx func cenv cx obj /\ expr_type obj = TupleT tys /\
    place_type cenv obj = ValPT (TupleT tys) ==>
    expr_vv_case nocalls ctx func cenv cx (Subscript ann obj idx)
Proof
  rpt gen_tac >> strip_tac >> simp[expr_vv_case_def] >>
  rpt gen_tac >> strip_tac >>
  `~tuple_popped_clash cx obj idx es` by
    (drule_all tuple_popped_clash_unreachable >> simp[]) >>
  drule_all tuple_pre_base >> strip_tac >> gvs[] >>
  `expr_vv_sim ctx func cenv cx ty obj es` by
    (qpat_x_assum `expr_vv_case _ _ _ _ _ obj` mp_tac >>
     simp[expr_vv_case_def] >> disch_then irule >> simp[] >>
     qexists_tac `env` >> simp[]) >>
  `literal_int_index (Literal ity (IntL (&k))) = k` by
    simp[literal_int_index_def] >>
  simp[expr_vv_sim_def] >> rpt gen_tac >> strip_tac >>
  drule_all compile_expr_tuple_subscript >> strip_tac >> gvs[] >>
  rename1 `compile_expr cenv ty obj sa = (bvv, sm)` >>
  drule attr_extends >> strip_tac >>
  drule compile_expr_extends >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  gvs[eval_expr_tuple_subscript, bind_def] >>
  Cases_on `eval_expr cx obj es` >> rename1 `_ = (er, es1)` >>
  `expr_vv_res_ok er` by (drule_all expr_body_pre_vv_res_ok >> simp[]) >>
  qpat_x_assum `expr_vv_sim _ _ _ _ _ obj _` mp_tac >>
  simp[expr_vv_sim_def] >>
  disch_then drule_all >> disch_then (qspec_then `s0` assume_tac) >>
  Cases_on `er` >> gvs[]
  >- (rename1 `eval_expr cx obj es = (INL btv, es1)` >>
      drule_all expr_body_pre_runtime_typed >> strip_tac >> gvs[] >>
      drule evaluate_tuple_type >> strip_tac >> gvs[] >>
      `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
      `~popped_at_elem btv k es1` by
        (fs[tuple_popped_clash_def] >> metis_tac[]) >>
      `!m. res <> INR (Error (TypeError m))` by
        (rpt strip_tac >> gvs[expr_vv_res_ok_def]) >>
      `LENGTH tvs = LENGTH tys` by
        (drule vyperTypeABITheory.OPT_MMAP_LENGTH >> simp[]) >>
      irule frag_exec_seq >>
      qexistsl_tac [`\s. vv_post func cenv cx obj es sa sm s0 es1 btv bvv s`,
                    `sm`] >>
      simp[] >> conj_tac
      >- (irule frag_exec_conseq >> goal_assum (drule_at Any) >> simp[]) >>
      qmatch_asmsub_abbrev_tac `emit_op ADD [_; Lit (n2w off)] sm = _` >>
      drule_all attr_add_frag >>
      disch_then (qspecl_then [`ctx`, `func`, `cx`, `es`, `s0`, `es1`, `btv`,
                               `expr_exit res`] assume_tac) >>
      irule frag_exec_conseq >> goal_assum (drule_at Any) >> simp[] >>
      rpt strip_tac >>
      drule_all tuple_base_read >> strip_tac >>
      drule select_tuple_read >>
      disch_then (drule_at (Pat `select_result _ _ _ _ _ = _`)) >>
      simp[] >> strip_tac >> gvs[] >>
      irule tuple_vv_post >> simp[Abbr `off`] >>
      conj_tac >- metis_tac[] >>
      qexistsl [`btv`, `vs`] >> simp[]) >>
  irule frag_exec_exit_prefix >> goal_assum (drule_at Any) >> simp[]
QED

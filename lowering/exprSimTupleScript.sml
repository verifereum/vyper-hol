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
 *   tuple_elem_slots_in_range, tuple_prefix_el_bound, dead_bytes_list_el,
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
  exprLowering exprLoweringProps compileEnv context
  valueEncoding vyperAST vyperInterpreter vyperState vyperStorage vyperValue
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
  cheat
QED

Theorem tuple_val_wf_el[local]:
  !vs tvs k.
    tuple_val_wf vs tvs /\ LENGTH vs = LENGTH tvs /\ k < LENGTH vs ==>
    val_wf (EL k tvs) (EL k vs)
Proof
  cheat
QED

Theorem sum_take_el_le[local]:
  !l k. k < LENGTH l ==> SUM (TAKE k l) + EL k l <= SUM l
Proof
  cheat
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
  cheat
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
  cheat
QED

Theorem tuple_offset_memory[local]:
  !cenv cx env es tys tvs k.
    expr_sim_inv cenv cx env es /\
    OPT_MMAP (evaluate_type (get_tenv cx)) tys = SOME tvs ==>
    tuple_offset cenv tys LocMemory k = SUM (TAKE k (MAP type_memory_size tvs))
Proof
  cheat
QED

Theorem tuple_offset_code[local]:
  !cenv cx env es tys tvs k.
    expr_sim_inv cenv cx env es /\
    OPT_MMAP (evaluate_type (get_tenv cx)) tys = SOME tvs ==>
    tuple_offset cenv tys LocCode k = SUM (TAKE k (MAP type_memory_size tvs))
Proof
  cheat
QED

Theorem tuple_offset_slots[local]:
  !cenv cx env es tys tvs k loc.
    expr_sim_inv cenv cx env es /\
    OPT_MMAP (evaluate_type (get_tenv cx)) tys = SOME tvs /\
    (loc = LocStorage \/ loc = LocTransient) ==>
    tuple_offset cenv tys loc k = tuple_prefix_slot_size k tvs
Proof
  cheat
QED

(* ===== A tuple's element ===== *)

Theorem tuple_in_memory_elem[local]:
  !vs tvs off mem k.
    tuple_in_memory vs tvs off mem /\ LENGTH vs = LENGTH tvs /\
    k < LENGTH vs ==>
    val_in_memory (EL k tvs) (EL k vs)
      (off + SUM (TAKE k (MAP type_memory_size tvs))) mem
Proof
  cheat
QED

Theorem decode_tuple_elem[local]:
  !tvs storage off vs k.
    decode_tuple storage off tvs = SOME vs /\ k < LENGTH tvs ==>
    k < LENGTH vs /\
    decode_value storage (off + tuple_prefix_slot_size k tvs) (EL k tvs) =
      SOME (EL k vs)
Proof
  cheat
QED

Theorem read_storage_slot_tuple_elem[local]:
  !cx tr slot tvs es v es1 k.
    read_storage_slot cx tr slot (TupleTV tvs) es = (INL v, es1) /\
    k < LENGTH tvs ==>
    ?vs. v = ArrayV (TupleV vs) /\ k < LENGTH vs /\
         read_storage_slot cx tr (slot + n2w (tuple_prefix_slot_size k tvs))
           (EL k tvs) es = (INL (EL k vs), es1)
Proof
  cheat
QED

Theorem decode_tuple_length[local]:
  !tvs storage off vs.
    decode_tuple storage off tvs = SOME vs ==> LENGTH vs = LENGTH tvs
Proof
  cheat
QED

Theorem read_storage_slot_tuple_length[local]:
  !cx tr slot tvs es v es1.
    read_storage_slot cx tr slot (TupleTV tvs) es = (INL v, es1) ==>
    ?vs. v = ArrayV (TupleV vs) /\ LENGTH vs = LENGTH tvs
Proof
  cheat
QED

(* An array decoded from storage is a static or dynamic array, never a
   tuple. *)
Theorem read_storage_slot_array_not_tuple[local]:
  !cx tr slot etv bd es vs es1.
    read_storage_slot cx tr slot (ArrayTV etv bd) es <>
      (INL (ArrayV (TupleV vs)), es1)
Proof
  cheat
QED

(* ===== The source's selection ===== *)

Theorem evaluate_subscripts_snoc_tuple[local]:
  !path tv a vs k.
    evaluate_subscripts tv a path = INL (ArrayV (TupleV vs)) /\
    k < LENGTH vs ==>
    evaluate_subscripts tv a (path ++ [ValueSubscript (IntV (&k))]) =
      INL (EL k vs)
Proof
  cheat
QED

Theorem read_popped_snoc_tuple[local]:
  !hist tv path vs k.
    read_popped tv path hist = SOME (ArrayV (TupleV vs)) /\
    k < LENGTH vs /\
    (!v'. ~MEM (path ++ [ValueSubscript (IntV (&k))], v') hist) ==>
    read_popped tv (path ++ [ValueSubscript (IntV (&k))]) hist =
      SOME (EL k vs)
Proof
  cheat
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
  cheat
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
  cheat
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
  cheat
QED

(* ===== Typing ===== *)

Theorem evaluate_tuple_type[local]:
  !tenv tys tvt.
    evaluate_type tenv (TupleT tys) = SOME tvt ==>
    ?tvs. tvt = TupleTV tvs /\ OPT_MMAP (evaluate_type tenv) tys = SOME tvs
Proof
  cheat
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
  cheat
QED

Theorem eval_expr_tuple_subscript[local]:
  !cx ann obj ity k es.
    eval_expr cx (Subscript ann obj (Literal ity (IntL (&k)))) es =
    (do r <- eval_expr cx obj;
        select_result cx (expr_type obj) r (ValueSubscript (IntV (&k))) od)
      es
Proof
  cheat
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
  cheat
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
               local_path_at cenv cx n (w2n w - b) tvt) \/
     val_footprint tvt v = 0)
Proof
  cheat
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
               local_path_at cenv cx n (w2n w - b) (TupleTV tvs)) \/
     type_memory_size_list tvs = 0)
Proof
  cheat
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
    LENGTH vs = LENGTH tvs /\ k < LENGTH tvs ==>
    vv_at cenv cx (EL k tys) sa sn es1 tv'
      (LocatedValue t (mk_ptr dst (vv_loc bvv))) q
Proof
  cheat
QED

(* A tuple's element sits inside the tuple's layout at its offset. *)
Theorem sub_layout_tuple_elem[local]:
  !itv iv k tvs vs j.
    sub_layout itv iv k (TupleTV tvs) (ArrayV (TupleV vs)) /\
    LENGTH vs = LENGTH tvs /\ j < LENGTH vs ==>
    sub_layout itv iv (k + SUM (TAKE j (MAP type_memory_size tvs)))
      (EL j tvs) (EL j vs)
Proof
  cheat
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
  cheat
QED

(* ===== A tuple element's slots in storage ===== *)

Theorem tuple_slots_in_range_el[local]:
  !tvs k off storage.
    tuple_slots_in_range storage off tvs /\ k < LENGTH tvs ==>
    slots_in_range storage (off + tuple_prefix_slot_size k tvs) (EL k tvs)
Proof
  cheat
QED

Theorem tuple_elem_slots_in_range[local]:
  !storage w tvs k.
    slots_in_range storage (w2n (w:bytes32)) (TupleTV tvs) /\
    k < LENGTH tvs ==>
    slots_in_range storage
      (w2n (w + n2w (tuple_prefix_slot_size k tvs))) (EL k tvs)
Proof
  cheat
QED

Theorem tuple_prefix_el_bound[local]:
  !tvs k.
    k < LENGTH tvs ==>
    tuple_prefix_slot_size k tvs + type_slot_size (EL k tvs) <=
    type_slot_size (TupleTV tvs)
Proof
  cheat
QED

Theorem dead_bytes_list_el[local]:
  !tvs k st base j b.
    dead_bytes_list st base tvs j b /\ k < LENGTH tvs /\
    base + tuple_prefix_slot_size k tvs <= j /\
    j < base + tuple_prefix_slot_size k tvs + type_slot_size (EL k tvs) ==>
    dead_bytes st (base + tuple_prefix_slot_size k tvs) (EL k tvs) j b
Proof
  cheat
QED

(* A tuple element of a value whose slots agree has its slots agree. *)
Theorem storage_range_agree_tuple_elem[local]:
  !st st' w tvs i.
    storage_range_agree st st' w (TupleTV tvs) /\ i < LENGTH tvs ==>
    storage_range_agree st st' (w + n2w (tuple_prefix_slot_size i tvs))
      (EL i tvs)
Proof
  cheat
QED

(* A tuple element of a value read live is read live. *)
Theorem storage_read_live_tuple_elem[local]:
  !cx tr st w tvs i.
    storage_read_live cx tr st w (TupleTV tvs) /\ i < LENGTH tvs ==>
    storage_read_live cx tr st (w + n2w (tuple_prefix_slot_size i tvs))
      (EL i tvs)
Proof
  cheat
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
  cheat
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
  cheat
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
    read_result cx tv' es1 = (INL (EL k vs), es1) ==>
    vv_post ctx func cenv cx (Subscript (EL k tys) obj idx) es sa sn s0 es1 tv'
      (LocatedValue (EL k tys) (mk_ptr dst (vv_loc bvv))) q
Proof
  cheat
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
  cheat
QED

Theorem tuple_memory_no_snapshot[local]:
  popped_keys_indexed es.scopes /\
  runtime_place_typed cx es (MemoryPlace id path) (TupleTV tvs) /\
  lookup_scopes id es.scopes = SOME entry ==>
  ~MEM (path ++ [ValueSubscript i],v) entry.popped
Proof
  cheat
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
  cheat
QED

(* The element's selection reads no gas observation. *)
Theorem tuple_select_gas_obs[local]:
  !cx ty tv i ee r.
    select_result cx ty tv (ValueSubscript (IntV i)) ee = (r, ee) ==>
    !tail. select_result cx ty tv (ValueSubscript (IntV i))
             (ee with gas_obs := tail) = (r, ee with gas_obs := tail)
Proof
  cheat
QED

Theorem tuple_source[local]:
  !cx ann obj ity k.
    eval_expr cx (Subscript ann obj (Literal ity (IntL (&k)))) =
    bind (eval_expr cx obj)
      (\r. select_result cx (expr_type obj) r (ValueSubscript (IntV (&k))))
Proof
  cheat
QED

Theorem tuple_operand_admissible[local]:
  !cenv cx env e es.
    expr_body_pre cenv cx env e es ==>
    gas_admissible (eval_expr cx e) expr_vv_res_ok es
Proof
  cheat
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
  cheat
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
  cheat
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
  cheat
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
  cheat
QED

Theorem compile_subscript_tuple_sim:
  !nocalls ctx func cenv cx ann obj idx tys.
    expr_vv_case nocalls ctx func cenv cx obj /\ expr_type obj = TupleT tys /\
    place_type cenv obj = ValPT (TupleT tys) /\
    (~nocalls ==> post_value_type cenv obj = expr_type obj) ==>
    expr_vv_case nocalls ctx func cenv cx (Subscript ann obj idx)
Proof
  cheat
QED

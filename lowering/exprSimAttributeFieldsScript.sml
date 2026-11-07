(*
 * Struct fields for the attribute simulation (#636, Places row 2)
 *
 * What exprSimAttribute needs of a struct field, apart from the lowering:
 * where ce_struct_fields puts it in memory and in storage, that a struct
 * decoded from storage decodes its field at the field's slot, and that the
 * source's selection of a field (select_result) reads the field of the
 * struct it selects from.
 *
 * TOP-LEVEL:
 *   fields_layout, struct_fields_layout — ce_struct_fields lays a struct out
 *                                  as its evaluated type, under expr_sim_inv
 *   mem_field_offset_layout, struct_field_type — a field's offset and type
 *                                  value in a laid out struct
 *   opt_mmap_el                  — an element of an OPT_MMAP result
 *   type_path_offset_mem, mem_path_offset_type — a path's offset in a
 *                                  declared type is its mem_path_offset in
 *                                  the type value, and back
 *   local_path_at_dynarray_len_at — a dynamic array where local_path_at puts
 *                                  it has its length word exempt
 *   local_path_at_dynarray_apart, local_val_at_dynarray_apart — a value
 *                                  with no dynamic array in it, in a local,
 *                                  is apart from the local's length words
 *                                  locals_kept exempts
 *   fields_in_memory_field, fields_val_wf_field, struct_field_offset_le,
 *   struct_field_offset_slots_eq — a field of a laid out struct
 *   read_storage_slot_field      — a field of a struct read from storage
 *   popped_at_field, select_attr_read — the source's selection
 *   popped_keys_indexed_not_at_field — popped_at_field never holds where
 *                                  expr_sim_inv does
 *   slot_count_of_memory_size    — a type's slots are its memory size
 *                                  rounded up to words
 *   decode_value_n2w, decode_struct_field,
 *   evaluate_subscripts_snoc_attr, evaluate_subscripts_append_err,
 *   read_popped_snoc_attr, read_memory_path_snoc_attr — steps of the
 *                                  field reads, exported for reuse
 *
 * Helpers: fields_layout_zip, read_slots_n2w, select_attr_read_immutable,
 *   alookup_zip_field, tuple_take_memory_bytes,
 *   type_step_offset_mem, fields_layout_alookup, mem_step_offset_type
 *
 * select_attr_read leaves out a local's place that memory no longer holds
 * and whose popped history has a snapshot at the field itself
 * (popped_at_field): read_popped may read the snapshot there, not the field
 * of the struct read at the place.
 *)

Theory exprSimAttributeFields
Ancestors
  loweringPosts
  exprSimFieldLayout
  exprSimHypsDefs
  storageDecodeMemory
  list rich_list finite_map pair
  exprSimProps exprSimHyps compileEnv valueEncoding
  vyperAST vyperInterpreter vyperState vyperStorage vyperValue
  vyperTyping vyperTypeSystem vyperTypeExprSoundness
Libs
  pairLib

(* ===== Struct layout ===== *)




(* The compile environment's fields of a struct, field by field: the same
   name and type_memory_size of the evaluated field type as size. *)



(* A field of a struct ce_struct_fields lays out as its type value: its
   offset is struct_field_offset's. *)
Theorem mem_field_offset_layout:
  !flds fs fld ftv.
    fields_layout flds fs /\ ALOOKUP fs fld = SOME ftv ==>
    mem_field_offset fs fld = SOME (struct_field_offset flds fld, ftv)
Proof
  cheat
QED


Theorem alookup_zip_field[local]:
  !fields tvs f fld fty fsz.
    OPT_MMAP f (MAP (FST o SND) fields) = SOME tvs /\
    ALOOKUP fields fld = SOME (fty, fsz) ==>
    ?ftv. ALOOKUP (ZIP (MAP FST fields, tvs)) fld = SOME ftv /\
          f fty = SOME ftv
Proof
  cheat
QED

(* A field of the lowering's struct table has, in the struct's type value,
   the type value its declared type evaluates to. *)
Theorem struct_field_type:
  !cenv cx env es sid fs fld fty fsz.
    expr_sim_inv cenv cx env es /\
    evaluate_type (get_tenv cx) (StructT sid) = SOME (StructTV fs) /\
    ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
      fld = SOME (fty, fsz) ==>
    ?ftv. ALOOKUP fs fld = SOME ftv /\
          evaluate_type (get_tenv cx) fty = SOME ftv
Proof
  cheat
QED

(* ===== Offsets of declared types and of their type values ===== *)

Theorem opt_mmap_el:
  !l l' k f.
    OPT_MMAP f l = SOME l' /\ k < LENGTH l ==>
    LENGTH l' = LENGTH l /\ f (EL k l) = SOME (EL k l')
Proof
  cheat
QED

Theorem tuple_take_memory_bytes[local]:
  !tys tvs cenv cx env es i.
    expr_sim_inv cenv cx env es /\
    OPT_MMAP (evaluate_type (get_tenv cx)) tys = SOME tvs ==>
    SUM (MAP (type_memory_bytes cenv) (TAKE i tys)) =
      type_memory_size_list (TAKE i tvs)
Proof
  cheat
QED

(* One step over a declared type is the same step over its type value. *)
Theorem type_step_offset_mem[local]:
  !cenv cx env es t tv sb k et.
    expr_sim_inv cenv cx env es /\
    evaluate_type (get_tenv cx) t = SOME tv /\
    type_step_offset cenv t sb = SOME (k,et) ==>
    ?etv. mem_step_offset tv sb = SOME (k,etv) /\
          evaluate_type (get_tenv cx) et = SOME etv
Proof
  cheat
QED

(* A path's offset in a declared type is its offset in the type value. *)
Theorem type_path_offset_mem:
  !path cenv cx env es t tv k pt.
    expr_sim_inv cenv cx env es /\
    evaluate_type (get_tenv cx) t = SOME tv /\
    type_path_offset cenv t path = SOME (k,pt) ==>
    ?ptv. mem_path_offset tv path = SOME (k,ptv) /\
          evaluate_type (get_tenv cx) pt = SOME ptv
Proof
  cheat
QED

Theorem fields_layout_alookup[local]:
  !flds fs fld ftv.
    fields_layout flds fs /\ ALOOKUP fs fld = SOME ftv ==>
    ?fty fsz. ALOOKUP flds fld = SOME (fty,fsz)
Proof
  cheat
QED

(* One step over a type value is the same step over the declared type it
   evaluates from. *)
Theorem mem_step_offset_type[local]:
  !cenv cx env es t tv sb k etv.
    expr_sim_inv cenv cx env es /\
    evaluate_type (get_tenv cx) t = SOME tv /\
    mem_step_offset tv sb = SOME (k,etv) ==>
    ?et. type_step_offset cenv t sb = SOME (k,et) /\
         evaluate_type (get_tenv cx) et = SOME etv
Proof
  cheat
QED

(* A path's offset in a type value is its offset in the declared type the
   type value evaluates from. *)
Theorem mem_path_offset_type:
  !path cenv cx env es t tv k ptv.
    expr_sim_inv cenv cx env es /\
    evaluate_type (get_tenv cx) t = SOME tv /\
    mem_path_offset tv path = SOME (k,ptv) ==>
    ?pt. type_path_offset cenv t path = SOME (k,pt) /\
         evaluate_type (get_tenv cx) pt = SOME ptv
Proof
  cheat
QED

(* A dynamic array where local_path_at puts it in a local has its length
   word exempt in locals_kept. *)
Theorem local_path_at_dynarray_len_at:
  !cenv cx env es n k etv m.
    expr_sim_inv cenv cx env es /\
    local_path_at cenv cx n k (ArrayTV etv (Dynamic m)) ==>
    dynarray_len_at cenv n k
Proof
  cheat
QED

(* A value with no dynamic array in it, where local_path_at puts it in a
   local, is apart from every length word locals_kept exempts there. *)
Theorem local_path_at_dynarray_apart:
  !cenv cx env es n k tv k'.
    expr_sim_inv cenv cx env es /\ local_path_at cenv cx n k tv /\
    dynarray_free tv /\ dynarray_len_at cenv n k' ==>
    k + type_memory_size tv <= k' \/ k' + 32 <= k
Proof
  cheat
QED

(* The same where local_val_at puts a well-formed value. *)
Theorem local_val_at_dynarray_apart:
  !cenv cx env es n k tv v k'.
    expr_sim_inv cenv cx env es /\ local_val_at cenv cx n k tv v /\
    val_wf tv v /\ dynarray_free tv /\ dynarray_len_at cenv n k' ==>
    k + val_footprint tv v <= k' \/ k' + 32 <= k
Proof
  cheat
QED











(* ===== A struct field in storage ===== *)

Theorem read_slots_n2w[local]:
  !n o1 o2 storage.
    (n2w o1 : bytes32) = n2w o2 ==>
    read_slots storage o1 n = read_slots storage o2 n
Proof
  cheat
QED

(* Decoding reads storage at offsets only through n2w, so an offset that
   wraps decodes the same. *)
Theorem decode_value_n2w:
  (!storage o1 tv o2. (n2w o1 : bytes32) = n2w o2 ==>
     decode_value storage o1 tv = decode_value storage o2 tv) /\
  (!storage o1 tvs o2. (n2w o1 : bytes32) = n2w o2 ==>
     decode_tuple storage o1 tvs = decode_tuple storage o2 tvs) /\
  (!storage o1 tv n o2. (n2w o1 : bytes32) = n2w o2 ==>
     decode_static_array storage o1 tv n =
     decode_static_array storage o2 tv n) /\
  (!storage o1 tv n o2. (n2w o1 : bytes32) = n2w o2 ==>
     decode_dyn_array storage o1 tv n = decode_dyn_array storage o2 tv n) /\
  (!storage o1 fs o2. (n2w o1 : bytes32) = n2w o2 ==>
     decode_struct storage o1 fs = decode_struct storage o2 fs)
Proof
  cheat
QED

Theorem decode_struct_field:
  !fs storage off vals id foff ftv.
    decode_struct storage off fs = SOME vals /\
    struct_field_slot fs id = SOME (foff, ftv) ==>
    ?fv. decode_value storage (off + foff) ftv = SOME fv /\
         ALOOKUP vals id = SOME fv
Proof
  cheat
QED

Theorem read_storage_slot_field:
  !cx tr slot fs es v es1 id foff ftv.
    read_storage_slot cx tr slot (StructTV fs) es = (INL v, es1) /\
    struct_field_slot fs id = SOME (foff, ftv) ==>
    ?vals fv. v = StructV vals /\ ALOOKUP vals id = SOME fv /\
              read_storage_slot cx tr (slot + n2w foff) ftv es = (INL fv, es1)
Proof
  cheat
QED

(* ===== The source's selection ===== *)

Theorem evaluate_subscripts_snoc_attr:
  !path tv a vals id fv.
    evaluate_subscripts tv a path = INL (StructV vals) /\
    ALOOKUP vals id = SOME fv ==>
    evaluate_subscripts tv a (path ++ [AttrSubscript id]) = INL fv
Proof
  cheat
QED

Theorem evaluate_subscripts_append_err:
  !path tv a err sfx.
    evaluate_subscripts tv a path = INR err ==>
    evaluate_subscripts tv a (path ++ sfx) = INR err
Proof
  cheat
QED

Theorem read_popped_snoc_attr:
  !hist tv path vals id fv.
    read_popped tv path hist = SOME (StructV vals) /\
    ALOOKUP vals id = SOME fv /\
    (!v'. ~MEM (path ++ [AttrSubscript id], v') hist) ==>
    read_popped tv (path ++ [AttrSubscript id]) hist = SOME fv
Proof
  cheat
QED

Theorem read_memory_path_snoc_attr:
  !entry path vals id fv.
    read_memory_path entry path = INL (StructV vals) /\
    ALOOKUP vals id = SOME fv /\
    (!err v'. evaluate_subscripts entry.type entry.value path = INR err ==>
              ~MEM (path ++ [AttrSubscript id], v') entry.popped) ==>
    read_memory_path entry (path ++ [AttrSubscript id]) = INL fv
Proof
  cheat
QED

(* The base's result is a local's place that memory no longer holds, so
   read_memory_path reads the field from the popped history, and that
   history has a snapshot exactly at the field: read_popped may read the
   snapshot there. *)
Definition popped_at_field_def:
  popped_at_field (PlaceR (MemoryPlace x path)) id (es:evaluation_state) =
    (?entry err v'. lookup_scopes x es.scopes = SOME entry /\
                    evaluate_subscripts entry.type entry.value path = INR err /\
                    MEM (path ++ [AttrSubscript id], v') entry.popped) /\
  popped_at_field _ _ _ = F
End

(* Under popped_keys_indexed (an expr_sim_inv clause) no popped key is a
   field: every key ends in an array index. *)
Theorem popped_keys_indexed_not_at_field:
  !tv id es. popped_keys_indexed es.scopes ==> ~popped_at_field tv id es
Proof
  cheat
QED

(* select_attr_read for an immutable's place. *)
Theorem select_attr_read_immutable[local]:
  !cx ty src x path id es vals res es1.
    read_result cx (PlaceR (ImmutablePlace src x path)) es =
      (INL (StructV vals), es) /\
    select_result cx ty (PlaceR (ImmutablePlace src x path)) (AttrSubscript id)
      es = (res, es1) /\
    (!m. res <> INR (Error (TypeError m))) ==>
    es1 = es /\
    ?tv' fv. res = INL tv' /\ ALOOKUP vals id = SOME fv /\
             read_result cx tv' es = (INL fv, es)
Proof
  cheat
QED

(* Selecting a field of a result whose read is a struct: unless the
   selection raises a type error, it succeeds without changing the state,
   and its read is the field. *)
Theorem select_attr_read:
  !cx ty tv id es vals res es1.
    read_result cx tv es = (INL (StructV vals), es) /\
    select_result cx ty tv (AttrSubscript id) es = (res, es1) /\
    ~popped_at_field tv id es /\
    (!m. res <> INR (Error (TypeError m))) ==>
    es1 = es /\
    ?tv' fv. res = INL tv' /\ ALOOKUP vals id = SOME fv /\
             read_result cx tv' es = (INL fv, es)
Proof
  cheat
QED

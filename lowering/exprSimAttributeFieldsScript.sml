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
 *   fields_in_memory_field, fields_val_wf_field, struct_field_offset_le,
 *   struct_field_offset_slots_eq — a field of a laid out struct
 *   read_storage_slot_field      — a field of a struct read from storage
 *   popped_at_field, select_attr_read — the source's selection
 *   popped_keys_indexed_not_at_field — popped_at_field never holds where
 *                                  expr_sim_inv does
 *   slot_count_of_memory_size    — a type's slots are its memory size
 *                                  rounded up to words
 *   type_memory_size_slots, decode_value_n2w, decode_struct_field,
 *   evaluate_subscripts_snoc_attr, evaluate_subscripts_append_err,
 *   read_popped_snoc_attr, read_memory_path_snoc_attr — steps of the
 *                                  field reads, exported for reuse
 *
 * Helpers: fields_layout_zip, read_slots_n2w, select_attr_read_immutable
 *
 * select_attr_read leaves out a local's place that memory no longer holds
 * and whose popped history has a snapshot at the field itself
 * (popped_at_field): read_popped may read the snapshot there, not the field
 * of the struct read at the place.
 *)

Theory exprSimAttributeFields
Ancestors
  list rich_list finite_map pair
  exprSimHyps compileEnv valueEncoding
  vyperAST vyperInterpreter vyperState vyperStorage vyperValue
  vyperTyping vyperTypeSystem vyperTypeExprSoundness
Libs
  pairLib

(* ===== Struct layout ===== *)

Theorem type_memory_size_slots:
  (!tv. type_memory_size tv = 32 * type_slot_size tv) /\
  (!tvs. type_memory_size_list tvs = 32 * type_slot_size_list tvs) /\
  (!fields. type_memory_size_fields fields = 32 * type_slot_size_fields fields)
Proof
  ho_match_mp_tac type_memory_size_ind >>
  simp[type_memory_size_def, type_slot_size_def,
       arithmeticTheory.LEFT_ADD_DISTRIB]
QED

Theorem slot_count_of_memory_size:
  !tv. (type_memory_size tv + 31) DIV 32 = type_slot_size tv
Proof
  rw[type_memory_size_slots] >>
  once_rewrite_tac[arithmeticTheory.MULT_COMM] >>
  irule arithmeticTheory.DIV_MULT >> simp[]
QED

(* The compile environment's fields of a struct, field by field: the same
   name and type_memory_size of the evaluated field type as size. *)
Definition fields_layout_def:
  fields_layout (fields : (string # type # num) list)
                (fs : (string # type_value) list) <=>
    LIST_REL (\(n,fty,sz) (n',tv). n = n' /\ sz = type_memory_size tv)
      fields fs
End

Theorem fields_layout_zip[local]:
  !fields tvs.
    OPT_MMAP (evaluate_type tenv) (MAP (FST o SND) fields) = SOME tvs /\
    EVERY (\(name, ty, sz). !tv. evaluate_type tenv ty = SOME tv ==>
                                 sz = type_memory_size tv) fields ==>
    fields_layout fields (ZIP (MAP FST fields, tvs))
Proof
  simp[fields_layout_def] >>
  Induct >> simp[] >> PairCases >> rpt strip_tac >> gvs[]
QED

Theorem struct_fields_layout:
  !cenv cx env es sid stv.
    expr_sim_inv cenv cx env es /\
    evaluate_type (get_tenv cx) (StructT sid) = SOME stv ==>
    ?fs. stv = StructTV fs /\
         fields_layout
           (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fs
Proof
  rpt gen_tac >> strip_tac >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx)` by
    gvs[expr_sim_inv_def] >>
  qpat_x_assum `sfields_tenv_consistent _ _` mp_tac >>
  simp[sfields_tenv_consistent_def] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  `EVERY (\(fname, fty, sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
            sz = type_memory_size tv) fields` by
    (fs[expr_sim_inv_def] >> metis_tac[]) >>
  simp[get_struct_fields_def] >>
  qpat_x_assum `MAP FST fields = _` (SUBST1_TAC o SYM) >>
  irule fields_layout_zip >> simp[] >>
  drule (cj 2 evaluate_type_mono) >> strip_tac >>
  gvs[vyperValueTheory.evaluate_types_OPT_MMAP] >>
  qexists_tac `get_tenv cx` >> simp[]
QED

Theorem fields_in_memory_field:
  !fields fs vals off mem id fv ftv.
    fields_layout fields fs /\ struct_has_type fs vals /\
    fields_in_memory vals fs off mem /\
    ALOOKUP vals id = SOME fv /\ ALOOKUP fs id = SOME ftv ==>
    val_in_memory ftv fv (off + struct_field_offset fields id) mem
Proof
  simp[fields_layout_def] >>
  Induct >> simp[] >> PairCases >> Cases >> simp[] >>
  PairCases_on `h` >> Cases >> simp[value_has_type_def] >>
  PairCases_on `h` >>
  simp[value_has_type_def, val_in_memory_def, struct_field_offset_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  Cases_on `h0 = id` >> gvs[] >>
  first_x_assum drule_all >> simp[]
QED

Theorem fields_val_wf_field:
  !vals fs id fv ftv.
    struct_has_type fs vals /\ fields_val_wf vals fs /\
    ALOOKUP vals id = SOME fv /\ ALOOKUP fs id = SOME ftv ==>
    val_wf ftv fv
Proof
  Induct >> simp[] >> PairCases >> Cases >> simp[value_has_type_def] >>
  PairCases_on `h` >> simp[value_has_type_def, val_wf_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  Cases_on `h0 = id` >> gvs[] >> metis_tac[]
QED

Theorem struct_field_offset_le:
  !fields fs id ftv.
    fields_layout fields fs /\ ALOOKUP fs id = SOME ftv ==>
    struct_field_offset fields id + type_memory_size ftv <=
      type_memory_size_fields fs
Proof
  simp[fields_layout_def] >>
  Induct >> simp[] >> PairCases >> Cases >> simp[] >>
  PairCases_on `h` >>
  simp[struct_field_offset_def, type_memory_size_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  Cases_on `h0 = id` >> gvs[] >>
  first_x_assum drule_all >> simp[]
QED

Theorem struct_field_offset_slots_eq:
  !fields fs id off ftv.
    fields_layout fields fs /\ struct_field_slot fs id = SOME (off, ftv) ==>
    struct_field_offset_slots fields id = off
Proof
  simp[fields_layout_def] >>
  Induct >> simp[struct_field_slot_def] >> PairCases >> Cases >>
  simp[struct_field_slot_def] >>
  PairCases_on `h` >>
  simp[struct_field_offset_slots_def, struct_field_slot_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  Cases_on `h0 = id` >> gvs[slot_count_of_memory_size] >>
  rename1 `struct_field_slot t id = SOME z` >> PairCases_on `z` >> gvs[] >>
  first_x_assum drule_all >> simp[]
QED

(* ===== A struct field in storage ===== *)

Theorem read_slots_n2w[local]:
  !n o1 o2 storage.
    (n2w o1 : bytes32) = n2w o2 ==>
    read_slots storage o1 n = read_slots storage o2 n
Proof
  Induct >> rpt strip_tac >> asm_simp_tac std_ss [read_slots_def] >>
  AP_TERM_TAC >> first_x_assum irule >>
  once_rewrite_tac[GSYM wordsTheory.word_add_n2w] >> asm_rewrite_tac[]
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
  ho_match_mp_tac decode_value_ind >> rpt conj_tac >> rpt gen_tac >>
  rpt strip_tac >>
  `!k. (n2w (o1 + k) : bytes32) = n2w (o2 + k)` by
    (gen_tac >> once_rewrite_tac[GSYM wordsTheory.word_add_n2w] >>
     asm_rewrite_tac[]) >>
  `!n. read_slots storage (o1 + 1) n = read_slots storage (o2 + 1) n` by
    metis_tac[read_slots_n2w] >>
  (* an induction hypothesis at the same offset: rewrite with it *)
  rpt (qpat_x_assum `!x. n2w o1 = n2w x ==> _` (fn ih =>
         qpat_assum `n2w o1 = n2w o2` (fn obj =>
           assume_tac (MP (SPEC ``o2:num`` ih) obj)))) >>
  once_rewrite_tac[decode_value_def] >>
  asm_rewrite_tac[read_slot_def, decode_dyn_bytes_def, LET_THM] >>
  (* a dynamic array's elements, after its length word *)
  TRY (BETA_TAC >> IF_CASES_TAC >> asm_rewrite_tac[] >>
       qpat_x_assum `!len. _ ==> _`
         (qspec_then `w2n (lookup_storage (n2w o2) storage)` mp_tac) >>
       asm_rewrite_tac[read_slot_def] >>
       disch_then (qspec_then `o2 + 1` mp_tac) >>
       asm_rewrite_tac[] >> disch_then (fn th => rewrite_tac[th]) >> NO_TAC) >>
  (* the rest of a tuple, array or struct, after its first component *)
  Cases_on `decode_value storage o2 tv` >>
  asm_rewrite_tac[optionTheory.option_case_def] >>
  rename1 `decode_value storage o2 tv = SOME dv` >>
  `decode_value storage o1 tv = SOME dv` by asm_rewrite_tac[] >>
  first_x_assum drule >>
  disch_then (qspec_then `o2 + type_slot_size tv` mp_tac) >>
  asm_rewrite_tac[] >> disch_then (fn th => rewrite_tac[th])
QED

Theorem decode_struct_field:
  !fs storage off vals id foff ftv.
    decode_struct storage off fs = SOME vals /\
    struct_field_slot fs id = SOME (foff, ftv) ==>
    ?fv. decode_value storage (off + foff) ftv = SOME fv /\
         ALOOKUP vals id = SOME fv
Proof
  Induct >> simp[struct_field_slot_def] >> PairCases >>
  simp[Once decode_value_def, struct_field_slot_def, AllCaseEqs()] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  Cases_on `h0 = id` >> gvs[] >>
  rename1 `struct_field_slot fs id = SOME z` >> PairCases_on `z` >> gvs[] >>
  first_x_assum drule_all >> simp[]
QED

Theorem read_storage_slot_field:
  !cx tr slot fs es v es1 id foff ftv.
    read_storage_slot cx tr slot (StructTV fs) es = (INL v, es1) /\
    struct_field_slot fs id = SOME (foff, ftv) ==>
    ?vals fv. v = StructV vals /\ ALOOKUP vals id = SOME fv /\
              read_storage_slot cx tr (slot + n2w foff) ftv es = (INL fv, es1)
Proof
  rpt gen_tac >> Cases_on `tr` >>
  simp[read_storage_slot_def, get_storage_backend_def,
       get_transient_storage_def, get_accounts_def, bind_def, return_def] >>
  qmatch_goalsub_abbrev_tac `decode_value stor` >>
  simp[Once decode_value_def] >>
  Cases_on `decode_struct stor (w2n slot) fs` >>
  simp[lift_option_def, raise_def, return_def] >>
  rpt strip_tac >> gvs[] >>
  drule_all decode_struct_field >> strip_tac >> simp[] >>
  `decode_value stor (w2n (slot + n2w foff)) ftv =
   decode_value stor (w2n slot + foff) ftv` by
    (irule (cj 1 decode_value_n2w) >>
     rewrite_tac[GSYM wordsTheory.word_add_n2w, wordsTheory.n2w_w2n]) >>
  simp[lift_option_def, return_def]
QED

(* ===== The source's selection ===== *)

Theorem evaluate_subscripts_snoc_attr:
  !path tv a vals id fv.
    evaluate_subscripts tv a path = INL (StructV vals) /\
    ALOOKUP vals id = SOME fv ==>
    evaluate_subscripts tv a (path ++ [AttrSubscript id]) = INL fv
Proof
  Induct
  >- (rw[evaluate_subscripts_def] >> simp[evaluate_subscripts_def]) >>
  Cases >> TRY (rename1 `ValueSubscript x` >> Cases_on `x`) >>
  rpt gen_tac >>
  TRY (rename1 `AttrSubscript fname :: _` >> Cases_on `a`) >>
  simp[evaluate_subscripts_def] >> strip_tac >>
  gvs[AllCaseEqs()] >> res_tac >> simp[]
QED

Theorem evaluate_subscripts_append_err:
  !path tv a err sfx.
    evaluate_subscripts tv a path = INR err ==>
    evaluate_subscripts tv a (path ++ sfx) = INR err
Proof
  Induct >- simp[evaluate_subscripts_def] >>
  Cases >> TRY (rename1 `ValueSubscript x` >> Cases_on `x`) >>
  rpt gen_tac >>
  TRY (rename1 `AttrSubscript fname :: _` >> Cases_on `a`) >>
  simp[evaluate_subscripts_def] >> strip_tac >>
  gvs[AllCaseEqs()] >> res_tac >> simp[]
QED

Theorem read_popped_snoc_attr:
  !hist tv path vals id fv.
    read_popped tv path hist = SOME (StructV vals) /\
    ALOOKUP vals id = SOME fv /\
    (!v'. ~MEM (path ++ [AttrSubscript id], v') hist) ==>
    read_popped tv (path ++ [AttrSubscript id]) hist = SOME fv
Proof
  Induct >> simp[read_popped_def] >> PairCases >> rpt gen_tac >>
  simp[read_popped_def] >> strip_tac >>
  Cases_on `IS_PREFIX path h0` >> gvs[]
  >- (`IS_PREFIX (path ++ [AttrSubscript id]) h0` by
        metis_tac[IS_PREFIX_TRANS, IS_PREFIX_APPEND3] >>
      `LENGTH h0 <= LENGTH path` by metis_tac[IS_PREFIX_LENGTH] >>
      simp[DROP_APPEND1] >>
      Cases_on `subscripts_type tv h0` >> gvs[] >>
      rename1 `evaluate_subscripts ptv h1 (DROP _ path)` >>
      Cases_on `evaluate_subscripts ptv h1 (DROP (LENGTH h0) path)` >> gvs[]
      >- (drule_all evaluate_subscripts_snoc_attr >> simp[]) >>
      drule evaluate_subscripts_append_err >> simp[]) >>
  `~IS_PREFIX (path ++ [AttrSubscript id]) h0` by
    (strip_tac >> gvs[GSYM SNOC_APPEND, isPREFIX_SNOC_EQ] >> metis_tac[]) >>
  simp[]
QED

Theorem read_memory_path_snoc_attr:
  !entry path vals id fv.
    read_memory_path entry path = INL (StructV vals) /\
    ALOOKUP vals id = SOME fv /\
    (!err v'. evaluate_subscripts entry.type entry.value path = INR err ==>
              ~MEM (path ++ [AttrSubscript id], v') entry.popped) ==>
    read_memory_path entry (path ++ [AttrSubscript id]) = INL fv
Proof
  rpt gen_tac >> simp[read_memory_path_def] >>
  Cases_on `evaluate_subscripts entry.type entry.value path` >> simp[] >>
  strip_tac >> gvs[]
  >- (drule_all evaluate_subscripts_snoc_attr >> simp[]) >>
  gvs[AllCaseEqs()] >>
  drule evaluate_subscripts_append_err >> simp[] >> strip_tac >>
  drule_all read_popped_snoc_attr >> simp[]
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
  rpt gen_tac >> strip_tac >> Cases_on `tv` >> simp[popped_at_field_def] >>
  rename1 `PlaceR pl` >> Cases_on `pl` >> simp[popped_at_field_def] >>
  rpt strip_tac >>
  drule vyperLookupTheory.lookup_scopes_find_containing_scope >> strip_tac >>
  drule vyperLookupTheory.find_containing_scope_structure >> strip_tac >>
  gvs[popped_keys_indexed_def] >>
  qpat_x_assum `!id entry. FLOOKUP env id = _ ==> _` drule >> strip_tac >>
  qpat_x_assum `EVERY _ (MAP FST _)`
    (mp_tac o SIMP_RULE (srw_ss()) [EVERY_MEM, MEM_MAP, PULL_EXISTS]) >>
  disch_then drule >> simp[GSYM SNOC_APPEND, SNOC_11]
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
  Cases_on `ALOOKUP vals id` >>
  simp[evaluate_subscripts_def, raise_def, return_def] >>
  rpt strip_tac >> gvs[evaluate_subscripts_def, return_def, raise_def] >>
  drule_all evaluate_subscripts_snoc_attr >>
  simp[read_result_def, read_place_def, bind_def, return_def,
       lift_option_type_def, lift_sum_def]
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
  rpt gen_tac >> Cases_on `tv`
  >~ [`Value v`]
  >- (simp[read_result_def, select_result_def, return_def, bind_def,
           lift_option_type_def, lift_sum_def] >>
      strip_tac >> gvs[] >>
      Cases_on `evaluate_type (get_tenv cx) ty` >>
      gvs[raise_def, return_def, evaluate_subscripts_def] >>
      Cases_on `ALOOKUP vals id` >>
      gvs[raise_def, return_def, evaluate_subscripts_def, read_result_def])
  >~ [`HashMapRef`] >- simp[read_result_def, raise_def] >>
  rename1 `PlaceR p` >> Cases_on `p`
  >~ [`StoragePlace tr slot ptv`]
  >- (simp[read_result_def, read_place_def, select_result_def,
           extend_place_def, bind_def, return_def] >>
      strip_tac >>
      Cases_on `ptv` >> gvs[extend_storage_place_def, raise_def] >>
      rename1 `struct_field_slot fs id` >>
      Cases_on `struct_field_slot fs id` >>
      gvs[lift_option_type_def, raise_def, return_def, bind_def] >>
      rename1 `struct_field_slot fs id = SOME fo` >> PairCases_on `fo` >>
      gvs[return_def, read_result_def, read_place_def] >>
      drule_all read_storage_slot_field >> strip_tac >> gvs[])
  >~ [`MemoryPlace x path`]
  >- (simp[read_result_def, read_place_def, select_result_def,
           extend_place_def, place_type_value_def, get_scopes_def,
           extend_memory_place_def, bind_def, ignore_bind_def, return_def,
           lift_option_type_def, lift_sum_def, popped_at_field_def] >>
      Cases_on `lookup_scopes x es.scopes` >> simp[raise_def] >>
      rename1 `lookup_scopes x es.scopes = SOME entry` >>
      Cases_on `read_memory_path entry path` >> simp[raise_def, return_def] >>
      Cases_on `subscripts_type entry.type path` >>
      simp[raise_def, return_def] >>
      Cases_on `ALOOKUP vals id` >>
      simp[evaluate_subscripts_def, raise_def, return_def] >>
      rpt strip_tac >> gvs[evaluate_subscripts_def, return_def, raise_def] >>
      drule_all read_memory_path_snoc_attr >>
      simp[read_result_def, read_place_def, get_scopes_def, bind_def,
           return_def, lift_option_type_def, lift_sum_def]) >>
  rename1 `ImmutablePlace src x path` >> strip_tac >>
  drule_all select_attr_read_immutable >> simp[]
QED

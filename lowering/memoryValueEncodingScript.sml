(* TOP-LEVEL: complete memory layouts imply the canonical valueEncoding
   relation for source-typed values, including packed tuples and structs.
   Sparse fixed arrays require source typing's bounded, distinct keys.
   No ABI encoder or encoder recursion is involved. *)
Theory memoryValueEncoding
Ancestors
  memoryValueDefs valueEncoding vyperTyping vyperValue list alist
  arithmetic pair sorting

(* ===== Canonical list interfaces ===== *)

Theorem canonical_elements_indexed:
  !vs offset tv mem.
    elems_in_memory vs offset tv mem <=>
    !i. i < LENGTH vs ==>
      val_in_memory tv (EL i vs) (offset + i * type_memory_size tv) mem
Proof
  Induct_on `vs` >> simp[val_in_memory_def] >> rpt gen_tac >> eq_tac
  >- (strip_tac >> Cases_on `i` >> simp[ADD_CLAUSES, MULT_CLAUSES] >>
      fs[ADD_ASSOC]) >>
  strip_tac >> conj_tac
  >- (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  qx_gen_tac `i` >> strip_tac >>
  first_x_assum (qspec_then `SUC i` mp_tac) >>
  asm_simp_tac std_ss [EL, TL, LESS_MONO_EQ, MULT_CLAUSES, AC ADD_COMM ADD_ASSOC]
QED

Theorem canonical_sparse_entries:
  !sparse offset tv mem.
    kvs_in_memory sparse offset tv mem <=>
    !k v. MEM (k,v) sparse ==>
      val_in_memory tv v (offset + k * type_memory_size tv) mem
Proof
  Induct_on `sparse` >> simp[val_in_memory_def] >>
  Cases >> simp[val_in_memory_def] >> metis_tac[]
QED

(* Defaults need no source-type well-formedness assumption: the base cases
   already use the canonical relation, even for unusual type descriptors. *)
Theorem default_array_memory_encoding:
  !tv bound.
    (!offset mem. memory_value_rel tv (default_value tv) offset mem ==>
      val_in_memory tv (default_value tv) offset mem) ==>
    !offset mem.
      memory_value_rel (ArrayTV tv bound) (default_value (ArrayTV tv bound)) offset mem ==>
      val_in_memory (ArrayTV tv bound) (default_value (ArrayTV tv bound)) offset mem
Proof
  rpt gen_tac >> strip_tac >> Cases_on `bound` >>
  simp[default_value_def, memory_value_rel_def, val_in_memory_def] >>
  metis_tac[]
QED

Theorem default_memory_encoding:
  (!tv offset mem.
    memory_value_rel tv (default_value tv) offset mem ==>
    val_in_memory tv (default_value tv) offset mem) /\
  (!tvs offset mem.
    memory_fields_rel tvs (MAP (\(name,tv). (name,default_value tv)) tvs) offset mem ==>
    fields_in_memory (MAP (\(name,tv). (name,default_value tv)) tvs) tvs offset mem) /\
  (!p:string # type_value. !offset mem.
    memory_value_rel (SND p) (default_value (SND p)) offset mem ==>
    val_in_memory (SND p) (default_value (SND p)) offset mem) /\
  (!tvs offset mem.
    memory_tuple_rel tvs (MAP default_value tvs) offset mem ==>
    tuple_in_memory (MAP default_value tvs) tvs offset mem)
Proof
  ho_match_mp_tac (TypeBase.induction_of ``:type_value``) >>
  simp[default_value_def, default_value_struct_MAP, default_value_tuple_MAP,
       memory_value_rel_def, val_in_memory_def, default_array_memory_encoding] >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  TRY (qmatch_asmsub_rename_tac `memory_value_rel (SND entry) _ _ _` >>
       PairCases_on `entry` >> fs[memory_value_rel_def, val_in_memory_def]) >>
  metis_tac[]
QED

(* ===== Typed bridge ===== *)

Theorem typed_sparse_entry:
  !sparse tv bound k v.
    sparse_has_type tv bound sparse /\ MEM (k,v) sparse ==>
    k < bound /\ value_has_type tv v
Proof
  Induct_on `sparse` >> simp[value_has_type_def] >>
  Cases >> simp[value_has_type_def] >> metis_tac[]
QED

Definition memory_encoding_bridge_def:
  memory_encoding_bridge tv <=>
    !v offset mem. value_has_type tv v /\ memory_value_rel tv v offset mem ==>
      val_in_memory tv v offset mem
End

Definition memory_fields_encoding_bridge_def:
  memory_fields_encoding_bridge tvs <=>
    !vs offset mem. struct_has_type tvs vs /\ memory_fields_rel tvs vs offset mem ==>
      fields_in_memory vs tvs offset mem
End

Definition memory_tuple_encoding_bridge_def:
  memory_tuple_encoding_bridge tvs <=>
    !vs offset mem. values_have_types tvs vs /\ memory_tuple_rel tvs vs offset mem ==>
      tuple_in_memory vs tvs offset mem
End

Theorem typed_fixed_memory_encoding:
  !tv bound sparse offset mem.
    memory_encoding_bridge tv /\
    value_has_type (ArrayTV tv (Fixed bound)) (ArrayV (SArrayV sparse)) /\
    memory_value_rel (ArrayTV tv (Fixed bound)) (ArrayV (SArrayV sparse)) offset mem ==>
    val_in_memory (ArrayTV tv (Fixed bound)) (ArrayV (SArrayV sparse)) offset mem
Proof
  rpt gen_tac >> simp_tac bool_ss [value_has_type_def, memory_value_rel_def] >>
  strip_tac >> simp[val_in_memory_def, canonical_sparse_entries] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `k < bound /\ value_has_type tv v` by (drule_all typed_sparse_entry >> simp[]) >>
      `ALOOKUP sparse k = SOME v` by
        (irule ALOOKUP_ALL_DISTINCT_MEM >> simp[SORTED_lt_ALL_DISTINCT]) >>
      qpat_x_assum `!i. i < bound ==> _` (qspec_then `k` mp_tac) >>
      simp[] >> strip_tac >> fs[memory_encoding_bridge_def]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!i. i < bound ==> _` (qspec_then `i` mp_tac) >>
  simp[] >> strip_tac >> irule (CONJUNCT1 default_memory_encoding) >> simp[]
QED

Theorem typed_dynamic_memory_encoding:
  !tv bound vs offset mem.
    memory_encoding_bridge tv /\
    value_has_type (ArrayTV tv (Dynamic bound)) (ArrayV (DynArrayV vs)) /\
    memory_value_rel (ArrayTV tv (Dynamic bound)) (ArrayV (DynArrayV vs)) offset mem ==>
    val_in_memory (ArrayTV tv (Dynamic bound)) (ArrayV (DynArrayV vs)) offset mem
Proof
  rpt gen_tac >> simp_tac bool_ss [value_has_type_def, memory_value_rel_def] >>
  strip_tac >> simp[val_in_memory_def, canonical_elements_indexed] >>
  rpt gen_tac >> strip_tac >>
  `value_has_type tv (EL i vs)` by fs[all_have_type_EVERY, EVERY_EL] >>
  fs[memory_encoding_bridge_def]
QED

Theorem memory_encoding_bridge_array:
  !tv bound. memory_encoding_bridge tv ==> memory_encoding_bridge (ArrayTV tv bound)
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [memory_encoding_bridge_def] >>
  Cases_on `bound` >> Cases_on `v` >> simp[value_has_type_def] >>
  rename1 `value_has_type _ (ArrayV array_value)` >> Cases_on `array_value` >>
  simp[value_has_type_def] >> rpt strip_tac >>
  FIRST [irule typed_fixed_memory_encoding, irule typed_dynamic_memory_encoding] >>
  simp[value_has_type_def]
QED

Theorem memory_encoding_bridge_struct:
  !tvs. memory_fields_encoding_bridge tvs ==> memory_encoding_bridge (StructTV tvs)
Proof
  simp_tac bool_ss [memory_encoding_bridge_def, memory_fields_encoding_bridge_def] >>
  rpt gen_tac >> strip_tac >> Cases_on `v` >>
  simp[value_has_type_def, memory_value_rel_def, val_in_memory_def]
QED

Theorem memory_encoding_bridge_tuple:
  !tvs. memory_tuple_encoding_bridge tvs ==> memory_encoding_bridge (TupleTV tvs)
Proof
  simp_tac bool_ss [memory_encoding_bridge_def, memory_tuple_encoding_bridge_def] >>
  rpt gen_tac >> strip_tac >> Cases_on `v` >> simp[value_has_type_def] >>
  rename1 `value_has_type _ (ArrayV array_value)` >> Cases_on `array_value` >>
  simp[value_has_type_def, memory_value_rel_def, val_in_memory_def]
QED

Theorem memory_fields_encoding_bridge_cons:
  !name tv tvs.
    memory_encoding_bridge tv /\ memory_fields_encoding_bridge tvs ==>
    memory_fields_encoding_bridge ((name,tv)::tvs)
Proof
  simp_tac bool_ss [memory_encoding_bridge_def, memory_fields_encoding_bridge_def] >>
  rpt gen_tac >> strip_tac >> Cases_on `vs` >> simp[value_has_type_def] >>
  rename1 `struct_has_type _ (entry::rest)` >> PairCases_on `entry` >>
  simp[value_has_type_def, memory_value_rel_def, val_in_memory_def]
QED

Theorem memory_tuple_encoding_bridge_cons:
  !tv tvs.
    memory_encoding_bridge tv /\ memory_tuple_encoding_bridge tvs ==>
    memory_tuple_encoding_bridge (tv::tvs)
Proof
  simp_tac bool_ss [memory_encoding_bridge_def, memory_tuple_encoding_bridge_def] >>
  rpt gen_tac >> strip_tac >> Cases_on `vs` >>
  simp[value_has_type_def, memory_value_rel_def, val_in_memory_def]
QED

Theorem memory_encoding_bridges:
  (!tv. memory_encoding_bridge tv) /\
  (!tvs. memory_fields_encoding_bridge tvs) /\
  (!p:string # type_value. memory_encoding_bridge (SND p)) /\
  (!tvs. memory_tuple_encoding_bridge tvs)
Proof
  ho_match_mp_tac (TypeBase.induction_of ``:type_value``) >>
  simp[memory_encoding_bridge_array, memory_encoding_bridge_struct,
       memory_encoding_bridge_tuple, memory_fields_encoding_bridge_cons,
       memory_tuple_encoding_bridge_cons] >>
  rpt conj_tac >> rpt gen_tac
  >- simp[memory_encoding_bridge_def, memory_value_rel_def]
  >- simp[memory_encoding_bridge_def, memory_value_rel_def]
  >- (simp_tac bool_ss [memory_encoding_bridge_def] >> Cases_on `v` >>
      simp[value_has_type_def, memory_value_rel_def, val_in_memory_def])
  >- (simp_tac bool_ss [memory_fields_encoding_bridge_def] >> Cases_on `vs` >>
      simp[value_has_type_def, val_in_memory_def])
  >- (strip_tac >> qmatch_asmsub_rename_tac `memory_encoding_bridge (SND entry)` >>
      PairCases_on `entry` >> fs[memory_fields_encoding_bridge_cons]) >>
  simp_tac bool_ss [memory_tuple_encoding_bridge_def] >> Cases_on `vs` >>
  simp[value_has_type_def, val_in_memory_def]
QED

(* Only prerequisites: complete layout and source value typing. In particular
   no type well-formedness, address bound, or encoder admissibility is needed. *)
Theorem memory_value_rel_val_in_memory =
  CONJUNCT1 memory_encoding_bridges |> REWRITE_RULE [memory_encoding_bridge_def];

Theorem memory_fields_rel_fields_in_memory =
  CONJUNCT1 (CONJUNCT2 memory_encoding_bridges) |>
    REWRITE_RULE [memory_fields_encoding_bridge_def];

Theorem memory_tuple_rel_tuple_in_memory =
  CONJUNCT2 (CONJUNCT2 (CONJUNCT2 memory_encoding_bridges)) |>
    REWRITE_RULE [memory_tuple_encoding_bridge_def];

Theorem memory_tuple_rel_val_in_memory:
  !tvs vs offset mem.
    memory_tuple_rel tvs vs offset mem /\ values_have_types tvs vs ==>
    val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) offset mem
Proof
  simp[val_in_memory_def] >> metis_tac[memory_tuple_rel_tuple_in_memory]
QED

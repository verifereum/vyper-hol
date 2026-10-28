(*
 * Encoding of aggregate literals in memory (#636)
 *
 * tuple_in_memory, elems_in_memory and kvs_in_memory on appended and
 * replicated lists, to build a tuple, struct or array literal's memory
 * child by child.
 *
 * TOP-LEVEL:
 *   fixed_array_from_dense — n dense elements are a Fixed n array
 *   tuple_in_memory_replicate_elems — a tuple of one type is
 *     elems_in_memory
 *   type_memory_size_list_replicate, OPT_MMAP_uniform_map — n copies of a
 *     type
 *
 * Helpers: elems_in_memory_EL, kvs_in_memory_every.
 *)
Theory exprSimAggregateEncoding
Ancestors
  valueEncodingProps valueEncodingProofs vyperValue list arithmetic pair

Theorem elems_in_memory_EL:
  !vs off tv mem i.
    elems_in_memory vs off tv mem /\ i < LENGTH vs ==>
    val_in_memory tv (EL i vs) (off + i * type_memory_size tv) mem
Proof
  Induct >> rewrite_tac[LENGTH, cj 14 valueEncodingTheory.val_in_memory_def,
                        cj 15 valueEncodingTheory.val_in_memory_def] >>
  rpt gen_tac >> Cases_on `i` >>
  simp[EL, MULT_CLAUSES, ADD_CLAUSES] >> rpt strip_tac >>
  first_x_assum drule >>
  disch_then (qspec_then `n` mp_tac) >>
  simp[AC ADD_ASSOC ADD_COMM]
QED

Theorem kvs_in_memory_every:
  !kvs off tv mem.
    kvs_in_memory kvs off tv mem <=>
    EVERY (\(i,v). val_in_memory tv v
                    (off + i * type_memory_size tv) mem) kvs
Proof
  Induct >> rewrite_tac[EVERY_DEF, cj 16 valueEncodingTheory.val_in_memory_def,
                        cj 17 valueEncodingTheory.val_in_memory_def] >>
  Cases_on `h` >> simp[cj 17 valueEncodingTheory.val_in_memory_def]
QED

Theorem fixed_array_from_dense:
  !vs n off tv mem.
    LENGTH vs = n /\ elems_in_memory vs off tv mem ==>
    val_in_memory (ArrayTV tv (Fixed n))
      (ArrayV (make_array_value tv (Fixed n) vs)) off mem
Proof
  rpt strip_tac >>
  rewrite_tac[make_array_value_def, valueEncodingPropsTheory.val_in_memory_sarray] >>
  conj_tac
  >- (rewrite_tac[kvs_in_memory_every, EVERY_MEM, FORALL_PROD] >>
      rpt strip_tac >> Cases_on `e` >>
      gvs[MEM_enumerate_static_array_iff] >>
      irule elems_in_memory_EL >> simp[] >> metis_tac[]) >>
  rpt strip_tac >>
  `i < LENGTH vs` by metis_tac[] >>
  drule enumerate_static_array_ALOOKUP >>
  disch_then (qspecl_then [`default_value tv`, `0`] mp_tac) >>
  simp[] >> strip_tac >>
  `EL i vs = default_value tv` by metis_tac[optionTheory.NOT_NONE_SOME] >>
  drule_all elems_in_memory_EL >> simp[]
QED

Theorem tuple_in_memory_replicate_elems:
  !vs p. tuple_in_memory vs (REPLICATE (LENGTH vs) tv) p mem <=>
    elems_in_memory vs p tv mem
Proof
  Induct >> simp[valueEncodingTheory.val_in_memory_def,
                 rich_listTheory.REPLICATE]
QED

Theorem type_memory_size_list_replicate:
  !n. type_memory_size_list (REPLICATE n tv) = n * type_memory_size tv
Proof
  Induct >> simp[valueEncodingTheory.type_memory_size_def,
                 rich_listTheory.REPLICATE, arithmeticTheory.MULT_CLAUSES]
QED

Theorem OPT_MMAP_uniform_map:
  !args. EVERY (\e. f e = ty) args /\ g ty = SOME tv ==>
    OPT_MMAP g (MAP f args) = SOME (REPLICATE (LENGTH args) tv)
Proof
  Induct >> simp[rich_listTheory.REPLICATE]
QED

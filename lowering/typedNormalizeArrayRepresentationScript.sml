(* Semantic reconstruction boundaries for typed normalization loops.
   Dense projection/introduction reuse elems_in_memory_EL/intro. *)
Theory typedNormalizeArrayRepresentation
Ancestors
  exprSimAggregateEncoding abiStaticSparseProps typedNormalizeFastRepresentation
  vyperTyping valueEncodingProps alist sorting list pair arithmetic

Theorem normalize_sparse_memory_index:
  ALL_DISTINCT (MAP FST kvs) /\
  EVERY (\kv. FST kv < n) kvs ==>
  (val_in_memory (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) b m <=>
   !j. j < n ==>
     val_in_memory tv
       (case ALOOKUP kvs j of SOME v => v | NONE => default_value tv)
       (b + j * type_memory_size tv) m)
Proof
  strip_tac >> fs[EVERY_MEM, FORALL_PROD] >>
  simp[valueEncodingPropsTheory.val_in_memory_sarray,
       kvs_in_memory_every, EVERY_MEM, FORALL_PROD] >>
  eq_tac
  >- (strip_tac >> gen_tac >> strip_tac >>
      Cases_on `ALOOKUP kvs j` >> gvs[] >>
      metis_tac[ALOOKUP_MEM]) >>
  strip_tac >> conj_tac
  >- (rpt strip_tac >>
      `ALOOKUP kvs p_1 = SOME p_2` by
        metis_tac[ALOOKUP_ALL_DISTINCT_MEM] >>
      `p_1 < n` by metis_tac[] >>
      first_x_assum (qspec_then `p_1` mp_tac) >> simp[]) >>
  rpt strip_tac >> first_x_assum (qspec_then `i` mp_tac) >> simp[]
QED

Theorem normalize_sparse_typed_keys:
  value_has_type (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) ==>
  ALL_DISTINCT (MAP FST kvs) /\ EVERY (\kv. FST kv < n) kvs
Proof
  simp[value_has_type_def] >> strip_tac >> conj_tac
  >- (irule SORTED_ALL_DISTINCT >> qexists_tac `$<` >>
      simp[relationTheory.irreflexive_def, relationTheory.transitive_def] >>
      metis_tac[LESS_TRANS]) >>
  simp[EVERY_MEM, FORALL_PROD] >> metis_tac[typed_sparse_key_bound]
QED

(* The loop may use the source default as its indexed semantic value.
   Reconstructing the destination additionally needs the absent-slot bridge. *)
Theorem normalize_sparse_destination_memory:
  ALL_DISTINCT (MAP FST kvs) /\ EVERY (\kv. FST kv < n) kvs /\
  (!j. j < n ==>
    val_in_memory dt
      (case ALOOKUP kvs j of SOME v => v | NONE => default_value st)
      (b + j * type_memory_size dt) m) /\
  (!p. val_in_memory dt (default_value st) p m ==>
        val_in_memory dt (default_value dt) p m) ==>
  val_in_memory (ArrayTV dt (Fixed n)) (ArrayV (SArrayV kvs)) b m
Proof
  strip_tac >>
  drule_all normalize_sparse_memory_index >> simp[] >>
  disch_then kall_tac >>
  gen_tac >> strip_tac >>
  qpat_x_assum `!j. j < n ==> _` (qspec_then `j` mp_tac) >>
  Cases_on `ALOOKUP kvs j` >> simp[] >> metis_tac[]
QED

Theorem normalize_dynamic_destination_memory:
  mem_word_at b m = n2w (LENGTH vs) /\
  (!j. j < LENGTH vs ==>
    val_in_memory tv (EL j vs) (b + 32 + j * type_memory_size tv) m) ==>
  val_in_memory (ArrayTV tv bd) (ArrayV (DynArrayV vs)) b m
Proof
  strip_tac >> simp[valueEncodingTheory.val_in_memory_def] >>
  irule elems_in_memory_intro >> simp[]
QED

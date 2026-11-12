(* Memory interpretation congruences, independent of ABI conversion. *)
Theory entryValueMemoryCongruence
Ancestors
  entrySparseMemory valueEncoding vyperValue list alist pair arithmetic valueEncodingDefs
  vyperTyping vyperValueOperation vyperAssignPreservesType


Theorem entry_elems_memory_congruence:
  LIST_REL (\v w. !p mem. val_in_memory tv v p mem <=>
                         val_in_memory tv w p mem) xs ys ==>
  !p mem. elems_in_memory xs p tv mem <=> elems_in_memory ys p tv mem
Proof
  qid_spec_tac `ys` >> Induct_on `xs` >> Cases_on `ys` >>
  simp[val_in_memory_def] >> metis_tac[]
QED

Theorem entry_sparse_memory_congruence:
  ALL_DISTINCT (MAP FST xs) /\ EVERY (\(i,v). i < n) xs /\
  ALL_DISTINCT (MAP FST ys) /\ EVERY (\(i,v). i < n) ys /\
  (!i p mem. i < n ==>
    (val_in_memory tv (case ALOOKUP xs i of NONE => default_value tv | SOME v => v) p mem <=>
     val_in_memory tv (case ALOOKUP ys i of NONE => default_value tv | SOME v => v) p mem)) ==>
  (val_in_memory (ArrayTV tv (Fixed n)) (ArrayV (SArrayV xs)) p mem <=>
   val_in_memory (ArrayTV tv (Fixed n)) (ArrayV (SArrayV ys)) p mem)
Proof
  strip_tac >> simp[entry_sparse_memory_indexed]
QED

Theorem entry_tuple_memory_congruence:
  LENGTH xs = LENGTH tvs /\ LENGTH ys = LENGTH tvs /\
  (!i p mem. i < LENGTH tvs ==>
    (val_in_memory (EL i tvs) (EL i xs) p mem <=>
     val_in_memory (EL i tvs) (EL i ys) p mem)) ==>
  !p mem. tuple_in_memory xs tvs p mem <=> tuple_in_memory ys tvs p mem
Proof
  map_every qid_spec_tac [`ys`, `xs`] >> Induct_on `tvs` >>
  Cases_on `xs` >> Cases_on `ys` >> simp[val_in_memory_def] >>
  rpt strip_tac >>
  rename1 `(val_in_memory etv x p mem /\ tuple_in_memory xt tvs _ mem) <=>
           (val_in_memory etv y p mem /\ tuple_in_memory yt tvs _ mem)` >>
  `!p mem. val_in_memory etv x p mem <=> val_in_memory etv y p mem` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `!p mem. tuple_in_memory xt tvs p mem <=> tuple_in_memory yt tvs p mem` by
    (first_x_assum irule >> simp[] >> rpt strip_tac >>
     qpat_x_assum `!i p mem. _` (qspec_then `SUC i` mp_tac) >> simp[]) >>
  simp[]
QED

Theorem entry_fields_memory_congruence:
  LENGTH xs = LENGTH fts /\ LENGTH ys = LENGTH fts /\
  (!i p mem. i < LENGTH fts ==>
    (val_in_memory (SND (EL i fts)) (SND (EL i xs)) p mem <=>
     val_in_memory (SND (EL i fts)) (SND (EL i ys)) p mem)) ==>
  !p mem. fields_in_memory xs fts p mem <=> fields_in_memory ys fts p mem
Proof
  strip_tac >> rewrite_tac[valueEncodingProofsTheory.fields_in_memory_tuple] >>
  irule entry_tuple_memory_congruence >> simp[EL_MAP]
QED

Theorem entry_typed_sparse_memory_indexed:
  value_has_type (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) ==>
  (val_in_memory (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) p mem <=>
   !i. i < n ==> val_in_memory tv
     (EL i (array_elements (ArrayTV tv (Fixed n)) (SArrayV kvs)))
     (p + i * type_memory_size tv) mem)
Proof
  strip_tac >> irule EQ_TRANS >>
  irule_at Any entry_sparse_memory_indexed >>
  gvs[value_has_type_def, array_elements_def] >>
  metis_tac[SORTED_lt_ALL_DISTINCT, sparse_has_type_all_less]
QED

Theorem entry_typed_sparse_element:
  well_formed_type_value tv /\
  value_has_type (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) /\ i < n ==>
  value_has_type tv (EL i (array_elements (ArrayTV tv (Fixed n)) (SArrayV kvs)))
Proof
  strip_tac >> gvs[array_elements_def] >>
  Cases_on `ALOOKUP kvs i` >> gvs[]
  >- metis_tac[default_value_well_typed] >>
  gvs[value_has_type_def] >> metis_tac[ALOOKUP_sparse_has_type]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then () else raise Fail "entry memory congruence inherited admission"
  end) [entry_elems_memory_congruence, entry_sparse_memory_congruence,
        entry_tuple_memory_congruence, entry_fields_memory_congruence,
        entry_typed_sparse_memory_indexed, entry_typed_sparse_element];

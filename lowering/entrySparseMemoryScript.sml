(* Indexed memory boundary for normalized sparse argument arrays. *)
Theory entrySparseMemory
Ancestors
  exprSimAggregateEncoding valueEncodingProofs valueEncodingProps
  valueEncoding vyperValue alist list pair arithmetic

Theorem entry_sparse_memory_indexed:
  ALL_DISTINCT (MAP FST kvs) /\ EVERY (\(i,v). i < n) kvs ==>
  (val_in_memory (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) p mem <=>
   !i. i < n ==> val_in_memory tv
     (case ALOOKUP kvs i of NONE => default_value tv | SOME v => v)
     (p + i * type_memory_size tv) mem)
Proof
  strip_tac >> rewrite_tac[val_in_memory_sarray] >> eq_tac
  >- (strip_tac >> rpt strip_tac >> Cases_on `ALOOKUP kvs i` >> simp[] >>
      metis_tac[kvs_in_memory_lookup]) >>
  strip_tac >> conj_tac
  >- (rewrite_tac[kvs_in_memory_every, EVERY_MEM, FORALL_PROD] >>
      rpt strip_tac >> Cases_on `e` >> rename1 `MEM (i,v) kvs` >>
      `ALOOKUP kvs i = SOME v` by
        metis_tac[ALOOKUP_ALL_DISTINCT_MEM] >>
      first_x_assum (qspec_then `i` mp_tac) >>
      gvs[EVERY_MEM, FORALL_PROD] >> metis_tac[]) >>
  rpt strip_tac >> first_x_assum (qspec_then `i` mp_tac) >> simp[]
QED

Theorem entry_sparse_memory_transport:
  ALL_DISTINCT (MAP FST xs) /\ EVERY (\(i,v). i < n) xs /\
  ALL_DISTINCT (MAP FST ys) /\ EVERY (\(i,v). i < n) ys /\
  (!i. i < n ==>
    (case ALOOKUP xs i of NONE => default_value tv | SOME v => v) =
    (case ALOOKUP ys i of NONE => default_value tv | SOME v => v)) ==>
  (val_in_memory (ArrayTV tv (Fixed n)) (ArrayV (SArrayV xs)) p mem <=>
   val_in_memory (ArrayTV tv (Fixed n)) (ArrayV (SArrayV ys)) p mem)
Proof
  strip_tac >> simp[entry_sparse_memory_indexed]
QED

Theorem entry_sparse_explicit_zero_memory:
  val_in_memory (ArrayTV (BaseTV (UintT 256)) (Fixed 1))
    (ArrayV (SArrayV [(0,IntV 0)])) p mem <=>
  val_in_memory (ArrayTV (BaseTV (UintT 256)) (Fixed 1))
    (ArrayV (SArrayV [])) p mem
Proof
  irule entry_sparse_memory_transport >>
  simp[vyperValueTheory.default_value_def]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then () else raise Fail "entry sparse memory inherited admission"
  end) [entry_sparse_memory_indexed, entry_sparse_memory_transport,
        entry_sparse_explicit_zero_memory];

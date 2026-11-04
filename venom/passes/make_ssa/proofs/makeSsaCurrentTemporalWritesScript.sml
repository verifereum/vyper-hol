(* Chronological algebra only: values may be dynamic origins, with no
   assumption that a static allocation event has executed. *)
Theory makeSsaCurrentTemporalWrites
Ancestors alist list

Definition current_chronological_writes_def:
  (current_chronological_writes [] m = m) /\
  (current_chronological_writes (w::ws) m =
    current_chronological_writes ws (w::m))
End

(* A snapshot read is distinct from the destination map. Cleanup uses m
   for both; a parallel PHI reads the fixed incoming snapshot. *)
Definition current_origin_copy_def:
  current_origin_copy incoming n dst m =
    case ALOOKUP incoming n of
      NONE => NONE
    | SOME origin => SOME ((dst,origin)::m)
End

Theorem current_chronological_writes_reverse:
  !ws m. current_chronological_writes ws m = REVERSE ws ++ m
Proof
  Induct >> simp[current_chronological_writes_def, REVERSE_DEF, APPEND_ASSOC]
QED

Theorem current_chronological_last_write:
  ALOOKUP (current_chronological_writes ws m) n =
    case ALOOKUP (REVERSE ws) n of
      NONE => ALOOKUP m n
    | SOME origin => SOME origin
Proof
  simp[current_chronological_writes_reverse, ALOOKUP_APPEND]
QED

Theorem current_chronological_no_write:
  !ws m. EVERY (\w. FST w <> n) ws ==>
    ALOOKUP (current_chronological_writes ws m) n = ALOOKUP m n
Proof
  Induct >> simp[current_chronological_writes_def] >>
  rpt gen_tac >> PairCases_on `h` >> simp[]
QED

Theorem current_chronological_append:
  !xs m ys. current_chronological_writes (xs ++ ys) m =
    current_chronological_writes ys (current_chronological_writes xs m)
Proof
  Induct >> simp[current_chronological_writes_def]
QED

Theorem current_origin_copy_missing:
  ALOOKUP incoming n = NONE ==>
  current_origin_copy incoming n dst m = NONE
Proof
  simp[current_origin_copy_def]
QED

Theorem current_origin_copy_present:
  ALOOKUP incoming n = SOME origin ==>
  current_origin_copy incoming n dst m = SOME ((dst,origin)::m)
Proof
  simp[current_origin_copy_def]
QED

Theorem current_origin_copy_lookup:
  ALOOKUP incoming n = SOME origin /\
  current_origin_copy incoming n dst m = SOME m' ==>
  ALOOKUP m' q = if q = dst then SOME origin else ALOOKUP m q
Proof
  simp[current_origin_copy_def] >> strip_tac >> gvs[] >>
  Cases_on `q = dst` >> simp[]
QED

Theorem current_singleton_copy_agreement:
  (selected = n \/ selected = dst) /\
  ALOOKUP snapshot n = SOME origin /\ ALOOKUP snapshot dst = SOME origin /\
  ALOOKUP m n = SOME origin ==>
  ALOOKUP snapshot selected = SOME origin /\
  current_origin_copy m n dst m = SOME ((dst,origin)::m) /\
  ALOOKUP ((dst,origin)::m) dst = SOME origin
Proof
  strip_tac >> simp[current_origin_copy_def]
QED

Theorem current_singleton_copy_direct:
  ALOOKUP snapshot n = SOME origin /\ ALOOKUP m n = SOME origin ==>
  ALOOKUP snapshot n = SOME origin /\
  current_origin_copy m n dst m = SOME ((dst,origin)::m) /\
  ALOOKUP ((dst,origin)::m) dst = SOME origin
Proof
  simp[current_origin_copy_def]
QED

(* Availability alone does not give origin agreement after a later write. *)
Theorem current_intervening_write_changes_origin:
  origin1 <> origin2 ==>
  ALOOKUP (current_chronological_writes [(n,origin1); (n,origin2)] m) n =
    SOME origin2 /\
  ALOOKUP (current_chronological_writes [(n,origin1); (n,origin2)] m) n <>
    ALOOKUP (current_chronological_writes [(n,origin1)] m) n
Proof
  simp[current_chronological_writes_def]
QED

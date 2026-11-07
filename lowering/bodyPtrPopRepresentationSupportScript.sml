Theory bodyPtrPopRepresentationSupport
Ancestors bodyPtrDefs valueEncoding valueEncodingProofs pred_set list arithmetic

(* Semantic supports avoid duplicating the recursive encoding (in particular
   sparse defaults). Memory is a finite zero-extended byte list, so agreement
   is expressed by its one-byte observations rather than function application.
   Supports need not be minimal, clean, or disjoint. *)
Definition pop_rep_support_def:
  pop_rep_support tv v a supp <=>
    !m n. (!i. i IN supp ==> mem_bytes_at i 1 m = mem_bytes_at i 1 n) ==>
      (val_in_memory tv v a m <=> val_in_memory tv v a n)
End

Theorem pop_rep_support_enlarge:
  pop_rep_support tv v a supp /\ supp SUBSET larger ==>
  pop_rep_support tv v a larger
Proof
  simp[pop_rep_support_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem pop_rep_support_transport:
  pop_rep_support tv v a supp /\
  (!i. i IN supp ==> mem_bytes_at i 1 m = mem_bytes_at i 1 n) /\
  val_in_memory tv v a m ==> val_in_memory tv v a n
Proof
  metis_tac[pop_rep_support_def]
QED

Theorem pop_support_patch_bytes[local]:
  !i supp m n.
  mem_bytes_at i 1
    (GENLIST (\j. if j IN supp then EL 0 (mem_bytes_at j 1 m)
                 else EL 0 (mem_bytes_at j 1 n)) (MAX (LENGTH m) (LENGTH n))) =
  if i IN supp then mem_bytes_at i 1 m else mem_bytes_at i 1 n
Proof
  rpt gen_tac >> Cases_on `i IN supp` >> simp[] >>
  irule LIST_EQ >> simp[valueEncodingProofsTheory.EL_mem_bytes_at] >>
  rpt strip_tac >> Cases_on `i < MAX (LENGTH m) (LENGTH n)` >>
  simp[valueEncodingProofsTheory.EL_mem_bytes_at] >>
  gvs[arithmeticTheory.MAX_DEF] >>
  simp[GSYM listTheory.EL, valueEncodingProofsTheory.EL_mem_bytes_at]
QED

Theorem pop_rep_support_robust_frame:
  pop_rep_support tv v a supp /\ DISJOINT supp writes /\
  mem_agree_outside writes before after /\
  (!m. mem_agree_outside dirty before m ==> val_in_memory tv v a m) ==>
  !m. mem_agree_outside dirty after m ==> val_in_memory tv v a m
Proof
  strip_tac >> rpt strip_tac >>
  qabbrev_tac `mix = GENLIST
    (\j. if j IN supp then EL 0 (mem_bytes_at j 1 m)
         else EL 0 (mem_bytes_at j 1 before)) (MAX (LENGTH m) (LENGTH before))` >>
  `!i. mem_bytes_at i 1 mix =
    if i IN supp then mem_bytes_at i 1 m else mem_bytes_at i 1 before` by
    simp[Abbr `mix`, pop_support_patch_bytes] >>
  `mem_agree_outside dirty before mix` by
    (simp[mem_agree_outside_def] >> rpt strip_tac >>
     Cases_on `i IN supp` >> simp[] >>
     `i NOTIN writes` by metis_tac[IN_DISJOINT] >>
     fs[mem_agree_outside_def] >> metis_tac[]) >>
  irule pop_rep_support_transport >>
  qexistsl_tac [`mix`,`supp`] >> simp[]
QED

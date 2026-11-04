Theory makeSsaCurrentDemandBoundary
Ancestors
  livenessDemandWitness livenessBlockProofs livenessTransferProofs
  livenessDefs list

Theorem finite_backward_slots[local]:
  !xs f.
    f (LENGTH xs) = out /\
    (!i. i < LENGTH xs ==> f i = transfer (EL i xs) (f (SUC i))) ==>
    !i. i <= LENGTH xs ==> f i = FOLDR transfer out (DROP i xs)
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >> fs[] >>
  `!i. i <= LENGTH xs ==> f (SUC i) = FOLDR transfer out (DROP i xs)` by
    (qpat_x_assum `!f. _` (qspec_then `\i. f (SUC i)` mp_tac) >>
     (impl_tac >-
       (simp[] >> rpt strip_tac >>
        first_x_assum (qspec_then `SUC i` mp_tac) >> simp[])) >> simp[]) >>
  Cases >> simp[] >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[]
QED

Theorem current_liveness_slot_fold:
  i <= LENGTH (liveness_instrs bbs lbl) ==>
  df_at [] (liveness_block bbs cfg lbl st) lbl i =
    FOLDR (liveness_transfer bbs) (liveness_out bbs cfg lbl st)
      (DROP i (liveness_instrs bbs lbl))
Proof
  strip_tac >> irule finite_backward_slots >>
  simp[liveness_block_exit, liveness_block_transfer]
QED

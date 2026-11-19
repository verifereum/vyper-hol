(* Link an occurrence across a finite interval of empty pieces. *)
Theory staticAbortRevertLink
Ancestors arithmetic

Theorem revert_first_active:
  !n i (len:num->num) (pc:num->num) (H:num->num->num).
    0 < len (i+n) /\
    (!q. i <= q /\ q < i+n ==>
         pc (SUC q) = pc q + len q /\ H (SUC q) 0 = H q (len q)) ==>
    ?u. i <= u /\ u <= i+n /\ 0 < len u /\
        pc u = pc i /\ H u 0 = H i 0
Proof
  Induct
  (* simp[] alone does not introduce the witness at distance zero. *)
  >- (rpt gen_tac >> strip_tac >> qexists `i` >> fs[]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `len i`
  >- (`pc (SUC i) = pc i /\ H (SUC i) 0 = H i 0` by
        (qpat_assum `!q. i <= q /\ q < i + SUC n ==> _`
           (qspec_then `i` mp_tac) >> simp[]) >>
      first_x_assum (qspecl_then [`SUC i`,`len`,`pc`,`H`] mp_tac) >>
      `SUC i + n = i + SUC n` by decide_tac >>
      (* The simplifier already discharges the shortened adjacency range;
         an additional impl_tac would target the existential implication. *)
      simp[] >> strip_tac >> qexists `u` >> simp[] >> decide_tac) >>
  qexists `i` >> simp[]
QED

(* Use the same selection function at the initial boundary and each exit. *)
Theorem revert_active_targets:
  !(K:num) (J:num) (len:num->num) (pc:num->num) (H:num->num->num).
    0 < len J /\
    (!q. K <= q /\ q < J ==>
         pc (SUC q) = pc q + len q /\ H (SUC q) 0 = H q (len q)) ==>
    ?next. !i. K <= i /\ i <= J ==>
      i <= next i /\ next i <= J /\ 0 < len (next i) /\
      pc (next i) = pc i /\ H (next i) 0 = H i 0
Proof
  rpt gen_tac >> strip_tac >>
  (* The arithmetic ancestors do not expose RIGHT_IMP_EXISTS_THM.
     Establish the guarded pointwise witnesses before Skolemization. *)
  `!i. ?u. K' <= i /\ i <= J ==>
      i <= u /\ u <= J /\ 0 < len u /\ pc u = pc i /\ H u 0 = H i 0`
    suffices_by simp[SKOLEM_THM] >>
  gen_tac >> Cases_on `K' <= i /\ i <= J` >> simp[] >>
  qspecl_then [`J-i`,`i`,`len`,`pc`,`H`] mp_tac revert_first_active >>
  `i + (J-i) = J` by decide_tac >> simp[] >>
  metis_tac[LESS_EQ_TRANS]
QED

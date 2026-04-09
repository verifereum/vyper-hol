(*
 * Worklist Iteration — Convergence Proofs
 *
 * All theorems take an invariant P so that inflationary need only
 * hold under P.  For the unconditional case, instantiate P = λ_. T.
 *
 * Termination: bounded measure + inflationary-under-P → WHILE terminates.
 * Fixpoint: deps_complete → result is a fixpoint for all labels.
 * Above: partial_order + inflationary-under-P → result ≥ initial.
 * Invariant: P preserved by process → P holds at result.
 *)

Theory worklistProofs
Ancestors
  worklistDefs latticeProofs

(* --- Shared infrastructure for worklist convergence --- *)

(* The ranking function for termination: lexicographic (b - m(st), |wl|) *)
Definition wl_rank_def:
  wl_rank (m : 'a -> num) b (p : 'b list # 'a) =
    (b - m (SND p), LENGTH (FST p))
End

(* Well-foundedness of the ranking order *)
Theorem wl_rank_wf[local]:
  WF (inv_image ($< LEX $<) (wl_rank m b))
Proof
  irule relationTheory.WF_inv_image >>
  irule pairTheory.WF_LEX >> rw[prim_recTheory.WF_LESS]
QED

(* Core: wl_step decreases the ranking when the worklist is non-empty
   and P is maintained *)
Theorem wl_step_decreases[local]:
  !(leq : 'a -> 'a -> bool) m b changed
   (process : 'b -> 'a -> 'a) deps (P : 'a -> bool) p.
    (!lbl st. changed lbl st (process lbl st) <=> process lbl st <> st) /\
    (!lbl st. P st ==> leq st (process lbl st)) /\
    (!lbl st. P st ==> P (process lbl st)) /\
    bounded_measure P leq m b /\
    P (SND p) /\ FST p <> [] ==>
    (inv_image ($< LEX $<) (wl_rank m b))
      (wl_step changed process deps p) p
Proof
  rw[wl_step_def, wl_rank_def, relationTheory.inv_image_def,
     pairTheory.LEX_DEF_THM] >>
  Cases_on `p` >> Cases_on `q` >> fs[] >>
  Cases_on `process h r = r` >> fs[] >>
  DISJ1_TAC >>
  fs[latticeDefsTheory.bounded_measure_def] >>
  `m r < m (process h r)` by (first_x_assum irule >> rw[] >> metis_tac[]) >>
  `m r <= b` by metis_tac[] >>
  `m (process h r) <= b` by metis_tac[] >>
  fs[]
QED

(* Termination: ∃n. worklist is empty after n steps.
   Nested complete induction: outer on b - m(SND s), inner on LENGTH(FST s).
   Change-step: b - m decreases. No-change step: LENGTH decreases. *)
Theorem wl_terminates[local]:
  !(leq : 'a -> 'a -> bool) m b changed
   (process : 'b -> 'a -> 'a) deps (P : 'a -> bool) wl st.
    (!lbl st. changed lbl st (process lbl st) <=> process lbl st <> st) /\
    (!lbl st. P st ==> leq st (process lbl st)) /\
    (!lbl st. P st ==> P (process lbl st)) /\
    bounded_measure P leq m b /\
    P st ==>
    ?n. FST (FUNPOW (wl_step changed process deps) n (wl, st)) = []
Proof
  rw[] >>
  `!d wl st. P st /\ bounded_measure P leq m b /\ b - m st <= d ==>
    ?n. FST (FUNPOW (wl_step changed process deps) n (wl, st)) = []`
    suffices_by (disch_then (qspecl_then [`b - m st`, `wl`, `st`] mp_tac) >> rw[]) >>
  completeInduct_on `d` >> rw[] >>
  completeInduct_on `LENGTH wl` >> rw[] >>
  Cases_on `wl`
  >- (qexists_tac `0` >> rw[arithmeticTheory.FUNPOW])
  >> Cases_on `process h st' = st'`
  >- ((* No-change: worklist shrinks, d stays *)
      `wl_step changed process deps (h::t, st') = (t, st')` by rw[wl_step_def] >>
      qpat_x_assum `!m. m < LENGTH (h::t) ==> _`
        (qspec_then `LENGTH t` mp_tac) >> rw[] >>
      pop_assum (qspec_then `t` mp_tac) >> rw[] >>
      qexists_tac `SUC n` >> rw[arithmeticTheory.FUNPOW])
  >> (* Change: m increases so b - m(new_st) < b - m(st) <= d *)
  `wl_step changed process deps (h::t, st') =
    (t ++ deps h, process h st')` by rw[wl_step_def] >>
  `P (process h st')` by metis_tac[] >>
  `leq st' (process h st')` by metis_tac[] >>
  `m st' < m (process h st')` by fs[latticeDefsTheory.bounded_measure_def] >>
  `m (process h st') <= b` by fs[latticeDefsTheory.bounded_measure_def] >>
  `b - m (process h st') < d` by fs[] >>
  qpat_x_assum `!m'. m' < d ==> _` drule >>
  disch_then (qspecl_then [`t ++ deps h`, `process h st'`] mp_tac) >> rw[] >>
  qexists_tac `SUC n` >> rw[arithmeticTheory.FUNPOW]
QED

(* Core worklist lemma: any invariant Q that implies P(SND p) and is
   preserved by wl_step is preserved by WHILE, and WHILE terminates.
   Uses OWHILE: termination gives SOME result, then OWHILE lemmas give properties. *)
Theorem wl_while_core[local]:
  !(leq : 'a -> 'a -> bool) m b changed
   (process : 'b -> 'a -> 'a) deps (P : 'a -> bool)
   (Q : 'b list # 'a -> bool) s.
    (!lbl st. changed lbl st (process lbl st) <=> process lbl st <> st) /\
    (!lbl st. P st ==> leq st (process lbl st)) /\
    (!lbl st. P st ==> P (process lbl st)) /\
    bounded_measure P leq m b /\
    Q s /\
    (!p. Q p ==> P (SND p)) /\
    (!p. Q p /\ FST p <> [] ==> Q (wl_step changed process deps p)) ==>
    Q (WHILE (\p. FST p <> []) (wl_step changed process deps) s) /\
    FST (WHILE (\p. FST p <> []) (wl_step changed process deps) s) = []
Proof
  rpt gen_tac >> strip_tac >> Cases_on `s` >>
  `P r` by metis_tac[pairTheory.SND] >>
  `?n. FST (FUNPOW (wl_step changed process deps) n (q, r)) = []` by
    (irule wl_terminates >> metis_tac[]) >>
  `?result. OWHILE (\p. FST p <> []) (wl_step changed process deps) (q,r) =
    SOME result` by (rw[WhileTheory.OWHILE_def] >> metis_tac[]) >>
  `WHILE (\p. FST p <> []) (wl_step changed process deps) (q,r) = result` by
    (drule WhileTheory.OWHILE_WHILE >> rw[]) >>
  `~(FST result <> [])` by
    (drule WhileTheory.OWHILE_ENDCOND >> rw[]) >>
  mp_tac (WhileTheory.OWHILE_INV_IND
    |> INST_TYPE [alpha |-> ``:'b list # 'a``]
    |> Q.INST [`P` |-> `Q`]) >>
  disch_then (qspecl_then
    [`\p. FST p <> []`, `wl_step changed process deps`, `(q,r)`] mp_tac) >>
  rw[]
QED

(* ===== Main theorems ===== *)

(* P-preservation through wl_step (reused across theorems) *)
Theorem wl_step_preserves_P[local]:
  !changed process deps (P : 'a -> bool) p.
    (!lbl st. changed lbl st (process lbl st) <=> process lbl st <> st) /\
    (!lbl st. P st ==> P (process lbl st)) /\
    P (SND p) /\ FST p <> [] ==>
    P (SND (wl_step changed process deps p))
Proof
  rw[wl_step_def] >>
  Cases_on `p` >> Cases_on `q` >> fs[] >>
  Cases_on `process h r = r` >> fs[]
QED

Theorem wl_iterate_terminates_proof:
  !(leq : 'a -> 'a -> bool) m b changed
   (process : 'b -> 'a -> 'a) deps wl0 st0 (P : 'a -> bool).
    (!lbl st. changed lbl st (process lbl st) <=> process lbl st <> st) /\
    (!lbl st. P st ==> leq st (process lbl st)) /\
    (!lbl st. P st ==> P (process lbl st)) /\
    P st0 /\
    bounded_measure P leq m b ==>
    FST (wl_iterate changed process deps wl0 st0) = []
Proof
  rw[wl_iterate_def] >>
  qspecl_then [`leq`,`m`,`b`,`changed`,`process`,`deps`,`P`,
               `\p. P (SND p)`, `(wl0, st0)`]
    mp_tac wl_while_core >>
  impl_tac >- (rw[] >> irule wl_step_preserves_P >> metis_tac[]) >>
  rw[]
QED

Theorem wl_iterate_invariant_proof:
  !(leq : 'a -> 'a -> bool) m b changed
   (process : 'b -> 'a -> 'a) deps wl0 st0 (P : 'a -> bool).
    (!lbl st. changed lbl st (process lbl st) <=> process lbl st <> st) /\
    (!lbl st. P st ==> leq st (process lbl st)) /\
    (!lbl st. P st ==> P (process lbl st)) /\
    P st0 /\
    bounded_measure P leq m b ==>
    P (SND (wl_iterate changed process deps wl0 st0))
Proof
  rw[wl_iterate_def] >>
  qspecl_then [`leq`,`m`,`b`,`changed`,`process`,`deps`,`P`,
               `\p. P (SND p)`, `(wl0, st0)`]
    mp_tac wl_while_core >>
  impl_tac >- (rw[] >> irule wl_step_preserves_P >> metis_tac[]) >>
  rw[]
QED

Theorem wl_iterate_above_proof:
  !(leq : 'a -> 'a -> bool) m b changed
   (process : 'b -> 'a -> 'a) deps wl0 st0 (P : 'a -> bool).
    (!lbl st. changed lbl st (process lbl st) <=> process lbl st <> st) /\
    partial_order leq /\
    (!lbl st. P st ==> leq st (process lbl st)) /\
    (!lbl st. P st ==> P (process lbl st)) /\
    P st0 /\
    bounded_measure P leq m b ==>
    leq st0 (SND (wl_iterate changed process deps wl0 st0))
Proof
  rw[wl_iterate_def] >>
  qspecl_then [`leq`,`m`,`b`,`changed`,`process`,`deps`,`P`,
               `\p. P (SND p) /\ leq st0 (SND p)`, `(wl0, st0)`]
    mp_tac wl_while_core >>
  impl_tac
  >- (rw[]
      >- fs[latticeDefsTheory.partial_order_def, relationTheory.reflexive_def]
      >- (irule wl_step_preserves_P >> metis_tac[])
      >- (Cases_on `p` >> Cases_on `q` >>
          fs[wl_step_def] >> Cases_on `process h r = r` >> fs[] >>
          fs[latticeDefsTheory.partial_order_def, relationTheory.transitive_def] >>
          first_x_assum irule >> qexists_tac `r` >> fs[])
      >> fs[])
  >> rw[]
QED

Theorem wl_iterate_fixpoint_proof:
  !(leq : 'a -> 'a -> bool) m b changed
   (process : 'b -> 'a -> 'a) deps wl0 st0 all_lbls (P : 'a -> bool).
    (!lbl st. changed lbl st (process lbl st) <=> process lbl st <> st) /\
    (!lbl st. P st ==> leq st (process lbl st)) /\
    (!lbl st. P st ==> P (process lbl st)) /\
    P st0 /\
    bounded_measure P leq m b /\
    wl_deps_complete changed process deps /\
    (!lbl. MEM lbl all_lbls ==> MEM lbl wl0) ==>
    is_fixpoint process all_lbls (SND (wl_iterate changed process deps wl0 st0))
Proof
  rw[wl_iterate_def, is_fixpoint_def] >>
  qspecl_then [`leq`,`m`,`b`,`changed`,`process`,`deps`,`P`,
               `\p. P (SND p) /\
                    !lbl. MEM lbl all_lbls /\
                          process lbl (SND p) <> SND p ==>
                          MEM lbl (FST p)`,
               `(wl0, st0)`]
    mp_tac wl_while_core >>
  impl_tac
  >- (rw[]
      >- (irule wl_step_preserves_P >> metis_tac[])
      >- (Cases_on `p` >> Cases_on `q` >>
          fs[wl_step_def, wl_deps_complete_def] >>
          qpat_x_assum `!lbl st. changed _ _ _ <=> _`
            (fn equiv =>
              RULE_ASSUM_TAC (REWRITE_RULE [equiv]) >>
              assume_tac equiv) >>
          Cases_on `process h r = r` >> fs[] >> rw[] >>
          fs[listTheory.MEM_APPEND] >> metis_tac[])
      >> metis_tac[])
  >> rw[] >> metis_tac[listTheory.MEM]
QED

(* ===== Process-measure variant (weaker precondition) =====
   Instead of bounded_measure (universal over all P-state pairs), requires only
   that process strictly increases m whenever it changes the state.
   Useful when no single ordering makes bounded_measure work universally
   (e.g., analyses where inst map changes don't always align with boundary ordering).

   All core lemmas take a valid_lbl predicate restricting which labels the
   measure/preservation conditions must hold for. The worklist invariant
   EVERY valid_lbl wl ensures only valid labels are ever processed.
   Unrestricted variants (valid_lbl = \_.T) are derived as corollaries. *)

(* Termination: restricted to valid labels *)
Theorem wl_terminates2[local]:
  !m b changed (process : 'b -> 'a -> 'a) deps (P : 'a -> bool)
   (valid_lbl : 'b -> bool) wl st.
    (!lbl st. changed lbl st (process lbl st) <=> process lbl st <> st) /\
    (!lbl st. valid_lbl lbl /\ P st /\ process lbl st <> st ==>
              m st < m (process lbl st)) /\
    (!lbl st. valid_lbl lbl /\ P st ==> P (process lbl st)) /\
    (!x. P x ==> m x <= b) /\
    P st /\
    EVERY valid_lbl wl /\
    (!lbl. valid_lbl lbl ==> EVERY valid_lbl (deps lbl)) ==>
    ?n. FST (FUNPOW (wl_step changed process deps) n (wl, st)) = []
Proof
  rw[] >>
  `!d wl st. P st /\ EVERY valid_lbl wl /\ b - m st <= d ==>
    ?n. FST (FUNPOW (wl_step changed process deps) n (wl, st)) = []`
    suffices_by
      (disch_then (qspecl_then [`b - m st`, `wl`, `st`] mp_tac) >> rw[]) >>
  completeInduct_on `d` >> rw[] >>
  completeInduct_on `LENGTH wl'` >> rw[] >>
  Cases_on `wl'`
  >- (qexists_tac `0` >> rw[arithmeticTheory.FUNPOW])
  >> `valid_lbl h /\ EVERY valid_lbl t` by fs[listTheory.EVERY_DEF] >>
  Cases_on `process h st' = st'`
  >- (`wl_step changed process deps (h::t, st') = (t, st')` by rw[wl_step_def] >>
      qpat_x_assum `!m. m < LENGTH (h::t) ==> _`
        (qspec_then `LENGTH t` mp_tac) >>
      rw[listTheory.LENGTH] >>
      pop_assum (qspec_then `t` mp_tac) >> rw[] >>
      qexists_tac `SUC n` >> rw[arithmeticTheory.FUNPOW])
  >> `wl_step changed process deps (h::t, st') =
       (t ++ deps h, process h st')` by rw[wl_step_def] >>
  `P (process h st')` by metis_tac[] >>
  `m st' < m (process h st')` by metis_tac[] >>
  `m (process h st') <= b` by metis_tac[] >>
  `b - m (process h st') < d` by fs[] >>
  `EVERY valid_lbl (deps h)` by metis_tac[] >>
  `EVERY valid_lbl (t ++ deps h)` by fs[listTheory.EVERY_APPEND] >>
  qpat_x_assum `!m'. m' < d ==> _` drule >>
  disch_then (qspecl_then [`t ++ deps h`, `process h st'`] mp_tac) >>
  rw[] >>
  qexists_tac `SUC n` >> rw[arithmeticTheory.FUNPOW]
QED

(* Core WHILE lemma: restricted to valid labels *)
Theorem wl_while_core2[local]:
  !m b changed (process : 'b -> 'a -> 'a) deps (P : 'a -> bool)
   (valid_lbl : 'b -> bool) (Q : 'b list # 'a -> bool) s.
    (!lbl st. changed lbl st (process lbl st) <=> process lbl st <> st) /\
    (!lbl st. valid_lbl lbl /\ P st /\ process lbl st <> st ==>
              m st < m (process lbl st)) /\
    (!lbl st. valid_lbl lbl /\ P st ==> P (process lbl st)) /\
    (!x. P x ==> m x <= b) /\
    (!lbl. valid_lbl lbl ==> EVERY valid_lbl (deps lbl)) /\
    Q s /\
    (!p. Q p ==> P (SND p) /\ EVERY valid_lbl (FST p)) /\
    (!p. Q p /\ FST p <> [] ==> Q (wl_step changed process deps p)) ==>
    Q (WHILE (\p. FST p <> []) (wl_step changed process deps) s) /\
    FST (WHILE (\p. FST p <> []) (wl_step changed process deps) s) = []
Proof
  rpt gen_tac >> strip_tac >> Cases_on `s` >>
  `P r /\ EVERY valid_lbl q` by
    metis_tac[pairTheory.SND, pairTheory.FST] >>
  `?n. FST (FUNPOW (wl_step changed process deps) n (q, r)) = []`
    suffices_by
    (strip_tac >>
     `?result. OWHILE (\p. FST p <> []) (wl_step changed process deps) (q,r) =
       SOME result` by (rw[WhileTheory.OWHILE_def] >> metis_tac[]) >>
     `WHILE (\p. FST p <> []) (wl_step changed process deps) (q,r) = result` by
       (drule WhileTheory.OWHILE_WHILE >> rw[]) >>
     `~(FST result <> [])` by
       (drule WhileTheory.OWHILE_ENDCOND >> rw[]) >>
     mp_tac (WhileTheory.OWHILE_INV_IND
       |> INST_TYPE [alpha |-> ``:'b list # 'a``]
       |> Q.INST [`P` |-> `Q`]) >>
     disch_then (qspecl_then
       [`\p. FST p <> []`, `wl_step changed process deps`, `(q,r)`] mp_tac) >>
     rw[]) >>
  irule wl_terminates2 >> metis_tac[]
QED

(* --- wl_step preserves EVERY valid_lbl under deps closure --- *)
Theorem wl_step_preserves_valid[local]:
  !changed process deps (valid_lbl : 'b -> bool) (P : 'a -> bool) p.
    (!lbl st. changed lbl st (process lbl st) <=> process lbl st <> st) /\
    (!lbl st. valid_lbl lbl /\ P st ==> P (process lbl st)) /\
    (!lbl. valid_lbl lbl ==> EVERY valid_lbl (deps lbl)) /\
    P (SND p) /\ EVERY valid_lbl (FST p) /\ FST p <> [] ==>
    P (SND (wl_step changed process deps p)) /\
    EVERY valid_lbl (FST (wl_step changed process deps p))
Proof
  rw[wl_step_def] >>
  Cases_on `p` >> Cases_on `q` >> fs[listTheory.EVERY_DEF] >>
  Cases_on `process h r = r` >> fs[listTheory.EVERY_APPEND]
QED

(* --- Public API: fixpoint (restricted) --- *)
Theorem wl_iterate_fixpoint_process_restricted:
  !m b changed (process : 'b -> 'a -> 'a) deps wl0 st0 all_lbls
   (P : 'a -> bool) (valid_lbl : 'b -> bool).
    (!lbl st. changed lbl st (process lbl st) <=> process lbl st <> st) /\
    (!lbl st. valid_lbl lbl /\ P st /\ process lbl st <> st ==>
              m st < m (process lbl st)) /\
    (!lbl st. valid_lbl lbl /\ P st ==> P (process lbl st)) /\
    P st0 /\
    (!x. P x ==> m x <= b) /\
    wl_deps_complete changed process deps /\
    (!lbl. MEM lbl all_lbls ==> MEM lbl wl0) /\
    EVERY valid_lbl wl0 /\
    (!lbl. valid_lbl lbl ==> EVERY valid_lbl (deps lbl)) ==>
    is_fixpoint process all_lbls (SND (wl_iterate changed process deps wl0 st0))
Proof
  rw[wl_iterate_def, is_fixpoint_def] >>
  qspecl_then [`m`,`b`,`changed`,`process`,`deps`,`P`, `valid_lbl`,
               `\p. P (SND p) /\ EVERY valid_lbl (FST p) /\
                    !lbl. MEM lbl all_lbls /\
                          process lbl (SND p) <> SND p ==>
                          MEM lbl (FST p)`,
               `(wl0, st0)`]
    mp_tac wl_while_core2 >>
  impl_tac
  >- (rw[]
      (* Goal 1: P (SND (wl_step ...)) *)
      >- (Cases_on `p` >> Cases_on `q` >>
          fs[wl_step_def, listTheory.EVERY_DEF] >>
          Cases_on `process h r = r` >> fs[listTheory.EVERY_APPEND] >>
          metis_tac[])
      (* Goal 2: EVERY valid_lbl (FST (wl_step ...)) *)
      >- (Cases_on `p` >> Cases_on `q` >>
          fs[wl_step_def, listTheory.EVERY_DEF] >>
          Cases_on `process h r = r` >>
          fs[listTheory.EVERY_APPEND] >> metis_tac[])
      (* Goal 3: MEM lbl' (FST (wl_step ...)) — all_lbls tracking *)
      >- (Cases_on `p` >> Cases_on `q` >>
          fs[wl_step_def, listTheory.EVERY_DEF] >>
          qpat_x_assum `wl_deps_complete _ _ _`
            (mp_tac o REWRITE_RULE [wl_deps_complete_def]) >>
          qpat_x_assum `!lbl st. changed _ _ _ <=> _`
            (fn equiv =>
              RULE_ASSUM_TAC (REWRITE_RULE [equiv]) >>
              assume_tac equiv >>
              disch_then (assume_tac o REWRITE_RULE [equiv])) >>
          Cases_on `process h r = r` >> fs[]
          >- (`lbl' = h \/ MEM lbl' t` by metis_tac[] >> fs[])
          >- (fs[listTheory.MEM_APPEND] >>
              Cases_on `process lbl' r = r`
              >- (disj2_tac >> first_x_assum drule >> metis_tac[])
              >- (`lbl' = h \/ MEM lbl' t` by metis_tac[] >> fs[] >>
                  disj2_tac >> first_x_assum drule >> metis_tac[])))
      (* Goal 4: Initial Q — P st0, EVERY valid_lbl wl0, tracking *)
      >> metis_tac[])
  >> simp[] >> metis_tac[listTheory.MEM]
QED

(* --- Unrestricted corollaries (valid_lbl = \_.T) --- *)
Theorem wl_iterate_fixpoint_process_proof:
  !m b changed (process : 'b -> 'a -> 'a) deps wl0 st0 all_lbls (P : 'a -> bool).
    (!lbl st. changed lbl st (process lbl st) <=> process lbl st <> st) /\
    (!lbl st. P st /\ process lbl st <> st ==> m st < m (process lbl st)) /\
    (!lbl st. P st ==> P (process lbl st)) /\
    P st0 /\
    (!x. P x ==> m x <= b) /\
    wl_deps_complete changed process deps /\
    (!lbl. MEM lbl all_lbls ==> MEM lbl wl0) ==>
    is_fixpoint process all_lbls (SND (wl_iterate changed process deps wl0 st0))
Proof
  rw[] >>
  irule wl_iterate_fixpoint_process_restricted >>
  rw[] >>
  qexistsl_tac [`P`, `b`, `m`, `\x:'b. T`] >>
  rw[listTheory.EVERY_MEM]
QED

Theorem wl_iterate_invariant_process_proof:
  !m b changed (process : 'b -> 'a -> 'a) deps wl0 st0 (P : 'a -> bool).
    (!lbl st. changed lbl st (process lbl st) <=> process lbl st <> st) /\
    (!lbl st. P st /\ process lbl st <> st ==> m st < m (process lbl st)) /\
    (!lbl st. P st ==> P (process lbl st)) /\
    P st0 /\
    (!x. P x ==> m x <= b) ==>
    P (SND (wl_iterate changed process deps wl0 st0))
Proof
  rw[wl_iterate_def] >>
  qspecl_then [`m`,`b`,`changed`,`process`,`deps`,`P`, `\x:'b. T`,
               `\p. P (SND p) /\ EVERY (\x:'b. T) (FST p)`,
               `(wl0, st0)`]
    mp_tac wl_while_core2 >>
  impl_tac
  >- (rw[listTheory.EVERY_MEM] >>
      Cases_on `p` >> Cases_on `q` >>
      fs[wl_step_def, listTheory.EVERY_DEF, listTheory.EVERY_MEM] >>
      Cases_on `process h r = r` >> fs[] >> metis_tac[])
  >> rw[]
QED

(* Restricted invariant preservation through wl_iterate.
   Like wl_iterate_invariant_process_proof but P only needs to be
   preserved for valid labels. *)
Theorem wl_iterate_invariant_process_restricted:
  !m b changed (process : 'b -> 'a -> 'a) deps wl0 st0
   (P : 'a -> bool) (valid_lbl : 'b -> bool).
    (!lbl st. changed lbl st (process lbl st) <=> process lbl st <> st) /\
    (!lbl st. valid_lbl lbl /\ P st /\ process lbl st <> st ==>
              m st < m (process lbl st)) /\
    (!lbl st. valid_lbl lbl /\ P st ==> P (process lbl st)) /\
    P st0 /\
    (!x. P x ==> m x <= b) /\
    EVERY valid_lbl wl0 /\
    (!lbl. valid_lbl lbl ==> EVERY valid_lbl (deps lbl)) ==>
    P (SND (wl_iterate changed process deps wl0 st0))
Proof
  rw[wl_iterate_def] >>
  qspecl_then [`m`,`b`,`changed`,`process`,`deps`,`P`, `valid_lbl`,
               `\p. P (SND p) /\ EVERY valid_lbl (FST p)`,
               `(wl0, st0)`]
    mp_tac wl_while_core2 >>
  impl_tac
  >- (rw[]
      >- (Cases_on `p` >> Cases_on `q` >>
          fs[wl_step_def, listTheory.EVERY_DEF] >>
          Cases_on `process h r = r` >>
          fs[listTheory.EVERY_APPEND] >> metis_tac[])
      >- (Cases_on `p` >> Cases_on `q` >>
          fs[wl_step_def, listTheory.EVERY_DEF] >>
          Cases_on `process h r = r` >>
          fs[listTheory.EVERY_APPEND] >> metis_tac[])
      >> metis_tac[])
  >> rw[]
QED

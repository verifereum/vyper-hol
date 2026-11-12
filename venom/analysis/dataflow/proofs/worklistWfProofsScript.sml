(*
 * Worklist Iteration — Well-Founded Rank Convergence
 *
 * Convergence and fixpoint theorems under an arbitrary well-founded
 * strict-descent relation R on a state rank rho, permitting unbounded
 * queue growth on changed steps.
 *)

Theory worklistWfProofs
Ancestors
  worklistDefs

Theorem wl_terminates_wf[local]:
 !R rho changed process deps P valid.
 WF R /\
 (!l s. changed l s (process l s) <=> process l s <> s) /\
 (!l s. valid l /\ P s /\ process l s <> s ==>
        R (rho (process l s)) (rho s)) /\
 (!l s. valid l /\ P s ==> P (process l s)) /\
 (!l. valid l ==> EVERY valid (deps l)) ==>
 !wl st. P st /\ EVERY valid wl ==>
 ?n. FST (FUNPOW (wl_step changed process deps) n (wl,st)) = []
Proof
 rpt gen_tac >> strip_tac >>
 `!r. !st wl. rho st = r /\ P st /\ EVERY valid wl ==>
  ?n. FST (FUNPOW (wl_step changed process deps) n (wl,st)) = []`
   suffices_by metis_tac[] >>
 qpat_x_assum `WF R` (mp_tac o MATCH_MP relationTheory.WF_INDUCTION_THM) >>
 disch_then ho_match_mp_tac >> qx_gen_tac `r` >> strip_tac >>
 qx_gen_tac `st` >> Induct >> rpt strip_tac
 >- (qexists_tac `0` >> simp[arithmeticTheory.FUNPOW]) >>
 gvs[listTheory.EVERY_DEF] >> Cases_on `process h st = st`
 >- (qexists_tac `SUC n` >> simp[arithmeticTheory.FUNPOW, wl_step_def]) >>
 `P (process h st)` by metis_tac[] >>
 `R (rho (process h st)) (rho st)` by metis_tac[] >>
 `EVERY valid (wl ++ deps h)` by
   metis_tac[listTheory.EVERY_APPEND] >>
 qpat_x_assum `!r'. R r' _ ==> _` drule >>
 disch_then (qspecl_then [`process h st`, `wl ++ deps h`] mp_tac) >>
 simp[] >> disch_then (qx_choose_then `steps` assume_tac) >>
 qexists_tac `SUC steps` >> simp[arithmeticTheory.FUNPOW, wl_step_def]
QED

Theorem wl_while_finite[local]:
 !changed process deps Q s.
 (?n. FST (FUNPOW (wl_step changed process deps) n s) = []) /\
 Q s /\ (!p. Q p /\ FST p <> [] ==> Q (wl_step changed process deps p)) ==>
 Q (WHILE (\p. FST p <> []) (wl_step changed process deps) s) /\
 FST (WHILE (\p. FST p <> []) (wl_step changed process deps) s) = []
Proof
 rpt gen_tac >> strip_tac >>
 `?result. OWHILE (\p. FST p <> []) (wl_step changed process deps) s = SOME result` by
   (simp[WhileTheory.OWHILE_def] >> metis_tac[]) >>
 drule WhileTheory.OWHILE_WHILE >> strip_tac >> simp[] >>
 reverse conj_tac
 >- (drule WhileTheory.OWHILE_ENDCOND >> simp[]) >>
 irule WhileTheory.OWHILE_INV_IND >>
 qexistsl_tac [`\p. FST p <> []`, `wl_step changed process deps`, `s`] >> simp[]
QED

Theorem wl_iterate_terminates_wf:
 !R rho changed process deps wl0 st0 P valid.
 WF R /\
 (!l s. changed l s (process l s) <=> process l s <> s) /\
 (!l s. valid l /\ P s /\ process l s <> s ==>
        R (rho (process l s)) (rho s)) /\
 (!l s. valid l /\ P s ==> P (process l s)) /\
 P st0 /\ EVERY valid wl0 /\
 (!l. valid l ==> EVERY valid (deps l)) ==>
 FST (wl_iterate changed process deps wl0 st0) = [] /\
 P (SND (wl_iterate changed process deps wl0 st0))
Proof
 rpt gen_tac >> strip_tac >>
 `(?n. FST (FUNPOW (wl_step changed process deps) n (wl0,st0)) = [])` by
   (drule_all wl_terminates_wf >> simp[]) >>
 `(P (SND (WHILE (\p. FST p <> []) (wl_step changed process deps) (wl0,st0))) /\
  EVERY valid (FST (WHILE (\p. FST p <> []) (wl_step changed process deps) (wl0,st0)))) /\
  FST (WHILE (\p. FST p <> []) (wl_step changed process deps) (wl0,st0)) = []` by
   (ho_match_mp_tac wl_while_finite >>
    conj_tac >- metis_tac[] >> simp[] >>
    rpt strip_tac >> Cases_on `p` >> Cases_on `q` >>
    gvs[wl_step_def, listTheory.EVERY_DEF] >>
    Cases_on `process h r = r` >> gvs[listTheory.EVERY_APPEND] >>
    metis_tac[]) >>
 simp[wl_iterate_def]
QED

Theorem wl_step_preserves_pending[local]:
 !changed process deps labels p.
 (!l s. changed l s (process l s) <=> process l s <> s) /\
 wl_deps_complete changed process deps /\
 (!l. MEM l labels /\ process l (SND p) <> SND p ==> MEM l (FST p)) /\
 FST p <> [] ==>
 !l. MEM l labels /\
 process l (SND (wl_step changed process deps p)) <>
   SND (wl_step changed process deps p) ==>
 MEM l (FST (wl_step changed process deps p))
Proof
 rpt gen_tac >> strip_tac >> Cases_on `p` >> Cases_on `q` >> gvs[] >>
 qpat_x_assum `wl_deps_complete _ _ _`
   (mp_tac o REWRITE_RULE [wl_deps_complete_def]) >>
 qpat_x_assum `!l s. changed _ _ _ <=> _`
   (fn equiv => RULE_ASSUM_TAC (REWRITE_RULE [equiv]) >>
    assume_tac equiv >> disch_then (assume_tac o REWRITE_RULE [equiv])) >>
 Cases_on `process h r = r` >> simp[wl_step_def] >> rpt strip_tac
 >- (`l = h \/ MEM l t` by metis_tac[listTheory.MEM] >> gvs[]) >>
 simp[listTheory.MEM_APPEND] >> Cases_on `process l r = r`
 >- (disj2_tac >>
     qpat_x_assum `!lbl st. _ ==> !b. _`
       (qspecl_then [`h`, `r`] mp_tac) >> simp[]) >>
 `l = h \/ MEM l t` by metis_tac[listTheory.MEM] >> gvs[] >>
 disj2_tac >>
 qpat_x_assum `!lbl st. _ ==> !b. _`
   (qspecl_then [`h`, `r`] mp_tac) >> simp[]
QED

Theorem wl_iterate_fixpoint_wf:
 !R rho changed process deps wl0 st0 labels P valid.
 WF R /\
 (!l s. changed l s (process l s) <=> process l s <> s) /\
 (!l s. valid l /\ P s /\ process l s <> s ==>
        R (rho (process l s)) (rho s)) /\
 (!l s. valid l /\ P s ==> P (process l s)) /\
 P st0 /\ EVERY valid wl0 /\
 (!l. valid l ==> EVERY valid (deps l)) /\
 wl_deps_complete changed process deps /\
 (!l. MEM l labels ==> MEM l wl0) ==>
 is_fixpoint process labels (SND (wl_iterate changed process deps wl0 st0))
Proof
 rpt gen_tac >> strip_tac >>
 `?n. FST (FUNPOW (wl_step changed process deps) n (wl0,st0)) = []` by
   (drule_all wl_terminates_wf >> simp[]) >>
 `(!l. MEM l labels /\
       process l (SND (WHILE (\p. FST p <> []) (wl_step changed process deps) (wl0,st0))) <>
       SND (WHILE (\p. FST p <> []) (wl_step changed process deps) (wl0,st0)) ==>
       MEM l (FST (WHILE (\p. FST p <> []) (wl_step changed process deps) (wl0,st0)))) /\
  FST (WHILE (\p. FST p <> []) (wl_step changed process deps) (wl0,st0)) = []` by
   (ho_match_mp_tac wl_while_finite >>
    conj_tac >- metis_tac[] >> simp[] >>
    rpt strip_tac >> irule wl_step_preserves_pending >> simp[] >>
    metis_tac[]) >>
 gvs[wl_iterate_def, is_fixpoint_def] >> metis_tac[listTheory.MEM]
QED

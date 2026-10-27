Theory livenessWorklistProofs
Ancestors
  worklistDefs While
Libs
  listTheory pairTheory arithmeticTheory

(* Unlike the older process API, scheduling need not detect list reordering. *)
Theorem wl_changed_terminates:
  !m b changed (process : 'a -> 'b -> 'b) deps P valid wl st.
    (!l s. valid l /\ P s ==> P (process l s) /\ m s <= m (process l s)) /\
    (!l s. valid l /\ P s /\ changed l s (process l s) ==>
           m s < m (process l s)) /\
    (!s. P s ==> m s <= b) /\
    (!l. valid l ==> EVERY valid (deps l)) /\
    P st /\ EVERY valid wl ==>
    ?n. FST (FUNPOW (wl_step changed process deps) n (wl,st)) = []
Proof
  rpt gen_tac >> strip_tac >>
  `!d wl st. P st /\ EVERY valid wl /\ b - m st <= d ==>
     ?n. FST (FUNPOW (wl_step changed process deps) n (wl,st)) = []`
    suffices_by
      (disch_then (qspecl_then [`b - m st`,`wl`,`st`] mp_tac) >> simp[]) >>
  completeInduct_on `d` >> gen_tac >>
  `!k wl st. LENGTH wl = k /\ P st /\ EVERY valid wl /\ b - m st <= d ==>
     ?n. FST (FUNPOW (wl_step changed process deps) n (wl,st)) = []`
    suffices_by metis_tac[] >>
  completeInduct_on `k` >> rpt strip_tac >>
  Cases_on `wl'` >> gvs[]
  >- (qexists_tac `0` >> simp[FUNPOW]) >>
  `valid h /\ EVERY valid t` by gvs[EVERY_DEF] >>
  `P (process h st') /\ m st' <= m (process h st')` by metis_tac[] >>
  Cases_on `changed h st' (process h st')`
  >- (`m st' < m (process h st')` by metis_tac[] >>
      `m (process h st') <= b` by metis_tac[] >>
      `b - m (process h st') < d` by decide_tac >>
      qpat_x_assum `!m'. m' < d ==> _` drule >>
      disch_then (qspecl_then [`t ++ deps h`,`process h st'`] mp_tac) >>
      simp[EVERY_APPEND] >> strip_tac >>
      qexists_tac `SUC n` >> simp[FUNPOW, wl_step_def]) >>
  qpat_x_assum `!m'. m' < SUC (LENGTH t) ==> _`
    (qspec_then `LENGTH t` mp_tac) >> simp[] >>
  disch_then (qspecl_then [`t`,`process h st'`] mp_tac) >>
  simp[] >> strip_tac >>
  qexists_tac `SUC n` >> simp[FUNPOW, wl_step_def]
QED

(* Termination evidence is separate from invariant transport. *)
Theorem wl_exhaustion_result:
  (!p. Q p /\ FST p <> [] ==> Q (wl_step changed process deps p)) /\
  Q (wl,st) /\
  (?n. FST (FUNPOW (wl_step changed process deps) n (wl,st)) = []) ==>
  Q (wl_iterate changed process deps wl st) /\
  FST (wl_iterate changed process deps wl st) = []
Proof
  strip_tac >>
  `?result. OWHILE (\p. FST p <> []) (wl_step changed process deps) (wl,st) =
    SOME result` by (simp[OWHILE_def] >> metis_tac[]) >>
  `WHILE (\p. FST p <> []) (wl_step changed process deps) (wl,st) = result` by
    metis_tac[OWHILE_WHILE] >>
  `FST result = []` by (drule OWHILE_ENDCOND >> simp[]) >>
  simp[wl_iterate_def] >>
  mp_tac (OWHILE_INV_IND |> INST_TYPE [alpha |-> ``:'a list # 'b``]
    |> Q.INST [`P` |-> `Q`]) >>
  disch_then (qspecl_then
    [`\p. FST p <> []`,`wl_step changed process deps`,`(wl,st)`] mp_tac) >>
  simp[]
QED

Theorem wl_funpow_empty:
  !n st. FUNPOW (wl_step changed process deps) n ([],st) = ([],st)
Proof
  Induct >> simp[FUNPOW, wl_step_def]
QED

Theorem wl_iterate_fuel_funpow:
  !fuel wl st.
    wl_iterate_fuel fuel changed process deps wl st =
    FUNPOW (wl_step changed process deps) fuel (wl,st)
Proof
  Induct >> simp[wl_iterate_fuel_def, FUNPOW] >> rpt gen_tac >>
  Cases_on `wl`
  >- simp[wl_iterate_fuel_def, wl_step_def, wl_funpow_empty] >>
  simp[wl_iterate_fuel_def, FUNPOW] >> pairarg_tac >> simp[]
QED

Theorem wl_funpow_invariant:
  (!p. Q p /\ FST p <> [] ==> Q (wl_step changed process deps p)) ==>
  !n p. Q p ==> Q (FUNPOW (wl_step changed process deps) n p)
Proof
  strip_tac >> Induct >> simp[FUNPOW] >> rpt strip_tac >>
  first_x_assum irule >> Cases_on `p` >> Cases_on `q` >>
  simp[wl_step_def] >> metis_tac[FST]
QED

Theorem wl_iterate_fuel_invariant:
  (!p. Q p /\ FST p <> [] ==> Q (wl_step changed process deps p)) /\
  Q (wl,st) ==>
  !fuel. Q (wl_iterate_fuel fuel changed process deps wl st)
Proof
  simp[wl_iterate_fuel_funpow] >> metis_tac[wl_funpow_invariant]
QED

Theorem wl_exhaustion_fuel_agreement:
  (?n. FST (FUNPOW (wl_step changed process deps) n (wl,st)) = []) ==>
  ?fuel. wl_iterate_fuel fuel changed process deps wl st =
         wl_iterate changed process deps wl st
Proof
  strip_tac >> simp[wl_iterate_fuel_funpow, wl_iterate_def] >>
  mp_tac (WHILE_FUNPOW |> INST_TYPE [alpha |-> ``:'a list # 'b``]
    |> Q.INST [`P` |-> `\p. FST p <> []`,
               `f` |-> `wl_step changed process deps`, `s` |-> `(wl,st)`]) >>
  impl_tac >- metis_tac[] >> metis_tac[]
QED

Theorem wl_changed_iterate:
  (!l s. valid l /\ P s ==> P (process l s) /\ m s <= m (process l s)) /\
  (!l s. valid l /\ P s /\ changed l s (process l s) ==>
         m s < m (process l s)) /\
  (!s. P s ==> m s <= b) /\
  (!l. valid l ==> EVERY valid (deps l)) /\
  P st /\ EVERY valid wl /\ Q (wl,st) /\
  (!p. P (SND p) /\ EVERY valid (FST p) /\ Q p /\ FST p <> [] ==>
        Q (wl_step changed process deps p)) ==>
  P (SND (wl_iterate changed process deps wl st)) /\
  EVERY valid (FST (wl_iterate changed process deps wl st)) /\
  Q (wl_iterate changed process deps wl st) /\
  FST (wl_iterate changed process deps wl st) = []
Proof
  strip_tac >>
  `?n. FST (FUNPOW (wl_step changed process deps) n (wl,st)) = []` by
    (irule wl_changed_terminates >> metis_tac[]) >>
  mp_tac (wl_exhaustion_result |> Q.INST
    [`Q` |-> `\p. P (SND p) /\ EVERY valid (FST p) /\ Q p`]) >>
  impl_tac
  >- (simp[] >> rpt strip_tac
      >- (Cases_on `p` >> Cases_on `q` >>
          gvs[wl_step_def, EVERY_DEF] >>
          Cases_on `changed h r (process h r)` >> simp[] >> metis_tac[])
      >- (Cases_on `p` >> Cases_on `q` >>
          gvs[wl_step_def, EVERY_DEF] >>
          Cases_on `changed h r (process h r)` >> simp[EVERY_APPEND] >> metis_tac[])
      >> metis_tac[]) >> simp[]
QED

(* All exports here are kernel proofs, including the generic fuel bridge. *)
val _ = List.app (fn (_,th) =>
  if List.all (fn s => s = "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th)))
  then () else raise Fail "oracle in changed-only worklist API")
  (DB.thms "livenessWorklistProofs");

Theory dftPositionalPendingOrbit
Ancestors
  dftCofinalSegments dftPositionalPendingClosure dftPositionalPendingGas
  dftOccurrenceMachine dftPositionalRuntime dftOriginalRuntime
  dftPositionalEdit venomInst list arithmetic

Theorem dft_pending_cofinal_segments:
  D = dft_pos_edit_ctx fi bi pre gas call post C /\
  dft_pos_runtime_ready C fi bi pre gas call post /\
  dft_original_context Corig C /\ dft_original_context Dorig D /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  call.inst_opcode = INVOKE /\ ~MEM (Var v) call.inst_operands /\ ~MEM v call.inst_outputs /\
  dft_pos_pending_aligned_phase w C D fi bi pre gas call post zs H l r ==>
  ?A B Z. A 0 = 0 /\ B 0 = 0 /\ Z 0 = (zs,H) /\
    (!n. A n < A (SUC n) /\ B n < B (SUC n)) /\
    (!n. n <= A n /\ n <= B n) /\
    (!j. ?n. A n <= j /\ j < A (SUC n)) /\
    (!j. ?n. B n <= j /\ j < B (SUC n)) /\
    (!n. dft_pos_pending_aligned_phase w C D fi bi pre gas call post
      (FST (Z n)) (SND (Z n))
      (FUNPOW (dft_occ_oracle_next w C) (A n) l)
      (FUNPOW (dft_occ_oracle_next w D) (B n) r)) /\
    (!n. pending_segment_account C D w
      (A (SUC n) - A n) (B (SUC n) - B n)
      (FUNPOW (dft_occ_oracle_next w C) (A n) l)
      (FUNPOW (dft_occ_oracle_next w D) (B n) r)
      (dft_pos_pending_gas_events (FST (Z n)) ++ SND (Z n))
      (dft_pos_pending_gas_events (FST (Z (SUC n))) ++ SND (Z (SUC n))))
Proof
  strip_tac >>
  qspecl_then
    [`\z l r. dft_pos_pending_aligned_phase w C D fi bi pre gas call post (FST z) (SND z) l r`,
     `\z z' a b l r. pending_segment_account C D w a b l r
       (dft_pos_pending_gas_events (FST z) ++ SND z)
       (dft_pos_pending_gas_events (FST z') ++ SND z')`]
    (irule o SRULE []) (Q.GENL [`P`,`account`] dft_annotated_cofinal_segments) >> simp[] >>
  gvs[] >> rpt gen_tac >> strip_tac >>
  drule_at (Pat `dft_pos_pending_aligned_phase _ _ _ _ _ _ _ _ _ _ _ _ _`) dft_pending_bounded_closed >>
  simp[] >> disch_then (qspecl_then [`Dorig`,`Corig`] mp_tac) >> simp[] >> strip_tac >>
  qexistsl [`a`,`b`,`(zs',H')`] >> simp[]
QED

Theorem dft_pending_hits_add:
  dft_pending_segment_hits C w (a+b) l inst addr =
  dft_pending_segment_hits C w a l inst addr +
  dft_pending_segment_hits C w b
    (FUNPOW (dft_occ_oracle_next w C) a l) inst addr
Proof
  once_rewrite_tac[ADD_COMM] >>
  simp[dft_pending_segment_hits_def, GENLIST_APPEND, SUM_APPEND, FUNPOW_ADD]
QED

Theorem dft_pending_account_hits:
  pending_segment_account C D w a b l r B B' ==>
  dft_pending_segment_hits C w a l inst addr + dft_pending_ledger_hits B inst addr =
  dft_pending_segment_hits D w b r inst addr + dft_pending_ledger_hits B' inst addr
Proof
  simp[pending_segment_account_def]
QED

Theorem dft_pending_account_count:
  pending_segment_account C D w a b l r B B' ==>
  dft_occ_count (FUNPOW (dft_occ_oracle_next w C) a l) + dft_occ_count r + LENGTH B =
  dft_occ_count (FUNPOW (dft_occ_oracle_next w D) b r) + dft_occ_count l + LENGTH B'
Proof
  simp[pending_segment_account_def]
QED

Theorem dft_pending_prefix_hits:
  A 0 = 0 /\ B 0 = 0 /\
  (!n. A n <= A (SUC n) /\ B n <= B (SUC n)) /\
  (!n. pending_segment_account C D w
    (A (SUC n) - A n) (B (SUC n) - B n)
    (FUNPOW (dft_occ_oracle_next w C) (A n) l)
    (FUNPOW (dft_occ_oracle_next w D) (B n) r) (ledger n) (ledger (SUC n))) ==>
  !n inst addr.
    dft_pending_segment_hits C w (A n) l inst addr + dft_pending_ledger_hits (ledger 0) inst addr =
    dft_pending_segment_hits D w (B n) r inst addr + dft_pending_ledger_hits (ledger n) inst addr
Proof
  strip_tac >> Induct >- simp[] >> rpt gen_tac >>
  qpat_x_assum `!n. A n <= _ /\ _` (qspec_then `n` strip_assume_tac) >>
  qpat_x_assum `!n. pending_segment_account _ _ _ _ _ _ _ _ _` (qspec_then `n` assume_tac) >>
  `A (SUC n) = A n + (A (SUC n) - A n)` by decide_tac >>
  `B (SUC n) = B n + (B (SUC n) - B n)` by decide_tac >>
  drule_all dft_pending_account_hits >>
  disch_then (qspecl_then [`inst`,`addr`] mp_tac) >>
  once_asm_rewrite_tac[] >> simp[dft_pending_hits_add] >>
  first_x_assum (qspecl_then [`inst`,`addr`] mp_tac) >> decide_tac
QED

Theorem dft_pending_prefix_count:
  A 0 = 0 /\ B 0 = 0 /\
  (!n. A n <= A (SUC n) /\ B n <= B (SUC n)) /\
  (!n. pending_segment_account C D w
    (A (SUC n) - A n) (B (SUC n) - B n)
    (FUNPOW (dft_occ_oracle_next w C) (A n) l)
    (FUNPOW (dft_occ_oracle_next w D) (B n) r) (ledger n) (ledger (SUC n))) ==>
  !n. dft_occ_count (FUNPOW (dft_occ_oracle_next w C) (A n) l) +
        dft_occ_count r + LENGTH (ledger 0) =
      dft_occ_count (FUNPOW (dft_occ_oracle_next w D) (B n) r) +
        dft_occ_count l + LENGTH (ledger n)
Proof
  strip_tac >> Induct >- simp[] >>
  qpat_x_assum `!n. A n <= _ /\ _` (qspec_then `n` strip_assume_tac) >>
  qpat_x_assum `!n. pending_segment_account _ _ _ _ _ _ _ _ _` (qspec_then `n` assume_tac) >>
  drule_all dft_pending_account_count >>
  simp[GSYM FUNPOW_ADD] >>
  `A (SUC n) - A n + A n = A (SUC n)` by decide_tac >>
  `B (SUC n) - B n + B n = B (SUC n)` by decide_tac >>
  simp[] >> decide_tac
QED

Theorem dft_pending_hits_positive:
  0 < dft_pending_segment_hits C w a l inst addr <=>
  ?j. j < a /\ dft_occ_gas_event inst addr (FUNPOW (dft_occ_oracle_next w C) j l)
Proof
  Induct_on `a` >- simp[] >>
  gvs[dft_pending_segment_hits_def, GENLIST, SUM_SNOC] >>
  Cases_on `dft_occ_gas_event inst addr (FUNPOW (dft_occ_oracle_next w C) a l)`
  >- (simp[] >> qexists `a` >> simp[]) >>
  simp[] >> eq_tac >> strip_tac
  >- (qexists `j` >> simp[]) >>
  `j < a` by (Cases_on `j = a` >> gvs[]) >> metis_tac[]
QED

Theorem dft_pending_ledger_positive:
  0 < dft_pending_ledger_hits B inst addr <=> MEM (inst,addr) B
Proof
  Induct_on `B` >- simp[] >> gen_tac >>
  Cases_on `h = (inst,addr)` >> gvs[dft_pending_ledger_hits_def]
QED

Theorem dft_pending_right_event_coverage:
  (!n. n <= B n) /\
  (!n inst addr. dft_pending_segment_hits C w (A n) l inst addr =
    dft_pending_segment_hits D w (B n) r inst addr +
    dft_pending_ledger_hits (ledger n) inst addr) /\
  dft_occ_gas_event inst addr (FUNPOW (dft_occ_oracle_next w D) j r) ==>
  ?i. dft_occ_gas_event inst addr (FUNPOW (dft_occ_oracle_next w C) i l)
Proof
  strip_tac >>
  `j < B (SUC j)` by
    (qpat_x_assum `!n. n <= B n` (qspec_then `SUC j` mp_tac) >> decide_tac) >>
  `0 < dft_pending_segment_hits D w (B (SUC j)) r inst addr` by
    (simp[dft_pending_hits_positive] >> qexists `j` >> simp[]) >>
  qpat_x_assum `!n inst addr. _ = _` (qspecl_then [`SUC j`,`inst`,`addr`] mp_tac) >>
  strip_tac >>
  `0 < dft_pending_segment_hits C w (A (SUC j)) l inst addr` by decide_tac >>
  fs[dft_pending_hits_positive] >> metis_tac[]
QED

Theorem dft_pending_left_event_residual:
  (!n inst addr. dft_pending_segment_hits C w (A n) l inst addr =
    dft_pending_segment_hits D w (B n) r inst addr +
    dft_pending_ledger_hits (ledger n) inst addr) /\
  dft_occ_gas_event inst addr (FUNPOW (dft_occ_oracle_next w C) j l) /\
  (!k. ~dft_occ_gas_event inst addr (FUNPOW (dft_occ_oracle_next w D) k r)) ==>
  !n. j < A n ==> MEM (inst,addr) (ledger n)
Proof
  rpt strip_tac >>
  `0 < dft_pending_segment_hits C w (A n) l inst addr` by
    (simp[dft_pending_hits_positive] >> qexists `j` >> simp[]) >>
  `dft_pending_segment_hits D w (B n) r inst addr = 0` by
    (CCONTR_TAC >> `0 < dft_pending_segment_hits D w (B n) r inst addr` by decide_tac >>
     fs[dft_pending_hits_positive] >> metis_tac[]) >>
  qpat_x_assum `!n inst addr. _ = _` (qspecl_then [`n`,`inst`,`addr`] mp_tac) >>
  simp[] >> strip_tac >>
  `0 < dft_pending_ledger_hits (ledger n) inst addr` by decide_tac >>
  fs[dft_pending_ledger_positive]
QED

Theorem dft_pending_account_compose:
  pending_segment_account C D w a b l r B0 B1 /\
  pending_segment_account C D w c d
    (FUNPOW (dft_occ_oracle_next w C) a l)
    (FUNPOW (dft_occ_oracle_next w D) b r) B1 B2 ==>
  pending_segment_account C D w (a+c) (b+d) l r B0 B2
Proof
  strip_tac >> simp[pending_segment_account_def] >>
  conj_tac >- suspend "hits" >>
  conj_tac >- suspend "count" >>
  conj_tac >- suspend "left_observe" >>
  suspend "right_observe"
QED

Resume dft_pending_account_compose[hits]:
  rpt gen_tac >>
  drule_all dft_pending_account_hits >>
  disch_then (qspecl_then [`inst`,`addr`] assume_tac) >>
  qpat_x_assum `pending_segment_account _ _ _ a _ _ _ _ _`
    (mp_then Any (qspecl_then [`inst`,`addr`] assume_tac) dft_pending_account_hits) >>
  simp[dft_pending_hits_add] >> decide_tac
QED

Resume dft_pending_account_compose[count]:
  drule_all dft_pending_account_count >> strip_tac >>
  qpat_x_assum `pending_segment_account _ _ _ a _ _ _ _ _`
    (mp_then Any assume_tac dft_pending_account_count) >>
  fs[GSYM FUNPOW_ADD] >> fs[AC ADD_ASSOC ADD_COMM] >> decide_tac
QED

Resume dft_pending_account_compose[left_observe]:
  rpt strip_tac >>
  qpat_x_assum `pending_segment_account _ _ _ a _ _ _ _ _`
    (mp_then Any assume_tac (cj 3 (iffLR pending_segment_account_def))) >>
  qpat_x_assum `pending_segment_account _ _ _ c _ _ _ _ _`
    (mp_then Any assume_tac (cj 3 (iffLR pending_segment_account_def))) >>
  Cases_on `j < a`
  >- (first_x_assum drule_all >> strip_tac >>
      qexistsl [`k`,`g`,`t`] >> simp[]) >>
  `j - a < c /\ j - a + a = j` by decide_tac >>
  `dft_open_observe f inst s
     (FUNPOW (dft_occ_oracle_next w C) (j-a)
       (FUNPOW (dft_occ_oracle_next w C) a l)).dft_occ_core` by
    simp[GSYM FUNPOW_ADD] >>
  first_x_assum drule_all >> strip_tac >>
  qexistsl [`k+b`,`g`,`t`] >> simp[FUNPOW_ADD]
QED

Resume dft_pending_account_compose[right_observe]:
  rpt strip_tac >>
  qpat_x_assum `pending_segment_account _ _ _ a _ _ _ _ _`
    (mp_then Any assume_tac (cj 4 (iffLR pending_segment_account_def))) >>
  qpat_x_assum `pending_segment_account _ _ _ c _ _ _ _ _`
    (mp_then Any assume_tac (cj 4 (iffLR pending_segment_account_def))) >>
  Cases_on `k < b`
  >- (first_x_assum drule_all >> strip_tac >>
      qexistsl [`j`,`f`,`s`] >> simp[]) >>
  `k - b < d /\ k - b + b = k` by decide_tac >>
  `dft_open_observe g inst t
     (FUNPOW (dft_occ_oracle_next w D) (k-b)
       (FUNPOW (dft_occ_oracle_next w D) b r)).dft_occ_core` by
    simp[GSYM FUNPOW_ADD] >>
  first_x_assum drule_all >> strip_tac >>
  qexistsl [`j+a`,`f`,`s`] >> simp[FUNPOW_ADD]
QED

Finalise dft_pending_account_compose

Theorem dft_pending_orbit_observe_forward:
  (!j. ?n. A n <= j /\ j < A (SUC n)) /\
  (!n. pending_segment_account C D w
    (A (SUC n) - A n) (B (SUC n) - B n)
    (FUNPOW (dft_occ_oracle_next w C) (A n) l)
    (FUNPOW (dft_occ_oracle_next w D) (B n) r) (ledger n) (ledger (SUC n))) /\
  dft_open_observe f inst s (FUNPOW (dft_occ_oracle_next w C) j l).dft_occ_core /\
  inst_mem_ranges inst s <> [] ==>
  ?k g t. dft_pos_functions C D f g /\
    dft_open_observe g inst t (FUNPOW (dft_occ_oracle_next w D) k r).dft_occ_core /\
    t.vs_memory = s.vs_memory /\ inst_mem_ranges inst t = inst_mem_ranges inst s
Proof
  strip_tac >>
  qpat_x_assum `!j. ?n. _` (qspec_then `j` strip_assume_tac) >>
  `j - A n < A (SUC n) - A n` by decide_tac >>
  `dft_open_observe f inst s
    (FUNPOW (dft_occ_oracle_next w C) (j - A n)
      (FUNPOW (dft_occ_oracle_next w C) (A n) l)).dft_occ_core` by
    metis_tac[dft_cut_offset] >>
  qpat_x_assum `!n. pending_segment_account _ _ _ _ _ _ _ _ _`
    (qspec_then `n` (mp_then Any mp_tac (cj 3 (iffLR pending_segment_account_def)))) >>
  disch_then drule_all >> strip_tac >>
  qexistsl [`k + B n`,`g`,`t`] >> simp[FUNPOW_ADD]
QED

Theorem dft_pending_orbit_observe_backward:
  (!j. ?n. B n <= j /\ j < B (SUC n)) /\
  (!n. pending_segment_account C D w
    (A (SUC n) - A n) (B (SUC n) - B n)
    (FUNPOW (dft_occ_oracle_next w C) (A n) l)
    (FUNPOW (dft_occ_oracle_next w D) (B n) r) (ledger n) (ledger (SUC n))) /\
  dft_open_observe g inst t (FUNPOW (dft_occ_oracle_next w D) k r).dft_occ_core /\
  inst_mem_ranges inst t <> [] ==>
  ?j f s. dft_pos_functions C D f g /\
    dft_open_observe f inst s (FUNPOW (dft_occ_oracle_next w C) j l).dft_occ_core /\
    t.vs_memory = s.vs_memory /\ inst_mem_ranges inst t = inst_mem_ranges inst s
Proof
  strip_tac >>
  qpat_x_assum `!j. ?n. _` (qspec_then `k` strip_assume_tac) >>
  `k - B n < B (SUC n) - B n` by decide_tac >>
  `dft_open_observe g inst t
    (FUNPOW (dft_occ_oracle_next w D) (k - B n)
      (FUNPOW (dft_occ_oracle_next w D) (B n) r)).dft_occ_core` by
    metis_tac[dft_cut_offset] >>
  qpat_x_assum `!n. pending_segment_account _ _ _ _ _ _ _ _ _`
    (qspec_then `n` (mp_then Any mp_tac (cj 4 (iffLR pending_segment_account_def)))) >>
  disch_then drule_all >> strip_tac >>
  qexistsl [`j + A n`,`f`,`s`] >> simp[FUNPOW_ADD]
QED

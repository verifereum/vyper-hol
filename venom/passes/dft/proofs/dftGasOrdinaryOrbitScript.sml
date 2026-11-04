Theory dftGasOrdinaryOrbit
Ancestors
  dftGasOrdinaryTrace dftOrdinaryEventTrace dftOriginalOrbit dftOriginalRuntime
  dftOccurrenceOrdinaryClosure dftOccurrenceGasEdit dftOccurrenceCallTrace
  dftOpenMachine dftOpenErase list arithmetic

Theorem dft_gas_ordinary_endpoint_root:
  dft_gas_ordinary_endpoint q pre x y post c d /\
  c.dft_occ_core = DftOpen (DftDone r) [] n ==>
  ?r' n'. d.dft_occ_core = DftOpen (DftDone r') [] n' /\
    dft_ordinary_result_rel r r'
Proof
  strip_tac >> fs[dft_gas_ordinary_endpoint_def]
  >- (irule dft_ordinary_endpoint_root >>
      simp[dft_ordinary_endpoint_def] >> metis_tac[]) >>
  fs[dft_gas_ordinary_stopped_def, dft_ordinary_result_rel_def] >> metis_tac[]
QED

Theorem dft_original_mixed_orbit_cofinal:
  !m c d.
  dft_original_gas_ordinary_environment Corig C L q pre x y post /\
  dft_original_label_ready C L c /\ dft_gas_ordinary_endpoint q pre x y post c d ==>
  ?p r. m <= p /\ m <= r /\
    dft_gas_ordinary_endpoint q pre x y post
      (FUNPOW (dft_occ_oracle_next w C) p c)
      (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x y post C)) r d) /\
    dft_original_label_ready C L (FUNPOW (dft_occ_oracle_next w C) p c)
Proof
  Induct
  >- (rpt strip_tac >> qexistsl_tac [`0`, `0`] >> simp[FUNPOW]) >>
  rpt strip_tac >> first_x_assum drule_all >> strip_tac >>
  drule_all dft_original_mixed_endpoint_segment >>
  disch_then (qspec_then `w` strip_assume_tac) >>
  qexistsl_tac [`p + k`, `r + j`] >>
  conj_tac >- decide_tac >> conj_tac >- decide_tac >>
  gvs[GSYM FUNPOW_ADD, ADD_COMM]
QED

Theorem dft_original_mixed_orbit_terminal:
  dft_original_gas_ordinary_environment Corig C L q pre x y post /\
  dft_original_label_ready C L c /\ dft_gas_ordinary_endpoint q pre x y post c d /\
  (FUNPOW (dft_occ_oracle_next w C) h c).dft_occ_core =
    DftOpen (DftDone r) [] n ==>
  ?j r' n'.
    (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x y post C)) j d).dft_occ_core =
      DftOpen (DftDone r') [] n' /\ dft_ordinary_result_rel r r'
Proof
  strip_tac >> drule_all dft_original_mixed_orbit_cofinal >>
  disch_then (qspecl_then [`w`, `h`] strip_assume_tac) >>
  `?delta. p = delta + h` by (qexists_tac `p - h` >> decide_tac) >>
  `?n. (FUNPOW (dft_occ_oracle_next w C) p c).dft_occ_core =
     DftOpen (DftDone r) [] n` by
    (gvs[FUNPOW_ADD] >> irule dft_occ_oracle_root_absorb >> metis_tac[]) >>
  drule_all dft_gas_ordinary_endpoint_root >> metis_tac[]
QED

Theorem dft_original_mixed_root_terminal:
  dft_original_gas_ordinary_environment Corig C s.vs_labels q pre x y post /\
  dft_original_function f fn /\ fn_reachable f s.vs_current_bb /\
  strict_dom_vars_defined f s /\ MEM fn C.ctx_functions ==>
  !h r n'.
    (FUNPOW (dft_occ_oracle_next w C) h
      (dft_occ_init (DftOpen (DftEnter fn 0 s) [] n))).dft_occ_core =
        DftOpen (DftDone r) [] n' ==>
    ?j r' n''.
      (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x y post C)) j
        (dft_occ_init (DftOpen
          (DftEnter (dft_gas_edit_fn q pre x y post fn) 0 s) [] n))).dft_occ_core =
        DftOpen (DftDone r') [] n'' /\ dft_ordinary_result_rel r r'
Proof
  strip_tac >>
  `dft_original_label_ready C s.vs_labels
    (dft_occ_init (DftOpen (DftEnter fn 0 s) [] n))` by
    (irule dft_original_label_root >> metis_tac[]) >>
  `dft_gas_ordinary_endpoint q pre x y post
    (dft_occ_init (DftOpen (DftEnter fn 0 s) [] n))
    (dft_occ_init (DftOpen
      (DftEnter (dft_gas_edit_fn q pre x y post fn) 0 s) [] n))` by
    simp[dft_gas_ordinary_endpoint_def, dft_ordinary_sync_init] >>
  rpt strip_tac >> irule dft_original_mixed_orbit_terminal >> metis_tac[]
QED

Theorem dft_original_mixed_orbit_observe:
  !h c d f i t.
  dft_original_gas_ordinary_environment Corig C L q pre x y post /\
  dft_original_label_ready C L c /\ dft_gas_ordinary_endpoint q pre x y post c d /\
  dft_open_observe f i t
    (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x y post C)) h d).dft_occ_core /\
  inst_mem_ranges i t <> [] ==>
  ?l g s. f = dft_gas_edit_fn q pre x y post g /\
    dft_open_observe g i s (FUNPOW (dft_occ_oracle_next w C) l c).dft_occ_core /\
    (!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t) /\
    inst_mem_ranges i s = inst_mem_ranges i t /\ s.vs_memory = t.vs_memory
Proof
  completeInduct_on `h` >> rpt strip_tac >>
  drule_all dft_original_mixed_endpoint_segment >>
  disch_then (qspec_then `w` strip_assume_tac) >>
  Cases_on `h < j`
  >- (drule_all dft_ordinary_prefix_cover_shift >> metis_tac[]) >>
  `h - j < h /\ h = (h - j) + j` by decide_tac >>
  first_x_assum (qspec_then `h - j` mp_tac) >> simp[] >>
  disch_then (qspecl_then
    [`FUNPOW (dft_occ_oracle_next w C) k c`,
     `FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x y post C)) j d`,
     `f`, `i`, `t`] mp_tac) >>
  simp[GSYM FUNPOW_ADD] >> strip_tac >>
  qexistsl_tac [`k + l`, `g`, `s`] >> simp[]
QED

Theorem dft_original_mixed_root_observe:
  dft_original_gas_ordinary_environment Corig C s.vs_labels q pre x y post /\
  dft_original_function f fn /\ fn_reachable f s.vs_current_bb /\
  strict_dom_vars_defined f s /\ MEM fn C.ctx_functions ==>
  !h g i t.
    dft_open_observe g i t
      (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x y post C)) h
        (dft_occ_init (DftOpen
          (DftEnter (dft_gas_edit_fn q pre x y post fn) 0 s) [] n))).dft_occ_core /\
    inst_mem_ranges i t <> [] ==>
    ?l g' u. g = dft_gas_edit_fn q pre x y post g' /\
      dft_open_observe g' i u
        (FUNPOW (dft_occ_oracle_next w C) l
          (dft_occ_init (DftOpen (DftEnter fn 0 s) [] n))).dft_occ_core /\
      (!op. MEM op i.inst_operands ==> eval_operand op u = eval_operand op t) /\
      inst_mem_ranges i u = inst_mem_ranges i t /\ u.vs_memory = t.vs_memory
Proof
  strip_tac >>
  `dft_original_label_ready C s.vs_labels
    (dft_occ_init (DftOpen (DftEnter fn 0 s) [] n))` by
    (irule dft_original_label_root >> metis_tac[]) >>
  `dft_gas_ordinary_endpoint q pre x y post
    (dft_occ_init (DftOpen (DftEnter fn 0 s) [] n))
    (dft_occ_init (DftOpen
      (DftEnter (dft_gas_edit_fn q pre x y post fn) 0 s) [] n))` by
    simp[dft_gas_ordinary_endpoint_def, dft_ordinary_sync_init] >>
  rpt strip_tac >> irule dft_original_mixed_orbit_observe >> metis_tac[]
QED

(* Local provenance only: no claim about absence in a later edited orbit. *)
Definition dft_mixed_discard_def:
  dft_mixed_discard w C L q pre x y post c d left i a <=>
    ?p r k j.
      let u = FUNPOW (dft_occ_oracle_next w C) p c;
          v = FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x y post C)) r d in
      dft_original_label_ready C L u /\
      dft_gas_ordinary_endpoint q pre x y post u v /\
      0 < k /\ k <= 3 /\ 0 < j /\ j <= 3 /\
      dft_gas_ordinary_stopped
        (FUNPOW (dft_occ_oracle_next w C) k u)
        (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x y post C)) j v) /\
      i = (if left then x else y) /\ i.inst_opcode = GAS /\
      a = u.dft_occ_path ++ [(u.dft_occ_visit,i.inst_id)] /\
      (if left then
        ((!z b. (?h. h < k /\ dft_occ_gas_event z b
          (FUNPOW (dft_occ_oracle_next w C) h u)) <=> z = i /\ b = a) /\
         (!h z b. h < j ==> ~dft_occ_gas_event z b
          (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x y post C)) h v)))
       else
        ((!z b. (?h. h < j /\ dft_occ_gas_event z b
          (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x y post C)) h v))
             <=> z = i /\ b = a) /\
         (!h z b. h < k ==> ~dft_occ_gas_event z b
          (FUNPOW (dft_occ_oracle_next w C) h u))))
End

Theorem dft_mixed_discard_shift:
  dft_mixed_discard w C L q pre x y post
    (FUNPOW (dft_occ_oracle_next w C) k c)
    (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x y post C)) j d)
    left i a ==>
  dft_mixed_discard w C L q pre x y post c d left i a
Proof
  simp[dft_mixed_discard_def] >> strip_tac >>
  qexistsl_tac [`p + k`, `r + j`, `k'`, `j'`] >>
  Cases_on `left` >> gvs[FUNPOW_ADD]
QED

Theorem dft_mixed_segment_event_forward:
  dft_original_label_ready C L c /\
  dft_gas_ordinary_endpoint q pre x y post c d /\
  0 < k /\ k <= 3 /\ 0 < j /\ j <= 3 /\
  dft_mixed_segment_events w C (dft_gas_edit_ctx q pre x y post C) x y c d k j /\
  h < k /\ dft_occ_gas_event i a (FUNPOW (dft_occ_oracle_next w C) h c) ==>
  (?t. dft_occ_gas_event i a
    (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x y post C)) t d)) \/
  dft_mixed_discard w C L q pre x y post c d T i a
Proof
  strip_tac >> fs[dft_mixed_segment_events_def]
  >- (disj1_tac >> fs[dft_segment_gas_cover_def] >> metis_tac[]) >>
  disj2_tac >> simp[dft_mixed_discard_def] >>
  qexistsl_tac [`0`, `0`, `k`, `j`] >> simp[FUNPOW] >> metis_tac[]
QED

Theorem dft_mixed_segment_event_backward:
  dft_original_label_ready C L c /\
  dft_gas_ordinary_endpoint q pre x y post c d /\
  0 < k /\ k <= 3 /\ 0 < j /\ j <= 3 /\
  dft_mixed_segment_events w C (dft_gas_edit_ctx q pre x y post C) x y c d k j /\
  h < j /\ dft_occ_gas_event i a
    (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x y post C)) h d) ==>
  (?t. dft_occ_gas_event i a (FUNPOW (dft_occ_oracle_next w C) t c)) \/
  dft_mixed_discard w C L q pre x y post c d F i a
Proof
  strip_tac >> fs[dft_mixed_segment_events_def]
  >- (disj1_tac >> fs[dft_segment_gas_cover_def] >> metis_tac[]) >>
  disj2_tac >> simp[dft_mixed_discard_def] >>
  qexistsl_tac [`0`, `0`, `k`, `j`] >> simp[FUNPOW] >> metis_tac[]
QED

Theorem dft_original_mixed_orbit_gas_forward:
  !h c d i a.
  dft_original_gas_ordinary_environment Corig C L q pre x y post /\
  dft_original_label_ready C L c /\ dft_gas_ordinary_endpoint q pre x y post c d /\
  dft_occ_gas_event i a (FUNPOW (dft_occ_oracle_next w C) h c) ==>
  (?t. dft_occ_gas_event i a
    (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x y post C)) t d)) \/
  dft_mixed_discard w C L q pre x y post c d T i a
Proof
  completeInduct_on `h` >> rpt strip_tac >>
  drule_all dft_original_mixed_endpoint_segment >>
  disch_then (qspec_then `w` strip_assume_tac) >>
  Cases_on `h < k`
  >- (drule_all dft_mixed_segment_event_forward >> simp[]) >>
  `h - k < h /\ h = (h - k) + k` by decide_tac >>
  first_x_assum (qspec_then `h - k` mp_tac) >> simp[] >>
  disch_then (qspecl_then
    [`FUNPOW (dft_occ_oracle_next w C) k c`,
     `FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x y post C)) j d`,
     `i`, `a`] mp_tac) >>
  simp[GSYM FUNPOW_ADD] >> strip_tac
  >- (disj1_tac >> qexists `j + t` >> simp[]) >>
  disj2_tac >> irule dft_mixed_discard_shift >> metis_tac[]
QED

Theorem dft_original_mixed_orbit_gas_backward:
  !h c d i a.
  dft_original_gas_ordinary_environment Corig C L q pre x y post /\
  dft_original_label_ready C L c /\ dft_gas_ordinary_endpoint q pre x y post c d /\
  dft_occ_gas_event i a
    (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x y post C)) h d) ==>
  (?t. dft_occ_gas_event i a (FUNPOW (dft_occ_oracle_next w C) t c)) \/
  dft_mixed_discard w C L q pre x y post c d F i a
Proof
  completeInduct_on `h` >> rpt strip_tac >>
  drule_all dft_original_mixed_endpoint_segment >>
  disch_then (qspec_then `w` strip_assume_tac) >>
  Cases_on `h < j`
  >- (drule_all dft_mixed_segment_event_backward >> simp[]) >>
  `h - j < h /\ h = (h - j) + j` by decide_tac >>
  first_x_assum (qspec_then `h - j` mp_tac) >> simp[] >>
  disch_then (qspecl_then
    [`FUNPOW (dft_occ_oracle_next w C) k c`,
     `FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x y post C)) j d`,
     `i`, `a`] mp_tac) >>
  simp[GSYM FUNPOW_ADD] >> strip_tac
  >- (disj1_tac >> qexists `k + t` >> simp[]) >>
  disj2_tac >> irule dft_mixed_discard_shift >> metis_tac[]
QED

Theorem dft_original_mixed_root_events:
  dft_original_gas_ordinary_environment Corig C s.vs_labels q pre x y post /\
  dft_original_function f fn /\ fn_reachable f s.vs_current_bb /\
  strict_dom_vars_defined f s /\ MEM fn C.ctx_functions ==>
  let c = dft_occ_init (DftOpen (DftEnter fn 0 s) [] n);
      d = dft_occ_init (DftOpen
        (DftEnter (dft_gas_edit_fn q pre x y post fn) 0 s) [] n) in
  (!h i a. dft_occ_gas_event i a (FUNPOW (dft_occ_oracle_next w C) h c) ==>
    (?t. dft_occ_gas_event i a
      (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x y post C)) t d)) \/
    dft_mixed_discard w C s.vs_labels q pre x y post c d T i a) /\
  (!h i a. dft_occ_gas_event i a
      (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x y post C)) h d) ==>
    (?t. dft_occ_gas_event i a (FUNPOW (dft_occ_oracle_next w C) t c)) \/
    dft_mixed_discard w C s.vs_labels q pre x y post c d F i a)
Proof
  strip_tac >>
  `dft_original_label_ready C s.vs_labels
    (dft_occ_init (DftOpen (DftEnter fn 0 s) [] n))` by
    (irule dft_original_label_root >> metis_tac[]) >>
  `dft_gas_ordinary_endpoint q pre x y post
    (dft_occ_init (DftOpen (DftEnter fn 0 s) [] n))
    (dft_occ_init (DftOpen
      (DftEnter (dft_gas_edit_fn q pre x y post fn) 0 s) [] n))` by
    simp[dft_gas_ordinary_endpoint_def, dft_ordinary_sync_init] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> drule_all dft_original_mixed_orbit_gas_forward >> simp[]) >>
  rpt strip_tac >> drule_all dft_original_mixed_orbit_gas_backward >> simp[]
QED

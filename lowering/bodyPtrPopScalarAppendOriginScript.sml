Theory bodyPtrPopScalarAppendOrigin
Ancestors
  bodyPtrPopRegionInvariant bodyPtrPopSynchronizedStore
  compileEnv vyperValue words pred_set ptrDiscipline vyperStorage vfmState

Theorem pop_region_taint_scalar_phase:
  bs + 1 + n <= dimword (:256) /\ l <= n /\
  lookup_storage (n2w bs) st = n2w l ==>
  (pop_region_taint_ok st bs (ArrayTV (BaseTV (UintT 256)) (Dynamic n)) X <=>
   !k b. (k,b) IN X /\ bs <= w2n k /\ w2n k < bs + 1 + n /\ b < 32 ==>
         bs + 1 + l <= w2n k)
Proof
  strip_tac >>
  simp[pop_region_taint_ok_def, type_slot_size_def, dead_bytes_def] >>
  eq_tac >> rpt strip_tac
  >- (first_x_assum drule_all >> strip_tac >> decide_tac) >>
  first_x_assum drule_all >> strip_tac >>
  qexists_tac `w2n k - (bs + 1)` >> decide_tac
QED

Theorem pop_region_taint_scalar_append:
  bs + 1 + n <= dimword (:256) /\ l < n /\
  lookup_storage (n2w bs) st = n2w l /\
  pop_region_taint_ok st bs (ArrayTV (BaseTV (UintT 256)) (Dynamic n)) X ==>
  pop_region_taint_ok
    (update_storage (n2w bs) (n2w (l+1))
      (update_storage (n2w (bs+1+l)) value st)) bs
    (ArrayTV (BaseTV (UintT 256)) (Dynamic n))
    (key_update (key_update X (n2w (bs+1+l)) {}) (n2w bs) {})
Proof
  strip_tac >>
  `l <= n /\ l+1 <= n` by decide_tac >>
  drule_all pop_region_taint_scalar_phase >> strip_tac >>
  `lookup_storage (n2w bs)
    (update_storage (n2w bs) (n2w (l+1))
      (update_storage (n2w (bs+1+l)) value st)) = n2w (l+1)` by
    simp[lookup_storage_def, update_storage_def] >>
  drule_all pop_region_taint_scalar_phase >>
  disch_then (fn th => rewrite_tac[th]) >>
  qpat_x_assum `!X. _` (fn th => fs[th]) >>
  simp[key_update_def] >> rpt strip_tac >>
  `bs+1+l < dimword (:256)` by decide_tac >>
  `w2n (n2w (bs+1+l) : bytes32) = bs+1+l` by simp[] >>
  `bs+1+l <= w2n k` by
    (first_x_assum drule_all >> decide_tac) >>
  `w2n k <> bs+1+l` by
    (strip_tac >> qpat_x_assum `k <> n2w (bs + (l + 1))` mp_tac >>
     `bs + (l+1) = w2n k` by decide_tac >>
     pop_assum (fn th => pure_rewrite_tac[th, n2w_w2n]) >> simp[NoAsms]) >>
  decide_tac
QED

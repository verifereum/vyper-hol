Theory dftPendingEventTrace
Ancestors
  dftPendingSuspension dftMixedResidualProbe dftOccurrenceMachine
  dftOccurrenceReplay dftOpenMachine dftOpenErase list

Theorem dft_pending_suspended_gas_event:
  dft_pending_suspended us fL fR tL tR sL sR path visit l r ==>
  (dft_occ_gas_event i a l <=> dft_occ_gas_event i a r)
Proof
  simp[dft_pending_suspended_def] >> rpt strip_tac >>
  Cases_on `ctl` >>
  gvs[dft_occ_gas_event_def, dft_occ_event_def] >> metis_tac[]
QED

(* The exit itself is deliberately excluded from the event clause. A resumed
   caller need not fetch the same instruction on its two sides. *)
Theorem dft_pending_suspended_prefix_event:
  dft_pending_suspended us fL fR tL tR sL sR path visit l r ==>
  !j.
    ((!k. k <= j ==>
      dft_pending_suspended us fL fR tL tR sL sR path visit
        (FUNPOW (dft_occ_oracle_next w C) k l)
        (FUNPOW (dft_occ_oracle_next w C) k r) /\
      (!i a. dft_occ_gas_event i a (FUNPOW (dft_occ_oracle_next w C) k l) <=>
        dft_occ_gas_event i a (FUNPOW (dft_occ_oracle_next w C) k r))) \/
    ?h. 0 < h /\ h <= j /\
      dft_pending_exit us fL fR tL tR sL sR path visit
        (FUNPOW (dft_occ_oracle_next w C) h l)
        (FUNPOW (dft_occ_oracle_next w C) h r) /\
      !k. k < h ==>
        dft_pending_suspended us fL fR tL tR sL sR path visit
          (FUNPOW (dft_occ_oracle_next w C) k l)
          (FUNPOW (dft_occ_oracle_next w C) k r) /\
        (!i a. dft_occ_gas_event i a (FUNPOW (dft_occ_oracle_next w C) k l) <=>
          dft_occ_gas_event i a (FUNPOW (dft_occ_oracle_next w C) k r)))
Proof
  strip_tac >> gen_tac >> drule dft_pending_suspended_prefix >>
  disch_then (qspecl_then [`w`, `C`, `j`] strip_assume_tac)
  >- (disj1_tac >> metis_tac[dft_pending_suspended_gas_event]) >>
  disj2_tac >> qexists_tac `h` >> simp[] >>
  metis_tac[dft_pending_suspended_gas_event]
QED

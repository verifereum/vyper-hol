Theory dftOrbitObservation
Ancestors
  dftRootedOrbitTerminal dftRootedMixedCoverage dftRootedGasOrbit
  dftOpenMachine dftOccurrenceMachine

(* Administrative counts and abort states are deliberately not observations.
   Instructions may change (operand flips), but their memory ranges may not. *)
Definition dft_terminal_observation_def:
  dft_terminal_observation rr rr' <=>
    rr' = rr \/ (?a s t. rr = Abort a s /\ rr' = Abort a t)
End

Definition dft_orbit_observation_def:
  dft_orbit_observation w C D c d <=>
    (!j rr n.
      (FUNPOW (dft_occ_oracle_next w C) j c).dft_occ_core =
        DftOpen (DftDone rr) [] n ==>
      ?k rr' m.
        (FUNPOW (dft_occ_oracle_next w D) k d).dft_occ_core =
          DftOpen (DftDone rr') [] m /\
        dft_terminal_observation rr rr') /\
    (!k g i t.
      dft_open_observe g i t
        (FUNPOW (dft_occ_oracle_next w D) k d).dft_occ_core /\
      inst_mem_ranges i t <> [] ==>
      ?j f h s.
        dft_open_observe f h s
          (FUNPOW (dft_occ_oracle_next w C) j c).dft_occ_core /\
        t.vs_memory = s.vs_memory /\ inst_mem_ranges i t = inst_mem_ranges h s)
End

Theorem dft_terminal_observation_refl[simp]:
  dft_terminal_observation rr rr
Proof
  simp[dft_terminal_observation_def]
QED

Theorem dft_terminal_observation_trans:
  dft_terminal_observation a b /\ dft_terminal_observation b c ==>
  dft_terminal_observation a c
Proof
  rw[dft_terminal_observation_def] >> gvs[] >> metis_tac[]
QED

Theorem dft_orbit_observation_refl:
  dft_orbit_observation w C C c c
Proof
  rw[dft_orbit_observation_def] >> metis_tac[dft_terminal_observation_refl]
QED

Theorem dft_orbit_observation_trans:
  dft_orbit_observation w C D c d /\
  dft_orbit_observation w D E d e ==>
  dft_orbit_observation w C E c e
Proof
  rewrite_tac[dft_orbit_observation_def] >> rpt strip_tac
  >- metis_tac[dft_terminal_observation_trans] >>
  metis_tac[]
QED

Theorem dft_gas_orbit_observation_forward:
  dft_pos_gas_orbit_cuts C D w fi bi pre c d A B ==>
  dft_orbit_observation w C D c d
Proof
  strip_tac >> rewrite_tac[dft_orbit_observation_def] >> conj_tac
  >- (rpt strip_tac >> drule_all dft_root_gas_orbit_terminal_forward >>
      metis_tac[dft_terminal_observation_refl]) >>
  rpt strip_tac >> drule_all dft_pos_gas_orbit_observe_backward >>
  metis_tac[]
QED

Theorem dft_gas_orbit_observation_backward:
  dft_pos_gas_orbit_cuts C D w fi bi pre c d A B ==>
  dft_orbit_observation w D C d c
Proof
  strip_tac >> rewrite_tac[dft_orbit_observation_def] >> conj_tac
  >- (rpt strip_tac >> drule_all dft_root_gas_orbit_terminal_backward >>
      metis_tac[dft_terminal_observation_refl]) >>
  rpt strip_tac >> drule_all dft_pos_gas_orbit_observe_forward >>
  metis_tac[]
QED

Theorem dft_mixed_orbit_observation_forward:
  dft_pos_mixed_orbit_cuts C D w fi bi pre gas inst c d A B ==>
  dft_orbit_observation w C D c d
Proof
  strip_tac >> rewrite_tac[dft_orbit_observation_def] >> conj_tac
  >- (rpt strip_tac >> drule_all dft_root_mixed_orbit_terminal_forward >>
      rewrite_tac[dft_terminal_observation_def] >> metis_tac[]) >>
  rpt strip_tac >> drule_all dft_pos_mixed_orbit_observe_backward >>
  metis_tac[]
QED

Theorem dft_mixed_orbit_observation_backward:
  dft_pos_mixed_orbit_cuts C D w fi bi pre gas inst c d A B ==>
  dft_orbit_observation w D C d c
Proof
  strip_tac >> rewrite_tac[dft_orbit_observation_def] >> conj_tac
  >- (rpt strip_tac >> drule_all dft_root_mixed_orbit_terminal_backward >>
      rewrite_tac[dft_terminal_observation_def] >> metis_tac[]) >>
  rpt strip_tac >> drule_all dft_pos_mixed_orbit_observe_forward >>
  metis_tac[]
QED

Theorem dft_orbit_observation_halt:
  dft_orbit_observation w C D c d /\
  (FUNPOW (dft_occ_oracle_next w C) j c).dft_occ_core =
    DftOpen (DftDone (Halt s)) [] n ==>
  ?k m. (FUNPOW (dft_occ_oracle_next w D) k d).dft_occ_core =
    DftOpen (DftDone (Halt s)) [] m
Proof
  rewrite_tac[dft_orbit_observation_def] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  gvs[dft_terminal_observation_def] >> metis_tac[]
QED

Theorem dft_orbit_observation_memory:
  dft_orbit_observation w C D c d /\
  dft_open_observe g i t
    (FUNPOW (dft_occ_oracle_next w D) k d).dft_occ_core /\
  inst_mem_ranges i t <> [] ==>
  ?j f h s.
    dft_open_observe f h s
      (FUNPOW (dft_occ_oracle_next w C) j c).dft_occ_core /\
    t.vs_memory = s.vs_memory /\ inst_mem_ranges i t = inst_mem_ranges h s
Proof
  simp[dft_orbit_observation_def] >> metis_tac[]
QED

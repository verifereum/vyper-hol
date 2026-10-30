(* Determinism of an existing execution stopped at its first compiler cut. *)
Theory abiEncoderPrefixSafety
Ancestors
  abiEncoderObserver venomExecSemantics venomState

Theorem abi_observer_step_functional:
  abi_observer_step ctx fn cut s t /\ abi_observer_step ctx fn cut s u ==>
  t = u
Proof
  rw[abi_observer_step_def] >> gvs[]
QED

Theorem local_prefix_endpoint_unique:
  !ctx fn cut s t. local_prefix ctx fn cut s t ==>
    !u. local_prefix ctx fn cut s u ==> t = u
Proof
  ho_match_mp_tac local_prefix_ind >> rpt strip_tac
  >- (qpat_x_assum `local_prefix _ _ _ _ _` mp_tac >>
      simp[Once local_prefix_cases, abi_observer_step_def]) >>
  qpat_x_assum `local_prefix ctx fn cut s u` mp_tac >>
  simp[Once local_prefix_cases] >> strip_tac
  >- gvs[abi_observer_step_def] >>
  metis_tac[abi_observer_step_functional]
QED

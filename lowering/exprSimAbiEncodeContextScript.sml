(* Only finite non-INVOKE prefixes are independent of the call context. *)
Theory exprSimAbiEncodeContext
Ancestors
  abiEncoderObserver abiDecoderLoop venomExecSemantics venomExecProofs

Theorem abi_encode_observer_step_context:
  abi_observer_step ctx fn cut s t ==>
  abi_observer_step ctx' fn cut s t
Proof
  rw[abi_observer_step_def] >>
  gvs[step_inst_non_invoke] >> metis_tac[]
QED

Theorem abi_encode_local_prefix_context:
  local_prefix ctx fn cut s t ==>
  !ctx'. local_prefix ctx' fn cut s t
Proof
  Induct_on `local_prefix` >> rpt strip_tac
  >- (irule (cj 1 local_prefix_rules) >> simp[]) >>
  rename1 `abi_observer_step ctx fn cut s middle` >>
  irule (cj 2 local_prefix_rules) >>
  qexists_tac `middle` >> simp[] >>
  irule abi_encode_observer_step_context >> goal_assum (drule_at Any)
QED

Theorem abi_encode_local_prefix_context_sim:
  local_prefix ctx fn cut s t ==> abi_decode_sim ctx' fn s t
Proof
  metis_tac[abi_encode_local_prefix_context, local_prefix_sim]
QED

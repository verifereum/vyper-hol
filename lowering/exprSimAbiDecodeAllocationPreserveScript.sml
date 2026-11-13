Theory exprSimAbiDecodeAllocationPreserve
Ancestors
  abiEncoderObserver venomMemProofs venomExecProps venomExecProofs
  venomExecSemantics venomState venomInst finite_map

(* Existing entries are never overwritten, even when an ALLOCA site is reused. *)
Theorem abi_decode_step_preserves_allocation:
  step_inst_base inst s = OK t /\
  FLOOKUP s.vs_allocas site = SOME entry ==>
  FLOOKUP t.vs_allocas site = SOME entry
Proof
  Cases_on `inst.inst_opcode = ALLOCA` >> strip_tac
  >- (qpat_x_assum `step_inst_base inst s = OK t` mp_tac >>
      asm_simp_tac (srw_ss()) [Once step_inst_base_def, AllCaseEqs()] >>
      simp[exec_alloca_def, AllCaseEqs(), update_var_def, FLOOKUP_UPDATE] >>
      rpt strip_tac >> gvs[] >>
      Cases_on `site = inst.inst_id` >> gvs[FLOOKUP_UPDATE]) >>
  drule step_inst_base_OK_not_INVOKE >> strip_tac >>
  `t.vs_allocas = s.vs_allocas` by
    metis_tac[step_inst_base_preserves_alloca_fields] >> simp[]
QED

Theorem abi_decode_observer_preserves_allocation:
  abi_observer_step ctx fn cut s t /\
  FLOOKUP s.vs_allocas site = SOME entry ==>
  FLOOKUP t.vs_allocas site = SOME entry
Proof
  rw[abi_observer_step_def] >>
  gvs[step_inst_non_invoke] >>
  drule_all abi_decode_step_preserves_allocation >> strip_tac >>
  gvs[] >>
  drule eval_phis_preserves_alloca_fields >> simp[]
QED

Theorem abi_decode_local_prefix_preserves_allocation:
  !ctx fn cut s t. local_prefix ctx fn cut s t ==>
  !site entry. FLOOKUP s.vs_allocas site = SOME entry ==>
    FLOOKUP t.vs_allocas site = SOME entry
Proof
  ho_match_mp_tac local_prefix_ind >> rpt strip_tac >>
  metis_tac[abi_decode_observer_preserves_allocation]
QED

Theorem abi_decode_stop_view_allocation:
  FLOOKUP (stop_view s).vs_allocas site = FLOOKUP s.vs_allocas site
Proof
  simp[stop_view_def, halt_state_def]
QED

Theorem abi_decode_local_prefix_stop_allocation:
  local_prefix ctx fn cut s t /\
  FLOOKUP s.vs_allocas site = SOME entry ==>
  FLOOKUP (stop_view t).vs_allocas site = SOME entry
Proof
  simp[abi_decode_stop_view_allocation] >>
  metis_tac[abi_decode_local_prefix_preserves_allocation]
QED

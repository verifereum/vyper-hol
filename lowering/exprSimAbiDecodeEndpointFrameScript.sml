Theory exprSimAbiDecodeEndpointFrame
Ancestors
  venomMemProofs venomExecProofs finite_map
  venomExecSemantics venomState abiEncoderObserver abiDecoderVarExtend
  abiEncoderVarTransport exprSimAbiGasBridge

(* A fixed entry map is exempt: only allocations absent there need a floor. *)
Definition abi_decode_allocation_floor_def:
  abi_decode_allocation_floor lo old s <=>
    lo <= s.vs_alloca_next /\
    !aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
      FLOOKUP old aid = SOME (b,sz) \/ lo <= b
End

Theorem abi_decode_allocation_floor_refl:
  abi_decode_allocation_floor s.vs_alloca_next s.vs_allocas s
Proof
  simp[abi_decode_allocation_floor_def]
QED

Theorem abi_decode_allocation_floor_alloca:
  abi_decode_allocation_floor lo old s /\ exec_alloca inst s n = OK t ==>
  abi_decode_allocation_floor lo old t
Proof
  simp[exec_alloca_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[abi_decode_allocation_floor_def, update_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> Cases_on `inst.inst_id = aid` >> gvs[]
QED

Theorem abi_decode_allocation_floor_step:
  inst.inst_opcode <> INVOKE /\ step_inst 0 ctx inst s = OK t /\
  abi_decode_allocation_floor lo old s ==>
  abi_decode_allocation_floor lo old t
Proof
  strip_tac >> gvs[step_inst_non_invoke] >>
  Cases_on `inst.inst_opcode = ALLOCA`
  >- (gvs[step_inst_base_def, exec_read1_def, AllCaseEqs()] >>
      metis_tac[abi_decode_allocation_floor_alloca]) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by
    metis_tac[step_inst_base_preserves_alloca_fields] >>
  gvs[abi_decode_allocation_floor_def]
QED

Theorem abi_decode_allocation_floor_observer_step:
  abi_observer_step ctx fn cut s t /\ abi_decode_allocation_floor lo old s ==>
  abi_decode_allocation_floor lo old t
Proof
  rw[abi_observer_step_def] >>
  drule_all abi_decode_allocation_floor_step >> strip_tac >>
  gvs[abi_decode_allocation_floor_def]
  >- (drule eval_phis_preserves_alloca_fields >> strip_tac >> gvs[])
QED

Theorem abi_decode_allocation_floor_prefix:
  !ctx fn cut s t. local_prefix ctx fn cut s t ==>
    !lo old. abi_decode_allocation_floor lo old s ==>
      abi_decode_allocation_floor lo old t
Proof
  ho_match_mp_tac local_prefix_ind >> rpt strip_tac >>
  metis_tac[abi_decode_allocation_floor_observer_step]
QED

Theorem abi_decode_prefix_new_allocations:
  local_prefix ctx fn cut s t ==>
  !aid b sz. FLOOKUP t.vs_allocas aid = SOME (b,sz) /\
    FLOOKUP s.vs_allocas aid = NONE ==> s.vs_alloca_next <= b
Proof
  strip_tac >> drule abi_decode_allocation_floor_prefix >>
  disch_then (qspecl_then [`s.vs_alloca_next`, `s.vs_allocas`] mp_tac) >>
  simp[abi_decode_allocation_floor_refl, abi_decode_allocation_floor_def] >>
  metis_tac[optionTheory.NOT_NONE_SOME]
QED

Theorem abi_decode_allocation_floor_stop_view:
  stop_view u = stop_view t ==>
  (abi_decode_allocation_floor lo old u <=> abi_decode_allocation_floor lo old t)
Proof
  strip_tac >> drule stop_view_fields >>
  simp[abi_decode_allocation_floor_def]
QED

Theorem abi_decode_allocation_floor_extend:
  abi_decoder_vars_extend extras u t ==>
  (abi_decode_allocation_floor lo old u <=> abi_decode_allocation_floor lo old t)
Proof
  strip_tac >> drule abi_decoder_vars_extend_observations >>
  simp[abi_decode_allocation_floor_def]
QED

Theorem abi_decode_allocation_floor_updates[simp]:
  abi_decode_allocation_floor lo old
    (t with <|vs_returndata := rd; vs_prev_bb := prev|>) <=>
  abi_decode_allocation_floor lo old t
Proof
  simp[abi_decode_allocation_floor_def]
QED

Theorem abi_decode_observer_continuation_floor:
  cs_extends sa sb /\ fn_has_code sa sb fn /\ frag_gas_free sa sb /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  (!fuel r. run_from fuel ctx (frag_observer sa sb fn id) t = r /\
    (!e. r <> Error e) ==>
    ?fuel'. run_from fuel' ctx (frag_observer sa sb fn id) s = r) ==>
  abi_decode_allocation_floor s.vs_alloca_next s.vs_allocas t
Proof
  strip_tac >>
  `run_from 0 ctx (frag_observer sa sb fn id) t = Halt (stop_view t)` by
    (irule run_from_stop_view >>
     simp[frag_observer_cut_lookup, frag_observer_cut_instruction] >>
     qexists_tac `id` >> simp[]) >>
  `?fuel. run_from fuel ctx (frag_observer sa sb fn id) s = Halt (stop_view t)` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `?u. local_prefix ctx (frag_observer sa sb fn id) (frag_observer_cut sb) s u /\
       stop_view u = stop_view t` by
    (irule frag_observer_halt_cut_prefix >> simp[] >>
     conj_tac >- (qexists_tac `fuel` >> simp[]) >>
     simp[frag_observer_cut_def, stop_view_def, halt_state_def] >>
     metis_tac[frag_observer_start_region]) >>
  drule abi_decode_allocation_floor_prefix >>
  disch_then (qspecl_then [`s.vs_alloca_next`, `s.vs_allocas`] mp_tac) >>
  simp[abi_decode_allocation_floor_refl] >>
  drule abi_decode_allocation_floor_stop_view >> simp[]
QED

Theorem abi_decode_endpoint_allocation_transport:
  stop_view u = stop_view t /\ abi_decoder_vars_extend extras u u' /\
  abi_decode_allocation_floor lo old t /\
  FLOOKUP t.vs_allocas aid = SOME (d,n) ==>
  abi_decode_allocation_floor lo old u' /\
  FLOOKUP u'.vs_allocas aid = SOME (d,n)
Proof
  strip_tac >> drule stop_view_fields >> strip_tac >>
  drule abi_decoder_vars_extend_observations >> strip_tac >>
  gvs[abi_decode_allocation_floor_def]
QED

Theorem abi_decode_endpoint_allocation_updates:
  abi_decode_allocation_floor lo old t /\
  FLOOKUP t.vs_allocas aid = SOME (d,n) ==>
  abi_decode_allocation_floor lo old
    (t with <|vs_returndata := rd; vs_prev_bb := prev|>) /\
  FLOOKUP (t with <|vs_returndata := rd; vs_prev_bb := prev|>).vs_allocas aid = SOME (d,n)
Proof
  simp[]
QED

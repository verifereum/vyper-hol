Theory bodyIntCallObserverFrame
Ancestors
  abiEncoderObserver bodyIntCallStorageFrame venomExecSemantics venomState list

Theorem eval_phis_storage_frame:
  !is s t. eval_phis s is = OK t ==>
    contract_storage t = contract_storage s /\
    contract_transient t = contract_transient s
Proof
  Induct_on `is` >> simp[eval_phis_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >>
  first_x_assum drule >>
  simp[update_var_def, contract_storage_def, contract_transient_def]
QED

Theorem abi_observer_step_storage_frame:
  abi_observer_step ctx fn cut s t /\
  (s.vs_current_bb,s.vs_inst_idx) IN R /\
  (!lbl idx bb inst. (lbl,idx) IN R /\ (lbl,idx) <> cut /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    get_instruction bb idx = SOME inst ==> readonly_opcode inst.inst_opcode) ==>
  contract_storage t = contract_storage s /\
  contract_transient t = contract_transient s
Proof
  rw[abi_observer_step_def] >>
  `readonly_opcode inst.inst_opcode` by metis_tac[] >>
  gvs[step_inst_non_invoke] >>
  drule_all step_readonly_storage >> strip_tac >>
  gvs[contract_storage_def, contract_transient_def] >>
  drule eval_phis_storage_frame >>
  simp[contract_storage_def, contract_transient_def]
QED

Theorem local_prefix_storage_frame:
  local_prefix ctx fn cut s t ==>
  !R. (s.vs_current_bb,s.vs_inst_idx) IN R /\
    observer_region_closed ctx fn cut R /\
    (!lbl idx bb inst. (lbl,idx) IN R /\ (lbl,idx) <> cut /\
      lookup_block lbl fn.fn_blocks = SOME bb /\
      get_instruction bb idx = SOME inst ==> readonly_opcode inst.inst_opcode) ==>
    contract_storage t = contract_storage s /\
    contract_transient t = contract_transient s
Proof
  Induct_on `local_prefix` >> rpt strip_tac >> simp[] >>
  rename1 `abi_observer_step ctx fn cut s middle` >>
  `(middle.vs_current_bb,middle.vs_inst_idx) IN R` by
    metis_tac[observer_region_closed_def] >>
  `contract_storage middle = contract_storage s /\
   contract_transient middle = contract_transient s` by
    (irule abi_observer_step_storage_frame >> metis_tac[]) >>
  qpat_x_assum `!R. _` (qspec_then `R` mp_tac) >> simp[] >> metis_tac[]
QED


Theorem abi_decode_sim_stop_prefix_frame:
  abi_decode_sim ctx fn s v /\
  observer_region_safe fn cut R /\ observer_region_closed ctx fn cut R /\
  (s.vs_current_bb,s.vs_inst_idx) IN R /\ ~s.vs_halted /\
  lookup_block v.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb v.vs_inst_idx = SOME (mk_inst id STOP [] []) /\
  (!lbl idx block inst. (lbl,idx) IN R /\ (lbl,idx) <> cut /\
    lookup_block lbl fn.fn_blocks = SOME block /\
    get_instruction block idx = SOME inst ==> readonly_opcode inst.inst_opcode) ==>
  ?u. local_prefix ctx fn cut s u /\ stop_view u = stop_view v /\
    contract_storage u = contract_storage s /\
    contract_transient u = contract_transient s
Proof
  strip_tac >> drule_all abi_decode_sim_stop_run >> strip_tac >>
  drule_all observer_region_run_prefix >> strip_tac >>
  qexists `u` >> simp[] >> irule local_prefix_storage_frame >> metis_tac[]
QED

Theorem abi_decode_sim_stop_storage_frame:
  abi_decode_sim ctx fn s v /\
  observer_region_safe fn cut R /\ observer_region_closed ctx fn cut R /\
  (s.vs_current_bb,s.vs_inst_idx) IN R /\ ~s.vs_halted /\
  lookup_block v.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb v.vs_inst_idx = SOME (mk_inst id STOP [] []) /\
  (!lbl idx block inst. (lbl,idx) IN R /\ (lbl,idx) <> cut /\
    lookup_block lbl fn.fn_blocks = SOME block /\
    get_instruction block idx = SOME inst ==> readonly_opcode inst.inst_opcode) ==>
  contract_storage v = contract_storage s /\
  contract_transient v = contract_transient s
Proof
  strip_tac >> drule_all abi_decode_sim_stop_prefix_frame >> strip_tac >>
  qpat_x_assum `stop_view u = stop_view v` mp_tac >>
  simp[stop_view_def, halt_state_def, venom_state_component_equality] >>
  rpt strip_tac >> gvs[contract_storage_def, contract_transient_def]
QED


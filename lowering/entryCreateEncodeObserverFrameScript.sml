(* Rebase the registered scratch sites and allocation charge at the same
   encoder endpoint. The observed byte and ghost witnesses do not change. *)
Theory entryCreateEncodeObserverFrame
Ancestors
  abiEncoderWindowPhase abiEncoderWindowContract abiEncoderRegisteredEffect
  exprSimAbiEncodeExecFrame exprSimAbiEncodeChargeTransfer exprSimAbiEncodeResources
  venomInstIdsProps pred_set list

Theorem create_encode_window_frame_transfer:
  fn_inst_ids_distinct f /\ fn_inst_ids_distinct obs /\
  (!i. MEM i (fn_insts obs) /\ i.inst_opcode = ALLOCA ==> MEM i (fn_insts f)) /\
  alloca_room ctx f s /\ abi_encoder_extend_sim ctx f s t /\
  window_phase oc obs a b (window_alloca_sites obs ids) outs s t /\
  abi_encode_exec_frame obs s t ==>
  window_phase ctx f a b (window_alloca_sites f ids) outs s t /\
  abi_encode_exec_frame f s t /\
  window_alloca_sites obs ids SUBSET window_alloca_sites f ids
Proof
  strip_tac >>
  `window_alloca_sites obs ids SUBSET window_alloca_sites f ids` by
    (simp[window_alloca_sites_def, SUBSET_DEF] >> metis_tac[]) >>
  drule window_phase_effect >> strip_tac >>
  `!i. MEM i (fn_insts f) /\ i.inst_opcode = ALLOCA /\
       ~MEM i (fn_insts obs) ==>
       FLOOKUP t.vs_allocas i.inst_id = FLOOKUP s.vs_allocas i.inst_id` by
    (rpt strip_tac >>
     `i.inst_id NOTIN window_alloca_sites obs ids` by
       (simp[window_alloca_sites_def] >> rpt strip_tac >>
        metis_tac[venomInstIdsPropsTheory.fn_inst_ids_distinct_inj]) >>
     fs[abi_encoder_registered_effect_def]) >>
  `t.vs_alloca_next + pending_alloca_size obs t <=
   s.vs_alloca_next + pending_alloca_size obs s` by fs[abi_encode_exec_frame_def] >>
  drule_all abi_encode_charge_difference_lift >> strip_tac >>
  `alloca_room ctx f t` by metis_tac[abi_encode_room_charge] >>
  `abi_encoder_registered_effect (window_alloca_sites f ids) outs s t` by
    (irule abi_encoder_registered_effect_enlarge >>
     qexistsl_tac [`window_alloca_sites obs ids`, `outs`] >> simp[]) >>
  fs[window_phase_def, abi_encode_exec_frame_def]
QED

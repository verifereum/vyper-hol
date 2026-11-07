(* Conditional source-valued positional registration, at chosen endpoints.
   Body-state initial agreement, fmp_room and literal-size history are not
   consequences asserted by this theory. *)
Theory entrySourceRegistrationFold
Ancestors
  entrySingletonProducer entryRegistrationFoldBoundary calldataRegistrationExec
  calldataSourceMemberFold calldataMemberResourceFrame abiDecoderReentry
  abiDecoderFrame compileEnv venomState venomExecSemantics words list arithmetic finite_map

(* The singleton's freshly allocated parameter survives its own decoder.
   This is not scratch ownership: cap may differ from 32. *)
Theorem entry_registration_new_owned_endpoint[local]:
  id < first.cs_next_id /\ first.cs_next_id <= last.cs_next_id /\
  first.cs_next_var <= last.cs_next_var /\
  FLOOKUP ready.vs_allocas id = SOME (p,cap) /\
  eval_operand dst ready = SOME (n2w p) /\
  abi_decoder_operand_live first.cs_next_var dst /\
  calldata_member_success ctx fn site limit_st first last p cap tv v ready out scratch ==>
  FLOOKUP out.vs_allocas id = SOME (p,cap) /\
  eval_operand dst out = SOME (n2w p) /\
  abi_decoder_operand_live last.cs_next_var dst /\
  val_wf tv v /\ val_in_memory tv v p out.vs_memory
Proof
  strip_tac >> drule calldata_member_success_observations >> strip_tac >>
  drule calldata_member_resource_observations >> strip_tac >>
  simp[] >> metis_tac[abi_decoder_operand_live_mono]
QED

(* Lift the chosen-old-local boundary positionally. The left list contains
   original type/value pairs; equal decoder descriptors never merge slots. *)
Theorem entry_registration_old_prefix_endpoint[local]:
  st.cs_next_id < first.cs_next_id /\ st.cs_next_id < last.cs_next_id /\
  st.cs_next_var <= first.cs_next_var /\ st.cs_next_var <= last.cs_next_var /\
  ready.vs_memory = initial.vs_memory /\
  (!id entry. FLOOKUP initial.vs_allocas id = SOME entry ==>
    FLOOKUP ready.vs_allocas id = SOME entry) /\
  (!op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op ready = eval_operand op initial) /\
  FLOOKUP ready.vs_allocas st.cs_next_id = SOME (q,n) /\
  calldata_member_resource_frame ctx fn site limit_st first.cs_next_id last.cs_next_id
    first.cs_next_var q n ready out scratch /\
  LIST_REL (\(tv,v) (dst,p,id).
    id < st.cs_next_id /\ abi_decoder_operand_live st.cs_next_var dst /\
    FLOOKUP initial.vs_allocas id = SOME (p,type_memory_size tv) /\
    eval_operand dst initial = SOME (n2w p) /\
    val_wf tv v /\ val_in_memory tv v p initial.vs_memory) values outputs ==>
  LIST_REL (\(tv,v) (dst,p,id).
    id < last.cs_next_id /\ abi_decoder_operand_live last.cs_next_var dst /\
    FLOOKUP out.vs_allocas id = SOME (p,type_memory_size tv) /\
    eval_operand dst out = SOME (n2w p) /\
    val_wf tv v /\ val_in_memory tv v p out.vs_memory) values outputs
Proof
  strip_tac >> irule LIST_REL_mono >>
  goal_assum $ drule_at Any >>
  simp_tac (srw_ss()) [pairTheory.FORALL_PROD] >>
  rpt gen_tac >> strip_tac >>
  drule_all entry_registration_preserves_owned_local >> strip_tac >>
  simp[] >> metis_tac[abi_decoder_operand_live_mono, LESS_TRANS]
QED

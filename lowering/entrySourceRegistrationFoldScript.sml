(* Conditional source-valued positional registration, at chosen endpoints.
   Body-state initial agreement, fmp_room and literal-size history are not
   consequences asserted by this theory. *)
Theory entrySourceRegistrationFold
Ancestors
  entrySingletonProducer entryRegistrationFoldBoundary calldataRegistrationExec
  calldataSourceMemberFold calldataMemberResourceFrame abiDecoderReentry
  abiDecoderFrame calldataRegistration moduleLowering exprLoweringProps
  compileEnv venomState venomExecSemantics words list arithmetic finite_map

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

(* Source/descriptor facts depend on the stable type-layout fields, not on
   the PtrVar bindings introduced while processing earlier parameters. *)
Theorem entry_registration_source_metadata_transport[local]:
  compile_register_positional_args ce done off st = (ce',middle) /\
  LIST_REL (\(name,prim,dyn,sz,info) (ty,tv,v,at,av).
    abi_decoder_coherent ce env sf ty tv /\
    info = type_to_abi_dec_info sf ce ty /\
    sz = abi_embedded_static_size ce.ce_struct_fields ty /\
    sz = abi_member_head_size at /\
    type_memory_bytes ce ty = type_memory_size tv /\
    (prim ==> ?c. info = DecPrimWord c) /\
    (dyn /\ ~prim <=> is_dynamic at) /\
    value_has_type tv v /\ vyper_to_abi env ty v = SOME av /\
    at = vyper_to_abi_type env ty /\ type_memory_size tv < dimword (:256)) specs values ==>
  LIST_REL (\(name,prim,dyn,sz,info) (ty,tv,v,at,av).
    abi_decoder_coherent ce' env sf ty tv /\
    info = type_to_abi_dec_info sf ce' ty /\
    sz = abi_embedded_static_size ce'.ce_struct_fields ty /\
    sz = abi_member_head_size at /\
    type_memory_bytes ce' ty = type_memory_size tv /\
    (prim ==> ?c. info = DecPrimWord c) /\
    (dyn /\ ~prim <=> is_dynamic at) /\
    value_has_type tv v /\ vyper_to_abi env ty v = SOME av /\
    at = vyper_to_abi_type env ty /\ type_memory_size tv < dimword (:256)) specs values
Proof
  strip_tac >> drule registration_env_fields >> strip_tac >>
  irule LIST_REL_mono >> goal_assum $ drule_at Any >>
  simp_tac (srw_ss()) [pairTheory.FORALL_PROD] >>
  rpt gen_tac >> strip_tac >>
  rename1 `abi_decoder_coherent ce env sf ty tv` >>
  drule registration_coherent_env_cong >>
  disch_then (qspec_then `ce'` mp_tac) >> simp[] >> strip_tac >>
  `type_memory_bytes ce' ty = type_memory_bytes ce ty` by
    metis_tac[type_memory_bytes_struct_fields] >>
  simp[registration_dec_info_env_cong]
QED

(* Binding preservation is independent of runtime memory preservation. *)
Theorem entry_registration_prefix_bindings[local]:
  !names outputs ce done off st ce' final.
    compile_register_positional_args ce done off st = (ce',final) /\
    EVERY (\(name,tv). ~MEM name (MAP (\(n,prim,dyn,sz,info). n) done)) names /\
    LIST_REL (\(name,tv) (dst,p,id).
      FLOOKUP ce.ce_vars name = SOME (PtrVar dst (type_memory_size tv))) names outputs ==>
    LIST_REL (\(name,tv) (dst,p,id).
      FLOOKUP ce'.ce_vars name = SOME (PtrVar dst (type_memory_size tv))) names outputs
Proof
  Induct >- simp[] >>
  gen_tac >> Cases_on `outputs` >> simp[] >>
  PairCases_on `h` >> PairCases_on `h'` >>
  rpt gen_tac >> strip_tac >> fs[] >>
  `FLOOKUP ce'.ce_vars h0 = FLOOKUP ce.ce_vars h0` by
    (drule registration_unmentioned_binding >>
     disch_then (qspec_then `h0` mp_tac) >> simp[]) >>
  simp[] >> first_x_assum drule >> simp[]
QED

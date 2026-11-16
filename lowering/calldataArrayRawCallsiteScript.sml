(* Raw array iteration: finite address setup and conditional child framing. *)
Theory calldataArrayRawCallsite
Ancestors
  calldataDynStep decoderArraySetupPtr calldataSourceCorrespondence
  calldataChildFrame calldataDynOwned entryDecoderSetupEndpoint
  entryDecoderStateFrame entryDecoderHistoryFrame abiDecoderCoherence
  abiDecoderDynamicLoopSetup abiDecoderLoopSetup abiDecoderContract
  abiDecoderReentry abiDecoderArraySetupInputs abiDecoderIndexedAddress
  loweringStateRelDefs compileEnv emitHelper emitHelperProps
  fragGasOriginPtr fragExecPtr ptrDiscipline bodyPtrDefs venomMemDefs
  valueEncodingProps valueEncodingDefs valueEncoding abiDecoderFrame
  venomState venomExecSemantics words arithmetic list finite_map pred_set
  instIdxIndep exprLoweringProps

Theorem calldata_array_raw_child_return_frame:
  abi_decode_footprint_frame
    ((dst+32+j*stride,stride)::scratch) s t /\ alloca_inv t /\
  (!id. id < lo \/ hi <= id ==>
    FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
  (counter_id < lo \/ hi <= counter_id) /\
  (output_id < lo \/ hi <= output_id) /\ counter_id <> output_id /\
  FLOOKUP s.vs_allocas counter_id = SOME (counter,32) /\
  FLOOKUP s.vs_allocas output_id = SOME (base_addr,cap) /\
  base_addr <= dst /\ dst+32+j*stride+stride <= base_addr+cap /\
  (!q len. MEM (q,len) scratch ==>
    ?id. lo <= id /\ id < hi /\ FLOOKUP t.vs_allocas id = SOME (q,len)) /\
  LENGTH xs = j /\ EVERY (val_wf tv) xs /\ stride = type_memory_size tv /\
  (!k. k < j ==> val_in_memory tv (EL k xs)
    (dst+32+k*stride) s.vs_memory)
  ==>
  FLOOKUP t.vs_allocas counter_id = SOME (counter,32) /\
  mload counter t = mload counter s /\ t.vs_call_ctx = s.vs_call_ctx /\
  mem_bytes_at dst (32+j*stride) t.vs_memory =
    mem_bytes_at dst (32+j*stride) s.vs_memory /\
  (!k. k < j ==> val_in_memory tv (EL k xs)
    (dst+32+k*stride) t.vs_memory)
Proof
  strip_tac >>
  `FLOOKUP t.vs_allocas counter_id = SOME (counter,32) /\
   FLOOKUP t.vs_allocas output_id = SOME (base_addr,cap)` by metis_tac[] >>
  `counter+32 <= dst+32+j*stride \/
   dst+32+j*stride+stride <= counter` by
    (qpat_x_assum `alloca_inv t` mp_tac >>
     simp_tac bool_ss [alloca_inv_def, allocas_non_overlapping_def] >>
     strip_tac >>
     first_x_assum (qspecl_then
       [`counter_id`,`output_id`,`counter`,`32`,`base_addr`,`cap`] mp_tac) >>
     impl_tac >- simp[] >> decide_tac) >>
  `mload counter t = mload counter s` by
    (irule (cj 2 calldata_child_preserves_counter) >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >>
  `mem_bytes_at dst (32+j*stride) t.vs_memory =
     mem_bytes_at dst (32+j*stride) s.vs_memory` by
    (irule calldata_child_preserves_contained_prefix >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     qexistsl_tac [`base_addr`,`cap`,`output_id`] >> simp[] >>
     conj_tac >- first_assum ACCEPT_TAC >> fs[]) >>
  drule_all calldata_prefix_window_transport >> strip_tac >>
  gvs[abi_decode_footprint_frame_def]
QED

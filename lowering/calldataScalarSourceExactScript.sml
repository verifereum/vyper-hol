(* Exact source observation for the existing arbitrary-word clamp runner. *)
Theory calldataScalarSourceExact
Ancestors
  calldataSourceWord calldataWordLive valueEncodingTyping
  abiDecoderCoherence exprLowering vyperCalldata valueEncodingDefs
  entryDecodeProps abiDecoderReentry venomExecSemantics venomState

Theorem calldata_scalar_source_exact:
  abi_decoder_coherent ce env sf ty tv /\ is_word_type ty /\
  type_to_abi_dec_info sf ce ty = DecPrimWord cl ==>
  ((cd_word_value tv w = NONE <=> ~abi_clamp_ok cl w) /\
   (!x. cd_word_value tv w = SOME x ==>
     value_has_type tv x /\ val_wf tv x /\ typed_val_to_w256 tv x = w))
Proof
  strip_tac >> conj_tac
  >- (drule_all calldata_coherent_word_rejects >> simp[]) >>
  drule_all calldata_coherent_word_value >>
  metis_tac[value_has_type_val_wf]
QED

Theorem calldata_scalar_clamp_outcome:
  abi_decoder_coherent ce env sf ty tv /\ is_word_type ty /\
  type_to_abi_dec_info sf ce ty = DecPrimWord cl /\
  compile_abi_clamp_basetype op cl sa = ((),sb) /\
  eval_operand op s = SOME w /\ abi_decoder_operand_live sa.cs_next_var op ==>
  ?t. (run_inst_seq (emitted_insts sa sb) s =
       if cd_word_value tv w = NONE then Abort Revert_abort t else OK t) /\
    (!v. abi_decoder_operand_live sa.cs_next_var v ==>
      eval_operand v t = eval_operand v s) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> drule_all calldata_clamp_repeat >>
  drule_all calldata_scalar_source_exact >>
  metis_tac[]
QED

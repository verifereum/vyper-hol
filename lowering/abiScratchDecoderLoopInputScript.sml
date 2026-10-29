(* Actual initialized input and its registered index establish loop data. *)
Theory abiScratchDecoderLoopInput
Ancestors
  abiScratchDecoderLoopContext abiScratchDecoderContract abiDecoderProtectedScratch
  abiDecoderCoherence abiDecoderTypedContract abiDecoderAllocation abiDecoderContract
  abiDecodeRanges compileEnv valueEncoding vyperABI vyperValue contractABI
  venomState words list arithmetic

Theorem abi_scratch_decoder_loop_input:
  abi_scratch_decoder_input ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    bs (ArrayV (DynArrayV vs)) st src dst opc hi sb d first last b cap initial /\
  abi_decoder_budget first last b cap initial /\ first <= site /\ site < last /\
  FLOOKUP initial.vs_allocas site = SOME (slot,32) /\
  eval_operand ip initial = SOME (n2w slot) /\ abi_decoder_operand_live st.cs_next_var ip /\
  (is_dynamic (vyper_to_abi_type env ty) ==>
    !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) ==>
  abi_scratch_decoder_loop_data ce env sf ty tv maxn bs vs opc hi ip src dst
    sb d slot first last b cap st.cs_next_var initial
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `site IN abi_decoder_ids first last` by simp[abi_decoder_ids_def] >>
  drule_all abi_decoder_budget_site_bounds >> strip_tac >>
  `b + cap < dimword (:256)` by fs[abi_decoder_budget_def] >>
  `slot < dimword (:256)` by decide_tac >>
  qhdtm_x_assum `abi_scratch_decoder_input`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_decoder_input_def]) >>
  RULE_ASSUM_TAC (SIMP_RULE bool_ss [Once vyper_to_abi_type_def]) >>
  asm_simp_tac bool_ss [abi_scratch_decoder_loop_data_def]
QED

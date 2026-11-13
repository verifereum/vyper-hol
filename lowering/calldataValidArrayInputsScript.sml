(* Actual calldata observations for source-valid dynamic arrays. *)
Theory calldataValidArrayInputs
Ancestors
  abiDecoderValidArray abiDecoderValidArraySetupInputs abiDecoderValidContract
  abiDecoderCoherence abiDecoderTypedContract abiDecoderContract abiDecodeRanges
  compileEnv valueEncoding valueEncodingTyping vyperTyping vyperABI contractABI
  venomState words list arithmetic

Theorem calldata_valid_array_inputs:
  abi_decoder_valid_pre ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    bs (ArrayV (DynArrayV vs)) st src dst CALLDATALOAD (Lit 0w) (Lit 0w) 0 sb d b cap initial ==>
  eval_operand src initial = SOME (n2w sb) /\
  abi_decode_load CALLDATALOAD (n2w sb : bytes32) initial = n2w (LENGTH vs) /\
  LENGTH vs <= maxn /\ LENGTH vs < dimword (:256) /\
  EVERY (val_wf tv) vs /\ type_memory_size tv = type_memory_bytes ce ty
Proof
  strip_tac >> drule abi_decoder_valid_array_pre_observations >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_valid_dynarray_values >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_valid_array_init_inputs >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `LENGTH vs < dimword (:256)` by metis_tac[LESS_EQ_LESS_TRANS] >>
  `abi_decode_load CALLDATALOAD (n2w sb : bytes32) initial = n2w (LENGTH vs)` by fs[] >>
  asm_rewrite_tac[] >>
  qpat_x_assum `all_have_type tv vs` mp_tac >>
  simp_tac bool_ss [all_have_type_EVERY, EVERY_MEM] >>
  metis_tac[cj 1 value_has_type_val_wf]
QED

Theorem calldata_valid_array_loaded_count:
  abi_decoder_valid_pre ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    bs (ArrayV (DynArrayV vs)) st src dst CALLDATALOAD (Lit 0w) (Lit 0w) 0 sb d b cap initial /\
  eval_operand src initial = SOME srcword ==>
  abi_decode_load CALLDATALOAD srcword initial = n2w (LENGTH vs)
Proof
  strip_tac >> drule calldata_valid_array_inputs >> strip_tac >> gvs[]
QED

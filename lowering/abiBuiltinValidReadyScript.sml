(* Actual builtin setup establishes the full source-valid recursive input. *)
Theory abiBuiltinValidReady
Ancestors
  abiBuiltinValidInput abiBuiltinPrefixReady abiBuiltinSourceInput abiBuiltinDecodeSetup
  abiBuiltinSetupExecute abiBuiltinAllocationState abiDecoderValidContract
  abiDecoderCoherence abiDecoderTypedContract abiDecoderReentry abiDecoderContract
  abiDecoderAllocation abiDecoderArrayInitExec compileEnv valueEncoding vyperABI contractABI
  venomState words list arithmetic

Theorem abi_builtin_valid_pre_ready:
  abi_builtin_decode_setup data min_size max_size (type_memory_bytes ce ty) st = (ops,ready) /\
  abi_builtin_valid_pre ce env sf ty tv bs v st first last data min_size max_size p d b cap initial /\
  abi_builtin_allocation_frame st.cs_next_var (abi_builtin_decode_output_site st min_size max_size)
    (type_memory_bytes ce ty) initial prepared /\
  eval_operand (FST ops) prepared = SOME (n2w d) /\
  eval_operand (FST (SND ops)) prepared = SOME (n2w (p + 32)) /\
  eval_operand (SND (SND ops)) prepared = SOME (n2w (p + 32 + LENGTH bs)) ==>
  first <= ready.cs_next_id /\ abi_decoder_budget first last b cap prepared /\
  abi_decoder_valid_pre ce env sf ty tv bs v ready (FST (SND ops)) (FST ops)
    MLOAD (SND (SND ops)) (p + 32) d b cap prepared
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_builtin_decode_setup_live >> strip_tac >>
  drule abi_builtin_decode_setup_shape >> strip_tac >>
  drule_all abi_builtin_valid_source >> strip_tac >>
  qpat_assum `abi_builtin_valid_pre ce env sf ty tv bs v st first last data min_size max_size p d b cap initial`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_valid_pre_def]) >>
  qpat_assum `abi_builtin_decode_resources _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_decode_resources_def]) >>
  `first <= ready.cs_next_id` by asm_simp_tac bool_ss [] >>
  `abi_decoder_budget first last b cap prepared` by
    (mp_tac (Q.INST [`next` |-> `st.cs_next_var`,
       `site` |-> `abi_builtin_decode_output_site st min_size max_size`,
       `outsz` |-> `type_memory_bytes ce ty`, `s` |-> `initial:venom_state`,
       `t` |-> `prepared:venom_state`] abi_builtin_allocation_frame_budget) >>
     asm_simp_tac bool_ss []) >>
  mp_tac (Q.INST [`prefix_len` |-> `LENGTH (bs:word8 list)`, `cnt` |-> `LENGTH (bs:word8 list)`,
    `outsz` |-> `type_memory_bytes ce ty`, `src` |-> `FST (SND (ops:operand # operand # operand))`,
    `dst` |-> `FST (ops:operand # operand # operand)`,
    `hi` |-> `SND (SND (ops:operand # operand # operand))`] abi_builtin_prefix_ranges) >>
  impl_tac >- asm_simp_tac bool_ss [LESS_EQ_REFL] >> strip_tac >>
  qpat_assum `abi_builtin_allocation_frame _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_allocation_frame_def]) >>
  asm_simp_tac (srw_ss()) [abi_decoder_valid_pre_def, abi_decode_source_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_BUILTIN_VALID_READY_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI actual-source builtin readiness not kernel closed: " ^ n)
  end) (DB.thms "abiBuiltinValidReady");

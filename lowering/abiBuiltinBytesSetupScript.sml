(* Shared actual builtin setup from source Bytes and ordinary allocation resources.
   This prefix does not depend on the decoded type or canonicality. *)
Theory abiBuiltinBytesSetup
Ancestors
  abiBuiltinValidBytes abiBuiltinDecodeSetup abiBuiltinSetupReach abiBuiltinAllocation
  abiDecoderBytes abiDecoderContract abiDecoderReentry valueEncoding valueEncodingProps
  emitHelperProps compileEnv venomState words arithmetic

Theorem abi_builtin_bytes_setup_resources:
  abi_builtin_decode_setup data min_size max_size (abi_decode_bytes_copy_size n) st =
    (ops,ready) /\
  abi_builtin_valid_bytes_resources n bs st data min_size max_size p d s ==>
  ?prepared. run_inst_seq (emitted_insts st ready) s = OK prepared /\
    eval_operand (FST ops) prepared = SOME (n2w d) /\
    eval_operand (FST (SND ops)) prepared = SOME (n2w (p + 32)) /\
    eval_operand (SND (SND ops)) prepared = SOME (n2w (p + 32 + LENGTH bs)) /\
    mem_bytes_at (p + 32) (LENGTH bs) (abi_decode_source MLOAD prepared) = bs /\
    fresh_vars_wrt ready prepared /\
    abi_builtin_allocation_frame st.cs_next_var
      (abi_builtin_decode_output_site st min_size max_size) (abi_decode_bytes_copy_size n)
      s prepared /\ inst_extends st ready
Proof
  strip_tac >> qpat_x_assum `abi_builtin_valid_bytes_resources _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_valid_bytes_resources_def]) >>
  drule abi_builtin_decode_setup_shape >> strip_tac >>
  `st.cs_next_var <= ready.cs_next_var /\ p < dimword (:256) /\
   abi_decode_bytes_copy_size n < dimword (:256)` by decide_tac >>
  `fresh_vars_wrt ready s` by
    (irule fresh_vars_wrt_mono >> qexists_tac `st` >> simp[GREATER_EQ]) >>
  `mload (w2n (n2w p:bytes32)) s = n2w (LENGTH bs)` by
    fs[val_in_memory_def, mem_word_at_eq_mload, w2n_n2w] >>
  drule_all (SIMP_RULE bool_ss [LESS_EQ_REFL]
    (Q.INST [`limit_st` |-> `ready`] abi_builtin_decode_setup_execute)) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st ready) s = OK prepared` >>
  qexists_tac `prepared` >> asm_simp_tac bool_ss [word_add_n2w] >>
  fs[abi_builtin_allocation_frame_def, abi_decode_source_def, val_in_memory_def]
QED

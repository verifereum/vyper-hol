(* Incoming resources for the complete builtin Bytes/String decoder.
   The source is its actual Bytes value, without a canonical encoding premise. *)
Theory abiBuiltinValidBytesPre
Ancestors
  abiDecoderValidBytes abiDecoderBytes abiBuiltinDecodeSetup abiBuiltinSetupExecute
  abiBuiltinAllocationState abiDecoderReentry abiDecoderContract
  valueEncoding valueEncodingProps emitHelperProps compileEnv venomState
  contractABI finite_map words list arithmetic

Definition abi_builtin_valid_bytes_resources_def:
  abi_builtin_valid_bytes_resources n bs st data min_size max_size p d s <=>
    val_in_memory (BaseTV (BytesT (Dynamic (LENGTH bs)))) (vyperValue$BytesV bs) p s.vs_memory /\
    eval_operand data s = SOME (n2w p) /\ abi_decoder_operand_live st.cs_next_var data /\
    min_size <= LENGTH bs /\ LENGTH bs <= max_size /\ max_size < dimword (:256) /\
    n < dimword (:256) /\ p + 32 + LENGTH bs < dimword (:256) /\
    d + abi_decode_bytes_copy_size n < dimword (:256) /\ fresh_vars_wrt st s /\
    ((FLOOKUP s.vs_allocas (abi_builtin_decode_output_site st min_size max_size) = NONE /\
        d = s.vs_alloca_next) \/
      FLOOKUP s.vs_allocas (abi_builtin_decode_output_site st min_size max_size) =
        SOME (d,abi_decode_bytes_copy_size n))
End

Definition abi_builtin_valid_bytes_pre_def:
  abi_builtin_valid_bytes_pre n at bs payload st data min_size max_size p d s <=>
    (at = Bytes NONE \/ at = String) /\ valid_enc at bs /\
    dec at bs = contractABI$BytesV payload /\ LENGTH payload <= n /\
    abi_builtin_valid_bytes_resources n bs st data min_size max_size p d s
End

Theorem abi_builtin_valid_bytes_ready:
  abi_builtin_decode_setup data min_size max_size (abi_decode_bytes_copy_size n) st =
    (ops,ready) /\
  abi_builtin_valid_bytes_pre n at bs payload st data min_size max_size p d s ==>
  ?prepared. run_inst_seq (emitted_insts st ready) s = OK prepared /\
    abi_decoder_valid_bytes_pre n at bs payload ready (FST (SND ops)) (FST ops)
      MLOAD (SND (SND ops)) (p + 32) d prepared /\
    abi_builtin_allocation_frame st.cs_next_var
      (abi_builtin_decode_output_site st min_size max_size) (abi_decode_bytes_copy_size n)
      s prepared /\ inst_extends st ready
Proof
  strip_tac >> qpat_x_assum `abi_builtin_valid_bytes_pre _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE
      [abi_builtin_valid_bytes_pre_def, abi_builtin_valid_bytes_resources_def]) >>
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
  qexists_tac `prepared` >> asm_simp_tac bool_ss [] >>
  qpat_assum `abi_builtin_allocation_frame _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_allocation_frame_def]) >>
  asm_simp_tac (srw_ss()) [abi_decoder_valid_bytes_pre_def, abi_decode_source_def,
    abi_decode_source_opcode_def, word_add_n2w] >> conj_tac
  >- fs[val_in_memory_def] >>
  disj2_tac >> qexists_tac `p + 32 + LENGTH bs` >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_BUILTIN_VALID_BYTES_PRE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI builtin valid bytes input not kernel closed: " ^ n)
  end) (DB.thms "abiBuiltinValidBytesPre");

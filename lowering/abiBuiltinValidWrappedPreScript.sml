(* Pure wrapped source input and actual builtin preparation for noncanonical bytes. *)
Theory abiBuiltinValidWrappedPre
Ancestors
  abiBuiltinBytesSetup abiBuiltinValidBytesPre abiValidWrappedBytesInput abiDecoderBytes
  abiBuiltinDecodeSetup abiBuiltinAllocationState abiDecoderContract
  compileEnv venomState contractABI words arithmetic

Definition abi_builtin_valid_wrapped_bytes_pre_def:
  abi_builtin_valid_wrapped_bytes_pre n at bs payload st data min_size max_size p d s <=>
    (at = Bytes NONE \/ at = String) /\ valid_enc (Tuple [at]) bs /\
    dec (Tuple [at]) bs = ListV [contractABI$BytesV payload] /\ LENGTH payload <= n /\
    abi_builtin_valid_bytes_resources n bs st data min_size max_size p d s
End

Theorem abi_builtin_valid_wrapped_bytes_ready:
  abi_builtin_decode_setup data min_size max_size (abi_decode_bytes_copy_size n) st =
    (ops,ready) /\
  abi_builtin_valid_wrapped_bytes_pre n at bs payload st data min_size max_size p d s ==>
  ?prepared. run_inst_seq (emitted_insts st ready) s = OK prepared /\
    abi_valid_wrapped_bytes_pre n at bs payload ready (FST (SND ops)) (FST ops)
      (SND (SND ops)) (p + 32) d prepared /\
    abi_builtin_allocation_frame st.cs_next_var
      (abi_builtin_decode_output_site st min_size max_size) (abi_decode_bytes_copy_size n)
      s prepared /\ inst_extends st ready
Proof
  strip_tac >> qpat_x_assum `abi_builtin_valid_wrapped_bytes_pre _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_valid_wrapped_bytes_pre_def]) >>
  drule_all abi_builtin_bytes_setup_resources >> strip_tac >>
  qpat_assum `abi_builtin_valid_bytes_resources _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_valid_bytes_resources_def]) >>
  qexists_tac `prepared` >> asm_simp_tac bool_ss [abi_valid_wrapped_bytes_pre_def] >>
  disj2_tac >> qexists_tac `p + 32 + LENGTH bs` >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_BUILTIN_VALID_WRAPPED_PRE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI builtin valid wrapped input not kernel closed: " ^ n)
  end) (DB.thms "abiBuiltinValidWrappedPre");

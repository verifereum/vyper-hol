(* The actual builtin allocation and length guards establish the singleton
   array input at the full input length, without canonicalizing its head. *)
Theory abiBuiltinWrappedArrayReady
Ancestors
  abiValidWrappedArrayInput abiValidSingletonPrefixInput abiBuiltinPrefixReady
  abiBuiltinSourceInput abiBuiltinDecodeSetup abiBuiltinSetupExecute abiBuiltinAllocationState
  abiDecoderCoherence abiDecoderTypedContract abiDecoderContract abiDecoderReentry
  abiDecoderAllocation abiDecoderArrayInitExec compileEnv valueEncoding
  vyperABI contractABI venomState words list arithmetic

Theorem abi_builtin_wrapped_array_ready:
  abi_builtin_decode_setup data min_size max_size (type_memory_bytes ce (ArrayT ty (Dynamic maxn)))
    st = (ops,ready) /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  evaluate_abi_decode env (TupleT [ArrayT ty (Dynamic maxn)]) bs = INL (ArrayV (TupleV [v])) /\
  ~is_dynamic (vyper_to_abi_type env ty) /\
  val_in_memory (BaseTV (BytesT (Dynamic input_bound))) (vyperValue$BytesV bs) p initial.vs_memory /\
  abi_builtin_decode_resources st first last min_size max_size
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) (LENGTH bs) p d b cap initial /\
  abi_builtin_allocation_frame st.cs_next_var (abi_builtin_decode_output_site st min_size max_size)
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) initial prepared /\
  eval_operand (FST ops) prepared = SOME (n2w d) /\
  eval_operand (FST (SND ops)) prepared = SOME (n2w (p + 32)) /\
  eval_operand (SND (SND ops)) prepared = SOME (n2w (p + 32 + LENGTH bs)) ==>
  first <= ready.cs_next_id /\ abi_decoder_budget first last b cap prepared /\
  abi_valid_singleton_prefix_pre ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) bs
    (dec (Array NONE (vyper_to_abi_type env ty)) (DROP (abi_head_word bs) bs)) v
    ready (FST (SND ops)) (FST ops) MLOAD (SND (SND ops)) (p + 32) d b cap prepared
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_builtin_decode_setup_live >> strip_tac >>
  drule abi_builtin_decode_setup_shape >> strip_tac >>
  `first <= ready.cs_next_id` by fs[abi_builtin_decode_resources_def] >>
  `abi_decoder_budget first last b cap prepared` by
    (mp_tac (Q.INST [`next` |-> `st.cs_next_var`,
       `site` |-> `abi_builtin_decode_output_site st min_size max_size`,
       `outsz` |-> `type_memory_bytes ce (ArrayT ty (Dynamic maxn))`,
       `s` |-> `initial:venom_state`, `t` |-> `prepared:venom_state`]
       abi_builtin_allocation_frame_budget) >> fs[abi_builtin_decode_resources_def]) >>
  `abi_decoder_ranges MLOAD (SND (SND ops)) (FST (SND ops)) (FST ops)
     (p + 32) (LENGTH bs) d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap prepared` by
    (drule_all (SIMP_RULE (srw_ss()) []
      (Q.INST [`prefix_len` |-> `LENGTH (bs:word8 list)`,
        `cnt` |-> `LENGTH (bs:word8 list)`] abi_builtin_prefix_ranges)) >> simp[]) >>
  `mem_bytes_at (p + 32) (LENGTH bs) (abi_decode_source MLOAD prepared) = bs` by
    fs[val_in_memory_def, abi_builtin_allocation_frame_def, abi_decode_source_def] >>
  drule_all abi_valid_wrapped_array_prefix_pre >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_BUILTIN_WRAPPED_ARRAY_READY_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI builtin wrapped array entry not kernel closed: " ^ n)
  end) (DB.thms "abiBuiltinWrappedArrayReady");

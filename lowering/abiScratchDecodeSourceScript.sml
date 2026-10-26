(* Complete source-success builtin decoding from coherent metadata. *)
Theory abiScratchDecodeSource
Ancestors
  abiBuiltinDecodeSetup
  abiScratchDecodeRun abiScratchDecodeInput abiDecoderReadableTypes abiBuiltinSourceInput
  abiScratchDecodeEffect abiDecoderCoherence abiDecoderContract abiDecoderLoop
  abiDecoderReentry abiEncoder builtinAbi fragExec compileEnv valueEncoding vyperABI
  contractABI venomState words list

Theorem lower_abi_decode_scratch_source:
  lower_abi_decode data (type_to_abi_dec_info sf ce ty) min_size max_size
    (type_memory_bytes ce ty) start = (out,final) /\ fn_has_code start final func /\
  (start.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_coherent ce env sf ty tv /\ evaluate_abi_decode env ty bs = INL v /\
  val_in_memory (BaseTV (BytesT (Dynamic input_bound))) (vyperValue$BytesV bs) src_base initial.vs_memory /\
  eval_operand data initial = SOME (n2w src_base) /\ abi_decoder_operand_live start.cs_next_var data /\
  abi_scratch_decode_resources start first last min_size max_size (type_memory_bytes ce ty)
    (LENGTH bs) src_base d b cap initial /\
  final.cs_next_id <= last /\ final.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = start.cs_current_bb /\ initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual. eval_operand out actual = SOME (n2w d) /\ val_in_memory tv v d actual.vs_memory /\
    abi_scratch_decode_effect first last start final limit_st
      (abi_builtin_decode_output_site start min_size max_size) d (type_memory_bytes ce ty)
      b cap initial actual /\ actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_scratch_decode_pre_from_source >> strip_tac >>
  drule_all lower_abi_decode_scratch >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_DECODE_SOURCE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI physical actual-source builtin result not kernel closed: " ^ n)
  end) (DB.thms "abiScratchDecodeSource");


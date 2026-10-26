(* Complete wrapped builtin result agrees with successful source decoding. *)
Theory abiBuiltinValidWrappedSource
Ancestors
  abiValidWrappedBytesSource abiBuiltinValidWrappedBytes abiBuiltinValidWrappedPre
  abiBuiltinValidBytesPre abiDecoderBytes abiDecoderContract abiDecoderLoop abiDecoderReentry
  abiEncoder builtinAbi fragExec vyperABI vyperValue valueEncoding compileEnv
  venomState words list

Theorem abi_builtin_valid_wrapped_source_pre:
  (ty = BaseT (BytesT (Dynamic n)) \/ ty = BaseT (StringT n)) /\
  evaluate_type env ty = SOME tv /\
  evaluate_abi_decode env (TupleT [ty]) bs = INL (ArrayV (TupleV [v])) /\
  abi_builtin_valid_bytes_resources n bs st data min_size max_size p d s ==>
  ?at payload. abi_builtin_valid_wrapped_bytes_pre n at bs payload st data min_size max_size p d s /\
    (!mem. val_in_memory (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV payload) d mem /\
      val_in_memory (BaseTV (StringT n)) (StringV (MAP (CHR o w2n) payload)) d mem ==>
      val_in_memory tv v d mem)
Proof
  strip_tac >> gvs[evaluate_type_def, Excl "dec_def", Excl "valid_enc_def"] >>
  FIRST
  [drule abi_valid_wrapped_bytes_source_decode >> strip_tac >>
     qexistsl_tac [`Bytes NONE`, `payload`] >>
     gvs[abi_builtin_valid_wrapped_bytes_pre_def, Excl "dec_def", Excl "valid_enc_def"],
   drule abi_valid_wrapped_string_source_decode >> strip_tac >>
     qexistsl_tac [`String`, `payload`] >>
     gvs[abi_builtin_valid_wrapped_bytes_pre_def, Excl "dec_def", Excl "valid_enc_def"]]
QED

Theorem lower_abi_decode_valid_wrapped_bytes_source:
  (ty = BaseT (BytesT (Dynamic n)) \/ ty = BaseT (StringT n)) /\
  evaluate_type env ty = SOME tv /\
  evaluate_abi_decode env (TupleT [ty]) bs = INL (ArrayV (TupleV [v])) /\
  lower_abi_decode data (DecComplex T [(DecBytestring n,32,abi_decode_bytes_copy_size n)])
    min_size max_size (abi_decode_bytes_copy_size n) st = (out,final) /\ fn_has_code st final func /\
  abi_builtin_valid_bytes_resources n bs st data min_size max_size p d initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. eval_operand out actual = SOME (n2w d) /\ val_in_memory tv v d actual.vs_memory /\
    abi_decode_frame d (abi_decode_bytes_copy_size n) initial actual /\
    fresh_vars_wrt final actual /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w) /\
    actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_builtin_valid_wrapped_source_pre >> strip_tac >>
  drule_all lower_abi_decode_valid_wrapped_bytes >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  first_x_assum irule >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_BUILTIN_VALID_WRAPPED_SOURCE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI builtin valid wrapped source not kernel closed: " ^ n)
  end) (DB.thms "abiBuiltinValidWrappedSource");

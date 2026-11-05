(* Actual emitted code for the allocation-free calldata word decoder. *)
Theory calldataWordPtr
Ancestors calldataDecodePtr abiDecoderClampedWord abiDecoderContract
  abiEncoder compileEnv emitHelper exprLoweringProps fragExec
  venomInst list arithmetic

Theorem calldata_unclamped_word_instructions:
  compile_abi_decode_to_buf (Var p) src CALLDATALOAD (Lit 0w)
    (DecPrimWord NoClamp) sa = ((),sb) ==>
  emitted_insts sa sb =
    [mk_inst sa.cs_next_id CALLDATALOAD [src]
       ["%" ++ toString sa.cs_next_var];
     mk_inst (sa.cs_next_id + 1) MSTORE
       [Var p; Var ("%" ++ toString sa.cs_next_var)] []] /\
  sb.cs_current_bb = sa.cs_current_bb /\ sb.cs_blocks = sa.cs_blocks /\
  LENGTH sb.cs_current_insts = LENGTH sa.cs_current_insts + 2
Proof
  simp[compile_abi_decode_to_buf_def, compile_abi_decode_static_def,
       compile_abi_clamp_basetype_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, emit_inst_def,
       fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def, APPEND_ASSOC, DROP_PREFIX]
QED

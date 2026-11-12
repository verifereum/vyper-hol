(* ABI suffix observations can be used under the counted gas bridge:
   unlike the execution relation itself these facts ignore return data. *)
Theory exprSimAbiEncodeInterface
Ancestors
  loweringStateRelDefs
  abiScratchBuiltinEffect abiScratchBuiltinOpenSource exprSimHash
  compileEnv abiDecoderAllocation abiScratchFootprint abiDecoderFrame
  venomState venomExecSemantics venomMemDefs

Theorem abi_encode_effect_returndata:
  abi_scratch_builtin_effect first last st final limit_st p outsz write_size b cap s
    (t with vs_returndata := rd) <=>
  abi_scratch_builtin_effect first last st final limit_st p outsz write_size b cap s t
Proof
  `!op. eval_operand op (t with vs_returndata := rd) = eval_operand op t` by
    (Cases >> simp[eval_operand_def, lookup_var_def]) >>
  simp[abi_decoder_missing_def, abi_scratch_builtin_effect_def, fresh_vars_wrt_def,
       abi_decoder_budget_def, abi_scratch_evolution_def,
       abi_decode_footprint_frame_def, eval_operand_def, lookup_var_def]
QED

Theorem abi_encode_output_returndata:
  (eval_operand out (t with vs_returndata := rd) = SOME (n2w p) /\
   mload p (t with vs_returndata := rd) = n2w (LENGTH bytes) /\
   mem_bytes_at (p+32) (LENGTH bytes) (t with vs_returndata := rd).vs_memory = bytes) <=>
  (eval_operand out t = SOME (n2w p) /\
   mload p t = n2w (LENGTH bytes) /\
   mem_bytes_at (p+32) (LENGTH bytes) t.vs_memory = bytes)
Proof
  Cases_on `out` >> simp[eval_operand_def, lookup_var_def, mload_def]
QED

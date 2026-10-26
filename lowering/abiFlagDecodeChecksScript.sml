(* Pinned Vyper's needs_clamp omits validation for a full-width flag. *)
Theory abiFlagDecodeChecks
Ancestors
  exprLowering abiEncoder compileEnv emitHelper venomInst list

Theorem abi_flag_256_decode_instructions:
  cenv.ce_flag_n_members (nsid_to_string nsid) = 256 ==>
  MAP (\i. i.inst_opcode)
    (SND (compile_abi_decode_to_buf (Lit 256w) (Lit 4w) CALLDATALOAD
      (Lit 0w) (type_to_abi_dec_info sfields cenv (FlagT nsid))
      <| cs_next_var := 0; cs_next_label := 0; cs_next_id := 0;
         cs_current_bb := "entry"; cs_current_insts := [];
         cs_blocks := []; cs_data_sections := [] |>)).cs_current_insts =
    [CALLDATALOAD; MSTORE]
Proof
  simp[type_to_abi_dec_info_def] >> EVAL_TAC
QED

Theorem abi_flag_255_decode_instructions:
  cenv.ce_flag_n_members (nsid_to_string nsid) = 255 ==>
  MAP (\i. i.inst_opcode)
    (SND (compile_abi_decode_to_buf (Lit 256w) (Lit 4w) CALLDATALOAD
      (Lit 0w) (type_to_abi_dec_info sfields cenv (FlagT nsid))
      <| cs_next_var := 0; cs_next_label := 0; cs_next_id := 0;
         cs_current_bb := "entry"; cs_current_insts := [];
         cs_blocks := []; cs_data_sections := [] |>)).cs_current_insts =
    [CALLDATALOAD; SHR; ISZERO; ASSERT; MSTORE]
Proof
  simp[type_to_abi_dec_info_def] >> EVAL_TAC
QED

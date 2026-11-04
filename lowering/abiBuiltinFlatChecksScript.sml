(* The legacy flat ABI contracts omit blocks emitted by recursive encoders and
   decoders. These concrete compilations satisfy their operand/freshness
   premises, but their final-block suffixes read registers from earlier blocks.
   Complete execution contracts use fn_has_code and abi_decode_sim instead. *)
Theory abiBuiltinFlatChecks
Ancestors
  builtinAbi abiEncoder exprLoweringProps compileEnv venomExecSemantics
  venomState venomInst words list finite_map

Definition abi_builtin_flat_probe_start_def:
  abi_builtin_flat_probe_start =
    <| cs_next_var := 0; cs_next_label := 0; cs_next_id := 0;
       cs_current_bb := "entry"; cs_current_insts := [];
       cs_blocks := []; cs_data_sections := [] |>
End

Definition abi_builtin_flat_encode_probe_def:
  abi_builtin_flat_encode_probe =
    lower_abi_encode T NONE (Lit 0w)
      (AbiDynArray (AbiBytestring 10) 32 64 T) 128
      abi_builtin_flat_probe_start
End

Definition abi_builtin_flat_decode_probe_def:
  abi_builtin_flat_decode_probe =
    lower_abi_decode (Lit 0w)
      (DecComplex T
        [(DecDynArray (DecPrimWord BoolClamp) 32 32 F 1,32,64);
         (DecPrimWord NoClamp,32,32)])
      64 128 96 abi_builtin_flat_probe_start
End

Theorem abi_builtin_flat_probe_premises:
  fresh_vars_wrt abi_builtin_flat_probe_start (init_venom_state "entry") /\
  eval_operand (Lit 0w) (init_venom_state "entry") = SOME 0w
Proof
  simp[fresh_vars_wrt_def, init_venom_state_def, eval_operand_def]
QED

Theorem abi_builtin_flat_encode_error:
  let final = SND abi_builtin_flat_encode_probe in
    final.cs_blocks <> [] /\
    run_inst_seq (emitted_insts abi_builtin_flat_probe_start final)
      (init_venom_state "entry") = Error "undefined operand"
Proof
  EVAL_TAC
QED

Theorem abi_builtin_flat_decode_error:
  let final = SND abi_builtin_flat_decode_probe in
    final.cs_blocks <> [] /\
    run_inst_seq (emitted_insts abi_builtin_flat_probe_start final)
      (init_venom_state "entry") = Error "undefined operand"
Proof
  EVAL_TAC
QED

Theorem abi_builtin_flat_encode_contract_false:
  ~(!(ensure:bool) method src ei maxlen s st out final w.
    lower_abi_encode ensure method src ei maxlen st = (out,final) /\
    eval_operand src s = SOME w /\ fresh_vars_wrt st s ==>
    ?actual. run_inst_seq (emitted_insts st final) s = OK actual)
Proof
  strip_tac >>
  mp_tac (SIMP_RULE bool_ss [LET_THM] abi_builtin_flat_encode_error) >> strip_tac >>
  qpat_x_assum `!ensure method src ei maxlen s st out final w. _`
    (mp_tac o Q.SPECL
    [`T`, `NONE`, `Lit 0w`, `AbiDynArray (AbiBytestring 10) 32 64 T`,
     `128`, `init_venom_state "entry"`, `abi_builtin_flat_probe_start`,
     `FST abi_builtin_flat_encode_probe`, `SND abi_builtin_flat_encode_probe`,
     `0w`]) >>
  gvs[GSYM abi_builtin_flat_encode_probe_def, abi_builtin_flat_probe_premises]
QED

Theorem abi_builtin_flat_decode_contract_false:
  ~(!data di min_size max_size out_size s st out final w.
    lower_abi_decode data di min_size max_size out_size st = (out,final) /\
    eval_operand data s = SOME w /\ fresh_vars_wrt st s ==>
    ?actual. run_inst_seq (emitted_insts st final) s = OK actual \/
      run_inst_seq (emitted_insts st final) s = Abort Revert_abort actual)
Proof
  strip_tac >>
  mp_tac (SIMP_RULE bool_ss [LET_THM] abi_builtin_flat_decode_error) >> strip_tac >>
  qpat_x_assum `!data di min_size max_size out_size s st out final w. _`
    (mp_tac o Q.SPECL
    [`Lit 0w`, `DecComplex T
       [(DecDynArray (DecPrimWord BoolClamp) 32 32 F 1,32,64);
        (DecPrimWord NoClamp,32,32)]`, `64`, `128`, `96`,
     `init_venom_state "entry"`, `abi_builtin_flat_probe_start`,
     `FST abi_builtin_flat_decode_probe`, `SND abi_builtin_flat_decode_probe`,
     `0w`]) >>
  gvs[GSYM abi_builtin_flat_decode_probe_def, abi_builtin_flat_probe_premises]
QED

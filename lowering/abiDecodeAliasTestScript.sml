(* A reused output allocation can overlap and destroy an unread input payload. *)
Theory abiDecodeAliasTest
Ancestors
  abiBuiltinValidBytes
  compileEnv loweringStateRelDefs abiDecoderContract abiDecoderBytesTyped builtinAbi abiBuiltinDecodeSetup venomExecSemantics venomState context words finite_map
  contractABI valueEncoding valueEncodingProps vyperABI
Libs
  wordsLib

Definition alias_compile_state_def:
  alias_compile_state = <| cs_next_var := 0; cs_next_label := 0;
    cs_next_id := 0; cs_current_bb := "entry"; cs_current_insts := [];
    cs_blocks := []; cs_data_sections := [] |>
End

Definition alias_bytes_def:
  alias_bytes = REPLICATE 31 (0w:word8) ++ [1w;1w] ++ REPLICATE 31 0w
End

Definition alias_initial_def:
  alias_initial = mstore 256 64w (mstore 288 1w
    (mstore 320 (n2w (2 ** 248))
      ((init_venom_state "entry") with
        vs_allocas := FEMPTY |+ (abi_builtin_decode_output_site alias_compile_state 64 64,(288,64)))))
End

Definition alias_code_def:
  alias_code = (SND (lower_abi_decode (Lit 256w) (DecBytestring 1) 64 64 64
    alias_compile_state)).cs_current_insts
End

Theorem alias_execution_corrupts_payload:
  case run_inst_seq alias_code alias_initial of
    OK actual => mload 288 actual = 1w /\ mload 320 actual = 0w
  | _ => F
Proof
  EVAL_TAC
QED

Theorem alias_preconditions_allow_payload_overlap:
  abi_builtin_valid_bytes_pre 1 (Bytes NONE) alias_bytes [1w]
    alias_compile_state (Lit 256w) 64 64 256 288 alias_initial
Proof
  rewrite_tac[abi_builtin_valid_bytes_pre_def,
              abi_builtin_valid_bytes_resources_def] >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- simp[fresh_vars_wrt_def, alias_compile_state_def, alias_initial_def,
    mstore_def, write_memory_with_expansion_def, init_venom_state_def] >>
  EVAL_TAC
QED

Theorem alias_no_successful_value:
  ~(?actual. run_inst_seq alias_code alias_initial = OK actual /\
    val_in_memory (BaseTV (BytesT (Dynamic 1))) (vyperValue$BytesV [1w]) 288 actual.vs_memory)
Proof
  strip_tac >>
  qpat_x_assum `run_inst_seq _ _ = _` mp_tac >> EVAL_TAC >>
  disch_then (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `val_in_memory _ _ _ _` mp_tac >> EVAL_TAC
QED

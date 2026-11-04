(* Isolated concrete probe for the legacy standalone Bytes helper. *)
Theory abiBuiltinBytesAliasProbe
Ancestors
  compileEnv abiDecoderContract abiDecoderBytesTyped builtinAbi abiBuiltinDecodeSetup venomExecSemantics venomState context words finite_map
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

(* Exact conjunction from abi_builtin_valid_bytes_pre/resources, n=1,
   at=Bytes NONE, payload=[1w], p=256, d=288, min=max=64, data=Lit256. *)
Theorem alias_legacy_preconditions:
  (Bytes NONE = Bytes NONE \/ Bytes NONE = String) /\
  vyper_decode_valid_enc (Bytes NONE) alias_bytes /\
  dec (Bytes NONE) alias_bytes = contractABI$BytesV [1w] /\
  LENGTH ([1w]:word8 list) <= 1 /\
  val_in_memory (BaseTV (BytesT (Dynamic (LENGTH alias_bytes))))
    (vyperValue$BytesV alias_bytes) 256 alias_initial.vs_memory /\
  eval_operand (Lit 256w) alias_initial = SOME (n2w 256) /\
  abi_decoder_operand_live alias_compile_state.cs_next_var (Lit 256w) /\
  64 <= LENGTH alias_bytes /\ LENGTH alias_bytes <= 64 /\ 64 < dimword (:256) /\
  1 < dimword (:256) /\ 256 + 32 + LENGTH alias_bytes < dimword (:256) /\
  288 + abi_decode_bytes_copy_size 1 < dimword (:256) /\
  fresh_vars_wrt alias_compile_state alias_initial /\
  ((FLOOKUP alias_initial.vs_allocas
      (abi_builtin_decode_output_site alias_compile_state 64 64) = NONE /\
      288 = alias_initial.vs_alloca_next) \/
   FLOOKUP alias_initial.vs_allocas
      (abi_builtin_decode_output_site alias_compile_state 64 64) = SOME (288,abi_decode_bytes_copy_size 1))
Proof
  conj_tac >- simp[] >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- simp[] >>
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

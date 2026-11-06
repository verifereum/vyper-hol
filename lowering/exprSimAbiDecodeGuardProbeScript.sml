Theory exprSimAbiDecodeGuardProbe
Ancestors exprSimAbiDecodeSizeProbe vyperABI contractABI words list valueEncodingProofs

Theorem abi_decode_guard_probe_wrap:
  (n2w (abi_size_bound sf
    (abi_decode_size_probe_type (2 ** 251 - 2))) :256 word) = 0w
Proof
  `dimindex (:256) = 256` by CONV_TAC fcpLib.INDEX_CONV >>
  simp[abi_decode_size_probe_abi, wordsTheory.n2w_11, dimword_def]
QED

Theorem abi_decode_guard_probe_dynamic:
  !k. is_dynamic (vyper_to_abi_type env (abi_decode_size_probe_type k))
Proof
  Induct >> simp[abi_decode_size_probe_type_def]
QED

Theorem abi_decode_guard_probe_vdynamic:
  !k. vyper_is_dynamic env (abi_decode_size_probe_type k)
Proof
  Induct >> simp[abi_decode_size_probe_type_def, vyper_is_dynamic_def]
QED

Theorem abi_decode_guard_probe_bound:
  !k. vyper_abi_size_bound env (abi_decode_size_probe_type k) = 64 + 32 * k
Proof
  Induct
  >- EVAL_TAC >>
  simp[abi_decode_size_probe_type_def, vyper_abi_size_bound_def,
    abi_decode_guard_probe_vdynamic]
QED

Theorem abi_decode_guard_probe_source_zero:
  !k. ?v. evaluate_abi_decode env (abi_decode_size_probe_type k)
    (REPLICATE 32 (0w:byte)) = INL v
Proof
  Induct
  >- (EVAL_TAC >> simp[]) >>
  fs[evaluate_abi_decode_def, vyper_valid_enc_def, AllCaseEqs()] >>
  simp[abi_decode_size_probe_type_def, evaluate_abi_decode_def,
       vyper_valid_enc_def, vyper_strict_enc_def, vyper_abi_size_bound_def,
       abi_decode_guard_probe_bound, abi_decode_guard_probe_vdynamic,
       vyper_decode_valid_enc_def, abi_decode_guard_probe_dynamic] >>
  simp[TAKE_LENGTH_TOO_LONG, word_of_bytes_replicate_zero,
       vyper_strict_enc_def] >>
  fs[vyper_strict_enc_def] >>
  fs[decode_abi_value_def, AllCaseEqs()] >>
  simp[decode_abi_value_def, Once dec_def] >>
  simp[abi_decode_guard_probe_dynamic, TAKE_LENGTH_TOO_LONG,
       word_of_bytes_replicate_zero]
QED

Theorem abi_decode_guard_probe_minimum:
  abi_static_size sf (abi_decode_size_probe_type (2 ** 251 - 2)) = 32
Proof
  `2 ** 251 - 2 = SUC (2 ** 251 - 3)` by EVAL_TAC >>
  asm_rewrite_tac[abi_decode_size_probe_type_def] >>
  simp[Once compileEnvTheory.abi_static_size_def, abi_decode_size_probe_dynamic]
QED

(* The word-sized interval has an empty intersection. This is a local guard
   diagnostic, not a realization of expr_vv_case's preconditions. *)
Theorem abi_decode_guard_probe_interval:
  !len:num. ~(32 <= len /\
    len <= w2n (n2w (abi_size_bound sf
      (abi_decode_size_probe_type (2 ** 251 - 2))) :256 word))
Proof
  rewrite_tac[abi_decode_guard_probe_wrap] >> simp[]
QED

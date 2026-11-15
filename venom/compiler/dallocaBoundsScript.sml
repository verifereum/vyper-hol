(* Numeric bounds for dynamic allocations. Source-size and execution-count
 * producers must establish these antecedents at the emitted sites.
 *)
Theory dallocaBounds
Ancestors
  fmpAlignment venomExecSemantics venomMemProps vfmConstants words arithmetic

Theorem ceil32_le_multiple:
  n <= 32 * k ==> ceil32 n <= 32 * k
Proof
  strip_tac >>
  `(n + 31) DIV 32 <= k` by
    (simp[DIV_LE_X] >> decide_tac) >>
  simp[ceil32_div_mul] >> decide_tac
QED

Theorem dalloca_calldata_size_bound:
  LENGTH (data:byte list) < 2 ** 64 ==> ceil32 (LENGTH data) <= 2 ** 64
Proof
  strip_tac >>
  mp_tac (Q.INST [`n` |-> `LENGTH (data:byte list)`, `k` |-> `2 ** 59`]
    ceil32_le_multiple) >>
  fs[] >> decide_tac
QED

Theorem dalloca_completed_create_size_bound:
  exec_create inst s value off sz salt = OK t ==>
  ceil32 (w2n sz) <= 65536
Proof
  simp[exec_create_def, AllCaseEqs()] >> rpt strip_tac >>
  `w2n sz <= 32 * 2048` by fs[max_code_size_def] >>
  drule ceil32_le_multiple >> simp[]
QED

Theorem dalloca_trailing_blueprint_size_bound:
  w2n (code_size:bytes32) < 2 ** 255 /\
  w2n (args_len:bytes32) < 2 ** 64 ==>
  ceil32 (w2n (code_size + args_len)) <= 2 ** 255 + 2 ** 64
Proof
  strip_tac >>
  `w2n code_size + w2n args_len < dimword (:256)` by
    (fs[dimword_def, dimindex_256] >> decide_tac) >>
  `w2n (code_size + args_len) <= 32 * (2 ** 250 + 2 ** 59)` by
    (fs[w2n_add_2] >> decide_tac) >>
  drule ceil32_le_multiple >> simp[]
QED

Theorem dalloca_split_budget:
  !F K:num. F < 2 ** 254 /\ K <= 2 ** 64 ==>
  F + K * 2 ** 64 + (2 ** 255 + 2 ** 64) < dimword (:256)
Proof
  simp[dimword_def, dimindex_256] >> decide_tac
QED

Theorem dalloca_chosen_raw_fmp_bound:
  !limit initial_fmp static_budget:num.
  limit <= dimword (:256) /\ initial_fmp < limit /\ static_budget < limit ==>
  w2n (n2w (MAX initial_fmp static_budget):bytes32) = MAX initial_fmp static_budget /\
  w2n (n2w (MAX initial_fmp static_budget):bytes32) < limit /\
  initial_fmp <= w2n (n2w (MAX initial_fmp static_budget):bytes32) /\
  static_budget <= w2n (n2w (MAX initial_fmp static_budget):bytes32)
Proof
  rpt gen_tac >> strip_tac >>
  `MAX initial_fmp static_budget < limit` by simp[MAX_DEF] >>
  `MAX initial_fmp static_budget < dimword (:256)` by decide_tac >>
  simp[w2n_n2w, MAX_DEF]
QED

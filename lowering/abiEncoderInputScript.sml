Theory abiEncoderInput
Ancestors
  abiDecodeRanges compileEnv valueEncoding contractABI words list rich_list arithmetic
  abiEncoderLeaves abiEncoderSourceChecks abiDecoderContract abiEncoder emitHelper venomState
  venomExecSemantics

(* ===== Encoder Input ===== *)

(* Pure source representation for all encoder descriptors.
   Static slices cover every byte, including omitted sparse-array defaults.
   Bytestring padding is deliberately not an input requirement. *)

Definition abi_encoder_member_span_def:
  abi_encoder_member_span (infos:(abi_enc_info # num # num # bool) list) =
    SUM (MAP (\(_,_,n,_). n) infos)
End

Definition abi_encoder_tuple_type_def:
  abi_encoder_tuple_type at ats <=>
    at = Tuple ats \/ ?n ct. at = Array (SOME n) ct /\ ats = REPLICATE n ct
End

Inductive abi_encoder_input:
[word:]
  (!at av sb cap mem.
    has_type at av /\ ~is_dynamic at /\ static_length at = 32 /\ 32 <= cap /\
    mem_bytes_at sb 32 mem = enc at av ==>
    abi_encoder_input AbiPrimWord at av sb cap mem)
[copy:]
  (!sz at av sb cap mem.
    has_type at av /\ ~is_dynamic at /\ static_length at = sz /\ sz <= cap /\
    mem_bytes_at sb sz mem = enc at av ==>
    abi_encoder_input (AbiCopy sz) at av sb cap mem)
[bytes:]
  (!maxlen at bs sb cap mem.
    (at = Bytes NONE \/ at = String) /\ has_type at (BytesV bs) /\
    LENGTH bs <= maxlen /\ 32 + LENGTH bs <= cap /\
    mem_word_at sb mem = n2w (LENGTH bs) /\
    mem_bytes_at (sb + 32) (LENGTH bs) mem = bs ==>
    abi_encoder_input (AbiBytestring maxlen) at (BytesV bs) sb cap mem)
[array:]
  (!ei abi_sz mem_sz dyn ct avs sb cap mem.
    has_type (Array NONE ct) (ListV avs) /\
    abi_sz = abi_member_head_size ct /\ dyn = is_dynamic ct /\
    32 + LENGTH avs * mem_sz <= cap /\
    mem_word_at sb mem = n2w (LENGTH avs) /\
    (!i. i < LENGTH avs ==>
      abi_encoder_input ei ct (EL i avs) (sb + 32 + i * mem_sz) mem_sz mem) ==>
    abi_encoder_input (AbiDynArray ei abi_sz mem_sz dyn) (Array NONE ct) (ListV avs) sb cap mem)
[complex:]
  (!infos at ats avs sb cap mem.
    abi_encoder_tuple_type at ats /\ has_type at (ListV avs) /\
    LENGTH infos = LENGTH ats /\ LENGTH ats = LENGTH avs /\
    abi_encoder_member_span infos <= cap /\
    (!i ei abi_sz mem_sz dyn. i < LENGTH infos /\ EL i infos = (ei,abi_sz,mem_sz,dyn) ==>
      abi_sz = abi_member_head_size (EL i ats) /\ dyn = is_dynamic (EL i ats) /\
      abi_encoder_input ei (EL i ats) (EL i avs)
        (sb + abi_encoder_member_span (TAKE i infos)) mem_sz mem) ==>
    abi_encoder_input (AbiComplex infos) at (ListV avs) sb cap mem)
End

Theorem abi_encoder_input_typed:
  abi_encoder_input ei at av sb cap mem ==> has_type at av
Proof
  simp_tac bool_ss [Once abi_encoder_input_cases] >> rpt strip_tac >> gvs[]
QED

Theorem abi_encoder_input_word_iff:
  abi_encoder_input AbiPrimWord at av sb cap mem <=>
  has_type at av /\ ~is_dynamic at /\ static_length at = 32 /\ 32 <= cap /\
  mem_bytes_at sb 32 mem = enc at av
Proof
  simp[Once abi_encoder_input_cases]
QED

Theorem abi_encoder_input_copy_iff:
  abi_encoder_input (AbiCopy sz) at av sb cap mem <=>
  has_type at av /\ ~is_dynamic at /\ static_length at = sz /\ sz <= cap /\
  mem_bytes_at sb sz mem = enc at av
Proof
  simp[Once abi_encoder_input_cases] >> eq_tac >> rpt strip_tac >> gvs[]
QED

Theorem abi_encoder_input_bytes_iff:
  abi_encoder_input (AbiBytestring maxlen) at av sb cap mem <=>
  ?bs. av = BytesV bs /\ (at = Bytes NONE \/ at = String) /\ has_type at (BytesV bs) /\
    LENGTH bs <= maxlen /\ 32 + LENGTH bs <= cap /\
    mem_word_at sb mem = n2w (LENGTH bs) /\ mem_bytes_at (sb + 32) (LENGTH bs) mem = bs
Proof
  simp[Once abi_encoder_input_cases] >> metis_tac[]
QED

Theorem abi_encoder_input_capacity:
  abi_encoder_input ei at av sb cap mem /\ cap <= larger ==>
  abi_encoder_input ei at av sb larger mem
Proof
  strip_tac >>
  qpat_x_assum `abi_encoder_input _ _ _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [abi_encoder_input_cases]) >>
  gvs[] >> ONCE_REWRITE_TAC [abi_encoder_input_cases] >> asm_simp_tac (srw_ss()) [LET_THM] >>
  gvs[AC ADD_COMM ADD_ASSOC, MULT_COMM] >>
  FIRST [decide_tac,
    rename1 `abi_encoder_tuple_type at ats` >> qexists_tac `ats` >> gvs[] >> decide_tac]
QED

(* ===== Layout ===== *)

(* Bounds for source slots inside recursive encoder input windows. *)

Theorem abi_encoder_member_span_append:
  abi_encoder_member_span (xs ++ ys) = abi_encoder_member_span xs + abi_encoder_member_span ys
Proof
  simp[abi_encoder_member_span_def, MAP_APPEND, SUM_APPEND]
QED

Theorem abi_encoder_prefix_sum_bound:
  !f xs i. i < LENGTH xs ==>
    SUM (MAP f (TAKE i xs)) + f (EL i xs) <= SUM (MAP f xs)
Proof
  Induct_on `xs` >- simp[] >> rpt gen_tac >> Cases_on `i` >> simp[] >>
  strip_tac >> first_x_assum drule >> disch_then (qspec_then `f` mp_tac) >> decide_tac
QED

Theorem abi_encoder_member_slot_bound:
  i < LENGTH infos /\ EL i infos = (ei,abi_sz,mem_sz,dyn) ==>
  abi_encoder_member_span (TAKE i infos) + mem_sz <= abi_encoder_member_span infos
Proof
  strip_tac >>
  mp_tac (Q.ISPEC `(\(_,_,mem_sz,_). mem_sz):abi_enc_info # num # num # bool -> num`
    abi_encoder_prefix_sum_bound) >>
  disch_then (qspecl_then [`infos`, `i`] mp_tac) >>
  asm_simp_tac (srw_ss()) [abi_encoder_member_span_def]
QED

Theorem abi_encoder_array_slot_bound:
  (i:num) < ncount /\ 32 + ncount * mem_sz <= cap ==>
  32 + i * mem_sz + mem_sz <= cap
Proof
  strip_tac >> `(i+1)*mem_sz <= ncount*mem_sz` by
    simp[LE_MULT_RCANCEL] >> pop_assum mp_tac >>
  PURE_REWRITE_TAC [RIGHT_ADD_DISTRIB, MULT_CLAUSES] >> strip_tac >> decide_tac
QED

Theorem abi_encoder_array_input_iff:
  abi_encoder_input (AbiDynArray ei abi_sz mem_sz dyn) at av sb cap mem <=>
  ?ct avs. at = Array NONE ct /\ av = ListV avs /\
    has_type (Array NONE ct) (ListV avs) /\
    abi_sz = abi_member_head_size ct /\ dyn = is_dynamic ct /\
    32 + LENGTH avs * mem_sz <= cap /\ mem_word_at sb mem = n2w (LENGTH avs) /\
    (!i. i < LENGTH avs ==>
      abi_encoder_input ei ct (EL i avs) (sb+32+i*mem_sz) mem_sz mem)
Proof
  simp[Once abi_encoder_input_cases] >> metis_tac[]
QED

Theorem abi_encoder_complex_input_iff:
  abi_encoder_input (AbiComplex infos) at av sb cap mem <=>
  ?ats avs. av = ListV avs /\ abi_encoder_tuple_type at ats /\ has_type at (ListV avs) /\
    LENGTH infos = LENGTH ats /\ LENGTH ats = LENGTH avs /\
    abi_encoder_member_span infos <= cap /\
    (!i ei abi_sz mem_sz dyn. i < LENGTH infos /\ EL i infos = (ei,abi_sz,mem_sz,dyn) ==>
      abi_sz = abi_member_head_size (EL i ats) /\ dyn = is_dynamic (EL i ats) /\
      abi_encoder_input ei (EL i ats) (EL i avs)
        (sb+abi_encoder_member_span (TAKE i infos)) mem_sz mem)
Proof
  simp[Once abi_encoder_input_cases] >> metis_tac[]
QED

(* ===== Leaves ===== *)

(* Static encoder leaves produce the semantic ABI encoding from complete input.
   No correctness property of an emitted fragment is an input premise. *)

Theorem abi_encoder_copy_input_sequence:
  compile_abi_encode_to_buf dst src (AbiCopy sz) st = (out,st') /\
  abi_encoder_input (AbiCopy sz) at av sb cap s.vs_memory /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w db) /\
  sb < dimword (:256) /\ db < dimword (:256) /\ sz < dimword (:256) /\
  fresh_vars_wrt st s ==>
  ?actual. run_inst_seq (emitted_insts st st') s = OK actual /\
    mem_bytes_at db (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    eval_operand out actual = SOME (n2w (LENGTH (enc at av))) /\
    abi_decode_frame db (LENGTH (enc at av)) s actual /\ fresh_vars_wrt st' actual /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op actual = SOME w)
Proof
  strip_tac >>
  qpat_assum `abi_encoder_input _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o REWRITE_RULE [abi_encoder_input_copy_iff]) >>
  `LENGTH (enc at av) = sz` by
    (drule_all (cj 1 enc_has_static_length) >> simp[]) >>
  drule_all abi_encode_copy_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st') s = OK actual` >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

Theorem abi_encoder_word_input_sequence:
  compile_abi_encode_to_buf dst src AbiPrimWord st = (out,st') /\
  abi_encoder_input AbiPrimWord at av sb cap s.vs_memory /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w db) /\
  sb < dimword (:256) /\ db < dimword (:256) /\ fresh_vars_wrt st s ==>
  ?actual. run_inst_seq (emitted_insts st st') s = OK actual /\
    mem_bytes_at db (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    eval_operand out actual = SOME (n2w (LENGTH (enc at av))) /\
    abi_decode_frame db (LENGTH (enc at av)) s actual /\ fresh_vars_wrt st' actual /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op actual = SOME w)
Proof
  strip_tac >>
  qpat_assum `abi_encoder_input _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o REWRITE_RULE [abi_encoder_input_word_iff]) >>
  `LENGTH (enc at av) = 32` by
    (drule_all (cj 1 enc_has_static_length) >> simp[]) >>
  drule_all abi_encode_word_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st') s = OK actual` >>
  qexists_tac `actual` >> asm_simp_tac (srw_ss()) []
QED

Theorem abi_encoder_input_excludes_uninitialized_sparse_defaults:
  ~abi_encoder_input (AbiCopy 32)
    (vyper_to_abi_type FEMPTY (ArrayT (BaseT (UintT 256)) (Fixed 1)))
    (ListV [NumV 0]) 0 cap abi_encoder_sparse_probe_memory
Proof
  metis_tac[abi_encoder_input_copy_iff, abi_encoder_sparse_probe_window]
QED

Theorem encoder_dynamic_input_head_size:
  abi_encoder_input (AbiDynArray ei h mem_sz T) at av sb cap mem ==>
  h = 32
Proof
  simp[abi_encoder_array_input_iff] >> rpt strip_tac >>
  gvs[abi_member_head_size_def]
QED

(*
 * Soundness and content theorems for Vyper's stricter ABI decode validation.
 *
 *   vyper_valid_enc_decode_valid_enc      the structural-validation projection
 *   vyper_valid_enc_length_lower/_upper   the size window, one bound each
 *   vyper_valid_enc_window/_rejects       relaxed validation plus that window
 *   vyper_valid_enc_head_offset_in_bounds  issue checks 1-2
 *   evaluate_abi_decode_vyper_valid_enc   the _abi_decode gate
 *   evaluate_abi_decode_returndata_vyper_valid_enc / _capped
 *                                        the returndata gate and its cap
 *   vyper_to_abi_enc_le_size_bound        our own encodings stay in the window
 *)

Theory vyperABIValid
Ancestors
  vyperTypeABI vyperABI contractABI arithmetic list rich_list combin
  byte finite_map vyperValue vyperMisc option
Libs
  wordsLib

(* ===== Structural validation projection ===== *)

Theorem vyper_valid_enc_decode_valid_enc:
  !env t bs. vyper_valid_enc env t bs ⇒
    vyper_decode_valid_enc (vyper_to_abi_type env t) bs
Proof
  rw[vyper_valid_enc_def]
QED

(* Strict ABI encodings also satisfy Vyper's validation, which ignores
   unused dynamic Bytes/String padding. *)
Theorem valid_enc_vyper_decode_valid_enc_mutual:
  (!t bs. valid_enc t bs ==> vyper_decode_valid_enc t bs) /\
  (!n l t bs hds. valid_enc_array n l t bs hds ==>
     vyper_decode_valid_enc_array n l t bs hds) /\
  (!ts bs hds. valid_enc_tuple ts bs hds ==>
     vyper_decode_valid_enc_tuple ts bs hds)
Proof
  ho_match_mp_tac valid_enc_ind >>
  rpt strip_tac >>
  fs[Once valid_enc_def] >>
  simp[Once vyper_decode_valid_enc_def] >>
  gvs[] >> Cases_on `is_dynamic t` >> gvs[]
QED

Theorem valid_enc_vyper_decode_valid_enc:
  !t bs. valid_enc t bs ==> vyper_decode_valid_enc t bs
Proof
  metis_tac[valid_enc_vyper_decode_valid_enc_mutual]
QED

Theorem vyper_decode_valid_enc_bytes_payload:
  (!bs. vyper_decode_valid_enc (Bytes NONE) bs ==>
     32 <= LENGTH bs /\
     dest_NumV (dec_number (Uint 256) (TAKE 32 bs)) <= LENGTH (DROP 32 bs)) /\
  (!bs. vyper_decode_valid_enc String bs ==>
     32 <= LENGTH bs /\
     dest_NumV (dec_number (Uint 256) (TAKE 32 bs)) <= LENGTH (DROP 32 bs))
Proof
  simp[vyper_decode_valid_enc_def]
QED

Theorem vyper_decode_valid_enc_fixed_bytes:
  !m bs. vyper_decode_valid_enc (Bytes (SOME m)) bs =
    valid_enc (Bytes (SOME m)) bs
Proof
  simp[vyper_decode_valid_enc_def, valid_enc_def]
QED

Theorem vyper_decode_dec_has_type_mutual:
  (!t bs. vyper_decode_valid_enc t bs ==> has_type t (dec t bs)) /\
  (!n b t bs hds acc.
     vyper_decode_valid_enc_array n b t bs hds /\
     n + LENGTH acc < dimword (:256) /\ have_type t (REVERSE acc) ==>
     has_type (Array NONE t) (dec_array n b t bs hds acc) /\
     has_type (Array (SOME (n + LENGTH acc)) t) (dec_array n b t bs hds acc)) /\
  (!ts bs hds acc ats.
     vyper_decode_valid_enc_tuple ts bs hds /\
     LENGTH ts + LENGTH acc < dimword (:256) /\ has_types ats (REVERSE acc) ==>
     has_type (Tuple (ats ++ ts)) (dec_tuple ts bs hds acc))
Proof
  ho_match_mp_tac dec_ind >> rpt strip_tac >>
  fs[Once vyper_decode_valid_enc_def] >> simp[Once dec_def]
  >- (first_x_assum (qspec_then `[]` mp_tac) >> rw[])
  >- (qmatch_goalsub_abbrev_tac `w2n w` >>
      qspec_then `w` mp_tac wordsTheory.w2n_lt >> rw[] >> gvs[LENGTH_TAKE_EQ])
  >- (qmatch_goalsub_abbrev_tac `w2n w` >>
      qspec_then `w` mp_tac wordsTheory.w2n_lt >> rw[] >> gvs[LENGTH_TAKE_EQ])
  >- (qpat_x_assum `has_types _ _ ==> _` mp_tac >>
      (impl_tac >- (rewrite_tac[GSYM REPLICATE, GSYM SNOC_REPLICATE, SNOC_APPEND] >>
        gvs[has_types_LIST_REL, LIST_REL_APPEND_EQ])) >>
      simp[ADD1])
  >- (qpat_x_assum `has_types _ _ ==> _` mp_tac >>
      (impl_tac >- (rewrite_tac[GSYM REPLICATE, GSYM SNOC_REPLICATE, SNOC_APPEND] >>
        gvs[has_types_LIST_REL, LIST_REL_APPEND_EQ])) >>
      simp[ADD1])
  >- (qpat_x_assum `has_types _ _ ==> _` mp_tac >>
      (impl_tac >- (rewrite_tac[GSYM REPLICATE, GSYM SNOC_REPLICATE, SNOC_APPEND] >>
        gvs[has_types_LIST_REL, LIST_REL_APPEND_EQ])) >>
      simp[ADD1])
  >- (qpat_x_assum `has_types _ _ ==> _` mp_tac >>
      (impl_tac >- (rewrite_tac[GSYM REPLICATE, GSYM SNOC_REPLICATE, SNOC_APPEND] >>
        gvs[has_types_LIST_REL, LIST_REL_APPEND_EQ])) >>
      simp[ADD1])
  >> Cases_on `is_dynamic t` >> gvs[] >>
  first_x_assum (qspec_then `ats ++ [t]` mp_tac) >>
  simp[has_types_LIST_REL, LIST_REL_APPEND_EQ] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  fs[has_types_LIST_REL]
QED

Theorem vyper_decode_dec_has_type:
  !t bs. vyper_decode_valid_enc t bs ==> has_type t (dec t bs)
Proof
  metis_tac[vyper_decode_dec_has_type_mutual]
QED

Theorem vyper_decode_valid_enc_tuple_REPLICATE:
  !n t bs hds.
    vyper_decode_valid_enc_tuple (REPLICATE n t) bs hds =
    vyper_decode_valid_enc_array n
      (if is_dynamic t then NONE else SOME (static_length t)) t bs hds
Proof
  Induct_on `n` >> simp[Once vyper_decode_valid_enc_def] >>
  rpt gen_tac >> Cases_on `is_dynamic t` >>
  simp[vyper_decode_valid_enc_def]
QED

Theorem vyper_decode_valid_enc_static_mutual:
  (!t bs. ~is_dynamic t /\ vyper_decode_valid_enc t bs ==> valid_enc t bs) /\
  (!n l t bs hds. ~is_dynamic t /\ vyper_decode_valid_enc_array n l t bs hds ==>
     valid_enc_array n l t bs hds) /\
  (!ts bs hds. EVERY (\t. ~is_dynamic t) ts /\
     vyper_decode_valid_enc_tuple ts bs hds ==> valid_enc_tuple ts bs hds)
Proof
  ho_match_mp_tac valid_enc_ind >> rpt strip_tac >>
  fs[Once vyper_decode_valid_enc_def] >>
  simp[Once valid_enc_def] >> gvs[] >>
  first_x_assum irule >>
  qpat_x_assum `~any_dynamic ts` mp_tac >>
  qpat_x_assum `LENGTH ts < _` kall_tac >>
  qpat_x_assum `vyper_decode_valid_enc_tuple _ _ _` kall_tac >>
  Induct_on `ts` >> simp[is_dynamic_def]
QED

Theorem vyper_decode_valid_enc_static:
  !t bs. ~is_dynamic t /\ vyper_decode_valid_enc t bs ==> valid_enc t bs
Proof
  metis_tac[vyper_decode_valid_enc_static_mutual]
QED

(* ===== Content of the size window (issue checks 4 and 5) ===== *)

(* Minimum expected ABI encoding size: the declared type's head is readable. *)
Theorem vyper_valid_enc_length_lower:
  !env t bs. vyper_valid_enc env t bs ⇒
    static_length (vyper_to_abi_type env t) ≤ LENGTH bs
Proof
  rw[vyper_valid_enc_def, vyper_strict_enc_def]
QED

(* Maximum encoding size; also the cap Vyper puts on the decode buffer. *)
Theorem vyper_valid_enc_length_upper:
  !env t bs. vyper_valid_enc env t bs ⇒ LENGTH bs ≤ vyper_abi_size_bound env t
Proof
  rw[vyper_valid_enc_def, vyper_strict_enc_def]
QED

Theorem vyper_valid_enc_window:
  !env t bs. vyper_valid_enc env t bs ⇔
    (vyper_decode_valid_enc (vyper_to_abi_type env t) bs ∧
     static_length (vyper_to_abi_type env t) ≤ LENGTH bs ∧
     LENGTH bs ≤ vyper_abi_size_bound env t)
Proof
  rw[vyper_valid_enc_def, vyper_strict_enc_def]
QED

(* What the window adds: malformed encodings, too-short buffers, and buffers
   past the declared Vyper bound are rejected. *)
Theorem vyper_valid_enc_rejects:
  !env t bs. ¬ vyper_valid_enc env t bs ⇔
    ¬ vyper_decode_valid_enc (vyper_to_abi_type env t) bs ∨
    ¬ (static_length (vyper_to_abi_type env t) ≤ LENGTH bs) ∨
    ¬ (LENGTH bs ≤ vyper_abi_size_bound env t)
Proof
  rw[vyper_valid_enc_window]
QED

(* ===== Offset pointers are within the buffer (issue checks 1-2) ===== *)

(* The three dynamic ABI types with a runtime length word need it readable. *)
Theorem vyper_decode_valid_enc_length_word_readable[local]:
  (!bs. vyper_decode_valid_enc (Bytes NONE) bs ⇒ 32 ≤ LENGTH bs) ∧
  (!bs. vyper_decode_valid_enc String bs ⇒ 32 ≤ LENGTH bs) ∧
  (!t2 bs. vyper_decode_valid_enc (Array NONE t2) bs ⇒ 32 ≤ LENGTH bs)
Proof
  rw[vyper_decode_valid_enc_def]
QED

Theorem drop_32_readable_in_bounds[local]:
  !bs n. 32 ≤ LENGTH (DROP n bs) ⇒ 32 + n ≤ LENGTH bs
Proof
  Induct_on `n` >> gvs[Once listTheory.DROP_LENGTH_TOO_LONG, LENGTH_TL]
QED

(* A dynamic member is reached at head offset j, and its own length word must
   be readable in DROP j bs.  Bounded nums then also rule out the 256-bit wrap
   that Vyper's `assert actual_ptr >= parent` guards against. *)
Theorem vyper_decode_valid_enc_tuple_offset_in_bounds[local]:
  (!t2 ts bs.
     vyper_decode_valid_enc (Tuple (Bytes NONE :: ts)) bs ⇒
     32 + abi_head_word bs ≤ LENGTH bs) ∧
  (!ts bs.
     vyper_decode_valid_enc (Tuple (String :: ts)) bs ⇒
     32 + abi_head_word bs ≤ LENGTH bs) ∧
  (!t2 ts bs.
     vyper_decode_valid_enc (Tuple (Array NONE t2 :: ts)) bs ⇒
     32 + abi_head_word bs ≤ LENGTH bs)
Proof
  rw[abi_head_word_def, vyper_decode_valid_enc_def] >> simp[] >> strip_tac
  >> drule_all vyper_decode_valid_enc_length_word_readable
  >> gvs[listTheory.DROP_LENGTH_TOO_LONG]
QED

(* The Vyper-type form: bounded dynamic members keep their head in the input. *)
Theorem vyper_valid_enc_head_offset_in_bounds:
  (!env ts bs.
     vyper_valid_enc env (TupleT (BaseT (BytesT (Dynamic n)) :: ts)) bs ⇒
     32 + abi_head_word bs ≤ LENGTH bs) ∧
  (!env ts bs.
     vyper_valid_enc env (TupleT (BaseT (StringT n) :: ts)) bs ⇒
     32 + abi_head_word bs ≤ LENGTH bs) ∧
  (!env t2 m ts bs.
     vyper_valid_enc env (TupleT (ArrayT t2 (Dynamic m) :: ts)) bs ⇒
     32 + abi_head_word bs ≤ LENGTH bs)
Proof
  PURE_REWRITE_TAC [vyper_valid_enc_def, vyper_to_abi_type_def,
                    vyper_base_to_abi_type_def]
  >> rpt strip_tac
  >- (drule (cj 1 vyper_decode_valid_enc_tuple_offset_in_bounds) >> gvs[])
  >- (drule (cj 2 vyper_decode_valid_enc_tuple_offset_in_bounds) >> gvs[])
  >> drule (cj 3 vyper_decode_valid_enc_tuple_offset_in_bounds) >> gvs[]
QED

(* ===== The two decoder paths use the gate they should ===== *)

Theorem evaluate_abi_decode_vyper_valid_enc:
  !tenv typ bs v. evaluate_abi_decode tenv typ bs = INL v ⇒
    vyper_valid_enc tenv typ bs
Proof
  rw[evaluate_abi_decode_def, decode_abi_value_def, AllCaseEqs(), LET_THM]
QED

(* Returndata gates on vyper_valid_enc_returndata, since Vyper caps that buffer
   at size_bound instead of rejecting it. *)
Theorem evaluate_abi_decode_returndata_vyper_valid_enc:
  !tenv typ bs v. evaluate_abi_decode_returndata tenv typ bs = INL v ⇒
    vyper_valid_enc_returndata tenv typ (TAKE (vyper_abi_size_bound tenv typ) bs)
Proof
  rw[evaluate_abi_decode_returndata_def, decode_abi_value_def, AllCaseEqs(),
     LET_THM]
QED

Theorem evaluate_abi_decode_returndata_capped:
  !tenv typ bs v cap. cap = vyper_abi_size_bound tenv typ ∧
    evaluate_abi_decode_returndata tenv typ bs = INL v ⇒
    vyper_valid_enc_returndata tenv typ (TAKE cap bs) ∧
    static_length (vyper_to_abi_type tenv typ) ≤ LENGTH (TAKE cap bs)
Proof
  rw[] >>
  drule_all evaluate_abi_decode_returndata_vyper_valid_enc >>
  simp[vyper_valid_enc_returndata_def]
QED

(* ===== The window never rejects our own encodings ===== *)

(* Encodings produced by the semantics stay inside Vyper's declared size
   window; structural validity is established independently. *)
Theorem vyper_to_abi_enc_le_size_bound:
  (!tenv typ v av tv.
    vyper_to_abi tenv typ v = SOME av ∧
    evaluate_type tenv typ = SOME tv ∧
    value_has_type tv v ==>
    LENGTH (enc (vyper_to_abi_type tenv typ) av) <=
    vyper_abi_size_bound tenv typ) ∧
  (!tenv ts vs avs tvs.
    vyper_to_abi_list tenv ts vs = SOME avs ∧
    LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) ts tvs ∧
    values_have_types tvs vs ==>
    LENGTH (enc (Tuple (vyper_to_abi_types tenv ts)) (ListV avs)) <=
    vyper_abi_size_bound tenv (TupleT ts))
Proof
  rpt conj_tac >> gvs[vyper_abi_size_bound_def] >> rpt strip_tac
  >- (drule_all (cj 1 vyper_to_abi_enc_length_bound) >> gvs[])
  >> drule_all (cj 2 vyper_to_abi_enc_length_bound) >> gvs[]
QED

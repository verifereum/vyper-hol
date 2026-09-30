(*
 * Soundness and content theorems for Vyper's stricter ABI decode validation.
 *
 * TOP-LEVEL
 *   vyper_valid_enc_valid_enc             vyper_valid_enc => valid_enc
 *   vyper_valid_enc_length_lower/_upper   the size window, one bound each
 *   vyper_valid_enc_window/_rejects       the window, and its excess over valid_enc
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

(* ===== Soundness: the vyper_valid_enc => valid_enc bridge ===== *)

(* A projection: the content is in vyper_valid_enc_rejects below. *)
Theorem vyper_valid_enc_valid_enc:
  !env t bs. vyper_valid_enc env t bs ⇒ valid_enc (vyper_to_abi_type env t) bs
Proof
  rw[vyper_valid_enc_def]
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
    (valid_enc (vyper_to_abi_type env t) bs ∧
     static_length (vyper_to_abi_type env t) ≤ LENGTH bs ∧
     LENGTH bs ≤ vyper_abi_size_bound env t)
Proof
  rw[vyper_valid_enc_def, vyper_strict_enc_def]
QED

(* What the window adds: too short, or past the bound, is rejected. *)
Theorem vyper_valid_enc_rejects:
  !env t bs. ¬ vyper_valid_enc env t bs ⇔
    ¬ valid_enc (vyper_to_abi_type env t) bs ∨
    ¬ (static_length (vyper_to_abi_type env t) ≤ LENGTH bs) ∨
    ¬ (LENGTH bs ≤ vyper_abi_size_bound env t)
Proof
  rw[vyper_valid_enc_window]
QED

(* ===== Offset pointers are within the buffer (issue checks 1-2) ===== *)

(* The three dynamic ABI types with a runtime length word need it readable. *)
Theorem valid_enc_length_word_readable[local]:
  (!bs. valid_enc (Bytes NONE) bs ⇒ 32 ≤ LENGTH bs) ∧
  (!bs. valid_enc (String) bs ⇒ 32 ≤ LENGTH bs) ∧
  (!t2 bs. valid_enc (Array NONE t2) bs ⇒ 32 ≤ LENGTH bs)
Proof
  rw[valid_enc_def]
QED

Theorem drop_32_readable_in_bounds[local]:
  !bs n. 32 ≤ LENGTH (DROP n bs) ⇒ 32 + n ≤ LENGTH bs
Proof
  Induct_on `n` >> gvs[Once listTheory.DROP_LENGTH_TOO_LONG, LENGTH_TL]
QED

(* A dynamic member is reached at head offset j, and its own length word must
   be readable in DROP j bs.  Bounded nums then also rule out the 256-bit wrap
   that Vyper's `assert actual_ptr >= parent` guards against. *)
Theorem valid_enc_tuple_offset_in_bounds[local]:
  (!t2 ts bs.
     valid_enc (Tuple (Bytes NONE :: ts)) bs ⇒
     32 + abi_head_word bs ≤ LENGTH bs) ∧
  (!ts bs.
     valid_enc (Tuple (String :: ts)) bs ⇒
     32 + abi_head_word bs ≤ LENGTH bs) ∧
  (!t2 ts bs.
     valid_enc (Tuple (Array NONE t2 :: ts)) bs ⇒
     32 + abi_head_word bs ≤ LENGTH bs)
Proof
  rw[abi_head_word_def, valid_enc_def] >> simp[] >> strip_tac
  >> drule_all valid_enc_length_word_readable
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
  >- (drule (cj 1 valid_enc_tuple_offset_in_bounds) >> gvs[])
  >- (drule (cj 2 valid_enc_tuple_offset_in_bounds) >> gvs[])
  >> drule (cj 3 valid_enc_tuple_offset_in_bounds) >> gvs[]
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
  rw[evaluate_abi_decode_returndata_vyper_valid_enc, vyper_valid_enc_returndata_def]
QED

(* ===== The window never rejects our own encodings ===== *)

(* KEY SAFETY THEOREM: with vyper_valid_enc_valid_enc this pins the refinement
   direction - vyper_valid_enc is exactly valid_enc plus the size window. *)
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

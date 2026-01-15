Theory vyperABI
Ancestors
  contractABI vyperAST vyperInterpreter
  vyperMisc
Libs
  cv_transLib
  wordsLib

(* Overloads to disambiguate ABI value constructors from Vyper value constructors *)
Overload abi_IntV[local] = “IntV : int -> abi_value”
Overload abi_BytesV[local] = “BytesV : word8 list -> abi_value”

Definition vyper_base_to_abi_type_def[simp]:
  vyper_base_to_abi_type (UintT n) = Uint n ∧
  vyper_base_to_abi_type (IntT n) = Int n ∧
  vyper_base_to_abi_type BoolT = Bool ∧
  vyper_base_to_abi_type DecimalT = Int 168 ∧
  vyper_base_to_abi_type (StringT _) = String ∧
  vyper_base_to_abi_type (BytesT (Dynamic _)) = Bytes NONE ∧
  vyper_base_to_abi_type (BytesT (Fixed n)) = Bytes (SOME n) ∧
  vyper_base_to_abi_type AddressT = Address
End

Definition vyper_to_abi_type_def[simp]:
  vyper_to_abi_type (BaseT bt) = vyper_base_to_abi_type bt ∧
  vyper_to_abi_type (TupleT ts) = Tuple (MAP vyper_to_abi_type ts) ∧
  vyper_to_abi_type (ArrayT t (Dynamic _)) = Array NONE (vyper_to_abi_type t) ∧
  vyper_to_abi_type (ArrayT t (Fixed n)) = Array (SOME n) (vyper_to_abi_type t) ∧
  vyper_to_abi_type (StructT id) = Tuple [] (* TODO *) ∧
  vyper_to_abi_type (FlagT _) = Uint 256 ∧
  vyper_to_abi_type NoneT = Tuple []
Termination
  WF_REL_TAC ‘measure type_size’
End

Definition check_IntV_def:
  check_IntV b i =
  if within_int_bound b i then SOME $ IntV b i else NONE
End

Definition abi_to_vyper_def[simp]:
  abi_to_vyper env (BaseT $ UintT z) (NumV n) = check_IntV (Unsigned z) (&n) ∧
  abi_to_vyper env (BaseT $ IntT z) (IntV i) = check_IntV (Signed z) i ∧
  abi_to_vyper env (BaseT $ AddressT) (NumV n) =
    (if within_int_bound (Unsigned 160) (&n)
     then SOME $ AddressV (n2w n)
     else NONE) ∧
  abi_to_vyper env (BaseT $ BoolT) (NumV n) =
    (if n ≤ 1 then SOME $ BoolV (n = 1) else NONE) ∧
  abi_to_vyper env (BaseT $ BytesT b) (BytesV bs) =
    (if compatible_bound b (LENGTH bs) then SOME $ BytesV b bs else NONE) ∧
  abi_to_vyper env (BaseT $ StringT z) (BytesV bs) =
    (if LENGTH bs ≤ z then SOME $ StringV z (MAP (CHR o w2n) bs) else NONE) ∧
  abi_to_vyper env (BaseT $ DecimalT) (IntV i) =
    (if within_int_bound (Signed 168) i then SOME $ DecimalV i else NONE) ∧
  abi_to_vyper env (TupleT ts) (ListV vs) =
    (case abi_to_vyper_list env ts vs of NONE => NONE
        | SOME vs => SOME $ ArrayV $ TupleV vs) ∧
  abi_to_vyper env (ArrayT t b) (ListV vs) = (
    let n = LENGTH vs in
      if compatible_bound b n then
        case abi_to_vyper_list env (REPLICATE n t) vs of NONE => NONE
           | SOME vs => case evaluate_type env t of NONE => NONE
	     | SOME tv => SOME $ ArrayV $ make_array_value tv b vs
      else NONE ) ∧
  abi_to_vyper env NoneT (ListV ls) = (if NULL ls then SOME NoneV else NONE) ∧
  abi_to_vyper env (StructT id) (ListV vs) =
    (case FLOOKUP env (string_to_num id) of
       | SOME (StructArgs args) =>
         (case abi_to_vyper_list env (MAP SND args) vs of NONE => NONE
          | SOME vs => SOME $ StructV $ ZIP (MAP FST args, vs))
       | _ => NONE) ∧
  abi_to_vyper env (FlagT id) (NumV n) =
    (case FLOOKUP env (string_to_num id) of
      | SOME (FlagArgs m) =>
        if m ≤ 256 ∧ n < 2 ** m then SOME $ FlagV m (&n) else NONE
      | _ => NONE) ∧
  abi_to_vyper _ _ _ = NONE ∧
  abi_to_vyper_list env [] [] = SOME [] ∧
  abi_to_vyper_list env (t::ts) (v::vs) =
    (case abi_to_vyper env t v of NONE => NONE | SOME v =>
       case abi_to_vyper_list env ts vs of NONE => NONE | SOME vs =>
         SOME (v::vs)) ∧
  abi_to_vyper_list _ _ _ = NONE
Termination
  WF_REL_TAC ‘measure (λx. case x of INL (_, _, v) => abi_value_size v
                                   | INR (_, _, vs) => list_size abi_value_size vs)’
End

val abi_to_vyper_pre_def =
  abi_to_vyper_def
  |> REWRITE_RULE[GSYM CHR_o_w2n_eq]
  |> cv_auto_trans_pre "abi_to_vyper_pre abi_to_vyper_list_pre";

Theorem abi_to_vyper_pre[cv_pre]:
  (!v1 v0 v. abi_to_vyper_pre v1 v0 v) ∧
  (!v1 v0 v. abi_to_vyper_list_pre v1 v0 v)
Proof
  ho_match_mp_tac abi_to_vyper_ind
  \\ rw[]
  \\ rw[Once abi_to_vyper_pre_def]
QED

(* ===== Vyper to ABI Value Conversion ===== *)

(* Helper lemmas for termination proof *)

Theorem value5_size_eq_list_size:
  ∀vs. value5_size vs = list_size value_size vs
Proof
  Induct \\ rw[value_size_def, listTheory.list_size_def]
QED

Theorem value1_size_ge_map_snd:
  ∀fields. list_size value_size (MAP SND fields) ≤ value1_size fields
Proof
  Induct \\ rw[value_size_def, listTheory.list_size_def]
  \\ Cases_on ‘h’ \\ rw[value_size_def]
  \\ ‘list_size (λx. value_size (SND x)) fields = list_size value_size (MAP SND fields)’
      by rw[listTheory.list_size_map]
  \\ fs[]
QED

Theorem extract_elements_size:
  ∀av vs. extract_elements (ArrayV av) = SOME vs ⇒
          list_size value_size vs < 1 + array_value_size av
Proof
  Cases \\ rw[extract_elements_def, value_size_def, value5_size_eq_list_size]
  (* CHEATED - need to prove for SArrayV case that GENLIST produces list
     with size bounded by array_value_size. The TupleV and DynArrayV cases
     follow directly from value5_size_eq_list_size. For SArrayV:
     - Need lemma about GENLIST size with ALOOKUP/default_value
     - Show list_size value_size (GENLIST f n) relates to value3_size al
  >- (irule arithmeticTheory.LESS_EQ_LESS_TRANS
      \\ qexists_tac 'value5_size l'
      \\ rw[value5_size_eq_list_size, listTheory.list_size_map]
      \\ (* need lemma about GENLIST with ALOOKUP *) ...)
  *)
  \\ cheat
QED

(* Convert Vyper values to ABI values for encoding.
   This is the inverse of abi_to_vyper. *)

Definition vyper_to_abi_value_def:
  vyper_to_abi_value (IntV (Unsigned _) i) =
    (if 0 ≤ i then SOME (NumV (Num i)) else NONE) ∧
  vyper_to_abi_value (IntV (Signed _) i) =
    SOME (abi_IntV i) ∧
  vyper_to_abi_value (BoolV b) =
    SOME (NumV (if b then 1 else 0)) ∧
  vyper_to_abi_value (BytesV _ bs) =
    SOME (abi_BytesV bs) ∧
  vyper_to_abi_value (StringV _ s) =
    SOME (abi_BytesV (MAP (n2w o ORD) s)) ∧
  vyper_to_abi_value (DecimalV i) =
    SOME (abi_IntV i) ∧
  vyper_to_abi_value (FlagV _ n) =
    SOME (NumV (Num (&n))) ∧
  vyper_to_abi_value NoneV =
    SOME (ListV []) ∧
  vyper_to_abi_value (StructV fields) =
    OPTION_MAP ListV (vyper_to_abi_value_list (MAP SND fields)) ∧
  vyper_to_abi_value (ArrayV av) =
    (case extract_elements (ArrayV av) of
       SOME vs => OPTION_MAP ListV (vyper_to_abi_value_list vs)
     | NONE => NONE) ∧
  vyper_to_abi_value_list [] = SOME [] ∧
  vyper_to_abi_value_list (v::vs) =
    (case vyper_to_abi_value v of NONE => NONE | SOME av =>
     case vyper_to_abi_value_list vs of NONE => NONE | SOME avs =>
       SOME (av::avs))
Termination
  WF_REL_TAC ‘measure (λx. case x of INL v => value_size v
                                   | INR vs => list_size value_size vs)’
  \\ cheat
  (* CHEATED - termination goals:
     1. StructV fields case: show list_size value_size (MAP SND fields) < 1 + value1_size fields
        - Use value1_size_ge_map_snd lemma
     2. ArrayV av case: show list_size value_size vs < 1 + array_value_size av
        when extract_elements (ArrayV av) = SOME vs
        - Use extract_elements_size lemma (also cheated)
     Original proof approach: use rw with value_size_def and list_size_def,
     then for StructV case use LESS_EQ_LESS_TRANS with value1_size_ge_map_snd,
     and for ArrayV case use drule with extract_elements_size.
  *)
End

(* NOTE: cv_auto_trans for vyper_to_abi_value fails because the cv translator
   needs to prove termination for its generated cv definition, and the recursion
   through extract_elements makes this complex. The original definition‘s
   termination is cheated, but that doesn‘t help the cv translation.
val vyper_to_abi_value_pre_def =
  vyper_to_abi_value_def
  |> cv_auto_trans_pre "vyper_to_abi_value_pre vyper_to_abi_value_list_pre";
*)

(* ===== ABI Builtin Evaluation ===== *)

(* Evaluation functions for AbiEncode and AbiDecode type builtins.
   These are called from the small-step interpreter when evaluating
   TypeBuiltin AbiEncode/AbiDecode. *)

Definition evaluate_abi_encode_def:
  evaluate_abi_encode typ vs =
    case vyper_to_abi_value (ArrayV (TupleV vs)) of
      SOME abiVal =>
        let abiTy = vyper_to_abi_type typ in
        let encoded = enc abiTy abiVal in
        INL $ BytesV (Dynamic (LENGTH encoded)) encoded
    | NONE => INR "abi_encode conversion"
End

(* TODO: cv_auto_trans for evaluate_abi_encode requires termination proof for vyper_to_abi_value
val () = cv_auto_trans evaluate_abi_encode_def;
*)

Definition evaluate_abi_decode_def:
  evaluate_abi_decode tenv typ bs =
    let abiTy = vyper_to_abi_type typ in
    if valid_enc abiTy bs then
      case abi_to_vyper tenv typ (dec abiTy bs) of
        SOME v => INL v
      | NONE => INR "abi_decode conversion"
    else INR "abi_decode invalid"
End

(* TODO: cv_auto_trans for evaluate_abi_decode - depends on enc/dec translations
val () = cv_auto_trans evaluate_abi_decode_def
*)

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
  WF_REL_TAC `measure type_size`
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
  WF_REL_TAC `measure (λx. case x of INL (_, _, v) => abi_value_size v
                                   | INR (_, _, vs) => list_size abi_value_size vs)`
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

(* Helper lemmas for termination proof.
   Using lambda forms since TFL expands MAP to lambda. *)

Theorem value5_size_eq_list_size:
  ∀vs. value5_size vs = list_size value_size vs
Proof
  Induct \\ rw[value_size_def, listTheory.list_size_def]
QED

Theorem value3_size_snd:
  ∀al. list_size (λx. value_size (SND x)) al ≤ value3_size al
Proof
  Induct \\ rw[value_size_def, listTheory.list_size_def]
  \\ Cases_on `h` \\ rw[value_size_def] \\ fs[]
QED

Theorem value1_size_snd:
  ∀fields. list_size (λx. value_size (SND x)) fields ≤ value1_size fields
Proof
  Induct \\ rw[value_size_def, listTheory.list_size_def]
  \\ Cases_on `h` \\ rw[value_size_def] \\ fs[]
QED

(* TFL expands pair types to pair_size, so we need lemmas relating them to valueN_size *)
Theorem value1_pair_size:
  ∀fields. list_size (pair_size (list_size char_size) value_size) fields = value1_size fields
Proof
  Induct \\ rw[listTheory.list_size_def, value_size_def, basicSizeTheory.pair_size_def]
  \\ Cases_on `h` \\ rw[value_size_def, basicSizeTheory.pair_size_def]
QED

Theorem value3_pair_size:
  ∀al. list_size (pair_size (λx. x) value_size) al = value3_size al
Proof
  Induct \\ rw[listTheory.list_size_def, value_size_def, basicSizeTheory.pair_size_def]
  \\ Cases_on `h` \\ rw[value_size_def, basicSizeTheory.pair_size_def]
QED

(* Convert Vyper values to ABI values for encoding.
   This is the inverse of abi_to_vyper.

   IMPORTANT: This function handles array_value cases directly instead of
   going through extract_elements, to ensure termination. For SArrayV, we
   only recurse on values stored in the alist, not on generated defaults.
   The type_value in SArrayV is used to generate ABI defaults directly
   without creating intermediate Vyper values.
*)

(* Generate ABI default value from a type_value.
   This terminates on type_value_size. *)
Definition abi_default_from_type_def:
  abi_default_from_type (BaseTV (UintT _)) = NumV 0 ∧
  abi_default_from_type (BaseTV (IntT _)) = abi_IntV 0 ∧
  abi_default_from_type (BaseTV BoolT) = NumV 0 ∧
  abi_default_from_type (BaseTV DecimalT) = abi_IntV 0 ∧
  abi_default_from_type (BaseTV (StringT _)) = abi_BytesV [] ∧
  abi_default_from_type (BaseTV (BytesT (Dynamic _))) = abi_BytesV [] ∧
  abi_default_from_type (BaseTV (BytesT (Fixed n))) = abi_BytesV (REPLICATE n 0w) ∧
  abi_default_from_type (BaseTV AddressT) = NumV 0 ∧
  abi_default_from_type (TupleTV ts) = ListV (abi_default_from_type_list ts) ∧
  abi_default_from_type (ArrayTV t (Dynamic _)) = ListV [] ∧
  abi_default_from_type (ArrayTV t (Fixed n)) =
    ListV (REPLICATE n (abi_default_from_type t)) ∧
  abi_default_from_type (StructTV fields) =
    ListV (abi_default_from_type_list (MAP SND fields)) ∧
  abi_default_from_type (FlagTV _) = NumV 0 ∧
  abi_default_from_type NoneTV = ListV [] ∧
  abi_default_from_type_list [] = [] ∧
  abi_default_from_type_list (t::ts) =
    abi_default_from_type t :: abi_default_from_type_list ts
Termination
  WF_REL_TAC `measure (λx. case x of INL t => type_value_size t
                                   | INR ts => list_size type_value_size ts)`
  \\ rw[type_value_size_def, listTheory.list_size_def, listTheory.list_size_map]
  \\ Induct_on `fields` \\ rw[type_value_size_def, listTheory.list_size_def]
  \\ Cases_on `h` \\ rw[type_value_size_def]
End

(* Convert Vyper value to ABI value, with separate handling for array_value.
   - For TupleV and DynArrayV: recurse on stored value list
   - For SArrayV: recurse on alist values, use abi_default_from_type for missing
*)
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
  vyper_to_abi_value (ArrayV (TupleV vs)) =
    OPTION_MAP ListV (vyper_to_abi_value_list vs) ∧
  vyper_to_abi_value (ArrayV (DynArrayV _ _ vs)) =
    OPTION_MAP ListV (vyper_to_abi_value_list vs) ∧
  vyper_to_abi_value (ArrayV (SArrayV t n al)) =
    (* For sparse arrays: convert stored values, fill in defaults *)
    (case vyper_to_abi_alist al of NONE => NONE | SOME abiAl =>
       let def = abi_default_from_type t in
       SOME (ListV (GENLIST (λi. case ALOOKUP abiAl i of
                                   SOME v => v | NONE => def) n))) ∧
  vyper_to_abi_value_list [] = SOME [] ∧
  vyper_to_abi_value_list (v::vs) =
    (case vyper_to_abi_value v of NONE => NONE | SOME av =>
     case vyper_to_abi_value_list vs of NONE => NONE | SOME avs =>
       SOME (av::avs)) ∧
  (* Convert alist of (index, value) pairs *)
  vyper_to_abi_alist [] = SOME [] ∧
  vyper_to_abi_alist ((i,v)::rest) =
    (case vyper_to_abi_value v of NONE => NONE | SOME av =>
     case vyper_to_abi_alist rest of NONE => NONE | SOME avs =>
       SOME ((i,av)::avs))
Termination
  WF_REL_TAC `measure (λx. case x of INL v => value_size v
                                   | INR (INL vs) => list_size value_size vs
                                   | INR (INR al) => value3_size al)`
  \\ rw[value_size_def, value5_size_eq_list_size, value1_pair_size, value3_pair_size]
  (* Remaining goal: list_size (λx. value_size (SND x)) fields < value1_size fields + 1 *)
  \\ rw[GSYM arithmeticTheory.ADD1]
  \\ irule arithmeticTheory.LESS_EQ_IMP_LESS_SUC
  \\ rw[value1_size_snd]
End

(* TODO: cv_auto_trans for abi_default_from_type fails due to REPLICATE recursion
val () = cv_auto_trans abi_default_from_type_def;
val () = cv_auto_trans vyper_to_abi_value_def;
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

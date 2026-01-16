Theory vyperABI
Ancestors
  contractABI vyperAST vyperTypeValue
  vyperMisc
Libs
  cv_transLib
  wordsLib

(* Overloads to disambiguate ABI value constructors from Vyper value constructors *)
Overload abi_IntV[local] = ``IntV : int -> abi_value``
Overload abi_BytesV[local] = ``BytesV : word8 list -> abi_value``

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
  vyper_to_abi_type (TupleT ts) = Tuple (vyper_to_abi_types ts) ∧
  vyper_to_abi_type (ArrayT t (Dynamic _)) = Array NONE (vyper_to_abi_type t) ∧
  vyper_to_abi_type (ArrayT t (Fixed n)) = Array (SOME n) (vyper_to_abi_type t) ∧
  vyper_to_abi_type (StructT id) = Tuple [] (* TODO *) ∧
  vyper_to_abi_type (FlagT _) = Uint 256 ∧
  vyper_to_abi_type NoneT = Tuple [] ∧
  vyper_to_abi_types [] = [] ∧
  vyper_to_abi_types (t::ts) = vyper_to_abi_type t :: vyper_to_abi_types ts
Termination
  WF_REL_TAC `measure (λx. case x of INL t => type_size t
                                   | INR ts => list_size type_size ts)`
End

val () = cv_auto_trans vyper_base_to_abi_type_def;
val () = cv_auto_trans_rec vyper_to_abi_type_def (
  WF_REL_TAC `measure (λx. case x of INL t => cv_size t
                                   | INR ts => cv_size ts)`
  \\ rw[]
  \\ TRY (Cases_on `cv_v` \\ gvs[cvTheory.cv_size_def] \\ NO_TAC)
  \\ Cases_on `cv_v` \\ gvs[cvTheory.cv_size_def]
  \\ qmatch_goalsub_rename_tac `cv_fst p`
  \\ Cases_on `p` \\ gvs[cvTheory.cv_size_def]
);

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

(* ===== ABI Decode Evaluation ===== *)

(* Evaluation function for AbiDecode type builtin.
   Called from the small-step interpreter when evaluating TypeBuiltin AbiDecode. *)

Definition evaluate_abi_decode_def:
  evaluate_abi_decode tenv typ bs =
    let abiTy = vyper_to_abi_type typ in
    if valid_enc abiTy bs then
      case abi_to_vyper tenv typ (dec abiTy bs) of
        SOME v => INL v
      | NONE => INR "abi_decode conversion"
    else INR "abi_decode invalid"
End

val () = cv_auto_trans evaluate_abi_decode_def;

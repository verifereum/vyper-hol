open HolKernel boolLib bossLib Parse wordsLib cv_transLib
     contractABITheory vyperAstTheory vyperInterpreterTheory

val () = new_theory "vyperAbi";

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

Definition abi_to_vyper_def[simp]:
  abi_to_vyper (BaseT $ UintT z) (NumV n) = SOME $ IntV (&n) ∧
  abi_to_vyper (BaseT $ IntT z) (IntV i) = SOME $ IntV i ∧
  abi_to_vyper (BaseT $ AddressT) (NumV n) = SOME $ AddressV (n2w n) ∧
  abi_to_vyper (BaseT $ BoolT) (NumV n) = SOME $ BoolV (0 < n) ∧
  abi_to_vyper (BaseT $ BytesT b) (BytesV bs) =
    (if compatible_bound b (LENGTH bs) then SOME $ BytesV b bs else NONE) ∧
  abi_to_vyper (BaseT $ StringT z) (BytesV bs) =
    (if LENGTH bs ≤ z then SOME $ StringV z (MAP (CHR o w2n) bs) else NONE) ∧
  abi_to_vyper (TupleT ts) (ListV vs) =
    (case abi_to_vyper_list ts vs of NONE => NONE
        | SOME vs => SOME $ ArrayV (Fixed (LENGTH ts)) vs) ∧
  abi_to_vyper (ArrayT t b) (ListV vs) = (
    let n = LENGTH vs in
      if compatible_bound b n then
        case abi_to_vyper_list (REPLICATE n t) vs of NONE => NONE
           | SOME vs => SOME $ ArrayV b vs
      else NONE ) ∧
  abi_to_vyper NoneT (ListV ls) = (if NULL ls then SOME NoneV else NONE) ∧
  abi_to_vyper _ _ = NONE ∧
  (* TODO: decimals *)
  (* TODO: flags *)
  (* TODO: structs *)
  abi_to_vyper_list [] [] = SOME [] ∧
  abi_to_vyper_list (t::ts) (v::vs) =
    (case abi_to_vyper t v of NONE => NONE | SOME v =>
       case abi_to_vyper_list ts vs of NONE => NONE | SOME vs =>
         SOME (v::vs)) ∧
  abi_to_vyper_list _ _ = NONE
Termination
  WF_REL_TAC ‘measure (λx. case x of INL (_, v) => abi_value_size v
                                   | INR (_, vs) => list_size abi_value_size vs)’
End

Definition CHR_o_w2n_def:
  CHR_o_w2n (b: byte) = CHR (w2n b)
End

val CHR_o_w2n_pre_def = cv_auto_trans_pre CHR_o_w2n_def;

Theorem CHR_o_w2n_pre[cv_pre]:
  CHR_o_w2n_pre x
Proof
  rw[CHR_o_w2n_pre_def]
  \\ qspec_then`x`mp_tac wordsTheory.w2n_lt
  \\ rw[]
QED

Theorem CHR_o_w2n_eq:
  CHR_o_w2n = CHR o w2n
Proof
  rw[FUN_EQ_THM, CHR_o_w2n_def]
QED

val abi_to_vyper_pre_def =
  abi_to_vyper_def
  |> REWRITE_RULE[GSYM CHR_o_w2n_eq]
  |> cv_auto_trans_pre;

Theorem abi_to_vyper_pre[cv_pre]:
  (!v0 v. abi_to_vyper_pre v0 v) ∧
  (!v0 v. abi_to_vyper_list_pre v0 v)
Proof
  ho_match_mp_tac abi_to_vyper_ind
  \\ rw[]
  \\ rw[Once abi_to_vyper_pre_def]
QED

val () = export_theory();

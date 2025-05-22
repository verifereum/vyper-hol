open HolKernel boolLib bossLib Parse
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

(*
Definition abi_to_vyper_def:
  abi_to_vyper (BaseT $ UintT z) (NumV n) = SOME $ IntV (&n) ∧
  abi_to_vyper (BaseT $ IntT z) (IntV i) = SOME $ IntV i ∧
  abi_to_vyper (BaseT $ AddressT) (NumV n) = SOME $ AddressV (n2w n) ∧
  abi_to_vyper (BaseT $ BoolT) (NumV n) = SOME $ BoolV (0 < n) ∧
  abi_to_vyper (BaseT $ BytesT b) (BytesV bs) =
    (if compatible_bound b (LENGTH bs) then SOME $ BytesV b bs else NONE) ∧
  abi_to_vyper (BaseT $ StringT z) (BytesV bs) =
    (if LENGTH bs ≤ z then SOME $ StringV z (MAP (CHR o w2n) sb) else NONE) ∧
  abi_to_vyper (TupleT ts) (ListV vs) =
  (* cover every case in has_type *)
*)

val () = export_theory();

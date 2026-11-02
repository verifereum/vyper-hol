Theory vyperABIEntries
Ancestors
  vyperABI vyperAST list rich_list arithmetic words
Libs
  proofAuditLib
  cv_transLib

(* Shared source-level ABI entries, independent of compiler labels/operands.
   k is the number of supplied keyword arguments, shortest signature first. *)
Definition abi_entries_def:
  abi_entries args dflts =
    GENLIST (\k. (TAKE (LENGTH args - LENGTH dflts + k) args, k))
      (LENGTH dflts + 1)
End

Theorem abi_entries_length[simp]:
  LENGTH (abi_entries args dflts) = LENGTH dflts + 1
Proof
  simp[abi_entries_def]
QED

Theorem abi_entries_el:
  k <= LENGTH dflts ==>
  EL k (abi_entries args dflts) =
    (TAKE (LENGTH args - LENGTH dflts + k) args, k)
Proof
  simp[abi_entries_def, EL_GENLIST]
QED

Theorem abi_entries_member:
  MEM (prefix,k) (abi_entries args dflts) <=>
  k <= LENGTH dflts /\
  prefix = TAKE (LENGTH args - LENGTH dflts + k) args
Proof
  simp[abi_entries_def, MEM_GENLIST] >> metis_tac[pairTheory.PAIR_EQ, LESS_EQ_IFF_LESS_SUC, ADD1]
QED

Theorem abi_entries_shortest:
  HD (abi_entries args dflts) =
    (TAKE (LENGTH args - LENGTH dflts) args, 0)
Proof
  simp[abi_entries_def, HD_GENLIST_COR]
QED

Theorem abi_entries_full:
  LENGTH dflts <= LENGTH args ==>
  EL (LENGTH dflts) (abi_entries args dflts) = (args,LENGTH dflts)
Proof
  simp[abi_entries_el]
QED

Theorem abi_entries_no_defaults[simp]:
  abi_entries args [] = [(args,0)]
Proof
  simp[abi_entries_def, GENLIST]
QED

Definition abi_method_id_def:
  abi_method_id tenv name arg_types =
    FOLDL (\n b. 256 * n + w2n b) 0
      (function_selector name (vyper_to_abi_types tenv arg_types))
End

Definition abi_function_signatures_def:
  abi_function_signatures name args dflts =
    MAP (\(prefix,k). (name, MAP SND prefix)) (abi_entries args dflts)
End

(* A public array getter consumes one uint256 index per array layer;
   a public mapping getter consumes its declared key type at each layer. *)
Definition abi_array_getter_args_def:
  abi_array_getter_args (ArrayT ty bound) =
    BaseT (UintT 256) :: abi_array_getter_args ty /\
  abi_array_getter_args _ = []
End

Definition abi_getter_args_def:
  abi_getter_args (Type ty) = abi_array_getter_args ty /\
  abi_getter_args (HashMapT kt vt) = kt :: abi_getter_args vt
End

Definition abi_decl_signatures_def:
  abi_decl_signatures (FunctionDecl External mut nr rr name args dflts ret body) =
    (if name = "__default__" then []
     else abi_function_signatures name args dflts) /\
  abi_decl_signatures (VariableDecl Public mut name ty slot) =
    [(name, abi_array_getter_args ty)] /\
  abi_decl_signatures (HashMapDecl Public trans name kt vt slot) =
    [(name, kt :: abi_getter_args vt)] /\
  abi_decl_signatures _ = []
End

Definition abi_external_signatures_def:
  abi_external_signatures tops = FLAT (MAP abi_decl_signatures tops)
End

Definition abi_external_method_ids_def:
  abi_external_method_ids tenv tops =
    MAP (\(name,tys). abi_method_id tenv name tys)
      (abi_external_signatures tops)
End

Theorem abi_function_signatures_no_defaults[simp]:
  abi_function_signatures name args [] = [(name, MAP SND args)]
Proof
  simp[abi_function_signatures_def]
QED

Theorem abi_function_signatures_length[simp]:
  LENGTH (abi_function_signatures name args dflts) = LENGTH dflts + 1
Proof
  simp[abi_function_signatures_def]
QED

val () = cv_auto_trans abi_entries_def;
val () = cv_auto_trans abi_method_id_def;
val () = cv_auto_trans abi_function_signatures_def;
val () = cv_auto_trans abi_array_getter_args_def;
val () = cv_auto_trans abi_getter_args_def;
val () = cv_auto_trans abi_decl_signatures_def;
val () = cv_auto_trans abi_external_signatures_def;
val () = cv_auto_trans abi_external_method_ids_def;

(* Checked prefix order and the three selectors of the dflt_multi witness. *)
Theorem dflt_multi_abi_method_ids:
  MAP (\(name,tys). abi_method_id FEMPTY name tys)
    (abi_function_signatures "f"
      [("a",BaseT (UintT 256)); ("b",BaseT BoolT);
       ("c",BaseT AddressT)] [();()]) =
    [0xb3de648b;0x2735acb7;0x879474db]
Proof
  CONV_TAC cv_eval
QED

Theorem abi_getter_signature_examples:
  abi_decl_signatures
    (VariableDecl Public Storage "x" (BaseT (UintT 256)) NONE) =
      [("x",[])] /\
  abi_decl_signatures
    (HashMapDecl Public F "m" (BaseT AddressT)
      (Type (ArrayT (BaseT BoolT) (Fixed 3))) NONE) =
      [("m",[BaseT AddressT; BaseT (UintT 256)])]
Proof
  EVAL_TAC
QED

val () = proofAuditLib.check_theory "vyperABIEntries";

Theory sourceOrdinaryAcceptanceBase
Ancestors
  vyperAST vyperContext vyperValue

(* The legacy interface constructor adds this pure identity operation. Source
   emits the address itself; expected AST normalization is explicit, not a
   false claim of literal legacy AST equality. *)
Theorem ordinary_interface_cast_value_identity:
  evaluate_builtin cx acc (BaseT AddressT) (Acc Address) [BaseT AddressT] [BytesV bs] =
    INL (BytesV bs)
Proof
  simp[evaluate_builtin_def, evaluate_account_op_def]
QED

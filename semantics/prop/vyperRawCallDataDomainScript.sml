Theory vyperRawCallDataDomain
Ancestors
  vyperTypeSystem

(* WHY THIS IS TRUE: The ordinary RawCallTarget lowering consumes a memory
   bytestring pointer. Its second operand must therefore have dynamic Bytes
   type, not the stack-word representation of bytesM. Unfolding the typing
   clause gives the capacity witness independently of the flags, keywords,
   default return, or result type. This is the domain fact behind the negative
   contract regression. RawCallCalldataTarget has no data operand and is not
   restricted by this change. *)
Theorem raw_call_typed_data_dynamic:
  well_typed_expr env (Call ty (RawCallTarget flags) args drv) ==>
  ?n. expr_type (EL 1 args) = BaseT (BytesT (Dynamic n))
Proof
  pure_rewrite_tac [well_typed_expr_def] >> strip_tac >>
  `1 < LENGTH args` by decide_tac >>
  fs[listTheory.EL_MAP]
QED

(* The abi_decode builtin fails with a runtime error, which a reverting
   Venom exit matches, exactly when evaluate_abi_decode rejects the bytes
   at the decoded (possibly tuple-wrapped) type. *)
Theory exprSimAbiDecodeReject
Ancestors
  vyperContext exprSimDefs

Theorem abi_decode_builtin_reject:
  !cx unwrap typ tys bs e t.
    evaluate_abi_decode (get_tenv cx)
      (if unwrap /\ needs_external_call_wrap typ then TupleT [typ] else typ)
      bs = INR e ==>
    evaluate_type_builtin cx (AbiDecode unwrap) typ tys [BytesV bs] =
      INR (RuntimeError e) /\
    expr_exit (INR (Error (RuntimeError e))) (Abort Revert_abort t)
Proof
  rw[evaluate_type_builtin_def, expr_exit_def] >> gvs[]
QED

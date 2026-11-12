(*
 * abi_encode, the tuple branch: more than one argument, or ensure_tuple.
 * A piece of bodyPtrAbiEncode: compile_abi_encode_args, the tuple buffer
 * and compile_store_abi_tuple, then lower_abi_encode.
 *
 * TOP-LEVEL:
 *   abi_encode_tuple_sim_ptr
 *)
Theory bodyPtrAbiEncodeTuple
Ancestors
  bodyPtrPreds bodyPtrDefs bodySim exprSimHyps vyperAST vyperInterpreter
  vyperState vyperContext vyperTypeCallGraph list

val _ = Parse.hide "body";

(* ADMITTED: the tuple branch is its own piece. *)
Theorem abi_encode_tuple_sim_ptr:
  !d PG tops ctx func cenv cx env ty ann b m typ es st.
    ~(LENGTH es = 1 /\ ~b) /\
    (type_builtin_args_length_ok (AbiEncode b m) (LENGTH es) ==>
     body_exprs_ptr_ok cx es) /\
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (TypeBuiltin ann (AbiEncode b m) typ es) st ==>
    expr_sim_ptr d ctx PG func cenv cx ty
      (TypeBuiltin ann (AbiEncode b m) typ es) st /\
    expr_vv_sim_ptr d ctx PG func cenv cx ty
      (TypeBuiltin ann (AbiEncode b m) typ es) st
Proof
  cheat
QED

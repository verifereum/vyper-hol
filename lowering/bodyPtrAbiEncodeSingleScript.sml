(*
 * abi_encode, the single-argument branch: one argument, no ensure_tuple.
 * A piece of bodyPtrAbiEncode: a word argument is staged in a 32-byte
 * buffer, a memory one unwrapped, then lower_abi_encode.
 *
 * TOP-LEVEL:
 *   abi_encode_single_sim_ptr
 *)
Theory bodyPtrAbiEncodeSingle
Ancestors
  abiEncodePtrPhases bodyPtrPreds bodyPtrDefs bodySim exprSimHyps vyperAST vyperInterpreter
  vyperState vyperContext vyperTypeCallGraph list

val _ = Parse.hide "body";

Theorem abi_encode_single_sim_ptr:
  !d PG tops ctx func cenv cx env ty ann m typ e st.
    body_expr_ptr_ok cx e /\
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (TypeBuiltin ann (AbiEncode F m) typ [e]) st ==>
    expr_sim_ptr d ctx PG func cenv cx ty
      (TypeBuiltin ann (AbiEncode F m) typ [e]) st /\
    expr_vv_sim_ptr d ctx PG func cenv cx ty
      (TypeBuiltin ann (AbiEncode F m) typ [e]) st
Proof
  cheat
QED

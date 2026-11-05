(*
 * S3 piece: a function body that lookup_function returns can only mention
 * an abi_decode target that occurs in the program, so bodyMemory's
 * body_stmts_sim_mem premise on abi_decode targets holds for the body of
 * the called external function.  Getter bodies mention none.
 *)
Theory loweringMemAbiTarget
Ancestors
  supportedProgram vyperInterpreter

Theorem lookup_function_abi_decode_target:
  !src name vis tops mut nr args dflts ret body target.
    lookup_function src name vis tops = SOME (mut, nr, args, dflts, ret, body) /\
    supported_stmts_expr_exists (expr_abi_decode_target_root target) body ==>
    occurs_abi_decode_target target tops
Proof
  cheat
QED

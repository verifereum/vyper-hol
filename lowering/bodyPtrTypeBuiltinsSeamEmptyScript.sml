(*
 * Seam of bodyPtrTypeBuiltins: empty(T) for a memory-valued T.
 * The word case is bodyPtrTypeBuiltinsWordCases' empty_word_body_expr_ptr_ok.
 *
 * TOP-LEVEL:
 *   empty_memory_body_expr_ptr_ok
 *)
Theory bodyPtrTypeBuiltinsSeamEmpty
Ancestors
  bodyPtrTypeBuiltinsEmptyExec bodyPtrTypeBuiltinsEmptyPost
  exprPtrUnwrap bodyPtrPreds bodyPtrDefs bodySim exprSimHyps vyperAST
  vyperInterpreter vyperState vyperContext vyperTypeCallGraph list

val _ = Parse.hide "body";

(* empty(T) for a non-word T lowers to compile_builtin_empty_complex:
   allocate a buffer of T's memory size, then zero it (a header MSTORE of
   0 for a bytestring or dynamic array, zero words for the rest), and
   return its base pointer as a LocMemory LocatedValue.  The source value
   is default_value of T, and typing forces args = [].  S1's proof of the
   case is in exprSimBuiltins/exprSimBufferEmpty*; the lane's proved pieces
   are bodyPtrTypeBuiltinsEmpty* (allocation, zero-word and header tails,
   frames, empty_robust_default_memory). *)
Theorem empty_memory_body_expr_ptr_ok:
  !cx ann typ args.
    ~is_word_type typ ==>
    body_expr_ptr_ok cx (TypeBuiltin ann Empty typ args)
Proof
  cheat
QED

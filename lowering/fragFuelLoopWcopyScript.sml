(*
 * Fuel bound for the word-copy loop of the context helpers.
 *
 * TOP-LEVEL:
 *   fuel_okS_compile_word_copy_loop_base
 *)

Theory fragFuelLoopWcopy
Ancestors
  fragFuel fragFuelContextBase emitHelper context venomInst
Libs
  fragFuelLib

(* The loop counts a fresh counter from 0 up to the value of count_op,
   leaving through the exit block when they are equal.  Each round runs
   the body's straight-line code and one JMP back to the condition block.
   count_op was allocated before the loop, and the body writes only the
   counter and variables it allocates itself, so the bound stays fixed and
   the number of rounds is below 2 ** 256. *)
Theorem fuel_okS_compile_word_copy_loop_base:
  !src_op dst_op count_op load_loc store_loc is_ctor imm Wv E.
    fuel_okS (\st. !x. count_op = Var x ==> var_below st.cs_next_var x) Wv {} E
      (compile_word_copy_loop_base src_op dst_op count_op load_loc store_loc
         is_ctor imm)
Proof
  cheat
QED

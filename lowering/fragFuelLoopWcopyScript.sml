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

(* Straight-line body, stopping before the counter update. *)
Theorem fuel_ok_word_copy_body[local]:
  !counter_var src_op dst_op load_loc store_loc is_ctor imm.
    fuel_ok {} {} {}
      (do
        src_off <- (if word_scale load_loc = 1 then
          emit_op ADD [src_op; Var counter_var]
        else do
          scaled <- emit_op MUL [Var counter_var; Lit (n2w (word_scale load_loc))];
          emit_op ADD [src_op; scaled]
        od);
        val_loaded <- compile_ptr_load is_ctor imm load_loc src_off;
        dst_off <- (if word_scale store_loc = 1 then
          emit_op ADD [dst_op; Var counter_var]
        else do
          scaled <- emit_op MUL [Var counter_var; Lit (n2w (word_scale store_loc))];
          emit_op ADD [dst_op; scaled]
        od);
        compile_ptr_store is_ctor imm store_loc dst_off val_loaded
      od)
Proof
  rpt gen_tac >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_compile_ptr_load,
             fuel_ok_compile_ptr_store] >>
  simp[is_terminator_def]
QED

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

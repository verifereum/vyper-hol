(*
 * Fuel bound for the array-membership search loop.
 *
 * TOP-LEVEL:
 *   fuel_okS_compile_array_membership_loop
 *)

Theory fragFuelLoopArrayMembership
Ancestors
  fragFuel fragFuelContextBase exprLowering compileEnv emitHelper context
  venomInst
Libs
  fragFuelLib

(* The loop counts a fresh idx_var from 0 up by 1 per round until it equals
   len_op, leaving through the exit block (or earlier through the found
   block).  len_op was allocated before the function (or is a literal; never
   a label, whose value the loader's bound says nothing about), and
   the loop writes only idx_var, result_var and variables it allocates
   itself, so the bound is fixed during the body; the loader is straight-line
   code by hypothesis.  So at most len_op (< 2 ** 256) rounds run, each of
   bounded length, and idx_var never wraps. *)
Theorem fuel_okS_compile_array_membership_loop:
  !loader.
    (!a Wv E. fuel_ok Wv {} E (loader a)) ==>
    !needle arr_op len_op elem_size offset_base bound_opt is_in Wv E.
      fuel_okS (\st. (!x. len_op = Var x ==> var_below st.cs_next_var x) /\
                     !l. len_op <> Label l)
        Wv {} E
        (compile_array_membership_loop needle arr_op len_op elem_size
           offset_base loader bound_opt is_in)
Proof
  cheat
QED

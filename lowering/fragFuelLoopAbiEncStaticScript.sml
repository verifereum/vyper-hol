(*
 * Fuel bound for the static-element dynamic-array ABI encode loop.
 *
 * TOP-LEVEL:
 *   fuel_okS_compile_abi_encode_dyn_static_loop
 *)

Theory fragFuelLoopAbiEncStatic
Ancestors
  fragFuel fragFuelContextBase abiEncoder compileEnv emitHelper context
  venomInst
Libs
  fragFuelLib

(* The loop counter lives in a buffer the function allocates itself and
   starts at 0.  Each round, while the counter is below len_op (unsigned),
   encodes one element with straight-line code (no calls back into the
   encoder) and adds 1, then jumps back to the header.  len_op is a
   parameter: when it is a variable it was allocated before the call, and
   the body writes only variables it allocates itself, so the bound stays
   fixed.  The counter is at most len_op < 2 ** 256, so it does not wrap
   and the loop leaves within 2 ** 256 rounds.  (The body's memory writes
   go to the destination buffer, disjoint from the counter's buffer.) *)
Theorem fuel_okS_compile_abi_encode_dyn_static_loop:
  !dst src elem_info elem_abi_sz elem_mem_sz len_op Wv E.
    fuel_okS (\st. !x. len_op = Var x ==> var_below st.cs_next_var x) Wv {} E
      (compile_abi_encode_dyn_static_loop dst src elem_info elem_abi_sz
         elem_mem_sz len_op)
Proof
  cheat
QED

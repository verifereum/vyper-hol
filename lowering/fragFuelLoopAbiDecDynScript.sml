(*
 * Fuel bound for the dynamic-array ABI decode loop.
 *
 * TOP-LEVEL:
 *   fuel_okS_compile_abi_decode_dyn_loop
 *)

Theory fragFuelLoopAbiDecDyn
Ancestors
  fragFuel fragFuelContextBase abiEncoder compileEnv emitHelper context
  venomInst
Libs
  fragFuelLib

(* Given a bound for decoding one element (the recursive call), the loop is
   bounded.  The counter is the word at i_ptr, which the caller allocated
   just before and set to 0.  Each round reloads the element count from the
   source (it is not written by the decode, which writes only to the
   destination buffer and to buffers it allocates itself), exits when the
   counter reaches it, and otherwise decodes one element and adds 1 to the
   counter.  The loaded count is below 2 ** 256 (and a checked maximum), so
   the counter does not wrap and the loop leaves within 2 ** 256 rounds.
   i_ptr is a parameter: when it is a variable it was allocated before the
   call, so the body, which writes only variables it allocates itself,
   leaves it alone; that is the precondition. *)
Theorem fuel_okS_compile_abi_decode_dyn_loop:
  !dst src_op load_opc base_op hi_op elem_info elem_abi_sz elem_mem_sz i_ptr cnt.
    ~is_terminator load_opc /\ load_opc <> PHI /\ load_opc <> INVOKE /\
    (!d s Wv E.
       fuel_ok Wv {} E
         (compile_abi_decode_to_buf d s load_opc base_op hi_op elem_info)) ==>
    !Wv E.
      fuel_okS (\st. !x. i_ptr = Var x ==> var_below st.cs_next_var x)
        Wv {} E
        (compile_abi_decode_dyn_loop dst src_op load_opc base_op hi_op
           elem_info elem_abi_sz elem_mem_sz i_ptr cnt)
Proof
  cheat
QED

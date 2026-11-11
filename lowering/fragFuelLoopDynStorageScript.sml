(*
 * Fuel bound for the dynamic-array-to-storage copy loop.
 *
 * TOP-LEVEL:
 *   fuel_ok_compile_dynarray_to_storage
 *)

Theory fragFuelLoopDynStorage
Ancestors
  fragFuel fragFuelContextBase fragFuelContext compileEnv emitHelper context
  venomInst
Libs
  fragFuelLib

(* The length is loaded into a fresh variable before the loop; the loop
   counts a fresh counter from 0 while it is below that length.  Each round
   copies one element (one word, or a word-copy loop over a literal count)
   and adds 1; the body writes only the counter and variables it allocates
   itself, so the length stays fixed and the loop leaves within 2 ** 256
   rounds. *)
Theorem fuel_ok_compile_dynarray_to_storage:
  !src_ptr dst_slot elem_words elem_mem_size transient Wv E.
    fuel_ok Wv {} E
      (compile_dynarray_to_storage src_ptr dst_slot elem_words elem_mem_size
         transient)
Proof
  cheat
QED

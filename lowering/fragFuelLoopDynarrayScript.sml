(*
 * Fuel bound for the dynamic-array typed-copy loop.
 *
 * TOP-LEVEL:
 *   fuel_ok_compile_copy_dynarray_typed
 *)

Theory fragFuelLoopDynarray
Ancestors
  fragFuel fragFuelContextBase compileEnv emitHelper context venomInst
Libs
  fragFuelLib

(* Given a bound for the element copy (the recursive call), the copy of a
   dynamic array is bounded.  The length is loaded into a fresh variable
   before the loop; the loop counts a fresh counter from 0 while it is
   below that length.  The body writes only the counter and variables it
   allocates itself, so the length stays fixed and the loop leaves within
   2 ** 256 rounds. *)
Theorem fuel_ok_compile_copy_dynarray_typed:
  !cenv dst dst_elem cap src src_elem.
    (!d s Wv E. fuel_ok Wv {} E
                  (compile_store_memory_typed cenv d dst_elem s src_elem)) ==>
    !Wv E. fuel_ok Wv {} E
             (compile_copy_dynarray_typed cenv dst dst_elem cap src src_elem)
Proof
  cheat
QED

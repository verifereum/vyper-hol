(*
 * Fuel bound for the sparse storage store (compile_store_slots).
 *
 * TOP-LEVEL:
 *   fuel_ok_compile_store_slots
 *)

Theory fragFuelLoopDynStorage
Ancestors
  fragFuel fragFuelContextBase fragFuelContext compileEnv emitHelper context
Libs
  fragFuelLib

Theorem fuel_ok_compile_store_slots:
  !cenv src slot ty tr Wv E.
    fuel_ok Wv {} E (compile_store_slots cenv src slot ty tr)
Proof
  (* OPEN_ADMISSION: SEQ-4347 (held; proof by compile_store_slots_ind).
     Branch bot/opus/seq-3901-t16-dynstorage.
     Forced restatement: the sparse-store port replaced the flat
     compile_dynarray_to_storage loop with compile_store_slots, whose
     element loop calls compile_store_slots recursively. *)
  cheat
QED

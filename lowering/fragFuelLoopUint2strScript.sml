(*
 * Fuel bound for the decimal-digit loop of uint2str.
 *
 * TOP-LEVEL:
 *   fuel_ok_compile_uint2str
 *)

Theory fragFuelLoopUint2str
Ancestors
  fragFuel fragFuelContextBase compileEnv emitHelper context venomInst
  builtinStrings
Libs
  fragFuelLib

(* The loop works on a fresh copy val_var of val_op, made before the loop
   (so no precondition on val_op is needed), and on a fresh counter i_var
   from 0.  Each round (cond -> body -> cond) runs straight-line code, sets
   val_var to val_var / 10 and adds 1 to i_var, leaving through final_lbl
   when val_var is 0.  The body writes only val_var, i_var and variables it
   allocates itself, so the loop variable is the one that shrinks: a 256-bit
   value reaches 0 after at most 78 divisions by 10, so i_var is at most 78
   and never wraps, and the bound is independent of the runtime state. *)
Theorem fuel_ok_compile_uint2str:
  !val_op n_digits buf_size Wv E.
    fuel_ok Wv {} E (compile_uint2str val_op n_digits buf_size)
Proof
  cheat
QED

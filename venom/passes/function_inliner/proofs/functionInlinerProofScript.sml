(* Context-level correctness for allocation-free internal-call inlining. *)

Theory functionInlinerProof
Ancestors
  functionInlinerContract o1PassContract finite_map

(* The initial frame may contain arbitrary variables and memory. Generated
   names are fresh for the input code, and return-PC values are opaque.
   GETFMP/FMP_PARAM/RETFMP remain allowed: without an allocating or SETFMP
   instruction, calls preserve FMP and RETFMP adopts that unchanged value. *)
Theorem function_inliner_correct:
  !ctx s threshold D.
    inliner_input_ok ctx /\ s.vs_labels = FEMPTY /\ ~s.vs_halted ==>
    ctx_sim D ctx (function_inliner_ctx threshold ctx) s s
Proof
  cheat
QED

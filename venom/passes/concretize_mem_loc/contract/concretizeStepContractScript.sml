(*
 * ConcretizeMemLoc's step contract: the structural half of its O1 pass
 * contract.  The pass rewrites each ALLOCA to an ASSIGN of a literal
 * position (concretize_function_with_positions), sets fn_eom and
 * fn_mems_used, clears the forced positions, and keeps blocks, labels,
 * instruction ids and the supply; its label map is empty.
 *
 * TOP-LEVEL:
 *   concretize_step_contract
 *)

Theory concretizeStepContract
Ancestors
  o1PassContract concretizeMemLocCorrectness concretizeMemLocDefs
  venomPassDispatcher

(* Intuition: concretize_function_fuel_in_context either returns fn itself
   (a function with a static layout and no ALLOCA) or
   apply_context_concretize_layout ctx layout fn.  The latter maps each
   instruction through concretize_inst_with_positions, which keeps the
   opcode except ALLOCA -> ASSIGN [Lit pos] with the same outputs and
   inst_id, and only touches metadata fields (fn_eom, fn_mems_used,
   fn_forced_alloc_positions).  So labels, block structure, terminators,
   INVOKE operands and PHIs are unchanged; fresh_names_ok holds because
   labels and ids are those of fn; the label map is []. *)
Theorem concretize_step_contract:
  o1_step_contract rpolicy (CFP_Simple VP_ConcretizeMemLoc)
Proof
  cheat
QED

(*
 * ConcretizeMemLoc's step contract: the structural half of its O1 pass
 * contract, at its walk position (run 2).
 *
 * TOP-LEVEL:
 *   concretize_step_contract_at
 *)
Theory concretizeStepContract
Ancestors
  o1PassContract concretizeMemLocDefs venomPassDispatcher

(* Why it holds (intuition, not a prescribed proof).

   concretize_function_fuel_in_context either returns fn itself (a
   function with a static layout and no ALLOCA) or
   apply_context_concretize_layout ctx layout fn, which maps each
   instruction through concretize_inst_with_positions: ALLOCA becomes
   ASSIGN [Lit pos] with the same outputs and inst_id, every other
   instruction is kept, and only metadata (fn_eom, fn_mems_used,
   fn_forced_alloc_positions) changes.  So labels, blocks, terminators,
   INVOKE operands, PHIs and each CALL's success check (call_checks_ok)
   are unchanged; fresh_names_ok holds because labels and ids are fn's;
   the label map is []; and the output has no ALLOCA (row 3). *)
Theorem concretize_step_contract_at:
  o1_step_contract_at 2 rpolicy (CFP_Simple VP_ConcretizeMemLoc)
Proof
  cheat
QED

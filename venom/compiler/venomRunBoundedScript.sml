(* The Venom run's resource bound, for the sufficient-gas theorems: the
 * stages S6b (run_venom_pipeline_run_bounded) produce it and S7g
 * (codegen_gas_sufficient) consumes it.
 *
 * TOP-LEVEL:
 *   venom_run_bounded  - the run ends within fuel, its memory below a bound
 *)
Theory venomRunBounded
Ancestors
  unitMemInv passSimulationDefs contextCodegenRel

(* Resource bound codegen's gas proof consumes: the run ends within fuel,
   and every access is below M or part of a revert forwarding.  The stages
   give fuel and M independent of the external-call outcomes. *)
Definition venom_run_bounded_def:
  venom_run_bounded fuel M ctx vs <=>
    terminates (run_context fuel ctx vs) /\
    mem_inv (\ctx fn inst s.
               in_revert_forward fn s \/
               EVERY (\(off,len). len = 0 \/ off + len <= M)
                 (inst_mem_ranges inst s)) ctx vs
End

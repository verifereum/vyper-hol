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

(* Every CREATE or CREATE2 the run reaches has an initcode within the
   EIP-3860 limit; the EVM answers a longer one with OutOfGas at any gas.
   S7g takes it as mem_inv (\ctx fn inst s. inst_create_size_ok inst s). *)
Definition inst_create_size_ok_def:
  inst_create_size_ok inst s <=>
    !v off sz salt sz_w.
      ((inst.inst_opcode = CREATE /\ inst.inst_operands = [v; off; sz]) \/
       (inst.inst_opcode = CREATE2 /\ inst.inst_operands = [v; off; sz; salt])) /\
      eval_operand sz s = SOME sz_w ==>
      w2n sz_w <= 2 * max_code_size
End

(* Opcode-specific ownership permits repeated writers of other registers. *)
Theory bodyPtrStructLitAllocationOwnership
Ancestors loweringShapeDefs compileEnv list

Theorem opaque_writer_unique_snoc:
  (!i x. MEM i insts /\ MEM x i.inst_outputs ==> not_fresh_at st x) /\
  (!i j x. MEM i insts /\ MEM j insts /\ i.inst_opcode = opc /\
           MEM x i.inst_outputs /\ MEM x j.inst_outputs ==> i = j) /\
  (inst.inst_opcode = opc ==>
     !x. MEM x inst.inst_outputs ==> ~not_fresh_at st x) /\
  (!x. MEM x inst.inst_outputs /\ not_fresh_at st x ==>
       ~opaque_out opc insts x) ==>
  !i j x. MEM i (insts ++ [inst]) /\ MEM j (insts ++ [inst]) /\
          i.inst_opcode = opc /\
          MEM x i.inst_outputs /\ MEM x j.inst_outputs ==> i = j
Proof
  rw[] >> gvs[] >> metis_tac[opaque_out_def]
QED

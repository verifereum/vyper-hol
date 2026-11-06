Theory bodyPtrStructLitCompilerOwnership
Ancestors bodyPtrStructLitAllocationOwnership loweringShapeRules
  loweringShapeDefs compileEnv venomInst list

(* The immutable shape interface singles out RETPC_PARAM. These predicates
   add the distinct ALLOCA ownership class without imposing SSA on counters. *)
Definition alloc_owned_def:
  alloc_owned st x <=> opaque_out ALLOCA (state_insts st) x
End

Definition alloc_writers_unique_def:
  alloc_writers_unique st <=>
    !i j x. MEM i (state_insts st) /\ MEM j (state_insts st) /\
            i.inst_opcode = ALLOCA /\ MEM x i.inst_outputs /\
            MEM x j.inst_outputs ==> i = j
End

Definition alloc_mutable_def:
  alloc_mutable st op <=> plain_operand st op /\
    !x. op = Var x ==> ~alloc_owned st x
End

Theorem alloc_writers_unique_emit_op:
  shape_base_state st /\ alloc_writers_unique st /\
  emit_op opc ops st = (v,st') ==> alloc_writers_unique st'
Proof
  rpt strip_tac >> drule emit_op_facts >> strip_tac >>
  fs[alloc_writers_unique_def, shape_base_state_def] >>
  rw[] >> gvs[mk_inst_def] >> metis_tac[]
QED

Theorem alloc_writers_unique_emit_inst:
  alloc_writers_unique st /\ opc <> ALLOCA /\
  EVERY (\x. ~opaque_out ALLOCA (state_insts st) x) outs /\
  emit_inst opc ops outs st = (u,st') ==> alloc_writers_unique st'
Proof
  rw[emit_inst_eq] >>
  gvs[alloc_writers_unique_def, state_insts_def, all_blocks_def,
      opaque_out_def, mk_inst_def, EVERY_MEM] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem alloc_writers_unique_emit_void:
  alloc_writers_unique st /\ emit_void opc ops st = (u,st') ==>
  alloc_writers_unique st'
Proof
  rw[emit_void_eq] >>
  gvs[alloc_writers_unique_def, state_insts_def, all_blocks_def,
      mk_inst_def] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem emit_op_nonalloc_output:
  shape_base_state st /\ emit_op opc ops st = (v,st') /\
  opc <> ALLOCA ==> !x. v = Var x ==>
    ~opaque_out ALLOCA (state_insts st') x
Proof
  rpt strip_tac >> drule emit_op_facts >> strip_tac >>
  gvs[opaque_out_def, mk_inst_def] >>
  fs[shape_base_state_def] >> metis_tac[]
QED

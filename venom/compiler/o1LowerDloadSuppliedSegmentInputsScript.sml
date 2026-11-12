Theory o1LowerDloadSuppliedSegmentInputs
Ancestors
  o1LowerDloadPtrDiscipline o1LowerDloadJointScalar o1LowerDloadJointRelation o1LowerDloadOccurrence
  o1LowerDloadGhost o1LowerDloadOpaque o1LowerDloadJointAssign
  ptrDiscipline pointerConfinedDefs memLocDefs unitShapeDefs o1PassContract
  venomInst finite_map list pred_set irSupply venomExecSemantics contextCodegenRel

Theorem ld_data_load_inputs_untainted:
  taint_ok fn tn inst s /\ MEM inst.inst_opcode [DLOAD;DLOADBYTES] ==>
  !op. MEM op inst.inst_operands ==> op_taint tn op = {}
Proof
  strip_tac >> gvs[taint_ok_def] >> metis_tac[]
QED

Theorem ld_joint_dload_inputs_clean:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\ inst.inst_opcode = DLOAD ==>
  !op. MEM op inst.inst_operands ==>
    op_prov H op = NONE /\ op_taint tn op = {} /\
    eval_operand op s = eval_operand op t
Proof
  strip_tac >> drule ld_joint_scalar_operands_clean >>
  gvs[is_pointer_preserving_op_def, mem_read_ops_def,
      mem_write_ops_def, retpc_use_ok_def] >>
  metis_tac[ld_data_load_inputs_untainted, MEM]
QED

Theorem ld_joint_dloadbytes_inputs_clean:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  inst.inst_opcode = DLOADBYTES /\ inst.inst_operands = [dst;src;sz] ==>
  !op. MEM op [src;sz] ==>
    op_prov H op = NONE /\ op_taint tn op = {} /\
    eval_operand op s = eval_operand op t
Proof
  (* P4a in progress *) cheat
QED

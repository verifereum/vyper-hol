Theory concretizePtrMcopyArchitectureProbe
Ancestors concretizePtrCopyContent concretizePtrValueTransport
  concretizePtrWriteClassification concretizePtrChronologicalHistory
  venomExecSemantics venomInst ptrDiscipline finite_map words

(* Syntax/type probe only: this term is NOT asserted as a theorem.
   Proposed next semantic boundary: backwards definedness, not byte agreement. *)
val _ = ``
  !(births:((num # num),num # num) fmap)
   (positions:(allocation,num # num) fmap)
   (TG:(string,num # num) fmap) (tn:taint)
   (s:venom_state) (t:venom_state) (inst:instruction)
   (dop:operand) (sop:operand) (nop:operand)
   (dt:bytes32) (rt:bytes32) (nt:bytes32) (fuel:num) (ctx:venom_context).
    inst.inst_opcode = MCOPY /\ inst.inst_operands = [dop;sop;nop] /\
    ptr_vars_transport births positions TG tn s t /\ s.vs_labels = t.vs_labels /\
    eval_operand dop t = SOME dt /\ eval_operand sop t = SOME rt /\
    eval_operand nop t = SOME nt ==>
    ?(d:bytes32) (r:bytes32) (n:bytes32).
      eval_operand dop s = SOME d /\ eval_operand sop s = SOME r /\
      eval_operand nop s = SOME n /\
      ptr_value_transport births positions (op_prov TG dop) (op_taint tn dop) d dt /\
      ptr_value_transport births positions (op_prov TG sop) (op_taint tn sop) r rt /\
      ptr_value_transport births positions (op_prov TG nop) (op_taint tn nop) n nt /\
      step_inst fuel ctx inst s = OK (mcopy (w2n d) (w2n r) (w2n n) s)
``;

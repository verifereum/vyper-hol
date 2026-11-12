Theory o1LowerDloadRepeatedNext
Ancestors
  o1LowerDloadJointAssign o1LowerDloadJointAllocation
  o1LowerDloadJointRelation o1LowerDloadOccurrence o1LowerDloadPairedAllocation
  o1LowerDloadEnvironment o1LowerDloadShared o1LowerDloadRelocationKernel
  ptrDiscipline venomExecSemantics venomState codegenRel contextCodegenRel
  finite_map words list pred_set arithmetic o1PassContract venomInst

Theorem ld_alloca_repeated_annotations[local]:
  occurrence_annotation_ok fl n a U B HP H stk PG G s /\
  inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [out] /\
  inst.inst_operands = [Lit amount] /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,z) ==>
  occurrence_sites_step a B inst (update_var out (n2w b) s) = B /\
  occurrence_step a HP H inst (update_var out (n2w b) s) =
    H |+ (out,(a,inst.inst_id)) /\
  step_taint inst s (update_var out (n2w b) s) tn =
    tn with t_var := tn.t_var |+ (out,{})
Proof
  (* P4a in progress *) cheat
QED

Theorem ld_joint_alloca_repeated_next:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\
  active_inst fn inst s /\ inst.inst_opcode = ALLOCA /\
  inst.inst_operands = [Lit amount] /\ inst.inst_outputs = [out] /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,z) /\
  step_inst fuel C inst s = OK s1 /\
  active_inst fn inst2 (s1 with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?t1 u fn'. step_inst fuel C' inst t = OK t1 /\
    lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    ld_joint_control u fn fn' s t /\ active_inst fn' inst t /\
    ld_joint_boundary vs C C' lo D stk PG (step_prov PG G inst s1)
      (step_taint inst s s1 tn) fn inst2
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx)
      n a U B HP (occurrence_step a HP H inst s1) sites X ts
Proof
  (* P4a in progress *) cheat
QED

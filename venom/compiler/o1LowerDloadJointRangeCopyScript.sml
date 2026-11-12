(* Relocated address ranges for ordinary copy instructions. *)
Theory o1LowerDloadJointRangeCopy
Ancestors
  o1LowerDloadPtrDiscipline o1LowerDloadRangeTransport o1LowerDloadJointMemoryWrite
  o1LowerDloadJointRelation o1LowerDloadOccurrence o1LowerDloadJointScalar
  o1LowerDloadEnvironment o1LowerDloadRelocationKernel
  o1LowerDloadAddressArithmetic ptrDiscipline venomState words finite_map
  pred_set list o1PassContract contextCodegenRel venomInst
  pointerConfinedDefs memLocDefs o1LowerDloadOpaque unitShapeDefs codegenRel venomExecSemantics venomWf

Theorem ld_joint_operand_range:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  MEM op inst.inst_operands /\ (!v. ~retpc_use_ok inst v) /\
  op_taint tn op = {} /\ eval_operand op s = SOME x /\
  (len <> 0 /\ (lo < w2n x+len \/ op_prov G op <> NONE) ==>
   ?v b z. op = Var v /\ FLOOKUP G v = SOME (b,z) /\
     b<=w2n x /\ w2n x+len<=b+z) ==>
  ?y. eval_operand op t = SOME y /\
    (len=0 \/ (w2n x=w2n y /\ (w2n x+len<=lo \/
       dyn_floor C vs<=w2n x /\ w2n x+len<=dimword (:256))) \/
     (?id b c z j. FLOOKUP sites id = SOME (b,c,z) /\ j+len<=z /\
                    w2n x=b+j /\ w2n y=c+j))
Proof
  (* P4a in progress *) cheat
QED

Theorem ld_joint_write_operand_range:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  mem_write_ops inst = SOME ops /\ ops.iao_ofst = op /\
  MEM op inst.inst_operands /\ (!v. ~retpc_use_ok inst v) /\
  op_taint tn op = {} /\ eval_operand op s = SOME x /\
  MEM (w2n x,len) (source_memory_write_ranges inst s) ==>
  ?y. eval_operand op t = SOME y /\
    (len=0 \/ (w2n x=w2n y /\ (w2n x+len<=lo \/
       dyn_floor C vs<=w2n x /\ w2n x+len<=dimword (:256))) \/
     (?id b c z j. FLOOKUP sites id = SOME (b,c,z) /\ j+len<=z /\
                    w2n x=b+j /\ w2n y=c+j))
Proof
  (* P4a in progress *) cheat
QED

Theorem ld_joint_read_operand_range:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  mem_read_ops inst = SOME ops /\ ops.iao_ofst = op /\
  MEM op inst.inst_operands /\ (!v. ~retpc_use_ok inst v) /\
  op_taint tn op = {} /\ eval_operand op s = SOME x /\
  MEM (w2n x,len) (source_memory_read_ranges inst s) ==>
  ?y. eval_operand op t = SOME y /\
    (len=0 \/ (w2n x=w2n y /\ (w2n x+len<=lo \/
       dyn_floor C vs<=w2n x /\ w2n x+len<=dimword (:256))) \/
     (?id b c z j. FLOOKUP sites id = SOME (b,c,z) /\ j+len<=z /\
                    w2n x=b+j /\ w2n y=c+j))
Proof
  (* P4a in progress *) cheat
QED

Theorem ld_joint_copy_scalar_operand:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  (inst.inst_opcode = MCOPY \/ inst.inst_opcode = CALLDATACOPY \/
   inst.inst_opcode = CODECOPY \/ inst.inst_opcode = RETURNDATACOPY) /\
  inst.inst_operands = [dst;src;sz] /\
  (op = sz \/ (inst.inst_opcode <> MCOPY /\ op = src)) ==>
  eval_operand op s = eval_operand op t
Proof
  (* P4a in progress *) cheat
QED

Theorem ld_joint_mcopy_operands:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  inst.inst_opcode = MCOPY /\ inst.inst_operands = [dst;src;sz] /\
  eval_operand dst s = SOME d /\ eval_operand src s = SOME r /\
  eval_operand sz s = SOME l ==>
  ?d' r'. eval_operand dst t = SOME d' /\ eval_operand src t = SOME r' /\
    eval_operand sz t = SOME l /\
    (w2n l=0 \/ (w2n d=w2n d' /\ (w2n d+w2n l<=lo \/
       dyn_floor C vs<=w2n d /\ w2n d+w2n l<=dimword (:256))) \/
     (?id b c z j. FLOOKUP sites id = SOME (b,c,z) /\ j+w2n l<=z /\
                    w2n d=b+j /\ w2n d'=c+j)) /\
    (w2n l=0 \/ (w2n r=w2n r' /\ (w2n r+w2n l<=lo \/
       dyn_floor C vs<=w2n r /\ w2n r+w2n l<=dimword (:256))) \/
     (?id b c z j. FLOOKUP sites id = SOME (b,c,z) /\ j+w2n l<=z /\
                    w2n r=b+j /\ w2n r'=c+j))
Proof
  (* P4a in progress *) cheat
QED

Theorem ld_mem_taint_mcopy:
  inst.inst_opcode = MCOPY /\ inst.inst_operands = [dst;src;sz] /\
  eval_operand dst s = SOME d /\ eval_operand src s = SOME r /\
  eval_operand sz s = SOME l ==>
  mem_taint tn inst s (mcopy (w2n d) (w2n r) (w2n l) s) =
    ((tn.t_mem DIFF {i | w2n d<=i /\ i<w2n d+w2n l}) UNION
     {w2n d+k | k<w2n l /\ w2n r+k IN tn.t_mem})
Proof
  strip_tac >>
  simp[mem_taint_def, step_writes_def, source_memory_write_ranges_def,
       sized_source_write_range_def, written_taint_def,
       new_site_bytes_def, mcopy_def, write_memory_with_expansion_def,
       range_bytes_def] >>
  simp[EXTENSION, FLOOKUP_DEF] >> metis_tac[]
QED

Theorem ld_joint_mcopy_step:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  inst.inst_opcode = MCOPY /\ step_inst fuel C inst s = OK s1 ==>
  ?t1. step_inst fuel C' inst t = OK t1 /\
    ld_memory_agree sites lo (mem_taint tn inst s s1)
      s1.vs_memory t1.vs_memory /\
    ld_dyn_agree (dyn_floor C vs) (mem_taint tn inst s s1)
      s1.vs_memory t1.vs_memory
Proof
  (* P4a in progress *) cheat
QED

Theorem ld_joint_mcopy_next:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\
  ptr_discipline lo C vs /\ opaque_use_ok fn /\
  active_inst fn inst s /\ inst.inst_opcode = MCOPY /\ ~in_revert_forward fn s /\
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

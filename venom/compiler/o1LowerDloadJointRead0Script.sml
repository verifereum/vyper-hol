(* Equal-observation read0 operations preserve the whole joint boundary. *)
Theory o1LowerDloadJointRead0
Ancestors
  o1LowerDloadJointScalar o1LowerDloadJointAssign o1LowerDloadJointRelation
  o1LowerDloadShared o1LowerDloadOccurrence o1LowerDloadEnvironment
  ptrDiscipline venomExecSemantics venomState venomInst o1PassContract
  list finite_map vfmState

Theorem ld_out_taint_default:
  ~MEM inst.inst_opcode [MLOAD; ILOAD; SLOAD; TLOAD; ASSIGN; SHL; SHR; SAR; MUL] ==>
  out_taint tn inst s = {}
Proof
  strip_tac >> simp[out_taint_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> gvs[])
QED

Theorem ld_joint_read0_step:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\
  MEM inst.inst_opcode
    [CALLER; ADDRESS; CALLVALUE; ORIGIN; GASPRICE; CHAINID;
     COINBASE; TIMESTAMP; NUMBER; PREVRANDAO; GASLIMIT; BASEFEE;
     BLOBBASEFEE; CALLDATASIZE; CODESIZE; RETURNDATASIZE; SELFBALANCE] /\
  step_inst fuel C inst s = OK s1 ==>
  ?out x. inst.inst_outputs = [out] /\ s1 = update_var out x s /\
    step_inst fuel C' inst t = OK (update_var out x t) /\
    ld_env_agree sites fn (occurrence_step a HP H inst s1)
      (step_taint inst s s1 tn) s1 (update_var out x t)
Proof
  (* P4a in progress *) cheat
QED

Theorem ld_joint_read0_next:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\
  active_inst fn inst s /\
  MEM inst.inst_opcode
    [CALLER; ADDRESS; CALLVALUE; ORIGIN; GASPRICE; CHAINID;
     COINBASE; TIMESTAMP; NUMBER; PREVRANDAO; GASLIMIT; BASEFEE;
     BLOBBASEFEE; CALLDATASIZE; CODESIZE; RETURNDATASIZE; SELFBALANCE] /\
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

Theorem ld_joint_gas_step:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ inst.inst_opcode = GAS /\
  step_inst fuel C inst s = OK s1 ==>
  ?out x rs. inst.inst_outputs = [out] /\
    s1 = update_var out x (s with vs_gas_readings := rs) /\
    step_inst fuel C' inst t = OK (update_var out x (t with vs_gas_readings := rs)) /\
    ld_env_agree sites fn (occurrence_step a HP H inst s1)
      (step_taint inst s s1 tn) s1 (update_var out x (t with vs_gas_readings := rs))
Proof
  (* P4a in progress *) cheat
QED

Theorem ld_joint_gas_next:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\
  active_inst fn inst s /\ inst.inst_opcode = GAS /\
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

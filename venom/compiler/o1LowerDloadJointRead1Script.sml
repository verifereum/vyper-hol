(* Environmental read1 observations ignore storage differences. *)
Theory o1LowerDloadJointRead1
Ancestors
  o1LowerDloadJointRead0 o1LowerDloadJointScalar o1LowerDloadJointAssign
  o1LowerDloadShared o1LowerDloadJointRelation o1LowerDloadOccurrence
  o1LowerDloadEnvironment ptrDiscipline venomExecSemantics venomState
  venomInst o1PassContract list finite_map vfmState pointerConfinedDefs
  memLocDefs unitShapeDefs

Theorem ld_shared_account_observations:
  ld_shared_agree D A tn s t ==>
  !addr. (lookup_account addr s.vs_accounts).balance =
           (lookup_account addr t.vs_accounts).balance /\
         (lookup_account addr s.vs_accounts).code =
           (lookup_account addr t.vs_accounts).code /\
         account_empty (lookup_account addr s.vs_accounts) =
           account_empty (lookup_account addr t.vs_accounts)
Proof
  strip_tac >> drule ld_shared_accounts_fields >> strip_tac >> gen_tac >>
  `s.vs_accounts addr with storage := (t.vs_accounts addr).storage =
   t.vs_accounts addr` by simp[] >>
  qpat_x_assum `!a. _` kall_tac >>
  qpat_x_assum `ld_shared_agree _ _ _ _ _` kall_tac >>
  simp[lookup_account_def] >>
  qsuff_tac
    `(s.vs_accounts addr with storage := (t.vs_accounts addr).storage).balance =
       (t.vs_accounts addr).balance /\
     (s.vs_accounts addr with storage := (t.vs_accounts addr).storage).code =
       (t.vs_accounts addr).code /\
     account_empty (s.vs_accounts addr with storage := (t.vs_accounts addr).storage) =
       account_empty (t.vs_accounts addr)`
  >- simp[account_empty_def] >>
  rpt conj_tac >> AP_TERM_TAC >> simp[]
QED

Theorem ld_joint_read1_operands_clean:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  MEM inst.inst_opcode
    [BLOCKHASH; BLOBHASH; BALANCE; EXTCODESIZE; EXTCODEHASH; CALLDATALOAD] ==>
  !op. MEM op inst.inst_operands ==>
    op_prov H op = NONE /\ op_taint tn op = {} /\
    eval_operand op s = eval_operand op t
Proof
  strip_tac >> drule ld_joint_scalar_operands_clean >>
  gvs[MEM, is_pointer_preserving_op_def, mem_read_ops_def,
      mem_write_ops_def, retpc_use_ok_def, taint_ok_def] >> metis_tac[]
QED

Theorem ld_joint_read1_step:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  MEM inst.inst_opcode
    [BLOCKHASH; BLOBHASH; BALANCE; EXTCODESIZE; EXTCODEHASH; CALLDATALOAD] /\
  step_inst fuel C inst s = OK s1 ==>
  ?out x. inst.inst_outputs = [out] /\ s1 = update_var out x s /\
    step_inst fuel C' inst t = OK (update_var out x t) /\
    ld_env_agree sites fn (occurrence_step a HP H inst s1)
      (step_taint inst s s1 tn) s1 (update_var out x t)
Proof
  (* P4a in progress *) cheat
QED

Theorem ld_joint_read1_next:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\
  ptr_discipline lo C vs /\ opaque_use_ok fn /\ active_inst fn inst s /\
  MEM inst.inst_opcode
    [BLOCKHASH; BLOBHASH; BALANCE; EXTCODESIZE; EXTCODEHASH; CALLDATALOAD] /\
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

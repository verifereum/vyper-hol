Theory concretizeLayoutLocalSelfdestruct
Ancestors concretizeLayoutLocalAssertions concretizeLayoutLocalBalanceReaders
  concretizeLayoutLocalTerminals frameRelocationLocal frameRelocationEnvironment
  frameResolvedTrace frameRelocationReachableSupport frameRelocationCleanOperands
  frameRelocationGuardedValues
  concretizeLayoutOperandCleanliness pointerConfinedDefs memLocDefs ptrDiscipline
  venomExecSemantics venomState vfmState finite_map list

Theorem selfdestruct_operands:
  ptr_discipline lo C vs0 /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  frame_reachable vs0 C stk PG G tn fn inst s /\
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    (birth::ids) ((rp,rv)::anns) /\
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = SELFDESTRUCT /\ relocation_env s t /\
  local_rel (\u. F)
    (guarded_ptr (retpc_var fn)
      (activation_lookup (0:num) (concretize_positions C')
        (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) rv)
    (guarded_bytes (retpc_var fn) rv tn) R Obs s t ==>
  !op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t
Proof
  strip_tac >>
  `taint_ok fn tn inst s` by (fs[ptr_discipline_def] >> metis_tac[]) >>
  `!u. FLOOKUP rv u <> NONE ==> u IN fn_pv P fn` by
    (drule resolved_config_current >> simp[] >> strip_tac >>
     rpt strip_tac >> irule reachable_resolved_support >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> metis_tac[]) >>
  `!w. MEM (Var w) inst.inst_operands ==> clean_scalar (retpc_var fn) rv tn w` by
    (rpt strip_tac >>
     `~is_pointer_preserving_op inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
      ~MEM inst.inst_opcode [EQ; LT; GT; ASSIGN; PHI; RET; SHL; SHR; SAR; MSTORE; SSTORE; TSTORE; ISTORE] /\
      mem_write_ops inst = NONE /\ mem_read_ops inst = NONE` by
       simp[is_pointer_preserving_op_def, mem_write_ops_def, mem_read_ops_def] >>
     drule_all nonpointer_operand_clean >> simp[]) >>
  rpt strip_tac >>
  drule_at (Pat `local_rel _ _ _ _ _ _ _`) guarded_scalar_operand >>
  disch_then (qspec_then `op` mp_tac) >>
  gvs[relocation_env_def] >> metis_tac[]
QED

Theorem accounts_agree_except_selfdestruct:
  accounts_agree_except D a b ==>
  accounts_agree_except D
    (\x. if x = self then (lookup_account self a) with balance := 0
         else if x = ben then (lookup_account ben a) with
           balance := (lookup_account self a).balance + (lookup_account ben a).balance
         else a x)
    (\x. if x = self then (lookup_account self b) with balance := 0
         else if x = ben then (lookup_account ben b) with
           balance := (lookup_account self b).balance + (lookup_account ben b).balance
         else b x)
Proof
  strip_tac >>
  `!x. (lookup_account x a).balance = (lookup_account x b).balance` by
    metis_tac[accounts_agree_except_balance] >>
  fs[accounts_agree_except_def, lookup_account_def] >> gen_tac >>
  Cases_on `x = self` >- (gvs[] >> metis_tac[]) >>
  Cases_on `x = ben` >> gvs[] >> metis_tac[]
QED

Theorem selfdestruct_abort_execution[local]:
  inst.inst_opcode = SELFDESTRUCT /\ relocation_env s t /\ variable_domains s t /\
  (!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t) /\
  step_inst_base inst s = Abort a post ==>
  ?post'. step_inst_base inst t = Abort a post' /\
    dead_result_rel D (Abort a post) (Abort a post')
Proof
  strip_tac >>
  `IS_SOME (eval_operands inst.inst_operands s) = IS_SOME (eval_operands inst.inst_operands t)` by
    (irule eval_operands_domain_agreement >> fs[relocation_env_def]) >>
  qpat_x_assum `step_inst_base inst s = Abort a post` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[venomInstTheory.opcode_case_def] >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[venomInstTheory.opcode_case_def] >>
  gvs[relocation_env_def, dead_result_rel_def] >>
  simp[AllCaseEqs()] >> metis_tac[MEM]
QED

Theorem selfdestruct_halt_execution[local]:
  inst.inst_opcode = SELFDESTRUCT /\ relocation_env s t /\ variable_domains s t /\
  (!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t) /\
  dead_result_rel D (Halt s) (Halt t) /\
  step_inst_base inst s = Halt post ==>
  ?post'. step_inst_base inst t = Halt post' /\
    dead_result_rel D (Halt post) (Halt post')
Proof
  strip_tac >>
  `IS_SOME (eval_operands inst.inst_operands s) = IS_SOME (eval_operands inst.inst_operands t)` by
    (irule eval_operands_domain_agreement >> fs[relocation_env_def]) >>
  qpat_x_assum `step_inst_base inst s = Halt post` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[venomInstTheory.opcode_case_def] >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[venomInstTheory.opcode_case_def] >>
  gvs[relocation_env_def] >>
  `eval_operand addr_op t = SOME addr` by metis_tac[] >>
  qpat_x_assum `eval_operand addr_op t = SOME addr` SUBST1_TAC >>
  simp[NoAsms] >>
  fs[dead_result_rel_def, halt_state_def, set_returndata_def] >>
  irule accounts_agree_except_selfdestruct >> simp[]
QED

Theorem concretize_selfdestruct_abort_complete:
  ptr_discipline lo C vs0 /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  frame_reachable vs0 C stk PG G tn fn inst s /\
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    (birth::ids) ((rp,rv)::anns) /\
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = SELFDESTRUCT /\ relocation_env s t /\
  local_rel (\u. F)
    (guarded_ptr (retpc_var fn)
      (activation_lookup (0:num) (concretize_positions C')
        (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) rv)
    (guarded_bytes (retpc_var fn) rv tn) R Obs s t /\
  step_inst_base inst s = Abort a post ==>
  ?post'. step_inst_base inst t = Abort a post' /\
    dead_result_rel D (Abort a post) (Abort a post')
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t` by
    (rpt strip_tac >> drule_all selfdestruct_operands >> simp[]) >>
  `variable_domains s t` by fs[local_rel_def] >>
  drule_all selfdestruct_abort_execution >> simp[]
QED

Theorem concretize_selfdestruct_complete:
  ptr_discipline lo C vs0 /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  frame_reachable vs0 C stk PG G tn fn inst s /\
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    (birth::ids) ((rp,rv)::anns) /\
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = SELFDESTRUCT /\ relocation_env s t /\
  local_rel (\u. F)
    (guarded_ptr (retpc_var fn)
      (activation_lookup (0:num) (concretize_positions C')
        (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) rv)
    (guarded_bytes (retpc_var fn) rv tn) R
    (\s t. dead_result_rel D (Halt s) (Halt t)) s t /\
  step_inst_base inst s = Halt post ==>
  ?post'. step_inst_base inst t = Halt post' /\
    dead_result_rel D (Halt post) (Halt post')
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t` by
    (rpt strip_tac >> drule_all selfdestruct_operands >> simp[]) >>
  `variable_domains s t /\ dead_result_rel D (Halt s) (Halt t)` by fs[local_rel_def] >>
  drule_all selfdestruct_halt_execution >> simp[]
QED

val _ = if null (hyp concretize_selfdestruct_complete) andalso
           null (hyp concretize_selfdestruct_abort_complete)
        then () else raise Fail "SELFDESTRUCT exports have hypotheses";

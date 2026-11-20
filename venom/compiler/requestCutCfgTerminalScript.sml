Theory requestCutCfgTerminal
Ancestors
  requestCutAssertCursor o1ContractCfgNormJointCursors frameJointTransition
  venomStepProps venomExecSemantics venomInst venomState list

(* The stopped selection reports a primitive C8 result before its root
   normalization. The selected C9 cursor has the same terminal kind. *)
Theorem request_cut_cfg_terminal_step:
  cfg_norm_joint_cursors C8 C9 (schedules,(rounds,cells),saved)
    (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 h8)
    (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 h9) /\
  inst8.inst_opcode <> INVOKE /\
  step_inst fuel C8 inst8 s8 = r /\
  ((?u. r = OK u /\ u.vs_halted) \/ (?u. r = Halt u) \/ (?a u. r = Abort a u)) ==>
  inst9 = inst8 /\
  ?post. step_inst 0 C9 inst9 s9 = Halt post \/
         ?a. step_inst 0 C9 inst9 s9 = Abort a post
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule cfg_norm_joint_source_running >> strip_tac >>
  qpat_x_assum `(?u. r = OK u /\ _) \/ _` strip_assume_tac
  >- metis_tac[step_inst_ok_halted]
  >- (gvs[] >> drule_all cfg_norm_joint_primitive_halt >> metis_tac[]) >>
  gvs[] >> Cases_on `MEM inst8.inst_opcode [ASSERT; ASSERT_UNREACHABLE]`
  >- (drule_all cfg_norm_joint_assert_abort >> metis_tac[]) >>
  drule_all cfg_norm_joint_primitive_abort >> metis_tac[]
QED

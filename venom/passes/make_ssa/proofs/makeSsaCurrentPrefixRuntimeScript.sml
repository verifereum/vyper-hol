Theory makeSsaCurrentPrefixRuntime
Ancestors
  o1FrameLockstep venomExecSemantics stateFrame venomState venomWf venomInst alist cfgNormBase simplifyCfgRetpc
Theorem current_prefix_assign_success:
  inst.inst_opcode = ASSIGN /\ inst.inst_outputs = [dst] /\
  inst.inst_operands = [op] /\ eval_operand op st = SOME v ==>
  step_inst fuel C inst st = OK (update_var dst v st)
Proof
  strip_tac >> simp[step_inst_non_invoke, step_inst_base_def]
QED

Theorem current_prefix_assign_frame:
  execution_frame (update_var dst v st) = execution_frame st
Proof
  simp[update_var_def, execution_frame_def]
QED

Theorem current_prefix_var_copy_success:
  inst.inst_opcode = ASSIGN /\ inst.inst_outputs = [dst] /\
  inst.inst_operands = [Var src] /\ IS_SOME (lookup_var src st) ==>
  ?v. lookup_var src st = SOME v /\
    step_inst fuel C inst st = OK (update_var dst v st) /\
    execution_frame (update_var dst v st) = execution_frame st
Proof
  strip_tac >> Cases_on `lookup_var src st` >> fs[] >>
  conj_tac
  >- (irule current_prefix_assign_success >> simp[eval_operand_def]) >>
  simp[update_var_def]
QED

Theorem current_prefix_selected_copy_success:
  phi_well_formed ops /\ ALL_DISTINCT (MAP FST (phi_pairs ops)) /\
  MEM (p,v) (phi_pairs ops) /\
  state_rel sg st st' /\ FLOOKUP sg src = SOME v /\
  lookup_var v st = SOME value /\
  inst.inst_opcode = ASSIGN /\ inst.inst_outputs = [dst] /\
  inst.inst_operands = [Var src] ==>
  resolve_phi p ops = SOME (Var v) /\
  step_inst fuel C inst st' = OK (update_var dst value st') /\
  execution_frame (update_var dst value st') = execution_frame st'
Proof
  strip_tac >>
  `lookup_var src st' = SOME value` by (fs[state_rel_def, vars_rel_def] >> metis_tac[]) >>
  conj_tac >- metis_tac[retpc_phi_pair_selected] >>
  conj_tac
  >- (irule current_prefix_assign_success >> simp[eval_operand_def]) >>
  simp[update_var_def]
QED

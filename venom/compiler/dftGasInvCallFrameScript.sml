Theory dftGasInvCallFrame
Ancestors
  dftGasOracleDefs dftCommutation dftIndexedExec venomExecSemantics
  venomInst venomState list instIdxIndep

Theorem inv_ev_invoke_frame:
  (!y. MEM (Var y) inst.inst_operands ==> x <> y) /\
  ~MEM x inst.inst_outputs /\ inst.inst_opcode = INVOKE ==>
  ev_step orc p d fuel ctx inst (update_var x v s) =
  (case ev_step orc p d fuel ctx inst s of
     OK t => OK (update_var x v t)
   | Halt t => Halt t
   | Abort a t => Abort a t
   | IntRet vals t => IntRet vals t
   | Error e => Error e)
Proof
  rpt strip_tac >> simp[ev_step_def] >>
  BasicProvers.TOP_CASE_TAC >> simp[] >>
  rename1 `decode_invoke inst = SOME pair` >>
  PairCases_on `pair` >> simp[] >>
  `inst.inst_operands = Label pair0 :: pair1`
    by (gvs[decode_invoke_def] >>
        Cases_on `inst.inst_operands` >> gvs[] >>
        Cases_on `h` >> gvs[]) >>
  BasicProvers.TOP_CASE_TAC >> simp[] >>
  `eval_operands pair1 (update_var x v s) = eval_operands pair1 s`
    by (irule eval_operands_update_var >> rw[] >> gvs[MEM]) >>
  simp[] >> BasicProvers.TOP_CASE_TAC >> simp[] >>
  simp[setup_callee_update_var] >>
  BasicProvers.TOP_CASE_TAC >> simp[] >>
  BasicProvers.TOP_CASE_TAC >> simp[] >>
  simp[merge_callee_update_var] >>
  rename1 `adopt_return_fmp ret (update_var x v merged)` >>
  `adopt_return_fmp ret (update_var x v merged) =
   update_var x v (adopt_return_fmp ret merged)`
    by (Cases_on `ret.iret_adopt_fmp` >>
        simp[adopt_return_fmp_def, update_var_def]) >>
  simp[bind_outputs_update_var] >>
  BasicProvers.TOP_CASE_TAC >> gvs[]
QED

Theorem inv_ev_invoke_updates_frame:
  !updates s.
  EVERY (\uw. ~MEM (Var (FST uw)) inst.inst_operands /\
              ~MEM (FST uw) inst.inst_outputs) updates /\
  inst.inst_opcode = INVOKE ==>
  ev_step orc p d fuel ctx inst
    (FOLDL (\st uw. update_var (FST uw) (SND uw) st) s updates) =
  (case ev_step orc p d fuel ctx inst s of
     OK t => OK (FOLDL (\st uw. update_var (FST uw) (SND uw) st) t updates)
   | Halt t => Halt t
   | Abort a t => Abort a t
   | IntRet vals t => IntRet vals t
   | Error e => Error e)
Proof
  Induct >- (simp[] >> rpt strip_tac >>
    Cases_on `ev_step orc p d fuel ctx inst s` >> simp[]) >>
  simp[] >> rpt strip_tac >>
  first_x_assum (qspec_then `update_var (FST h) (SND h) s` mp_tac) >>
  simp[] >>
  `ev_step orc p d fuel ctx inst (update_var (FST h) (SND h) s) =
   (case ev_step orc p d fuel ctx inst s of
      OK t => OK (update_var (FST h) (SND h) t)
    | Halt t => Halt t | Abort a t => Abort a t
    | IntRet vals t => IntRet vals t | Error e => Error e)`
    by (irule inv_ev_invoke_frame >> metis_tac[]) >>
  simp[] >> Cases_on `ev_step orc p d fuel ctx inst s` >> simp[]
QED

Theorem inv_ev_invoke_preserves_idx:
  inst.inst_opcode = INVOKE /\ ev_step orc p d fuel ctx inst s = OK t ==>
  t.vs_inst_idx = s.vs_inst_idx
Proof
  simp[ev_step_def] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  drule bind_outputs_inst_idx >>
  simp[merge_callee_state_inst_idx]
QED

Theorem inv_call_updates_idx[local]:
  !updates s n.
  FOLDL (\st (out,w). update_var out w st)
    (s with vs_inst_idx := n) updates =
  (FOLDL (\st (out,w). update_var out w st) s updates)
    with vs_inst_idx := n
Proof
  Induct >> simp[] >> rpt gen_tac >> PairCases_on `h` >> simp[] >>
  `update_var h0 h1 (s with vs_inst_idx := n) =
   (update_var h0 h1 s) with vs_inst_idx := n` by simp[update_var_def] >>
  simp[]
QED

Theorem inv_ev_invoke_ok_idx:
  inst.inst_opcode = INVOKE /\ ev_step orc p d fuel ctx inst s = OK t ==>
  ev_step orc p d fuel ctx inst (s with vs_inst_idx := n) =
    OK (t with vs_inst_idx := n)
Proof
  strip_tac >>
  gvs[ev_step_def, AllCaseEqs()] >>
  `setup_callee callee_fn args (s with vs_inst_idx := n) =
   setup_callee callee_fn args s` by simp[NoAsms, setup_callee_def] >>
  simp[eval_ops_inst_idx] >>
  `merge_callee_state (s with vs_inst_idx := n) callee_s' =
   (merge_callee_state s callee_s') with vs_inst_idx := n`
    by simp[merge_callee_state_def] >>
  `adopt_return_fmp ret ((merge_callee_state s callee_s') with vs_inst_idx := n) =
   (adopt_return_fmp ret (merge_callee_state s callee_s')) with vs_inst_idx := n`
    by (Cases_on `ret.iret_adopt_fmp` >> simp[adopt_return_fmp_def]) >>
  simp[] >>
  qpat_x_assum `bind_outputs _ _ _ = SOME t` mp_tac >>
  simp[bind_outputs_def, pairTheory.UNCURRY_DEF, inv_call_updates_idx]
QED

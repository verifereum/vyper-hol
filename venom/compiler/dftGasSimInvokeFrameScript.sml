Theory dftGasSimInvokeFrame
Ancestors
  dftGasOracleDefs dftCommutation instIdxIndep venomExecSemantics
  venomState venomInst list

Theorem ev_step_invoke_update_var:
  (!y. MEM (Var y) inst.inst_operands ==> out <> y) /\
  ~MEM out inst.inst_outputs /\ inst.inst_opcode = INVOKE ==>
  ev_step orc p d fuel ctx inst (update_var out value s) =
  (case ev_step orc p d fuel ctx inst s of
     OK t => OK (update_var out value t) | r => r)
Proof
  rpt strip_tac >>
  simp[ev_step_def] >>
  BasicProvers.TOP_CASE_TAC >> simp[] >>
  rename1 `decode_invoke inst = SOME decoded` >>
  PairCases_on `decoded` >> simp[] >>
  `inst.inst_operands = Label decoded0 :: decoded1`
    by (gvs[decode_invoke_def] >>
        Cases_on `inst.inst_operands` >> gvs[] >>
        Cases_on `h` >> gvs[]) >>
  BasicProvers.TOP_CASE_TAC >> simp[] >>
  `eval_operands decoded1 (update_var out value s) = eval_operands decoded1 s`
    by (irule eval_operands_update_var >> rw[] >> gvs[MEM]) >>
  simp[] >>
  BasicProvers.TOP_CASE_TAC >> simp[] >>
  simp[setup_callee_update_var] >>
  BasicProvers.TOP_CASE_TAC >> simp[] >>
  BasicProvers.TOP_CASE_TAC >> simp[] >>
  rename1 `ev_blocks _ _ _ _ _ _ _ = IntRet ret callee_s` >>
  `!st fmp. (update_var out value st) with vs_fmp := fmp =
       update_var out value (st with vs_fmp := fmp)`
    by simp[update_var_def] >>
  Cases_on `ret.iret_adopt_fmp` >>
  simp[merge_callee_update_var, adopt_return_fmp_def,
       bind_outputs_update_var] >>
  BasicProvers.TOP_CASE_TAC >> gvs[]
QED

Theorem ev_step_invoke_inst_idx:
  inst.inst_opcode = INVOKE ==>
  ev_step orc p d fuel ctx inst (s with vs_inst_idx := n) =
  (case ev_step orc p d fuel ctx inst s of
     OK t => OK (t with vs_inst_idx := n) | r => r)
Proof
  strip_tac >>
  `!v w st. update_var v w (st with vs_inst_idx := n) =
       (update_var v w st) with vs_inst_idx := n`
    by simp[update_var_def] >>
  `!pairs st. FOLDL (\u (v,w). update_var v w u)
       (st with vs_inst_idx := n) pairs =
       (FOLDL (\u (v,w). update_var v w u) st pairs) with vs_inst_idx := n`
    by (Induct >> simp[pairTheory.FORALL_PROD]) >>
  `!outs vals st. bind_outputs outs vals (st with vs_inst_idx := n) =
     OPTION_MAP (\t. t with vs_inst_idx := n) (bind_outputs outs vals st)`
    by (rpt gen_tac >> Cases_on `LENGTH outs = LENGTH vals` >>
        simp[bind_outputs_def]) >>
  `!caller callee. merge_callee_state (caller with vs_inst_idx := n) callee =
       (merge_callee_state caller callee) with vs_inst_idx := n`
    by simp[merge_callee_state_def] >>
  `!ret st. adopt_return_fmp ret (st with vs_inst_idx := n) =
       (adopt_return_fmp ret st) with vs_inst_idx := n`
    by (rpt gen_tac >> Cases_on `ret.iret_adopt_fmp` >>
        simp[adopt_return_fmp_def]) >>
  simp[ev_step_def, eval_ops_inst_idx, setup_callee_def] >>
  BasicProvers.TOP_CASE_TAC >> simp[] >>
  rename1 `decode_invoke inst = SOME decoded` >>
  PairCases_on `decoded` >> simp[] >>
  BasicProvers.TOP_CASE_TAC >> simp[] >>
  BasicProvers.TOP_CASE_TAC >> simp[] >>
  BasicProvers.TOP_CASE_TAC >> simp[] >>
  BasicProvers.TOP_CASE_TAC >> simp[] >>
  rename1 `ev_blocks _ _ _ _ _ _ _ = IntRet ret callee_s` >>
  Cases_on `bind_outputs inst.inst_outputs ret.iret_values
     (adopt_return_fmp ret (merge_callee_state s callee_s))` >> simp[]
QED

Theorem ev_step_invoke_inst_idx_non_ok:
  inst.inst_opcode = INVOKE /\
  ev_step orc p d fuel ctx inst s = r /\ (!t. r <> OK t) ==>
  ev_step orc p d fuel ctx inst (s with vs_inst_idx := n) = r
Proof
  strip_tac >> simp[ev_step_invoke_inst_idx] >>
  Cases_on `r` >> gvs[]
QED

Theorem ev_step_invoke_update_var_non_ok:
  inst.inst_opcode = INVOKE /\
  (!y. MEM (Var y) inst.inst_operands ==> out <> y) /\
  ~MEM out inst.inst_outputs /\
  ev_step orc p d fuel ctx inst s = r /\ (!t. r <> OK t) ==>
  ev_step orc p d fuel ctx inst (update_var out value s) = r
Proof
  strip_tac >> drule_all ev_step_invoke_update_var >>
  Cases_on `r` >> gvs[]
QED

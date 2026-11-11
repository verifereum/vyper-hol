(* Execution of a return adapter after namespace routing.  Child reads and
   parent destinations are independent lists; layout is supplied by the producer. *)
Theory functionInlinerRoutedReturnExecution
Ancestors
  functionInlinerReturnTransport functionInlinerOperational functionInlinerFmp
  venomExecSemantics venomExecProofs venomState venomInst list pair

Theorem inline_routed_return_exec_block:
  LENGTH dests = LENGTH ops /\ eval_operands ops t = SOME vals /\
  (!x v. MEM x dests /\ MEM (Var v) ops ==> x <> v) /\
  bb.bb_instructions = pre ++
    MAP (\(x,op). <| inst_id := 0; inst_opcode := ASSIGN;
      inst_operands := [op]; inst_outputs := [x] |>) (ZIP (dests,ops)) ++
    [<| inst_id := id; inst_opcode := JMP;
        inst_operands := [Label ret]; inst_outputs := [] |>] /\
  ~t.vs_halted ==>
  let u = FOLDL (\u (x,w). update_var x w u) t (ZIP (dests,vals)) in
    exec_block fuel ctx bb (t with vs_inst_idx := LENGTH pre) =
      OK (jump_to ret u) /\
    bind_outputs dests vals t = SOME u /\
    (jump_to ret u).vs_current_bb = ret /\
    (jump_to ret u).vs_prev_bb = SOME t.vs_current_bb /\
    (jump_to ret u).vs_inst_idx = 0
Proof
  strip_tac >> simp[LET_THM] >>
  `LENGTH vals = LENGTH dests` by metis_tac[eval_operands_length] >>
  conj_tac
  >- (irule inline_return_sequence_exec_block >>
      drule_all inline_return_routed_zip_execute >>
      disch_then (qspecl_then [`fuel`, `ctx`] assume_tac) >>
      simp[inline_writes_control] >>
      goal_assum (drule_at Any) >>
      qexists `id` >>
      simp[EVERY_MEM, MEM_MAP, FORALL_PROD, get_instruction_def,
        EL_APPEND_EQN] >> rpt strip_tac >> gvs[] >>
      pairarg_tac >> simp[]) >>
  simp[bind_outputs_def, jump_to_def, inline_writes_control]
QED

(* Successful source RET/RETFMP supplies the user values and arity.  No
   equality between the child's read route and the parent's write route is used. *)
Theorem inline_routed_return_source_resume:
  step_inst source_fuel source_ctx inst s = IntRet ir s' ==>
  MEM inst.inst_opcode [RET; RETFMP] /\
  inst.inst_operands = source_ops ++ [pc] /\
  raw_return_user_arity inst = SOME (LENGTH dests) /\
  LENGTH ops = LENGTH source_ops /\
  eval_operands ops t = SOME ir.iret_values /\
  (!x v. MEM x dests /\ MEM (Var v) ops ==> x <> v) /\
  bb.bb_instructions = pre ++
    MAP (\(x,op). <| inst_id := 0; inst_opcode := ASSIGN;
      inst_operands := [op]; inst_outputs := [x] |>) (ZIP (dests,ops)) ++
    [<| inst_id := id; inst_opcode := JMP;
        inst_operands := [Label ret]; inst_outputs := [] |>] /\
  ~t.vs_halted ==>
  ?u caller'.
    s' = s /\ eval_operands source_ops s = SOME ir.iret_values /\
    exec_block fuel ctx bb (t with vs_inst_idx := LENGTH pre) =
      OK (jump_to ret u) /\
    u = FOLDL (\u (x,w). update_var x w u) t (ZIP (dests,ir.iret_values)) /\
    bind_outputs dests ir.iret_values caller = SOME caller' /\
    bind_outputs dests ir.iret_values
      (adopt_return_fmp ir (merge_callee_state caller s')) =
      SOME (adopt_return_fmp ir (merge_callee_state caller' s')) /\
    (adopt_return_fmp ir (merge_callee_state caller' s')).vs_fmp =
      (if inst.inst_opcode = RETFMP then s'.vs_fmp else caller.vs_fmp) /\
    (jump_to ret u).vs_current_bb = ret /\
    (jump_to ret u).vs_prev_bb = SOME t.vs_current_bb /\
    (jump_to ret u).vs_inst_idx = 0
Proof
  strip_tac >> strip_tac >>
  drule_all inline_return_source >> strip_tac >>
  `LENGTH dests = LENGTH ops` by metis_tac[] >>
  drule_all inline_routed_return_exec_block >>
  disch_then (qspecl_then [`fuel`, `ctx`] mp_tac) >>
  simp[LET_THM] >> strip_tac >>
  `LENGTH ir.iret_values = LENGTH dests` by
    metis_tac[eval_operands_length] >>
  `?caller'. bind_outputs dests ir.iret_values caller = SOME caller'` by
    simp[bind_outputs_def] >>
  qexists `caller'` >>
  simp[inline_return_bind_merge] >>
  drule inline_bind_outputs_fmp >> strip_tac >>
  Cases_on `ir.iret_adopt_fmp` >>
  gvs[adopt_return_fmp_def, merge_callee_state_def]
QED

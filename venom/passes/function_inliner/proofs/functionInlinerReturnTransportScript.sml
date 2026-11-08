(* Static-arity return execution through caller-output assignments and a
   continuation jump. Generated functions need not satisfy the root contract. *)
Theory functionInlinerReturnTransport
Ancestors
  functionInlinerReturnBoundary functionInlinerDefs venomExecProofs
  venomExecSemantics venomState venomInst stateFrame
  indexedLists rich_list list pred_set string functionInlinerFrame
  analysisSimDefs venomWfProps

Theorem inline_return_assignments:
  !inst rvs pc p outs args ret pi.
    (inst.inst_opcode = RET \/ inst.inst_opcode = RETFMP) /\
    inst.inst_operands = rvs ++ [pc] /\
    EVERY (\op. ~is_label_op op) rvs ==>
    FRONT (FST (rewrite_inline_inst args outs ret
      (clone_instruction p [] inst) pi)) =
    MAPi (\i rv. <| inst_id := 0; inst_opcode := ASSIGN;
      inst_operands := [clone_operand p [] rv];
      inst_outputs := [EL i outs] |>) rvs
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY (\op. ~is_label_op op) (MAP (clone_operand p []) rvs)` by
    (gvs[EVERY_MAP, EVERY_MEM] >> rpt strip_tac >>
     first_x_assum drule >> Cases_on `x` >>
     gvs[clone_operand_def, is_label_op_def]) >>
  `FILTER (\op. ~is_label_op op) (MAP (clone_operand p []) rvs) =
    MAP (clone_operand p []) rvs` by simp[FILTER_EQ_ID] >>
  gvs[rewrite_inline_inst_def, clone_instruction_def, is_param_opcode_def,
    MAP_APPEND, TAKE_APPEND, FRONT_APPEND, TAKE_LENGTH_TOO_LONG] >>
  irule LIST_EQ >> simp[EL_MAPi, EL_MAP]
QED

Theorem inline_return_zip_execute:
  !outs ops vals p V opaque caller P s t fuel ctx.
    LENGTH outs = LENGTH ops /\ eval_operands ops s = SOME vals /\
    EVERY (\op. (!v. op = Var v ==> v IN V /\ v NOTIN opaque) /\
      ~is_label_op op) ops /\
    (!x v. MEM x outs /\ v IN V ==> STRCAT p v <> x) /\
    inline_opaque_frame_rel (STRCAT p) V opaque caller.vs_vars P s t ==>
    run_insts fuel ctx
      (MAP (\(x,op). <| inst_id := 0; inst_opcode := ASSIGN;
        inst_operands := [clone_operand p [] op]; inst_outputs := [x] |>)
        (ZIP (outs,ops))) t =
      OK (FOLDL (\t (x,w). update_var x w t) t (ZIP (outs,vals))) /\
    inline_opaque_frame_rel (STRCAT p) V opaque
      (FOLDL (\c (x,w). update_var x w c) caller (ZIP (outs,vals))).vs_vars P s
      (FOLDL (\t (x,w). update_var x w t) t (ZIP (outs,vals)))
Proof
  Induct >> Cases_on `ops` >> simp[] >> rpt gen_tac >> strip_tac
  >- gvs[eval_operands_def, run_insts_def] >>
  gvs[eval_operands_def, AllCaseEqs()] >>
  rename1 `eval_operand rv s = SOME w` >>
  rename1 `inline_opaque_frame_rel (STRCAT p) V opaque caller.vs_vars P s target` >>
  `eval_operands (MAP (inline_rename_operand (STRCAT p) (\l. l)) [rv]) target =
    eval_operands [rv] s` by
    (irule inline_opaque_frame_eval_operands >>
     qexistsl [`P`, `V`, `opaque`, `caller.vs_vars`] >>
     simp[] >> Cases_on `rv` >> gvs[is_label_op_def]) >>
  `eval_operand (clone_operand p [] rv) target = SOME w` by
    gvs[clone_operand_inline_rename, eval_operands_def, AllCaseEqs()] >>
  simp[run_insts_def, step_inst_non_invoke, step_inst_base_opcode_eqs] >>
  first_x_assum irule >> simp[] >> conj_tac
  >- metis_tac[] >>
  irule inline_opaque_frame_write_caller >> simp[] >> metis_tac[]
QED

Theorem inline_return_zip_syntax:
  LENGTH outs = LENGTH ops ==>
  MAP (\(x,op). <| inst_id := 0; inst_opcode := ASSIGN;
      inst_operands := [clone_operand p [] op]; inst_outputs := [x] |>)
    (ZIP (outs,ops)) =
  MAPi (\i op. <| inst_id := 0; inst_opcode := ASSIGN;
      inst_operands := [clone_operand p [] op]; inst_outputs := [EL i outs] |>) ops
Proof
  strip_tac >> irule LIST_EQ >> simp[EL_MAP, EL_MAPi, EL_ZIP]
QED

Theorem inline_return_assignments_execute:
  LENGTH outs = LENGTH ops /\ eval_operands ops s = SOME vals /\
  EVERY (\op. (!v. op = Var v ==> v IN V /\ v NOTIN opaque) /\
    ~is_label_op op) ops /\
  (!x v. MEM x outs /\ v IN V ==> STRCAT p v <> x) /\
  inline_opaque_frame_rel (STRCAT p) V opaque caller.vs_vars P s t ==>
  ?u caller'.
    run_insts fuel ctx
      (MAPi (\i op. <| inst_id := 0; inst_opcode := ASSIGN;
        inst_operands := [clone_operand p [] op]; inst_outputs := [EL i outs] |>) ops)
      t = OK u /\
    bind_outputs outs vals caller = SOME caller' /\
    bind_outputs outs vals t = SOME u /\
    inline_opaque_frame_rel (STRCAT p) V opaque caller'.vs_vars P s u
Proof
  strip_tac >> drule_all inline_return_zip_execute >>
  disch_then (qspecl_then [`fuel`, `ctx`] mp_tac) >>
  simp[inline_return_zip_syntax] >> strip_tac >>
  `LENGTH vals = LENGTH outs` by metis_tac[eval_operands_length] >>
  simp[bind_outputs_def] >> metis_tac[]
QED

Theorem inline_return_sequence_exec_block:
  run_insts fuel ctx assigns t = OK u /\
  EVERY (\i. i.inst_opcode = ASSIGN) assigns /\
  k + LENGTH assigns < LENGTH bb.bb_instructions /\
  (!j. j < LENGTH assigns ==> EL (k + j) bb.bb_instructions = EL j assigns) /\
  get_instruction bb (k + LENGTH assigns) = SOME
    <| inst_id := id; inst_opcode := JMP; inst_operands := [Label ret];
       inst_outputs := [] |> /\ ~u.vs_halted ==>
  exec_block fuel ctx bb (t with vs_inst_idx := k) = OK (jump_to ret u)
Proof
  strip_tac >>
  `exec_block fuel ctx bb (t with vs_inst_idx := k) =
    exec_block fuel ctx bb (u with vs_inst_idx := k + LENGTH assigns)` by
    (irule exec_block_skip_prefix_non_invoke >> simp[] >>
     gvs[EVERY_MEM] >> rpt strip_tac >> first_x_assum drule >>
     gvs[is_terminator_def]) >>
  asm_rewrite_tac[] >>
  simp[Once exec_block_def, step_inst_non_invoke, step_inst_base_opcode_eqs,
    is_terminator_def, jump_to_def]
QED

Theorem inline_return_rewrite_sequence:
  (inst.inst_opcode = RET \/ inst.inst_opcode = RETFMP) /\
  inst.inst_operands = ops ++ [pc] /\
  EVERY (\op. ~is_label_op op) ops ==>
  FST (rewrite_inline_inst args outs ret (clone_instruction p [] inst) param_idx) =
    MAPi (\i op. <| inst_id := 0; inst_opcode := ASSIGN;
      inst_operands := [clone_operand p [] op]; inst_outputs := [EL i outs] |>) ops ++
    [inst with <| inst_opcode := JMP; inst_operands := [Label ret]; inst_outputs := [] |>]
Proof
  strip_tac >>
  `EVERY (\op. ~is_label_op op) (MAP (clone_operand p []) ops)` by
    (gvs[EVERY_MAP, EVERY_MEM] >> rpt strip_tac >>
     first_x_assum drule >> Cases_on `x` >>
     gvs[clone_operand_def, is_label_op_def]) >>
  `FILTER (\op. ~is_label_op op) (MAP (clone_operand p []) ops) =
    MAP (clone_operand p []) ops` by simp[FILTER_EQ_ID] >>
  gvs[rewrite_inline_inst_def, clone_instruction_def, is_param_opcode_def,
    MAP_APPEND, TAKE_APPEND, TAKE_LENGTH_TOO_LONG] >>
  irule LIST_EQ >> simp[EL_MAPi, EL_MAP]
QED

Theorem inline_return_bind_control[local]:
  bind_outputs outs vals t = SOME u ==>
  u.vs_halted = t.vs_halted /\ u.vs_current_bb = t.vs_current_bb
Proof
  strip_tac >> conj_tac >>
  irule venomInstProofs1Theory.bind_outputs_preserves >>
  simp[update_var_def] >> goal_assum (drule_at Any)
QED

Theorem inline_return_rewrite_exec_block:
  MEM inst.inst_opcode [RET; RETFMP] /\ 
  inst.inst_operands = ops ++ [pc] /\ LENGTH outs = LENGTH ops /\
  eval_operands ops s = SOME vals /\
  EVERY (\op. (!v. op = Var v ==> v IN V /\ v NOTIN opaque) /\
    ~is_label_op op) ops /\
  (!x v. MEM x outs /\ v IN V ==> STRCAT p v <> x) /\
  inline_opaque_frame_rel (STRCAT p) V opaque caller.vs_vars P s t /\
  bb.bb_instructions = pre ++
    FST (rewrite_inline_inst args outs ret (clone_instruction p [] inst) param_idx) /\
  ~t.vs_halted ==>
  ?u caller'.
    exec_block fuel ctx bb (t with vs_inst_idx := LENGTH pre) = OK (jump_to ret u) /\
    bind_outputs outs vals caller = SOME caller' /\
    bind_outputs outs vals t = SOME u /\
    inline_opaque_frame_rel (STRCAT p) V opaque caller'.vs_vars P s u /\
    (jump_to ret u).vs_current_bb = ret /\
    (jump_to ret u).vs_inst_idx = 0 /\
    (jump_to ret u).vs_prev_bb = SOME t.vs_current_bb
Proof
  pure_rewrite_tac [MEM] >> strip_tac >> (
  `EVERY (\op. ~is_label_op op) ops` by
    gvs[EVERY_MEM] >>
  imp_res_tac inline_return_rewrite_sequence >>
  drule_all inline_return_assignments_execute >>
  disch_then (qspecl_then [`fuel`, `ctx`] strip_assume_tac) >>
  drule inline_return_bind_control >> strip_tac >>
  qexistsl [`u`, `caller'`] >> conj_tac
  >- (irule inline_return_sequence_exec_block >> simp[] >>
      goal_assum (drule_at Any) >>
      simp[EVERY_MEM, MEM_MAPi, inline_return_rewrite_sequence, get_instruction_def,
        EL_APPEND_EQN] >> qexists `inst.inst_id` >>
      simp[instruction_component_equality] >> rpt strip_tac >> gvs[]) >>
  simp[jump_to_def])
QED

Theorem inline_return_source:
  MEM inst.inst_opcode [RET; RETFMP] /\ 
  inst.inst_operands = ops ++ [pc] /\
  raw_return_user_arity inst = SOME (LENGTH (outs:string list)) /\
  step_inst fuel ctx inst s = IntRet ir s' ==>
  s' = s /\ LENGTH outs = LENGTH ops /\
  eval_operands ops s = SOME ir.iret_values /\
  ir.iret_adopt_fmp =
    (if inst.inst_opcode = RETFMP then SOME s.vs_fmp else NONE)
Proof
  pure_rewrite_tac [MEM] >> strip_tac >>
  gvs[step_inst_non_invoke, step_inst_base_opcode_eqs,
    callLayoutDefsTheory.raw_return_user_arity_def,
    fnFrameBoundaryGenRetTheory.eval_operands_append,
    eval_operands_def, AllCaseEqs()] >>
  qpat_x_assum `_ ++ [_] = _` (SUBST1_TAC o SYM) >> simp[FRONT_APPEND]
QED

(* Restoring the caller's locals commutes with the generated output writes.
   FMP adoption is kept explicit: RET restores caller FMP, RETFMP adopts it. *)
Theorem inline_return_writes_merge[local]:
  !pairs caller s ir.
  FOLDL (\t (x,w). update_var x w t)
    (adopt_return_fmp ir (merge_callee_state caller s)) pairs =
  adopt_return_fmp ir
    (merge_callee_state (FOLDL (\t (x,w). update_var x w t) caller pairs) s)
Proof
  Induct >> simp[] >> rpt gen_tac >> PairCases_on `h` >> simp[] >>
  `update_var h0 h1 (adopt_return_fmp ir (merge_callee_state caller s)) =
   adopt_return_fmp ir (merge_callee_state (update_var h0 h1 caller) s)` by
    (Cases_on `ir.iret_adopt_fmp` >>
     simp[adopt_return_fmp_def, merge_callee_state_def, update_var_def]) >>
  simp[]
QED

Theorem inline_return_bind_merge:
  bind_outputs outs vals caller = SOME caller' ==>
  bind_outputs outs vals (adopt_return_fmp ir (merge_callee_state caller s)) =
    SOME (adopt_return_fmp ir (merge_callee_state caller' s))
Proof
  simp[bind_outputs_def] >> strip_tac >> gvs[inline_return_writes_merge]
QED

Theorem inline_return_merge_effects:
  inline_opaque_frame_rel ren V opaque saved P s u ==>
  merge_callee_state caller s = merge_callee_state caller u /\
  u.vs_fmp = s.vs_fmp
Proof
  simp[inline_opaque_frame_rel_def, inline_frame_rel_def] >> rpt strip_tac >>
  qpat_x_assum `inline_shared_frame s = inline_shared_frame u` mp_tac >>
  simp[inline_shared_frame_def, execution_frame_def,
    venom_state_component_equality, merge_callee_state_def]
QED

Theorem inline_return_exit:
  (inst.inst_opcode = RET \/ inst.inst_opcode = RETFMP) /\
  inst.inst_operands = ops ++ [pc] /\
  raw_return_user_arity inst = SOME (LENGTH outs) /\
  step_inst source_fuel ctx inst s = IntRet ir s' /\
  EVERY (\op. (!v. op = Var v ==> v IN V /\ v NOTIN opaque) /\
    ~is_label_op op) ops /\
  (!x v. MEM x outs /\ v IN V ==> STRCAT p v <> x) /\
  inline_opaque_frame_rel (STRCAT p) V opaque caller.vs_vars P s t /\
  bb.bb_instructions = pre ++
    FST (rewrite_inline_inst args outs ret (clone_instruction p [] inst) param_idx) /\
  ~t.vs_halted ==>
  ?u caller'.
    exec_block fuel ctx bb (t with vs_inst_idx := LENGTH pre) = OK (jump_to ret u) /\
    bind_outputs outs ir.iret_values caller = SOME caller' /\
    bind_outputs outs ir.iret_values
      (adopt_return_fmp ir (merge_callee_state caller s')) =
      SOME (adopt_return_fmp ir (merge_callee_state caller' s')) /\
    inline_opaque_frame_rel (STRCAT p) V opaque caller'.vs_vars P s' u /\
    (!x. x IN P ==> lookup_var x (jump_to ret u) =
      lookup_var x (adopt_return_fmp ir (merge_callee_state caller' s'))) /\
    merge_callee_state caller u = merge_callee_state caller s' /\
    u.vs_fmp = s'.vs_fmp /\
    (adopt_return_fmp ir (merge_callee_state caller' s')).vs_fmp =
      (if inst.inst_opcode = RETFMP then s'.vs_fmp else caller.vs_fmp) /\
    (jump_to ret u).vs_current_bb = ret /\
    (jump_to ret u).vs_inst_idx = 0 /\
    (jump_to ret u).vs_prev_bb = SOME t.vs_current_bb
Proof
  strip_tac >> (
  `MEM inst.inst_opcode [RET; RETFMP]` by simp[] >>
  drule_all inline_return_source >> strip_tac >>
  qpat_x_assum `s' = s` SUBST_ALL_TAC >>
  drule_all inline_return_rewrite_exec_block >>
  disch_then (qspecl_then [`fuel`, `ctx`] strip_assume_tac) >>
  qexistsl [`u`, `caller'`] >> simp[inline_return_bind_merge] >>
  imp_res_tac inline_return_merge_effects >> simp[] >>
  conj_tac
  >- (gvs[inline_opaque_frame_rel_def, inline_frame_rel_def,
        lookup_var_def, jump_to_def, adopt_return_fmp_def, merge_callee_state_def]) >>
  drule inline_return_bind_control >> strip_tac >>
  `caller'.vs_fmp = caller.vs_fmp` by
    (irule venomInstProofs1Theory.bind_outputs_preserves >>
     simp[update_var_def] >> goal_assum (drule_at Any)) >>
  gvs[adopt_return_fmp_def])
QED

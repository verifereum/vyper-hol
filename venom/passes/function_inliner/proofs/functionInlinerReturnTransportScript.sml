(* Source-indexed transport of return assignment prefixes.  This theory does
   not assert that a generated function satisfies the original input contract. *)
Theory functionInlinerReturnTransport
Ancestors
  functionInlinerReturnBoundary functionInlinerDefs venomExecProofs
  venomExecSemantics venomState venomInst simplifyCfgPhiSemantics stateFrame
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

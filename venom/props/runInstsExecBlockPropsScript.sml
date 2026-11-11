Theory runInstsExecBlockProps
Ancestors
  analysisSimProofsBase analysisSimDefs instIdxIndep venomWf
  venomExecSemantics venomInst venomState list
Libs
  wordsLib

Definition result_idx_zero_def:
  result_idx_zero r = exec_result_map (\s. s with vs_inst_idx := 0) r
End

Definition result_halt_wrap_def:
  result_halt_wrap r =
    case r of OK s => if s.vs_halted then Halt s else OK s
    | other => other
End

Theorem step_inst_idx_zero:
  !fuel ctx inst s j.
    result_idx_zero (step_inst fuel ctx inst (s with vs_inst_idx := j)) =
    result_idx_zero (step_inst fuel ctx inst s)
Proof
  rpt gen_tac >> Cases_on `inst.inst_opcode = INVOKE`
  >- (simp[invoke_step_inst_idx_OK_only] >>
      Cases_on `step_inst fuel ctx inst s` >>
      simp[result_idx_zero_def, exec_result_map_def]) >>
  Cases_on `is_terminator inst.inst_opcode`
  >- simp[result_idx_zero_def, step_inst_non_invoke,
          terminator_step_inst_base_idx_norm0] >>
  simp[step_inst_idx_indep] >>
  Cases_on `step_inst fuel ctx inst s` >>
  simp[result_idx_zero_def, exec_result_map_def]
QED

Theorem run_insts_idx_zero:
  !xs fuel ctx s j.
    result_idx_zero (run_insts fuel ctx xs (s with vs_inst_idx := j)) =
    result_idx_zero (run_insts fuel ctx xs s)
Proof
  Induct >> simp[run_insts_def, result_idx_zero_def, exec_result_map_def] >>
  rpt gen_tac >>
  qspecl_then [`fuel`,`ctx`,`h`,`s`,`j`] mp_tac step_inst_idx_zero >>
  Cases_on `step_inst fuel ctx h s` >>
  Cases_on `step_inst fuel ctx h (s with vs_inst_idx := j)` >>
  simp[result_idx_zero_def, exec_result_map_def] >> rpt strip_tac >> gvs[] >>
  first_assum (qspecl_then [`fuel`,`ctx`,`v'`,`0`] assume_tac) >>
  first_x_assum (qspecl_then [`fuel`,`ctx`,`v`,`0`] assume_tac) >>
  gvs[result_idx_zero_def]
QED

Theorem exec_block_run_insts_suffix:
  !xs fuel ctx bb s.
    DROP s.vs_inst_idx bb.bb_instructions = xs /\ xs <> [] /\
    EVERY (\i. ~is_terminator i.inst_opcode) (FRONT xs) /\
    is_terminator (LAST xs).inst_opcode ==>
    result_idx_zero (exec_block fuel ctx bb s) =
    result_halt_wrap (result_idx_zero (run_insts fuel ctx xs s))
Proof
  Induct >- simp[] >>
  rpt gen_tac >> strip_tac >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by
    (qpat_x_assum `DROP _ _ = _` (mp_tac o Q.AP_TERM `LENGTH`) >>
     simp[]) >>
  `get_instruction bb s.vs_inst_idx = SOME h` by
    (simp[get_instruction_def] >>
     drule (GSYM listTheory.HD_DROP) >> simp[]) >>
  once_rewrite_tac[exec_block_def] >> simp[] >>
  Cases_on `xs = []`
  >- (gvs[run_insts_def] >> Cases_on `step_inst fuel ctx h s` >>
      simp[result_idx_zero_def, exec_result_map_def, result_halt_wrap_def] >>
      Cases_on `v.vs_halted` >> simp[exec_result_map_def]) >>
  `~is_terminator h.inst_opcode` by
    (Cases_on `xs` >> gvs[]) >>
  simp[] >> Cases_on `step_inst fuel ctx h s` >>
  simp[run_insts_def, result_idx_zero_def, exec_result_map_def,
       result_halt_wrap_def] >>
  first_x_assum (qspecl_then
    [`fuel`,`ctx`,`bb`,`v with vs_inst_idx := SUC s.vs_inst_idx`] mp_tac) >>
  impl_tac
  >- (gvs[FRONT_DEF] >>
      `DROP (SUC s.vs_inst_idx) bb.bb_instructions = xs` by
        (qpat_x_assum `DROP _ _ = _` (mp_tac o Q.AP_TERM `DROP 1`) >>
         simp[rich_listTheory.DROP_DROP_T, arithmeticTheory.ADD1]) >> Cases_on `xs` >> gvs[]) >>
  simp[run_insts_idx_zero, result_idx_zero_def, result_halt_wrap_def]
QED

Theorem exec_block_run_insts:
  !fuel ctx bb s j.
    bb_well_formed bb /\ j < LENGTH bb.bb_instructions ==>
    result_idx_zero (exec_block fuel ctx bb (s with vs_inst_idx := j)) =
    result_halt_wrap
      (result_idx_zero (run_insts fuel ctx (DROP j bb.bb_instructions) s))
Proof
  rpt strip_tac >>
  qspecl_then [`DROP j bb.bb_instructions`,`fuel`,`ctx`,`bb`,
               `s with vs_inst_idx := j`] mp_tac exec_block_run_insts_suffix >>
  simp[run_insts_idx_zero] >> disch_then irule >>
  gvs[bb_well_formed_def, last_drop] >>
  simp[EVERY_EL] >> rpt strip_tac >>
  `DROP j bb.bb_instructions <> []` by simp[] >>
  `n+j < LENGTH bb.bb_instructions /\
   n+j <> PRE (LENGTH bb.bb_instructions)` by
    (gvs[LENGTH_FRONT] >> decide_tac) >>
  `EL n (FRONT (DROP j bb.bb_instructions)) =
   EL (n+j) bb.bb_instructions` by
    simp[rich_listTheory.EL_FRONT, EL_DROP, NULL_EQ] >>
  metis_tac[]
QED

(* Unlike internal instruction cursors, Error payloads are unchanged. *)
Theorem exec_block_run_insts_error:
  !fuel ctx bb s j e.
    bb_well_formed bb /\ j < LENGTH bb.bb_instructions ==>
    (exec_block fuel ctx bb (s with vs_inst_idx := j) = Error e <=>
     run_insts fuel ctx (DROP j bb.bb_instructions) s = Error e)
Proof
  rpt strip_tac >>
  qspecl_then [`fuel`,`ctx`,`bb`,`s`,`j`] mp_tac exec_block_run_insts >>
  simp[] >>
  Cases_on `exec_block fuel ctx bb (s with vs_inst_idx := j)` >>
  Cases_on `run_insts fuel ctx (DROP j bb.bb_instructions) s` >>
  simp[result_idx_zero_def, exec_result_map_def, result_halt_wrap_def] >>
  gvs[AllCaseEqs()]
QED

(* Existing venomExecProofs.exec_block_OK_inst_idx_0 recovers the
   unnormalized successful exit from this normalized interface. *)
Theorem exec_block_run_insts_ok:
  !fuel ctx bb s j t.
    bb_well_formed bb /\ j < LENGTH bb.bb_instructions ==>
    (exec_block fuel ctx bb (s with vs_inst_idx := j) = OK t <=>
     ?u. run_insts fuel ctx (DROP j bb.bb_instructions) s = OK u /\
         ~u.vs_halted /\ t = u with vs_inst_idx := 0)
Proof
  rpt strip_tac >>
  qspecl_then [`fuel`,`ctx`,`bb`,`s`,`j`] mp_tac exec_block_run_insts >>
  simp[] >>
  Cases_on `exec_block fuel ctx bb (s with vs_inst_idx := j)` >>
  Cases_on `run_insts fuel ctx (DROP j bb.bb_instructions) s` >>
  simp[result_idx_zero_def, exec_result_map_def, result_halt_wrap_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  imp_res_tac venomExecProofsTheory.exec_block_OK_inst_idx_0 >>
  gvs[] >> metis_tac[]
QED

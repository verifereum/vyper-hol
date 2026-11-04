Theory frameRawReachable
Ancestors
  contextRawReachable ptrDiscipline venomExecSemantics venomInst contextCodegenRel
  crossBlockSimProps passSimulationDefs

Theorem raw_reachable_completed_invoke:
  !vs ctx caller callinst s nm ops callee args cs fuel ret se sr inst'.
  raw_reachable vs ctx caller callinst s /\ active_inst caller callinst s /\
  callinst.inst_opcode = INVOKE /\ decode_invoke callinst = SOME (nm,ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  run_blocks fuel ctx callee cs = IntRet ret se /\
  bind_outputs callinst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state s se)) = SOME sr /\
  active_inst caller inst' (sr with vs_inst_idx := SUC s.vs_inst_idx) ==>
  raw_reachable vs ctx caller inst' (sr with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  rpt strip_tac >>
  `step_inst fuel ctx callinst s = OK sr` by
    simp[Once step_inst_def] >>
  irule raw_reachable_next >>
  conj_tac >- simp[] >>
  qexistsl [`fuel`,`callinst`] >> simp[is_terminator_def]
QED

(* The block lookup is explicit: active_inst alone uses membership, which
   need not identify the block returned by lookup_block without uniqueness. *)
Theorem run_blocks_immediate_return:
  !ctx fn cs bb sp s1 rinst fuel ret se.
  lookup_block cs.vs_current_bb fn.fn_blocks = SOME bb /\
  eval_phis cs bb.bb_instructions = OK sp /\
  s1 = sp with vs_inst_idx := phi_prefix_length bb.bb_instructions /\
  get_instruction bb s1.vs_inst_idx = SOME rinst /\
  step_inst fuel ctx rinst s1 = IntRet ret se ==>
  run_blocks (SUC fuel) ctx fn cs = IntRet ret se
Proof
  rpt strip_tac >> gvs[] >>
  `exec_block fuel ctx bb (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) = IntRet ret se` by
    simp[Once exec_block_def] >>
  simp[Once run_blocks_unfold, run_block_def]
QED

Theorem frame_step_fuel_mono:
  !f ctx inst s. (!e. step_inst f ctx inst s <> Error e) ==>
  !k. step_inst (f+k) ctx inst s = step_inst f ctx inst s
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (
    qpat_x_assum `!e. _` mp_tac >>
    simp[Once step_inst_def] >>
    Cases_on `decode_invoke inst` >- simp[] >>
    PairCases_on `x` >> simp[] >>
    Cases_on `lookup_function x0 ctx.ctx_functions` >- simp[] >>
    rename1 `lookup_function x0 ctx.ctx_functions = SOME callee` >>
    Cases_on `eval_operands x1 s` >- simp[] >>
    rename1 `eval_operands x1 s = SOME args` >>
    Cases_on `setup_callee callee args s` >- simp[] >>
    rename1 `setup_callee callee args s = SOME cs` >>
    strip_tac >>
    `terminates (run_blocks f ctx callee cs)` by
      (Cases_on `run_blocks f ctx callee cs` >> gvs[terminates_def]) >>
    drule run_blocks_fuel_mono >> disch_then (qspec_then `k` assume_tac) >>
    simp[step_inst_def]) >>
  simp[step_inst_def]
QED

Theorem frame_exec_fuel_mono:
  !f ctx bb s. (!e. exec_block f ctx bb s <> Error e) ==>
  !k. exec_block (f+k) ctx bb s = exec_block f ctx bb s
Proof
  rpt gen_tac >>
  measureInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >>
  qpat_x_assum `!e. _` mp_tac >>
  once_rewrite_tac[exec_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >- simp[] >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  simp[] >> strip_tac >>
  `!e. step_inst f ctx inst s <> Error e` by
    (spose_not_then strip_assume_tac >> gvs[]) >>
  drule frame_step_fuel_mono >> disch_then (qspec_then `k` assume_tac) >>
  simp[] >>
  Cases_on `step_inst f ctx inst s` >> gvs[] >>
  rename1 `step_inst f ctx inst s = OK s'` >>
  Cases_on `is_terminator inst.inst_opcode` >> gvs[] >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by
    (gvs[get_instruction_def, AllCaseEqs()]) >>
  first_x_assum irule >> simp[]
QED

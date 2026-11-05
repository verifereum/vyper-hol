Theory exprSendPtr
Ancestors
  callStepPtr wordArgsPtr exprSimSend fragGasSeqPtr fragGasPathPtr stmtAssertPtr
  ptrSafeRun ptrDiscipline venomExecSemantics venomExecProofs
  venomInst venomInstProofs venomState opcodeClass memLocDefs codegenRel contextCodegenRel list
  venomCallOracleDefs venomMemProps ghostPcTransportPtr

Theorem ptr_inst_ok_assert:
  ~ctx_has_dalloca ctx /\ op_taint tn op = {} /\
  eval_operand op s = SOME w ==>
  ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id ASSERT [op] []) s
Proof
  strip_tac >> drule step_assert_behavior >> strip_tac >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def,
       mk_inst_def] >>
  rpt strip_tac >> gvs[step_inst_non_invoke] >>
  first_x_assum (qspec_then `id` mp_tac) >>
  Cases_on `w = 0w` >> gvs[]
QED

Theorem assert_ghost_unchanged:
  step_prov PG G (mk_inst id ASSERT [op] []) s = G /\
  step_taint (mk_inst id ASSERT [op] []) s s tn = tn
Proof
  simp[step_prov_def, step_taint_def, mk_inst_def, set_prov_def,
       set_var_taint_def, mem_taint_def, store_taint_def, imm_taint_def,
       adopt_reset_def, new_site_bytes_def, step_writes_def,
       source_memory_write_ranges_def, written_taint_def] >>
  Cases_on `tn` >>
  simp[finite_mapTheory.DRESTRICT_UNIV, range_bytes_def,
       finite_mapTheory.FLOOKUP_DEF, pred_setTheory.EXTENSION,
       SF CONJ_ss] >>
  simp[taint_component_equality]
QED

Theorem assert_ok_path_ptr:
  ~ctx_has_dalloca ctx /\ op_taint tn op = {} /\
  eval_operand op s = SOME w /\ w <> 0w /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id ASSERT [op] []) ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 G tn
    (OK (s with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `step_inst_base (mk_inst id ASSERT [op] []) s = OK s` by
    (simp[mk_inst_def] >> drule step_assert_behavior >> simp[]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id ASSERT [op] []) s` by
    (irule ptr_inst_ok_assert >> metis_tac[]) >>
  `(mk_inst id ASSERT [op] []).inst_opcode <> INVOKE /\
   ~is_terminator (mk_inst id ASSERT [op] []).inst_opcode` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all straight_line_ptr_edge >>
  simp[mk_inst_def, is_terminator_def, assert_ghost_unchanged] >>
  strip_tac >>
  `~(s with vs_inst_idx := SUC s.vs_inst_idx).vs_halted` by simp[] >>
  metis_tac[gas_path_ptr_rules, arithmeticTheory.ADD_CLAUSES]
QED

Theorem assert_fail_path_ptr:
  ~ctx_has_dalloca ctx /\ op_taint tn op = {} /\
  eval_operand op s = SOME 0w /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id ASSERT [op] []) ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 G tn
    (Abort Revert_abort (revert_state (set_returndata [] s)))
Proof
  strip_tac >>
  `step_inst_base (mk_inst id ASSERT [op] []) s =
     Abort Revert_abort (revert_state (set_returndata [] s))` by
    (simp[mk_inst_def] >> drule step_assert_behavior >> simp[]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id ASSERT [op] []) s` by
    (irule ptr_inst_ok_assert >> metis_tac[]) >>
  `(mk_inst id ASSERT [op] []).inst_opcode <> INVOKE /\
   ~is_terminator (mk_inst id ASSERT [op] []).inst_opcode` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all gas_path_ptr_abort >> simp[mk_inst_def, is_terminator_def]
QED

Theorem ptr_inst_ok_send_call:
  inst.inst_opcode = CALL /\
  inst.inst_operands = [gas; addr; value; Lit 0w; Lit 0w; Lit 0w; Lit 0w] /\
  eval_operand gas s = SOME gw /\ eval_operand addr s = SOME aw /\
  eval_operand value s = SOME vw /\
  op_taint tn gas = {} /\ op_taint tn addr = {} /\
  op_taint tn value = {} /\ ~ctx_has_dalloca ctx /\
  stor_taint_ok cx tn s ==>
  ptr_inst_ok (cx_dead cx) 0 fuel ctx fn G tn inst s
Proof
  strip_tac >> irule ptr_inst_ok_call >> simp[allocas_from_def] >>
  gvs[bodyPtrDefsTheory.stor_taint_ok_def, bodyPtrDefsTheory.cx_dead_def] >>
  conj_tac
  >- (irule taint_ok_call >>
      gvs[op_taint_def, source_memory_read_ranges_def,
          mem_read_ops_def, memory_range_of_operands_def, eval_operand_def]) >>
  irule access_ok_call >> simp[eval_operand_def]
QED

Theorem send_call_step:
  ~s.vs_call_ctx.cc_static /\
  inst.inst_opcode = CALL /\ inst.inst_outputs = [out] /\
  inst.inst_operands = [gas; addr; value; Lit 0w; Lit 0w; Lit 0w; Lit 0w] /\
  eval_operand gas s = SOME gw /\ eval_operand addr s = SOME aw /\
  eval_operand value s = SOME vw ==>
  step_inst_base inst s =
    OK (update_var out
      (FST (consume_call_outcome (venom_call_request s aw vw 0w 0w F) 0 0 s))
      (SND (consume_call_outcome (venom_call_request s aw vw 0w 0w F) 0 0 s)))
Proof
  strip_tac >>
  simp[Once step_inst_base_def, eval_operand_def, Excl "consume_call_outcome_eq"] >>
  simp[exec_ext_call_def, Excl "consume_call_outcome_eq"] >>
  pairarg_tac >> simp[Excl "consume_call_outcome_eq"]
QED

Theorem send_call_runtime_frame:
  ~s.vs_call_ctx.cc_static /\
  inst.inst_opcode = CALL /\ inst.inst_outputs = [out] /\
  inst.inst_operands = [gas; addr; value; Lit 0w; Lit 0w; Lit 0w; Lit 0w] /\
  eval_operand gas s = SOME gw /\ eval_operand addr s = SOME aw /\
  eval_operand value s = SOME vw /\ step_inst_base inst s = OK u ==>
  u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
  u.vs_fmp = s.vs_fmp /\ u.vs_call_ctx = s.vs_call_ctx /\
  (!p. p <> out ==> lookup_var p u = lookup_var p s)
Proof
  strip_tac >> drule_all send_call_step >>
  gvs[Excl "consume_call_outcome_eq"] >>
  simp[consume_call_outcome_eq, write_memory_with_expansion_empty_0,
       update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  metis_tac[]
QED

Theorem send_call_stor_taint:
  ~s.vs_call_ctx.cc_static /\ stor_taint_ok cx tn s /\
  inst.inst_opcode = CALL /\ inst.inst_outputs = [out] /\
  inst.inst_operands = [gas; addr; value; Lit 0w; Lit 0w; Lit 0w; Lit 0w] /\
  eval_operand gas s = SOME gw /\ eval_operand addr s = SOME aw /\
  eval_operand value s = SOME vw /\ step_inst_base inst s = OK u ==>
  stor_taint_ok cx (step_taint inst s u tn) u
Proof
  strip_tac >> drule_all send_call_runtime_frame >> strip_tac >>
  irule call_stor_taint_ok >> simp[] >> strip_tac >>
  drule_all send_call_step >> strip_tac >>
  gvs[update_var_def, Excl "consume_call_outcome_eq"] >>
  irule consume_call_no_reset_accounts >>
  simp[Excl "consume_call_outcome_eq"] >>
  qexistsl_tac [`0w`, `aw`, `0w`, `0`, `0`, `vw`] >> simp[]
QED

Theorem send_call_ghost_inv:
  ~s.vs_call_ctx.cc_static /\ ghost_inv d cenv cx es G tn s /\
  es'.scopes = es.scopes /\
  inst.inst_opcode = CALL /\ inst.inst_outputs = [out] /\
  inst.inst_operands = [gas; addr; value; Lit 0w; Lit 0w; Lit 0w; Lit 0w] /\
  eval_operand gas s = SOME gw /\ eval_operand addr s = SOME aw /\
  eval_operand value s = SOME vw /\ step_inst_base inst s = OK u /\
  (!n p sz. FLOOKUP cenv.ce_vars n = SOME (PtrVar (Var p) sz) ==> p <> out) /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> p <> out) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> p <> out) ==>
  ghost_inv d cenv cx es' (step_prov PG G inst u) (step_taint inst s u tn) u
Proof
  strip_tac >>
  `stor_taint_ok cx tn s` by gvs[bodyPtrDefsTheory.ghost_inv_def] >>
  drule_all send_call_runtime_frame >> strip_tac >>
  `stor_taint_ok cx (step_taint inst s u tn) u` by
    (irule send_call_stor_taint >> metis_tac[]) >>
  `(step_taint inst s u tn).t_mem = tn.t_mem` by
    (irule call_zero_region_memory_taint >> metis_tac[]) >>
  irule call_ghost_inv >> metis_tac[]
QED

Theorem send_call_ghost_kept:
  ~s.vs_call_ctx.cc_static /\ ~not_fresh_at sa out /\
  inst.inst_opcode = CALL /\ inst.inst_outputs = [out] /\
  inst.inst_operands = [gas; addr; value; Lit 0w; Lit 0w; Lit 0w; Lit 0w] /\
  eval_operand gas s = SOME gw /\ eval_operand addr s = SOME aw /\
  eval_operand value s = SOME vw /\ step_inst_base inst s = OK u ==>
  ghost_kept cenv es sa G tn s (step_prov PG G inst u) (step_taint inst s u tn)
Proof
  strip_tac >> drule_all send_call_runtime_frame >> strip_tac >>
  irule call_ghost_kept >> metis_tac[]
QED

Theorem call_assert_ok_path_ptr:
  inst.inst_opcode = CALL /\ inst.inst_outputs = [out] /\
  inst.inst_operands = [gas; addr; value; ao; az; ro; rz] /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst aid ASSERT [Var out] []) /\
  ptr_inst_ok D 0 0 ctx fn G tn inst s /\
  step_inst_base inst s = OK u /\
  eval_operand (Var out) u = SOME w /\ w <> 0w ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G inst u) (step_taint inst s u tn)
    (OK (u with vs_inst_idx := SUC (SUC s.vs_inst_idx)))
Proof
  strip_tac >>
  `step_inst 0 ctx inst s = OK u` by simp[step_inst_non_invoke] >>
  `~is_terminator inst.inst_opcode` by simp[is_terminator_def] >>
  `~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    metis_tac[step_preserves_halted, step_preserves_control_flow] >>
  `op_taint (step_taint inst s u tn) (Var out) = {}` by
    metis_tac[call_output_untainted] >>
  `gas_path_ptr D 0 ctx fn PG (step_prov PG G inst u)
    (step_taint inst s u tn) (u with vs_inst_idx := SUC s.vs_inst_idx) 0
    (step_prov PG G inst u) (step_taint inst s u tn)
    (OK ((u with vs_inst_idx := SUC s.vs_inst_idx) with vs_inst_idx :=
      SUC (u with vs_inst_idx := SUC s.vs_inst_idx).vs_inst_idx))` by
    (irule assert_ok_path_ptr >> simp[] >> metis_tac[]) >>
  fs[] >>
  `(inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode)` by
    simp[is_terminator_def] >>
  drule_all gas_path_ptr_step >> simp[]
QED

Theorem call_assert_fail_path_ptr:
  inst.inst_opcode = CALL /\ inst.inst_outputs = [out] /\
  inst.inst_operands = [gas; addr; value; ao; az; ro; rz] /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst aid ASSERT [Var out] []) /\
  ptr_inst_ok D 0 0 ctx fn G tn inst s /\
  step_inst_base inst s = OK u /\ eval_operand (Var out) u = SOME 0w ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G inst u) (step_taint inst s u tn)
    (Abort Revert_abort (revert_state
      (set_returndata [] (u with vs_inst_idx := SUC s.vs_inst_idx))))
Proof
  strip_tac >>
  `step_inst 0 ctx inst s = OK u` by simp[step_inst_non_invoke] >>
  `~is_terminator inst.inst_opcode` by simp[is_terminator_def] >>
  `~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    metis_tac[step_preserves_halted, step_preserves_control_flow] >>
  `op_taint (step_taint inst s u tn) (Var out) = {}` by
    metis_tac[call_output_untainted] >>
  `gas_path_ptr D 0 ctx fn PG (step_prov PG G inst u)
    (step_taint inst s u tn) (u with vs_inst_idx := SUC s.vs_inst_idx) 0
    (step_prov PG G inst u) (step_taint inst s u tn)
    (Abort Revert_abort (revert_state
      (set_returndata [] (u with vs_inst_idx := SUC s.vs_inst_idx))))` by
    (irule assert_fail_path_ptr >> simp[] >> metis_tac[]) >>
  `(inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode)` by
    simp[is_terminator_def] >>
  drule_all gas_path_ptr_step >> simp[]
QED

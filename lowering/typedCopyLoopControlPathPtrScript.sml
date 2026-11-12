(* Counted execution boundaries for typed-copy loop control. *)
Theory typedCopyLoopControlPathPtr
Ancestors
 typedCopyLoopBackedgePtr typedCopyLoopHeaderPtr fragGasPathPtr exprSimPtrProps fragGasSeqPtr
 gasCount ptrSafeRun ptrDiscipline venomExecSemantics venomInst venomState
 finite_map words arithmetic list venomExecProofs

Theorem typed_copy_control_jump_path_ptr:
 !D lo ctx fn PG G tn s bb inst lbl.
 ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
 get_instruction bb s.vs_inst_idx = SOME inst /\
 inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> GAS /\
 is_terminator inst.inst_opcode /\
 ptr_inst_ok D lo 0 ctx fn G tn inst s /\
 step_inst_base inst s = OK (jump_to lbl s) ==>
 gas_path_ptr D lo ctx fn PG G tn s 0 G tn (OK (jump_to lbl s))
Proof
 rpt strip_tac >>
 `gas_path_ptr_edge D lo ctx fn PG G tn s 0 G tn (OK (jump_to lbl s))` by
  (rewrite_tac[gas_path_ptr_edge_def] >> simp[] >>
   qexists_tac `0:num` >>
   simp[step_inst_non_invoke, gas_count_step_def,
        ptr_safe_step_def] >> metis_tac[]) >>
 `~(jump_to lbl s).vs_halted` by simp[jump_to_def] >>
 metis_tac[gas_path_ptr_rules, ADD_CLAUSES]
QED

Theorem typed_copy_control_arith_path_ptr:
 !D ctx fn PG G tn s bb id opc ops out u.
 (opc = LT /\ (?v k. ops = [Var v; Lit k]) \/
  opc = MUL \/ opc = ISZERO) /\
 ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
 lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
 get_instruction bb s.vs_inst_idx = SOME (mk_inst id opc ops [out]) /\
 (!op. MEM op ops ==> op_taint tn op = {}) /\
 step_inst_base (mk_inst id opc ops [out]) s = OK u /\
 ~u.vs_halted /\ u.vs_requests = s.vs_requests /\
 u.vs_allocas = s.vs_allocas /\ u.vs_fmp = s.vs_fmp ==>
 gas_path_ptr D 0 ctx fn PG G tn s 0 (DRESTRICT G (COMPL {out}))
  (tn with t_var := tn.t_var |+ (out,{}))
  (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
 rpt strip_tac >>
 `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id opc ops [out]) s` by
  (gvs[] >>
   simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
        mk_inst_def, codegenRelTheory.source_memory_write_ranges_def,
        contextCodegenRelTheory.source_memory_read_ranges_def] >>
   simp[GSYM mk_inst_def, step_inst_non_invoke] >> metis_tac[]) >>
 `step_prov PG G (mk_inst id opc ops [out]) u = DRESTRICT G (COMPL {out}) /\
  step_taint (mk_inst id opc ops [out]) s u tn =
   (tn with t_var := tn.t_var |+ (out,{}))` by
  (irule typed_copy_loop_arith_ghost >> simp[] >> metis_tac[]) >>
 `~is_terminator (mk_inst id opc ops [out]).inst_opcode /\
  (mk_inst id opc ops [out]).inst_opcode <> INVOKE /\
  (mk_inst id opc ops [out]).inst_opcode <> GAS` by
   gvs[mk_inst_def, is_terminator_def] >>
 drule_all gas_path_ptr_one_step >>
 disch_then (qspec_then `PG` mp_tac) >> gvs[]
QED

Theorem typed_copy_control_scalar_path_ptr:
 !D ctx fn PG G tn s bb id opc ops out u.
 (opc = ADD \/ opc = ASSIGN) /\
 ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
 lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
 get_instruction bb s.vs_inst_idx = SOME (mk_inst id opc ops [out]) /\
 (!op. MEM op ops ==> op_taint tn op = {} /\ op_prov G op = NONE) /\
 step_inst_base (mk_inst id opc ops [out]) s = OK u /\
 ~u.vs_halted /\ u.vs_requests = s.vs_requests /\
 u.vs_allocas = s.vs_allocas /\ u.vs_fmp = s.vs_fmp ==>
 gas_path_ptr D 0 ctx fn PG G tn s 0
  (step_prov PG G (mk_inst id opc ops [out]) u)
  (step_taint (mk_inst id opc ops [out]) s u tn)
  (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
 rpt strip_tac >> irule gas_path_ptr_one_step >>
 gvs[mk_inst_def, is_terminator_def] >>
 simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
      mk_inst_def, codegenRelTheory.source_memory_write_ranges_def,
      contextCodegenRelTheory.source_memory_read_ranges_def] >>
 simp[GSYM mk_inst_def, step_inst_non_invoke] >> metis_tac[]
QED

Theorem typed_copy_loop_init_path_ptr:
 !D ctx fn PG G tn s bb pre id ctr cond.
 ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
 lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
 bb.bb_instructions = pre ++
  [mk_inst id ASSIGN [Lit 0w] [ctr]; mk_inst (id+1) JMP [Label cond] []] /\
 s.vs_inst_idx = LENGTH pre ==>
 gas_path_ptr D 0 ctx fn PG G tn s 0
  (DRESTRICT G (COMPL {ctr})) (tn with t_var := tn.t_var |+ (ctr,{}))
  (OK (jump_to cond
    ((update_var ctr 0w s) with vs_inst_idx := SUC s.vs_inst_idx)))
Proof
 rpt strip_tac >>
 qabbrev_tac `u = update_var ctr 0w s` >>
 qabbrev_tac `v = u with vs_inst_idx := SUC s.vs_inst_idx` >>
 qabbrev_tac `gg = step_prov PG G (mk_inst id ASSIGN [Lit 0w] [ctr]) u` >>
 qabbrev_tac `tt = step_taint (mk_inst id ASSIGN [Lit 0w] [ctr]) s u tn` >>
 `step_inst_base (mk_inst id ASSIGN [Lit 0w] [ctr]) s = OK u` by
  simp[step_inst_base_opcode_eqs, mk_inst_def, eval_operand_def, Abbr `u`] >>
 `gas_path_ptr D 0 ctx fn PG G tn s 0 gg tt (OK v)` by
  (simp[Abbr `gg`, Abbr `tt`, Abbr `v`, NoAsms] >>
   irule typed_copy_control_scalar_path_ptr >>
   simp[Abbr `u`, update_var_def, op_taint_def, op_prov_def] >>
   simp[get_instruction_def, EL_APPEND_EQN]) >>
 `gg = DRESTRICT G (COMPL {ctr}) /\
  tt = (tn with t_var := tn.t_var |+ (ctr,{}))` by
  (simp[Abbr `gg`, Abbr `tt`, Abbr `u`, step_prov_def, set_prov_def,
    out_prov_def, first_prov_def, op_prov_def, step_taint_def,
    set_var_taint_def, out_taint_def, eval_operand_def, op_taint_def,
    taint_component_equality, mk_inst_def, update_var_def,
    mem_taint_def, written_taint_def, store_taint_def, imm_taint_def,
    step_writes_def, codegenRelTheory.source_memory_write_ranges_def,
    adopt_reset_def, range_bytes_def, new_site_bytes_def,
    FLOOKUP_DEF, pred_setTheory.EXTENSION, SF CONJ_ss]) >>
 `gas_path_ptr D 0 ctx fn PG gg tt v 0 gg tt (OK (jump_to cond v))` by
  (irule typed_copy_control_jump_path_ptr >>
   (conj_tac >- simp[Abbr `v`, Abbr `u`, update_var_def]) >>
   qexistsl [`bb`, `mk_inst (id+1) JMP [Label cond] []`] >>
   simp[Abbr `v`, Abbr `u`, update_var_def, get_instruction_def,
     EL_APPEND_EQN, ADD1, mk_inst_def, is_terminator_def] >>
   simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
     codegenRelTheory.source_memory_write_ranges_def,
     contextCodegenRelTheory.source_memory_read_ranges_def,
     op_taint_def, step_inst_non_invoke, GSYM mk_inst_def,
     step_jmp_behavior, jump_to_def]) >>
 drule_all gas_path_ptr_then >> simp[Abbr `v`, Abbr `u`]
QED


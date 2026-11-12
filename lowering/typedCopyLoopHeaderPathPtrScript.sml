Theory typedCopyLoopHeaderPathPtr
Ancestors
  typedCopyLoopControlPathPtr typedCopyLoopHeaderPtr fragGasSeqPtr exprSimPtrProps
  ptrSafeRun ptrDiscipline venomInst venomExecSemantics venomState finite_map words arithmetic

(* Schematic endpoints keep ghost record normalization outside path matching. *)
Theorem typed_copy_header_arith_path_ptr:
 !D ctx fn PG G tn s bb id opc ops out u Gf tnf sf.
 (opc = LT \/ opc = MUL \/ opc = ISZERO) /\
 ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
 lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
 get_instruction bb s.vs_inst_idx = SOME (mk_inst id opc ops [out]) /\
 (!op. MEM op ops ==> op_taint tn op = {}) /\
 (opc = LT ==> !op. MEM op ops ==> op_prov G op = NONE) /\
 step_inst_base (mk_inst id opc ops [out]) s = OK u /\
 ~u.vs_halted /\ u.vs_requests = s.vs_requests /\
 u.vs_allocas = s.vs_allocas /\ u.vs_fmp = s.vs_fmp /\
 Gf = DRESTRICT G (COMPL {out}) /\
 tnf = (tn with t_var := tn.t_var |+ (out,{})) /\
 sf = (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
 gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf)
Proof
 rpt gen_tac >>
 disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
 `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id opc ops [out]) s` by
  (gvs[] >>
   simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
        mk_inst_def, codegenRelTheory.source_memory_write_ranges_def,
        contextCodegenRelTheory.source_memory_read_ranges_def] >>
   simp[GSYM mk_inst_def, step_inst_non_invoke] >>
   rpt strip_tac >> gvs[DISJ_IMP_THM, FORALL_AND_THM, op_prov_def, FLOOKUP_DEF] >> metis_tac[]) >>
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

Theorem typed_copy_header_path_ptr:
 !D ctx fn PG G tn s bb id ctr len lt done i n body_lbl exit_lbl.
 ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
 lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
 bb.bb_instructions =
 [mk_inst id LT [Var ctr; len] [lt];
  mk_inst (id+1) ISZERO [Var lt] [done];
  mk_inst (id+2) JNZ [Var done; Label exit_lbl; Label body_lbl] []] /\
 s.vs_inst_idx = 0 /\ lookup_var ctr s = SOME (n2w i) /\
 eval_operand len s = SOME (n2w n) /\
 op_taint tn (Var ctr) = {} /\ op_taint tn len = {} /\
 op_prov G (Var ctr) = NONE /\ op_prov G len = NONE /\
 i <= n /\ n < dimword(:256) /\ ctr <> lt /\ ctr <> done ==>
 ?Gf tnf sf.
 gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
 Gf = DRESTRICT (DRESTRICT G (COMPL {lt})) (COMPL {done}) /\
 tnf = (tn with t_var := (tn.t_var |+ (lt,{})) |+ (done,{})) /\
 sf = jump_to (if i < n then body_lbl else exit_lbl)
   (update_var done (bool_to_word (~(i < n)))
    (update_var lt (bool_to_word (i < n)) s) with vs_inst_idx := 2) /\
 sf.vs_current_bb = (if i < n then body_lbl else exit_lbl) /\
 sf.vs_inst_idx = 0 /\ ~sf.vs_halted /\
 lookup_var ctr sf = SOME (n2w i) /\
 sf.vs_memory = s.vs_memory /\ sf.vs_allocas = s.vs_allocas /\
 sf.vs_fmp = s.vs_fmp /\ sf.vs_requests = s.vs_requests /\
 tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
 tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
 (!p. p <> lt /\ p <> done ==>
   lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
   op_taint tnf (Var p) = op_taint tn (Var p))
Proof
 rpt strip_tac >>
 qabbrev_tac `u = update_var lt (bool_to_word (i < n)) s` >>
 qabbrev_tac `v = u with vs_inst_idx := SUC s.vs_inst_idx` >>
 qabbrev_tac `w = update_var done (bool_to_word (~(i < n))) v` >>
 qabbrev_tac `x = w with vs_inst_idx := SUC v.vs_inst_idx` >>
 qabbrev_tac `g1 = DRESTRICT G (COMPL {lt})` >>
 qabbrev_tac `g2 = DRESTRICT g1 (COMPL {done})` >>
 qabbrev_tac `t1 = tn with t_var := tn.t_var |+ (lt,{})` >>
 qabbrev_tac `t2 = t1 with t_var := t1.t_var |+ (done,{})` >>
 `step_inst_base (mk_inst id LT [Var ctr; len] [lt]) s = OK u` by
  (simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
    eval_operand_def, Abbr `u`, bool_to_word_def, w2n_n2w, LESS_MOD] >>
   `i < dimword(:256)` by decide_tac >> simp[]) >>
 `gas_path_ptr D 0 ctx fn PG G tn s 0 g1 t1 (OK v)` by
  (irule typed_copy_header_arith_path_ptr >> simp[] >>
   qexistsl [ `id`, `LT`, `[Var ctr; len]`, `lt`, `u`] >>
   simp[Abbr `g1`, Abbr `t1`, Abbr `v`, Abbr `u`, update_var_def,
     get_instruction_def, DISJ_IMP_THM, FORALL_AND_THM]) >>
 `step_inst_base (mk_inst (id+1) ISZERO [Var lt] [done]) v = OK w` by
  (simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure1_def,
    eval_operand_def, lookup_var_def, update_var_def,
    Abbr `v`, Abbr `u`, Abbr `w`, bool_to_word_def, FLOOKUP_UPDATE] >>
   Cases_on `i < n` >> simp[]) >>
 `gas_path_ptr D 0 ctx fn PG g1 t1 v 0 g2 t2 (OK x)` by
  (irule typed_copy_header_arith_path_ptr >>
   simp[Abbr `v`, Abbr `u`, update_var_def] >>
   qexistsl [ `id+1`, `ISZERO`, `[Var lt]`, `done`, `w`] >>
   simp[Abbr `g2`, Abbr `t2`, Abbr `x`, Abbr `w`,
     Abbr `t1`, update_var_def,
     op_taint_def, get_instruction_def, FLOOKUP_UPDATE] >>
   gvs[update_var_def]) >>
 `gas_path_ptr D 0 ctx fn PG g2 t2 x 0 g2 t2
   (OK (jump_to (if i < n then body_lbl else exit_lbl) x))` by
  (irule typed_copy_control_jump_path_ptr >>
   (conj_tac >- simp[Abbr `x`, Abbr `w`, Abbr `v`, Abbr `u`, update_var_def]) >>
   qexistsl [`bb`, `mk_inst (id+2) JNZ [Var done; Label exit_lbl; Label body_lbl] []`] >>
   simp[Abbr `x`, Abbr `w`, Abbr `v`, Abbr `u`, update_var_def,
     get_instruction_def, mk_inst_def, is_terminator_def] >>
   simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
     codegenRelTheory.source_memory_write_ranges_def,
     contextCodegenRelTheory.source_memory_read_ranges_def,
     GSYM mk_inst_def, step_inst_non_invoke,
     Abbr `t2`, Abbr `t1`, op_taint_def, FLOOKUP_UPDATE,
     step_inst_base_opcode_eqs, eval_operand_def, lookup_var_def,
     bool_to_word_def] >>
   Cases_on `i < n` >> simp[jump_to_def, update_var_def] >>
   rpt strip_tac >> Cases_on `op` >> gvs[]) >>
 `gas_path_ptr D 0 ctx fn PG G tn s 0 g2 t2
   (OK (jump_to (if i < n then body_lbl else exit_lbl) x))` by
  metis_tac[fragGasPathPtrTheory.gas_path_ptr_then, ADD_CLAUSES] >>
 qexistsl [`g2`, `t2`, `jump_to (if i < n then body_lbl else exit_lbl) x`] >>
 simp[Abbr `g2`, Abbr `t2`, Abbr `t1`, Abbr `x`, Abbr `w`,
   Abbr `v`, Abbr `u`, update_var_def, jump_to_def,
   lookup_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, Abbr `g1`,
   op_taint_def] >> rpt strip_tac >> gvs[lookup_var_def]
QED

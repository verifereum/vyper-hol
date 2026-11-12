Theory typedCopyLoopBackedgePathPtr
Ancestors
 typedCopyLoopControlPathPtr typedCopyLoopBackedgePtr fragGasPathPtr
 ptrSafeRun ptrDiscipline venomInst venomExecSemantics venomState venomExecProofs
 finite_map words arithmetic list

Theorem typed_copy_loop_backedge_path_ptr:
 !D ctx fn PG G tn s bb pre id ctr tmp cond i.
 lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
 bb.bb_instructions = pre ++
 [mk_inst id ADD [Var ctr;Lit 1w] [tmp];
  mk_inst (id+1) ASSIGN [Var tmp] [ctr];
  mk_inst (id+2) JMP [Label cond] []] /\
 s.vs_inst_idx = LENGTH pre /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
 lookup_var ctr s = SOME (n2w i) /\ ctr <> tmp /\
 FLOOKUP G ctr = NONE /\ op_taint tn (Var ctr) = {} ==>
 ?Gf tnf sf.
 gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
 sf = jump_to cond (update_var ctr (n2w (i+1))
   (update_var tmp (n2w (i+1)) s)) /\
 Gf = DRESTRICT (DRESTRICT G (COMPL {tmp})) (COMPL {ctr}) /\
 tnf = (tn with t_var := (tn.t_var |+ (tmp,{})) |+ (ctr,{})) /\
 sf.vs_current_bb = cond /\ sf.vs_inst_idx = 0 /\ ~sf.vs_halted /\
 sf.vs_allocas = s.vs_allocas /\ sf.vs_fmp = s.vs_fmp /\
 sf.vs_requests = s.vs_requests /\ tnf.t_imm = tn.t_imm /\
 lookup_var ctr sf = SOME (n2w (i+1)) /\
 FLOOKUP Gf ctr = NONE /\ op_taint tnf (Var ctr) = {} /\
 sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
 tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
 (!p. p <> ctr /\ p <> tmp ==>
  lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
  op_taint tnf (Var p) = op_taint tn (Var p) /\
  (!n. ptr_covers G tn p s n ==> ptr_covers Gf tnf p sf n))
Proof
 rpt strip_tac >>
 qabbrev_tac `u = update_var tmp (n2w (i+1)) s` >>
 qabbrev_tac `v = u with vs_inst_idx := SUC s.vs_inst_idx` >>
 qabbrev_tac `w = update_var ctr (n2w (i+1)) v` >>
 qabbrev_tac `x = w with vs_inst_idx := SUC v.vs_inst_idx` >>
 qabbrev_tac `g1 = DRESTRICT G (COMPL {tmp})` >>
 qabbrev_tac `g2 = DRESTRICT g1 (COMPL {ctr})` >>
 qabbrev_tac `t1 = tn with t_var := tn.t_var |+ (tmp,{})` >>
 qabbrev_tac `t2 = t1 with t_var := t1.t_var |+ (ctr,{})` >>
 `gas_path_ptr D 0 ctx fn PG G tn s 0 g1 t1 (OK v)` by
  suspend "add" >>
 `gas_path_ptr D 0 ctx fn PG g1 t1 v 0 g2 t2 (OK x)` by
  suspend "assign" >>
 `gas_path_ptr D 0 ctx fn PG g2 t2 x 0 g2 t2 (OK (jump_to cond x))` by
  suspend "jump" >>
 `gas_path_ptr D 0 ctx fn PG G tn s 0 g2 t2 (OK (jump_to cond x))` by
  metis_tac[gas_path_ptr_then, ADD_CLAUSES] >>
 qexistsl [`g2`, `t2`, `jump_to cond x`] >> simp[] >>
 simp[Abbr `g2`, Abbr `g1`, Abbr `t2`, Abbr `t1`,
   Abbr `x`, Abbr `w`, Abbr `v`, Abbr `u`,
   jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
   FLOOKUP_DRESTRICT, op_taint_def, bodyPtrDefsTheory.ptr_covers_def] >>
 rpt strip_tac >> gvs[]
QED

Resume typed_copy_loop_backedge_path_ptr[add]:
 qabbrev_tac `gg = step_prov PG G (mk_inst id ADD [Var ctr;Lit 1w] [tmp]) u` >>
 qabbrev_tac `tt = step_taint (mk_inst id ADD [Var ctr;Lit 1w] [tmp]) s u tn` >>
 `gas_path_ptr D 0 ctx fn PG G tn s 0 gg tt (OK v)` by
  (simp[Abbr `gg`, Abbr `tt`, Abbr `v`, NoAsms] >>
   irule typed_copy_control_scalar_path_ptr >>
   simp[Abbr `u`, update_var_def] >>
   simp[op_taint_def, op_prov_def, DISJ_IMP_THM, FORALL_AND_THM,
     get_instruction_def, EL_APPEND_EQN, step_inst_base_opcode_eqs,
     mk_inst_def, exec_pure2_def, eval_operand_def, word_add_n2w,
     update_var_def] >> gvs[op_taint_def]) >>
 `gg = g1 /\ tt = t1` by
  (simp[Abbr `gg`, Abbr `tt`, Abbr `g1`, Abbr `t1`, Abbr `u`,
    step_prov_def, set_prov_def, out_prov_def, first_prov_def,
    op_prov_def, step_taint_def, set_var_taint_def, out_taint_def,
    eval_operand_def, op_taint_def, taint_component_equality,
    mk_inst_def, update_var_def, mem_taint_def, written_taint_def,
    store_taint_def, imm_taint_def, step_writes_def,
    codegenRelTheory.source_memory_write_ranges_def, adopt_reset_def,
    range_bytes_def, new_site_bytes_def, FLOOKUP_DEF,
    pred_setTheory.EXTENSION, SF CONJ_ss] >> gvs[op_taint_def, FLOOKUP_DEF]) >>
 gvs[]
QED

Resume typed_copy_loop_backedge_path_ptr[assign]:
 qabbrev_tac `gg = step_prov PG g1 (mk_inst (id+1) ASSIGN [Var tmp] [ctr]) w` >>
 qabbrev_tac `tt = step_taint (mk_inst (id+1) ASSIGN [Var tmp] [ctr]) v w t1` >>
 `gas_path_ptr D 0 ctx fn PG g1 t1 v 0 gg tt (OK x)` by
  (simp[Abbr `gg`, Abbr `tt`, Abbr `x`, NoAsms] >>
   irule typed_copy_control_scalar_path_ptr >>
   simp[Abbr `w`, Abbr `v`, Abbr `u`, update_var_def,
     Abbr `t1`, Abbr `g1`, op_taint_def, op_prov_def,
     FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, get_instruction_def,
     EL_APPEND_EQN, step_inst_base_opcode_eqs, mk_inst_def,
     eval_operand_def, lookup_var_def, ADD1]) >>
 `gg = g2 /\ tt = t2` by
  (simp[Abbr `gg`, Abbr `tt`, Abbr `g2`, Abbr `t2`, Abbr `w`,
    step_prov_def, set_prov_def, out_prov_def, first_prov_def,
    op_prov_def, step_taint_def, set_var_taint_def, out_taint_def,
    eval_operand_def, op_taint_def, taint_component_equality,
    mk_inst_def, update_var_def, mem_taint_def, written_taint_def,
    store_taint_def, imm_taint_def, step_writes_def,
    codegenRelTheory.source_memory_write_ranges_def, adopt_reset_def,
    range_bytes_def, new_site_bytes_def, FLOOKUP_DEF,
    pred_setTheory.EXTENSION, SF CONJ_ss,
    Abbr `g1`, Abbr `t1`, Abbr `v`, Abbr `u`, FLOOKUP_DRESTRICT,
    FLOOKUP_UPDATE, lookup_var_def]) >> gvs[]
QED

Resume typed_copy_loop_backedge_path_ptr[jump]:
 irule typed_copy_control_jump_path_ptr >>
 (conj_tac >- simp[Abbr `x`, Abbr `w`, Abbr `v`, Abbr `u`, update_var_def]) >>
 qexistsl [`bb`, `mk_inst (id+2) JMP [Label cond] []`] >>
 simp[Abbr `x`, Abbr `w`, Abbr `v`, Abbr `u`, update_var_def,
   get_instruction_def, EL_APPEND_EQN, ADD1, mk_inst_def, is_terminator_def] >>
 simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
   codegenRelTheory.source_memory_write_ranges_def,
   contextCodegenRelTheory.source_memory_read_ranges_def,
   op_taint_def, step_inst_non_invoke, GSYM mk_inst_def,
   step_jmp_behavior, jump_to_def]
QED

Finalise typed_copy_loop_backedge_path_ptr

(* Typed-array loop backedge at the recursive child's actual final block. *)
Theory typedCopyLoopBackedgePtr
Ancestors typedCopyLoopHeaderPtr venomExecSemantics venomInst venomState
  words finite_map arithmetic

Theorem typed_copy_loop_backedge_frame:
  !G tn s ctr tmp i cond sf Gf tnf.
    sf = jump_to cond (update_var ctr (n2w (i+1))
           (update_var tmp (n2w (i+1)) s)) /\
    Gf = DRESTRICT (DRESTRICT G (COMPL {tmp})) (COMPL {ctr}) /\
    tnf = (tn with t_var := (tn.t_var |+ (tmp,{})) |+ (ctr,{})) /\
    ctr <> tmp ==>
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
  gvs[bodyPtrDefsTheory.ptr_covers_def, lookup_var_def, update_var_def,
      jump_to_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT,
      ptrDisciplineTheory.op_taint_def]
QED

Theorem typed_copy_loop_backedge_run:
  !ctx fn s bb pre id ctr tmp cond i n sf.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    bb.bb_instructions = pre ++
      [mk_inst id ADD [Var ctr; Lit 1w] [tmp];
       mk_inst (id+1) ASSIGN [Var tmp] [ctr];
       mk_inst (id+2) JMP [Label cond] []] /\
    s.vs_inst_idx = LENGTH pre /\ ~s.vs_halted /\
    lookup_var ctr s = SOME (n2w i) /\ i < n /\ n < dimword(:256) /\
    ctr <> tmp /\
    sf = jump_to cond (update_var ctr (n2w (i+1))
           (update_var tmp (n2w (i+1)) s)) ==>
    !fuel. run_from (SUC fuel) ctx fn s = run_blocks (SUC fuel) ctx fn sf
Proof
  rpt strip_tac >>
  simp[fragExecTheory.run_from_def, Once exec_block_def, get_instruction_def,
       step_inst_non_invoke, listTheory.EL_APPEND_EQN, arithmeticTheory.ADD1] >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs, mk_inst_def, instruction_accessors,
    instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure2_def, eval_operand_def, word_add_n2w] >>
  simp[Once exec_block_def, get_instruction_def, update_var_def,
       step_inst_non_invoke, is_terminator_def, listTheory.EL_APPEND_EQN, arithmeticTheory.ADD1] >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs, mk_inst_def, instruction_accessors,
    instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
  simp[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
  simp[Once exec_block_def, get_instruction_def, update_var_def,
       step_inst_non_invoke, is_terminator_def, listTheory.EL_APPEND_EQN, arithmeticTheory.ADD1] >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs, mk_inst_def, instruction_accessors,
    instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
  simp[eval_operand_def, jump_to_def]
QED

Theorem scalar_backedge_prov[local]:
  !PG G s id root out k w.
    FLOOKUP G root = NONE ==>
    step_prov PG G (mk_inst id ADD [Var root; Lit k] [out]) (update_var out w s) =
      DRESTRICT G (COMPL {out}) /\
    step_prov PG G (mk_inst id ASSIGN [Var root] [out]) (update_var out w s) =
      DRESTRICT G (COMPL {out})
Proof
  simp[ptrDisciplineTheory.step_prov_def, ptrDisciplineTheory.set_prov_def,
       ptrDisciplineTheory.out_prov_def, ptrDisciplineTheory.first_prov_def,
       ptrDisciplineTheory.op_prov_def, mk_inst_def]
QED

Theorem scalar_backedge_ghost[local]:
  !tn s id root out k w.
    op_taint tn (Var root) = {} ==>
    step_taint (mk_inst id ADD [Var root; Lit k] [out]) s (update_var out w s) tn =
      (tn with t_var := tn.t_var |+ (out,{})) /\
    step_taint (mk_inst id ASSIGN [Var root] [out]) s (update_var out w s) tn =
      (tn with t_var := tn.t_var |+ (out,{}))
Proof
  rpt gen_tac >> strip_tac >>
  `new_site_bytes s (update_var out w s) = {}` by
    simp[ptrDisciplineTheory.new_site_bytes_def, update_var_def,
         FLOOKUP_DEF, pred_setTheory.EXTENSION, SF CONJ_ss] >>
  gvs[] >>
  simp[ptrDisciplineTheory.step_prov_def, ptrDisciplineTheory.set_prov_def,
       ptrDisciplineTheory.out_prov_def, ptrDisciplineTheory.first_prov_def,
       ptrDisciplineTheory.op_prov_def, ptrDisciplineTheory.step_taint_def,
       ptrDisciplineTheory.set_var_taint_def, mk_inst_def,
       ptrDisciplineTheory.mem_taint_def, ptrDisciplineTheory.step_writes_def,
       codegenRelTheory.source_memory_write_ranges_def,
       ptrDisciplineTheory.written_taint_def, ptrDisciplineTheory.store_taint_def,
       ptrDisciplineTheory.adopt_reset_def, ptrDisciplineTheory.out_taint_def,
       ptrDisciplineTheory.op_taint_def, ptrDisciplineTheory.imm_taint_def,
       ptrDisciplineTheory.range_bytes_def,
       ptrDisciplineTheory.taint_component_equality] >>
  Cases_on `lookup_var root s` >> gvs[eval_operand_def,
    ptrDisciplineTheory.op_taint_def]
QED

Theorem typed_copy_loop_backedge_ghost_run:
  !ctx fn PG G tn s bb pre id ctr tmp cond i n sf Gf tnf target.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    bb.bb_instructions = pre ++
      [mk_inst id ADD [Var ctr; Lit 1w] [tmp];
       mk_inst (id+1) ASSIGN [Var tmp] [ctr];
       mk_inst (id+2) JMP [Label cond] []] /\
    s.vs_inst_idx = LENGTH pre /\ ~s.vs_halted /\
    lookup_var ctr s = SOME (n2w i) /\ i < n /\ n < dimword(:256) /\ ctr <> tmp /\
    sf = jump_to cond (update_var ctr (n2w (i+1))
           (update_var tmp (n2w (i+1)) s)) /\
    FLOOKUP G ctr = NONE /\ op_taint tn (Var ctr) = {} /\
    lookup_block cond fn.fn_blocks = SOME target /\
    phi_prefix_length target.bb_instructions = 0 /\
    Gf = DRESTRICT (DRESTRICT G (COMPL {tmp})) (COMPL {ctr}) /\
    tnf = (tn with t_var := (tn.t_var |+ (tmp,{})) |+ (ctr,{})) ==>
    !fuel. ghost_run (SUC fuel) ctx fn PG G tn s =
      ghost_run fuel ctx fn PG Gf tnf sf
Proof
  rpt strip_tac >>
  simp[ptrSafeRunTheory.ghost_run_def,
       Once ptrSafeRunTheory.ghost_block_def, get_instruction_def,
       step_inst_non_invoke, listTheory.EL_APPEND_EQN, arithmeticTheory.ADD1] >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs, mk_inst_def, instruction_accessors,
    instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure2_def, eval_operand_def, word_add_n2w, is_terminator_def] >>
  simp[ptrSafeRunTheory.ghost_step_def, mk_inst_def,
       step_inst_non_invoke, exec_pure2_def, eval_operand_def,
       word_add_n2w, SRULE [mk_inst_def] scalar_backedge_ghost,
       SRULE [mk_inst_def] scalar_backedge_prov] >>
  simp[Once ptrSafeRunTheory.ghost_block_def, get_instruction_def,
       ptrSafeRunTheory.ghost_step_def, step_inst_non_invoke, update_var_def,
       listTheory.EL_APPEND_EQN, arithmeticTheory.ADD1] >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs, mk_inst_def, instruction_accessors,
    instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
  simp[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE, is_terminator_def,
       SRULE [update_var_def, mk_inst_def] scalar_backedge_ghost,
       FLOOKUP_DRESTRICT, ptrDisciplineTheory.op_taint_def] >>
  simp[exec_pure2_def, eval_operand_def, mk_inst_def, word_add_n2w,
       SRULE [mk_inst_def] scalar_backedge_ghost,
       SRULE [mk_inst_def] scalar_backedge_prov,
       FLOOKUP_DRESTRICT, FLOOKUP_UPDATE, ptrDisciplineTheory.op_taint_def] >>
  simp[Once ptrSafeRunTheory.ghost_block_def, get_instruction_def,
       step_inst_non_invoke, update_var_def,
       listTheory.EL_APPEND_EQN, arithmeticTheory.ADD1] >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs, mk_inst_def, instruction_accessors,
    instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
  simp[eval_operand_def, is_terminator_def, jump_to_def] >>
  gvs[update_var_def, jump_to_def] >>
  qmatch_goalsub_abbrev_tac `entry_prov fn sj gg` >>
  qmatch_goalsub_abbrev_tac `entry_taint_vars fn sj tt` >>
  `entry_prov fn sj gg = gg /\ entry_taint_vars fn sj tt = tt` by
    (irule typedCopyArrayPtrTheory.entry_ghost_no_phi >>
     simp[Abbr `sj`] >> metis_tac[]) >>
  simp[Once ptrSafeRunTheory.ghost_blocks_def, Abbr `sj`, GSYM arithmeticTheory.ADD1] >>
  Cases_on `target.bb_instructions`
  >- simp[eval_phis_def] >>
  Cases_on `h.inst_opcode = PHI` >>
  gvs[phi_prefix_length_def, eval_phis_def]
QED

Theorem scalar_backedge_check[local]:
  !D ctx fn G tn s id opc ops outs s' fuel.
    (opc = ADD \/ opc = ASSIGN \/ opc = JMP) /\
    (!op. MEM op ops ==> op_taint tn op = {}) /\
    ~ctx_has_dalloca ctx /\
    step_inst_base (mk_inst id opc ops outs) s = OK s' /\
    s'.vs_requests = s.vs_requests ==>
    ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id opc ops outs) s
Proof
  rpt strip_tac >> gvs[] >>
  simp[ptrSafeRunTheory.ptr_inst_ok_def, ptrDisciplineTheory.access_ok_def,
       ptrDisciplineTheory.taint_ok_def, ptrDisciplineTheory.allocas_from_def,
       mk_inst_def, codegenRelTheory.source_memory_write_ranges_def,
       contextCodegenRelTheory.source_memory_read_ranges_def] >>
  simp[GSYM mk_inst_def, step_inst_non_invoke] >> metis_tac[]
QED

Theorem typed_copy_loop_backedge_ptr_safe:
  !D ctx fn PG G tn s bb pre id ctr tmp cond i n sf Gf tnf target.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    bb.bb_instructions = pre ++
      [mk_inst id ADD [Var ctr; Lit 1w] [tmp];
       mk_inst (id+1) ASSIGN [Var tmp] [ctr];
       mk_inst (id+2) JMP [Label cond] []] /\
    s.vs_inst_idx = LENGTH pre /\ ~s.vs_halted /\
    lookup_var ctr s = SOME (n2w i) /\ i < n /\ n < dimword(:256) /\ ctr <> tmp /\
    sf = jump_to cond (update_var ctr (n2w (i+1))
           (update_var tmp (n2w (i+1)) s)) /\
    FLOOKUP G ctr = NONE /\ op_taint tn (Var ctr) = {} /\
    lookup_block cond fn.fn_blocks = SOME target /\
    phi_prefix_length target.bb_instructions = 0 /\
    Gf = DRESTRICT (DRESTRICT G (COMPL {tmp})) (COMPL {ctr}) /\
    tnf = (tn with t_var := (tn.t_var |+ (tmp,{})) |+ (ctr,{})) /\
    ~ctx_has_dalloca ctx ==>
    !fuel. ptr_safe_run D 0 fuel ctx fn PG Gf tnf sf ==>
      ptr_safe_run D 0 (SUC fuel) ctx fn PG G tn s
Proof
  rpt strip_tac >>
  simp[ptrSafeRunTheory.ptr_safe_run_def,
       Once ptrSafeRunTheory.ptr_safe_block_def, get_instruction_def,
       ptrSafeRunTheory.ptr_safe_step_def,
       step_inst_non_invoke, listTheory.EL_APPEND_EQN, arithmeticTheory.ADD1] >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs, mk_inst_def, instruction_accessors,
    instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure2_def, eval_operand_def, word_add_n2w, is_terminator_def] >>
  conj_tac
  >- (irule (SRULE [mk_inst_def] scalar_backedge_check) >>
      simp[] >> conj_tac
      >- (rpt strip_tac >> gvs[ptrDisciplineTheory.op_taint_def]) >>
      asm_simp_tac bool_ss [step_inst_base_opcode_eqs, instruction_accessors, instruction_accfupds,
        combinTheory.K_THM, opcode_case_def] >>
      simp[exec_pure2_def, eval_operand_def, update_var_def]) >>
  simp[ptrSafeRunTheory.ghost_step_def, mk_inst_def,
       step_inst_non_invoke, exec_pure2_def, eval_operand_def,
       word_add_n2w, SRULE [mk_inst_def] scalar_backedge_ghost,
       SRULE [mk_inst_def] scalar_backedge_prov] >>
  simp[Once ptrSafeRunTheory.ptr_safe_block_def, get_instruction_def,
       ptrSafeRunTheory.ptr_safe_step_def,
       ptrSafeRunTheory.ghost_step_def, step_inst_non_invoke, update_var_def,
       listTheory.EL_APPEND_EQN, arithmeticTheory.ADD1] >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs, mk_inst_def, instruction_accessors,
    instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
  simp[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE, is_terminator_def,
       SRULE [update_var_def, mk_inst_def] scalar_backedge_ghost,
       FLOOKUP_DRESTRICT, ptrDisciplineTheory.op_taint_def] >>
  simp[exec_pure2_def, eval_operand_def, mk_inst_def, word_add_n2w,
       SRULE [mk_inst_def] scalar_backedge_ghost,
       SRULE [mk_inst_def] scalar_backedge_prov,
       FLOOKUP_DRESTRICT, FLOOKUP_UPDATE, ptrDisciplineTheory.op_taint_def] >>
  conj_tac
  >- (irule (SRULE [mk_inst_def] scalar_backedge_check) >>
      simp[ptrDisciplineTheory.op_taint_def, FLOOKUP_UPDATE] >>
      asm_simp_tac bool_ss [step_inst_base_opcode_eqs, instruction_accessors, instruction_accfupds,
        combinTheory.K_THM, opcode_case_def] >>
      simp[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE, update_var_def]) >>
  simp[exec_pure2_def, eval_operand_def, mk_inst_def, word_add_n2w,
       SRULE [mk_inst_def] scalar_backedge_ghost,
       SRULE [mk_inst_def] scalar_backedge_prov,
       FLOOKUP_DRESTRICT, FLOOKUP_UPDATE, ptrDisciplineTheory.op_taint_def] >>
  simp[Once ptrSafeRunTheory.ptr_safe_block_def, get_instruction_def,
       ptrSafeRunTheory.ptr_safe_step_def,
       step_inst_non_invoke, update_var_def,
       listTheory.EL_APPEND_EQN, arithmeticTheory.ADD1] >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs, mk_inst_def, instruction_accessors,
    instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
  simp[eval_operand_def, is_terminator_def, jump_to_def] >>
  conj_tac
  >- (irule (SRULE [mk_inst_def] scalar_backedge_check) >>
      simp[] >> conj_tac
      >- (rpt strip_tac >> gvs[ptrDisciplineTheory.op_taint_def]) >>
      asm_simp_tac bool_ss [step_inst_base_opcode_eqs, instruction_accessors, instruction_accfupds,
        combinTheory.K_THM, opcode_case_def] >>
      simp[eval_operand_def, jump_to_def]) >>
  gvs[update_var_def, jump_to_def] >>
  qmatch_goalsub_abbrev_tac `entry_prov fn sj gg` >>
  qmatch_goalsub_abbrev_tac `entry_taint_vars fn sj tt` >>
  `entry_prov fn sj gg = gg /\ entry_taint_vars fn sj tt = tt` by
    (irule typedCopyArrayPtrTheory.entry_ghost_no_phi >>
     simp[Abbr `sj`] >> metis_tac[]) >>
  simp[Once ptrSafeRunTheory.ptr_safe_blocks_def, Abbr `sj`, GSYM arithmeticTheory.ADD1] >>
  qpat_x_assum `ptr_safe_run _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[ptrSafeRunTheory.ptr_safe_run_def, GSYM arithmeticTheory.ADD1] >>
  Cases_on `target.bb_instructions`
  >- simp[eval_phis_def] >>
  Cases_on `h.inst_opcode = PHI` >>
  gvs[phi_prefix_length_def, eval_phis_def]
QED

(* Compiler-facing audit (no duplicate layout specialization).
   compile_copy_sarray_typed_loop_layout identifies the backedge block as
   HD sz.cs_blocks, with pre = se.cs_current_insts, id = se.cs_next_id,
   tmp = "%" ++ toString se.cs_next_var and the generated cond label.
   typed_copy_loop_slice_locations locates this block in fn from fn_has_code;
   compile_copy_sarray_typed_loop_no_phi locates the PHI-free cond target.
   The runtime child postcondition must still supply current_bb =
   se.cs_current_bb, inst_idx = LENGTH pre, nonhaltedness, the counter lookup,
   i < count < dimword(:256), and the clean provenance-free scalar invariant.
   Name separation ctr <> tmp comes from compile-time counter growth, not
   runtime freshness. The context premise is ~ctx_has_dalloca ctx. The
   continuation uses precisely sf, Gf and tnf in the generic results above.
   None of these lemmas assumes that the child's final block is its entry,
   that pre is empty, or that tmp has no stale runtime binding. *)

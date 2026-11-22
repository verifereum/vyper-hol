(* Erase the cursor increments of an observed straight-line prefix. *)
Theory createSizeStraightPrefix
Ancestors
  exprLoweringProps fragExec fragGasOrigin instIdxIndep venomExecSemantics venomInst
  venomState venomInstProofs1 list rich_list arithmetic relation
  compileEnv emitHelper loweringShapeRules builtinCreate context

Theorem create_straight_taken_edge[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
  gas_origin_edge F explicit ctx fn s ms (OK u) ==>
  ?v. step_inst_base i s = OK v /\
      u = (v with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  simp[gas_origin_edge_def, step_inst_non_invoke, exit_result_def] >>
  rpt strip_tac >> gvs[step_inst_non_invoke, exit_result_def] >>
  qpat_x_assum `OK u = _` (assume_tac o SYM) >> fs[exit_result_def]
QED

Theorem create_straight_prefix_run:
  !code s t R fn ctx explicit bb.
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
    t.vs_current_bb = s.vs_current_bb /\
    t.vs_inst_idx = s.vs_inst_idx + LENGTH code /\
    (!u v. R u v ==> ?ms. gas_origin_edge F explicit ctx fn u ms (OK v)) /\
    (!u v. u.vs_current_bb = t.vs_current_bb /\ u.vs_inst_idx = t.vs_inst_idx ==> ~R u v) /\
    RTC R s t ==>
    run_inst_seq code s = OK (t with vs_inst_idx := s.vs_inst_idx)
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (qpat_x_assum `RTC R s t` (strip_assume_tac o ONCE_REWRITE_RULE[RTC_CASES1])
      >- (qpat_x_assum `s = t` SUBST_ALL_TAC >> simp[run_inst_seq_def]) >>
      fs[] >> metis_tac[]) >>
  `s <> t` by (strip_tac >> qpat_x_assum `s = t` SUBST_ALL_TAC >> fs[]) >>
  qpat_x_assum `RTC R s t` (strip_assume_tac o ONCE_REWRITE_RULE[RTC_CASES1]) >>
  rename1 `R s u` >>
  `h.inst_opcode <> INVOKE /\ ~is_terminator h.inst_opcode /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code` by fs[] >>
  `?rest. DROP s.vs_inst_idx bb.bb_instructions = h::(code ++ rest)` by
    (qpat_x_assum `h::code ≼ _` (mp_tac o REWRITE_RULE[IS_PREFIX_APPEND]) >> simp[]) >>
  drule DROP_EQ_CONS >> simp[] >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME h` by simp[get_instruction_def] >>
  `?v. step_inst_base h s = OK v /\ u = (v with vs_inst_idx := SUC s.vs_inst_idx)` by
    metis_tac[create_straight_taken_edge] >>
  `v.vs_current_bb = s.vs_current_bb /\ v.vs_inst_idx = s.vs_inst_idx` by
    metis_tac[step_inst_base_preserves_all,step_inst_base_preserves_inst_idx] >>
  `run_inst_seq code u = OK (t with vs_inst_idx := u.vs_inst_idx)` by
    (first_x_assum (qspecl_then [`u`,`t`,`R`,`fn`,`ctx`,`explicit`,`bb`] mp_tac) >>
     simp[IS_PREFIX_APPEND, ADD_CLAUSES] >> metis_tac[ADD_CLAUSES, LENGTH]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) code` by fs[EVERY_MEM] >>
  `v = (u with vs_inst_idx := s.vs_inst_idx)` by
    (simp[] >> qpat_assum `v.vs_inst_idx = _`
      (fn th => PURE_ONCE_REWRITE_TAC[GSYM th]) >> simp[]) >>
  qpat_x_assum `u = (v with vs_inst_idx := _)` kall_tac >>
  simp[Once run_inst_seq_def] >>
  qpat_x_assum `v = (u with vs_inst_idx := _)` SUBST1_TAC >>
  simp[run_inst_seq_inst_idx, exec_result_map_def]
QED

Theorem create_copy_preparation_code:
  emit_op EXTCODESIZE [target] c = (code,a1) /\
  emit_void ASSERT [code] a1 = ((),a2) /\
  emit_op SHL [Lit 56w;code] a2 = (shifted,a3) /\
  emit_op OR [Lit 0x620000003d81600b3d39f3w;shifted] a3 = (preamble,a4) /\
  emit_op ADD [code;Lit 32w] a4 = (request,a5) /\
  compile_alloc_dynamic request a5 = (alloc_ptr,a6) /\
  emit_void MSTORE [alloc_ptr;preamble] a6 = ((),a7) /\
  emit_op ADD [alloc_ptr;Lit 32w] a7 = (code_dst,a8) /\
  emit_void EXTCODECOPY [target;code_dst;Lit 0w;code] a8 = ((),a9) /\
  emit_op ADD [alloc_ptr;Lit 21w] a9 = (buf,a10) /\
  emit_op ADD [code;Lit 11w] a10 = (len,sc) ==>
  (!salt rof result sb. compile_create_dispatch buf len value salt rof sc = (result,sb) ==>
    compile_create_copy target value salt rof c = (result,sb)) /\
  cs_extends c sc /\ sc.cs_current_bb = c.cs_current_bb /\
  sc.cs_current_insts = c.cs_current_insts ++ emitted_insts c sc /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts c sc) /\
  EVERY (\z. c.cs_next_id <= z.cs_next_id /\ z.cs_next_id <= sc.cs_next_id)
    [c;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;sc]
Proof
  strip_tac >> conj_tac
  >- simp[compile_create_copy_def, compile_create_dispatch_def,
          comp_bind_def, comp_ignore_bind_def] >>
  fs[compile_alloc_dynamic_def, emit_op_eq, emit_void_eq] >> gvs[] >>
  SIMP_TAC pure_ss [cs_extends_def, emitted_insts_def, compile_state_accfupds,
    GSYM APPEND_ASSOC, APPEND, DROP_LENGTH_APPEND] >>
  simp[DROP_APPEND, DROP_LENGTH_TOO_LONG, mk_inst_def, is_terminator_def]
QED

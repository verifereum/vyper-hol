(* Executed test of the concrete typed-array loop. *)
Theory typedCopyLoopHeaderPtr
Ancestors typedCopyLoopLayoutPtr typedCopyOffsetPtr venomExecSemantics
  venomInst venomState words finite_map arithmetic

Theorem typed_copy_loop_test_steps:
  !s ctr lt done id i n body_lbl exit_lbl.
    lookup_var ctr s = SOME (n2w i) /\
    i <= n /\ n < dimword(:256) /\ ctr <> lt /\ ctr <> done ==>
    ?s1 s2.
      s1 = update_var lt (bool_to_word (i < n)) s /\
      s2 = update_var done (bool_to_word (~(i < n))) s1 /\
      step_inst_base (mk_inst id LT [Var ctr; Lit (n2w n)] [lt]) s = OK s1 /\
      step_inst_base (mk_inst (id+1) ISZERO [Var lt] [done]) s1 = OK s2 /\
      step_inst_base (mk_inst (id+2) JNZ
        [Var done; Label exit_lbl; Label body_lbl] []) s2 =
        OK (jump_to (if i < n then body_lbl else exit_lbl) s2) /\
      lookup_var ctr s2 = lookup_var ctr s /\ s2.vs_memory = s.vs_memory
Proof
  rpt strip_tac >>
  `i < dimword(:256)` by decide_tac >>
  simp[] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[mk_inst_def, instruction_accessors,
                  instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure2_def, exec_pure1_def, eval_operand_def,
       bool_to_word_def, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE, w2n_n2w, LESS_MOD] >>
  Cases_on `i < n` >> gvs[lookup_var_def]
QED

(* These operations overwrite one result without touching memory or the
   other ghost entries, including on loop reentry with stale temporaries. *)
Theorem typed_copy_loop_arith_ghost:
  !PG G tn s id opc ops out s'.
    (opc = LT \/ opc = MUL \/ opc = ISZERO) /\
    s'.vs_allocas = s.vs_allocas /\ s'.vs_fmp = s.vs_fmp ==>
    step_prov PG G (mk_inst id opc ops [out]) s' =
      DRESTRICT G (COMPL {out}) /\
    step_taint (mk_inst id opc ops [out]) s s' tn =
      (tn with t_var := tn.t_var |+ (out,{}))
Proof
  rpt gen_tac >> strip_tac >>
  `new_site_bytes s s' = {}` by
    simp[ptrDisciplineTheory.new_site_bytes_def, update_var_def,
         FLOOKUP_DEF, pred_setTheory.EXTENSION, SF CONJ_ss] >>
  gvs[] >>
  (simp[ptrDisciplineTheory.step_prov_def, ptrDisciplineTheory.set_prov_def,
       ptrDisciplineTheory.out_prov_def, ptrDisciplineTheory.step_taint_def,
       ptrDisciplineTheory.set_var_taint_def, mk_inst_def,
       ptrDisciplineTheory.mem_taint_def, ptrDisciplineTheory.step_writes_def,
       codegenRelTheory.source_memory_write_ranges_def,
       ptrDisciplineTheory.written_taint_def,
       ptrDisciplineTheory.store_taint_def, ptrDisciplineTheory.adopt_reset_def,
       ptrDisciplineTheory.imm_taint_def, ptrDisciplineTheory.range_bytes_def,
       ptrDisciplineTheory.taint_component_equality] >>
  Cases_on `ops` >> simp[ptrDisciplineTheory.out_taint_def] >>
  Cases_on `t`
  >- (simp[ptrDisciplineTheory.out_taint_def] >>
      Cases_on `eval_operand h s` >> simp[]) >>
  Cases_on `t'` >> simp[ptrDisciplineTheory.out_taint_def] >>
  Cases_on `eval_operand h s` >> simp[] >>
  Cases_on `t` >> simp[])
QED
Theorem typed_copy_loop_test_check:
  !D ctx fn G tn s id opc ops outs s' fuel.
    (opc = LT /\ (?v k. ops = [Var v; Lit k]) \/
     opc = MUL \/ opc = ISZERO \/ opc = JNZ) /\
    (!op. MEM op ops ==> op_taint tn op = {}) /\
    ~ctx_has_dalloca ctx /\
    step_inst_base (mk_inst id opc ops outs) s = OK s' /\
    s'.vs_requests = s.vs_requests ==>
    ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id opc ops outs) s
Proof
  rpt strip_tac >>
  gvs[] >>
  simp[ptrSafeRunTheory.ptr_inst_ok_def, ptrDisciplineTheory.access_ok_def,
       ptrDisciplineTheory.taint_ok_def, ptrDisciplineTheory.allocas_from_def,
       mk_inst_def, codegenRelTheory.source_memory_write_ranges_def,
       contextCodegenRelTheory.source_memory_read_ranges_def] >>
  simp[GSYM mk_inst_def, step_inst_non_invoke] >> metis_tac[]
QED

Theorem typed_copy_loop_test_run:
  !ctx fn s ctr lt done id i n body_lbl exit_lbl bb.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    bb.bb_instructions =
      [mk_inst id LT [Var ctr; Lit (n2w n)] [lt];
       mk_inst (id+1) ISZERO [Var lt] [done];
       mk_inst (id+2) JNZ [Var done; Label exit_lbl; Label body_lbl] []] /\
    s.vs_inst_idx = 0 /\ ~s.vs_halted /\
    lookup_var ctr s = SOME (n2w i) /\
    i <= n /\ n < dimword(:256) /\ ctr <> lt /\ ctr <> done ==>
    !fuel.
      run_from (SUC fuel) ctx fn s =
      run_blocks (SUC fuel) ctx fn
        (jump_to (if i < n then body_lbl else exit_lbl)
          (update_var done (bool_to_word (~(i < n)))
            (update_var lt (bool_to_word (i < n)) s)))
Proof
  rpt strip_tac >>
  `i < dimword(:256)` by decide_tac >>
  simp[fragExecTheory.run_from_def, Once exec_block_def, get_instruction_def,
       step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[mk_inst_def, instruction_accessors,
    instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure2_def, eval_operand_def, w2n_n2w, LESS_MOD] >>
  simp[Once exec_block_def, get_instruction_def, update_var_def,
       step_inst_non_invoke, is_terminator_def] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[mk_inst_def, instruction_accessors,
    instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure1_def, eval_operand_def, lookup_var_def,
       FLOOKUP_UPDATE, bool_to_word_def] >>
  simp[Once exec_block_def, get_instruction_def, update_var_def,
       step_inst_non_invoke, is_terminator_def] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[mk_inst_def, instruction_accessors,
    instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
  Cases_on `i < n` >>
  simp[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE,
       bool_to_word_def, jump_to_def]
QED

Theorem typed_copy_loop_test_ghost_run:
  !ctx fn PG G tn s ctr lt done id i n body_lbl exit_lbl bb target.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    bb.bb_instructions =
      [mk_inst id LT [Var ctr; Lit (n2w n)] [lt];
       mk_inst (id+1) ISZERO [Var lt] [done];
       mk_inst (id+2) JNZ [Var done; Label exit_lbl; Label body_lbl] []] /\
    lookup_block (if i < n then body_lbl else exit_lbl) fn.fn_blocks =
      SOME target /\ phi_prefix_length target.bb_instructions = 0 /\
    s.vs_inst_idx = 0 /\ ~s.vs_halted /\
    lookup_var ctr s = SOME (n2w i) /\
    i <= n /\ n < dimword(:256) /\ ctr <> lt /\ ctr <> done ==>
    !fuel.
      ghost_run (SUC fuel) ctx fn PG G tn s =
      ghost_run fuel ctx fn PG
        (DRESTRICT (DRESTRICT G (COMPL {lt})) (COMPL {done}))
        (tn with t_var := (tn.t_var |+ (lt,{})) |+ (done,{}))
        (jump_to (if i < n then body_lbl else exit_lbl)
          (update_var done (bool_to_word (~(i < n)))
            (update_var lt (bool_to_word (i < n)) s)))
Proof
  rpt strip_tac >>
  `i < dimword(:256)` by decide_tac >>
  qspecl_then [`s`, `ctr`, `lt`, `done`] mp_tac typed_copy_loop_test_steps >>
  disch_then (qspecl_then [`id`, `i`, `n`] mp_tac) >>
  disch_then (qspecl_then [`body_lbl`, `exit_lbl`] mp_tac) >>
  asm_rewrite_tac[] >> strip_tac >> gvs[] >>
  simp[ptrSafeRunTheory.ghost_run_def,
       Once ptrSafeRunTheory.ghost_block_def, get_instruction_def,
       step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[mk_inst_def, instruction_accessors,
    instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure2_def, eval_operand_def, w2n_n2w, LESS_MOD,
       is_terminator_def] >>
  simp[ptrSafeRunTheory.ghost_step_def, GSYM mk_inst_def,
       step_inst_non_invoke, typed_copy_loop_arith_ghost] >>
  simp[Once ptrSafeRunTheory.ghost_block_def, get_instruction_def,
       ptrSafeRunTheory.ghost_step_def, step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[mk_inst_def, instruction_accessors,
    instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure1_def, eval_operand_def, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE, bool_to_word_def, is_terminator_def,
       SRULE [update_var_def, mk_inst_def] typed_copy_loop_arith_ghost] >>
  simp[ptrDisciplineTheory.step_prov_def, ptrDisciplineTheory.set_prov_def,
       ptrDisciplineTheory.out_prov_def] >>
  simp[Once ptrSafeRunTheory.ghost_block_def, get_instruction_def,
       step_inst_non_invoke, mk_inst_def, is_terminator_def] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[instruction_accessors, instruction_accfupds,
    combinTheory.K_THM, opcode_case_def] >>
  Cases_on `i < n` >>
  simp[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE,
       bool_to_word_def, jump_to_def] >>
  gvs[] >>
  qmatch_goalsub_abbrev_tac `entry_prov fn sj gg` >>
  qmatch_goalsub_abbrev_tac `entry_taint_vars fn sj tt` >>
  `entry_prov fn sj gg = gg /\ entry_taint_vars fn sj tt = tt` by
    (irule typedCopyArrayPtrTheory.entry_ghost_no_phi >> simp[Abbr `sj`] >> metis_tac[]) >>
  simp[Once ptrSafeRunTheory.ghost_blocks_def, Abbr `sj`] >>
  (Cases_on `target.bb_instructions`
   >- simp[eval_phis_def] >>
   Cases_on `h.inst_opcode = PHI` >>
   gvs[phi_prefix_length_def, eval_phis_def])
QED

Theorem typed_copy_loop_test_ptr_safe:
  !D ctx fn PG G tn s ctr lt done id i n body_lbl exit_lbl bb target.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    bb.bb_instructions =
      [mk_inst id LT [Var ctr; Lit (n2w n)] [lt];
       mk_inst (id+1) ISZERO [Var lt] [done];
       mk_inst (id+2) JNZ [Var done; Label exit_lbl; Label body_lbl] []] /\
    lookup_block (if i < n then body_lbl else exit_lbl) fn.fn_blocks =
      SOME target /\ phi_prefix_length target.bb_instructions = 0 /\
    s.vs_inst_idx = 0 /\ ~s.vs_halted /\
    lookup_var ctr s = SOME (n2w i) /\ op_taint tn (Var ctr) = {} /\
    ~ctx_has_dalloca ctx /\
    i <= n /\ n < dimword(:256) /\ ctr <> lt /\ ctr <> done ==>
    !fuel.
      ptr_safe_run D 0 fuel ctx fn PG
        (DRESTRICT (DRESTRICT G (COMPL {lt})) (COMPL {done}))
        (tn with t_var := (tn.t_var |+ (lt,{})) |+ (done,{}))
        (jump_to (if i < n then body_lbl else exit_lbl)
          (update_var done (bool_to_word (~(i < n)))
            (update_var lt (bool_to_word (i < n)) s))) ==>
      ptr_safe_run D 0 (SUC fuel) ctx fn PG G tn s
Proof
  rpt strip_tac >>
  `i < dimword(:256)` by decide_tac >>
  simp[ptrSafeRunTheory.ptr_safe_run_def,
       Once ptrSafeRunTheory.ptr_safe_block_def, get_instruction_def,
       ptrSafeRunTheory.ptr_safe_step_def,
       ptrSafeRunTheory.ghost_step_def, step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[mk_inst_def, instruction_accessors,
    instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure2_def, eval_operand_def, w2n_n2w, LESS_MOD,
       is_terminator_def,
       SRULE [mk_inst_def] typed_copy_loop_arith_ghost,
       ptrDisciplineTheory.step_prov_def, ptrDisciplineTheory.set_prov_def,
       ptrDisciplineTheory.out_prov_def] >>
  conj_tac
  >- (irule (SRULE [mk_inst_def] typed_copy_loop_test_check) >>
      simp[] >> conj_tac
      >- (rpt strip_tac >> gvs[ptrDisciplineTheory.op_taint_def]) >>
      PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
      pure_rewrite_tac[instruction_accessors, instruction_accfupds,
        combinTheory.K_THM, opcode_case_def] >>
      simp[exec_pure2_def, eval_operand_def, update_var_def]) >>
  simp[update_var_def, SRULE [mk_inst_def] typed_copy_loop_arith_ghost] >>
  simp[Once ptrSafeRunTheory.ptr_safe_block_def, get_instruction_def,
       ptrSafeRunTheory.ptr_safe_step_def,
       ptrSafeRunTheory.ghost_step_def, step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[mk_inst_def, instruction_accessors,
    instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure1_def, eval_operand_def, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE, bool_to_word_def, is_terminator_def,
       SRULE [mk_inst_def] typed_copy_loop_arith_ghost,
       ptrDisciplineTheory.step_prov_def, ptrDisciplineTheory.set_prov_def,
       ptrDisciplineTheory.out_prov_def] >>
  conj_tac
  >- (irule (SRULE [mk_inst_def] typed_copy_loop_test_check) >>
      simp[ptrDisciplineTheory.op_taint_def, FLOOKUP_UPDATE] >>
      PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
      pure_rewrite_tac[instruction_accessors, instruction_accfupds,
        combinTheory.K_THM, opcode_case_def] >>
      simp[exec_pure1_def, eval_operand_def, lookup_var_def,
           FLOOKUP_UPDATE, update_var_def]) >>
  simp[Once ptrSafeRunTheory.ptr_safe_block_def, get_instruction_def,
       ptrSafeRunTheory.ptr_safe_step_def,
       ptrSafeRunTheory.ghost_step_def, step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[mk_inst_def, instruction_accessors,
    instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
  Cases_on `i < n` >>
  simp[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE,
       bool_to_word_def, jump_to_def, is_terminator_def] >>
  (conj_tac
   >- (irule (SRULE [mk_inst_def] typed_copy_loop_test_check) >>
       simp[ptrDisciplineTheory.op_taint_def, FLOOKUP_UPDATE] >>
       conj_tac
       >- (rpt strip_tac >> gvs[]) >>
       PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
       pure_rewrite_tac[instruction_accessors, instruction_accfupds,
         combinTheory.K_THM, opcode_case_def] >>
       simp[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE,
            jump_to_def]) >>
   gvs[update_var_def, jump_to_def, finite_mapTheory.DRESTRICT_DRESTRICT] >>
   qmatch_goalsub_abbrev_tac `entry_prov fn sj gg` >>
   qmatch_goalsub_abbrev_tac `entry_taint_vars fn sj tt` >>
   `entry_prov fn sj gg = gg /\ entry_taint_vars fn sj tt = tt` by
     (irule typedCopyArrayPtrTheory.entry_ghost_no_phi >>
      simp[Abbr `sj`] >> metis_tac[]) >>
   simp[Once ptrSafeRunTheory.ptr_safe_blocks_def, Abbr `sj`] >>
   qpat_x_assum `ptr_safe_run _ _ _ _ _ _ _ _ _` mp_tac >>
   simp[ptrSafeRunTheory.ptr_safe_run_def] >>
   Cases_on `target.bb_instructions`
   >- simp[eval_phis_def] >>
   Cases_on `h.inst_opcode = PHI` >>
   gvs[phi_prefix_length_def, eval_phis_def])
QED

(* The body prefix uses dynamic offsets, not the literal-offset helper. *)
Theorem typed_copy_loop_address_steps:
  !s ctr so doff sp dp src dst id i ss ds sb db.
    lookup_var ctr s = SOME (n2w i) /\
    eval_operand src s = SOME (n2w sb) /\
    eval_operand dst s = SOME (n2w db) /\
    ALL_DISTINCT [so; doff; sp; dp] /\
    (!v. MEM v [so; doff; sp; dp] ==>
      ctr <> v /\ src <> Var v /\ dst <> Var v) ==>
    ?s1 s2 s3 s4.
      s1 = update_var so (n2w (i * ss)) s /\
      s2 = update_var doff (n2w (i * ds)) s1 /\
      s3 = update_var sp (n2w (sb + i * ss)) s2 /\
      s4 = update_var dp (n2w (db + i * ds)) s3 /\
      step_inst_base (mk_inst id MUL [Var ctr; Lit (n2w ss)] [so]) s = OK s1 /\
      step_inst_base (mk_inst (id+1) MUL [Var ctr; Lit (n2w ds)] [doff]) s1 = OK s2 /\
      step_inst_base (mk_inst (id+2) ADD [src; Var so] [sp]) s2 = OK s3 /\
      step_inst_base (mk_inst (id+3) ADD [dst; Var doff] [dp]) s3 = OK s4 /\
      eval_operand (Var sp) s4 = SOME (n2w (sb + i * ss)) /\
      eval_operand (Var dp) s4 = SOME (n2w (db + i * ds)) /\
      lookup_var ctr s4 = lookup_var ctr s /\
      eval_operand src s4 = eval_operand src s /\
      eval_operand dst s4 = eval_operand dst s /\
      s4.vs_memory = s.vs_memory
Proof
  rpt gen_tac >> strip_tac >>
  fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[mk_inst_def, instruction_accessors,
    instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
  Cases_on `src` >> Cases_on `dst` >>
  gvs[exec_pure2_def, eval_operand_def, lookup_var_def, update_var_def,
      FLOOKUP_UPDATE, word_mul_n2w, word_add_n2w] >>
  metis_tac[]
QED

Theorem typed_copy_loop_dynamic_offset_covers:
  !PG G tn s root offset out id a off total n.
    lookup_var root s = SOME a /\
    eval_operand offset s = SOME (n2w off) /\
    ptr_covers G tn root s total /\
    off < total /\ off + n <= total /\
    w2n a + off < dimword(:256) /\ root <> out ==>
    ptr_covers
      (step_prov PG G (mk_inst id ADD [Var root; offset] [out])
        (update_var out (a + n2w off) s))
      (step_taint (mk_inst id ADD [Var root; offset] [out]) s
        (update_var out (a + n2w off) s) tn)
      out (update_var out (a + n2w off) s) n
Proof
  rpt strip_tac >>
  `op_taint (step_taint (mk_inst id ADD [Var root; offset] [out]) s
    (update_var out (a + n2w off) s) tn) (Var out) = {}` by
      simp[typedCopyPtrTheory.copy_len_binop_ghost_frame] >>
  gvs[bodyPtrDefsTheory.ptr_covers_def] >>
  `off < dimword(:256)` by decide_tac >>
  simp[ptrDisciplineTheory.step_prov_def, ptrDisciplineTheory.set_prov_def,
       ptrDisciplineTheory.out_prov_def, ptrDisciplineTheory.first_prov_def,
       ptrDisciplineTheory.op_prov_def, mk_inst_def, FLOOKUP_UPDATE,
       lookup_var_def, update_var_def, wordsTheory.w2n_add_2,
       wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >> decide_tac
QED

Theorem typed_copy_loop_mul_frag_ptr:
  !cx ctx PG sa sb id left right out P Q R.
    sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts ++
      [mk_inst id MUL [left;right] [out]] /\
    (!G tn s. P G tn s ==>
      op_taint tn left = {} /\ op_taint tn right = {} /\
      ?a b. eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
        Q (DRESTRICT G (COMPL {out}))
          (tn with t_var := tn.t_var |+ (out,{}))
          ((update_var out (a*b) s) with vs_inst_idx := SUC s.vs_inst_idx)) ==>
    frag_exec_ptr cx ctx PG sa sb P Q R
Proof
  rpt gen_tac >> strip_tac >>
  irule typedCopyPtrTheory.ptr_fragment_step >>
  simp[mk_inst_def, is_terminator_def] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  qexists_tac `update_var out (a*b) s` >>
  conj_tac
  >- (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
      pure_rewrite_tac[instruction_accessors, instruction_accfupds,
        combinTheory.K_THM, opcode_case_def] >>
      simp[exec_pure2_def]) >>
  simp[update_var_def,
       SRULE [mk_inst_def, update_var_def] typed_copy_loop_arith_ghost] >>
  conj_tac
  >- (rpt strip_tac >>
      `step_inst_base (mk_inst id MUL [left;right] [out]) s =
         OK (update_var out (a*b) s)` by
        (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
         pure_rewrite_tac[mk_inst_def, instruction_accessors, instruction_accfupds,
           combinTheory.K_THM, opcode_case_def] >> simp[exec_pure2_def]) >>
      `!op. MEM op [left;right] ==> op_taint tn op = {}` by
        (rpt strip_tac >> gvs[]) >>
      ` (update_var out (a*b) s).vs_requests = s.vs_requests` by
         simp[update_var_def] >>
      metis_tac[typed_copy_loop_test_check, mk_inst_def]) >>
  gvs[update_var_def, ptrDisciplineTheory.step_prov_def,
      ptrDisciplineTheory.set_prov_def, ptrDisciplineTheory.out_prov_def]
QED

Theorem typed_copy_loop_test_frame:
  !G tn s lt done b1 b2 lbl p.
    p <> lt /\ p <> done ==>
    lookup_var p (jump_to lbl (update_var done b2 (update_var lt b1 s))) =
      lookup_var p s /\
    FLOOKUP (DRESTRICT (DRESTRICT G (COMPL {lt})) (COMPL {done})) p =
      FLOOKUP G p /\
    op_taint (tn with t_var := (tn.t_var |+ (lt,{})) |+ (done,{})) (Var p) =
      op_taint tn (Var p) /\
    (jump_to lbl (update_var done b2 (update_var lt b1 s))).vs_memory = s.vs_memory /\
    (tn with t_var := (tn.t_var |+ (lt,{})) |+ (done,{})).t_mem = tn.t_mem /\
    (tn with t_var := (tn.t_var |+ (lt,{})) |+ (done,{})).t_stor = tn.t_stor /\
    (tn with t_var := (tn.t_var |+ (lt,{})) |+ (done,{})).t_trans = tn.t_trans /\
    (!n. ptr_covers G tn p s n ==>
      ptr_covers (DRESTRICT (DRESTRICT G (COMPL {lt})) (COMPL {done}))
        (tn with t_var := (tn.t_var |+ (lt,{})) |+ (done,{})) p
        (jump_to lbl (update_var done b2 (update_var lt b1 s))) n)
Proof
  rpt strip_tac >>
  gvs[bodyPtrDefsTheory.ptr_covers_def, lookup_var_def, update_var_def,
      jump_to_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT,
      ptrDisciplineTheory.op_taint_def]
QED

Theorem typed_copy_loop_address_frag_ptr:
  !cx ctx PG R sb si ctr so doff sp dp sr dr id i ss ds a b S T G tn s.
    lookup_var ctr s = SOME (n2w i) /\ op_taint tn (Var ctr) = {} /\
    lookup_var sr s = SOME a /\ lookup_var dr s = SOME b /\
    ptr_covers G tn sr s S /\ ptr_covers G tn dr s T /\
    ALL_DISTINCT [so;doff;sp;dp] /\
    (!v. MEM v [so;doff;sp;dp] ==> ctr <> v /\ sr <> v /\ dr <> v) /\
    i*ss < S /\ i*ss+ss <= S /\ i*ds < T /\ i*ds+ds <= T /\
    w2n a+i*ss < dimword(:256) /\ w2n b+i*ds < dimword(:256) /\
    si.cs_blocks = sb.cs_blocks /\ si.cs_current_bb = sb.cs_current_bb /\
    si.cs_current_insts = sb.cs_current_insts ++
      [mk_inst id MUL [Var ctr;Lit (n2w ss)] [so];
       mk_inst (id+1) MUL [Var ctr;Lit (n2w ds)] [doff];
       mk_inst (id+2) ADD [Var sr;Var so] [sp];
       mk_inst (id+3) ADD [Var dr;Var doff] [dp]] ==>
    ?Gf tnf sf.
      frag_exec_ptr cx ctx PG sb si
        (\g t v. g=G /\ t=tn /\ v=s)
        (\g t v. g=Gf /\ t=tnf /\ v=sf) R /\
      lookup_var sp sf = SOME (n2w (w2n a+i*ss)) /\
      lookup_var dp sf = SOME (n2w (w2n b+i*ds)) /\
      ptr_covers Gf tnf sp sf ss /\ ptr_covers Gf tnf dp sf ds /\
      sf.vs_memory=s.vs_memory /\ tnf.t_mem=tn.t_mem /\
      tnf.t_stor=tn.t_stor /\ tnf.t_trans=tn.t_trans /\
      (!p. ~MEM p [so;doff;sp;dp] ==>
        lookup_var p sf=lookup_var p s /\ FLOOKUP Gf p=FLOOKUP G p /\
        op_taint tnf (Var p)=op_taint tn (Var p))
Proof
  typedCopyLoopAmbientLib.address_witnesses >>
  conj_tac >- suspend "fragment" >>
  suspend "resources"
QED

Resume typed_copy_loop_address_frag_ptr[fragment]:
  typedCopyLoopAmbientLib.address_fragment typed_copy_loop_mul_frag_ptr
QED

Resume typed_copy_loop_address_frag_ptr[resources]:
  typedCopyLoopAmbientLib.address_resources typed_copy_loop_dynamic_offset_covers
QED

Finalise typed_copy_loop_address_frag_ptr

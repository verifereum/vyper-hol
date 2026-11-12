(* Operand-bounded control interface shared by fixed and dynamic typed copies. *)
Theory assignTupleTypedCopyArrayPtr
Ancestors typedCopyLoopHeaderPtr typedCopyLoopBackedgePtr
  typedCopyLayoutPtr fragContinuationPtr venomExecSemantics venomInst venomState
  words finite_map arithmetic bodyPtrEnvBuiltinsGuards

Theorem typed_copy_operand_loop_test_steps:
  !s ctr bound lt done id i n body_lbl exit_lbl.
    lookup_var ctr s = SOME (n2w i) /\
    eval_operand bound s = SOME (n2w n) /\
    i <= n /\ n < dimword(:256) /\ ctr <> lt /\ ctr <> done ==>
    ?s1 s2.
      s1 = update_var lt (bool_to_word (i < n)) s /\
      s2 = update_var done (bool_to_word (~(i < n))) s1 /\
      step_inst_base (mk_inst id LT [Var ctr; bound] [lt]) s = OK s1 /\
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

Theorem typed_copy_operand_loop_test_run:
  !ctx fn s ctr bound lt done id i n body_lbl exit_lbl bb.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    bb.bb_instructions =
      [mk_inst id LT [Var ctr; bound] [lt];
       mk_inst (id+1) ISZERO [Var lt] [done];
       mk_inst (id+2) JNZ [Var done; Label exit_lbl; Label body_lbl] []] /\
    s.vs_inst_idx = 0 /\ ~s.vs_halted /\
    lookup_var ctr s = SOME (n2w i) /\
    eval_operand bound s = SOME (n2w n) /\
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

Theorem typed_copy_operand_loop_test_ghost_run:
  !ctx fn PG G tn s ctr bound lt done id i n body_lbl exit_lbl bb target.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    bb.bb_instructions =
      [mk_inst id LT [Var ctr; bound] [lt];
       mk_inst (id+1) ISZERO [Var lt] [done];
       mk_inst (id+2) JNZ [Var done; Label exit_lbl; Label body_lbl] []] /\
    lookup_block (if i < n then body_lbl else exit_lbl) fn.fn_blocks =
      SOME target /\ phi_prefix_length target.bb_instructions = 0 /\
    s.vs_inst_idx = 0 /\ ~s.vs_halted /\
    lookup_var ctr s = SOME (n2w i) /\
    eval_operand bound s = SOME (n2w n) /\
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
  qspecl_then [`s`, `ctr`, `bound`, `lt`, `done`] mp_tac
    typed_copy_operand_loop_test_steps >>
  disch_then (qspecl_then [`id`, `i`, `n`, `body_lbl`, `exit_lbl`] mp_tac) >>
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
       step_inst_non_invoke, typed_copy_loop_arith_ghost_clean] >>
  simp[Once ptrSafeRunTheory.ghost_block_def, get_instruction_def,
       ptrSafeRunTheory.ghost_step_def, step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[mk_inst_def, instruction_accessors,
    instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure1_def, eval_operand_def, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE, bool_to_word_def, is_terminator_def,
       SRULE [update_var_def, mk_inst_def] typed_copy_loop_arith_ghost_clean] >>
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
    (irule typedCopyArrayPtrTheory.entry_ghost_no_phi >>
     simp[Abbr `sj`] >> metis_tac[]) >>
  simp[Once ptrSafeRunTheory.ghost_blocks_def, Abbr `sj`] >>
  (Cases_on `target.bb_instructions`
   >- simp[eval_phis_def] >>
   Cases_on `h.inst_opcode = PHI` >>
   gvs[phi_prefix_length_def, eval_phis_def])
QED


Theorem typed_copy_operand_loop_test_ptr_safe:
  !D ctx fn PG G tn s ctr bound lt done id i n body_lbl exit_lbl bb target.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    bb.bb_instructions =
      [mk_inst id LT [Var ctr; bound] [lt];
       mk_inst (id+1) ISZERO [Var lt] [done];
       mk_inst (id+2) JNZ [Var done; Label exit_lbl; Label body_lbl] []] /\
    lookup_block (if i < n then body_lbl else exit_lbl) fn.fn_blocks =
      SOME target /\ phi_prefix_length target.bb_instructions = 0 /\
    s.vs_inst_idx = 0 /\ ~s.vs_halted /\
    lookup_var ctr s = SOME (n2w i) /\
    eval_operand bound s = SOME (n2w n) /\
    op_taint tn (Var ctr) = {} /\ op_taint tn bound = {} /\
    op_prov G (Var ctr) = NONE /\ op_prov G bound = NONE /\
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
       SRULE [mk_inst_def] typed_copy_loop_arith_ghost_clean,
       ptrDisciplineTheory.step_prov_def, ptrDisciplineTheory.set_prov_def,
       ptrDisciplineTheory.out_prov_def] >>
  conj_tac
  >- (irule (SRULE [mk_inst_def] guard_compare_inst_ok) >>
      simp[] >> rpt strip_tac >> gvs[]) >>
  simp[update_var_def, SRULE [mk_inst_def] typed_copy_loop_arith_ghost_clean] >>
  simp[Once ptrSafeRunTheory.ptr_safe_block_def, get_instruction_def,
       ptrSafeRunTheory.ptr_safe_step_def,
       ptrSafeRunTheory.ghost_step_def, step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[mk_inst_def, instruction_accessors,
    instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure1_def, eval_operand_def, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE, bool_to_word_def, is_terminator_def,
       SRULE [mk_inst_def] typed_copy_loop_arith_ghost_clean,
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

Theorem typed_copy_operand_loop_test_continuation:
  !D ctx fn PG G tn s ctr bound lt done id i n body_lbl exit_lbl bb target
    Gf tnf sf.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    bb.bb_instructions =
      [mk_inst id LT [Var ctr; bound] [lt];
       mk_inst (id+1) ISZERO [Var lt] [done];
       mk_inst (id+2) JNZ [Var done; Label exit_lbl; Label body_lbl] []] /\
    lookup_block (if i < n then body_lbl else exit_lbl) fn.fn_blocks =
      SOME target /\ phi_prefix_length target.bb_instructions = 0 /\
    s.vs_inst_idx = 0 /\ ~s.vs_halted /\
    lookup_var ctr s = SOME (n2w i) /\
    eval_operand bound s = SOME (n2w n) /\
    op_taint tn (Var ctr) = {} /\ op_taint tn bound = {} /\
    op_prov G (Var ctr) = NONE /\ op_prov G bound = NONE /\
    ~ctx_has_dalloca ctx /\
    i <= n /\ n < dimword(:256) /\ ctr <> lt /\ ctr <> done /\
    Gf = DRESTRICT (DRESTRICT G (COMPL {lt})) (COMPL {done}) /\
    tnf = (tn with t_var := (tn.t_var |+ (lt,{})) |+ (done,{})) /\
    sf = jump_to (if i < n then body_lbl else exit_lbl)
      (update_var done (bool_to_word (~(i < n)))
        (update_var lt (bool_to_word (i < n)) s)) ==>
    !fuel r. run_from fuel ctx fn sf = r /\ (!e. r <> Error e) ==>
      run_from (SUC fuel) ctx fn s = r /\
      ghost_run (SUC fuel) ctx fn PG G tn s =
        ghost_run fuel ctx fn PG Gf tnf sf /\
      (ptr_safe_run D 0 fuel ctx fn PG Gf tnf sf ==>
       ptr_safe_run D 0 (SUC fuel) ctx fn PG G tn s)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `!fuel. run_from (SUC fuel) ctx fn s = run_blocks (SUC fuel) ctx fn sf` by
    (gvs[] >> irule typed_copy_operand_loop_test_run >> metis_tac[]) >>
  `!fuel. run_blocks (SUC fuel) ctx fn sf = run_from fuel ctx fn sf` by
    (gen_tac >>
     `lookup_block sf.vs_current_bb fn.fn_blocks = SOME target` by
       simp[jump_to_def] >>
     drule_all fragExecTheory.run_blocks_run_from_no_phi >>
     simp[jump_to_def] >> gvs[jump_to_def]) >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (gvs[] >> irule (SRULE [] typed_copy_operand_loop_test_ghost_run) >>
      metis_tac[]) >>
  strip_tac >> gvs[] >>
  irule (SRULE [] typed_copy_operand_loop_test_ptr_safe) >> metis_tac[]
QED

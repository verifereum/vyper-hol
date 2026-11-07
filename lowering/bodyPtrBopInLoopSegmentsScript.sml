(* Concrete checked segments of the mutable membership search loop. *)
Theory bodyPtrBopInLoopSegments
Ancestors bodyPtrBopInLoopControl bodyPtrBopInLiteralSuffix bodyPtrBopInLoopExit
  fragGasSeqPtr fragGasPathPtr ptrSafeRun ptrDiscipline venomExecSemantics venomExecProofs
  venomInstProofs venomInst venomState emitHelper gasCount codegenRel
  contextCodegenRel finite_map words stmtAppendStorageRunPtr

Theorem membership_jnz_path:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id JNZ [op;Label lt;Label lf] []) /\
  eval_operand op s = SOME (bool_to_word b) /\ op_taint tn op = {} ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 G tn
    (OK (jump_to (if b then lt else lf) s))
Proof
  strip_tac >>
  `eval_operand op s = SOME (if b then 1w else 0w)` by (Cases_on `b` >> gvs[bool_to_word_def]) >>
  drule step_jnz_behavior >>
  disch_then (qspecl_then [`lt`, `lf`, `id`] assume_tac) >>
  `step_inst 0 ctx (mk_inst id JNZ [op;Label lt;Label lf] []) s =
    OK (jump_to (if b then lt else lf) s)` by
    (simp[step_inst_non_invoke, mk_inst_def, step_jnz_behavior,
          bool_to_word_def] >> Cases_on `b` >> gvs[]) >>
  `ptr_safe_step D 0 0 ctx fn PG G tn
    (mk_inst id JNZ [op;Label lt;Label lf] []) s` by
    (simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
          allocas_from_def, mk_inst_def, source_memory_write_ranges_def,
          source_memory_read_ranges_def, op_taint_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke] >>
     simp[mk_inst_def, step_jnz_behavior, jump_to_def] >>
     Cases_on `b` >> gvs[op_taint_def, bool_to_word_def] >>
     gen_tac >> Cases_on `op' = op` >> gvs[] >>
     Cases_on `op' = Label lt` >> gvs[] >>
     Cases_on `op' = Label lf` >> gvs[]) >>
  `is_terminator (mk_inst id JNZ [op;Label lt;Label lf] []).inst_opcode /\
   (mk_inst id JNZ [op;Label lt;Label lf] []).inst_opcode <> INVOKE` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all raw_jump_path_ptr >> simp[mk_inst_def, gas_count_step_def]
QED

Theorem membership_eq_branch_path:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id EQ [a;b] [dst]) /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst (id+1) JNZ [Var dst;Label lt;Label lf] []) /\
  eval_operand a s = SOME aw /\ eval_operand b s = SOME bw /\
  op_prov G a = NONE /\ op_prov G b = NONE /\
  op_taint tn a = {} /\ op_taint tn b = {} ==>
  ?G' tn'.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
      (OK (jump_to (if aw = bw then lt else lf)
        (update_var dst (bool_to_word (aw = bw)) s))) /\
    FLOOKUP G' dst = NONE /\ op_taint tn' (Var dst) = {} /\
    (tn' with t_var := tn.t_var) = tn /\
    (!p. p <> dst ==> FLOOKUP G' p = FLOOKUP G p /\
      op_taint tn' (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `step_inst_base (mk_inst id EQ [a;b] [dst]) s =
    OK (update_var dst (bool_to_word (aw = bw)) s)` by
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     pure_rewrite_tac[mk_inst_def, instruction_accessors,
       instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
     simp[exec_pure2_def]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id EQ [a;b] [dst]) s` by
    (irule membership_eq_check >> metis_tac[]) >>
  `~is_terminator (mk_inst id EQ [a;b] [dst]).inst_opcode /\
    (mk_inst id EQ [a;b] [dst]).inst_opcode <> INVOKE` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all straight_line_ptr_edge >>
  disch_then (qspec_then `PG` mp_tac) >> simp[mk_inst_def] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr_edge D 0 ctx fn PG G tn s 0 G1 tn1 (OK s1)` >>
  `tn1 = tn with t_var := tn.t_var |+ (dst,{})` by
    (simp[Abbr `tn1`, GSYM mk_inst_def] >> irule membership_scalar_ghost_frame >> simp[]) >>
  `eval_operand (Var dst) s1 = SOME (bool_to_word (aw = bw)) /\
    op_taint tn1 (Var dst) = {}` by
    simp[Abbr `s1`, eval_operand_def, lookup_var_def, update_var_def,
         op_taint_def, FLOOKUP_UPDATE] >>
  `gas_path_ptr D 0 ctx fn PG G1 tn1 s1 0 G1 tn1
    (OK (jump_to (if aw = bw then lt else lf) s1))` by
    (irule membership_jnz_path >> simp[Abbr `s1`, update_var_def] >>
     qexistsl_tac [`id+1`, `Var dst`] >>
     simp[eval_operand_def, lookup_var_def, update_var_def, op_taint_def, FLOOKUP_UPDATE]) >>
  drule (cj 2 gas_path_ptr_rules) >> disch_then drule >> simp[] >> strip_tac >>
  qexistsl_tac [`G1`, `tn1`] >>
  simp[Abbr `s1`, jump_to_def, update_var_def, op_taint_def, FLOOKUP_UPDATE] >>
  suspend "frame"
QED

Resume membership_eq_branch_path[frame]:
  gvs[jump_to_def, update_var_def] >>
  simp[Abbr `G1`, GSYM mk_inst_def] >> conj_tac
  >- (irule membership_scalar_provenance >> simp[]) >>
  rpt strip_tac >> simp[scalar_step_old_prov]
QED

Finalise membership_eq_branch_path

Theorem membership_found_path:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id ASSIGN [Lit 1w] [dst]) /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst (id+1) JMP [Label exit] []) ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 (DRESTRICT G (COMPL {dst}))
    (tn with t_var := set_var_taint tn.t_var [dst] {})
    (OK (jump_to exit (update_var dst 1w s)))
Proof
  strip_tac >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 (DRESTRICT G (COMPL {dst}))
    (tn with t_var := set_var_taint tn.t_var [dst] {})
    (OK (update_var dst 1w s with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule membership_assign_literal_path >> metis_tac[]) >>
  qmatch_asmsub_abbrev_tac `OK s1` >>
  `gas_path_ptr D 0 ctx fn PG (DRESTRICT G (COMPL {dst}))
    (tn with t_var := set_var_taint tn.t_var [dst] {}) s1 0
    (DRESTRICT G (COMPL {dst}))
    (tn with t_var := set_var_taint tn.t_var [dst] {})
    (OK (jump_to exit s1))` by
    (irule membership_jump_path >> simp[Abbr `s1`, update_var_def] >> metis_tac[]) >>
  drule_all gas_path_ptr_then >>
  simp[Abbr `s1`, jump_to_def, update_var_def]
QED

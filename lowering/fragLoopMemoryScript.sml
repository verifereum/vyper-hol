(* Memory-safe composition of the loop layout emitted by lowering. *)
Theory fragLoopMemory
Ancestors
  fragExecMem fragExec compileEnv emitHelper exprLoweringProps
  venomState venomExecSemantics venomExecProofs memSafeRun venomInst list

Theorem mem_safe_run_jump_no_phi[local]:
  !fuel ctx fn s bb inst lbl bb'.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
    inst_mem_below_frontier inst s /\
    step_inst_base inst s = OK (jump_to lbl s) /\ ~s.vs_halted /\
    lookup_block lbl fn.fn_blocks = SOME bb' /\
    phi_prefix_length bb'.bb_instructions = 0 /\
    mem_safe_run fuel ctx fn (jump_to lbl s) ==>
    mem_safe_run (SUC fuel) ctx fn s
Proof
  rpt strip_tac >>
  `exec_block (SUC fuel) ctx bb s = OK (jump_to lbl s)` by
    simp[Once exec_block_def, step_inst_non_invoke, jump_to_def] >>
  `mem_safe_block (SUC fuel) ctx bb s` by
    simp[Once mem_safe_block_def, mem_safe_step_non_invoke,
         step_inst_non_invoke] >>
  `!t. eval_phis t bb'.bb_instructions = OK t` by
    (Cases_on `bb'.bb_instructions` >>
     gvs[phi_prefix_length_def, eval_phis_def, AllCaseEqs()]) >>
  `mem_safe_blocks (SUC fuel) ctx fn (jump_to lbl s)` by
    (simp[Once mem_safe_blocks_def, jump_to_def] >>
     qpat_x_assum `mem_safe_run fuel _ _ _` mp_tac >>
     simp[mem_safe_run_def, jump_to_def]) >>
  simp[mem_safe_run_def]
QED

Theorem mem_safe_run_jump_result[local]:
  !fuel ctx fn s bb inst lbl r.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
    inst_mem_below_frontier inst s /\
    step_inst_base inst s = OK (jump_to lbl s) /\ ~s.vs_halted /\
    run_from fuel ctx fn (jump_to lbl s) = r /\ (!e. r <> Error e) /\
    mem_safe_run fuel ctx fn (jump_to lbl s) ==>
    mem_safe_run (SUC fuel) ctx fn s
Proof
  rpt strip_tac >>
  Cases_on `lookup_block lbl fn.fn_blocks`
  >- gvs[run_from_def, jump_to_def] >>
  rename1 `lookup_block lbl _ = SOME bb'` >>
  Cases_on `phi_prefix_length bb'.bb_instructions = 0`
  >- (irule mem_safe_run_jump_no_phi >> metis_tac[]) >>
  `?phi rest. bb'.bb_instructions = phi :: rest /\ phi.inst_opcode = PHI` by
    (Cases_on `bb'.bb_instructions` >> gvs[phi_prefix_length_def] >>
     rename1 `h.inst_opcode` >> Cases_on `h.inst_opcode = PHI` >> gvs[]) >>
  qpat_x_assum `run_from _ _ _ _ = _` mp_tac >>
  simp[run_from_def, jump_to_def, Once exec_block_def, get_instruction_def,
       step_inst_non_invoke, step_inst_base_def] >> metis_tac[]
QED

(* Pure quotation abbreviation: no new HOL constant or definition. *)
val M = ``\ctx fn s st Q R.
    (?t. Q t /\ ~t.vs_halted /\
         t.vs_current_bb = st.cs_current_bb /\
         t.vs_inst_idx = LENGTH st.cs_current_insts /\
         !fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
                  ?fuel'. run_from fuel' ctx fn s = r /\
                    (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s)) \/
    (?fuel r. run_from fuel ctx fn s = r /\ exit_result r /\ R r /\
              mem_safe_run fuel ctx fn s)``;

Theorem mem_outcome_refl[local]:
  Q s /\ ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ^M ctx fn s st Q R
Proof
  simp[] >> strip_tac >> disj1_tac >> qexists_tac `s` >> simp[] >> metis_tac[]
QED

Theorem mem_outcome_apply[local]:
  frag_exec_mem ctx sa sb P Q R /\ fn_has_code sa sb fn /\
  P s /\ ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ^M ctx fn s sb Q R
Proof
  simp[frag_exec_mem_def] >> metis_tac[]
QED

Theorem mem_outcome_compose[local]:
  ^M ctx fn s sa P R /\
  (!t. P t /\ ~t.vs_halted /\ t.vs_current_bb = sa.cs_current_bb /\
       t.vs_inst_idx = LENGTH sa.cs_current_insts ==>
       ^M ctx fn t sb Q R) ==>
  ^M ctx fn s sb Q R
Proof
  simp[] >> strip_tac
  >- (first_x_assum drule >> simp[] >> strip_tac
      >- (rename1 `Q endpoint` >> disj1_tac >>
          qexists_tac `endpoint` >> simp[] >> metis_tac[]) >>
      disj2_tac >> metis_tac[exit_result_not_error]) >>
  disj2_tac >> metis_tac[]
QED

Theorem mem_outcome_jump[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  inst_mem_below_frontier inst s /\
  step_inst_base inst s = OK (jump_to lbl s) /\ ~s.vs_halted /\
  ^M ctx fn (jump_to lbl s) sb Q R ==>
  ^M ctx fn s sb Q R
Proof
  simp[] >> rpt strip_tac
  >- (rename1 `Q endpoint` >> disj1_tac >> qexists_tac `endpoint` >>
      simp[] >> rpt strip_tac >>
      qpat_x_assum `!fuel. _ ==> ?fuel'. _` drule >> strip_tac >>
      qexists_tac `SUC fuel'` >>
      conj_tac >- metis_tac[run_from_jump_result] >>
      metis_tac[mem_safe_run_jump_result]) >>
  disj2_tac >> qexists_tac `SUC fuel` >>
  `!e. run_from fuel ctx fn (jump_to lbl s) <> Error e` by
    metis_tac[exit_result_not_error] >>
  `run_from (SUC fuel) ctx fn s = run_from fuel ctx fn (jump_to lbl s)` by
    metis_tac[run_from_jump_result] >>
  simp[] >> metis_tac[mem_safe_run_jump_result]
QED

Theorem mem_outcome_jmp[local]:
  lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb (LENGTH sa.cs_current_insts) =
    SOME (mk_inst id JMP [Label lbl] []) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ^M ctx fn (jump_to lbl s) sb Q R ==>
  ^M ctx fn s sb Q R
Proof
  rpt strip_tac >> irule mem_outcome_jump >>
  goal_assum (drule_at Any) >>
  simp[mk_inst_def, is_terminator_def, step_inst_base_def] >>
  qexists_tac `lbl` >>
  simp[unitTransformDefsTheory.inst_mem_below_frontier_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def] >> metis_tac[]
QED

Theorem mem_outcome_jnz[local]:
  !sa fn bb id cnd exit body s w ctx sb Q R.
  lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb (LENGTH sa.cs_current_insts) =
    SOME (mk_inst id JNZ [cnd; Label exit; Label body] []) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand cnd s = SOME w /\
  ^M ctx fn (jump_to (if w = 0w then body else exit) s) sb Q R ==>
  ^M ctx fn s sb Q R
Proof
  rpt strip_tac >> irule mem_outcome_jump >>
  goal_assum (drule_at Any) >>
  simp[mk_inst_def, is_terminator_def, step_inst_base_def] >>
  Cases_on `w = 0w` >> gvs[] >>
  qmatch_goalsub_rename_tac `jump_to target s = jump_to _ s` >>
  qexists_tac `target` >>
  simp[unitTransformDefsTheory.inst_mem_below_frontier_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def] >> metis_tac[]
QED

Theorem frag_exec_loop_mem:
  !ctx st0 st1 sth stj st2 stb ste st3 stx hdr body exit cnd
   x0 x1 x2 x3 x4 x5 I J N R.
    emit_inst JMP [Label hdr] [] st0 = (x0, st1) /\
    new_block hdr st1 = (x1, sth) /\
    emit_inst JNZ [cnd; Label exit; Label body] [] stj = (x2, st2) /\
    new_block body st2 = (x3, stb) /\
    emit_inst JMP [Label hdr] [] ste = (x4, st3) /\
    new_block exit st3 = (x5, stx) /\
    cs_extends sth stj /\ cs_extends stb ste /\
    (!k s l. I k s ==> I k (jump_to l s)) /\
    (!k s l. J k s ==> J k (jump_to l s)) /\
    (!k. k <= N ==> frag_exec_mem ctx sth stj (I k) (J k) R) /\
    (!k s. k <= N /\ J k s ==>
           ?w. eval_operand cnd s = SOME w /\ (w = 0w <=> k < N)) /\
    (!k. k < N ==> frag_exec_mem ctx stb ste (J k) (I (SUC k)) R) ==>
    frag_exec_mem ctx st0 stx (I 0) (J N) R
Proof
  cheat
QED

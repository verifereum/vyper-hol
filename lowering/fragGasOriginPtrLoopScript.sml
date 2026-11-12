(* Zero-mark joint gas-origin pointer paths across control flow: a plain
   JMP edge, and a well-founded loop that reaches its exit through
   zero-mark iterations.  Straight-line runs use
   run_inst_seq_gas_origin_ptr_path; paths chain by
   gas_origin_ptr_path_append. *)
Theory fragGasOriginPtrLoop
Ancestors
  fragGasOriginPtr fragGasSeqPtr fragGasOrigin fragGasPathPtr ptrSafeRun
  ptrDiscipline venomExecSemantics venomExecProps venomInst venomInstProps venomState
  memSafeRun unitTransformDefs gasEvents relation list rich_list pair
  arithmetic

(* Zero-mark paths chain through an OK midpoint. *)
Theorem gas_origin_ptr_path_trans:
  gas_origin_ptr_path cx st [] (OK s1, G1, tn1) /\
  gas_origin_ptr_path cx (s1, G1, tn1) [] out ==>
  gas_origin_ptr_path cx st [] out
Proof
  strip_tac >> PairCases_on `out` >>
  drule gas_origin_ptr_path_append >> simp[] >>
  disch_then drule >> simp[]
QED

(* One straight-line non-GAS instruction, with its pointer check and ghost
   step as the backward towers state them. *)
Theorem step_origin_ptr_path:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
  i.inst_opcode <> GAS /\
  inst_mem_below_frontier i s /\ inst_dload_in_section i s /\
  ptr_safe_step D lo 0 ctx func PG G tn i s /\
  step_inst 0 ctx i s = OK u /\
  ghost_step 0 ctx PG G tn i s = (G', tn') ==>
  gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (s, G, tn) []
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx), G', tn')
Proof
  strip_tac >>
  `step_inst_base i s = OK u` by gvs[step_inst_non_invoke] >>
  `~u.vs_halted` by metis_tac[step_preserves_halted] >>
  `G' = step_prov PG G i u /\ tn' = step_taint i s u tn` by
    (qspecl_then [`0`, `ctx`, `PG`, `G`, `tn`, `i`, `s`, `u`] mp_tac
       ghost_step_non_invoke >> simp[]) >>
  `ptr_inst_ok D lo 0 ctx func G tn i s` by metis_tac[ptr_safe_step_inst_ok] >>
  mp_tac straight_line_origin_ptr_edge >> simp[] >> strip_tac >>
  `gas_origin_ptr_path (D, lo, explicit, ctx, func, PG)
     (u with vs_inst_idx := SUC s.vs_inst_idx, step_prov PG G i u,
      step_taint i s u tn) []
     (OK (u with vs_inst_idx := SUC s.vs_inst_idx), step_prov PG G i u,
      step_taint i s u tn)` by simp[gas_origin_ptr_path_rules] >>
  drule_all (cj 2 gas_origin_ptr_path_rules) >> simp[]
QED

Theorem prefix_trace_origin_ptr_indexed[local]:
  !xs k bb u g q.
    isPREFIX xs (DROP k bb.bb_instructions) /\
    lookup_block (u 0).vs_current_bb func.fn_blocks = SOME bb /\
    ~(u 0).vs_halted /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
               i.inst_opcode <> GAS) xs /\
    (!j. j < LENGTH xs ==>
      step_inst 0 ctx (EL j xs) ((u j) with vs_inst_idx := k + j) =
        OK ((u (SUC j)) with vs_inst_idx := k + j) /\
      inst_mem_below_frontier (EL j xs) ((u j) with vs_inst_idx := k + j) /\
      inst_dload_in_section (EL j xs) ((u j) with vs_inst_idx := k + j) /\
      ptr_safe_step D lo 0 ctx func PG (g j) (q j) (EL j xs)
        ((u j) with vs_inst_idx := k + j) /\
      ghost_step 0 ctx PG (g j) (q j) (EL j xs)
        ((u j) with vs_inst_idx := k + j) = (g (SUC j), q (SUC j))) ==>
    gas_origin_ptr_path (D, lo, explicit, ctx, func, PG)
      ((u 0) with vs_inst_idx := k, g 0, q 0) []
      (OK ((u (LENGTH xs)) with vs_inst_idx := k + LENGTH xs),
       g (LENGTH xs), q (LENGTH xs))
Proof
  Induct
  >- (rpt strip_tac >> simp[] >>
      irule (cj 1 gas_origin_ptr_path_rules) >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!j. j < LENGTH _ ==> _`
    (qspec_then `0` (strip_assume_tac o SRULE [])) >>
  fs[EVERY_DEF] >>
  `get_instruction bb k = SOME h /\ isPREFIX xs (DROP (SUC k) bb.bb_instructions)` by
    (Cases_on `DROP k bb.bb_instructions` >> gvs[] >>
     `k < LENGTH bb.bb_instructions` by
       (spose_not_then assume_tac >> gvs[DROP_LENGTH_TOO_LONG]) >>
     `DROP (SUC k) bb.bb_instructions = t` by
       (qspecl_then [`1`,`k`,`bb.bb_instructions`] mp_tac DROP_DROP >>
        simp[ADD1]) >>
     gvs[get_instruction_def] >>
     qspecl_then [`0`,`k`,`bb.bb_instructions`] mp_tac EL_DROP >> gvs[]) >>
  `(u 1).vs_current_bb = (u 0).vs_current_bb /\ ~(u 1).vs_halted` by
    (drule_all step_preserves_control_flow >>
     drule_all step_preserves_halted >> simp[]) >>
  qpat_x_assum `!k bb u g q. _`
    (qspecl_then [`SUC k`, `bb`, `u o SUC`, `g o SUC`, `q o SUC`] mp_tac) >>
  impl_tac
  >- (simp[] >> rpt strip_tac >>
      qpat_x_assum `!j. j < LENGTH _ ==> _` (qspec_then `SUC j` mp_tac) >>
      simp[ADD_CLAUSES]) >>
  simp[ADD_CLAUSES] >> strip_tac >>
  `gas_origin_ptr_path (D, lo, explicit, ctx, func, PG)
     ((u 0) with vs_inst_idx := k, g 0, q 0) []
     (OK ((u 1) with vs_inst_idx := SUC k), g 1, q 1)` by
    (mp_tac (Q.INST [`s` |-> `(u 0) with vs_inst_idx := k`, `i` |-> `h`,
                     `G` |-> `g 0`, `tn` |-> `q 0`,
                     `u` |-> `(u 1) with vs_inst_idx := k`,
                     `G'` |-> `g 1`, `tn'` |-> `q 1`] step_origin_ptr_path) >>
     simp[]) >>
  drule gas_origin_ptr_path_append >>
  disch_then (qspecl_then [`(u 1) with vs_inst_idx := SUC k`, `g 1`, `q 1`,
    `[]`, `OK ((u (SUC (LENGTH xs))) with vs_inst_idx := SUC (k + LENGTH xs))`,
    `g (SUC (LENGTH xs))`, `q (SUC (LENGTH xs))`] mp_tac) >>
  simp[]
QED

(* The forward twin of prefix_trace_ptr_safe_block: a checked trace of
   non-GAS straight-line instructions is one zero-mark joint path. *)
Theorem prefix_trace_origin_ptr_path:
  !xs bb s G tn u g q.
    ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX xs (DROP s.vs_inst_idx bb.bb_instructions) /\
    u 0 = s /\ g 0 = G /\ q 0 = tn /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
               i.inst_opcode <> GAS) xs /\
    (!j. j < LENGTH xs ==>
      step_inst 0 ctx (EL j xs) ((u j) with vs_inst_idx := s.vs_inst_idx + j) =
        OK ((u (SUC j)) with vs_inst_idx := s.vs_inst_idx + j) /\
      inst_mem_below_frontier (EL j xs)
        ((u j) with vs_inst_idx := s.vs_inst_idx + j) /\
      inst_dload_in_section (EL j xs)
        ((u j) with vs_inst_idx := s.vs_inst_idx + j) /\
      ptr_safe_step D lo 0 ctx func PG (g j) (q j) (EL j xs)
        ((u j) with vs_inst_idx := s.vs_inst_idx + j) /\
      ghost_step 0 ctx PG (g j) (q j) (EL j xs)
        ((u j) with vs_inst_idx := s.vs_inst_idx + j) = (g (SUC j), q (SUC j))) ==>
    gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (s, G, tn) []
      (OK ((u (LENGTH xs)) with vs_inst_idx := s.vs_inst_idx + LENGTH xs),
       g (LENGTH xs), q (LENGTH xs))
Proof
  rpt strip_tac >>
  `s with vs_inst_idx := s.vs_inst_idx = s` by
    simp[venom_state_component_equality] >>
  qspecl_then [`xs`, `s.vs_inst_idx`, `bb`, `u`, `g`, `q`] mp_tac
    prefix_trace_origin_ptr_indexed >>
  gvs[]
QED

(* A JMP keeps the ghost and lands on the jump target, as in
   emit_jump_path_ptr. *)
Theorem jmp_origin_ptr_path:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst iid JMP [Label lbl] []) /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ allocas_from lo s ==>
  gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (s, G, tn) []
    (OK (jump_to lbl s), G, tn)
Proof
  strip_tac >>
  `ptr_safe_step D lo 0 ctx func PG G tn (mk_inst iid JMP [Label lbl] []) s` by
    (simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
          mk_inst_def, source_memory_write_ranges_def,
          source_memory_read_ranges_def, op_taint_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke] >>
     simp[mk_inst_def, step_jmp_behavior, jump_to_def]) >>
  `gas_origin_ptr_edge (D, lo, explicit, ctx, func, PG) (s, G, tn) []
     (OK (jump_to lbl s), G, tn)` by
    (PURE_REWRITE_TAC[gas_origin_ptr_edge_def] >> conj_tac
     >- (rewrite_tac[gas_origin_edge_def] >> conj_tac >- simp[] >>
         qexistsl_tac [`0`, `bb`, `mk_inst iid JMP [Label lbl] []`,
                       `OK (jump_to lbl s)`] >>
         simp[step_inst_non_invoke, mk_inst_def, step_jmp_behavior,
              gas_events_step_def, is_terminator_def,
              mem_safe_step_non_invoke, inst_mem_below_frontier_def,
              inst_dload_in_section_def, source_memory_read_ranges_def,
              source_memory_write_ranges_def] >>
         metis_tac[]) >>
     rewrite_tac[gas_path_ptr_edge_def] >> simp[] >>
     qexists_tac `0:num` >>
     simp[step_inst_non_invoke, mk_inst_def, gas_count_step_def,
          step_jmp_behavior, is_terminator_def] >>
     fs[mk_inst_def] >> metis_tac[]) >>
  `~(jump_to lbl s).vs_halted` by simp[jump_to_def] >>
  `gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (jump_to lbl s, G, tn)
     [] (OK (jump_to lbl s), G, tn)` by simp[gas_origin_ptr_path_rules] >>
  drule_all (cj 2 gas_origin_ptr_path_rules) >> simp[]
QED

(* A loop whose every non-exit state P reaches a smaller P state by a
   zero-mark path reaches an exit state Q by a zero-mark path. *)
Theorem gas_origin_ptr_path_loop:
  !R P Q.
    WF R /\
    (!s G tn. P (s, G, tn) ==> ~s.vs_halted) /\
    (!s G tn. P (s, G, tn) /\ ~Q (s, G, tn) ==>
       ?s' G' tn'. P (s', G', tn') /\ R (s', G', tn') (s, G, tn) /\
         gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (s, G, tn) []
           (OK s', G', tn')) ==>
    !s G tn. P (s, G, tn) ==>
      ?s' G' tn'. P (s', G', tn') /\ Q (s', G', tn') /\
        gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (s, G, tn) []
          (OK s', G', tn')
Proof
  rpt gen_tac >> strip_tac >>
  `!x. P x ==>
     ?s' G' tn'. P (s', G', tn') /\ Q (s', G', tn') /\
       gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) x []
         (OK s', G', tn')` suffices_by
    (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  drule relationTheory.WF_INDUCTION_THM >> disch_then ho_match_mp_tac >>
  gen_tac >> PairCases_on `x` >> rpt strip_tac >>
  Cases_on `Q (x0, x1, x2)`
  >- (qexistsl_tac [`x0`, `x1`, `x2`] >> simp[] >>
      irule (cj 1 gas_origin_ptr_path_rules) >> metis_tac[]) >>
  qpat_x_assum `!s G tn. P _ /\ ~Q _ ==> _`
    (qspecl_then [`x0`, `x1`, `x2`] mp_tac) >>
  simp[] >> strip_tac >>
  qpat_x_assum `!y. R y _ ==> _` drule_all >> strip_tac >>
  qexistsl_tac [`s''`, `G''`, `tn''`] >> simp[] >>
  qpat_x_assum `gas_origin_ptr_path _ (x0, x1, x2) _ _`
    (assume_tac o MATCH_MP gas_origin_ptr_path_append) >>
  pop_assum (qspecl_then [`s'`, `G'`, `tn'`, `[]`, `OK s''`, `G''`, `tn''`]
    mp_tac) >>
  simp[]
QED

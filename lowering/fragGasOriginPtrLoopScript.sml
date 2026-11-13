(* Zero-mark joint gas-origin pointer paths across control flow: a plain
   JMP edge, and a well-founded loop that reaches its exit through
   zero-mark iterations.  Straight-line runs use
   run_inst_seq_gas_origin_ptr_path; paths chain by
   gas_origin_ptr_path_append. *)
Theory fragGasOriginPtrLoop
Ancestors
  fragGasOriginPtr fragGasSeqPtr fragGasOrigin fragGasPathPtr ptrSafeRun
  ptrDiscipline venomExecSemantics venomExecProps venomInst venomInstProps venomState
  memSafeRun unitTransformDefs gasEvents gasCount fragExecMem relation list rich_list pair
  arithmetic

(* Zero-mark paths chain through an OK midpoint. *)
Theorem gas_origin_ptr_path_trans:
  gas_origin_ptr_path cx st [] (OK s1, G1, tn1) /\
  gas_origin_ptr_path cx (s1, G1, tn1) [] out ==>
  gas_origin_ptr_path cx st [] out
Proof
  strip_tac >> PairCases_on `out` >>
  qspecl_then [`cx`,`st`,`[]`,`(OK s1,G1,tn1)`] mp_tac gas_origin_ptr_path_append >>
  impl_tac >- first_assum ACCEPT_TAC >> simp[] >>
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
    run_inst_seq_mem_ok xs ((u 0) with vs_inst_idx := k) /\
    (!j. j < LENGTH xs ==>
      step_inst 0 ctx (EL j xs) ((u j) with vs_inst_idx := k + j) =
        OK ((u (SUC j)) with vs_inst_idx := k + j) /\
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
  `EVERY (\i. ~is_terminator i.inst_opcode) xs` by fs[EVERY_MEM] >>
  `step_inst_base h ((u 0) with vs_inst_idx := k) =
     OK ((u 1) with vs_inst_idx := k)` by gvs[step_inst_non_invoke] >>
  `inst_mem_below_frontier h ((u 0) with vs_inst_idx := k) /\
   inst_dload_in_section h ((u 0) with vs_inst_idx := k) /\
   run_inst_seq_mem_ok xs ((u 1) with vs_inst_idx := SUC k)` by
    (qpat_x_assum `run_inst_seq_mem_ok (_::_) _` mp_tac >>
     simp[run_inst_seq_mem_ok_def]) >>
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
  >- (simp[] >> rpt strip_tac
      >~ [`run_inst_seq_mem_ok`]
      >- (drule run_inst_seq_mem_ok_inst_idx >>
          disch_then (qspecl_then [`u 1`, `SUC k`] (SUBST1_TAC o SYM)) >>
          first_assum ACCEPT_TAC) >>
      qpat_x_assum `!j. j < _ ==> _` (qspec_then `SUC j` mp_tac) >>
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
  qpat_x_assum `gas_origin_ptr_path _ ((u 0) with vs_inst_idx := k, g 0, q 0) [] _`
    (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
  disch_then (qspecl_then [`(u 1) with vs_inst_idx := SUC k`, `g 1`, `q 1`,
    `[]`, `OK ((u (SUC (LENGTH xs))) with vs_inst_idx := SUC (k + LENGTH xs))`,
    `g (SUC (LENGTH xs))`, `q (SUC (LENGTH xs))`] mp_tac) >>
  simp[]
QED

(* The forward twin of prefix_trace_ptr_safe_block: a memory-checked trace
   of non-GAS straight-line instructions is one zero-mark joint path. *)
Theorem prefix_trace_origin_ptr_path:
  !xs bb s G tn u g q.
    ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX xs (DROP s.vs_inst_idx bb.bb_instructions) /\
    u 0 = s /\ g 0 = G /\ q 0 = tn /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
               i.inst_opcode <> GAS) xs /\
    run_inst_seq_mem_ok xs s /\
    (!j. j < LENGTH xs ==>
      step_inst 0 ctx (EL j xs) ((u j) with vs_inst_idx := s.vs_inst_idx + j) =
        OK ((u (SUC j)) with vs_inst_idx := s.vs_inst_idx + j) /\
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

(* One pointer-checked step in front of a checked suffix. *)
Theorem inst_seq_ptr_cons_step:
  inst.inst_opcode <> INVOKE /\ step_inst 0 ctx inst s = OK t /\
  ptr_safe_step D lo 0 ctx func PG G tn inst s /\
  ghost_step 0 ctx PG G tn inst s = (H,qt) /\
  inst_seq_ptr D lo ctx func PG H qt ys
    (t with vs_inst_idx := SUC s.vs_inst_idx) G' tn' ==>
  inst_seq_ptr D lo ctx func PG G tn (inst::ys) s G' tn'
Proof
  strip_tac >>
  `step_inst_base inst s = OK t` by gvs[step_inst_non_invoke] >>
  qspecl_then [`0`,`ctx`,`PG`,`G`,`tn`,`inst`,`s`,`t`] mp_tac
    ghost_step_non_invoke >>
  simp[] >> strip_tac >> gvs[] >>
  simp[inst_seq_ptr_def] >> metis_tac[ptr_safe_step_inst_ok]
QED

Theorem prefix_trace_inst_seq_ptr_indexed[local]:
  !xs k u g q.
    EVERY (\i. i.inst_opcode <> INVOKE) xs /\
    (!j. j < LENGTH xs ==>
      step_inst 0 ctx (EL j xs) ((u j) with vs_inst_idx := k + j) =
        OK ((u (SUC j)) with vs_inst_idx := k + j) /\
      ptr_safe_step D lo 0 ctx func PG (g j) (q j) (EL j xs)
        ((u j) with vs_inst_idx := k + j) /\
      ghost_step 0 ctx PG (g j) (q j) (EL j xs)
        ((u j) with vs_inst_idx := k + j) = (g (SUC j), q (SUC j))) /\
    inst_seq_ptr D lo ctx func PG (g (LENGTH xs)) (q (LENGTH xs)) ys
      ((u (LENGTH xs)) with vs_inst_idx := k + LENGTH xs) G' tn' ==>
    inst_seq_ptr D lo ctx func PG (g 0) (q 0) (xs ++ ys)
      ((u 0) with vs_inst_idx := k) G' tn'
Proof
  Induct >- simp[] >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!j. j < LENGTH _ ==> _`
    (qspec_then `0` (strip_assume_tac o SRULE [])) >>
  fs[EVERY_DEF, ADD_CLAUSES] >>
  `step_inst_base h ((u 0) with vs_inst_idx := k) =
     OK ((u 1) with vs_inst_idx := k)` by gvs[step_inst_non_invoke] >>
  `ghost_step 0 ctx PG (g 0) (q 0) h ((u 0) with vs_inst_idx := k) =
     (step_prov PG (g 0) h ((u 1) with vs_inst_idx := k),
      step_taint h ((u 0) with vs_inst_idx := k)
        ((u 1) with vs_inst_idx := k) (q 0))` by
    (irule ghost_step_non_invoke >> simp[]) >>
  `g 1 = step_prov PG (g 0) h ((u 1) with vs_inst_idx := k) /\
   q 1 = step_taint h ((u 0) with vs_inst_idx := k)
     ((u 1) with vs_inst_idx := k) (q 0)` by
    (qpat_x_assum `ghost_step _ _ _ _ _ _ _ = (g 1, q 1)` mp_tac >> simp[]) >>
  `ptr_inst_ok D lo 0 ctx func (g 0) (q 0) h ((u 0) with vs_inst_idx := k)` by
    metis_tac[ptr_safe_step_inst_ok] >>
  qpat_x_assum `!k u g q. _`
    (qspecl_then [`SUC k`, `u o SUC`, `g o SUC`, `q o SUC`] mp_tac) >>
  impl_tac
  >- (simp[ADD_CLAUSES] >> rpt strip_tac >>
      qpat_x_assum `!j. j < _ ==> _` (qspec_then `SUC j` mp_tac) >>
      simp[ADD_CLAUSES]) >>
  simp[inst_seq_ptr_def]
QED

(* The trace a backward tower proves (prefix_trace_ptr_safe_block's facts at
   fuel 0) is the pointer check inst_seq_ptr along the same run, followed by
   any checked suffix. *)
Theorem prefix_trace_inst_seq_ptr:
  !xs s u g q.
    u 0 = s /\
    EVERY (\i. i.inst_opcode <> INVOKE) xs /\
    (!j. j < LENGTH xs ==>
      step_inst 0 ctx (EL j xs) ((u j) with vs_inst_idx := s.vs_inst_idx + j) =
        OK ((u (SUC j)) with vs_inst_idx := s.vs_inst_idx + j) /\
      ptr_safe_step D lo 0 ctx func PG (g j) (q j) (EL j xs)
        ((u j) with vs_inst_idx := s.vs_inst_idx + j) /\
      ghost_step 0 ctx PG (g j) (q j) (EL j xs)
        ((u j) with vs_inst_idx := s.vs_inst_idx + j) = (g (SUC j), q (SUC j))) /\
    inst_seq_ptr D lo ctx func PG (g (LENGTH xs)) (q (LENGTH xs)) ys
      ((u (LENGTH xs)) with vs_inst_idx := s.vs_inst_idx + LENGTH xs) G' tn' ==>
    inst_seq_ptr D lo ctx func PG (g 0) (q 0) (xs ++ ys) s G' tn'
Proof
  rpt strip_tac >>
  `s with vs_inst_idx := s.vs_inst_idx = s` by
    simp[venom_state_component_equality] >>
  qspecl_then [`xs`, `s.vs_inst_idx`, `u`, `g`, `q`] mp_tac
    prefix_trace_inst_seq_ptr_indexed >>
  gvs[]
QED

(* The joint twin of ctor_checked_emitted_endpoint: code emitted in place
   between two codegen states runs as one zero-mark joint path. *)
Theorem emitted_origin_ptr_path:
  fn_has_code st st' func /\ inst_extends st st' /\
  st'.cs_current_bb = st.cs_current_bb /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> GAS) (emitted_insts st st') /\
  run_inst_seq_mem_ok (emitted_insts st st') s /\
  inst_seq_ptr D lo ctx func PG G tn (emitted_insts st st') s H qt /\
  run_inst_seq (emitted_insts st st') s = OK t ==>
  gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (s, G, tn) []
    (OK (t with vs_inst_idx := LENGTH st'.cs_current_insts), H, qt)
Proof
  strip_tac >>
  `?bb. lookup_block st.cs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX st'.cs_current_insts bb.bb_instructions` by
    (gvs[fn_has_code_def, inst_extends_def] >> metis_tac[]) >>
  `?code. st'.cs_current_insts = st.cs_current_insts ++ code /\
          emitted_insts st st' = code` by
    (fs[inst_extends_def, IS_PREFIX_APPEND] >>
     simp[emitted_insts_def, DROP_LENGTH_APPEND]) >>
  `isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `isPREFIX st'.cs_current_insts _` mp_tac >>
     simp[IS_PREFIX_APPEND] >> strip_tac >> simp[IS_PREFIX_APPEND] >>
     rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> metis_tac[]) >>
  qpat_x_assum `emitted_insts st st' = code` (fn th => fs[th]) >>
  `FILTER (\i. i.inst_opcode = GAS) code = []` by fs[FILTER_EQ_NIL, EVERY_MEM] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code` by
    fs[EVERY_MEM] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  mp_tac (Q.SPECL [`code`, `s`, `t`, `G`, `tn`, `H`, `qt`, `ctx`, `func`, `bb`]
    run_inst_seq_gas_origin_ptr_path) >>
  simp[]
QED

(* A non-INVOKE terminator that lands on jump_to keeps the ghost, as in
   emit_jump_path_ptr. *)
Theorem jump_origin_ptr_path:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
  i.inst_opcode <> GAS /\
  inst_mem_below_frontier i s /\ inst_dload_in_section i s /\
  ptr_safe_step D lo 0 ctx func PG G tn i s /\
  step_inst_base i s = OK (jump_to lbl s) /\ ~s.vs_halted ==>
  gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (s, G, tn) []
    (OK (jump_to lbl s), G, tn)
Proof
  strip_tac >>
  `step_inst 0 ctx i s = OK (jump_to lbl s)` by simp[step_inst_non_invoke] >>
  `gas_origin_ptr_edge (D, lo, explicit, ctx, func, PG) (s, G, tn) []
     (OK (jump_to lbl s), G, tn)` by
    (PURE_REWRITE_TAC[gas_origin_ptr_edge_def] >> conj_tac
     >- (rewrite_tac[gas_origin_edge_def] >> conj_tac >- simp[] >>
         qexistsl_tac [`0`, `bb`, `i`, `OK (jump_to lbl s)`] >>
         simp[gas_events_step_def, mem_safe_step_non_invoke] >>
         metis_tac[]) >>
     rewrite_tac[gas_path_ptr_edge_def] >> conj_tac >- simp[] >>
     qexistsl_tac [`0`, `bb`, `i`, `OK (jump_to lbl s)`] >>
     simp[gas_count_step_def] >> metis_tac[]) >>
  `~(jump_to lbl s).vs_halted` by simp[jump_to_def] >>
  `gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (jump_to lbl s, G, tn)
     [] (OK (jump_to lbl s), G, tn)` by simp[gas_origin_ptr_path_rules] >>
  drule_all (cj 2 gas_origin_ptr_path_rules) >> simp[]
QED

Theorem jmp_origin_ptr_path:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst iid JMP [Label lbl] []) /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ allocas_from lo s ==>
  gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (s, G, tn) []
    (OK (jump_to lbl s), G, tn)
Proof
  strip_tac >>
  `step_inst_base (mk_inst iid JMP [Label lbl] []) s = OK (jump_to lbl s)` by
    simp[mk_inst_def, step_jmp_behavior] >>
  `ptr_safe_step D lo 0 ctx func PG G tn (mk_inst iid JMP [Label lbl] []) s` by
    (simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
          mk_inst_def, source_memory_write_ranges_def,
          source_memory_read_ranges_def, op_taint_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke] >>
     simp[mk_inst_def, step_jmp_behavior, jump_to_def]) >>
  mp_tac (Q.INST [`i` |-> `mk_inst iid JMP [Label lbl] []`]
    jump_origin_ptr_path) >>
  simp[] >>
  simp[mk_inst_def, is_terminator_def, inst_mem_below_frontier_def,
       inst_dload_in_section_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def]
QED

(* A JNZ on an untainted condition keeps the ghost and lands on the taken
   label. *)
Theorem jnz_origin_ptr_path:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst iid JNZ [cond; Label l1; Label l2] []) /\
  eval_operand cond s = SOME w /\ op_taint tn cond = {} /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ allocas_from lo s ==>
  gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (s, G, tn) []
    (OK (jump_to (if w <> 0w then l1 else l2) s), G, tn)
Proof
  strip_tac >>
  `step_inst_base (mk_inst iid JNZ [cond; Label l1; Label l2] []) s =
     OK (jump_to (if w <> 0w then l1 else l2) s)` by
    (simp[mk_inst_def] >> drule step_jnz_behavior >> rw[]) >>
  `ptr_safe_step D lo 0 ctx func PG G tn
     (mk_inst iid JNZ [cond; Label l1; Label l2] []) s` by
    (simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
          mk_inst_def, source_memory_write_ranges_def,
          source_memory_read_ranges_def, op_taint_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke] >>
     rw[jump_to_def]) >>
  mp_tac (Q.INST [`i` |-> `mk_inst iid JNZ [cond; Label l1; Label l2] []`,
                  `lbl` |-> `if w <> 0w then l1 else l2`]
    jump_origin_ptr_path) >>
  simp[] >>
  simp[mk_inst_def, is_terminator_def, inst_mem_below_frontier_def,
       inst_dload_in_section_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def]
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

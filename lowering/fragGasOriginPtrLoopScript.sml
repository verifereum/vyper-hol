(* Zero-mark joint gas-origin pointer paths across control flow: a plain
   JMP edge, and a well-founded loop that reaches its exit through
   zero-mark iterations.  Straight-line runs use
   run_inst_seq_gas_origin_ptr_path; paths chain by
   gas_origin_ptr_path_append. *)
Theory fragGasOriginPtrLoop
Ancestors
  fragGasOriginPtr fragGasSeqPtr fragGasOrigin fragGasPathPtr ptrSafeRun
  ptrDiscipline venomExecSemantics venomExecProps venomInst venomState memSafeRun
  unitTransformDefs gasEvents relation list pair

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

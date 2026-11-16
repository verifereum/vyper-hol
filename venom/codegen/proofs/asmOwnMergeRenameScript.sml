(* One global label rename preserves refinement with fixed own-code bytes. *)
Theory asmOwnMergeRename
Ancestors
  asmOwnMergeCodecopy asmOwnMergeStep asmOwnMergeSkip asmOwnMergeRun
  asmOptMergeJumpdests asmSymOwnCode asmSplice asmSymSem asmOptimizer
  asmWf asmSem list rich_list

Theorem rename_refines_own:
  (next = AsmLabel y /\ y <> x \/
   next = AsmPushLabel y /\ third = AsmOp "JUMP") ==>
  asm_refines_own (pre ++ AsmLabel x :: next :: third :: more)
    (MAP (rename_push_label x y)
      (pre ++ AsmLabel x :: next :: third :: more))
Proof
  disch_tac >>
  qabbrev_tac `P = pre ++ AsmLabel x :: next :: third :: more` >>
  simp[asm_refines_own_def, rename_filter_data] >> strip_tac >>
  `asm_static_wf (MAP (rename_push_label x y) P)`
    by (irule rename_static_wf >>
        qpat_x_assum `next = _ /\ _ \/ _` strip_assume_tac >>
        simp[Abbr `P`, asm_label_refs_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
        metis_tac[MEM, MEM_APPEND]) >>
  pop_assum (fn th => rewrite_tac [th]) >> rpt strip_tac >>
  `asm_labels_unique P` by fs[asm_static_wf_def] >>
  `INDEX_OF (AsmLabel x) P = SOME (LENGTH pre)`
    by (`~MEM (AsmLabel x) pre`
          by (irule asm_labels_unique_append_not_mem >>
              qexists_tac `AsmLabel x :: next :: third :: more` >>
              fs[Abbr `P`]) >>
        simp[Abbr `P`, INDEX_OF_APPEND, INDEX_OF_CONS]) >>
  irule rename_run_own_under >> conj_tac
  >- (rpt gen_tac >> strip_tac >> irule rename_step_own_under >>
      simp[] >> metis_tac[codecopy_rel_own]) >>
  simp[] >> reverse conj_tac
  >- simp[rn_rel_def, sym_init_def, ml_rel_def, mem_blocks_ok_def] >>
  rpt strip_tac >>
  irule rename_skip_own >> simp[] >>
  qexistsl_tac [`next`, `pre`, `third :: more`, `x`] >>
  fs[Abbr `P`]
QED

(* The label rename preserves each bound when both sides read installed code. *)
Theory asmOptWithinRename
Ancestors
  asmSpliceWithinOwn asmSpliceWithin asmRefinesWithin asmSymSemWithin
  asmOwnMergeRename asmOwnMergeCodecopy asmOwnMergeStep asmOptMergeJumpdests
  asmFinalizerPrefixRename asmSymPcOwn asmSpliceOwn asmSplice asmSymOwnCode
  asmSymSem asmOptimizer asmWf asmSem list rich_list

Theorem rename_site_within_own[local]:
  (next = AsmLabel y ∧ y ≠ x ∨ next = AsmPushLabel y ∧ third = AsmOp "JUMP") ==>
  asm_within_own (pre ++ AsmLabel x :: next :: third :: more)
    (MAP (rename_push_label x y) (pre ++ AsmLabel x :: next :: third :: more))
Proof
  disch_then assume_tac >>
  qabbrev_tac `p = pre ++ AsmLabel x :: next :: third :: more` >>
  BETA_TAC >> strip_tac >>
  `asm_static_wf (MAP (rename_push_label x y) p)` by
    (mp_tac (Q.INST [`pre` |-> `pre`, `more` |-> `more`] rename_refines_own) >>
     simp[Abbr `p`, asm_refines_own_def]) >>
  simp[] >>
  `asm_labels_unique p` by fs[asm_static_wf_def] >>
  `INDEX_OF (AsmLabel x) p = SOME (LENGTH pre)` by
    (`¬MEM (AsmLabel x) pre` by
       (irule asm_labels_unique_append_not_mem >>
        qexists_tac `AsmLabel x :: next :: third :: more` >> fs[Abbr `p`]) >>
     simp[Abbr `p`, INDEX_OF_APPEND, INDEX_OF_CONS]) >>
  qexists_tac `1` >> rpt gen_tac >> strip_tac >> simp[] >>
  qspecl_then [`p`, `LENGTH pre`, `x`, `y`, `env`, `P`, `Q`,
    `sym_step_own p env own`, `sym_step_own (MAP (rename_push_label x y) p) env own`]
    mp_tac rename_run_within_for >>
  (impl_tac >- suspend "step_and_skip") >>
  disch_then (qspecl_then [`k`, `sym_init s`, `sym_init s`] mp_tac) >>
  simp[rn_rel_def, sym_init_def, ml_rel_def, mem_blocks_ok_def]
QED

Resume rename_site_within_own[step_and_skip]:
  simp[] >> rpt conj_tac
  >- metis_tac[sym_step_own_base_stack]
  >- (mp_tac (MATCH_MP rename_step_own_under
        (GENL [``ss:sym_state``, ``ss':sym_state``] codecopy_rel_own)) >>
      simp[]) >>
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.INST [`sfx` |-> `third :: more`, `t` |-> `t`, `k` |-> `k'`,
    `R` |-> `P`, `stepf` |-> `sym_step_own p env own`,
    `runf` |-> `sym_steps_own p env own`] within_skip_for) >>
  simp[sym_steps_own_def] >>
  impl_tac >-
    (qpat_x_assum `next = _ ∧ _ ∨ _` strip_assume_tac >> gvs[Abbr `p`] >>
     rpt gen_tac >> strip_tac >>
     irule sym_steps_own_agree_on_window >>
     qexists_tac `LENGTH pre` >> simp[EL_APPEND_EQN] >>
     rpt gen_tac >> strip_tac >>
     `i = 0 \/ i = 1 \/ i = 2` by decide_tac >>
     gvs[] >> decide_tac) >>
  simp_tac bool_ss [Abbr `p`, GSYM APPEND_ASSOC, APPEND]
QED

Finalise rename_site_within_own

Theorem merge_jumpdests_within_own:
  asm_within_own p (FST (merge_jumpdests p))
Proof
  mp_tac (Q.SPEC `asm_within_own` merge_jumpdests_prefix_transport_for) >>
  (impl_tac >-
    (rpt conj_tac
     >- metis_tac[asm_within_own_refl]
     >- metis_tac[rename_site_within_own, rich_listTheory.APPEND_ASSOC_CONS] >>
     metis_tac[asm_within_own_trans])) >>
  BETA_TAC >> strip_tac >> strip_tac >> first_x_assum drule >> simp[]
QED

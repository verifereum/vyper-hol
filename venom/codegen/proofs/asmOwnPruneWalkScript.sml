(* The prune-unused walk is conditional on singleton deletion refinement.
   Only the window definitions, not the general splice theorem, are used. *)
Theory asmOwnPruneWalk
Ancestors
  asmSpliceOwn finalizerContractOwn asmSymOwnCode asmSplice asmSymPc
  asmSymSem asmOptimizer asmWf asmSem

Theorem unused_label_window_refines_own:
  asm_window_refines_own pfx [AsmLabel l] [] sfx
Proof
  rw[asm_window_refines_own_def] >>
  `LENGTH pfx < LENGTH (pfx ++ [AsmLabel l] ++ sfx) /\
   EL (LENGTH pfx) (pfx ++ [AsmLabel l] ++ sfx) = AsmLabel l`
    by simp[listTheory.EL_APPEND_EQN] >>
  qexistsl_tac [`SUC 0`, `0`] >>
  simp[sym_steps_own_def, sym_step_own_def, sym_step_def, sym_lift_def,
       asm_step_def, asm_next_def, sym_terminal_def] >>
  simp[splice_pc_def, sym_with_pc_def, sym_state_component_equality,
       asm_state_component_equality]
QED

Theorem filter_unused_refines_own_under:
  (!pfx l sfx. ~MEM l (asm_label_refs (pfx ++ [AsmLabel l] ++ sfx)) ==>
     asm_refines_own (pfx ++ [AsmLabel l] ++ sfx) (pfx ++ sfx)) ==>
  !sfx pfx. (!l. MEM l (asm_label_refs (pfx ++ sfx)) ==> MEM l used) ==>
    asm_refines_own (pfx ++ sfx)
      (pfx ++ FILTER ($~ o asm_unused_label used) sfx)
Proof
  strip_tac >> Induct >- simp[asm_refines_own_refl] >>
  rpt strip_tac >> reverse (Cases_on `asm_unused_label used h`) >> simp[]
  >- (first_x_assum (qspec_then `pfx ++ [h]` mp_tac) >>
      REWRITE_TAC[GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >>
      disch_then irule >> simp[]) >>
  Cases_on `h` >> gvs[asm_unused_label_def] >>
  rename1 `AsmLabel l0` >>
  irule asm_refines_own_trans >>
  qexists_tac `pfx ++ sfx` >>
  `!l. MEM l (asm_label_refs (pfx ++ sfx)) ==> MEM l used`
    by (qpat_assum `!l. MEM l (asm_label_refs (pfx ++ AsmLabel l0 :: sfx)) ==> _`
          mp_tac >>
        simp[label_refs_append, asm_label_refs_def]) >>
  `~MEM l0 (asm_label_refs (pfx ++ AsmLabel l0 :: sfx))`
    by metis_tac[] >>
  simp[] >>
  first_x_assum (qspecl_then [`pfx`, `l0`, `sfx`] mp_tac) >>
  REWRITE_TAC[GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >>
  simp[]
QED

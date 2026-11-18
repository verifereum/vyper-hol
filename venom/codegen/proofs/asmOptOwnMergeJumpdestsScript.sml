(* Label renaming with fixed own-code bytes. The existing rename relation
   keeps concrete words equal, so both concrete CODECOPY operands and
   CODESIZE results agree. Label-source copies retain the data-label
   discipline; the existing stack and memory-label relations apply. *)
Theory asmOptOwnMergeJumpdests
Ancestors
  asmOwnMergeWalk asmOwnMergeRename asmSymOwnCode asmOptimizer

Theorem merge_jumpdests_refines_own:
  ∀p. asm_refines_own p (FST (merge_jumpdests p))
Proof
  gen_tac >>
  mp_tac merge_jumpdests_walk_refines_own_under >>
  impl_tac >- metis_tac[rename_refines_own] >>
  disch_then (qspecl_then [`LENGTH p`, `[]`, `p`, `F`] mp_tac) >>
  simp[merge_jumpdests_def]
QED

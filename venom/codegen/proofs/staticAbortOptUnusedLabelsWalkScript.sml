Theory staticAbortOptUnusedLabelsWalk
Ancestors
  asmOptimizer asmSplice

(* Only one-label deletion is assumed; the filter traversal and preservation
   of its fixed reference list are proved here. No execution premise is used. *)
Theorem unused_labels_filter_preserves_contextual:
  (!pre l tail.
     ~MEM l (asm_label_refs (pre ++ [AsmLabel l] ++ tail)) /\
     P (pre ++ [AsmLabel l] ++ tail) ==> P (pre ++ tail)) ==>
  !p. P p ==> P (FST (prune_unused_jumpdests p))
Proof
  strip_tac >>
  `!rest pre used.
     used = asm_label_refs (pre ++ rest) /\ P (pre ++ rest) ==>
     P (pre ++ FILTER ($~ o asm_unused_label used) rest)`
    suffices_by
      (strip_tac >> gen_tac >>
       first_x_assum
         (qspecl_then [`p`, `[]`, `asm_label_refs p`] mp_tac) >>
       simp[prune_unused_jumpdests_def]) >>
  Induct >- simp[] >>
  rpt gen_tac >> strip_tac >>
  reverse (Cases_on `asm_unused_label used h`) >> simp[]
  >- (first_x_assum (qspecl_then [`pre ++ [h]`, `used`] mp_tac) >>
      rewrite_tac[GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >>
      gvs[] >>
      pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >>
      rewrite_tac[]) >>
  Cases_on `h` >> gvs[asm_unused_label_def] >>
  rename1 `AsmLabel l` >>
  `asm_label_refs (pre ++ AsmLabel l :: rest) =
   asm_label_refs (pre ++ rest)` by
    simp[label_refs_append, asm_label_refs_def] >>
  rule_assum_tac
    (REWRITE_RULE[GSYM listTheory.APPEND_ASSOC, listTheory.APPEND]) >>
  `P (pre ++ rest)` by
    (qpat_x_assum `!pre l tail. _` irule >>
     qexists_tac `l` >>
     pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >>
     asm_rewrite_tac[]) >>
  asm_rewrite_tac[] >> first_x_assum irule >> asm_rewrite_tac[]
QED

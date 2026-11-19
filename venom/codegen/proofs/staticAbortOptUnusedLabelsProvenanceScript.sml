Theory staticAbortOptUnusedLabelsProvenance
Ancestors
  asmOptPruneUnused asmSplice asmSymSem asmSem blockSimHelpers
  staticAbortTrace symbolResolve

(* All three reference constructors are needed. In particular an offset
   push remains provenance even if its current numeric value is a jump
   target of a different shape. This claim is about a tag's label identity,
   not about aliases between byte offsets. *)
Theorem unused_label_excludes_provenanced_incoming_tag:
  ~MEM l (asm_label_refs p) /\
  (!k t d. tags k = SOME (t,d) ==>
     MEM (AsmPushLabel t) p \/ MEM (AsmPushOfst t d) p \/
     MEM (AsmDataLabel t) p) ==>
  !k d. tags k <> SOME (l,d)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!k t d. _` drule >> strip_tac
  >- (`MEM l (asm_label_refs p)` by
        (rewrite_tac[asmOptimizerTheory.asm_label_refs_def,
                     listTheory.MEM_FLAT, listTheory.MEM_MAP, PULL_EXISTS] >>
         qexists `[l]` >> reverse conj_tac >- simp[] >>
         qexists `AsmPushLabel l` >> simp[]) >> gvs[])
  >- (`MEM l (asm_label_refs p)` by
        (rewrite_tac[asmOptimizerTheory.asm_label_refs_def,
                     listTheory.MEM_FLAT, listTheory.MEM_MAP, PULL_EXISTS] >>
         qexists `[l]` >> reverse conj_tac >- simp[] >>
         qexists `AsmPushOfst l d` >> simp[]) >> gvs[]) >>
  `MEM l (asm_label_refs p)` by
    (rewrite_tac[asmOptimizerTheory.asm_label_refs_def,
                 listTheory.MEM_FLAT, listTheory.MEM_MAP, PULL_EXISTS] >>
         qexists `[l]` >> reverse conj_tac >- simp[] >>
     qexists `AsmDataLabel l` >> simp[]) >> gvs[]
QED

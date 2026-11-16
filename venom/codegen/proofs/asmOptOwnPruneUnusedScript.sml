(* First client of the shared own-code splice simulation. *)
Theory asmOptOwnPruneUnused
Ancestors symbolResolve[qualified,ignore_grammar]
  asmOwnPruneWalk asmSpliceOwn asmSymPcOwn finalizerContractOwn
  asmSplice asmSymPc asmSymOwnCode asmSymSem asmOptimizer asmWf asmSem

Theorem prune_unused_jumpdests_refines_own:
  ∀p. asm_refines_own p (FST (prune_unused_jumpdests p))
Proof
  gen_tac >>
  mp_tac (Q.INST [`used` |-> `asm_label_refs p`]
    filter_unused_refines_own_under) >>
  impl_tac
  >- (rpt strip_tac >>
      mp_tac (Q.INST [`pat` |-> `[AsmLabel l]`, `repl` |-> `[]`]
        asm_splice_window_refines_own) >>
      impl_tac
      >- (simp[asm_splice_ok_def, unused_label_window_refines_own,
              is_data_inst_def, asm_label_refs_def,
              symbolResolveTheory.asm_inst_size_def] >> (gvs[asm_splice_ok_def, unused_label_window_refines_own, is_data_inst_def, asm_label_refs_def, symbolResolveTheory.asm_inst_size_def])) >>
      simp[]) >>
  disch_then (qspecl_then [`p`, `[]`] mp_tac) >>
  simp[prune_unused_jumpdests_def]
QED

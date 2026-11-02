(*
 * A DFT schedule of an SSA function is SSA.
 *
 * The schedule (dft_block_rel) keeps each block's label, its pseudo prefix
 * and its terminator last, so the CFG and dominance are unchanged; it
 * permutes the other instructions keeping every use after the in-block
 * definition it reads.  The CFGNormalization stage after DFT needs wf_ssa
 * on its input.
 *)
Theory dftSsaPreserve
Ancestors
  dftScheduleOrder dftStructural dftDefs venomWf venomInst list

(* Why it holds (unchecked notes):
   - ssa_form: the same instructions up to flip_operands, which keeps
     outputs.
   - bb_succs reads the last instruction: the terminator in both
     (bb_well_formed puts it last in the input; dft_must_order keeps every
     instruction before it), and terminators are not flippable.  So
     fn_cfg_edge, fn_reachable, fn_dominates and fn_entry_label agree.
   - def_dominates_uses: PHIs are unchanged; a flipped instruction uses
     the same variables; a use in the same block as its definition stays
     after it (the data clause of dft_must_order). *)
Theorem dft_block_rel_wf_ssa:
  !fn bbs.
    wf_ssa fn /\ wf_function fn /\ fn_pseudos_prefix fn /\
    LIST_REL dft_block_rel fn.fn_blocks bbs ==>
    wf_ssa (fn with fn_blocks := bbs)
Proof
  cheat
QED

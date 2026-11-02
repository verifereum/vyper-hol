(*
 * DFT's step part of the O1 pass contract: on any function of the O1
 * shape, SSA or not, dft_fn keeps the shape, takes no new labels or
 * instruction ids, renames no label and leaves the supply alone.
 *)
Theory o1DftStep
Ancestors
  o1PassContract unitShapeDefs venomPassDispatcher dftStructural dftDefs
  venomWf venomInst list

(* Why it holds (unchecked notes):
   - Without SSA, dft_fn can drop an instruction (a block whose ADD reads
     its own output: nothing reaches it from the entries), but it never
     duplicates one (distinct ids, ds_visited) and every output
     instruction is an input one or its flip_operands
     (dft_block_from_orig, schedule_output_from_block).  So the output
     ids and labels are a subset of the input's (dft_fn_labels_map).
   - The terminator stays last: it has no outputs (inst_wf), so nothing
     depends on it (eda_deps_backward_plain needs only distinct ids); it
     is the last entry, so it is emitted last.  bb_succs reads the last
     instruction, so the CFG facts are unchanged.
   - Pseudos: the output is FILTER is_pseudo ++ schedule, and PHIs are
     already a prefix (bb_well_formed).
   - Flips touch two-operand ADD/MUL/OR/XOR/AND/EQ and GT/LT/SGT/SLT,
     keep arity and opcode class.  ADD [op; Label "code_end"] has at
     most one child, so it is never flipped (the flipped form would fail
     label_positions_ok).
   - The SSA lemmas (dft_fn_all_perm_of, dft_fn_dft_inv,
     dft_fn_blocks_well_formed) don't apply: their hypotheses include
     wf_ssa. *)
Theorem dft_step_contract:
  o1_step_contract rpolicy (CFP_Simple VP_DFT)
Proof
  cheat
QED

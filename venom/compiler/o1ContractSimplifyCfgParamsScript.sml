(*
 * SimplifyCFG keeps the parameter layout the O1 function row asks for
 * from stage 4 on: pseudo instructions (PHIs and parameters) lead every
 * block, and only the first block has parameters.
 *
 * TOP-LEVEL:
 *   simplify_cfg_fn_param_prefix
 *)
Theory o1ContractSimplifyCfgParams
Ancestors
  o1PassContract simplifyCfgCollapseShape simplifyCfgInvariant
  simplifyCfgDefs callLayoutDefs venomWf venomInst cfgTransform
  list rich_list

(* Why it holds (intuition, not a prescribed proof).

   The first block keeps its label and stays first: it has no
   predecessors (first_block_no_preds), so neither a chain merge nor a
   jump bypass removes it, and it is reachable, so unreachable-block
   removal keeps it.  It has no PHI (first_block_no_phi), so the PHI
   fixup leaves it alone, and a chain merge into it appends a block with
   no PHI (can_merge_blocks) and, being a non-first block, no parameter,
   after FRONT of a pseudo-prefixed list.  Every other block has no
   parameter: chain merges and bypasses only rewrite operands and turn a
   JNZ into a JMP, so they keep every opcode except at the merged block,
   and the PHI fixup puts the remaining PHIs first (fix_phis_in_block),
   so with no parameters its pseudos are exactly its leading PHIs.  The
   block-label substitution leaves bb_label and opcodes alone. *)
Theorem simplify_cfg_fn_param_prefix:
  o1_fn_shape C fn /\ fn_pseudos_prefix fn /\
  EVERY (\bb. no_param_insts bb.bb_instructions) (TL fn.fn_blocks) ==>
  fn_pseudos_prefix (simplify_cfg_fn fn) /\
  EVERY (\bb. no_param_insts bb.bb_instructions)
    (TL (simplify_cfg_fn fn).fn_blocks)
Proof
  cheat
QED

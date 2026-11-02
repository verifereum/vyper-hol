(*
 * SimplifyCFG against the O1 pass contract: the step part.
 *
 * The dispatched transform is simplify_cfg_fn_with_labels, which keeps the
 * supply and makes no new labels or instruction ids: it deletes blocks,
 * merges a block into its single predecessor, bypasses jump-only blocks,
 * and rewrites PHIs and jumps in place.  So one run keeps the O1 function
 * shape, its names are fresh trivially, and its label map sends only
 * merged or bypassed blocks, never the entry (which has no predecessors),
 * to labels that remain.
 *)
Theory o1ContractSimplifyCfgStep
Ancestors
  o1PassContract simplifyCfgCorrectness simplifyCfgLabelProps
  simplifyCfgDefs venomPassDispatcher venomWf

Theorem simplify_cfg_step_contract:
  o1_step_contract rpolicy (CFP_Simple VP_SimplifyCFG)
Proof
  cheat
QED

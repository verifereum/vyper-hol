(*
 * The syntactic half of MakeSSA's pointer discipline: the pass keeps
 * fn_ptr_ok P, of the function and of its reachable part.
 *)
Theory o1ContractMakeSsaPtrOk
Ancestors
  ptrDiscipline pointerConfinedDefs pointerConfinedProps unitShapeDefs
  venomWf cfgWf o1PassContract makeSsaCurrentDefs makeSsaCurrentProps
  makeSsaCurrentCfg makeSsaCurrentOrigin makeSsaCurrentWfSsa
  makeSsaCurrentInputOk makeSsaCurrentNonDegenerate

(* Why it holds.  make_ssa_current_fn_origin gives orig, from fn' vars to
   fn vars: each instruction of fn' is a renamed non-PHI of fn (same
   opcode and id, outputs and Var operands mapped by orig), a NOP, or a
   PHI/ASSIGN whose output w is a renamed output of some instruction of fn
   and whose Var operands u have orig u = orig w or are operands of the
   input PHI defining orig w.

   Forward: v' IN pointer_derived_vars fn' R' ==> orig v' IN
   pointer_derived_vars fn R, for R' = ptr_roots P fn', alloca_roots fn',
   and ptr_roots P fn' DIFF alloca_roots fn' against the matching R of fn
   (pointer_use_vars_least).  For the last one, a DALLOCA or pointer PARAM
   output of fn is a pointer, so fn_ptr_ok's definition clause on fn puts
   it outside alloca_roots fn.

   Backward: a variable v' of fn' with orig v' IN fn_pv P fn is in
   fn_pv P fn'.  By induction on where v' is defined, ordered by the
   shortest CFG distance of its block from the entry, then by its index:
   fn_defs_reach_uses fn' and all_reachable fn' (make_ssa_current_fn_input_ok)
   put a definition of each operand earlier on a shortest path (a PHI
   operand's at the end of the predecessor the shortest path comes
   through, fn_phis_cover_preds fn').  The definition of v' is, by fn's
   definition clause, a root (and a root of fn'), or pointer-preserving
   with a pointer operand; a PHI or ASSIGN of the second kind has only
   pointer operands (fn's clause and phi_pv_all_var fn), and has at least
   one (ASSIGN: origin; PHI: make_ssa_current_fn_phis_non_degenerate, and
   no PHI sits in the entry block: its pairs are CFG edges into the block,
   make_ssa_current_fn_cfg, first_block_no_preds).

   Then each conjunct of fn_ptr_ok P fn' follows from fn's: per
   instruction through orig and forward inclusion; the LT/GT/EQ exemption
   and phi_pv_all_var need backward inclusion; the definition clause on
   fn' follows from SSA (wf_ssa fn', make_ssa_current_fn_wf_ssa: one
   definition per variable) and fn' pv being the least closure.

   Every Var operand of a PHI of fn' sits in a (Label, Var) pair whose
   label is a CFG edge into its block: wf_ssa fn' gives phi_edge_uses_wf,
   hence phi_well_formed (phi_well_formed_var_pair).  So the backward
   induction reaches every PHI operand, and with all_reachable fn'
   filter_phi_ops drops nothing: reachable_fn fn' = fn'. *)
Theorem make_ssa_current_fn_ptr_ok:
  make_ssa_input_ok fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (fn',s') /\ fn_ptr_ok P fn ==>
  fn_ptr_ok P fn' /\ fn_ptr_ok P (reachable_fn fn')
Proof
  cheat
QED

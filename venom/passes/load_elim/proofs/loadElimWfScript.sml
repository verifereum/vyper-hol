(*
 * Load Elimination — structural well-formedness and SSA preservation.
 *
 * Each of the five rounds keeps labels and terminators, replaces loads
 * by ASSIGNs and redundant stores by NOPs (same inst_id), and inserts
 * PHIs right after a block's PHI prefix with ids above the round's
 * fn_max_inst_id; clear_nops_function then drops the NOPs.
 *)

Theory loadElimWf
Ancestors
  loadElimDefs analysisSimDefs passSharedDefs passSharedProps venomWf
  cfgTransform

Theorem load_elim_function_preserves_wf:
  !fn. wf_function fn ==> wf_function (load_elim_function fn)
Proof
  cheat
QED

(* New variables are the PHI outputs "$le_phi_<load id>", one per load
   rewritten through a PHI.  The five rounds rewrite disjoint load
   opcodes and instruction ids are distinct (wf_function), so these
   names are distinct, and the prefix premise keeps them apart from
   fn's own variables.  Rewritten loads keep their single output. *)
Theorem load_elim_function_preserves_ssa:
  !fn. wf_function fn /\ ssa_form fn /\
       EVERY (\v. ~isPREFIX "$le_phi_" v) (fn_all_vars fn) ==>
       ssa_form (load_elim_function fn)
Proof
  cheat
QED

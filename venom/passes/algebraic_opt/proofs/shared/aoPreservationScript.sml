(* Structural preservation through phases 1-3.
 *
 * TOP-LEVEL: ao_phases123_preserve_wf
 *)

Theory aoPreservation
Ancestors
  algebraicOptDefs aoWf
  venomWf venomInst
Libs
  BasicProvers

Theorem ao_phases123_preserve_wf:
  !fn.
    let fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks in
    let targets = ao_compute_fn_iszero_targets fn0 in
    let dfg = dfg_build_function fn0 in
    let ra = range_analyze fn0 in
    let mid = fn_max_inst_id fn0 in
    let fn1 = fn0 with fn_blocks :=
      MAP (ao_transform_block mid dfg ra targets) fn0.fn_blocks in
    wf_function fn /\ ssa_form fn /\ EVERY inst_wf (fn_insts fn) ==>
    wf_function fn1 /\ ssa_form fn1 /\
    EVERY inst_wf (fn_insts fn1)
Proof
  cheat
QED

val _ = export_theory();

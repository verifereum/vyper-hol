(* Phase 5 WF/SSA preservation: ao_or_truthy_function preserves wf_function
 * and ssa_form.
 *
 * The OR-truthy rewrite is a length-preserving 1:1 MAP that keeps inst_id and
 * inst_outputs, leaves terminators and PHIs untouched, and only ever turns OR
 * into ASSIGN — so the generic map_transform preservation lemmas apply.
 *
 * TOP-LEVEL: ao_phase5_preserves_wf, ao_phase5_preserves_ssa
 *)

Theory aoPhase5Wf
Ancestors
  algebraicOptDefs
  passSimulationProps passSimulationDefs
  venomWf venomInst
Libs
  BasicProvers

val _ = delsimps ["ao_or_truthy_scan_def", "ao_or_truthy_apply_inst_def"]

(* fn_insts commutes with a 1:1 block map. *)
Triviality fn_insts_block_map[local]:
  !f fn.
    fn_insts (function_map_transform (block_map_transform f) fn) =
    MAP f (fn_insts fn)
Proof
  rpt gen_tac >>
  simp[function_map_transform_def, fn_insts_def] >>
  qspec_tac (`fn.fn_blocks`,`bbs`) >>
  Induct >>
  simp[fn_insts_blocks_def, block_map_transform_def, listTheory.MAP_APPEND]
QED

(* ===== Per-instruction shape facts for ao_or_truthy_apply_inst ===== *)

Triviality apply_inst_id[local]:
  !ids inst. (ao_or_truthy_apply_inst ids inst).inst_id = inst.inst_id
Proof
  rw[ao_or_truthy_apply_inst_def]
QED

Triviality apply_term_id[local]:
  !ids inst.
    is_terminator inst.inst_opcode ==> ao_or_truthy_apply_inst ids inst = inst
Proof
  rw[ao_or_truthy_apply_inst_def] >> gvs[is_terminator_def]
QED

Triviality apply_nonterm[local]:
  !ids inst.
    ~is_terminator inst.inst_opcode ==>
    ~is_terminator (ao_or_truthy_apply_inst ids inst).inst_opcode
Proof
  rw[ao_or_truthy_apply_inst_def] >> gvs[is_terminator_def]
QED

Triviality apply_phi[local]:
  !ids inst.
    inst.inst_opcode = PHI ==> (ao_or_truthy_apply_inst ids inst).inst_opcode = PHI
Proof
  rw[ao_or_truthy_apply_inst_def]
QED

Triviality apply_nonphi[local]:
  !ids inst.
    inst.inst_opcode <> PHI ==>
    (ao_or_truthy_apply_inst ids inst).inst_opcode <> PHI
Proof
  rw[ao_or_truthy_apply_inst_def]
QED

Triviality apply_outputs[local]:
  !ids inst.
    (ao_or_truthy_apply_inst ids inst).inst_outputs = inst.inst_outputs
Proof
  rw[ao_or_truthy_apply_inst_def]
QED

(* ao_or_truthy_function as a function_map_transform (block_map_transform f). *)
Triviality or_truthy_as_map_transform[local]:
  !fn.
    ~NULL (ao_or_truthy_scan (dfg_build_function fn) (fn_insts fn)) ==>
    ao_or_truthy_function (dfg_build_function fn) fn =
    function_map_transform
      (block_map_transform
        (ao_or_truthy_apply_inst
           (ao_or_truthy_scan (dfg_build_function fn) (fn_insts fn)))) fn
Proof
  rpt strip_tac >>
  simp[ao_or_truthy_function_def, LET_THM, function_map_transform_def,
       ir_function_component_equality, listTheory.MAP_EQ_f,
       block_map_transform_def]
QED

Triviality or_truthy_null_id[local]:
  !fn.
    NULL (ao_or_truthy_scan (dfg_build_function fn) (fn_insts fn)) ==>
    ao_or_truthy_function (dfg_build_function fn) fn = fn
Proof
  rpt strip_tac >> simp[ao_or_truthy_function_def, LET_THM]
QED

(* ===== Top-level preservation ===== *)

Theorem ao_phase5_preserves_wf:
  !fn. wf_function fn ==>
    wf_function (ao_or_truthy_function (dfg_build_function fn) fn)
Proof
  rpt strip_tac >>
  Cases_on `NULL (ao_or_truthy_scan (dfg_build_function fn) (fn_insts fn))`
  >- (`ao_or_truthy_function (dfg_build_function fn) fn = fn` by
        (irule or_truthy_null_id >> simp[]) >> simp[]) >>
  `ao_or_truthy_function (dfg_build_function fn) fn =
   function_map_transform
     (block_map_transform
       (ao_or_truthy_apply_inst
          (ao_or_truthy_scan (dfg_build_function fn) (fn_insts fn)))) fn` by
    (irule or_truthy_as_map_transform >> simp[]) >>
  pop_assum (fn th => REWRITE_TAC[th]) >>
  irule map_transform_preserves_wf >>
  simp[apply_inst_id, apply_term_id, apply_nonterm, apply_phi, apply_nonphi]
QED

(* SSA only depends on FLAT (MAP inst_outputs (fn_insts fn)); the OR-truthy
   rewrite preserves inst_outputs exactly, so no wf_function is required. *)
Theorem ao_phase5_preserves_ssa:
  !fn. ssa_form fn ==>
    ssa_form (ao_or_truthy_function (dfg_build_function fn) fn)
Proof
  rpt strip_tac >>
  Cases_on `NULL (ao_or_truthy_scan (dfg_build_function fn) (fn_insts fn))`
  >- (`ao_or_truthy_function (dfg_build_function fn) fn = fn` by
        (irule or_truthy_null_id >> simp[]) >> simp[]) >>
  `ao_or_truthy_function (dfg_build_function fn) fn =
   function_map_transform
     (block_map_transform
       (ao_or_truthy_apply_inst
          (ao_or_truthy_scan (dfg_build_function fn) (fn_insts fn)))) fn` by
    (irule or_truthy_as_map_transform >> simp[]) >>
  pop_assum (fn th => REWRITE_TAC[th]) >>
  fs[ssa_form_def, fn_insts_block_map, listTheory.MAP_MAP_o,
     combinTheory.o_DEF, apply_outputs]
QED


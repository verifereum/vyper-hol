(* Phase 1 WF & SSA preservation: ao_handle_offset_inst
 *
 * TOP-LEVEL:
 *   ao_phase1_preserves_wf  — wf_function preserved
 *   ao_phase1_preserves_ssa — ssa_form preserved
 *   ao_phase1_preserves_inst_wf — EVERY inst_wf preserved
 *)

Theory aoPhase1Wf
Ancestors
  algebraicOptDefs
  venomState venomWf venomInst passSimulationProps passSimulationDefs
  passSharedDefs list rich_list
Libs
  pairLib BasicProvers

(* ===== ao_handle_offset_inst preserves structural fields ===== *)

Theorem ao_handle_offset_inst_preserves_id:
  !inst. (ao_handle_offset_inst inst).inst_id = inst.inst_id
Proof
  gen_tac >> simp[ao_handle_offset_inst_def] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `h` >> simp[] >>
  Cases_on `h'` >> simp[] >>
  Cases_on `t'` >> simp[]
QED

Theorem ao_handle_offset_inst_outputs:
  !inst. (ao_handle_offset_inst inst).inst_outputs = inst.inst_outputs
Proof
  gen_tac >> simp[ao_handle_offset_inst_def] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `h` >> simp[] >>
  Cases_on `h'` >> simp[] >>
  Cases_on `t'` >> simp[]
QED

Triviality term_not_add[local]:
  !opc. is_terminator opc ==> opc <> ADD
Proof
  Cases >> simp[is_terminator_def]
QED

Theorem ao_handle_offset_inst_term:
  !inst. is_terminator inst.inst_opcode ==> ao_handle_offset_inst inst = inst
Proof
  rpt strip_tac >>
  `inst.inst_opcode <> ADD` by metis_tac[term_not_add] >>
  simp[ao_handle_offset_inst_def]
QED

Theorem ao_handle_offset_inst_not_term:
  !inst. ~is_terminator inst.inst_opcode ==>
    ~is_terminator (ao_handle_offset_inst inst).inst_opcode
Proof
  gen_tac >> simp[ao_handle_offset_inst_def] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `h` >> simp[] >>
  Cases_on `h'` >> simp[] >>
  Cases_on `t'` >> simp[is_terminator_def]
QED

Theorem ao_handle_offset_inst_phi:
  !inst. inst.inst_opcode = PHI ==>
    (ao_handle_offset_inst inst).inst_opcode = PHI
Proof
  simp[ao_handle_offset_inst_def]
QED

Theorem ao_handle_offset_inst_not_phi:
  !inst. inst.inst_opcode <> PHI ==>
    (ao_handle_offset_inst inst).inst_opcode <> PHI
Proof
  gen_tac >> simp[ao_handle_offset_inst_def] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `h` >> simp[] >>
  Cases_on `h'` >> simp[] >>
  Cases_on `t'` >> simp[]
QED

Theorem ao_handle_offset_inst_wf:
  !inst. inst_wf inst ==> inst_wf (ao_handle_offset_inst inst)
Proof
  gen_tac >> strip_tac >>
  simp[ao_handle_offset_inst_def] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `h` >> simp[] >>
  Cases_on `h'` >> simp[] >>
  Cases_on `t'` >> simp[] >>
  fs[inst_wf_def]
QED


(* ===== Phase 1 preserves wf_function ===== *)

Theorem ao_phase1_preserves_wf:
  !fn. wf_function fn ==>
    wf_function (function_map_transform
      (block_map_transform ao_handle_offset_inst) fn)
Proof
  rpt strip_tac >>
  irule map_transform_preserves_wf >> simp[] >>
  metis_tac[ao_handle_offset_inst_preserves_id,
            ao_handle_offset_inst_term,
            ao_handle_offset_inst_not_term,
            ao_handle_offset_inst_phi,
            ao_handle_offset_inst_not_phi]
QED

(* ===== Phase 1 preserves ssa_form ===== *)

Theorem ao_phase1_preserves_ssa:
  !fn. wf_function fn /\ ssa_form fn ==>
    ssa_form (function_map_transform
      (block_map_transform ao_handle_offset_inst) fn)
Proof
  rpt strip_tac >>
  irule map_transform_preserves_ssa >>
  simp[ao_handle_offset_inst_preserves_id, ao_handle_offset_inst_outputs]
QED

(* ===== Phase 1 preserves EVERY inst_wf ===== *)

Triviality fn_insts_blocks_every[local]:
  !blocks p. EVERY p (fn_insts_blocks blocks) <=>
    EVERY (\bb. EVERY p bb.bb_instructions) blocks
Proof
  Induct >> simp[fn_insts_blocks_def, listTheory.EVERY_APPEND]
QED

Triviality phase1_preserves_inst_wf_blocks[local]:
  !blocks. EVERY (\bb. EVERY inst_wf bb.bb_instructions) blocks ==>
    EVERY (\bb. EVERY inst_wf bb.bb_instructions)
      (MAP (block_map_transform ao_handle_offset_inst) blocks)
Proof
  Induct >> simp[] >> rpt strip_tac >>
  simp[block_map_transform_def, listTheory.EVERY_MAP, listTheory.EVERY_MEM] >>
  rpt strip_tac >> gvs[listTheory.MEM_MAP] >>
  irule ao_handle_offset_inst_wf >>
  fs[listTheory.EVERY_MEM]
QED

Theorem ao_phase1_preserves_inst_wf:
  !fn. EVERY inst_wf (fn_insts fn) ==>
    EVERY inst_wf (fn_insts (function_map_transform
      (block_map_transform ao_handle_offset_inst) fn))
Proof
  rpt strip_tac >>
  simp[fn_insts_def, function_map_transform_def] >>
  `EVERY (\bb. EVERY inst_wf bb.bb_instructions)
     (MAP (block_map_transform ao_handle_offset_inst) fn.fn_blocks)` suffices_by
    simp[fn_insts_blocks_every] >>
  irule phase1_preserves_inst_wf_blocks >>
  fs[fn_insts_def, fn_insts_blocks_every]
QED

(* ===== Phase 1 preserves iszero no-label property ===== *)


(* ===== Phase 1 preserves def_dominates_uses (hence wf_ssa) ===== *)

(* ao_handle_offset_inst never introduces Var operands *)
Theorem ao_handle_offset_inst_var_operand:
  !inst x. MEM (Var x) (ao_handle_offset_inst inst).inst_operands ==>
           MEM (Var x) inst.inst_operands
Proof
  rpt strip_tac >> qpat_x_assum `MEM _ _` mp_tac >>
  simp[ao_handle_offset_inst_def] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `h` >> simp[] >>
  Cases_on `h'` >> simp[] >>
  Cases_on `t'` >> simp[]
QED

Triviality all_distinct_map_inj_mem[local]:
  !f l x y. ALL_DISTINCT (MAP f l) /\ MEM x l /\ MEM y l /\ (f x = f y)
    ==> (x = y)
Proof
  metis_tac[MEM_EL, EL_MAP, ALL_DISTINCT_EL_IMP, LENGTH_MAP]
QED


Triviality fmt_bmt_entry_label[local]:
  !f fn. fn_entry_label (function_map_transform (block_map_transform f) fn) =
         fn_entry_label fn
Proof
  rpt gen_tac >>
  simp[fn_entry_label_def, entry_block_def, function_map_transform_def] >>
  Cases_on `fn.fn_blocks` >> simp[block_map_transform_def]
QED

Triviality bb_succs_last[local]:
  !bb. bb.bb_instructions <> [] ==>
       bb_succs bb = nub (REVERSE (get_successors (LAST bb.bb_instructions)))
Proof
  rpt strip_tac >> Cases_on `bb.bb_instructions` >> fs[bb_succs_def]
QED

Triviality ao_phase1_bb_succs[local]:
  !bb. bb_well_formed bb ==>
       bb_succs (block_map_transform ao_handle_offset_inst bb) = bb_succs bb
Proof
  rpt strip_tac >> fs[bb_well_formed_def] >>
  `bb.bb_instructions <> []` by (CCONTR_TAC >> fs[]) >>
  `MAP ao_handle_offset_inst bb.bb_instructions <> []` by
    (Cases_on `bb.bb_instructions` >> fs[]) >>
  simp[bb_succs_last, block_map_transform_def, LAST_MAP] >>
  `ao_handle_offset_inst (LAST bb.bb_instructions) = LAST bb.bb_instructions` by
    (irule ao_handle_offset_inst_term >> fs[]) >>
  simp[]
QED

Triviality ao_phase1_cfg_edge_eq[local]:
  !fn. wf_function fn ==>
       fn_cfg_edge
         (function_map_transform (block_map_transform ao_handle_offset_inst) fn) =
       fn_cfg_edge fn
Proof
  rw[FUN_EQ_THM, fn_cfg_edge_def, function_map_transform_def, MEM_MAP,
     PULL_EXISTS] >>
  eq_tac >> strip_tac >> gvs[] >>
  rename1 `MEM bk fn.fn_blocks` >> qexists_tac `bk` >>
  `bb_well_formed bk` by gvs[wf_function_def] >>
  gvs[block_map_transform_def, ao_phase1_bb_succs]
QED

Triviality ao_phase1_reachable_eq[local]:
  !fn. wf_function fn ==>
       fn_reachable
         (function_map_transform (block_map_transform ao_handle_offset_inst) fn) =
       fn_reachable fn
Proof
  rpt strip_tac >>
  simp[FUN_EQ_THM, fn_reachable_def, fmt_bmt_entry_label] >>
  `fn_cfg_edge
     (function_map_transform (block_map_transform ao_handle_offset_inst) fn) =
   fn_cfg_edge fn` by metis_tac[ao_phase1_cfg_edge_eq] >>
  simp[]
QED

Triviality ao_phase1_dominates_eq[local]:
  !fn. wf_function fn ==>
       fn_dominates
         (function_map_transform (block_map_transform ao_handle_offset_inst) fn) =
       fn_dominates fn
Proof
  rpt strip_tac >>
  `fn_cfg_edge
     (function_map_transform (block_map_transform ao_handle_offset_inst) fn) =
   fn_cfg_edge fn` by metis_tac[ao_phase1_cfg_edge_eq] >>
  `!path. is_fn_path
            (function_map_transform (block_map_transform ao_handle_offset_inst) fn)
            path <=> is_fn_path fn path` by
    (Induct >> simp[is_fn_path_def] >>
     Cases_on `path` >> gvs[is_fn_path_def]) >>
  simp[FUN_EQ_THM, fn_dominates_def, fmt_bmt_entry_label] >>
  metis_tac[ao_phase1_reachable_eq]
QED

Theorem ao_phase1_preserves_def_dominates_uses:
  !fn. wf_function fn /\ def_dominates_uses fn ==>
       def_dominates_uses
         (function_map_transform (block_map_transform ao_handle_offset_inst) fn)
Proof
  rpt strip_tac >>
  `fn_dominates
     (function_map_transform (block_map_transform ao_handle_offset_inst) fn) =
   fn_dominates fn` by metis_tac[ao_phase1_dominates_eq] >>
  simp[def_dominates_uses_def] >>
  qpat_x_assum `fn_dominates _ = fn_dominates fn` (fn th => simp[th]) >>
  simp[function_map_transform_def] >>
  rpt strip_tac >>
  `?bb_o. bb = block_map_transform ao_handle_offset_inst bb_o /\
          MEM bb_o fn.fn_blocks` by metis_tac[MEM_MAP] >>
  pop_assum strip_assume_tac >>
  qpat_x_assum `bb = _` SUBST_ALL_TAC >>
  `?inst_o. inst = ao_handle_offset_inst inst_o /\
            MEM inst_o bb_o.bb_instructions` by
     (fs[block_map_transform_def] >> metis_tac[MEM_MAP]) >>
  pop_assum strip_assume_tac >>
  qpat_x_assum `inst = _` SUBST_ALL_TAC >>
  drule ao_handle_offset_inst_var_operand >> strip_tac >>
  fs[def_dominates_uses_def] >>
  first_x_assum (qspecl_then [`bb_o`, `inst_o`, `v`] mp_tac) >>
  simp[] >> strip_tac >>
  rename1 `MEM def_bb fn.fn_blocks` >>
  rename1 `MEM def_inst def_bb.bb_instructions` >>
  qexistsl_tac [`block_map_transform ao_handle_offset_inst def_bb`,
                `ao_handle_offset_inst def_inst`] >>
  rpt conj_tac
  >- (simp[MEM_MAP] >> qexists_tac `def_bb` >> fs[])
  >- (simp[block_map_transform_def, MEM_MAP] >> qexists_tac `def_inst` >> fs[])
  >- fs[ao_handle_offset_inst_outputs]
  >- fs[block_map_transform_def]
  >- (strip_tac >>
      `def_bb.bb_label = bb_o.bb_label` by
        (qpat_x_assum
           `block_map_transform _ def_bb = block_map_transform _ bb_o` mp_tac >>
         simp[block_map_transform_def, basic_block_component_equality]) >>
      `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
        gvs[wf_function_def, fn_labels_def] >>
      `def_bb = bb_o` by
        (qspecl_then [`\b. b.bb_label`, `fn.fn_blocks`, `def_bb`, `bb_o`]
           mp_tac all_distinct_map_inj_mem >> simp[]) >>
      gvs[] >>
      qexistsl_tac [`i`, `j`] >>
      `i < LENGTH bb_o.bb_instructions` by
        metis_tac[arithmeticTheory.LESS_TRANS] >>
      simp[block_map_transform_def, EL_MAP])
QED

Theorem ao_phase1_preserves_wf_ssa:
  !fn. wf_function fn /\ wf_ssa fn ==>
       wf_ssa (function_map_transform
         (block_map_transform ao_handle_offset_inst) fn)
Proof
  rpt strip_tac >> fs[wf_ssa_def] >> conj_tac
  >- (irule ao_phase1_preserves_ssa >> simp[])
  >- (irule ao_phase1_preserves_def_dominates_uses >> simp[])
QED

val _ = export_theory();

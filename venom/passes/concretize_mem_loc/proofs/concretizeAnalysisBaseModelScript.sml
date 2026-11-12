(* Proof-only base-set model; offsets are intentionally abstracted away. *)
Theory concretizeAnalysisBaseModel
Ancestors singleWriterScan concretizeAnalysisAffine concretizeAnalysisSupport
  concretizeAnalysisBoundary basePtrDefs basePtrProofs ptrDiscipline
  list pred_set combin finite_map venomInst

Definition bp_descriptor_def:
  bp_descriptor inst =
    case inst_output inst of
      NONE => NONE
    | SOME out =>
      case inst.inst_opcode of
        ALLOCA => SOME (out,{Allocation inst.inst_id},{})
      | ASSIGN => (case inst.inst_operands of
          [Var x] => SOME (out,{},{x}) | _ => NONE)
      | ADD => (case inst.inst_operands of
          [Var x; Lit n] => SOME (out,{},{x})
        | [Lit n; Var x] => SOME (out,{},{x})
        | [Var x; Var y] => SOME (out,{},{x;y}) | _ => NONE)
      | SUB => (case inst.inst_operands of
          [Var x; Lit n] => SOME (out,{},{x})
        | [Var x; Var y] => SOME (out,{},{x}) | _ => NONE)
      | PHI => SOME (out,{},out INSERT set (MAP SND (phi_pairs inst.inst_operands)))
      | _ => NONE
End

Definition bp_descriptor_step_def:
  bp_descriptor_step inst X =
    case bp_descriptor inst of NONE => X | SOME d => sw_update d X
End

Theorem bp_bases_empty:
  bp_bases r v = {} <=> bp_get_ptrs r v = []
Proof
  simp[bp_bases_def]
QED

(* Admissibility is exactly what rules out stale skipped destinations. *)
Theorem sw_empty_rhs_identity:
  MEM d ds /\ sw_admissible ds X /\ sw_rhs d X = {} ==>
  sw_update d X = X
Proof
  rpt strip_tac >>
  `X (sw_out d) = {}` by metis_tac[sw_admissible_def, SUBSET_EMPTY] >>
  simp[FUN_EQ_THM, sw_update_def] >> metis_tac[]
QED

Theorem bp_offset_base_set:
  set (MAP ptr_base (MAP (\p. offset_by p off) ps)) =
  set (MAP ptr_base ps)
Proof
  simp[MAP_MAP_o, o_DEF] >> AP_TERM_TAC >> irule MAP_CONG >> simp[] >>
  Cases >> rename1 `Ptr a ofs` >> Cases_on `ofs` >> Cases_on `off` >>
  simp[offset_by_def, ptr_base_def]
QED

Theorem bp_sub_offset_base_set:
  set (MAP ptr_base (MAP (\p. sub_offset_by p off) ps)) =
  set (MAP ptr_base ps)
Proof
  simp[MAP_MAP_o, o_DEF] >> AP_TERM_TAC >> irule MAP_CONG >> simp[] >>
  Cases >> rename1 `Ptr a ofs` >> Cases_on `ofs` >> Cases_on `off` >>
  simp[sub_offset_by_def, ptr_base_def] >>
  strip_tac >> IF_CASES_TAC >> simp[ptr_base_def]
QED

Theorem bp_literal_base_transfer:
  inst_output inst = SOME out /\
  ((inst.inst_opcode = ADD /\ inst.inst_operands = [Var x; Lit n]) \/
   (inst.inst_opcode = ADD /\ inst.inst_operands = [Lit n; Var x]) \/
   (inst.inst_opcode = SUB /\ inst.inst_operands = [Var x; Lit n])) /\
  bp_get_ptrs r x <> [] ==>
  bp_bases (SND (bp_handle_inst r inst)) out = bp_bases r x
Proof
  rpt strip_tac >>
  simp[bp_handle_inst_def, bp_bases_def, bp_get_ptrs_update,
       bp_offset_base_set, bp_sub_offset_base_set]
QED

Theorem bp_bases_other_var:
  inst_output inst <> SOME v ==>
  bp_bases (SND (bp_handle_inst r inst)) v = bp_bases r v
Proof
  strip_tac >>
  `bp_get_ptrs (SND (bp_handle_inst r inst)) v = bp_get_ptrs r v` by
    (irule bp_handle_inst_other_var_proof >> simp[] >>
     qexists_tac `FST (bp_handle_inst r inst)` >>
     qexists_tac `inst` >> simp[]) >>
  simp[bp_bases_def]
QED

(* Universal boundary probes, including empty sources and PHI feedback. *)
Theorem bp_assign_descriptor_refines:
  inst_output inst = SOME out /\ inst.inst_opcode = ASSIGN /\
  inst.inst_operands = [Var x] ==>
  bp_bases (SND (bp_handle_inst r inst)) = bp_descriptor_step inst (bp_bases r)
Proof
  rpt strip_tac >> irule EQ_EXT >> qx_gen_tac `v` >>
  simp[bp_descriptor_step_def, bp_descriptor_def,
    sw_update_def, sw_out_def, sw_rhs_def] >>
  Cases_on `v = out`
  >- (gvs[] >> metis_tac[bp_assign_base_transfer]) >>
  simp[] >> irule bp_bases_other_var >> simp[]
QED

Theorem bp_phi_descriptor_refines:
  inst_output inst = SOME out /\ inst.inst_opcode = PHI ==>
  bp_bases (SND (bp_handle_inst r inst)) = bp_descriptor_step inst (bp_bases r)
Proof
  rpt strip_tac >> irule EQ_EXT >> qx_gen_tac `v` >>
  simp[bp_descriptor_step_def, bp_descriptor_def,
    sw_update_def, sw_out_def, sw_rhs_def] >>
  Cases_on `v = out`
  >- (gvs[] >> drule_all bp_phi_base_transfer >>
      simp[LIST_TO_SET_MAP]) >>
  simp[] >> irule bp_bases_other_var >> simp[]
QED


Theorem bp_alloca_descriptor_refines:
  inst_output inst = SOME out /\ inst.inst_opcode = ALLOCA ==>
  bp_bases (SND (bp_handle_inst r inst)) = bp_descriptor_step inst (bp_bases r)
Proof
  rpt strip_tac >> irule EQ_EXT >> qx_gen_tac `v` >>
  simp[bp_descriptor_step_def, bp_descriptor_def,
    sw_update_def, sw_out_def, sw_rhs_def] >>
  Cases_on `v = out`
  >- gvs[bp_bases_def, bp_handle_inst_def, bp_get_ptrs_update,
         ptr_from_alloca_def, ptr_base_def] >>
  simp[] >> irule bp_bases_other_var >> simp[]
QED

Theorem bp_add_descriptor_refines:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  bp_supported (fn_pv P fn) r /\
  inst_output inst = SOME out /\ inst.inst_opcode = ADD /\
  inst.inst_operands = [Var x; Var y] /\
  MEM (out,{},{x;y}) ds /\ sw_admissible ds (bp_bases r) ==>
  bp_bases (SND (bp_handle_inst r inst)) = bp_descriptor_step inst (bp_bases r)
Proof
  rpt strip_tac >>
  irule EQ_EXT >> qx_gen_tac `v` >>
  simp[bp_descriptor_step_def, bp_descriptor_def,
    sw_update_def, sw_out_def, sw_rhs_def] >>
  Cases_on `v = out`
  >- (gvs[] >>
      Cases_on `bp_get_ptrs r x = []`
      >- (Cases_on `bp_get_ptrs r y = []`
          >- (`sw_rhs (out,{},{x;y}) (bp_bases r) = {}` by
                simp[sw_rhs_def, bp_bases_def] >>
              `bp_bases r out = {}` by
                metis_tac[sw_admissible_def, sw_out_def, SUBSET_EMPTY] >>
              simp[bp_handle_inst_def, bp_bases_def] >>
              metis_tac[bp_bases_empty]) >>
          `bp_bases (SND (bp_handle_inst r inst)) out = bp_bases r y` by
            (irule bp_affine_add_right_base_transfer >> metis_tac[]) >>
          simp[bp_bases_def]) >>
      `bp_get_ptrs r y = []` by
        (irule bp_supported_add_right_empty >>
         metis_tac[bp_supported_def]) >>
      drule_all bp_affine_add_base_transfer >> simp[bp_bases_def]) >>
  simp[] >> irule bp_bases_other_var >> simp[]
QED

Theorem bp_literal_descriptor_refines:
  inst_output inst = SOME out /\
  ((inst.inst_opcode = ADD /\ inst.inst_operands = [Var x; Lit n]) \/
   (inst.inst_opcode = ADD /\ inst.inst_operands = [Lit n; Var x]) \/
   (inst.inst_opcode = SUB /\ inst.inst_operands = [Var x; Lit n])) /\
  MEM (out,{},{x}) ds /\ sw_admissible ds (bp_bases r) ==>
  bp_bases (SND (bp_handle_inst r inst)) = bp_descriptor_step inst (bp_bases r)
Proof
  rpt strip_tac >> (irule EQ_EXT >> qx_gen_tac `v` >>
  simp[bp_descriptor_step_def, bp_descriptor_def,
    sw_update_def, sw_out_def, sw_rhs_def] >>
  Cases_on `v = out`
  >- (gvs[] >> Cases_on `bp_get_ptrs r x = []`
      >- (`sw_rhs (out,{},{x}) (bp_bases r) = {}` by
            simp[sw_rhs_def, bp_bases_def] >>
          `bp_bases r out = {}` by
            metis_tac[sw_admissible_def, sw_out_def, SUBSET_EMPTY] >>
          simp[bp_handle_inst_def, bp_bases_def] >>
          metis_tac[bp_bases_empty]) >>
      metis_tac[bp_literal_base_transfer]) >>
  simp[] >> irule bp_bases_other_var >> simp[])
QED

Theorem bp_sub_descriptor_refines:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  bp_supported (fn_pv P fn) r /\
  inst_output inst = SOME out /\ inst.inst_opcode = SUB /\
  inst.inst_operands = [Var x; Var y] /\
  MEM (out,{},{x}) ds /\ sw_admissible ds (bp_bases r) ==>
  bp_bases (SND (bp_handle_inst r inst)) = bp_descriptor_step inst (bp_bases r)
Proof
  rpt strip_tac >>
  `bp_get_ptrs r y = []` by
    (irule bp_supported_sub_right_empty >> metis_tac[]) >>
  irule EQ_EXT >> qx_gen_tac `v` >>
  simp[bp_descriptor_step_def, bp_descriptor_def,
    sw_update_def, sw_out_def, sw_rhs_def] >>
  Cases_on `v = out`
  >- (gvs[] >> Cases_on `bp_get_ptrs r x = []`
      >- (`sw_rhs (out,{},{x}) (bp_bases r) = {}` by
            simp[sw_rhs_def, bp_bases_def] >>
          `bp_bases r out = {}` by
            metis_tac[sw_admissible_def, sw_out_def, SUBSET_EMPTY] >>
          simp[bp_handle_inst_def, bp_bases_def] >>
          metis_tac[bp_bases_empty]) >>
      irule bp_affine_sub_base_transfer >> metis_tac[]) >>
  simp[] >> irule bp_bases_other_var >> simp[]
QED

Theorem bp_descriptor_none:
  bp_descriptor inst = NONE ==> bp_handle_inst r inst = (F,r)
Proof
  Cases_on `inst_output inst` >> simp[bp_descriptor_def, bp_handle_inst_def] >>
  Cases_on `inst.inst_opcode` >> simp[] >> (
  Cases_on `inst.inst_operands` >> simp[] >>
  rename1 `inst.inst_operands = h::t` >>
  Cases_on `t`
  >- (Cases_on `h` >> simp[]) >> simp[] >>
  rename1 `inst.inst_operands = h::h2::t2` >>
  Cases_on `t2` >> simp[] >>
  Cases_on `h` >> Cases_on `h2` >> simp[])
QED

Theorem bp_descriptor_refines:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  bp_supported (fn_pv P fn) r /\
  (!d. bp_descriptor inst = SOME d ==> MEM d ds) /\
  sw_admissible ds (bp_bases r) ==>
  bp_bases (SND (bp_handle_inst r inst)) = bp_descriptor_step inst (bp_bases r)
Proof
  rpt strip_tac >> Cases_on `bp_descriptor inst`
  >- (drule bp_descriptor_none >>
      simp[bp_descriptor_step_def]) >>
  Cases_on `inst_output inst`
  >- gvs[bp_descriptor_def] >>
  rename1 `inst_output inst = SOME out` >>
  Cases_on `inst.inst_opcode` >> gvs[bp_descriptor_def]
  >~ [`inst.inst_opcode = ALLOCA`]
  >- (irule bp_alloca_descriptor_refines >> simp[])
  >~ [`inst.inst_opcode = PHI`]
  >- (irule bp_phi_descriptor_refines >> simp[]) >>
  (Cases_on `inst.inst_operands` >> gvs[] >>
   rename1 `inst.inst_operands = h::t` >> Cases_on `t`
   >- (Cases_on `h` >> gvs[] >>
       irule bp_assign_descriptor_refines >> simp[]) >>
   rename1 `inst.inst_operands = h::h2::t2` >>
   Cases_on `t2` >> gvs[] >>
   Cases_on `h` >> Cases_on `h2` >> gvs[] >>
   metis_tac[bp_literal_descriptor_refines,
             bp_add_descriptor_refines, bp_sub_descriptor_refines])
QED

Definition bp_descriptor_stream_def:
  bp_descriptor_stream [] = [] /\
  bp_descriptor_stream (i::is) =
    case bp_descriptor i of
      NONE => bp_descriptor_stream is
    | SOME d => d::bp_descriptor_stream is
End

Theorem bp_descriptor_step_admissible:
  sw_consistent ds /\ sw_admissible ds X /\
  (!d. bp_descriptor inst = SOME d ==> MEM d ds) ==>
  sw_admissible ds (bp_descriptor_step inst X)
Proof
  rpt strip_tac >> Cases_on `bp_descriptor inst` >>
  simp[bp_descriptor_step_def] >> irule sw_update_admissible >> simp[]
QED

Theorem bp_process_block_descriptor_refines:
  !insts r.
  fn_ptr_ok P fn /\ EVERY (\i. MEM i (fn_insts fn)) insts /\
  bp_supported (fn_pv P fn) r /\ sw_consistent ds /\
  EVERY (\d. MEM d ds) (bp_descriptor_stream insts) /\
  sw_admissible ds (bp_bases r) ==>
  bp_bases (SND (bp_process_block r insts)) =
    sw_scan (bp_descriptor_stream insts) (bp_bases r)
Proof
  Induct >> simp[bp_process_block_def, bp_descriptor_stream_def, sw_scan_def] >>
  rpt strip_tac >>
  `!d. bp_descriptor h = SOME d ==> MEM d ds` by
    (Cases_on `bp_descriptor h` >> gvs[bp_descriptor_stream_def]) >>
  `EVERY (\d. MEM d ds) (bp_descriptor_stream insts)` by
    (Cases_on `bp_descriptor h` >> gvs[bp_descriptor_stream_def]) >>
  `bp_bases (SND (bp_handle_inst r h)) = bp_descriptor_step h (bp_bases r)` by
    (irule bp_descriptor_refines >> metis_tac[]) >>
  `sw_admissible ds (bp_bases (SND (bp_handle_inst r h)))` by
    (simp[] >> irule bp_descriptor_step_admissible >> simp[]) >>
  `bp_supported (fn_pv P fn) (SND (bp_handle_inst r h))` by
    (irule bp_supported_fn_inst >> simp[]) >>
  first_x_assum (qspec_then `SND (bp_handle_inst r h)` mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `bp_handle_inst r h` >> simp[] >>
  pairarg_tac >> simp[] >>
  Cases_on `bp_descriptor h` >>
  gvs[bp_descriptor_stream_def, sw_scan_def, bp_descriptor_step_def]
QED

Theorem bp_process_block_descriptor_admissible:
  fn_ptr_ok P fn /\ EVERY (\i. MEM i (fn_insts fn)) insts /\
  bp_supported (fn_pv P fn) r /\ sw_consistent ds /\
  EVERY (\d. MEM d ds) (bp_descriptor_stream insts) /\
  sw_admissible ds (bp_bases r) ==>
  sw_admissible ds (bp_bases (SND (bp_process_block r insts)))
Proof
  strip_tac >> drule_all bp_process_block_descriptor_refines >>
  disch_then SUBST1_TAC >> irule sw_scan_admissible >> simp[]
QED

Theorem bp_process_block_descriptor_bottom:
  fn_ptr_ok P fn /\ EVERY (\i. MEM i (fn_insts fn)) insts /\
  sw_consistent ds /\ EVERY (\d. MEM d ds) (bp_descriptor_stream insts) ==>
  bp_bases (SND (bp_process_block FEMPTY insts)) =
    sw_scan (bp_descriptor_stream insts) (\v. {})
Proof
  strip_tac >>
  `bp_bases FEMPTY = (\v. {})` by
    simp[FUN_EQ_THM, bp_bases_def, bp_get_ptrs_def] >>
  `bp_bases (SND (bp_process_block FEMPTY insts)) =
   sw_scan (bp_descriptor_stream insts) (bp_bases FEMPTY)` suffices_by simp[] >>
  irule bp_process_block_descriptor_refines >>
  conj_tac
  >- (qexistsl [`P`, `fn`] >> simp[bp_supported_def, bp_get_ptrs_def]) >>
  qexists `ds` >> simp[sw_bottom_admissible]
QED

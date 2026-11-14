(* Direct writes in the original owner's block cannot use the source site.
   This is a provenance exclusion, not a claim about calls or byte overlap. *)
Theory readonlyInvokeCopyFwdHistorySource
Ancestors
  readonlyInvokeCopyFwdHistorySelected readonlyInvokeCopyFwdHistory
  readonlyInvokeCopyFwdProtectionSelected occurrenceGeometry occurrenceOrigin
  o1LowerDloadOccurrence invokeCopyFwdCommonDefs readonlyInvokeCopyFwdPlan
  ptrDiscipline list finite_map

Theorem ricf_located_event_source_write_exclusion:
  ricf_located_event ctx0 fn log round b es prefix e current /\
  ssa_form fn /\ ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) /\
  ricf_src_alloca fn /\
  (ricf_event_copy e (EL b fn.fn_blocks)).inst_operands = [Var dst;Var sv;sz] /\
  dfg_get_def (dfg_build_function fn)
    (icf_assign_root (dfg_build_function fn) {} dst) = SOME di /\
  icf_is_alloca di /\
  MEM ai (fn_insts fn) /\ ai.inst_opcode = ALLOCA /\ ai.inst_outputs = [sv] /\
  fn_inst_ids_distinct fn /\ occurrence_syntax_origin fn a H /\
  occurrence_annotation_ok n a U B HP H stk PG G s /\
  occurrence_natural_geometry lo a U B stk s /\
  FLOOKUP B (a,ai.inst_id) = SOME (sb,z) /\ 0 < z /\
  e.rfe_index <= j /\ j < LENGTH (EL b fn.fn_blocks).bb_instructions /\
  mem_write_ops (EL j (EL b fn.fn_blocks).bb_instructions) = SOME ops ==>
  op_prov G ops.iao_ofst <> SOME (sb,z)
Proof
  strip_tac >> strip_tac >>
  `occurrence_env_ok B (a::MAP (\u. u.of_owner) U) H G` by
    gvs[occurrence_annotation_ok_def] >>
  `op_prov H ops.iao_ofst = SOME (a,ai.inst_id)` by
    (irule occurrence_geometry_op_positive_key >> metis_tac[]) >>
  drule_all ricf_located_event_validation >> strip_tac >>
  drule_all ricf_located_event_source_block >> strip_tac >>
  drule_all ricf_located_event_source_descriptor >> strip_tac >>
  drule ricf_block_edit_EL >> strip_tac >>
  drule_all ricf_event_copy_shape >> strip_tac >>
  `MEM (EL b fn.fn_blocks) fn.fn_blocks` by simp[EL_MEM] >>
  `e.rfe_index < LENGTH (EL b fn.fn_blocks).bb_instructions` by
    gvs[ricf_event_copy_def] >>
  `!inst. MEM inst (fn_insts fn) /\ MEM (Var sv) inst.inst_operands ==>
     ~is_pointer_preserving_op inst.inst_opcode` by
    (gvs[ricf_event_copy_def] >>
     `e.rfe_index < LENGTH (EL b fn.fn_blocks).bb_instructions` by
       (gvs[] >> decide_tac) >>
     metis_tac[ricf_source_copy_isolated]) >>
  `ops.iao_ofst = Var sv` by
    (irule ricf_isolated_occurrence_operand >> metis_tac[]) >>
  fs[ricf_src_alloca_def] >>
  qpat_x_assum `!bb k dst src size di. _`
    (qspecl_then [`EL b fn.fn_blocks`, `e.rfe_index`] mp_tac) >>
  disch_then (qspecl_then [`dst`, `Var sv`, `sz`, `di`] mp_tac) >>
  gvs[ricf_event_copy_def] >>
  `e.rfe_index < LENGTH (EL b fn.fn_blocks).bb_instructions` by
    (gvs[] >> decide_tac) >>
  simp[] >> metis_tac[]
QED

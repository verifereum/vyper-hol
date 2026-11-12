(* Static destination ranges for original instructions.  These facts do not
   assert that a dynamic owner visit has passed its activating copy. *)
Theory readonlyInvokeCopyFwdHistoryExclusion
Ancestors
  readonlyInvokeCopyFwdHistoryReadExceptions
  readonlyInvokeCopyFwdHistoryCopyUniqueness
  readonlyInvokeCopyFwdHistoryDestinationAccess
  occurrenceAccess occurrenceGeometry ptrDiscipline list finite_map

Theorem ricf_located_event_destination_ranges:
  ricf_located_event ctx0 original log round b es prefix e current /\
  ssa_form original /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts original)) /\
  fn_inst_wf original /\ fn_inst_ids_distinct original /\ ricf_src_alloca original /\
  (ricf_event_copy e (EL b original.fn_blocks)).inst_operands = [Var dst;src;sz] /\
  occurrence_syntax_origin original a H /\ MEM ai (fn_insts original) /\
  ai.inst_opcode = ALLOCA /\
  ai.inst_outputs = [icf_assign_root (dfg_build_function original) {} dst] /\
  cb < LENGTH original.fn_blocks /\
  i < LENGTH (EL cb original.fn_blocks).bb_instructions /\
  old = EL i (EL cb original.fn_blocks).bb_instructions /\
  occurrence_natural_geometry lo a U B stk s /\
  occurrence_env_ok B owners H G /\
  FLOOKUP B (a,ai.inst_id) = SOME (db,z) /\
  access_ok lo G original old s /\ ~in_revert_forward original s ==>
  (!off len k. MEM (off,len) (source_memory_read_ranges old s) /\ k < z ==>
     ~(off <= db+k /\ db+k < off+len)) /\
  (old.inst_id <> (ricf_event_copy e (EL b original.fn_blocks)).inst_id ==>
   !off len k. MEM (off,len) (source_memory_write_ranges old s) /\ k < z ==>
     ~(off <= db+k /\ db+k < off+len))
Proof
  strip_tac >> conj_tac
  >- (rpt strip_tac >>
      `!ops. mem_read_ops old = SOME ops ==>
         op_prov G ops.iao_ofst <> SOME (db,z)` by
        (rpt strip_tac >>
         `0 < z` by decide_tac >>
         `op_prov H ops.iao_ofst = SOME (a,ai.inst_id)` by
           (irule occurrence_geometry_op_positive_key >> metis_tac[]) >>
         drule_all ricf_located_event_original_read_exclusion >> simp[]) >>
      metis_tac[occurrence_access_read_exclusion]) >>
  rpt strip_tac >>
  `!ops. mem_write_ops old = SOME ops ==>
     op_prov G ops.iao_ofst <> SOME (db,z)` by
    (rpt strip_tac >>
     `0 < z` by decide_tac >>
     `op_prov H ops.iao_ofst = SOME (a,ai.inst_id)` by
       (irule occurrence_geometry_op_positive_key >> metis_tac[]) >>
     drule_all ricf_located_event_original_write_unique >> simp[]) >>
  metis_tac[occurrence_access_write_exclusion]
QED

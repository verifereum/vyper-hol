(* Destination byte exclusions concern original instructions, including the
   exact copies erased in earlier logged rounds.  No dynamic activation or
   availability of cross agreement is asserted here. *)
Theory readonlyInvokeCopyFwdHistoryDestinationAccess
Ancestors
  readonlyInvokeCopyFwdHistoryUses occurrenceAccess occurrenceGeometry
  o1LowerDloadOccurrence ptrDiscipline list finite_map

Theorem ricf_located_event_destination_access:
  ricf_located_event ctx0 original log round b es prefix e current /\
  ssa_form original /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts original)) /\
  fn_inst_wf original /\ fn_inst_ids_distinct original /\
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
  ((!off len k. MEM (off,len) (source_memory_read_ranges old s) /\ k < z ==>
      ~(off <= db+k /\ db+k < off+len)) \/
   (old.inst_opcode = MCOPY /\
    ricf_prior_erasure ctx0 original log round cb i old)) /\
  ((!off len k. MEM (off,len) (source_memory_write_ranges old s) /\ k < z ==>
      ~(off <= db+k /\ db+k < off+len)) \/
   (old.inst_opcode = MCOPY /\
    (old.inst_id = (ricf_event_copy e (EL b original.fn_blocks)).inst_id \/
     ricf_prior_erasure ctx0 original log round cb i old)))
Proof
  strip_tac >>
  drule_all ricf_located_event_original_address_use >> strip_tac >>
  conj_tac
  >- (Cases_on `old.inst_opcode = MCOPY /\
         ricf_prior_erasure ctx0 original log round cb i old`
      >- simp[] >>
      disj1_tac >> rpt strip_tac >>
      `!ops. mem_read_ops old = SOME ops ==>
        op_prov G ops.iao_ofst <> SOME (db,z)` by
        (rpt strip_tac >>
         `0 < z` by decide_tac >>
         `op_prov H ops.iao_ofst = SOME (a,ai.inst_id)` by
           (irule occurrence_geometry_op_positive_key >> metis_tac[]) >>
         metis_tac[]) >>
      metis_tac[occurrence_access_read_exclusion]) >>
  Cases_on `old.inst_opcode = MCOPY /\
    (old.inst_id = (ricf_event_copy e (EL b original.fn_blocks)).inst_id \/
     ricf_prior_erasure ctx0 original log round cb i old)`
  >- simp[] >>
  disj1_tac >> rpt strip_tac >>
  `!ops. mem_write_ops old = SOME ops ==>
    op_prov G ops.iao_ofst <> SOME (db,z)` by
    (rpt strip_tac >>
     `0 < z` by decide_tac >>
     `op_prov H ops.iao_ofst = SOME (a,ai.inst_id)` by
       (irule occurrence_geometry_op_positive_key >> metis_tac[]) >>
     metis_tac[]) >>
  metis_tac[occurrence_access_write_exclusion]
QED

(* Consumer form: exception discharge remains a separate obligation.  The
   read clause does not exclude the activating copy's destination write. *)
Theorem ricf_located_event_destination_ordinary_ranges:
  ricf_located_event ctx0 original log round b es prefix e current /\
  ssa_form original /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts original)) /\
  fn_inst_wf original /\ fn_inst_ids_distinct original /\
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
  ((~(old.inst_opcode = MCOPY /\
      ricf_prior_erasure ctx0 original log round cb i old) ==>
    !off len k. MEM (off,len) (source_memory_read_ranges old s) /\ k < z ==>
      ~(off <= db+k /\ db+k < off+len)) /\
   (~(old.inst_opcode = MCOPY /\
      (old.inst_id = (ricf_event_copy e (EL b original.fn_blocks)).inst_id \/
       ricf_prior_erasure ctx0 original log round cb i old)) ==>
    !off len k. MEM (off,len) (source_memory_write_ranges old s) /\ k < z ==>
      ~(off <= db+k /\ db+k < off+len)))
Proof
  strip_tac >> drule_all ricf_located_event_destination_access >>
  metis_tac[]
QED

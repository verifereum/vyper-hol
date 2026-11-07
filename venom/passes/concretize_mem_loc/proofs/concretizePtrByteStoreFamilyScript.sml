(*
 * Paired-prefix extension for the N8 opcode family (MSTORE8; ISTORE).
 *)
Theory concretizePtrByteStoreFamily
Ancestors
  concretizePtrStorageReadProducer ptrDiscipline concretizePtrRequestHistory
  concretizePtrTaintContent concretizePtrOpaqueRetpc concretizePtrSharedFields
  venomExecSemantics venomState finite_map concretizePtrStoreSteps
  venomMemProps regularCallEmitSim pointerConfinedDefs memLocDefs

Theorem ptr_byte_store_mstore8_operands_untainted:
  taint_ok fn tn inst s /\ inst.inst_opcode = MSTORE8 ==>
  !op. MEM op inst.inst_operands ==> op_taint tn op = {}
Proof
  strip_tac >> gvs[taint_ok_def] >> metis_tac[]
QED

Theorem ptr_byte_store_history_istore:
  ptr_history_content tn s t /\ word_agree_except m u v ==>
  ptr_history_content (tn with t_imm := key_update tn.t_imm k m)
    (istore k u s) (istore k v t)
Proof
  simp[ptr_history_content_def, ptr_taint_content_def,
    ptr_taint_control_def, ptr_core_shared_def, ptr_shared_fields_def,
    istore_def, mstore_def, contract_storage_def, contract_transient_def] >>
  rpt strip_tac >> gvs[FLOOKUP_UPDATE, key_update_def] >>
  Cases_on `k = k'` >> gvs[]
QED

Theorem ptr_byte_store_istore_operands_no_provenance:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = ISTORE /\
  (!x. x IN FDOM TG ==> x IN fn_pv P fn) /\
  MEM op inst.inst_operands ==> op_prov TG op = NONE
Proof
  strip_tac >>
  `!v. MEM (Var v) inst.inst_operands ==> v NOTIN fn_pv P fn` by
    (gvs[fn_ptr_ok_def] >> metis_tac[]) >>
  Cases_on `op` >> gvs[op_prov_def] >> metis_tac[flookup_thm]
QED

Theorem ptr_byte_store_mstore8_history:
  ptr_history_content tn s t ==>
  ptr_history_content tn (mstore8 off u s) (mstore8 offt v t)
Proof
  simp[ptr_history_content_def, ptr_taint_content_def,
    ptr_taint_control_def, ptr_core_shared_def, ptr_shared_fields_def,
    mstore8_def, contract_storage_def, contract_transient_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem ptr_byte_store_mstore8_written_byte:
  (w2w u : word8) = w2w v ==>
  read_byte off (mstore8 off u s).vs_memory =
  read_byte offt (mstore8 offt v t).vs_memory
Proof
  simp[mstore8_eq_write_mem, read_byte_write_memory_with_expansion]
QED

Theorem ptr_byte_store_istore_written_bytes:
  k < 32 /\ EL k (word_to_bytes u T) = EL k (word_to_bytes v T) ==>
  read_byte (off + k) (istore off u s).vs_memory =
  read_byte (offt + k) (istore offt v t).vs_memory
Proof
  strip_tac >> rewrite_tac[istore_memory] >>
  irule ptr_mstore_written_bytes >> simp[]
QED

Theorem ptr_byte_store_mstore8_value_no_provenance:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = MSTORE8 /\ inst.inst_operands = [a;v] /\
  (!x. x IN FDOM TG ==> x IN fn_pv P fn) ==>
  op_prov TG v = NONE
Proof
  strip_tac >>
  `ptr_use_ok P (fn_pv P fn) inst` by
    (gvs[fn_ptr_ok_def] >> metis_tac[]) >>
  `!x. v = Var x ==> x NOTIN fn_pv P fn` by
    (rpt strip_tac >>
     gvs[ptr_use_ok_def, is_pointer_preserving_op_def,
       mem_write_ops_def, mem_read_ops_def] >>
     first_x_assum (qspec_then `x` mp_tac) >> simp[] >>
     strip_tac >> gvs[] >> strip_tac >> gvs[]) >>
  Cases_on `v` >> gvs[op_prov_def] >> metis_tac[flookup_thm]
QED

Theorem ptr_paired_byte_store_prefix_normalize:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ max_live_eom C' = SOME eom /\
  LIST_REL (ptr_paired_code R lp positions) C.ctx_functions C'.ctx_functions /\
  EVERY (\f. fn_inst_wf f /\ retpc_shape_ok f /\ opaque_use_ok f /\
    first_block_no_phi f /\ EVERY bb_well_formed f.fn_blocks /\
    ALL_DISTINCT (fn_labels f) /\
    (!i. MEM i (fn_insts f) /\ i.inst_opcode = ALLOCA ==>
      IS_SOME (FLOOKUP (lp f) (Allocation i.inst_id)))) C.ctx_functions /\
  EVERY (\g. ALL_DISTINCT (fn_labels g)) C'.ctx_functions /\
  (!f g. ptr_paired_code R lp positions f g ==> g.fn_name = f.fn_name) /\
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  a.po_inst.inst_opcode <> NOP /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  ptr_chrono_step C' at zt /\ MEM a.po_inst.inst_opcode [MSTORE8; ISTORE] ==>
  ?delta z tokens' registry' births' PT' TG' saved' entries' snapshots calls' ws'.
    delta <> [] /\ LENGTH snapshots = LENGTH delta /\
    ptr_paired_prefix R lp positions lo vs C C'
      (h ++ delta) z (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
      tokens' registry' births' PT' TG' saved' entries'
      (H ++ snapshots) calls' ws' /\
    z.po_inst.inst_opcode <> NOP /\
    zt.po_inst = concretize_inst_with_positions (lp z.po_fn) z.po_inst
Proof
  cheat
QED


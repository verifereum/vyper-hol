(*
 * Paired-prefix extension for the N12 opcode family (SSTORE; TSTORE).
 *)
Theory concretizePtrStorageWriteFamily
Ancestors
  concretizePtrStorageReadProducer concretizePtrOpaqueRetpc
  concretizePtrRequestCompletionProbe concretizePtrTaintStorageProbe
  concretizePtrRequestHistory concretizePtrTaintContent concretizePtrValueTransport
  ptrDiscipline pointerConfinedDefs memLocDefs venomInst venomState
  venomExecSemantics codegenRel list finite_map pred_set

Theorem ptr_storage_write_operand_discipline[local]:
  fn_ptr_ok P fn /\ opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  taint_ok fn tn inst s /\ inst.inst_operands = [key; data] /\
  (!v tag. FLOOKUP TG v = SOME tag ==> v IN fn_pv P fn) /\
  MEM inst.inst_opcode [SSTORE; TSTORE] ==>
  EVERY (\op. ptr_nonopaque_operand fn op /\ op_prov TG op = NONE)
    inst.inst_operands /\ op_taint tn key = {}
Proof
  strip_tac >>
  `EVERY (ptr_nonopaque_operand fn) inst.inst_operands` by
    (irule ptr_nonopaque_instruction_operands >> simp[] >> fs[MEM]) >>
  `!v. MEM (Var v) inst.inst_operands ==> v NOTIN fn_pv P fn` by
    (qpat_x_assum `fn_ptr_ok P fn` mp_tac >>
     simp[fn_ptr_ok_def] >> strip_tac >>
     qpat_x_assum `!inst. MEM inst (fn_insts fn) ==> _`
       (qspec_then `inst` mp_tac) >> fs[MEM] >>
     simp[ptr_use_ok_def, is_pointer_preserving_op_def,
          mem_write_ops_def, mem_read_ops_def] >> metis_tac[]) >>
  conj_tac
  >- (simp[EVERY_MEM] >> gen_tac >> strip_tac >>
      `ptr_nonopaque_operand fn op` by fs[EVERY_MEM] >> simp[] >>
      Cases_on `op` >> gvs[op_prov_def] >>
      Cases_on `FLOOKUP TG s'` >> simp[] >> metis_tac[]) >>
  qpat_x_assum `taint_ok _ _ _ _` mp_tac >> fs[MEM] >>
  simp[taint_ok_def] >> metis_tac[]
QED

Theorem ptr_history_tstore[local]:
  ptr_history_content tn s t /\ word_agree_except m u v ==>
  ptr_history_content (tn with t_trans := key_update tn.t_trans k m)
    (tstore k u s) (tstore k v t)
Proof
  simp[ptr_history_content_def] >> strip_tac >>
  drule_all ptr_taint_content_tstore >>
  disch_then (qspec_then `k` mp_tac) >> simp[tstore_def]
QED

Theorem ptr_storage_write_history_execution[local]:
  ptr_history_content tn s t /\ MEM inst.inst_opcode [SSTORE; TSTORE] /\
  inst.inst_operands = [a; d] /\ inst.inst_outputs = [] /\
  eval_operand a s = SOME k /\ eval_operand a t = SOME k /\
  eval_operand d s = SOME u /\ eval_operand d t = SOME v /\
  word_agree_except (op_taint tn d) u v /\
  step_inst fuel Ct inst t = OK t' ==>
  ?s'. step_inst 0 C inst s = OK s' /\
    ptr_history_content (step_taint inst s s' tn) s' t' /\
    ((s' = sstore k u s /\ t' = sstore k v t) \/
     (s' = tstore k u s /\ t' = tstore k v t))
Proof
  strip_tac >>
  `s.vs_call_ctx = t.vs_call_ctx` by
    metis_tac[ptr_history_content_call_ctx] >>
  fs[MEM] >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  simp[step_inst_non_invoke] >> PURE_REWRITE_TAC[step_inst_base_def] >>
  ASM_REWRITE_TAC[] >> simp[Once opcode_case_def] >>
  simp[eval_operands_def, exec_write2_def] >> strip_tac >>
  gvs[AllCaseEqs()] >>
  simp[step_inst_non_invoke, step_inst_base_def, Once opcode_case_def,
       exec_write2_def, eval_operands_def] >>
  fs[step_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
     mem_taint_def, set_var_taint_def, new_site_bytes_def,
     step_writes_def, written_taint_def, range_bytes_def,
     source_memory_write_ranges_def, FLOOKUP_DEF]
  >- (irule ptr_history_content_masks >>
      qexists_tac `tn with t_stor := key_update tn.t_stor k (op_taint tn d)` >>
      simp[] >> metis_tac[ptr_history_sstore]) >>
  irule ptr_history_content_masks >>
  qexists_tac `tn with t_trans := key_update tn.t_trans k (op_taint tn d)` >>
  simp[] >> metis_tac[ptr_history_tstore]
QED

Theorem ptr_mixed_storage_write_execution[local]:
  ptr_mixed_vars births positions TG tn f g s t /\ ptr_history_content tn s t /\
  EVERY (\op. ptr_nonopaque_operand f op /\ op_prov TG op = NONE)
    inst.inst_operands /\ op_taint tn key = {} /\
  inst.inst_operands = [key; data] /\ inst.inst_outputs = [] /\
  MEM inst.inst_opcode [SSTORE; TSTORE] /\
  step_inst fuel Ct inst t = OK t' ==>
  ?s'. step_inst 0 C inst s = OK s' /\
    ptr_history_content (step_taint inst s s' tn) s' t' /\
    ptr_mixed_vars births positions (step_prov PT TG inst s')
      (step_taint inst s s' tn) f g s' t'
Proof
  strip_tac >>
  `s.vs_labels = t.vs_labels` by metis_tac[ptr_history_content_labels] >>
  `ptr_lookup_transport births positions NONE {} (eval_operand key s)
     (eval_operand key t)` by
    (fs[EVERY_DEF] >> metis_tac[ptr_mixed_vars_eval]) >>
  `ptr_lookup_transport births positions NONE (op_taint tn data)
     (eval_operand data s) (eval_operand data t)` by
    (fs[EVERY_DEF] >> metis_tac[ptr_mixed_vars_eval]) >>
  Cases_on `eval_operand key t`
  >- (qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
      fs[MEM] >> simp[step_inst_non_invoke, step_inst_base_def,
        Once opcode_case_def, exec_write2_def, eval_operands_def]) >>
  Cases_on `eval_operand data t`
  >- (qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
      fs[MEM] >> simp[step_inst_non_invoke, step_inst_base_def,
        Once opcode_case_def, exec_write2_def, eval_operands_def]) >>
  Cases_on `eval_operand key s` >>
  gvs[ptr_lookup_transport_def, ptr_value_transport_scalar_empty] >>
  Cases_on `eval_operand data s` >>
  gvs[ptr_lookup_transport_def, ptr_value_transport_def] >>
  `MEM inst.inst_opcode [SSTORE; TSTORE]` by simp[] >>
  drule_all ptr_storage_write_history_execution >>
  disch_then (qspec_then `C` strip_assume_tac) >>
  qexists_tac `s'` >> simp[] >>
  irule ptr_mixed_vars_fields >>
  qexistsl_tac [`s`, `t`, `tn`] >>
  fs[MEM, step_prov_def, out_prov_def, set_prov_def,
     step_taint_def, set_var_taint_def, sstore_def, tstore_def,
     DRESTRICT_UNIV]
QED

Theorem ptr_paired_storage_write_prefix_normalize:
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
  ptr_chrono_step C' at zt /\ MEM a.po_inst.inst_opcode [SSTORE; TSTORE] ==>
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


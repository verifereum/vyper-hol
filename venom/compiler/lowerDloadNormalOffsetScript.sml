Theory lowerDloadNormalOffset
Ancestors
  lowerDloadNormalExisting lowerDloadResidualNonmemory lowerDloadNormalData
  lowerDloadReadEffects lowerDloadPairedBoundary lowerDloadOwnership
  lowerDloadOpaqueExecution lowerDloadOperand lowerDloadScalarClosure
  lowerDloadVariableTransport lowerDloadFrameCertificate lowerDloadCoverageInvariant
  lowerDloadParamProducer memLocDefs codegenRel
  venomExecSemantics venomState venomWf venomInst ptrDiscipline
  finite_map pred_set list

Theorem ld_normal_offset_backward:
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  o1_ctx_shape CS /\ (!g. MEM g CS.ctx_functions ==> fn_ptr_ok P g) /\
  i.inst_opcode = OFFSET /\
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk f /\
  step_inst fuel CT i t = OK t' ==>
  ?s'. step_inst fuel CS i s = OK s' /\
    ld_normal_data CS fn V U lo E L H AP BP
      (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t'
      astk live keys d A suspended gstk f
Proof
  strip_tac >>
  `inst_wf i` by metis_tac[ld_annotated_inst_wf] >>
  `?v lbl out. i.inst_operands = [Lit v; Label lbl] /\ i.inst_outputs = [out]` by
    (qpat_x_assum `inst_wf i` mp_tac >>
     simp[inst_wf_def, LENGTH_EQ_NUM_compute] >> metis_tac[]) >>
  `ld_owned_vars U E AG BH tn un s t /\
   (!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
   (!v. ld_owned_selection E (FLOOKUP AG v) (FLOOKUP BH v))` by
    (drule ld_normal_data_frame >> simp[ld_frame_data_def]) >>
  `!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t` by
    (fs[ld_owned_vars_def] >> rpt strip_tac >> gvs[eval_operand_def]) >>
  `exec_pure2 word_add i t = OK t'` by
    (qpat_x_assum `step_inst fuel CT i t = OK t'` mp_tac >>
     simp[step_inst_non_invoke, step_inst_base_def]) >>
  drule_all ld_exec_pure2_backward >> strip_tac >> gvs[] >>
  qexists_tac `update_var out w s` >>
  conj_tac >- simp[step_inst_non_invoke, step_inst_base_def] >>
  suspend "completion"
QED

Resume ld_normal_offset_backward[completion]:
  `ld_owned_value E NONE NONE {} {} w w` by
    simp[ld_owned_value_def, ld_mask_word_def] >>
  `ld_owned_vars U E (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
    (step_taint i s (update_var out w s) tn)
    (step_taint i t (update_var out w t) un)
    (update_var out w s) (update_var out w t)` by
    (simp[ld_step_prov_def, ld_out_prov_def] >>
     irule ld_owned_vars_update_supported >>
     simp[step_taint_def, out_taint_def, op_taint_def, eval_operand_def] >>
     qexistsl_tac [`{}`, `{}`, `tn`, `un`] >> simp[]) >>
  irule ld_normal_step_vars_complete >> simp[ld_update_var_restore] >>
  conj_tac >- metis_tac[ld_lookup_defined_update] >>
  suspend "fields"
QED

Resume ld_normal_offset_backward[fields]:
  conj_tac
  >- (simp[ld_step_prov_def, ld_out_prov_def] >>
      irule ld_owned_set_selection >> simp[ld_owned_selection_def]) >>
  `source_memory_write_ranges i s = [] /\ source_memory_write_ranges i t = []` by
    simp[source_memory_write_ranges_def] >>
  simp[step_taint_def, mem_taint_def, new_site_bytes_def,
       written_taint_def, step_writes_def, store_taint_def, imm_taint_def,
       adopt_reset_def, update_var_def, range_bytes_def, EXTENSION, FLOOKUP_DEF] >>
  metis_tac[]
QED

Finalise ld_normal_offset_backward

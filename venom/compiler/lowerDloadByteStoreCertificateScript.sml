Theory lowerDloadByteStoreCertificate
Ancestors
  lowerDloadByteStoreProduction lowerDloadStoreCertificate lowerDloadEffectTransport
  lowerDloadReachableDiscipline lowerDloadProvenanceSupport
  lowerDloadAccessClassification lowerDloadStoreProducer
  lowerDloadCertificateProbe lowerDloadMaskBounds lowerDloadFrameCertificate
  lowerDloadTargetGeometry lowerDloadOwnership lowerDloadAllocation
  ptrDiscipline venomExecSemantics venomState finite_map pred_set words list
  lowerDloadPairedBoundary lowerDloadOperand memLocDefs pointerConfinedDefs venomInst o1PassContract
  contextCodegenRel codegenRel

Theorem ld_mstore8_certificate_backward:
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  ptr_discipline lo CS vs0 /\
  (!fn. MEM fn CS.ctx_functions ==> fn_ptr_ok P fn) /\
  i.inst_opcode = MSTORE8 /\ i.inst_operands = [dst;value] /\
  i.inst_outputs = [] /\ ~in_revert_forward fn s /\
  ld_owned_vars U E AG BH tn un s t /\
  (!v. MEM (Var v) [dst;value] ==> v IN U) /\
  (!v owner bs sz. FLOOKUP AG v = SOME(owner,(bs,sz)) ==> owner IN live) /\
  (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
    lo <= bs /\ lo <= bt /\ bs+sz < dimword(:256) /\ bt+sz < dimword(:256)) /\
  (!owner other bs bt sz cs ct cz.
    owner IN live /\ other IN live /\ owner <> other /\
    ld_site_entry E owner bs bt sz /\ ld_site_entry E other cs ct cz ==>
    (bs+sz <= cs \/ cs+cz <= bs) /\ (bt+sz <= ct \/ ct+cz <= bt)) /\
  ld_byte_rel (\a b. (a=b /\ a<lo) \/ ld_site_bytes E live a b)
    tn.t_mem un.t_mem (\a. read_memory a 1 s) (\b. read_memory b 1 t) /\
  ld_shared_state tn un s t /\
  ld_frame_embedding E L H s t /\ ld_alloc_account keys d A s t /\
  (!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  LIST_REL (ld_owned_selection E) AP BP /\
  (!v. ld_owned_selection E (FLOOKUP AG v) (FLOOKUP BH v)) /\
  d = 32 * SUM (MAP CARD suspended) /\
  ld_frame_bound t.vs_alloca_next H BP BH /\ ld_stack_bound t.vs_alloca_next gstk /\
  lo <= f /\ allocas_from f t /\ f <= t.vs_alloca_next /\
  (!owner bs sz. ld_live astk L AP AG (owner,(bs,sz)) ==> owner IN live /\ lo <= bs) /\
  (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
    lo <= bs /\ lo <= bt /\ bs+sz <= s.vs_alloca_next /\ bt+sz <= t.vs_alloca_next) /\
  (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
    bt+sz <= f \/ ?j. j NOTIN keys /\ FLOOKUP t.vs_allocas j = SOME(bt,sz)) /\
  (!v. op_taint tn (Var v) SUBSET count 32) /\
  (!v. op_taint un (Var v) SUBSET count 32) /\
  un.t_stor SUBSET tn.t_stor /\ un.t_trans SUBSET tn.t_trans /\ un.t_imm SUBSET tn.t_imm /\
  step_inst fuel CT i t = OK t' ==>
  ?s'. step_inst fuel CS i s = OK s' /\
    ld_byte_rel (\a b. (a=b /\ a<lo) \/ ld_site_bytes E live a b)
      (step_taint i s s' tn).t_mem (step_taint i t t' un).t_mem
      (\a. read_memory a 1 s') (\b. read_memory b 1 t') /\
    ld_shared_state (step_taint i s s' tn) (step_taint i t t' un) s' t' /\
    ld_owned_vars U E (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t' /\
    ld_frame_embedding E L H s' t' /\ ld_alloc_account keys d A s' t' /\
    (!v. v IN V ==> (lookup_var v s' = NONE <=> lookup_var v t' = NONE)) /\
    LIST_REL (ld_owned_selection E) AP BP /\
    (!v. ld_owned_selection E (FLOOKUP (ld_step_prov AP AG L i) v)
      (FLOOKUP (ld_step_prov BP BH H i) v)) /\
    d = 32 * SUM (MAP CARD suspended) /\
    ld_frame_bound t'.vs_alloca_next H BP (ld_step_prov BP BH H i) /\
    ld_stack_bound t'.vs_alloca_next gstk /\
    lo <= f /\ allocas_from f t' /\ f <= t'.vs_alloca_next /\
    (!owner bs sz. ld_live astk L AP (ld_step_prov AP AG L i) (owner,(bs,sz)) ==>
      owner IN live /\ lo <= bs) /\
    (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
      lo <= bs /\ lo <= bt /\ bs+sz <= s'.vs_alloca_next /\ bt+sz <= t'.vs_alloca_next) /\
    (!owner other bs bt sz cs ct cz.
      owner IN live /\ other IN live /\ owner <> other /\
      ld_site_entry E owner bs bt sz /\ ld_site_entry E other cs ct cz ==>
      (bs+sz <= cs \/ cs+cz <= bs) /\ (bt+sz <= ct \/ ct+cz <= bt)) /\
    (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
      bt+sz <= f \/ ?j. j NOTIN keys /\ FLOOKUP t'.vs_allocas j = SOME(bt,sz)) /\
    (!v. op_taint (step_taint i s s' tn) (Var v) SUBSET count 32) /\
    (!v. op_taint (step_taint i t t' un) (Var v) SUBSET count 32) /\
    (step_taint i t t' un).t_stor SUBSET (step_taint i s s' tn).t_stor /\
    (step_taint i t t' un).t_trans SUBSET (step_taint i s s' tn).t_trans /\
    (step_taint i t t' un).t_imm SUBSET (step_taint i s s' tn).t_imm /\
    (s' with vs_memory := s.vs_memory) = s /\
    (t' with vs_memory := t.vs_memory) = t
Proof
  strip_tac >>
  `?y w. eval_operand dst t = SOME y /\ eval_operand value t = SOME w /\
    t' = mstore8 (w2n y) w t` by
    (qpat_x_assum `step_inst fuel CT i t = OK t'` mp_tac >>
     simp[step_inst_non_invoke] >> pure_once_rewrite_tac[step_inst_base_def] >>
     qpat_assum `i.inst_opcode = MSTORE8` (fn th => pure_rewrite_tac[th]) >>
     simp[exec_write2_def, AllCaseEqs()] >> metis_tac[]) >>
  `?x v. eval_operand dst s = SOME x /\ eval_operand value s = SOME v` by
    suspend "source_operands" >>
  `MEM fn CS.ctx_functions` by (drule_all ld_annotated_fn_member >> simp[]) >>
  `MEM i (fn_insts fn)` by
    (drule ld_annotated_active_inst >>
     simp[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[EL_MEM]) >>
  `fn_ptr_ok P fn` by metis_tac[] >>
  `ptr_use_ok P (fn_pv P fn) i` by metis_tac[fn_ptr_ok_def] >>
  `ld_op_prov AG value = NONE` by suspend "value_provenance" >>
  drule_all ld_annotated_access_ok >> strip_tac >>
  drule_all ld_annotated_taint_ok >> strip_tac >>
  `op_taint tn dst = {}` by
    (irule ld_taint_operand_clean >> goal_assum (drule_at Any) >> simp[]) >>
  `op_taint tn value = {}` by
    (irule ld_taint_operand_clean >> goal_assum (drule_at Any) >> simp[]) >>
  `v = w` by
    (drule ld_owned_operand_clean >> disch_then (qspec_then `value` mp_tac) >> simp[]) >>
  `MEM (w2n x,1) (source_memory_write_ranges i s)` by
    simp[source_memory_write_ranges_def, fixed_source_write_range_def] >>
  `((w2n x = w2n y /\ w2n x+1 <= lo) \/
    (?owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz /\
      bs <= w2n x /\ w2n x+1 <= bs+sz /\ w2n y = bt+(w2n x-bs)))` by
    suspend "write_classification" >>
  `!a b. ((a=b /\ a<lo) \/ ld_site_bytes E live a b) ==>
     (a = w2n x <=> b = w2n y)` by
    (`(!a b. ((a=b /\ a<lo) \/ ld_site_bytes E live a b) ==>
        ((w2n x<=a /\ a<w2n x+1) <=> (w2n y<=b /\ b<w2n y+1))) /\
      (!a b. ((a=b /\ a<lo) \/ ld_site_bytes E live a b) /\
        w2n x<=a /\ a<w2n x+1 ==> a-w2n x=b-w2n y)` by
       (irule ld_fixed_live_write_footprint >> metis_tac[]) >>
     rpt gen_tac >> strip_tac >>
     qpat_x_assum `!a b. _ ==> ((_ /\ _) <=> (_ /\ _))`
       (qspecl_then [`a`,`b`] mp_tac) >> simp[] >> decide_tac) >>
  `?s'. step_inst fuel CS i s = OK s' /\
    ld_byte_rel (\a b. (a=b /\ a<lo) \/ ld_site_bytes E live a b)
      (step_taint i s s' tn).t_mem (step_taint i t t' un).t_mem
      (\a. read_memory a 1 s') (\b. read_memory b 1 t') /\
    ld_shared_state (step_taint i s s' tn) (step_taint i t t' un) s' t' /\
    (s' with vs_memory := s.vs_memory) = s /\
    (t' with vs_memory := t.vs_memory) = t` by
    (gvs[] >> irule ld_mstore8_annotated_memory_backward >>
     simp[] >> metis_tac[]) >>
  suspend "frame_transport"
QED

Resume ld_mstore8_certificate_backward[source_operands]:
  drule ld_owned_operand_defined >> disch_then (qspec_then `dst` mp_tac) >>
  simp[] >> strip_tac >>
  drule ld_owned_operand_defined >> disch_then (qspec_then `value` mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `eval_operand dst s` >> Cases_on `eval_operand value s` >>
  gvs[] >> metis_tac[]
QED

Resume ld_mstore8_certificate_backward[value_provenance]:
  `!z. value = Var z ==> z NOTIN fn_pv P fn` by
    (gen_tac >> disch_tac >>
     qpat_x_assum `ptr_use_ok P (fn_pv P fn) i` mp_tac >>
     simp[ptr_use_ok_def] >>
     disch_then (qspec_then `z` mp_tac) >>
     simp[is_pointer_preserving_op_def, mem_write_ops_def, mem_read_ops_def] >>
     Cases_on `dst = Var z` >> simp[]) >>
  metis_tac[ld_annotated_scalar_prov]
QED

Resume ld_mstore8_certificate_backward[write_classification]:
  drule ld_access_write_classification >>
  disch_then (qspecl_then [`w2n x`,`1`] mp_tac) >> simp[] >> strip_tac
  >- (disj1_tac >> simp[] >>
      `ld_op_prov AG dst = NONE` by
        (qpat_x_assum `!ops. _` mp_tac >>
         simp[mem_write_ops_def, GSYM ld_erase_op_prov]) >>
      drule ld_owned_operand_clean >> disch_then (qspec_then `dst` mp_tac) >> simp[]) >>
  disj2_tac >> gvs[mem_write_ops_def] >>
  `owner IN live` by metis_tac[] >>
  `v' IN U` by simp[] >>
  `?bt. ld_site_entry E owner bs bt sz` by
    (drule ld_owned_operand_value >>
     disch_then (qspecl_then [`y`,`x`,`Var v'`] mp_tac) >>
     simp[ld_op_prov_def, ld_owned_value_def] >> metis_tac[]) >>
  `bs+sz < dimword(:256)` by metis_tac[] >>
  `!bt. ld_site_entry E owner bs bt sz ==> bt+sz < dimword(:256)` by metis_tac[] >>
  `0 < (1:num)` by decide_tac >>
  drule_all ld_owned_address_transport >> metis_tac[]
QED

Resume ld_mstore8_certificate_backward[frame_transport]:
  markerLib.RESUME_TAC >> rpt strip_tac >> qexists_tac `s'` >> asm_rewrite_tac[] >>
  dxrule ld_memory_restore_normalize >> disch_then SUBST_ALL_TAC >>
  dxrule ld_memory_restore_normalize >> disch_then SUBST_ALL_TAC >>
  simp[ld_empty_outputs_prov_tvar, ld_frame_embedding_def, ld_alloc_account_def,
       ld_owned_vars_def, lookup_var_def, allocas_from_def] >>
  fs[ld_owned_vars_def, ld_frame_embedding_def, ld_alloc_account_def,
     allocas_from_def] >>
  simp[op_taint_def, ld_empty_outputs_prov_tvar,
       step_taint_def, store_taint_def, imm_taint_def, adopt_reset_def,
       set_var_taint_def, DRESTRICT_UNIV] >>
  fs[mstore8_def, lookup_var_def, op_taint_def] >> gvs[] >> asm_rewrite_tac[]
QED

Finalise ld_mstore8_certificate_backward

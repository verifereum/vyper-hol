Theory lowerDloadCopyCertificate
Ancestors
  lowerDloadVariableTransport lowerDloadAssignProducer lowerDloadPhiProducer
  lowerDloadOwnership ptrDiscipline venomState finite_map pred_set
  lowerDloadByteStoreCertificate lowerDloadCopyProduction lowerDloadEffectTransport
  lowerDloadReachableDiscipline lowerDloadProvenanceSupport
  lowerDloadAccessClassification lowerDloadStoreProducer lowerDloadPairedBoundary
  lowerDloadCertificateProbe lowerDloadFrameCertificate lowerDloadTargetGeometry
  lowerDloadLifetime lowerDloadAllocation lowerDloadOperand memLocDefs pointerConfinedDefs venomInst
  o1PassContract contextCodegenRel codegenRel venomExecSemantics words list

(* The existing ASSIGN and parallel PHI certificates both conclude the first
   premise below. Their C1-C12 conclusions need not be duplicated to transport
   the separate frame floor and live allocation representation. lo <= f is
   unchanged; together with f <= next it supplies their lo <= next premise.
   This boundary establishes no annotated successor or block-label alignment. *)
Theorem ld_vars_floor_representation_transport:
  (t' with vs_vars := t.vs_vars) = t /\
  allocas_from f t /\ f <= t.vs_alloca_next /\
  (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
    bt+sz <= f \/ ?j. j NOTIN keys /\ FLOOKUP t.vs_allocas j = SOME(bt,sz)) ==>
  allocas_from f t' /\ f <= t'.vs_alloca_next /\
  (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
    bt+sz <= f \/ ?j. j NOTIN keys /\ FLOOKUP t'.vs_allocas j = SOME(bt,sz))
Proof
  strip_tac >> dxrule ld_vars_restore_normalize >>
  disch_then SUBST_ALL_TAC >> simp[allocas_from_def] >>
  qpat_x_assum `allocas_from f t` mp_tac >> simp[allocas_from_def] >>
  strip_tac >> asm_rewrite_tac[]
QED

Theorem ld_mcopy_certificate_backward:
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  ptr_discipline lo CS vs0 /\
  (!fn. MEM fn CS.ctx_functions ==> fn_ptr_ok P fn) /\
  i.inst_opcode = MCOPY /\ i.inst_operands = [dst;src;lenop] /\
  i.inst_outputs = [] /\ ~in_revert_forward fn s /\
  ld_owned_vars U E AG BH tn un s t /\
  (!v. MEM (Var v) [dst;src;lenop] ==> v IN U) /\
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
  `?q u n. eval_operand dst t = SOME q /\ eval_operand src t = SOME u /\
    eval_operand lenop t = SOME n /\ t' = mcopy (w2n q) (w2n u) (w2n n) t` by
    (qpat_x_assum `step_inst fuel CT i t = OK t'` mp_tac >>
     simp[step_inst_non_invoke] >> pure_once_rewrite_tac[step_inst_base_def] >>
     qpat_assum `i.inst_opcode = MCOPY` (fn th => pure_rewrite_tac[th]) >>
     simp[AllCaseEqs()] >> metis_tac[]) >>
  `?p r m. eval_operand dst s = SOME p /\ eval_operand src s = SOME r /\
    eval_operand lenop s = SOME m` by suspend "source_operands" >>
  `MEM fn CS.ctx_functions` by (drule_all ld_annotated_fn_member >> simp[]) >>
  `MEM i (fn_insts fn)` by
    (drule ld_annotated_active_inst >>
     simp[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[EL_MEM]) >>
  `fn_ptr_ok P fn` by metis_tac[] >>
  `ptr_use_ok P (fn_pv P fn) i` by metis_tac[fn_ptr_ok_def] >>
  `ld_op_prov AG lenop = NONE` by suspend "lenop_provenance" >>
  drule_all ld_annotated_access_ok >> strip_tac >>
  drule_all ld_annotated_taint_ok >> strip_tac >>
  `!op. MEM op [dst;src;lenop] ==> op_taint tn op = {}` by
    (rpt strip_tac >> fs[] >> irule ld_taint_operand_clean >>
     goal_assum (drule_at Any) >> simp[]) >>
  `m = n` by
    (drule ld_owned_operand_clean >> disch_then (qspec_then `lenop` mp_tac) >> simp[]) >>
  `(!a b. ((a=b /\ a<lo) \/ ld_site_bytes E live a b) ==>
      ((w2n p<=a /\ a<w2n p+w2n n) <=> (w2n q<=b /\ b<w2n q+w2n n))) /\
   (!a b. ((a=b /\ a<lo) \/ ld_site_bytes E live a b) /\
      w2n p<=a /\ a<w2n p+w2n n ==> a-w2n p=b-w2n q) /\
   (!j. j<w2n n ==> ((w2n r+j = w2n u+j /\ w2n r+j<lo) \/
     ld_site_bytes E live (w2n r+j) (w2n u+j)))` by suspend "geometry" >>
  `?s'. step_inst fuel CS i s = OK s' /\
    ld_byte_rel (\a b. (a=b /\ a<lo) \/ ld_site_bytes E live a b)
      (step_taint i s s' tn).t_mem (step_taint i t t' un).t_mem
      (\a. read_memory a 1 s') (\b. read_memory b 1 t') /\
    ld_shared_state (step_taint i s s' tn) (step_taint i t t' un) s' t' /\
    (s' with vs_memory := s.vs_memory) = s /\
    (t' with vs_memory := t.vs_memory) = t` by
    (gvs[] >> irule ld_mcopy_annotated_memory_backward >> simp[] >> metis_tac[]) >>
  suspend "frame_transport"
QED

Resume ld_mcopy_certificate_backward[source_operands]:
  drule ld_owned_operand_defined >> disch_then (qspec_then `dst` mp_tac) >>
  simp[] >> strip_tac >>
  drule ld_owned_operand_defined >> disch_then (qspec_then `src` mp_tac) >>
  simp[] >> strip_tac >>
  drule ld_owned_operand_defined >> disch_then (qspec_then `lenop` mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `eval_operand dst s` >> Cases_on `eval_operand src s` >>
  Cases_on `eval_operand lenop s` >> gvs[] >> metis_tac[]
QED

Resume ld_mcopy_certificate_backward[lenop_provenance]:
  `!z. lenop = Var z ==> z NOTIN fn_pv P fn` by
    (gen_tac >> disch_tac >>
     qpat_x_assum `ptr_use_ok P (fn_pv P fn) i` mp_tac >>
     simp[ptr_use_ok_def] >> disch_then (qspec_then `z` mp_tac) >>
     simp[is_pointer_preserving_op_def, mem_write_ops_def, mem_read_ops_def] >>
     Cases_on `dst = Var z` >> Cases_on `src = Var z` >>
     simp[LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM]) >>
  metis_tac[ld_annotated_scalar_prov]
QED

Resume ld_mcopy_certificate_backward[geometry]:
  Cases_on `w2n n = 0` >- simp[] >>
  `MEM (w2n p,w2n n) (source_memory_write_ranges i s)` by
    simp[source_memory_write_ranges_def, sized_source_write_range_def] >>
  `MEM (w2n r,w2n n) (source_memory_read_ranges i s)` by
    simp[source_memory_read_ranges_def] >>
  suspend "positive_geometry"
QED

Resume ld_mcopy_certificate_backward[positive_geometry]:
  `!j. j<w2n n ==> ((w2n r+j = w2n u+j /\ w2n r+j<lo) \/
     ld_site_bytes E live (w2n r+j) (w2n u+j))` by suspend "source_classification" >>
  `((w2n p = w2n q /\ w2n p+w2n n <= lo) \/
    (?owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz /\
      bs <= w2n p /\ w2n p+w2n n <= bs+sz /\ w2n q=bt+(w2n p-bs)))` by
    suspend "destination_classification" >>
  `(!a b. ((a=b /\ a<lo) \/ ld_site_bytes E live a b) ==>
      ((w2n p<=a /\ a<w2n p+w2n n) <=> (w2n q<=b /\ b<w2n q+w2n n))) /\
   (!a b. ((a=b /\ a<lo) \/ ld_site_bytes E live a b) /\
      w2n p<=a /\ a<w2n p+w2n n ==> a-w2n p=b-w2n q)` by
    (irule ld_fixed_live_write_footprint >>
     conj_tac >- metis_tac[] >>
     conj_tac >- asm_rewrite_tac[] >> metis_tac[]) >>
  asm_rewrite_tac[]
QED

Resume ld_mcopy_certificate_backward[destination_classification]:
  `0 < w2n n` by decide_tac >>
  drule ld_access_write_classification >>
  disch_then (qspecl_then [`w2n p`,`w2n n`] mp_tac) >> simp[] >> strip_tac
  >- (disj1_tac >> simp[] >>
      `ld_op_prov AG dst = NONE` by
        (qpat_x_assum `!ops. _` mp_tac >>
         simp[mem_write_ops_def, GSYM ld_erase_op_prov]) >>
      drule ld_owned_operand_clean >> disch_then (qspec_then `dst` mp_tac) >> simp[]) >>
  disj2_tac >> gvs[mem_write_ops_def] >>
  `owner IN live` by metis_tac[] >>
  `v IN U` by simp[] >>
  `?bt. ld_site_entry E owner bs bt sz` by
    (drule ld_owned_operand_value >>
     disch_then (qspecl_then [`q`,`p`,`Var v`] mp_tac) >>
     simp[ld_op_prov_def, ld_owned_value_def] >> metis_tac[]) >>
  `bs+sz < dimword(:256)` by metis_tac[] >>
  `!bt. ld_site_entry E owner bs bt sz ==> bt+sz < dimword(:256)` by metis_tac[] >>
  drule_all (SRULE[arithmeticTheory.ADD_COMM] ld_owned_address_transport) >> metis_tac[]
QED

Resume ld_mcopy_certificate_backward[source_classification]:
  markerLib.RESUME_TAC >>
  `0 < w2n n` by decide_tac >>
  drule ld_access_read_classification >>
  disch_then (qspecl_then [`w2n r`,`w2n n`] mp_tac) >> simp[] >> strip_tac
  >- (`ld_op_prov AG src = NONE` by
        (qpat_x_assum `!ops. _` mp_tac >>
         simp[mem_read_ops_def, GSYM ld_erase_op_prov]) >>
      `r = u` by
        (drule ld_owned_operand_clean >> disch_then (qspec_then `src` mp_tac) >> simp[]) >>
      rpt strip_tac >> disj1_tac >> gvs[] >> decide_tac) >>
  gvs[mem_read_ops_def] >>
  `owner IN live` by metis_tac[] >>
  `v IN U` by simp[] >>
  `?bt. ld_site_entry E owner bs bt sz` by
    (drule ld_owned_operand_value >>
     disch_then (qspecl_then [`u`,`r`,`Var v`] mp_tac) >>
     simp[ld_op_prov_def, ld_owned_value_def] >> metis_tac[]) >>
  `bs+sz < dimword(:256)` by metis_tac[] >>
  `!bt. ld_site_entry E owner bs bt sz ==> bt+sz < dimword(:256)` by metis_tac[] >>
  drule_all (SRULE[arithmeticTheory.ADD_COMM] ld_owned_address_transport) >> strip_tac >>
  rpt strip_tac >> disj2_tac >> simp[ld_site_bytes_def] >>
  qexistsl_tac [`owner`,`bs`,`bt'`,`sz`,`w2n r-bs+j`] >>
  simp[] >> decide_tac
QED

Resume ld_mcopy_certificate_backward[frame_transport]:
  qpat_x_assum `t' = mcopy _ _ _ t` kall_tac >>
  qexists_tac `s'` >> asm_rewrite_tac[] >>
  dxrule ld_memory_restore_normalize >> disch_then SUBST_ALL_TAC >>
  dxrule ld_memory_restore_normalize >> disch_then SUBST_ALL_TAC >>
  simp[ld_empty_outputs_prov_tvar, ld_frame_embedding_def, ld_alloc_account_def,
       ld_owned_vars_def, lookup_var_def, allocas_from_def] >>
  fs[ld_owned_vars_def, ld_frame_embedding_def, ld_alloc_account_def,
     allocas_from_def] >>
  simp[op_taint_def, ld_empty_outputs_prov_tvar,
       step_taint_def, store_taint_def, imm_taint_def, adopt_reset_def,
       set_var_taint_def, DRESTRICT_UNIV] >>
  fs[mcopy_def, lookup_var_def, op_taint_def] >> gvs[] >> asm_rewrite_tac[]
QED

Finalise ld_mcopy_certificate_backward

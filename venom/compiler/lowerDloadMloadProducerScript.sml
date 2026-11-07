Theory lowerDloadMloadProducer
Ancestors
  lowerDloadMemoryExecution lowerDloadShiftProducer lowerDloadVariableTransport
  lowerDloadMaskBounds lowerDloadParamProducer lowerDloadOpaqueExecution
  lowerDloadReachableDiscipline lowerDloadPairedBoundary lowerDloadOwnership
  lowerDloadProvenanceSupport o1PassContract
  lowerDloadTargetGeometry lowerDloadAllocation ptrDiscipline
  pointerConfinedDefs contextCodegenRel memLocDefs venomInst
  venomExecSemantics venomState finite_map list pred_set words codegenRel

Theorem ld_mload_update:
  i.inst_opcode = MLOAD /\ i.inst_outputs = [out] /\
  step_inst fuel C i s = OK s' ==> ?w. s' = update_var out w s
Proof
  strip_tac >> qpat_x_assum `step_inst fuel C i s = OK s'` mp_tac >>
  simp[Once step_inst_non_invoke, SimpLHS] >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  qpat_assum `i.inst_opcode = _` (fn th => pure_rewrite_tac[th]) >>
  simp[exec_read1_def, SimpLHS] >>
  strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem ld_mload_taint_nonvar:
  i.inst_opcode = MLOAD /\ i.inst_outputs = [out] /\
  step_inst fuel C i s = OK s' ==>
  (step_taint i s s' tn).t_mem = tn.t_mem /\
  (step_taint i s s' tn).t_stor = tn.t_stor /\
  (step_taint i s s' tn).t_trans = tn.t_trans /\
  (step_taint i s s' tn).t_imm = tn.t_imm
Proof
  strip_tac >> drule_all ld_mload_update >> strip_tac >> gvs[] >>
  simp[step_taint_def, mem_taint_def, new_site_bytes_def,
    written_taint_def, step_writes_def, source_memory_write_ranges_def,
    store_taint_def, imm_taint_def, adopt_reset_def, update_var_def,
    range_bytes_def, EXTENSION, FLOOKUP_DEF] >>
  simp[SF CONJ_ss] >>
  namedCases_on `i.inst_operands` ["", "a ops1"] >> simp[] >>
  namedCases_on `ops1` ["", "b ops2"] >> simp[] >>
  namedCases_on `ops2` ["", "c ops3"] >> simp[] >>
  Cases_on `ops3` >> simp[]
QED

Theorem ld_mload_live_backward:
  i.inst_opcode = MLOAD /\ i.inst_operands = [op] /\
  i.inst_outputs = [out] /\
  ld_owned_vars V E AG AH tn un s t /\
  (!v. op = Var v ==> v IN V) /\ op_taint tn op = {} /\
  access_ok lo (ld_erase AG) fn i s /\ ~in_revert_forward fn s /\
  (!v owner bs sz. FLOOKUP AG v = SOME(owner,(bs,sz)) ==>
    owner IN live /\ bs+sz < dimword(:256)) /\
  (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
    bt+sz < dimword(:256)) /\
  (!a. a < lo ==> R a a) /\
  (!a b. ld_site_bytes E live a b ==> R a b) /\
  ld_byte_rel R tn.t_mem un.t_mem
    (\a. read_memory a 1 s) (\b. read_memory b 1 t) /\
  step_inst fuelT CT i t = OK t' ==>
  ?s'. step_inst fuelS CS i s = OK s' /\
    ld_owned_vars V E (ld_step_prov AP AG L i) (ld_step_prov BP AH H i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t'
Proof
  strip_tac >>
  `!u. step_inst fuelS CS i u = step_inst fuelT CT i u` by
    (gen_tac >> simp[step_inst_non_invoke] >>
     pure_once_rewrite_tac[step_inst_base_def] >>
     qpat_assum `i.inst_opcode = MLOAD` (fn th => pure_rewrite_tac[th]) >> simp[]) >>
  simp[] >> irule ld_owned_mload_backward >>
  simp[] >> qexists_tac `R` >> simp[] >>
  rpt strip_tac >> drule_all ld_owned_mload_live_range >> simp[]
QED

Theorem ld_mload_certificate_backward:
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  ptr_discipline lo CS vs0 /\
  (!f. MEM f CS.ctx_functions ==> fn_ptr_ok P f) /\ opaque_use_ok fn /\
  i.inst_opcode = MLOAD /\ i.inst_operands = [op] /\ i.inst_outputs = [out] /\
  ~in_revert_forward fn s /\
  (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
    bs+sz < dimword(:256) /\ bt+sz < dimword(:256)) /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  LENGTH AP = LENGTH s.vs_params /\ LENGTH BP = LENGTH t.vs_params /\
  LENGTH s.vs_params = LENGTH t.vs_params /\
  (!q. q < LENGTH s.vs_params ==>
    ld_owned_value E (EL q AP) (EL q BP) {} {}
      (EL q s.vs_params) (EL q t.vs_params)) /\
  ld_frame_embedding E L H s t /\
  LIST_REL (ld_owned_selection E) AP BP /\
  (!v. ld_owned_selection E (FLOOKUP AG v) (FLOOKUP BH v)) /\
  ld_owned_vars {v | v IN V /\ ~retpc_var fn v} E AG BH tn un s t /\
  (!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  ld_alloc_account keys d A s t /\
  ld_frame_bound t.vs_alloca_next H BP BH /\
  ld_stack_bound t.vs_alloca_next gstk /\ lo <= t.vs_alloca_next /\
  (!owner bs sz. ld_live astk L AP AG (owner,(bs,sz)) ==>
    owner IN live /\ lo <= bs) /\
  (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
    lo <= bs /\ lo <= bt /\ bs+sz <= s.vs_alloca_next /\
    bt+sz <= t.vs_alloca_next) /\
  (!owner other bs bt sz cs ct cz.
    owner IN live /\ other IN live /\ owner <> other /\
    ld_site_entry E owner bs bt sz /\ ld_site_entry E other cs ct cz ==>
    (bs+sz <= cs \/ cs+cz <= bs) /\ (bt+sz <= ct \/ ct+cz <= bt)) /\
  ld_byte_rel (\a b. (a=b /\ a<lo) \/ ld_site_bytes E live a b)
    tn.t_mem un.t_mem (\a. read_memory a 1 s) (\b. read_memory b 1 t) /\
  (!v. op_taint tn (Var v) SUBSET count 32) /\
  (!v. op_taint un (Var v) SUBSET count 32) /\
  un.t_stor SUBSET tn.t_stor /\ un.t_trans SUBSET tn.t_trans /\
  un.t_imm SUBSET tn.t_imm /\
  step_inst fuelT CT i t = OK t' ==>
  ?s'. step_inst fuelS CS i s = OK s' /\
    ld_frame_embedding E L H s' t' /\
    LIST_REL (ld_owned_selection E) AP BP /\
    (!v. ld_owned_selection E (FLOOKUP (ld_step_prov AP AG L i) v)
      (FLOOKUP (ld_step_prov BP BH H i) v)) /\
    ld_owned_vars {v | v IN V /\ ~retpc_var fn v} E
      (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t' /\
    (!v. v IN V ==> (lookup_var v s' = NONE <=> lookup_var v t' = NONE)) /\
    ld_alloc_account keys d A s' t' /\
    ld_frame_bound t'.vs_alloca_next H BP (ld_step_prov BP BH H i) /\
    ld_stack_bound t'.vs_alloca_next gstk /\ lo <= t'.vs_alloca_next /\
    (!owner bs sz. ld_live astk L AP (ld_step_prov AP AG L i) (owner,(bs,sz)) ==>
      owner IN live /\ lo <= bs) /\
    (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
      lo <= bs /\ lo <= bt /\ bs+sz <= s'.vs_alloca_next /\
      bt+sz <= t'.vs_alloca_next) /\
    (!owner other bs bt sz cs ct cz.
      owner IN live /\ other IN live /\ owner <> other /\
      ld_site_entry E owner bs bt sz /\ ld_site_entry E other cs ct cz ==>
      (bs+sz <= cs \/ cs+cz <= bs) /\ (bt+sz <= ct \/ ct+cz <= bt)) /\
    ld_byte_rel (\a b. (a=b /\ a<lo) \/ ld_site_bytes E live a b)
      (step_taint i s s' tn).t_mem (step_taint i t t' un).t_mem
      (\a. read_memory a 1 s') (\b. read_memory b 1 t') /\
    (!v. op_taint (step_taint i s s' tn) (Var v) SUBSET count 32) /\
    (!v. op_taint (step_taint i t t' un) (Var v) SUBSET count 32) /\
    (step_taint i t t' un).t_stor SUBSET (step_taint i s s' tn).t_stor /\
    (step_taint i t t' un).t_trans SUBSET (step_taint i s s' tn).t_trans /\
    (step_taint i t t' un).t_imm SUBSET (step_taint i s s' tn).t_imm /\
    LENGTH AP = LENGTH s'.vs_params /\ LENGTH BP = LENGTH t'.vs_params /\
    LENGTH s'.vs_params = LENGTH t'.vs_params /\
    (!q. q < LENGTH s'.vs_params ==>
      ld_owned_value E (EL q AP) (EL q BP) {} {}
        (EL q s'.vs_params) (EL q t'.vs_params)) /\
    (s' with vs_vars := s.vs_vars) = s /\
    (t' with vs_vars := t.vs_vars) = t
Proof
  strip_tac >>
  `MEM i (fn_insts fn)` by
    (drule ld_annotated_active_inst >>
     simp[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[EL_MEM]) >>
  `!v. op = Var v ==> v IN {v | v IN V /\ ~retpc_var fn v}` by
    (rpt strip_tac >> simp[] >>
     irule ld_retpc_observable_operand >> simp[] >> qexists_tac `i` >>
     simp[] >> metis_tac[MEM]) >>
  `access_ok lo (ld_erase AG) fn i s` by metis_tac[ld_annotated_access_ok] >>
  `taint_ok fn tn i s` by metis_tac[ld_annotated_taint_ok] >>
  `op_taint tn op = {}` by
    (irule ld_taint_operand_clean >> qexistsl_tac [`fn`,`i`,`s`] >> simp[]) >>
  `!v owner bs sz. FLOOKUP AG v = SOME(owner,(bs,sz)) ==>
    owner IN live /\ bs+sz < dimword(:256)` by
    (rpt strip_tac >>
     `ld_live astk L AP AG (owner,(bs,sz))` by
       (simp[ld_live_def, ld_selected_def] >> metis_tac[]) >>
     `owner IN live` by metis_tac[] >>
     `?bt. ld_site_entry E owner bs bt sz` by
       (qpat_x_assum `!v. ld_owned_selection E _ _` (qspec_then `v` mp_tac) >>
        simp[ld_owned_selection_def] >> metis_tac[]) >> metis_tac[]) >>
  `!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
    bt+sz < dimword(:256)` by metis_tac[] >>
  `?s'. step_inst fuelS CS i s = OK s' /\
    ld_owned_vars {v | v IN V /\ ~retpc_var fn v} E
      (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t'` by
    (irule ld_mload_live_backward >> simp[] >>
     conj_tac >- metis_tac[] >>
     conj_tac >- (fs[] >> metis_tac[]) >>
     qexistsl_tac [`\a b. (a=b /\ a<lo) \/ ld_site_bytes E live a b`,
                    `fn`, `live`, `lo`] >> simp[] >> rpt conj_tac >> fs[]) >>
  qexists_tac `s'` >>
  `?w. s' = update_var out w s` by metis_tac[ld_mload_update] >>
  `?w. t' = update_var out w t` by metis_tac[ld_mload_update] >>
  `!v. v IN V ==> (lookup_var v s' = NONE <=> lookup_var v t' = NONE)` by
    (simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >> metis_tac[lookup_var_def]) >>
  `!v. ld_owned_selection E (FLOOKUP (ld_step_prov AP AG L i) v)
      (FLOOKUP (ld_step_prov BP BH H i) v)` by
    (`ld_step_prov AP AG L i = ld_set_prov AG [out] NONE /\
      ld_step_prov BP BH H i = ld_set_prov BH [out] NONE` by
       simp[ld_step_prov_def, ld_out_prov_def] >>
     simp[] >> irule ld_owned_set_selection >> simp[ld_owned_selection_def]) >>
  `ld_frame_bound t.vs_alloca_next H BP (ld_step_prov BP BH H i)` by
    (irule ld_frame_bound_step >> simp[]) >>
  `!owner bs sz. ld_live astk L AP (ld_step_prov AP AG L i) (owner,(bs,sz)) ==>
      owner IN live /\ lo <= bs` by metis_tac[ld_live_step_prov] >>
  `s' with vs_vars := s.vs_vars = s` by simp[ld_update_var_restore] >>
  `t' with vs_vars := t.vs_vars = t` by simp[ld_update_var_restore] >>
  `ld_frame_embedding E L H s' t'` by metis_tac[ld_frame_embedding_vars_transport] >>
  `ld_alloc_account keys d A s' t'` by metis_tac[ld_alloc_account_vars_transport] >>
  `ld_byte_rel (\a b. (a=b /\ a<lo) \/ ld_site_bytes E live a b)
    tn.t_mem un.t_mem (\a. read_memory a 1 s') (\b. read_memory b 1 t')` by
    metis_tac[ld_byte_rel_vars_transport] >>
  `(step_taint i s s' tn).t_mem = tn.t_mem /\
   (step_taint i s s' tn).t_stor = tn.t_stor /\
   (step_taint i s s' tn).t_trans = tn.t_trans /\
   (step_taint i s s' tn).t_imm = tn.t_imm /\
   (step_taint i t t' un).t_mem = un.t_mem /\
   (step_taint i t t' un).t_stor = un.t_stor /\
   (step_taint i t t' un).t_trans = un.t_trans /\
   (step_taint i t t' un).t_imm = un.t_imm` by
    metis_tac[ld_mload_taint_nonvar] >>
  qpat_x_assum `s' = update_var out w s` kall_tac >>
  qpat_x_assum `t' = update_var out w' t` kall_tac >>
  simp[ld_step_taint_bound] >>
  dxrule ld_vars_restore_normalize >> disch_then SUBST_ALL_TAC >>
  dxrule ld_vars_restore_normalize >> disch_then SUBST_ALL_TAC >>
  simp[] >> rpt conj_tac >> fs[]
QED

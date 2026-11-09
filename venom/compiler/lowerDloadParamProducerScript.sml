Theory lowerDloadParamProducer
Ancestors
  lowerDloadOpaqueExecution lowerDloadOwnership lowerDloadMaskBounds
  ptrDiscipline venomExecSemantics venomInst venomState finite_map list pred_set
  lowerDloadPairedBoundary lowerDloadFrameCertificate lowerDloadAllocation lowerDloadRelocation codegenRel

Theorem ld_param_backward:
  i.inst_opcode = PARAM /\ i.inst_operands = [Lit idx] /\
  i.inst_outputs = [out] /\
  LENGTH AP = LENGTH s.vs_params /\ LENGTH BP = LENGTH t.vs_params /\
  LENGTH s.vs_params = LENGTH t.vs_params /\
  (!q. q < LENGTH s.vs_params ==>
    ld_owned_value E (EL q AP) (EL q BP) {} {}
      (EL q s.vs_params) (EL q t.vs_params)) /\
  ld_owned_vars U E AG BH tn un s t /\
  (!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  step_inst fuel CT i t = OK t' ==>
  ?s'. step_inst fuel CS i s = OK s' /\
    s' = update_var out (EL (w2n idx) s.vs_params) s /\
    t' = update_var out (EL (w2n idx) t.vs_params) t /\
    w2n idx < LENGTH s.vs_params /\
    ld_owned_vars U E (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t' /\
    (!v. v IN V ==> (lookup_var v s' = NONE <=> lookup_var v t' = NONE))
Proof
  strip_tac >>
  qpat_x_assum `step_inst fuel CT i t = OK t'` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def] >>
  IF_CASES_TAC >> simp[] >> strip_tac >> gvs[] >>
  reverse conj_tac >- metis_tac[ld_lookup_defined_update] >>
  simp[ld_step_prov_def, ld_out_prov_def] >>
  irule ld_owned_vars_update_supported >>
  goal_assum (drule_at Any) >>
  simp[step_taint_def, out_taint_def, eval_operand_def] >>
  qexistsl_tac [`{}`, `{}`] >> simp[]
QED

Theorem ld_live_step_prov:
  ld_live astk L AP (ld_step_prov AP AG L i) site ==>
  ld_live astk L AP AG site
Proof
  simp[ld_live_def] >> metis_tac[ld_step_selected]
QED

Theorem ld_param_selection:
  i.inst_opcode = PARAM /\ i.inst_operands = [Lit idx] /\
  LENGTH AP = LENGTH BP /\ w2n idx < LENGTH AP /\
  LIST_REL (ld_owned_selection E) AP BP /\
  (!v. ld_owned_selection E (FLOOKUP AG v) (FLOOKUP BH v)) ==>
  !v. ld_owned_selection E (FLOOKUP (ld_step_prov AP AG L i) v)
    (FLOOKUP (ld_step_prov BP BH H i) v)
Proof
  strip_tac >> simp[ld_step_prov_def, ld_out_prov_def] >>
  `ld_owned_selection E (EL (w2n idx) AP) (EL (w2n idx) BP)` by
    (fs[LIST_REL_EL_EQN]) >>
  metis_tac[ld_owned_set_selection]
QED

Theorem ld_update_var_restore:
  (update_var out x s) with vs_vars := s.vs_vars = s
Proof
  simp[update_var_def]
QED

Theorem ld_frame_embedding_update_var:
  ld_frame_embedding E L H (update_var out x s) (update_var out y t) <=>
  ld_frame_embedding E L H s t
Proof
  simp[ld_frame_embedding_def, update_var_def]
QED

Theorem ld_alloc_account_update_var:
  ld_alloc_account keys d A (update_var out x s) (update_var out y t) <=>
  ld_alloc_account keys d A s t
Proof
  simp[ld_alloc_account_def, update_var_def]
QED

Theorem ld_singleton_update_taint_nonvar:
  i.inst_operands = [op] /\ source_memory_write_ranges i s = [] ==>
  (step_taint i s (update_var out x s) tn).t_mem = tn.t_mem /\
  (step_taint i s (update_var out x s) tn).t_stor = tn.t_stor /\
  (step_taint i s (update_var out x s) tn).t_trans = tn.t_trans /\
  (step_taint i s (update_var out x s) tn).t_imm = tn.t_imm
Proof
  strip_tac >>
  simp[step_taint_def, mem_taint_def, new_site_bytes_def,
       written_taint_def, step_writes_def, store_taint_def, imm_taint_def,
       adopt_reset_def, update_var_def,
       range_bytes_def, EXTENSION, FLOOKUP_DEF] >> metis_tac[]
QED

Theorem ld_param_taint_nonvar:
  i.inst_opcode = PARAM /\ i.inst_operands = [Lit idx] ==>
  (step_taint i s (update_var out x s) tn).t_mem = tn.t_mem /\
  (step_taint i s (update_var out x s) tn).t_stor = tn.t_stor /\
  (step_taint i s (update_var out x s) tn).t_trans = tn.t_trans /\
  (step_taint i s (update_var out x s) tn).t_imm = tn.t_imm
Proof
  strip_tac >> irule ld_singleton_update_taint_nonvar >>
  simp[source_memory_write_ranges_def]
QED

Theorem ld_byte_rel_update_var:
  ld_byte_rel R Ms Mt (\a. read_memory a 1 (update_var out x s))
    (\b. read_memory b 1 (update_var out y t)) <=>
  ld_byte_rel R Ms Mt (\a. read_memory a 1 s) (\b. read_memory b 1 t)
Proof
  simp[read_memory_def, update_var_def]
QED

Theorem ld_param_certificate_backward:
  i.inst_opcode = PARAM /\ i.inst_operands = [Lit idx] /\
  i.inst_outputs = [out] /\
  LENGTH AP = LENGTH s.vs_params /\ LENGTH BP = LENGTH t.vs_params /\
  LENGTH s.vs_params = LENGTH t.vs_params /\
  (!q. q < LENGTH s.vs_params ==>
    ld_owned_value E (EL q AP) (EL q BP) {} {}
      (EL q s.vs_params) (EL q t.vs_params)) /\
  ld_frame_embedding E L H s t /\
  LIST_REL (ld_owned_selection E) AP BP /\
  (!v. ld_owned_selection E (FLOOKUP AG v) (FLOOKUP BH v)) /\
  ld_owned_vars U E AG BH tn un s t /\
  (!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  ld_alloc_account keys d A s t /\ d = 32 * SUM (MAP CARD suspended) /\
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
  step_inst fuel CT i t = OK t' ==>
  ?s'. step_inst fuel CS i s = OK s' /\
    ld_frame_embedding E L H s' t' /\
    LIST_REL (ld_owned_selection E) AP BP /\
    (!v. ld_owned_selection E (FLOOKUP (ld_step_prov AP AG L i) v)
      (FLOOKUP (ld_step_prov BP BH H i) v)) /\
    ld_owned_vars U E (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t' /\
    (!v. v IN V ==> (lookup_var v s' = NONE <=> lookup_var v t' = NONE)) /\
    ld_alloc_account keys d A s' t' /\ d = 32 * SUM (MAP CARD suspended) /\
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
  strip_tac >> drule_all ld_param_backward >>
  disch_then (qspecl_then [`L`, `H`, `CS`] strip_assume_tac) >>
  qexists_tac `s'` >>
  `!v. ld_owned_selection E (FLOOKUP (ld_step_prov AP AG L i) v)
    (FLOOKUP (ld_step_prov BP BH H i) v)` by
    (irule ld_param_selection >> simp[] >> metis_tac[]) >>
  `ld_frame_bound t.vs_alloca_next H BP (ld_step_prov BP BH H i)` by
    (irule ld_frame_bound_step >> simp[]) >>
  `!owner bs sz. ld_live astk L AP (ld_step_prov AP AG L i) (owner,(bs,sz)) ==>
    owner IN live /\ lo <= bs` by metis_tac[ld_live_step_prov] >>
  simp[ld_step_taint_bound] >>
  gvs[] >>
  simp[ld_frame_embedding_update_var, ld_alloc_account_update_var,
       ld_param_taint_nonvar, ld_byte_rel_update_var, ld_update_var_restore] >>
  simp[update_var_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

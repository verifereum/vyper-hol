Theory lowerDloadAffineProducer
Ancestors
  lowerDloadPureEffects
  lowerDloadProvenanceSupport lowerDloadOrdinaryExecution lowerDloadOwnership
  lowerDloadReachableDiscipline ptrDiscipline pointerConfinedDefs
  contextCodegenRel memLocDefs venomInst list pred_set
  lowerDloadVariableTransport lowerDloadMaskBounds lowerDloadPairedBoundary
  lowerDloadParamProducer lowerDloadOpaqueExecution
  venomExecSemantics venomState finite_map codegenRel o1PassContract

Theorem ld_annotated_affine_prov:
  (!f. MEM f ctx.ctx_functions ==> fn_ptr_ok P f) /\
  ld_annotated_reachable vs0 ctx astk k L AP AG tn fn i s /\
  (i.inst_opcode = ADD \/ i.inst_opcode = SUB) /\
  i.inst_operands = [a;b] ==>
  ld_op_prov AG b = NONE \/
    (i.inst_opcode = ADD /\ ld_op_prov AG a = NONE)
Proof
  strip_tac >>
  `MEM fn ctx.ctx_functions` by metis_tac[ld_annotated_fn_member] >>
  `fn_ptr_ok P fn` by metis_tac[] >>
  `?bb. MEM bb fn.fn_blocks /\ MEM i bb.bb_instructions` by
    (drule ld_annotated_active_inst >>
     simp[active_inst_def] >> metis_tac[EL_MEM]) >>
  `(~(?u v. a = Var u /\ b = Var v /\
       u IN fn_pv P fn /\ v IN fn_pv P fn)) /\
    (i.inst_opcode = SUB ==> !v. b = Var v ==> v NOTIN fn_pv P fn)` by
    (fs[fn_ptr_ok_def, affine_pointer_ops_def, fn_pv_def] >> metis_tac[]) >>
  (Cases_on `!v. b = Var v ==> v NOTIN fn_pv P fn`
  >- (disj1_tac >> irule ld_annotated_scalar_prov >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  disj2_tac >>
  `i.inst_opcode = ADD` by metis_tac[] >> simp[] >>
  irule ld_annotated_scalar_prov >> goal_assum (drule_at Any) >>
  simp[] >> metis_tac[])
QED

Theorem ld_annotated_affine_backward:
  (!f. MEM f ctx.ctx_functions ==> fn_ptr_ok P f) /\
  ptr_discipline lo ctx vs0 /\
  ld_annotated_reachable vs0 ctx astk k L AP AG tn fn i s /\
  (i.inst_opcode = ADD \/ i.inst_opcode = SUB) /\
  i.inst_operands = [a;b] /\ i.inst_outputs = [out] /\
  ld_owned_vars V E AG BH tn un s t /\
  (!v. a = Var v \/ b = Var v ==> v IN V) /\
  step_inst fuelT CT i t = OK t' ==>
  ?s'. step_inst fuelS ctx i s = OK s' /\
    ld_owned_vars V E (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t'
Proof
  strip_tac >>
  `taint_ok fn tn i s` by metis_tac[ld_annotated_taint_ok] >>
  `!op. MEM op i.inst_operands ==> op_taint tn op = {}` by
    (rpt strip_tac >> irule ld_taint_operand_clean >>
     qexistsl [`fn`, `i`, `s`] >> simp[]) >>
  `op_taint tn a = {} /\ op_taint tn b = {}` by metis_tac[MEM] >>
  `ld_op_prov AG b = NONE \/
    (i.inst_opcode = ADD /\ ld_op_prov AG a = NONE)` by
    metis_tac[ld_annotated_affine_prov] >>
  irule ld_owned_offset_cases_backward >> simp[] >> metis_tac[]
QED

Theorem ld_owned_first_selection:
  (!v. ld_owned_selection E (FLOOKUP AG v) (FLOOKUP BH v)) ==>
  !ops. ld_owned_selection E (ld_first_prov AG ops) (ld_first_prov BH ops)
Proof
  strip_tac >> Induct
  >- simp[ld_first_prov_def, ld_owned_selection_def] >>
  gen_tac >> pure_rewrite_tac[ld_first_prov_def] >>
  `ld_owned_selection E (ld_op_prov AG h) (ld_op_prov BH h)` by
    metis_tac[ld_owned_op_selection] >>
  Cases_on `ld_op_prov AG h` >> Cases_on `ld_op_prov BH h` >>
  gvs[ld_owned_selection_def]
QED

Theorem ld_affine_update:
  (i.inst_opcode = ADD \/ i.inst_opcode = SUB) /\
  i.inst_outputs = [out] /\ step_inst fuel C i s = OK s' ==>
  ?w. s' = update_var out w s
Proof
  strip_tac >> irule ld_pure_update >>
  simp[MEM] >> metis_tac[]
QED

Theorem ld_affine_restore:
  (i.inst_opcode = ADD \/ i.inst_opcode = SUB) /\
  i.inst_outputs = [out] /\ step_inst fuel C i s = OK s' ==>
  (s' with vs_vars := s.vs_vars) = s
Proof
  strip_tac >> `?w. s' = update_var out w s` by metis_tac[ld_affine_update] >>
  simp[ld_update_var_restore]
QED

Theorem ld_affine_defined:
  (i.inst_opcode = ADD \/ i.inst_opcode = SUB) /\
  i.inst_outputs = [out] /\ step_inst fuel C i s = OK s' ==>
  !v. lookup_var v s' = NONE <=> v <> out /\ lookup_var v s = NONE
Proof
  strip_tac >> `?w. s' = update_var out w s` by metis_tac[ld_affine_update] >>
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem ld_affine_selection:
  (i.inst_opcode = ADD \/ i.inst_opcode = SUB) /\
  (!v. ld_owned_selection E (FLOOKUP AG v) (FLOOKUP BH v)) ==>
  !v. ld_owned_selection E (FLOOKUP (ld_step_prov AP AG L i) v)
    (FLOOKUP (ld_step_prov BP BH H i) v)
Proof
  strip_tac >> simp[ld_step_prov_def, ld_out_prov_def] >>
  irule ld_owned_set_selection >> simp[ld_owned_first_selection]
QED

Theorem ld_affine_taint_nonvar:
  (i.inst_opcode = ADD \/ i.inst_opcode = SUB) /\
  i.inst_operands = [a;b] /\
  i.inst_outputs = [out] /\ step_inst fuel C i s = OK s' ==>
  (step_taint i s s' tn).t_mem = tn.t_mem /\
  (step_taint i s s' tn).t_stor = tn.t_stor /\
  (step_taint i s s' tn).t_trans = tn.t_trans /\
  (step_taint i s s' tn).t_imm = tn.t_imm
Proof
  strip_tac >> irule ld_pure_taint_nonvar >>
  simp[MEM] >> metis_tac[]
QED

Theorem ld_affine_certificate_backward:
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  ptr_discipline lo CS vs0 /\
  (!f. MEM f CS.ctx_functions ==> fn_ptr_ok P f) /\ opaque_use_ok fn /\
  (i.inst_opcode = ADD \/ i.inst_opcode = SUB) /\
  i.inst_operands = [a;b] /\ i.inst_outputs = [out] /\
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
  strip_tac >>
  `MEM i (fn_insts fn)` by
    (drule ld_annotated_active_inst >>
     simp[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[EL_MEM]) >>
  `!v. a = Var v \/ b = Var v ==> v IN {v | v IN V /\ ~retpc_var fn v}` by
    (rpt strip_tac >> simp[] >>
     irule ld_retpc_observable_operand >> simp[] >> qexists_tac `i` >> simp[]) >>
  `?s'. step_inst fuelS CS i s = OK s' /\
    ld_owned_vars {v | v IN V /\ ~retpc_var fn v} E
      (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t'` by
    (irule ld_annotated_affine_backward >> simp[] >> fs[] >> metis_tac[]) >>
  qexists_tac `s'` >>
  `!v. v IN V ==> (lookup_var v s' = NONE <=> lookup_var v t' = NONE)` by
    metis_tac[ld_affine_defined] >>
  `!v. ld_owned_selection E (FLOOKUP (ld_step_prov AP AG L i) v)
      (FLOOKUP (ld_step_prov BP BH H i) v)` by metis_tac[ld_affine_selection] >>
  `ld_frame_bound t.vs_alloca_next H BP (ld_step_prov BP BH H i)` by
    (irule ld_frame_bound_step >> simp[]) >>
  `!owner bs sz. ld_live astk L AP (ld_step_prov AP AG L i) (owner,(bs,sz)) ==>
      owner IN live /\ lo <= bs` by metis_tac[ld_live_step_prov] >>
  `s' with vs_vars := s.vs_vars = s` by metis_tac[ld_affine_restore] >>
  `t' with vs_vars := t.vs_vars = t` by metis_tac[ld_affine_restore] >>
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
    metis_tac[ld_affine_taint_nonvar] >>
  simp[ld_step_taint_bound] >>
  dxrule ld_vars_restore_normalize >> disch_then SUBST_ALL_TAC >>
  dxrule ld_vars_restore_normalize >> disch_then SUBST_ALL_TAC >>
  simp[] >> rpt conj_tac >> fs[]
QED

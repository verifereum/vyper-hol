Theory lowerDloadScalarProducer
Ancestors
  lowerDloadPureEffects
  lowerDloadReachableScalarExecution lowerDloadVariableTransport
  lowerDloadMaskBounds lowerDloadOwnership lowerDloadPairedBoundary lowerDloadParamProducer
  ptrDiscipline venomExecSemantics venomState finite_map list pred_set codegenRel
  lowerDloadOpaqueExecution lowerDloadProvenanceSupport pointerConfinedDefs venomInst
  contextCodegenRel o1PassContract

Theorem ld_scalar_update:
  MEM i.inst_opcode [MUL; Div; Mod; SDIV; SMOD; Exp; ADDMOD; MULMOD;
    SLT; SGT; ISZERO; AND; OR; XOR; NOT] /\
  i.inst_outputs = [out] /\ step_inst fuel C i s = OK s' ==>
  ?w. s' = update_var out w s
Proof
  strip_tac >> irule ld_pure_update >>
  simp[MEM] >> fs[MEM] >> metis_tac[]
QED

Theorem ld_scalar_restore:
  MEM i.inst_opcode [MUL; Div; Mod; SDIV; SMOD; Exp; ADDMOD; MULMOD;
    SLT; SGT; ISZERO; AND; OR; XOR; NOT] /\
  i.inst_outputs = [out] /\ step_inst fuel C i s = OK s' ==>
  (s' with vs_vars := s.vs_vars) = s
Proof
  strip_tac >> drule_all ld_scalar_update >> strip_tac >>
  simp[ld_update_var_restore]
QED

Theorem ld_scalar_defined:
  MEM i.inst_opcode [MUL; Div; Mod; SDIV; SMOD; Exp; ADDMOD; MULMOD;
    SLT; SGT; ISZERO; AND; OR; XOR; NOT] /\
  i.inst_outputs = [out] /\ step_inst fuel C i s = OK s' ==>
  !v. lookup_var v s' = NONE <=> v <> out /\ lookup_var v s = NONE
Proof
  strip_tac >> drule_all ld_scalar_update >> strip_tac >>
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem ld_scalar_prov:
  MEM i.inst_opcode [MUL; Div; Mod; SDIV; SMOD; Exp; ADDMOD; MULMOD;
    SLT; SGT; ISZERO; AND; OR; XOR; NOT] /\ i.inst_outputs = [out] ==>
  ld_step_prov AP AG L i = ld_set_prov AG [out] NONE
Proof
  simp[MEM] >> strip_tac >> simp[ld_step_prov_def, ld_out_prov_def]
QED

Theorem ld_scalar_taint_nonvar:
  MEM i.inst_opcode [MUL; Div; Mod; SDIV; SMOD; Exp; ADDMOD; MULMOD;
    SLT; SGT; ISZERO; AND; OR; XOR; NOT] /\
  i.inst_outputs = [out] /\ step_inst fuel C i s = OK s' ==>
  (step_taint i s s' tn).t_mem = tn.t_mem /\
  (step_taint i s s' tn).t_stor = tn.t_stor /\
  (step_taint i s s' tn).t_trans = tn.t_trans /\
  (step_taint i s s' tn).t_imm = tn.t_imm
Proof
  strip_tac >> irule ld_pure_taint_nonvar >>
  simp[MEM] >> fs[MEM] >> metis_tac[]
QED

Theorem ld_clean_scalar_certificate_backward:
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  ptr_discipline lo CS vs0 /\
  (!f. MEM f CS.ctx_functions ==> fn_ptr_ok P f) /\ opaque_use_ok fn /\
  MEM i.inst_opcode [MUL; Div; Mod; SDIV; SMOD; Exp; ADDMOD; MULMOD;
    SLT; SGT; ISZERO; AND; OR; XOR; NOT] /\ i.inst_outputs = [out] /\
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
  `!v. MEM (Var v) i.inst_operands ==> v IN {v | v IN V /\ ~retpc_var fn v}` by
    (rpt strip_tac >> simp[] >>
     irule ld_retpc_observable_operand >> simp[] >> qexists_tac `i` >>
     qpat_x_assum `MEM i.inst_opcode _` mp_tac >> simp[MEM] >>
     strip_tac >> simp[]) >>
  `?s'. step_inst fuelS CS i s = OK s' /\
    ld_owned_vars {v | v IN V /\ ~retpc_var fn v} E
      (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t'` by
    (irule ld_annotated_clean_scalar_backward >> rpt conj_tac >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  qexists_tac `s'` >>
  `!v. v IN V ==> (lookup_var v s' = NONE <=> lookup_var v t' = NONE)` by
    metis_tac[ld_scalar_defined] >>
  `!v. ld_owned_selection E (FLOOKUP (ld_step_prov AP AG L i) v)
      (FLOOKUP (ld_step_prov BP BH H i) v)` by
    (`ld_step_prov AP AG L i = ld_set_prov AG [out] NONE /\
      ld_step_prov BP BH H i = ld_set_prov BH [out] NONE` by
       metis_tac[ld_scalar_prov] >>
     simp[] >> irule ld_owned_set_selection >> simp[ld_owned_selection_def]) >>
  `ld_frame_bound t.vs_alloca_next H BP (ld_step_prov BP BH H i)` by
    (irule ld_frame_bound_step >> simp[]) >>
  `!owner bs sz. ld_live astk L AP (ld_step_prov AP AG L i) (owner,(bs,sz)) ==>
      owner IN live /\ lo <= bs` by metis_tac[ld_live_step_prov] >>
  `s' with vs_vars := s.vs_vars = s` by metis_tac[ld_scalar_restore] >>
  `t' with vs_vars := t.vs_vars = t` by metis_tac[ld_scalar_restore] >>
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
    metis_tac[ld_scalar_taint_nonvar] >>
  simp[ld_step_taint_bound] >>
  dxrule ld_vars_restore_normalize >> disch_then SUBST_ALL_TAC >>
  dxrule ld_vars_restore_normalize >> disch_then SUBST_ALL_TAC >>
  simp[] >> rpt conj_tac >> fs[]
QED

Theory lowerDloadNormalLoad
Ancestors
  lowerDloadLoadCertificate lowerDloadNormalData lowerDloadCoverageInvariant
  lowerDloadFrameCertificate lowerDloadSharedState lowerDloadOwnership
  lowerDloadAllocation lowerDloadPhaseBoundary lowerDloadNormalAlloca ptrDiscipline
  venomExecSemantics venomState venomInst finite_map pred_set list words

Theorem ld_load_normal_data_backward:
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn u0 s t0
    astk live keys d0 A suspended gstk f /\
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn inst s /\
  ptr_discipline lo CS vs0 /\
  (!fn. MEM fn CS.ctx_functions ==> fn_ptr_ok P fn) /\
  inst.inst_opcode = DLOAD /\ inst.inst_operands = [off] /\ inst.inst_outputs = [out] /\
  ~in_revert_forward fn s /\ dload_offset_ok CS fn inst s /\
  (!v. off = Var v ==> v IN U) /\
  a.inst_opcode = ALLOCA /\ a.inst_operands = [Lit 32w] /\ a.inst_outputs = [av] /\
  b.inst_opcode = ADD /\ b.inst_operands = [off;Label "code_end"] /\ b.inst_outputs = [bv] /\
  c.inst_opcode = CODECOPY /\ c.inst_operands = [Var av;Var bv;Lit 32w] /\ c.inst_outputs = [] /\
  d.inst_opcode = MLOAD /\ d.inst_operands = [Var av] /\ d.inst_outputs = [out] /\
  av <> bv /\ av NOTIN U /\ bv NOTIN U /\ av NOTIN V /\ bv NOTIN V /\
  out IN U /\ out IN V /\ av NOTIN FDOM BH /\ bv NOTIN FDOM BH /\
  ld_target_prefix CT [a;b;c;d] t0 u0 (SUC (SUC (SUC (SUC 0)))) t u /\
  code_layout_valid s /\
  eval_operand (Label "code_end") t0 =
    SOME (n2w (LENGTH s.vs_code - LENGTH s.vs_data_section)) /\
  a.inst_id IN keys /\ allocas_non_overlapping t0 /\ alloca_next_valid t0 /\
  t0.vs_alloca_next < dimword (:256) /\
  (a.inst_id NOTIN A ==> t0.vs_alloca_next + 32 < dimword (:256)) ==>
  ?z. step_inst fuel CS inst s = OK z /\
    ld_normal_data CS fn V U lo E L H AP BP
      (ld_set_prov AG [out] NONE)
      (ld_set_prov (ld_set_prov BH [bv] NONE) [out] NONE)
      (step_taint inst s z tn) u z t astk live keys d0 (a.inst_id INSERT A)
      suspended gstk f /\
    ld_step_prov AP AG L inst = ld_set_prov AG [out] NONE /\
    ld_step_prov BP (ld_step_prov BP (ld_step_prov BP (ld_step_prov BP BH H a) H b) H c) H d =
      ld_set_prov (ld_set_prov BH [bv] NONE) [out] NONE /\
    (z with vs_vars := s.vs_vars) = s /\
    (t with <|vs_memory := t0.vs_memory; vs_vars := t0.vs_vars;
              vs_allocas := t0.vs_allocas; vs_alloca_next := t0.vs_alloca_next;
              vs_inst_idx := t0.vs_inst_idx|>) = t0
Proof
  strip_tac >>
  drule ld_normal_data_frame >> strip_tac >>
  drule ld_normal_data_geometry >> strip_tac >>
  drule ld_normal_data_masks >> strip_tac >>
  drule ld_normal_data_memory >> strip_tac >>
  drule ld_frame_data_embedding >> strip_tac >>
  drule ld_frame_data_params >> strip_tac >>
  drule ld_frame_data_provenance >> strip_tac >>
  drule ld_frame_data_vars >> strip_tac >>
  drule ld_frame_data_definedness >> strip_tac >>
  drule ld_frame_data_shared >> strip_tac >>
  `t0.vs_code = s.vs_code` by
    (drule ld_shared_state_environment >> simp[]) >>
  qpat_assum `ld_annotated_reachable _ _ _ _ _ _ _ _ _ _ _`
    (mp_then Any mp_tac ld_load_certificate_backward) >>
  disch_then (fn th =>
    qpat_assum `ld_target_prefix _ _ _ _ _ _ _` (mp_then Any mp_tac th)) >>
  disch_then (fn th =>
    qpat_assum `ld_frame_embedding _ _ _ _ _` (mp_then Any mp_tac th)) >>
  disch_then (fn th =>
    qpat_assum `ld_owned_vars _ _ _ _ _ _ _ _` (mp_then Any mp_tac th)) >>
  disch_then (fn th =>
    qpat_assum `ld_alloc_account _ _ _ _ _` (mp_then Any mp_tac th)) >>
  disch_then (fn th =>
    qpat_assum `ptr_discipline _ _ _` (mp_then Any mp_tac th)) >>
  disch_then (fn th =>
    qpat_assum `!fn. MEM fn CS.ctx_functions ==> fn_ptr_ok P fn`
      (mp_then Any mp_tac th)) >>
  disch_then (fn th =>
    qpat_assum `LIST_REL (ld_owned_selection E) AP BP` (mp_then Any mp_tac th)) >>
  disch_then (fn th =>
    qpat_assum `!v. v IN V ==> _` (mp_then Any mp_tac th)) >>
  disch_then (fn th =>
    qpat_assum `ld_stack_bound _ gstk` (mp_then Any mp_tac th)) >>
  disch_then (fn th =>
    qpat_assum `allocas_from f t0` (mp_then Any mp_tac th)) >>
  disch_then (fn th =>
    qpat_assum `inst.inst_operands = [off]` (mp_then Any mp_tac th)) >>
  disch_then (fn th =>
    qpat_assum `inst.inst_outputs = [out]` (mp_then Any mp_tac th)) >>
  disch_then (fn th =>
    qpat_assum `a.inst_outputs = [av]` (mp_then Any mp_tac th)) >>
  disch_then (fn th =>
    qpat_assum `b.inst_outputs = [bv]` (mp_then Any mp_tac th)) >>
  disch_then (qspecl_then [`live`,`fuel`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `z` strip_assume_tac) >>
  qexists_tac `z` >> asm_rewrite_tac[] >>
  irule ld_normal_data_assemble >> asm_rewrite_tac[] >>
  rpt conj_tac
  >- suspend "storage"
  >- suspend "transient"
  >- suspend "support"
  >- metis_tac[]
  >- suspend "gas"
  >- suspend "params"
  >- suspend "allocas_floor"
  >- (qpat_x_assum `ld_alloc_account keys d0 (a.inst_id INSERT A) z t` mp_tac >>
      asm_rewrite_tac[]) >>
  simp[ld_frame_data_def] >> suspend "shared"
QED

Resume ld_load_normal_data_backward[storage]:
  drule ld_normal_data_companions >>
  qpat_assum `z with vs_vars := _ = s` (SUBST1_TAC o SYM) >>
  qpat_assum `t with <|vs_memory := _; vs_vars := _; vs_allocas := _;
    vs_alloca_next := _; vs_inst_idx := _|> = t0` (SUBST1_TAC o SYM) >> simp[]
QED

Resume ld_load_normal_data_backward[transient]:
  drule ld_normal_data_companions >>
  qpat_assum `z with vs_vars := _ = s` (SUBST1_TAC o SYM) >>
  qpat_assum `t with <|vs_memory := _; vs_vars := _; vs_allocas := _;
    vs_alloca_next := _; vs_inst_idx := _|> = t0` (SUBST1_TAC o SYM) >> simp[]
QED

Resume ld_load_normal_data_backward[gas]:
  drule ld_normal_data_companions >>
  qpat_assum `z with vs_vars := _ = s` (SUBST1_TAC o SYM) >>
  qpat_assum `t with <|vs_memory := _; vs_vars := _; vs_allocas := _;
    vs_alloca_next := _; vs_inst_idx := _|> = t0` (SUBST1_TAC o SYM) >> simp[]
QED

Resume ld_load_normal_data_backward[params]:
  drule ld_normal_data_envelope >>
  qpat_assum `z with vs_vars := _ = s` (SUBST1_TAC o SYM) >>
  qpat_assum `t with <|vs_memory := _; vs_vars := _; vs_allocas := _;
    vs_alloca_next := _; vs_inst_idx := _|> = t0` (SUBST1_TAC o SYM) >> simp[]
QED

Resume ld_load_normal_data_backward[support]:
  simp[ld_set_prov_def, FLOOKUP_DRESTRICT] >> rpt strip_tac >>
  first_x_assum irule >> goal_assum (drule_at Any)
QED

Resume ld_load_normal_data_backward[shared]:
  drule_all ld_load_source_effects >> disch_then (qspec_then `tn` strip_assume_tac) >>
  qpat_x_assum `ld_shared_state tn u0 s t0` mp_tac >>
  qpat_assum `z with vs_vars := _ = s` (SUBST1_TAC o SYM) >>
  qpat_assum `t with <|vs_memory := _; vs_vars := _; vs_allocas := _;
    vs_alloca_next := _; vs_inst_idx := _|> = t0` (SUBST1_TAC o SYM) >>
  simp[ld_shared_state_def] >> fs[]
QED

Resume ld_load_normal_data_backward[allocas_floor]:
  `!v. off = Var v ==> v <> av` by metis_tac[] >>
  qpat_assum `ld_target_prefix _ _ _ _ _ _ _`
    (mp_then Any (drule_all_then mp_tac) ld_load_completed_restoration) >>
  disch_then (qx_choose_then `t1` strip_assume_tac) >>
  qpat_x_assum `step_inst 0 CT a t0 = OK t1` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, eval_operand_def] >>
  disch_tac >>
  drule_all ld_alloca_frontier_floor >> strip_tac >>
  qpat_x_assum `allocas_from f t1` mp_tac >>
  qpat_x_assum `t with <|vs_vars := t1.vs_vars; vs_memory := t1.vs_memory;
    vs_inst_idx := t1.vs_inst_idx|> = t1` (SUBST1_TAC o SYM) >>
  simp[allocas_from_def]
QED

Finalise ld_load_normal_data_backward

Theory lowerDloadNormalExisting
Ancestors
  lowerDloadNormalTransport lowerDloadNormalData lowerDloadCoverageInvariant
  lowerDloadScalarProducer lowerDloadReachableScalarExecution
  lowerDloadReachableDiscipline lowerDloadOpaqueExecution lowerDloadMaskBounds
  lowerDloadOwnership lowerDloadPairedBoundary lowerDloadParamProducer
  lowerDloadVariableTransport ptrDiscipline venomExecSemantics venomState
  o1PassContract codegenRel contextCodegenRel finite_map pred_set list
  lowerDloadProvenanceSupport pointerConfinedDefs venomInst
  lowerDloadAssignProducer lowerDloadParameterEnvelope lowerDloadAffineProducer memLocDefs

(* A single annotation-step completion for variable-only families. Selection
   monotonicity supplies owner support even for an output copied from AP or L. *)
Theorem ld_normal_step_vars_complete:
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk f /\
  (s' with vs_vars := s.vs_vars) = s /\
  (t' with vs_vars := t.vs_vars) = t /\
  ld_owned_vars U E (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
    (step_taint i s s' tn) (step_taint i t t' un) s' t' /\
  (!v. v IN V ==> (lookup_var v s' = NONE <=> lookup_var v t' = NONE)) /\
  (!v. ld_owned_selection E (FLOOKUP (ld_step_prov AP AG L i) v)
    (FLOOKUP (ld_step_prov BP BH H i) v)) /\
  (step_taint i s s' tn).t_mem = tn.t_mem /\
  (step_taint i t t' un).t_mem = un.t_mem /\
  (step_taint i s s' tn).t_stor = tn.t_stor /\
  (step_taint i t t' un).t_stor = un.t_stor /\
  (step_taint i s s' tn).t_trans = tn.t_trans /\
  (step_taint i t t' un).t_trans = un.t_trans /\
  (step_taint i s s' tn).t_imm = tn.t_imm /\
  (step_taint i t t' un).t_imm = un.t_imm ==>
  ld_normal_data CS fn V U lo E L H AP BP
    (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
    (step_taint i s s' tn) (step_taint i t t' un) s' t'
    astk live keys d A suspended gstk f
Proof
  strip_tac >>
  `(!v. op_taint tn (Var v) SUBSET count 32) /\
   (!v. op_taint un (Var v) SUBSET count 32)` by
    (drule ld_normal_data_masks >> simp[]) >>
  `ld_frame_bound t.vs_alloca_next H BP BH` by
    (drule ld_normal_data_geometry >> strip_tac >> asm_rewrite_tac[]) >>
  `ld_frame_bound t.vs_alloca_next H BP (ld_step_prov BP BH H i)` by
    (irule ld_frame_bound_step >> simp[]) >>
  `t'.vs_alloca_next = t.vs_alloca_next` by
    (dxrule ld_vars_restore_normalize >> disch_then SUBST1_TAC >> simp[]) >>
  `!owner bs sz. ld_live astk L AP AG (owner,(bs,sz)) ==>
    owner IN live /\ lo <= bs` by
    (drule ld_normal_data_geometry >> strip_tac >> asm_rewrite_tac[]) >>
  `!owner bs sz. ld_live astk L AP (ld_step_prov AP AG L i) (owner,(bs,sz)) ==>
    owner IN live /\ lo <= bs` by metis_tac[ld_live_step_prov] >>
  drule ld_normal_data_vars_complete >> disch_then irule >>
  simp[ld_step_taint_bound] >> rpt strip_tac >>
  `ld_live astk L AP (ld_step_prov AP AG L i) (owner,(bs,sz))` by
    (simp[ld_live_def, ld_selected_def] >> metis_tac[]) >>
  metis_tac[]
QED

(* This uses the execution boundary below the legacy scalar certificate: that
   certificate's unconditional parameter-length premise is not valid at entry. *)
Theorem ld_normal_clean_scalar_backward:
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  ptr_discipline lo CS vs0 /\
  (!f. MEM f CS.ctx_functions ==> fn_ptr_ok P f) /\ opaque_use_ok fn /\
  U = {v | v IN V /\ ~retpc_var fn v} /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  MEM i.inst_opcode [MUL; Div; Mod; SDIV; SMOD; Exp; ADDMOD; MULMOD;
    SLT; SGT; ISZERO; AND; OR; XOR; NOT] /\ i.inst_outputs = [out] /\
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
  `MEM i (fn_insts fn)` by
    (drule ld_annotated_active_inst >>
     simp[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[EL_MEM]) >>
  `!v. MEM (Var v) i.inst_operands ==> v IN U` by
    (rpt strip_tac >> simp[] >>
     irule ld_retpc_observable_operand >> simp[] >> qexists_tac `i` >>
     qpat_x_assum `MEM i.inst_opcode _` mp_tac >> simp[MEM] >>
     strip_tac >> simp[]) >>
  `ld_owned_vars U E AG BH tn un s t` by
    (drule ld_normal_data_frame >> simp[ld_frame_data_def]) >>
  `?s'. step_inst fuel CS i s = OK s' /\
    ld_owned_vars U E (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t'` by
    (drule_all ld_annotated_clean_scalar_backward >> simp[]) >>
  qexists_tac `s'` >> simp[] >>
  suspend "completion"
QED

Resume ld_normal_clean_scalar_backward[completion]:
  `s' with vs_vars := s.vs_vars = s` by metis_tac[ld_scalar_restore] >>
  `t' with vs_vars := t.vs_vars = t` by metis_tac[ld_scalar_restore] >>
  qpat_x_assum `U = _` SUBST_ALL_TAC >>
  drule ld_normal_step_vars_complete >> disch_then irule >>
  simp[] >> suspend "fields"
QED

Resume ld_normal_clean_scalar_backward[fields]:
  `!v. ld_owned_selection E (FLOOKUP AG v) (FLOOKUP BH v)` by
    (drule ld_normal_data_frame >> simp[ld_frame_data_def]) >>
  `ld_step_prov AP AG L i = ld_set_prov AG [out] NONE /\
   ld_step_prov BP BH H i = ld_set_prov BH [out] NONE` by
    metis_tac[ld_scalar_prov] >>
  `!v. ld_owned_selection E (FLOOKUP (ld_step_prov AP AG L i) v)
    (FLOOKUP (ld_step_prov BP BH H i) v)` by
    (simp[] >> irule ld_owned_set_selection >> simp[ld_owned_selection_def]) >>
  `!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)` by
    (drule ld_normal_data_frame >> simp[ld_frame_data_def]) >>
  simp[] >> conj_tac >- metis_tac[ld_scalar_defined] >>
  metis_tac[ld_scalar_taint_nonvar]
QED

Finalise ld_normal_clean_scalar_backward

Theorem ld_normal_assign_backward:
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  U = {v | v IN V /\ ~retpc_var fn v} /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  i.inst_opcode = ASSIGN /\ i.inst_operands = [op] /\ i.inst_outputs = [out] /\
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk f /\
  step_inst fuel CT i t = OK t' ==>
  ?s'. step_inst fuel CS i s = OK s' /\
    ld_normal_data CS fn V U lo E L H AP BP
      (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t'
      astk live keys d A suspended gstk f
Proof
  strip_tac >> qpat_x_assum `U = _` SUBST_ALL_TAC >>
  `MEM i (fn_insts fn)` by
    (drule ld_annotated_active_inst >>
     simp[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[EL_MEM]) >>
  `ld_frame_data V {v | v IN V /\ ~retpc_var fn v} E L H AP BP AG BH tn un s t` by
    (drule ld_normal_data_frame >> simp[]) >>
  `ld_owned_vars {v | v IN V /\ ~retpc_var fn v} E AG BH tn un s t /\
   (!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
   (!v. ld_owned_selection E (FLOOKUP AG v) (FLOOKUP BH v))` by
    fs[ld_frame_data_def] >>
  `!v. op = Var v ==> v IN V` by metis_tac[MEM] >>
  `?x y s'. eval_operand op s = SOME x /\ eval_operand op t = SOME y /\
    s' = update_var out x s /\ t' = update_var out y t /\
    step_inst fuel CS i s = OK s' /\
    ld_owned_vars {v | v IN V /\ ~retpc_var fn v} E
      (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t' /\
    (!v. v IN V ==> (lookup_var v s' = NONE <=> lookup_var v t' = NONE))` by
    (irule ld_nonopaque_assign_backward >> rpt conj_tac >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[MEM]) >>
  qexists_tac `s'` >> simp[] >>
  drule ld_normal_step_vars_complete >> disch_then irule >> simp[] >>
  `!v. ld_owned_selection E (FLOOKUP (ld_step_prov AP AG L i) v)
    (FLOOKUP (ld_step_prov BP BH H i) v)` by
    (irule ld_assign_selection >> simp[]) >>
  simp[] >> gvs[] >> simp[ld_update_var_restore] >>
  `source_memory_write_ranges i s = [] /\ source_memory_write_ranges i t = []` by
    simp[source_memory_write_ranges_def] >>
  metis_tac[ld_singleton_update_taint_nonvar]
QED

Theorem ld_normal_param_backward:
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  i.inst_opcode = PARAM /\ i.inst_operands = [Lit idx] /\ i.inst_outputs = [out] /\
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
  `MEM i (fn_insts fn)` by
    (drule ld_annotated_active_inst >>
     simp[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[EL_MEM]) >>
  drule ld_normal_data_frame >> strip_tac >>
  drule ld_normal_data_envelope >> disch_then assume_tac >>
  drule_all ld_param_envelope_backward >> strip_tac >>
  qexists_tac `s'` >> (conj_tac >- asm_rewrite_tac[]) >>
  drule ld_normal_step_vars_complete >> disch_then irule >>
  `ld_owned_vars U E (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
    (step_taint i s s' tn) (step_taint i t t' un) s' t' /\
   (!v. v IN V ==> (lookup_var v s' = NONE <=> lookup_var v t' = NONE)) /\
   (!v. ld_owned_selection E (FLOOKUP (ld_step_prov AP AG L i) v)
    (FLOOKUP (ld_step_prov BP BH H i) v))` by
    gvs[ld_frame_data_def] >>
  simp[] >> gvs[] >> simp[ld_update_var_restore, ld_param_taint_nonvar]
QED

Theorem ld_normal_retpc_param_backward:
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  U = {v | v IN V /\ ~retpc_var fn v} /\
  i.inst_opcode = RETPC_PARAM /\ i.inst_operands = [Lit idx] /\ i.inst_outputs = [out] /\
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk f /\
  step_inst fuel CT i t = OK t' ==>
  ?s'. step_inst fuel CS i s = OK s' /\
    ld_normal_data CS fn V U lo E L H AP BP
      (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t'
      astk live keys d A suspended gstk f
Proof
  strip_tac >> qpat_x_assum `U = _` SUBST_ALL_TAC >>
  `MEM i (fn_insts fn)` by
    (drule ld_annotated_active_inst >>
     simp[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[EL_MEM]) >>
  `ld_owned_vars {v | v IN V /\ ~retpc_var fn v} E AG BH tn un s t /\
   (!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
   (!v. ld_owned_selection E (FLOOKUP AG v) (FLOOKUP BH v))` by
    (drule ld_normal_data_frame >> simp[ld_frame_data_def]) >>
  `?s'. step_inst fuel CS i s = OK s' /\
    ld_owned_vars {v | v IN V /\ ~retpc_var fn v} E
      (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t' /\
    (!v. v IN V ==> (lookup_var v s' = NONE <=> lookup_var v t' = NONE))` by
    (irule ld_retpc_param_backward >> rpt conj_tac >>
     goal_assum (drule_at Any) >> simp[]) >>
  qexists_tac `s'` >> (conj_tac >- asm_rewrite_tac[]) >>
  drule ld_normal_step_vars_complete >> disch_then irule >>
  `!v. ld_owned_selection E (FLOOKUP (ld_step_prov AP AG L i) v)
    (FLOOKUP (ld_step_prov BP BH H i) v)` by
    (simp[ld_step_prov_def, ld_out_prov_def] >>
     metis_tac[ld_owned_set_selection, ld_owned_selection_def]) >>
  simp[] >>
  qpat_x_assum `step_inst fuel CS i s = OK s'` mp_tac >>
  qpat_x_assum `step_inst fuel CT i t = OK t'` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def] >>
  ntac 2 (disch_then (SUBST_ALL_TAC o SYM)) >>
  `source_memory_write_ranges i s = [] /\ source_memory_write_ranges i t = []` by
    simp[source_memory_write_ranges_def] >>
  simp[ld_update_var_restore, ld_singleton_update_taint_nonvar]
QED

Theorem ld_normal_affine_backward:
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  ptr_discipline lo CS vs0 /\
  (!g. MEM g CS.ctx_functions ==> fn_ptr_ok P g) /\ opaque_use_ok fn /\
  U = {v | v IN V /\ ~retpc_var fn v} /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  (i.inst_opcode = ADD \/ i.inst_opcode = SUB) /\
  i.inst_operands = [a;b] /\ i.inst_outputs = [out] /\
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk f /\
  step_inst fuel CT i t = OK t' ==>
  ?s'. step_inst fuel CS i s = OK s' /\
    ld_normal_data CS fn V U lo E L H AP BP
      (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t'
      astk live keys d A suspended gstk f
Proof
  strip_tac >> qpat_x_assum `U = _` SUBST_ALL_TAC >>
  `MEM i (fn_insts fn)` by
    (drule ld_annotated_active_inst >>
     simp[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[EL_MEM]) >>
  `!v. a = Var v \/ b = Var v ==> v IN {v | v IN V /\ ~retpc_var fn v}` by
    (rpt strip_tac >> simp[] >>
     irule ld_retpc_observable_operand >> simp[] >> qexists_tac `i` >> simp[]) >>
  `ld_owned_vars {v | v IN V /\ ~retpc_var fn v} E AG BH tn un s t /\
   (!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
   (!v. ld_owned_selection E (FLOOKUP AG v) (FLOOKUP BH v))` by
    (drule ld_normal_data_frame >> simp[ld_frame_data_def]) >>
  `?s'. step_inst fuel CS i s = OK s' /\
    ld_owned_vars {v | v IN V /\ ~retpc_var fn v} E
      (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t'` by
    (irule ld_annotated_affine_backward >> simp[] >> fs[] >> metis_tac[]) >>
  qexists_tac `s'` >> (conj_tac >- asm_rewrite_tac[]) >>
  `s' with vs_vars := s.vs_vars = s` by metis_tac[ld_affine_restore] >>
  `t' with vs_vars := t.vs_vars = t` by metis_tac[ld_affine_restore] >>
  `!v. v IN V ==> (lookup_var v s' = NONE <=> lookup_var v t' = NONE)` by
    metis_tac[ld_affine_defined] >>
  `!v. ld_owned_selection E (FLOOKUP (ld_step_prov AP AG L i) v)
    (FLOOKUP (ld_step_prov BP BH H i) v)` by metis_tac[ld_affine_selection] >>
  drule ld_normal_step_vars_complete >> disch_then irule >> simp[] >>
  metis_tac[ld_affine_taint_nonvar]
QED

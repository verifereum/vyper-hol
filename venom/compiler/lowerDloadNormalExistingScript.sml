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
  lowerDloadShiftProducer lowerDloadCompareProducer lowerDloadOrdinaryExecution
  lowerDloadPureEffects lowerDloadMloadProducer lowerDloadOperand
  lowerDloadStoreCertificate lowerDloadCertificateProbe lowerDloadFrameCertificate
  lowerDloadEffectTransport lowerDloadByteStoreCertificate lowerDloadCopyCertificate

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

Theorem ld_normal_shift_backward:
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  ptr_discipline lo CS vs0 /\
  (!f. MEM f CS.ctx_functions ==> fn_ptr_ok P f) /\ opaque_use_ok fn /\
  U = {v | v IN V /\ ~retpc_var fn v} /\
  (!x. MEM (Var x) i.inst_operands ==> x IN V) /\
  MEM i.inst_opcode [SHL;SHR;SAR] /\
  i.inst_operands = [n;v] /\ i.inst_outputs = [out] /\
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
  `!x. n = Var x \/ v = Var x ==> x IN {v | v IN V /\ ~retpc_var fn v}` by
    (rpt strip_tac >> simp[] >>
     irule ld_retpc_observable_operand >> simp[] >> qexists_tac `i` >>
     qpat_x_assum `MEM i.inst_opcode _` mp_tac >> simp[MEM] >>
     strip_tac >> simp[] >> metis_tac[MEM]) >>
  `ld_owned_vars {v | v IN V /\ ~retpc_var fn v} E AG BH tn un s t /\
   (!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
   (!v. ld_owned_selection E (FLOOKUP AG v) (FLOOKUP BH v))` by
    (drule ld_normal_data_frame >> simp[ld_frame_data_def]) >>
  `?s'. step_inst fuel CS i s = OK s' /\
    ld_owned_vars {v | v IN V /\ ~retpc_var fn v} E
      (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t'` by
    (drule_all ld_annotated_shift_backward >> simp[]) >>
  qexists_tac `s'` >> (conj_tac >- asm_rewrite_tac[]) >>
  `?w. s' = update_var out w s` by metis_tac[ld_shift_update] >>
  `?w. t' = update_var out w t` by metis_tac[ld_shift_update] >>
  drule ld_normal_step_vars_complete >> disch_then irule >>
  simp[ld_update_var_restore] >>
  `!v. ld_owned_selection E (FLOOKUP (ld_step_prov AP AG L i) v)
    (FLOOKUP (ld_step_prov BP BH H i) v)` by
    (`ld_step_prov AP AG L i = ld_set_prov AG [out] NONE /\
      ld_step_prov BP BH H i = ld_set_prov BH [out] NONE` by
       (qpat_x_assum `MEM i.inst_opcode [SHL;SHR;SAR]` mp_tac >>
        simp[MEM] >> strip_tac >> simp[ld_step_prov_def, ld_out_prov_def]) >>
     simp[] >> irule ld_owned_set_selection >> simp[ld_owned_selection_def]) >>
  simp[] >> conj_tac
  >- (simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >> metis_tac[lookup_var_def]) >>
  metis_tac[ld_shift_taint_nonvar]
QED

Theorem ld_normal_compare_backward:
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  ptr_discipline lo CS vs0 /\ o1_ctx_shape CS /\
  mem_inv dload_headroom_ok CS vs0 /\
  callee_first names CS.ctx_functions /\ ld_stack_origin vs0 CS stk fn s0 /\
  LIST_REL (\A g. FINITE A /\
    CARD A <= LENGTH (FILTER (\i. i.inst_opcode = DLOAD) (fn_insts g)))
    (A::suspended) (fn::MAP (\f. f.cf_fn) stk) /\
  (!f. MEM f CS.ctx_functions ==> fn_ptr_ok P f) /\ opaque_use_ok fn /\
  U = {v | v IN V /\ ~retpc_var fn v} /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  MEM i.inst_opcode [EQ;LT;GT] /\
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
     irule ld_retpc_observable_operand >> simp[] >> qexists_tac `i` >>
     qpat_x_assum `MEM i.inst_opcode _` mp_tac >> simp[MEM] >>
     strip_tac >> simp[] >> metis_tac[MEM]) >>
  `ld_owned_vars {v | v IN V /\ ~retpc_var fn v} E AG BH tn un s t /\
   (!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
   (!v. ld_owned_selection E (FLOOKUP AG v) (FLOOKUP BH v))` by
    (drule ld_normal_data_frame >> simp[ld_frame_data_def]) >>
  `ld_alloc_account keys d A s t /\ d = 32 * SUM (MAP CARD suspended) /\
   (!owner bs sz. ld_live astk L AP AG (owner,(bs,sz)) ==> owner IN live) /\
   (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
      bs+sz <= s.vs_alloca_next /\ bt+sz <= t.vs_alloca_next)` by
    (drule ld_normal_data_geometry >> strip_tac >> rpt conj_tac >> metis_tac[]) >>
  `?s'. step_inst fuel CS i s = OK s' /\
    ld_owned_vars {v | v IN V /\ ~retpc_var fn v} E
      (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t'` by
    (drule_all ld_annotated_compare_backward >> simp[]) >>
  qexists_tac `s'` >> (conj_tac >- asm_rewrite_tac[]) >>
  suspend "completion"
QED

Resume ld_normal_compare_backward[completion]:
  `MEM i.inst_opcode [ADD;SUB;EQ;LT;GT;MUL;Div;Mod;SDIV;SMOD;Exp;
    ADDMOD;MULMOD;SLT;SGT;ISZERO;AND;OR;XOR;NOT]` by fs[MEM] >>
  `?w. s' = update_var out w s` by metis_tac[ld_pure_update] >>
  `?w. t' = update_var out w t` by metis_tac[ld_pure_update] >>
  drule ld_normal_step_vars_complete >> disch_then irule >>
  simp[ld_update_var_restore] >>
  `!v. ld_owned_selection E (FLOOKUP (ld_step_prov AP AG L i) v)
    (FLOOKUP (ld_step_prov BP BH H i) v)` by
    (`ld_step_prov AP AG L i = ld_set_prov AG [out] NONE /\
      ld_step_prov BP BH H i = ld_set_prov BH [out] NONE` by
       (qpat_x_assum `MEM i.inst_opcode [EQ;LT;GT]` mp_tac >>
        simp[MEM] >> strip_tac >> simp[ld_step_prov_def, ld_out_prov_def]) >>
     simp[] >> irule ld_owned_set_selection >> simp[ld_owned_selection_def]) >>
  simp[] >> conj_tac
  >- (simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >> metis_tac[lookup_var_def]) >>
  metis_tac[ld_pure_taint_nonvar]
QED

Finalise ld_normal_compare_backward

Theorem ld_normal_mload_backward:
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  ptr_discipline lo CS vs0 /\
  (!f. MEM f CS.ctx_functions ==> fn_ptr_ok P f) /\ opaque_use_ok fn /\
  U = {v | v IN V /\ ~retpc_var fn v} /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  i.inst_opcode = MLOAD /\ i.inst_operands = [op] /\ i.inst_outputs = [out] /\
  ~in_revert_forward fn s /\
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
  `!v. op = Var v ==> v IN {v | v IN V /\ ~retpc_var fn v}` by
    (rpt strip_tac >> simp[] >>
     irule ld_retpc_observable_operand >> simp[] >> qexists_tac `i` >>
     simp[] >> metis_tac[MEM]) >>
  `ld_owned_vars {v | v IN V /\ ~retpc_var fn v} E AG BH tn un s t /\
   (!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
   (!v. ld_owned_selection E (FLOOKUP AG v) (FLOOKUP BH v))` by
    (drule ld_normal_data_frame >> simp[ld_frame_data_def]) >>
  `access_ok lo (ld_erase AG) fn i s` by metis_tac[ld_annotated_access_ok] >>
  `taint_ok fn tn i s` by metis_tac[ld_annotated_taint_ok] >>
  `op_taint tn op = {}` by
    (irule ld_taint_operand_clean >> qexistsl_tac [`fn`,`i`,`s`] >> simp[]) >>
  `!v owner bs sz. FLOOKUP AG v = SOME(owner,(bs,sz)) ==>
    owner IN live /\ bs+sz < dimword(:256)` by
    (drule ld_normal_data_geometry >> strip_tac >> rpt strip_tac >>
     `?bt. ld_site_entry E owner bs bt sz` by
       (qpat_x_assum `!v. ld_owned_selection E _ _` (qspec_then `v` mp_tac) >>
        simp[ld_owned_selection_def] >> metis_tac[]) >> metis_tac[]) >>
  `!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
    bt+sz < dimword(:256)` by
    (drule ld_normal_data_geometry >> strip_tac >> metis_tac[]) >>
  drule ld_normal_data_memory >> disch_then assume_tac >>
  `?s'. step_inst fuel CS i s = OK s' /\
    ld_owned_vars {v | v IN V /\ ~retpc_var fn v} E
      (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t'` by
    (irule ld_mload_live_backward >> simp[] >>
     conj_tac >- metis_tac[] >>
     conj_tac >- (fs[] >> metis_tac[]) >>
     qexistsl_tac [`\a b. (a=b /\ a<lo) \/ ld_site_bytes E live a b`,
                    `fn`, `live`, `lo`] >> simp[] >> rpt conj_tac >> fs[]) >>
  qexists_tac `s'` >> (conj_tac >- asm_rewrite_tac[]) >>
  suspend "completion"
QED

Resume ld_normal_mload_backward[completion]:
  `?w. s' = update_var out w s` by metis_tac[ld_mload_update] >>
  `?w. t' = update_var out w t` by metis_tac[ld_mload_update] >>
  drule ld_normal_step_vars_complete >> disch_then irule >>
  simp[ld_update_var_restore] >>
  `!v. ld_owned_selection E (FLOOKUP (ld_step_prov AP AG L i) v)
    (FLOOKUP (ld_step_prov BP BH H i) v)` by
    (`ld_step_prov AP AG L i = ld_set_prov AG [out] NONE /\
      ld_step_prov BP BH H i = ld_set_prov BH [out] NONE` by
       simp[ld_step_prov_def, ld_out_prov_def] >>
     simp[] >> irule ld_owned_set_selection >> simp[ld_owned_selection_def]) >>
  simp[] >> conj_tac
  >- (simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >> metis_tac[lookup_var_def]) >>
  metis_tac[ld_mload_taint_nonvar]
QED

Finalise ld_normal_mload_backward

Theorem ld_normal_step_memory_complete:
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk f /\
  (s' with vs_memory := s.vs_memory) = s /\
  (t' with vs_memory := t.vs_memory) = t /\
  ld_owned_vars U E (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
    (step_taint i s s' tn) (step_taint i t t' un) s' t' /\
  (!v. ld_owned_selection E (FLOOKUP (ld_step_prov AP AG L i) v)
    (FLOOKUP (ld_step_prov BP BH H i) v)) /\
  ld_byte_rel (\a b. (a=b /\ a<lo) \/ ld_site_bytes E live a b)
    (step_taint i s s' tn).t_mem (step_taint i t t' un).t_mem
    (\a. read_memory a 1 s') (\b. read_memory b 1 t') /\
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
    (dxrule ld_memory_restore_normalize >> disch_then SUBST1_TAC >> simp[]) >>
  `!owner bs sz. ld_live astk L AP AG (owner,(bs,sz)) ==>
    owner IN live /\ lo <= bs` by
    (drule ld_normal_data_geometry >> strip_tac >> asm_rewrite_tac[]) >>
  `!owner bs sz. ld_live astk L AP (ld_step_prov AP AG L i) (owner,(bs,sz)) ==>
    owner IN live /\ lo <= bs` by metis_tac[ld_live_step_prov] >>
  drule ld_normal_data_memory_complete >> disch_then irule >>
  simp[ld_step_taint_bound] >> rpt strip_tac >>
  `ld_live astk L AP (ld_step_prov AP AG L i) (owner,(bs,sz))` by
    (simp[ld_live_def, ld_selected_def] >> metis_tac[]) >> metis_tac[]
QED

Theorem ld_normal_mstore_backward:
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  ptr_discipline lo CS vs0 /\
  (!f. MEM f CS.ctx_functions ==> fn_ptr_ok P f) /\ opaque_use_ok fn /\
  U = {v | v IN V /\ ~retpc_var fn v} /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  i.inst_opcode = MSTORE /\ i.inst_operands = [dst;value] /\ i.inst_outputs = [] /\
  ~in_revert_forward fn s /\
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
  `!v. MEM (Var v) [dst;value] ==> v IN {v | v IN V /\ ~retpc_var fn v}` by
    (rpt strip_tac >> `v IN V` by metis_tac[] >> simp[] >>
     irule ld_retpc_observable_operand >> simp[] >> qexists_tac `i` >> simp[] >> metis_tac[MEM]) >>
  drule ld_normal_data_frame >> simp[ld_frame_data_def] >> strip_tac >>
  drule ld_normal_data_geometry >> strip_tac >>
  drule ld_normal_data_masks >> strip_tac >>
  drule ld_normal_data_memory >> disch_then assume_tac >>
  `op_taint tn value SUBSET count 32 /\ op_taint un value SUBSET count 32` by
    (Cases_on `value` >> simp[op_taint_def] >> metis_tac[op_taint_def]) >>
  drule_all ld_reachable_mstore_state_backward >>
  disch_then (qspec_then `BP` (qx_choose_then `s'` (qx_choose_then `x`
    (qx_choose_then `v` (qx_choose_then `y` (qx_choose_then `w` strip_assume_tac)))))) >>
  qexists_tac `s'` >> (conj_tac >- asm_rewrite_tac[]) >>
  drule ld_normal_step_memory_complete >> disch_then irule >>
  simp[ld_empty_outputs_prov_tvar] >>
  simp[step_taint_def, store_taint_def, imm_taint_def, adopt_reset_def,
       mstore_def]
QED

Theorem ld_normal_mstore8_backward:
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  ptr_discipline lo CS vs0 /\
  (!f. MEM f CS.ctx_functions ==> fn_ptr_ok P f) /\ opaque_use_ok fn /\
  U = {v | v IN V /\ ~retpc_var fn v} /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  i.inst_opcode = MSTORE8 /\ i.inst_operands = [dst;value] /\ i.inst_outputs = [] /\
  ~in_revert_forward fn s /\
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
  `!v. MEM (Var v) [dst;value] ==> v IN {v | v IN V /\ ~retpc_var fn v}` by
    (rpt strip_tac >> `v IN V` by metis_tac[] >> simp[] >>
     irule ld_retpc_observable_operand >> simp[] >> qexists_tac `i` >> simp[] >> metis_tac[MEM]) >>
  drule ld_normal_data_frame >> simp[ld_frame_data_def] >> strip_tac >>
  drule ld_normal_data_geometry >> strip_tac >>
  drule ld_normal_data_masks >> strip_tac >>
  drule ld_normal_data_memory >> disch_then assume_tac >>
  drule_all ld_mstore8_certificate_backward >> strip_tac >>
  qexists_tac `s'` >> (conj_tac >- asm_rewrite_tac[]) >>
  drule ld_normal_step_memory_complete >> disch_then irule >> simp[] >>
  dxrule ld_memory_restore_normalize >> disch_then SUBST_ALL_TAC >>
  dxrule ld_memory_restore_normalize >> disch_then SUBST_ALL_TAC >>
  simp[step_taint_def, store_taint_def, imm_taint_def, adopt_reset_def]
QED

Theorem ld_normal_mcopy_backward:
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  ptr_discipline lo CS vs0 /\
  (!f. MEM f CS.ctx_functions ==> fn_ptr_ok P f) /\ opaque_use_ok fn /\
  U = {v | v IN V /\ ~retpc_var fn v} /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  i.inst_opcode = MCOPY /\ i.inst_operands = [dst;src;lenop] /\ i.inst_outputs = [] /\
  ~in_revert_forward fn s /\
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
  `!v. MEM (Var v) [dst;src;lenop] ==> v IN {v | v IN V /\ ~retpc_var fn v}` by
    (rpt strip_tac >> `v IN V` by metis_tac[] >> simp[] >>
     irule ld_retpc_observable_operand >> simp[] >> qexists_tac `i` >> simp[] >> metis_tac[MEM]) >>
  drule ld_normal_data_frame >> simp[ld_frame_data_def] >> strip_tac >>
  drule ld_normal_data_geometry >> strip_tac >>
  drule ld_normal_data_masks >> strip_tac >>
  drule ld_normal_data_memory >> disch_then assume_tac >>
  drule_all ld_mcopy_certificate_backward >> strip_tac >>
  qexists_tac `s'` >> (conj_tac >- asm_rewrite_tac[]) >>
  drule ld_normal_step_memory_complete >> disch_then irule >> simp[] >>
  dxrule ld_memory_restore_normalize >> disch_then SUBST_ALL_TAC >>
  dxrule ld_memory_restore_normalize >> disch_then SUBST_ALL_TAC >>
  simp[step_taint_def, store_taint_def, imm_taint_def, adopt_reset_def]
QED

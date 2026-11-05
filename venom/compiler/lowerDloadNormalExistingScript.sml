Theory lowerDloadNormalExisting
Ancestors
  lowerDloadNormalTransport lowerDloadNormalData lowerDloadCoverageInvariant
  lowerDloadScalarProducer lowerDloadReachableScalarExecution
  lowerDloadReachableDiscipline lowerDloadOpaqueExecution lowerDloadMaskBounds
  lowerDloadOwnership lowerDloadPairedBoundary lowerDloadParamProducer
  lowerDloadVariableTransport ptrDiscipline venomExecSemantics venomState
  o1PassContract codegenRel contextCodegenRel finite_map pred_set list
  lowerDloadProvenanceSupport pointerConfinedDefs venomInst

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
  drule ld_normal_data_vars_complete >> disch_then irule >>
  simp[ld_step_taint_bound] >>
  suspend "fields"
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
  `(!v. op_taint tn (Var v) SUBSET count 32) /\
   (!v. op_taint un (Var v) SUBSET count 32)` by
    (drule ld_normal_data_masks >> simp[]) >>
  `!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)` by
    (drule ld_normal_data_frame >> simp[ld_frame_data_def]) >>
  `ld_frame_bound t.vs_alloca_next H BP BH` by
    (drule ld_normal_data_geometry >> strip_tac >> asm_rewrite_tac[]) >>
  `ld_frame_bound t.vs_alloca_next H BP (ld_step_prov BP BH H i)` by
    (irule ld_frame_bound_step >> simp[]) >>
  `t'.vs_alloca_next = t.vs_alloca_next` by
    (dxrule ld_vars_restore_normalize >> disch_then SUBST1_TAC >> simp[]) >>
  `!v owner bs sz. FLOOKUP AG v = SOME(owner,(bs,sz)) ==> owner IN live` by
    (drule ld_normal_data_geometry >> strip_tac >> asm_rewrite_tac[]) >>
  `!owner bs sz. ld_live astk L AP AG (owner,(bs,sz)) ==>
    owner IN live /\ lo <= bs` by
    (drule ld_normal_data_geometry >> strip_tac >> asm_rewrite_tac[]) >>
  simp[ld_step_taint_bound] >>
  conj_tac >- (simp[ld_set_prov_def, FLOOKUP_DRESTRICT] >> metis_tac[]) >>
  conj_tac >- metis_tac[ld_scalar_defined] >>
  conj_tac >- metis_tac[ld_live_step_prov] >>
  metis_tac[ld_scalar_taint_nonvar]
QED

Finalise ld_normal_clean_scalar_backward

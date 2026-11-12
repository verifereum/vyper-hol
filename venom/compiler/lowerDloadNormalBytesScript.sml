Theory lowerDloadNormalBytes
Ancestors
  lowerDloadBytesProducer lowerDloadBytesEffects lowerDloadNormalData
  lowerDloadCoverageInvariant lowerDloadFrameCertificate lowerDloadSharedState
  lowerDloadOwnership lowerDloadAllocation ptrDiscipline venomState
  venomExecSemantics lowerDloadDefs finite_map pred_set list words

Theorem ld_bytes_normal_data_backward:
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn u0 s t0
    astk live keys d A suspended gstk f /\
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn inst s /\
  ptr_discipline lo CS vs0 /\
  (!fn. MEM fn CS.ctx_functions ==> fn_ptr_ok P fn) /\
  inst.inst_opcode = DLOADBYTES /\ inst.inst_operands = [dst;off;sz] /\
  inst.inst_outputs = [] /\ ~in_revert_forward fn s /\
  (!v. MEM (Var v) [dst;off;sz] ==> v IN U) /\
  a.inst_opcode = ADD /\ a.inst_operands = [off;Label "code_end"] /\
  a.inst_outputs = [av] /\
  c.inst_opcode = CODECOPY /\ c.inst_operands = [dst;Var av;sz] /\
  c.inst_outputs = [] /\
  (!v. dst = Var v ==> v <> av) /\ (!v. sz = Var v ==> v <> av) /\
  ld_target_prefix CT [a;c] t0 u0 (SUC (SUC 0)) t u /\
  code_layout_valid s /\
  eval_operand (Label "code_end") t0 =
    SOME (n2w (LENGTH s.vs_code - LENGTH s.vs_data_section)) /\
  dload_offset_ok CS fn inst s /\ av NOTIN U /\ av NOTIN V /\
  av NOTIN FDOM BH ==>
  ?z. step_inst fuel CS inst s = OK z /\
    ld_normal_data CS fn V U lo E L H AP BP AG BH (step_taint inst s z tn) u z t
      astk live keys d A suspended gstk f /\
    ld_step_prov AP AG L inst = AG /\
    ld_step_prov BP (ld_step_prov BP BH H a) H c = BH /\
    (z with vs_memory := s.vs_memory) = s /\
    (t with <|vs_memory := t0.vs_memory; vs_vars := t0.vs_vars;
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
  drule ld_shared_state_environment >> strip_tac >>
  `lo <= t0.vs_alloca_next` by decide_tac >>
  `t0.vs_code = s.vs_code` by simp[] >>
  `!owner bs bt size. owner IN live /\ ld_site_entry E owner bs bt size ==>
     bs+size <= s.vs_alloca_next /\ bt+size <= t0.vs_alloca_next` by
    metis_tac[] >>
  `!owner bs bt size. ld_live astk L AP AG (owner,(bs,size)) /\
     ld_site_entry E owner bs bt size ==>
     bt+size <= f \/ ?j. j NOTIN keys /\ FLOOKUP t0.vs_allocas j = SOME(bt,size)` by
    metis_tac[] >>
  drule_all ld_bytes_certificate_backward >>
  disch_then (qspec_then `fuel` (qx_choose_then `z` strip_assume_tac)) >>
  `z.vs_gas_readings = t.vs_gas_readings /\
   (!a. a <> z.vs_call_ctx.cc_address ==>
     (z.vs_accounts a).storage = (t.vs_accounts a).storage) /\
   (!a. a <> z.vs_call_ctx.cc_address ==> z.vs_transient a = t.vs_transient a)` by
    (drule ld_normal_data_companions >>
     qpat_assum `z with vs_memory := _ = s` (SUBST1_TAC o SYM) >>
     qpat_assum `t with <|vs_memory := _; vs_vars := _; vs_inst_idx := _|> = t0`
       (SUBST1_TAC o SYM) >> simp[]) >>
  drule ld_normal_data_envelope >> disch_then assume_tac >>
  qexists_tac `z` >> asm_rewrite_tac[] >>
  irule ld_normal_data_assemble >> asm_rewrite_tac[] >>
  rpt conj_tac
  >- (qpat_x_assum `allocas_from f t0` mp_tac >>
      qpat_assum `t with <|vs_memory := _; vs_vars := _; vs_inst_idx := _|> = t0`
        (SUBST1_TAC o SYM) >> simp[allocas_from_def])
  >- (qpat_x_assum `ld_alloc_account keys d A z t` mp_tac >> asm_rewrite_tac[]) >>
  simp[ld_frame_data_def] >>
  drule_all ld_bytes_structural_values >> strip_tac >>
  qpat_x_assum `ld_shared_state tn u0 s t0` mp_tac >>
  qpat_assum `z with vs_memory := _ = s` (SUBST1_TAC o SYM) >>
  qpat_assum `t with <|vs_memory := _; vs_vars := _; vs_inst_idx := _|> = t0`
    (SUBST1_TAC o SYM) >> simp[ld_shared_state_def]
QED

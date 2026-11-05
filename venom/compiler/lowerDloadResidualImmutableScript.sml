Theory lowerDloadResidualImmutable
Ancestors
  lowerDloadNormalExisting lowerDloadAccessClassification lowerDloadMemoryExecution
  lowerDloadNormalData lowerDloadCoverageInvariant lowerDloadVariableTransport lowerDloadMloadProducer
  lowerDloadPairedBoundary lowerDloadParamProducer lowerDloadOpaqueExecution
  lowerDloadProvenanceSupport lowerDloadReachableDiscipline
  lowerDloadOwnership ptrDiscipline memLocDefs venomExecSemantics venomState
  venomInst pointerConfinedDefs contextCodegenRel codegenRel o1PassContract
  finite_map pred_set list words

(* Immutable accesses cannot use a relocated pointer: source pointer discipline
   makes every variable operand scalar, and access discipline then forces the
   fixed positive-size range into the identity low-address region. *)
Theorem ld_annotated_immutable_scalar:
  (!f. MEM f CS.ctx_functions ==> fn_ptr_ok P f) /\
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  MEM i.inst_opcode [ILOAD;ISTORE] /\ MEM op i.inst_operands ==>
  ld_op_prov AG op = NONE
Proof
  strip_tac >>
  `MEM fn CS.ctx_functions` by metis_tac[ld_annotated_fn_member] >>
  `MEM i (fn_insts fn)` by
    (drule ld_annotated_active_inst >>
     simp[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[EL_MEM]) >>
  `fn_ptr_ok P fn` by metis_tac[] >>
  `!v. op = Var v ==> v NOTIN fn_pv P fn` by
    (qpat_x_assum `fn_ptr_ok P fn` mp_tac >>
     pure_rewrite_tac[fn_ptr_ok_def] >> strip_tac >>
     first_x_assum (qspec_then `i` mp_tac) >>
     simp[] >> qpat_x_assum `MEM i.inst_opcode _` mp_tac >>
     simp[MEM] >> metis_tac[]) >>
  drule_all ld_annotated_scalar_prov >> simp[]
QED

Theorem ld_immutable_scalar_access_low:
  MEM i.inst_opcode [ILOAD;ISTORE] /\
  ld_op_prov AG op = NONE /\
  (i.inst_opcode = ILOAD ==> i.inst_operands = [op]) /\
  (i.inst_opcode = ISTORE ==>
     i.inst_operands = [op;value] /\ IS_SOME (eval_operand value s)) /\
  eval_operand op s = SOME addr /\
  access_ok lo (ld_erase AG) fn i s /\ ~in_revert_forward fn s ==>
  w2n addr + 32 <= lo
Proof
  strip_tac >>
  qpat_x_assum `MEM i.inst_opcode _` mp_tac >> simp[MEM] >> strip_tac >>
  Cases_on `eval_operand value s` >> gvs[] >>
  fs[access_ok_def, source_memory_read_ranges_def, source_memory_write_ranges_def,
     mem_read_ops_def, mem_write_ops_def,
     fixed_source_write_range_def] >>
  spose_not_then assume_tac >>
  `lo < w2n addr + 32` by decide_tac >>
  gvs[ld_op_prov_def, ld_erase_lookup, op_prov_def] >>
  metis_tac[]
QED

(* ILOAD and MLOAD have exactly the same execution and taint effect.  The
   distinction in pointer discipline is handled before this boundary. *)
Theorem ld_iload_mload_effect:
  i.inst_opcode = ILOAD /\ i.inst_operands = [op] ==>
  step_inst fuel C (i with inst_opcode := MLOAD) s = step_inst fuel C i s /\
  ld_step_prov AP AG L (i with inst_opcode := MLOAD) = ld_step_prov AP AG L i /\
  step_taint (i with inst_opcode := MLOAD) s s' tn = step_taint i s s' tn /\
  access_ok lo P fn (i with inst_opcode := MLOAD) s = access_ok lo P fn i s
Proof
  strip_tac >> rpt conj_tac
  >- (simp[step_inst_non_invoke] >>
      pure_rewrite_tac[step_inst_base_def] >>
      asm_rewrite_tac[] >> simp[exec_read1_def])
  >- simp[ld_step_prov_def, ld_out_prov_def]
  >- simp[step_taint_def, out_taint_def, mem_taint_def, new_site_bytes_def,
          written_taint_def, step_writes_def, source_memory_write_ranges_def,
          store_taint_def, imm_taint_def, adopt_reset_def]
  >> simp[access_ok_def, source_memory_read_ranges_def,
          source_memory_write_ranges_def, mem_read_ops_def, mem_write_ops_def]
QED

Theorem ld_iload_low_backward:
  i.inst_opcode = ILOAD /\ i.inst_operands = [op] /\ i.inst_outputs = [out] /\
  ld_owned_vars U E AG BH tn un s t /\
  (!v. op = Var v ==> v IN U) /\ op_taint tn op = {} /\
  ld_op_prov AG op = NONE /\
  access_ok lo (ld_erase AG) fn i s /\ ~in_revert_forward fn s /\
  ld_byte_rel R tn.t_mem un.t_mem
    (\a. read_memory a 1 s) (\b. read_memory b 1 t) /\
  (!a. a < lo ==> R a a) /\
  step_inst fuel CT i t = OK t' ==>
  ?s'. step_inst fuel CS i s = OK s' /\
    ld_owned_vars U E (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t'
Proof
  strip_tac >>
  `!u C. step_inst fuel C i u = step_inst fuel CT i u` by
    (rpt gen_tac >> simp[step_inst_non_invoke] >>
     pure_rewrite_tac[step_inst_base_def] >> asm_rewrite_tac[] >> simp[]) >>
  `!u. step_inst fuel CT (i with inst_opcode := MLOAD) u = step_inst fuel CT i u` by
    metis_tac[ld_iload_mload_effect] >>
  `?s'. step_inst fuel CT (i with inst_opcode := MLOAD) s = OK s' /\
    ld_owned_vars U E (ld_step_prov AP AG L (i with inst_opcode := MLOAD))
      (ld_step_prov BP BH H (i with inst_opcode := MLOAD))
      (step_taint (i with inst_opcode := MLOAD) s s' tn)
      (step_taint (i with inst_opcode := MLOAD) t t' un) s' t'` by
    (irule ld_owned_mload_backward >> simp[] >> qexists_tac `R` >> simp[] >>
     rpt strip_tac >>
     `x = y` by (drule_all ld_owned_operand_clean >> simp[]) >> gvs[] >>
     `w2n x + 32 <= lo` by
       (irule ld_immutable_scalar_access_low >>
        goal_assum (drule_at (Pat `access_ok _ _ _ _ _`)) >> simp[]) >>
     first_x_assum irule >> decide_tac) >>
  qexists_tac `s'` >>
  gvs[] >> metis_tac[ld_iload_mload_effect]
QED

Theorem ld_normal_iload_backward:
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  ptr_discipline lo CS vs0 /\
  (!f. MEM f CS.ctx_functions ==> fn_ptr_ok P f) /\ opaque_use_ok fn /\
  U = {v | v IN V /\ ~retpc_var fn v} /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  i.inst_opcode = ILOAD /\ i.inst_operands = [op] /\ i.inst_outputs = [out] /\
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
  `ld_owned_vars {v | v IN V /\ ~retpc_var fn v} E AG BH tn un s t` by
    (drule ld_normal_data_frame >> simp[ld_frame_data_def]) >>
  `access_ok lo (ld_erase AG) fn i s` by metis_tac[ld_annotated_access_ok] >>
  `taint_ok fn tn i s` by metis_tac[ld_annotated_taint_ok] >>
  `op_taint tn op = {}` by
    (irule ld_taint_operand_clean >> qexistsl_tac [`fn`,`i`,`s`] >> simp[]) >>
  `ld_op_prov AG op = NONE` by
    (irule ld_annotated_immutable_scalar >>
     goal_assum (drule_at (Pat `ld_annotated_reachable _ _ _ _ _ _ _ _ _ _ _`)) >>
     simp[] >> metis_tac[]) >>
  drule ld_normal_data_memory >> disch_then assume_tac >>
  `?s'. step_inst fuel CS i s = OK s' /\
    ld_owned_vars {v | v IN V /\ ~retpc_var fn v} E
      (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t'` by
    (irule ld_iload_low_backward >> simp[] >>
     conj_tac >- metis_tac[] >>
     conj_tac >- (fs[] >> metis_tac[]) >>
     qexistsl_tac [`\a b. (a=b /\ a<lo) \/ ld_site_bytes E live a b`, `fn`, `lo`] >> simp[]) >>
  qexists_tac `s'` >> (conj_tac >- asm_rewrite_tac[]) >>
  suspend "completion"
QED

Resume ld_normal_iload_backward[completion]:
  `step_inst fuel CS (i with inst_opcode := MLOAD) s = OK s' /\
   step_inst fuel CT (i with inst_opcode := MLOAD) t = OK t'` by
    metis_tac[ld_iload_mload_effect] >>
  `?w. s' = update_var out w s` by
    (irule ld_mload_update >> goal_assum (drule_at Any) >> simp[]) >>
  `?w. t' = update_var out w t` by
    (irule ld_mload_update >> goal_assum (drule_at Any) >> simp[]) >>
  `!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)` by
    (drule ld_normal_data_frame >> simp[ld_frame_data_def]) >>
  `!v. ld_owned_selection E (FLOOKUP AG v) (FLOOKUP BH v)` by
    (drule ld_normal_data_frame >> simp[ld_frame_data_def]) >>
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
  simp[step_taint_def, mem_taint_def, new_site_bytes_def,
    written_taint_def, step_writes_def, source_memory_write_ranges_def,
    store_taint_def, imm_taint_def, adopt_reset_def, update_var_def,
    range_bytes_def, EXTENSION, FLOOKUP_DEF] >> simp[SF CONJ_ss]
QED

Finalise ld_normal_iload_backward

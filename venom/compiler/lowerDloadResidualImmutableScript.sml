Theory lowerDloadResidualImmutable
Ancestors
  lowerDloadNormalExisting lowerDloadAccessClassification lowerDloadMemoryExecution
  lowerDloadNormalData lowerDloadCoverageInvariant lowerDloadVariableTransport lowerDloadMloadProducer
  lowerDloadPairedBoundary lowerDloadParamProducer lowerDloadOpaqueExecution
  lowerDloadStoreExecution lowerDloadStoreProducer lowerDloadImmutableWrite
  lowerDloadSharedState lowerDloadMaskedStorage lowerDloadAllocation lowerDloadRelocation
  lowerDloadCertificateProbe lowerDloadFrameCertificate lowerDloadMaskBounds lowerDloadOperand
  lowerDloadLifetime
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

Theorem ld_istore_memory_projection:
  i.inst_opcode = ISTORE /\ i.inst_operands = [dst;value] /\
  eval_operand dst s = SOME off /\ eval_operand value s = SOME x ==>
  (step_taint i s (istore (w2n off) x s) tn).t_mem =
    (step_taint (i with inst_opcode := MSTORE) s (mstore (w2n off) x s) tn).t_mem /\
  (!a n. read_memory a n (istore (w2n off) x s) =
    read_memory a n (mstore (w2n off) x s))
Proof
  simp[step_taint_def, mem_taint_def, new_site_bytes_def, written_taint_def,
    step_writes_def, source_memory_write_ranges_def, fixed_source_write_range_def,
    istore_def, mstore_def, read_memory_def]
QED

Theorem ld_istore_byte_rel:
  i.inst_opcode = ISTORE /\ i.inst_operands = [dst;value] /\ i.inst_outputs = [] /\
  eval_operand dst s = SOME off /\ eval_operand dst t = SOME off /\
  eval_operand value s = SOME x /\ eval_operand value t = SOME y /\
  op_taint tn value SUBSET count 32 /\ op_taint un value SUBSET count 32 /\
  ld_mask_word (op_taint tn value) (op_taint un value) x y /\
  ld_byte_rel R tn.t_mem un.t_mem (\a. read_memory a 1 s) (\b. read_memory b 1 t) /\
  (!a b. R a b ==> ((w2n off <= a /\ a < w2n off+32) <=>
                       (w2n off <= b /\ b < w2n off+32))) /\
  (!a b. R a b /\ w2n off <= a /\ a < w2n off+32 ==> a=b) ==>
  ld_byte_rel R
    (step_taint i s (istore (w2n off) x s) tn).t_mem
    (step_taint i t (istore (w2n off) y t) un).t_mem
    (\a. read_memory a 1 (istore (w2n off) x s))
    (\b. read_memory b 1 (istore (w2n off) y t))
Proof
  strip_tac >>
  `step_inst 0 C (i with inst_opcode := MSTORE) t = OK (mstore (w2n off) y t)` by
    (simp[step_inst_non_invoke] >> pure_rewrite_tac[step_inst_base_def] >>
     simp[exec_write2_def]) >>
  `!s'. step_inst 0 C (i with inst_opcode := MSTORE) s = OK s' ==>
     s' = mstore (w2n off) x s` by
    (simp[step_inst_non_invoke] >> pure_rewrite_tac[step_inst_base_def] >>
     simp[exec_write2_def]) >>
  drule_at (Pat `step_inst _ _ _ _ = OK _`) ld_mstore_memory_backward >> simp[] >>
  disch_then (drule_at (Pat `ld_byte_rel _ _ _ _ _`)) >> simp[] >>
  impl_tac >- (simp[] >> metis_tac[]) >>
  strip_tac >> gvs[] >>
  simp[ld_istore_memory_projection] >>
  qpat_x_assum `ld_byte_rel R tn.t_mem un.t_mem _ _` kall_tac >>
  gvs[ld_byte_rel_def, istore_def, read_memory_def] >> metis_tac[]
QED

(* ISTORE has a two-field footprint. Shared immutable bookkeeping is supplied
   separately from the byte relation; neither is inferred from the other. *)
Theorem ld_normal_istore_complete:
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk f /\
  i.inst_outputs = [] /\
  ld_shared_state
    (step_taint i s (istore p x s) tn) (step_taint i t (istore q y t) un)
    (istore p x s) (istore q y t) /\
  ld_byte_rel (\a b. (a=b /\ a<lo) \/ ld_site_bytes E live a b)
    (step_taint i s (istore p x s) tn).t_mem
    (step_taint i t (istore q y t) un).t_mem
    (\a. read_memory a 1 (istore p x s)) (\b. read_memory b 1 (istore q y t)) ==>
  ld_normal_data CS fn V U lo E L H AP BP
    (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
    (step_taint i s (istore p x s) tn) (step_taint i t (istore q y t) un)
    (istore p x s) (istore q y t) astk live keys d A suspended gstk f
Proof
  strip_tac >>
  `ld_frame_data V U E L H AP BP AG BH tn un s t` by
    metis_tac[ld_normal_data_frame] >>
  `ld_owned_vars U E AG BH
    (step_taint i s (istore p x s) tn) (step_taint i t (istore q y t) un)
    (istore p x s) (istore q y t)` by
    (irule (iffRL ld_owned_vars_tvar_cong) >>
     simp[ld_empty_outputs_prov_tvar] >> qexistsl_tac [`tn`,`un`] >>
     gvs[ld_frame_data_def, ld_owned_vars_def, istore_def, mstore_def, lookup_var_def]) >>
  `ld_frame_data V U E L H AP BP AG BH
    (step_taint i s (istore p x s) tn) (step_taint i t (istore q y t) un)
    (istore p x s) (istore q y t)` by
    (fs[ld_frame_data_def] >>
     simp[ld_frame_embedding_def, istore_def, mstore_def, lookup_var_def] >>
     fs[ld_frame_embedding_def, lookup_var_def] >> asm_rewrite_tac[]) >>
  `((step_taint i t (istore q y t) un).t_stor SUBSET
      (step_taint i s (istore p x s) tn).t_stor) /\
   ((step_taint i t (istore q y t) un).t_trans SUBSET
      (step_taint i s (istore p x s) tn).t_trans) /\
   ((step_taint i t (istore q y t) un).t_imm SUBSET
      (step_taint i s (istore p x s) tn).t_imm)` by
    fs[ld_shared_state_def] >>
  gvs[ld_normal_data_def, ld_empty_outputs_prov_tvar,
      ld_alloc_account_def, istore_def, mstore_def, allocas_from_def, op_taint_def] >>
  asm_rewrite_tac[]
QED

Theorem ld_istore_owned_backward:
  i.inst_opcode = ISTORE /\ i.inst_operands = [dst;value] /\
  ld_owned_vars U E AG BH tn un s t /\
  (!v. MEM (Var v) [dst;value] ==> v IN U) /\
  ld_op_prov AG dst = NONE /\ ld_op_prov AG value = NONE /\
  op_taint tn dst = {} /\ step_inst fuel CT i t = OK t' ==>
  ?off x y. eval_operand dst s = SOME off /\ eval_operand dst t = SOME off /\
    eval_operand value s = SOME x /\ eval_operand value t = SOME y /\
    ld_mask_word (op_taint tn value) (op_taint un value) x y /\
    step_inst fuel CS i s = OK (istore (w2n off) x s) /\
    t' = istore (w2n off) y t
Proof
  strip_tac >>
  `eval_operand dst s = eval_operand dst t` by
    (irule ld_owned_operand_clean >>
     goal_assum (drule_at (Pat `ld_owned_vars _ _ _ _ _ _ _ _`)) >> simp[] >> metis_tac[MEM]) >>
  qpat_x_assum `step_inst fuel CT i t = OK t'` mp_tac >>
  simp[Once step_inst_non_invoke, SimpLHS] >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[] >> simp[exec_write2_def, AllCaseEqs()] >> strip_tac >>
  rename1 `eval_operand dst t = SOME off` >>
  rename1 `eval_operand value t = SOME y` >>
  `eval_operand value s <> NONE` by
    (drule ld_owned_operand_defined >>
     disch_then (qspec_then `value` mp_tac) >> simp[] >> metis_tac[MEM]) >>
  Cases_on `eval_operand value s` >> gvs[] >>
  rename1 `eval_operand value s = SOME x` >>
  `ld_owned_value E NONE (ld_op_prov BH value)
    (op_taint tn value) (op_taint un value) x y` by
    (drule_at (Pat `eval_operand _ _ = SOME _`) ld_owned_operand_value >>
     simp[] >> metis_tac[MEM]) >>
  `ld_mask_word (op_taint tn value) (op_taint un value) x y` by
    fs[ld_owned_value_def] >>
  simp[] >>
  simp[step_inst_non_invoke] >> pure_rewrite_tac[step_inst_base_def] >>
  simp[exec_write2_def]
QED

Theorem ld_normal_istore_backward:
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  ptr_discipline lo CS vs0 /\
  (!f. MEM f CS.ctx_functions ==> fn_ptr_ok P f) /\ opaque_use_ok fn /\
  U = {v | v IN V /\ ~retpc_var fn v} /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  i.inst_opcode = ISTORE /\ i.inst_operands = [dst;value] /\ i.inst_outputs = [] /\
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
    (rpt strip_tac >> simp[] >> conj_tac >- metis_tac[] >>
     irule ld_retpc_observable_operand >> simp[] >> qexists_tac `i` >>
     simp[] >> metis_tac[MEM]) >>
  `ld_owned_vars {v | v IN V /\ ~retpc_var fn v} E AG BH tn un s t /\
   ld_shared_state tn un s t` by
    (drule ld_normal_data_frame >> simp[ld_frame_data_def]) >>
  `access_ok lo (ld_erase AG) fn i s` by metis_tac[ld_annotated_access_ok] >>
  `taint_ok fn tn i s` by metis_tac[ld_annotated_taint_ok] >>
  `op_taint tn dst = {}` by
    (irule ld_taint_store_address_clean >> qexistsl_tac [`fn`,`i`,`s`,`value`] >> simp[]) >>
  `!op. MEM op [dst;value] ==> ld_op_prov AG op = NONE` by
    (rpt strip_tac >> irule ld_annotated_immutable_scalar >>
     goal_assum (drule_at (Pat `ld_annotated_reachable _ _ _ _ _ _ _ _ _ _ _`)) >>
     simp[] >> metis_tac[MEM]) >>
  `?off x y. eval_operand dst s = SOME off /\ eval_operand dst t = SOME off /\
    eval_operand value s = SOME x /\ eval_operand value t = SOME y /\
    ld_mask_word (op_taint tn value) (op_taint un value) x y /\
    step_inst fuel CS i s = OK (istore (w2n off) x s) /\
    t' = istore (w2n off) y t` by
    (irule ld_istore_owned_backward >> simp[] >>
     conj_tac >- metis_tac[] >>
     goal_assum (drule_at (Pat `ld_owned_vars _ _ _ _ _ _ _ _`)) >> simp[]) >>
  qexists_tac `istore (w2n off) x s` >> (conj_tac >- asm_rewrite_tac[]) >>
  gvs[] >> irule ld_normal_istore_complete >> simp[] >>
  conj_tac >- suspend "shared" >> suspend "bytes"
QED

Resume ld_normal_istore_backward[shared]:
  `word_agree_except (op_taint tn value INTER count 32) x y /\
   op_taint un value SUBSET op_taint tn value` by
    (fs[ld_mask_word_def, word_agree_except_def] >> metis_tac[]) >>
  drule_all ld_shared_istore >>
  disch_then (qspec_then `w2n off` mp_tac) >>
  simp[step_taint_def, imm_taint_def, store_taint_def, adopt_reset_def,
       ld_shared_state_def]
QED

Resume ld_normal_istore_backward[bytes]:
  `w2n off + 32 <= lo` by
    (irule ld_immutable_scalar_access_low >>
     goal_assum (drule_at (Pat `access_ok _ _ _ _ _`)) >> simp[]) >>
  `op_taint tn value SUBSET count 32 /\ op_taint un value SUBSET count 32` by
    (drule ld_normal_data_masks >> strip_tac >>
     conj_tac >> irule ld_op_taint_bound >> simp[]) >>
  `(!a b. ((a=b /\ a<lo) \/ ld_site_bytes E live a b) ==>
      ((w2n off <= a /\ a < w2n off+32) <=> (w2n off <= b /\ b < w2n off+32))) /\
   (!a b. ((a=b /\ a<lo) \/ ld_site_bytes E live a b) /\
      w2n off <= a /\ a < w2n off+32 ==> a=b)` by
    (drule ld_normal_data_geometry >> strip_tac >>
     `(!a b. ((a=b /\ a<lo) \/ ld_site_bytes E live a b) ==>
        ((w2n off <= a /\ a < w2n off+32) <=> (w2n off <= b /\ b < w2n off+32))) /\
      (!a b. ((a=b /\ a<lo) \/ ld_site_bytes E live a b) /\
        w2n off <= a /\ a < w2n off+32 ==> a-w2n off=b-w2n off)` by
       (irule ld_fixed_live_write_footprint >> simp[] >> metis_tac[]) >>
     conj_tac >- metis_tac[] >>
     rpt strip_tac >>
     `w2n off <= b /\ b < w2n off + 32` by metis_tac[] >>
     `a - w2n off = b - w2n off` by metis_tac[] >>
     decide_tac) >>
  irule ld_istore_byte_rel >> simp[] >>
  drule ld_normal_data_memory >> simp[] >> metis_tac[]
QED

Finalise ld_normal_istore_backward

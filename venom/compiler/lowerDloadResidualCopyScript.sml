Theory lowerDloadResidualCopy
Ancestors
  lowerDloadNormalExisting lowerDloadNormalTransport lowerDloadCleanCopy
  lowerDloadSharedState lowerDloadMemoryExecution lowerDloadCopyCertificate
  lowerDloadEffectTransport venomExecSemantics venomState ptrDiscipline
  list words pred_set vfmState venomInst memLocDefs codegenRel
  lowerDloadProvenanceSupport lowerDloadReachableDiscipline
  lowerDloadPairedBoundary pointerConfinedDefs contextCodegenRel o1PassContract
  lowerDloadNormalData lowerDloadCoverageInvariant lowerDloadOpaqueExecution
  lowerDloadStoreProducer lowerDloadAccessClassification lowerDloadOwnership
  lowerDloadCertificateProbe lowerDloadTargetGeometry lowerDloadOperand

(* The payload is obtained from the shared environment, never assumed equal. *)
Theorem ld_payload_copy_execution_backward:
  MEM i.inst_opcode [CALLDATACOPY; CODECOPY; RETURNDATACOPY; EXTCODECOPY] /\
  i.inst_operands = (if i.inst_opcode = EXTCODECOPY then [addr;dst;off;sz]
                     else [dst;off;sz]) /\
  ld_shared_state tn un s t /\
  eval_operand dst s = SOME p /\ eval_operand dst t = SOME q /\
  eval_operand off s = SOME r /\ eval_operand off t = SOME r /\
  eval_operand sz s = SOME n /\ eval_operand sz t = SOME n /\
  (i.inst_opcode = EXTCODECOPY ==>
    eval_operand addr s = SOME a /\ eval_operand addr t = SOME a) /\
  step_inst fuelT CT i t = OK t' ==>
  ?bs. LENGTH bs = w2n n /\
    step_inst fuelS CS i s = OK (write_memory_with_expansion (w2n p) bs s) /\
    t' = write_memory_with_expansion (w2n q) bs t
Proof
  strip_tac >>
  drule ld_shared_state_environment >> strip_tac >>
  `!a. (lookup_account a s.vs_accounts).code =
       (lookup_account a t.vs_accounts).code` by
    (drule ld_shared_state_nonstorage >> strip_tac >> gen_tac >>
     first_x_assum (qspec_then `a'` mp_tac) >>
     simp[lookup_account_def] >> disch_tac >>
     qsuff_tac `(s.vs_accounts a' with storage := (t.vs_accounts a').storage).code =
       (t.vs_accounts a').code` >- simp[] >> AP_TERM_TAC >> simp[]) >>
  qpat_x_assum `step_inst fuelT CT i t = OK t'` mp_tac >>
  qpat_x_assum `MEM i.inst_opcode _` mp_tac >> simp[MEM] >> strip_tac >>
  simp[Once step_inst_non_invoke, SimpLHS] >>
  asm_rewrite_tac[step_inst_base_def, opcode_case_def] >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  simp[Once step_inst_non_invoke] >>
  asm_rewrite_tac[step_inst_base_def, opcode_case_def] >>
  simp[] >>
  qmatch_goalsub_abbrev_tac `write_memory_with_expansion (w2n p) payload s` >>
  qexists_tac `payload` >> simp[Abbr `payload`, LENGTH_TAKE]
QED

Theorem ld_payload_copy_taint:
  MEM i.inst_opcode [CALLDATACOPY; CODECOPY; RETURNDATACOPY; EXTCODECOPY] /\
  i.inst_operands = (if i.inst_opcode = EXTCODECOPY then [addr;dst;off;sz]
                     else [dst;off;sz]) /\
  eval_operand dst s = SOME p /\ eval_operand sz s = SOME n /\
  eval_operand off s = SOME r /\
  (i.inst_opcode = EXTCODECOPY ==> eval_operand addr s = SOME a) /\
  (s' with vs_memory := s.vs_memory) = s ==>
  (step_taint i s s' tn).t_mem =
    tn.t_mem DIFF {a | w2n p <= a /\ a < w2n p + w2n n} /\
  (step_taint i s s' tn).t_stor = tn.t_stor /\
  (step_taint i s s' tn).t_trans = tn.t_trans /\
  (step_taint i s s' tn).t_imm = tn.t_imm
Proof
  strip_tac >> dxrule ld_memory_restore_normalize >> disch_then SUBST_ALL_TAC >>
  qpat_x_assum `MEM i.inst_opcode _` mp_tac >> simp[MEM] >> strip_tac >>
  gvs[step_taint_def, store_taint_def, imm_taint_def, adopt_reset_def,
      mem_taint_def, new_site_bytes_def, step_writes_def,
      source_memory_write_ranges_def, sized_source_write_range_def,
      written_taint_def, range_bytes_def, finite_mapTheory.FLOOKUP_DEF,
      EXTENSION, SF CONJ_ss] >> metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem ld_payload_scalars_not_pointer:
  ptr_use_ok P pv i /\
  MEM i.inst_opcode [CALLDATACOPY; CODECOPY; RETURNDATACOPY; EXTCODECOPY] /\
  i.inst_operands = (if i.inst_opcode = EXTCODECOPY then [addr;dst;off;sz]
                     else [dst;off;sz]) ==>
  !op v. MEM op (if i.inst_opcode = EXTCODECOPY then [addr;off;sz]
                else [off;sz]) /\ op = Var v ==> v NOTIN pv
Proof
  strip_tac >>
  qpat_x_assum `MEM i.inst_opcode _` mp_tac >> simp[MEM] >> strip_tac >>
  gvs[] >> rpt strip_tac >> gvs[] >>
  qpat_x_assum `ptr_use_ok P pv i` mp_tac >>
  pure_rewrite_tac[ptr_use_ok_def] >>
  disch_then (mp_tac o CONJUNCT2) >> disch_then (qspec_then `v` mp_tac) >>
  simp[is_pointer_preserving_op_def, mem_write_ops_def, mem_read_ops_def] >>
  Cases_on `dst = Var v` >> simp[] >>
  Cases_on `off = Var v` >> simp[] >>
  Cases_on `sz = Var v` >> simp[] >>
  Cases_on `addr = Var v` >> simp[]
QED

Theorem ld_annotated_payload_operands:
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  ptr_discipline lo CS vs0 /\
  (!f. MEM f CS.ctx_functions ==> fn_ptr_ok P f) /\
  MEM i.inst_opcode [CALLDATACOPY; CODECOPY; RETURNDATACOPY; EXTCODECOPY] /\
  i.inst_operands = (if i.inst_opcode = EXTCODECOPY then [addr;dst;off;sz]
                     else [dst;off;sz]) /\ ~in_revert_forward fn s /\
  ld_owned_vars U E AG BH tn un s t /\
  (!v. MEM (Var v) i.inst_operands ==> v IN U) ==>
  (!op. MEM op i.inst_operands ==> op_taint tn op = {}) /\
  (!op. MEM op (if i.inst_opcode = EXTCODECOPY then [addr;off;sz]
                else [off;sz]) ==> eval_operand op s = eval_operand op t)
Proof
  strip_tac >>
  `MEM fn CS.ctx_functions` by metis_tac[ld_annotated_fn_member] >>
  `MEM i (fn_insts fn)` by
    (drule ld_annotated_active_inst >>
     simp[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[EL_MEM]) >>
  `ptr_use_ok P (fn_pv P fn) i` by metis_tac[fn_ptr_ok_def] >>
  `!op v. MEM op (if i.inst_opcode = EXTCODECOPY then [addr;off;sz]
                 else [off;sz]) /\ op = Var v ==> v NOTIN fn_pv P fn` by
    (mp_tac (Q.INST [`pv` |-> `fn_pv P fn`] ld_payload_scalars_not_pointer) >>
     simp[]) >>
  drule_all ld_annotated_taint_ok >> strip_tac >>
  `!op. MEM op i.inst_operands ==> op_taint tn op = {}` by
    (rpt strip_tac >> irule ld_taint_operand_clean >>
     goal_assum (drule_at Any) >>
     qpat_x_assum `MEM i.inst_opcode _` mp_tac >> simp[MEM] >>
     strip_tac >> simp[] >> metis_tac[]) >>
  conj_tac >- asm_rewrite_tac[] >> rpt strip_tac >>
  `MEM op i.inst_operands` by
    (Cases_on `i.inst_opcode = EXTCODECOPY` >> gvs[MEM] >> metis_tac[]) >>
  `ld_op_prov AG op = NONE` by metis_tac[ld_annotated_scalar_prov] >>
  drule ld_owned_operand_clean >> disch_then (qspec_then `op` mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem ld_normal_payload_copy_backward:
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  ptr_discipline lo CS vs0 /\
  (!g. MEM g CS.ctx_functions ==> fn_ptr_ok P g) /\ opaque_use_ok fn /\
  U = {v | v IN V /\ ~retpc_var fn v} /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  MEM i.inst_opcode [CALLDATACOPY; CODECOPY; RETURNDATACOPY; EXTCODECOPY] /\
  i.inst_operands = (if i.inst_opcode = EXTCODECOPY then [addr;dst;off;sz]
                     else [dst;off;sz]) /\ i.inst_outputs = [] /\
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
  strip_tac >>
  `MEM i (fn_insts fn)` by
    (drule ld_annotated_active_inst >>
     simp[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[EL_MEM]) >>
  `!v. MEM (Var v) i.inst_operands ==> v IN U` by
    (rpt strip_tac >> simp[] >>
     irule ld_retpc_observable_operand >> simp[] >> qexists_tac `i` >>
     simp[] >> qpat_x_assum `MEM i.inst_opcode _` mp_tac >> simp[MEM] >>
     strip_tac >> simp[]) >>
  drule ld_normal_data_frame >> simp[ld_frame_data_def] >> strip_tac >>
  drule ld_normal_data_geometry >> strip_tac >>
  `ld_owned_vars U E AG BH tn un s t` by metis_tac[] >>
  mp_tac ld_annotated_payload_operands >> asm_rewrite_tac[] >> strip_tac >>
  `?q r n a. eval_operand dst t = SOME q /\ eval_operand off t = SOME r /\
    eval_operand sz t = SOME n /\
    (i.inst_opcode = EXTCODECOPY ==> eval_operand addr t = SOME a)` by
    suspend "target_operands" >>
  `eval_operand off s = SOME r /\ eval_operand sz s = SOME n /\
    (i.inst_opcode = EXTCODECOPY ==> eval_operand addr s = SOME a)` by
    (Cases_on `i.inst_opcode = EXTCODECOPY` >> fs[MEM] >> metis_tac[]) >>
  `?p. eval_operand dst s = SOME p` by
    (drule ld_owned_operand_defined >> disch_then (qspec_then `dst` mp_tac) >>
     Cases_on `i.inst_opcode = EXTCODECOPY` >> fs[MEM] >>
     Cases_on `eval_operand dst s` >> gvs[]) >>
  `?bs. LENGTH bs = w2n n /\
    step_inst fuel CS i s = OK (write_memory_with_expansion (w2n p) bs s) /\
    t' = write_memory_with_expansion (w2n q) bs t` by
    (irule ld_payload_copy_execution_backward >>
     conj_tac >- metis_tac[] >>
     conj_tac >- (qexistsl_tac [`a`,`addr`,`dst`,`off`,`r`,`sz`] >> simp[]) >>
     simp[] >> metis_tac[]) >>
  `(!a b. ((a=b /\ a<lo) \/ ld_site_bytes E live a b) ==>
      ((w2n p<=a /\ a<w2n p+w2n n) <=> (w2n q<=b /\ b<w2n q+w2n n))) /\
   (!a b. ((a=b /\ a<lo) \/ ld_site_bytes E live a b) /\
      w2n p<=a /\ a<w2n p+w2n n ==> a-w2n p=b-w2n q)` by suspend "geometry" >>
  suspend "complete"
QED

Resume ld_normal_payload_copy_backward[target_operands]:
  qpat_x_assum `step_inst fuel CT i t = OK t'` mp_tac >>
  qpat_x_assum `MEM i.inst_opcode _` mp_tac >> simp[MEM] >> strip_tac >>
  simp[Once step_inst_non_invoke, SimpLHS] >>
  asm_rewrite_tac[step_inst_base_def, opcode_case_def] >>
  simp[AllCaseEqs()] >> strip_tac >> metis_tac[]
QED

Resume ld_normal_payload_copy_backward[geometry]:
  Cases_on `w2n n = 0` >- simp[] >>
  qhdtm_x_assum `ld_normal_data` kall_tac >>
  qhdtm_x_assum `ld_frame_embedding` kall_tac >>
  qhdtm_x_assum `ld_alloc_account` kall_tac >>
  qhdtm_x_assum `ld_frame_bound` kall_tac >>
  qhdtm_x_assum `ld_stack_bound` kall_tac >>
  qhdtm_x_assum `ld_shared_state` kall_tac >>
  qpat_x_assum `step_inst fuel CT i t = OK t'` kall_tac >>
  qpat_x_assum `step_inst fuel CS i s = OK _` kall_tac >>
  drule_all ld_annotated_access_ok >> strip_tac >>
  `MEM (w2n p,w2n n) (source_memory_write_ranges i s)` by
    (qpat_x_assum `MEM i.inst_opcode _` mp_tac >> simp[MEM] >> strip_tac >>
     simp[source_memory_write_ranges_def, sized_source_write_range_def]) >>
  `0 < w2n n` by decide_tac >>
  `((w2n p = w2n q /\ w2n p+w2n n <= lo) \/
    (?owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz /\
      bs <= w2n p /\ w2n p+w2n n <= bs+sz /\ w2n q=bt+(w2n p-bs)))` by
    suspend "destination" >>
  (match_mp_tac ld_fixed_live_write_footprint >>
   conj_tac >- metis_tac[] >>
   conj_tac >- asm_rewrite_tac[] >> metis_tac[])
QED

Resume ld_normal_payload_copy_backward[destination]:
  drule ld_access_write_classification >>
  disch_then (qspecl_then [`w2n p`,`w2n n`] mp_tac) >> simp[] >> strip_tac
  >- (disj1_tac >> simp[] >>
      `ld_op_prov AG dst = NONE` by
        (qpat_x_assum `!ops. _` mp_tac >>
         qpat_x_assum `MEM i.inst_opcode _` mp_tac >> simp[MEM] >> strip_tac >>
         simp[mem_write_ops_def, GSYM ld_erase_op_prov]) >>
      drule ld_owned_operand_clean >> disch_then (qspec_then `dst` mp_tac) >>
      Cases_on `i.inst_opcode = EXTCODECOPY` >> fs[MEM]) >>
  disj2_tac >>
  `mem_write_ops i = SOME <| iao_ofst := dst; iao_size := SOME sz;
                            iao_max_size := SOME sz |>` by
    (qpat_x_assum `MEM i.inst_opcode _` mp_tac >> simp[MEM] >> strip_tac >>
     gvs[mem_write_ops_def]) >>
  gvs[] >>
  `owner IN live` by metis_tac[] >>
  `v IN {v | v IN V /\ ~retpc_var fn v}` by
    (Cases_on `i.inst_opcode = EXTCODECOPY` >> fs[MEM] >> metis_tac[]) >>
  `?bt. ld_site_entry E owner bs' bt sz'` by
    (drule ld_owned_operand_value >>
     disch_then (qspecl_then [`q`,`p`,`Var v`] mp_tac) >>
     simp[ld_op_prov_def, ld_owned_value_def] >> metis_tac[]) >>
  `bs'+sz' < dimword(:256)` by metis_tac[] >>
  `!bt. ld_site_entry E owner bs' bt sz' ==> bt+sz' < dimword(:256)` by metis_tac[] >>
  drule_all (SRULE[arithmeticTheory.ADD_COMM] ld_owned_address_transport) >> metis_tac[]
QED

Resume ld_normal_payload_copy_backward[complete]:
  qpat_x_assum `U = _` SUBST_ALL_TAC >>
  qpat_x_assum `d = _` SUBST_ALL_TAC >>
  qexists_tac `write_memory_with_expansion (w2n p) bs s` >>
  conj_tac >- asm_rewrite_tac[] >>
  `((write_memory_with_expansion (w2n p) bs s) with vs_memory := s.vs_memory) = s /\
   (t' with vs_memory := t.vs_memory) = t` by
    simp[write_memory_with_expansion_def, expand_memory_def, write_memory_def] >>
  mp_tac (Q.INST [`s'` |-> `write_memory_with_expansion (w2n p) bs s`]
    ld_payload_copy_taint) >> asm_rewrite_tac[] >> strip_tac >>
  mp_tac (Q.INST [`s` |-> `t`, `s'` |-> `t'`, `tn` |-> `un`, `p` |-> `q`]
    ld_payload_copy_taint) >> asm_rewrite_tac[] >> strip_tac >>
  `ld_byte_rel (\a b. (a=b /\ a<lo) \/ ld_site_bytes E live a b)
    ((step_taint i s (write_memory_with_expansion (w2n p) bs s) tn).t_mem)
    ((step_taint i t t' un).t_mem)
    (\a. read_memory a 1 (write_memory_with_expansion (w2n p) bs s))
    (\b. read_memory b 1 t')` by suspend "bytes" >>
  drule ld_normal_step_memory_complete >> disch_then irule >> simp[] >>
  suspend "annotation"
QED

Resume ld_normal_payload_copy_backward[bytes]:
  drule ld_normal_data_memory >> disch_tac >>
  asm_rewrite_tac[] >>
  qpat_x_assum `LENGTH bs = _`
    (fn th => match_mp_tac (REWRITE_RULE [th] ld_shared_payload_write)) >>
  gvs[arithmeticTheory.ADD_COMM] >> metis_tac[]
QED

Resume ld_normal_payload_copy_backward[annotation]:
  gvs[ld_empty_outputs_prov_tvar, arithmeticTheory.ADD_COMM] >>
  fs[ld_owned_vars_def] >>
  simp[ld_owned_vars_def, ld_empty_outputs_prov_tvar,
       write_memory_with_expansion_def, expand_memory_def, write_memory_def,
       lookup_var_def, op_taint_def] >>
  fs[lookup_var_def, op_taint_def]
QED

Finalise ld_normal_payload_copy_backward

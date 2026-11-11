Theory lowerDloadResidualRead
Ancestors
  lowerDloadNormalExisting lowerDloadRelocation o1LowerDloadRangeTransport
  venomExecSemantics venomState list rich_list pred_set words byte venomInst lowerDloadReachableDiscipline
  lowerDloadAccessClassification lowerDloadTargetGeometry memLocDefs codegenRel
  ptrDiscipline lowerDloadPairedBoundary lowerDloadOwnership lowerDloadLifetime
  lowerDloadNormalData lowerDloadFrameCertificate finite_map lowerDloadCoverageInvariant
  lowerDloadOpaqueExecution lowerDloadProvenanceSupport pointerConfinedDefs
  lowerDloadParamProducer lowerDloadVariableTransport contextCodegenRel o1PassContract lowerDloadOperand
  lowerDloadSharedState lowerDloadAllocation lowerDloadReturnBoundary o1LowerDloadJointInternalEffects

(* Singleton observations determine padded slices, including empty and
   beyond-the-end reads; neither memory length need agree. *)
Theorem ld_byte_rel_clean_read_memory:
  (!j. j < n ==> R (a+j) (b+j)) /\
  DISJOINT X {q | a <= q /\ q < a+n} /\
  ld_byte_rel R X Y (\q. venomState$read_memory q 1 s) (\q. venomState$read_memory q 1 t) ==>
  venomState$read_memory a n s = venomState$read_memory b n t
Proof
  strip_tac >> match_mp_tac listTheory.LIST_EQ >> simp[ld_read_memory_length] >>
  rpt strip_tac >> simp[ld_read_memory_element] >>
  `a+x NOTIN X` by
    (qpat_x_assum `DISJOINT _ _` mp_tac >>
     simp[DISJOINT_DEF, EXTENSION] >>
     disch_then (qspec_then `a+x` mp_tac) >> simp[]) >>
  `venomState$read_memory (a+x) 1 s = venomState$read_memory (b+x) 1 t` by
    (gvs[ld_byte_rel_def] >> metis_tac[]) >>
  pop_assum (mp_tac o AP_TERM ``EL 0 : word8 list -> word8``) >>
  simp[ld_read_memory_element]
QED

Theorem ld_sha3_execution_backward:
  i.inst_opcode = SHA3 /\ i.inst_operands = [off;sz] /\
  eval_operand off s = SOME p /\ eval_operand off t = SOME q /\
  eval_operand sz s = SOME n /\ eval_operand sz t = SOME n /\
  venomState$read_memory (w2n p) (w2n n) s =
    venomState$read_memory (w2n q) (w2n n) t /\
  step_inst fuel CT i t = OK t' ==>
  ?out h. i.inst_outputs = [out] /\
    step_inst fuel CS i s = OK (update_var out h s) /\
    t' = update_var out h t
Proof
  strip_tac >> qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[Once step_inst_non_invoke, SimpLHS] >>
  asm_rewrite_tac[step_inst_base_def, opcode_case_def] >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac `update_var out hash t` >>
  qexists_tac `hash` >> simp[] >>
  simp[Once step_inst_non_invoke, SimpLHS] >>
  asm_rewrite_tac[step_inst_base_def, opcode_case_def] >>
  gvs[venomStateTheory.read_memory_def, Abbr `hash`] >> metis_tac[]
QED

Theorem ld_log_execution_backward:
  i.inst_opcode = LOG /\ i.inst_operands = Lit tc :: rest /\
  ~s.vs_call_ctx.cc_static /\
  s.vs_call_ctx.cc_address = t.vs_call_ctx.cc_address /\
  eval_operand (EL 0 (REVERSE rest)) s = SOME p /\
  eval_operand (EL 0 (REVERSE rest)) t = SOME q /\
  eval_operand (EL 1 (REVERSE rest)) s = SOME n /\
  eval_operand (EL 1 (REVERSE rest)) t = SOME n /\
  eval_operands (DROP 2 (REVERSE rest)) s =
    eval_operands (DROP 2 (REVERSE rest)) t /\
  venomState$read_memory (w2n p) (w2n n) s =
    venomState$read_memory (w2n q) (w2n n) t /\
  step_inst fuel CT i t = OK t' ==>
  ?ev. step_inst fuel CS i s = OK (s with vs_logs := s.vs_logs ++ [ev]) /\
    t' = t with vs_logs := t.vs_logs ++ [ev]
Proof
  strip_tac >> qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[Once step_inst_non_invoke, SimpLHS] >>
  asm_rewrite_tac[step_inst_base_def, opcode_case_def] >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac `t with vs_logs := t.vs_logs ++ [ev]` >>
  qexists_tac `ev` >> simp[] >>
  simp[Once step_inst_non_invoke, SimpLHS] >>
  asm_rewrite_tac[step_inst_base_def, opcode_case_def] >>
  gvs[venomStateTheory.read_memory_def, Abbr `ev`] >> metis_tac[]
QED

Theorem ld_annotated_observation_clean:
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  ptr_discipline lo CS vs0 /\ MEM i.inst_opcode [SHA3; LOG] ==>
  (!op. MEM op i.inst_operands ==> op_taint tn op = {}) /\
  (!a n. MEM (a,n) (source_memory_read_ranges i s) ==>
    DISJOINT tn.t_mem {q | a <= q /\ q < a+n})
Proof
  strip_tac >> drule_all ld_annotated_taint_ok >> strip_tac >>
  conj_tac
  >- (rpt strip_tac >> irule ld_taint_operand_clean >>
      goal_assum (drule_at Any) >>
      qpat_x_assum `MEM i.inst_opcode _` mp_tac >> simp[MEM] >>
      strip_tac >> simp[] >> metis_tac[]) >>
  rpt strip_tac >>
  qpat_x_assum `taint_ok _ _ _ _` mp_tac >>
  qpat_x_assum `MEM i.inst_opcode _` mp_tac >> simp[MEM] >>
  strip_tac >> simp[taint_ok_def, about_to_revert_def, DISJOINT_DEF, EXTENSION] >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

(* The access classification is shared by all variable-width observations.
   Its zero-width branch deliberately does not require a live pointer site. *)
Theorem ld_owned_read_range_geometry:
  access_ok lo (ld_erase AG) fn i s /\ ~in_revert_forward fn s /\
  mem_read_ops i = SOME ops /\
  MEM (w2n p,n) (source_memory_read_ranges i s) /\
  eval_operand ops.iao_ofst s = SOME p /\
  eval_operand ops.iao_ofst t = SOME q /\
  op_taint tn ops.iao_ofst = {} /\
  (!v. ops.iao_ofst = Var v ==> v IN U) /\
  ld_owned_vars U E AG BH tn un s t /\
  (!v owner bs sz. FLOOKUP AG v = SOME(owner,(bs,sz)) ==>
    owner IN live /\ bs+sz < dimword(:256)) /\
  (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
    bt+sz < dimword(:256)) ==>
  !j. j < n ==>
    ((w2n p+j = w2n q+j /\ w2n p+j < lo) \/
     ld_site_bytes E live (w2n p+j) (w2n q+j))
Proof
  strip_tac >> Cases_on `n = 0` >- simp[] >>
  drule ld_access_read_classification >>
  disch_then (qspecl_then [`w2n p`,`n`] mp_tac) >> simp[] >> strip_tac
  >- (`ld_op_prov AG ops.iao_ofst = NONE` by
        (gvs[GSYM ld_erase_op_prov]) >>
      drule ld_owned_operand_clean >>
      disch_then (qspec_then `ops.iao_ofst` mp_tac) >>
      simp[] >> rpt strip_tac >> gvs[] >> decide_tac) >>
  gvs[] >>
  `?bt. ld_site_entry E owner bs bt sz /\
    FLOOKUP BH v = SOME(owner,(bt,sz)) /\
    w2n q = bt+(w2n p-bs) /\ w2n q+n <= bt+sz` by
    (irule ld_owned_address_transport >> simp[] >>
     conj_tac >- metis_tac[] >>
     conj_tac >- metis_tac[] >>
     qexistsl_tac [`AG`,`U`,`s`,`t`,`tn`,`un`] >> simp[]) >>
  rpt strip_tac >> disj2_tac >>
  simp[ld_site_bytes_def] >>
  qexistsl_tac [`owner`,`bs`,`bt`,`sz`,`w2n p-bs+j`] >> simp[] >>
  metis_tac[]
QED

Theorem ld_normal_observation_read:
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  ptr_discipline lo CS vs0 /\ MEM i.inst_opcode [SHA3; LOG] /\
  ~in_revert_forward fn s /\
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk f /\
  mem_read_ops i = SOME ops /\ MEM ops.iao_ofst i.inst_operands /\
  (!v. ops.iao_ofst = Var v ==> v IN U) /\
  MEM (w2n p,n) (source_memory_read_ranges i s) /\
  eval_operand ops.iao_ofst s = SOME p /\
  eval_operand ops.iao_ofst t = SOME q ==>
  venomState$read_memory (w2n p) n s = venomState$read_memory (w2n q) n t
Proof
  strip_tac >>
  drule_all ld_annotated_observation_clean >> strip_tac >>
  drule ld_normal_data_frame >> simp[ld_frame_data_def] >> strip_tac >>
  drule ld_normal_data_geometry >> strip_tac >>
  `!v owner bs sz. FLOOKUP AG v = SOME(owner,(bs,sz)) ==>
    owner IN live /\ bs+sz < dimword(:256)` by
    (rpt strip_tac >>
     `owner IN live` by metis_tac[] >> simp[] >>
     `?bt. ld_site_entry E owner bs bt sz` by
       (qpat_x_assum `!v. ld_owned_selection E _ _` (qspec_then `v` mp_tac) >>
        simp[ld_owned_selection_def] >> metis_tac[]) >> metis_tac[]) >>
  `!j. j < n ==>
    ((w2n p+j = w2n q+j /\ w2n p+j < lo) \/
      ld_site_bytes E live (w2n p+j) (w2n q+j))` by
    (mp_tac ld_owned_read_range_geometry >> asm_rewrite_tac[] >>
     impl_tac >- (metis_tac[ld_annotated_access_ok]) >> simp[]) >>
  irule ld_byte_rel_clean_read_memory >>
  qexistsl_tac [`(\a b. (a=b /\ a<lo) \/ ld_site_bytes E live a b)`,
    `tn.t_mem`,`un.t_mem`] >> simp[] >>
  conj_tac >- (gvs[arithmeticTheory.ADD_COMM]) >>
  drule ld_normal_data_memory >> simp[]
QED

Theorem ld_normal_sha3_backward:
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  ptr_discipline lo CS vs0 /\
  (!f. MEM f CS.ctx_functions ==> fn_ptr_ok P f) /\ opaque_use_ok fn /\
  U = {v | v IN V /\ ~retpc_var fn v} /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  i.inst_opcode = SHA3 /\ i.inst_operands = [off;sz] /\
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
     irule ld_retpc_observable_operand >> simp[] >> qexists_tac `i` >> simp[]) >>
  `ld_owned_vars U E AG BH tn un s t /\
   (!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
   (!v. ld_owned_selection E (FLOOKUP AG v) (FLOOKUP BH v))` by
    (drule ld_normal_data_frame >> simp[ld_frame_data_def]) >>
  `!op. MEM op i.inst_operands ==> op_taint tn op = {}` by
    (drule ld_annotated_observation_clean >> simp[] >> metis_tac[]) >>
  `ld_op_prov AG sz = NONE` by suspend "size_scalar" >>
  `eval_operand sz s = eval_operand sz t` by
    (irule ld_owned_operand_clean >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[MEM]) >>
  `?q n. eval_operand off t = SOME q /\ eval_operand sz t = SOME n` by
    (qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
     simp[Once step_inst_non_invoke, SimpLHS] >>
     asm_rewrite_tac[step_inst_base_def, opcode_case_def] >>
     simp[AllCaseEqs()] >> metis_tac[]) >>
  `?p. eval_operand off s = SOME p` by
    (Cases_on `eval_operand off s` >> simp[] >>
     metis_tac[ld_owned_operand_defined, MEM, optionTheory.NOT_SOME_NONE]) >>
  `venomState$read_memory (w2n p) (w2n n) s =
    venomState$read_memory (w2n q) (w2n n) t` by suspend "read" >>
  `eval_operand sz s = SOME n` by metis_tac[] >>
  drule_all ld_sha3_execution_backward >>
  disch_then (qspec_then `CS` strip_assume_tac) >> gvs[] >>
  suspend "completion"
QED

Resume ld_normal_sha3_backward[size_scalar]:
  `MEM fn CS.ctx_functions` by metis_tac[ld_annotated_fn_member] >>
  `fn_ptr_ok P fn` by metis_tac[] >>
  `ptr_use_ok P (fn_pv P fn) i` by (fs[fn_ptr_ok_def] >> metis_tac[]) >>
  `!v. sz = Var v ==> v NOTIN fn_pv P fn` by
    (rpt strip_tac >>
     qpat_x_assum `ptr_use_ok _ _ _` mp_tac >>
     simp[ptr_use_ok_def, is_pointer_preserving_op_def,
          mem_read_ops_def, mem_write_ops_def] >>
     qexists_tac `v` >> Cases_on `off = Var v` >> gvs[]) >>
  drule_all ld_annotated_scalar_prov >> simp[]
QED

Resume ld_normal_sha3_backward[read]:
  irule ld_normal_observation_read >>
  goal_assum (drule_at (Pat `ld_normal_data _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `ld_annotated_reachable _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[mem_read_ops_def, source_memory_read_ranges_def] >>
  suspend "read_fields"
QED

Resume ld_normal_sha3_backward[completion]:
  irule ld_normal_step_vars_complete >>
  simp[ld_update_var_restore] >>
  `ld_step_prov AP AG L i = ld_set_prov AG [out] NONE /\
   ld_step_prov BP BH H i = ld_set_prov BH [out] NONE` by
    simp[ld_step_prov_def, ld_out_prov_def] >>
  `!v. ld_owned_selection E (FLOOKUP (ld_step_prov AP AG L i) v)
    (FLOOKUP (ld_step_prov BP BH H i) v)` by
    (simp[] >> irule ld_owned_set_selection >> simp[ld_owned_selection_def]) >>
  simp[] >> conj_tac >- metis_tac[ld_lookup_defined_update] >>
  `ld_owned_vars {v | v IN V /\ ~retpc_var fn v} E
    (ld_set_prov AG [out] NONE) (ld_set_prov BH [out] NONE)
    (step_taint i s (update_var out h s) tn)
    (step_taint i t (update_var out h t) un)
    (update_var out h s) (update_var out h t)` by
    (irule ld_owned_vars_update_supported >>
     goal_assum (drule_at Any) >> qexistsl_tac [`{}`,`{}`] >>
     simp[ld_owned_value_def, ld_mask_word_def, step_taint_def, out_taint_def]) >>
  asm_rewrite_tac[] >>
  simp[step_taint_def, mem_taint_def, new_site_bytes_def,
       step_writes_def, source_memory_write_ranges_def,
       store_taint_def, imm_taint_def, adopt_reset_def,
       written_taint_def, range_bytes_def, update_var_def, FLOOKUP_DEF, EXTENSION] >>
  rpt CASE_TAC >> simp[] >> metis_tac[]
QED

Resume ld_normal_sha3_backward[read_fields]:
  conj_tac >- (gvs[] >> metis_tac[]) >>
  simp[memory_range_of_operands_def]
QED

Finalise ld_normal_sha3_backward

Theorem ld_normal_data_logs:
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un
    (s with vs_logs := sl) (t with vs_logs := tl)
    astk live keys d A suspended gstk f <=>
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk f
Proof
  simp[ld_normal_data_def, ld_frame_data_def, ld_frame_embedding_def,
       ld_owned_vars_def, lookup_var_def, ld_shared_state_def,
       ld_alloc_account_def, allocas_from_def, venomStateTheory.read_memory_def]
QED

Theorem ld_normal_log_backward:
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  ptr_discipline lo CS vs0 /\
  (!f. MEM f CS.ctx_functions ==> fn_ptr_ok P f) /\ opaque_use_ok fn /\
  U = {v | v IN V /\ ~retpc_var fn v} /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  i.inst_opcode = LOG /\ i.inst_operands = Lit tc :: REVERSE (off::sz::topics) /\
  i.inst_outputs = [] /\ ~in_revert_forward fn s /\
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
     irule ld_retpc_observable_operand >> simp[] >> qexists_tac `i` >> simp[]) >>
  `ld_owned_vars U E AG BH tn un s t /\
   (!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
   (!v. ld_owned_selection E (FLOOKUP AG v) (FLOOKUP BH v))` by
    (drule ld_normal_data_frame >> simp[ld_frame_data_def]) >>
  `!op. MEM op i.inst_operands ==> op_taint tn op = {}` by
    (drule ld_annotated_observation_clean >> simp[] >> metis_tac[]) >>
  `!op. MEM op (sz::topics) ==> ld_op_prov AG op = NONE` by suspend "scalar" >>
  `eval_operand sz s = eval_operand sz t /\
   eval_operands topics s = eval_operands topics t` by suspend "operands" >>
  `?q n. eval_operand off t = SOME q /\ eval_operand sz t = SOME n /\
    ~t.vs_call_ctx.cc_static /\ LENGTH topics = w2n tc /\
    IS_SOME (eval_operands topics t)` by suspend "target" >>
  `?p. eval_operand off s = SOME p` by
    (Cases_on `eval_operand off s` >> simp[] >>
     metis_tac[ld_owned_operand_defined, MEM, MEM_REVERSE, optionTheory.NOT_SOME_NONE]) >>
  `venomState$read_memory (w2n p) (w2n n) s =
    venomState$read_memory (w2n q) (w2n n) t` by suspend "read" >>
  `s.vs_call_ctx = t.vs_call_ctx` by
    (drule ld_normal_data_frame >> simp[ld_frame_data_def, ld_shared_state_def]) >>
  `?ev. step_inst fuel CS i s = OK (s with vs_logs := s.vs_logs ++ [ev]) /\
    t' = t with vs_logs := t.vs_logs ++ [ev]` by
    (irule ld_log_execution_backward >>
     simp[REVERSE_APPEND] >> metis_tac[]) >>
  gvs[] >> suspend "completion"
QED

Resume ld_normal_log_backward[scalar]:
  `MEM fn CS.ctx_functions` by metis_tac[ld_annotated_fn_member] >>
  `fn_ptr_ok P fn` by metis_tac[] >>
  `ptr_use_ok P (fn_pv P fn) i` by (fs[fn_ptr_ok_def] >> metis_tac[]) >>
  rpt strip_tac >>
  `!v. op = Var v ==> v NOTIN fn_pv P fn` by
    (rpt strip_tac >>
     qpat_x_assum `ptr_use_ok _ _ _` mp_tac >>
     simp[ptr_use_ok_def, is_pointer_preserving_op_def,
          mem_read_ops_def, mem_write_ops_def, REVERSE_APPEND] >>
     qexists_tac `v` >> conj_tac >- (gvs[] >> metis_tac[]) >>
     Cases_on `topics` >> simp[FILTER_APPEND] >>
     Cases_on `off = Var v` >> simp[] >>
     gvs[] >> strip_tac >>
     pop_assum (mp_tac o AP_TERM ``LENGTH : operand list -> num``) >>
     simp[] >> rpt CASE_TAC >> gvs[] >>
     rename1 `FILTER ($= (Var v)) (REVERSE xs) <> []` >>
     `MEM (Var v) (FILTER ($= (Var v)) (REVERSE xs))` by
       simp[MEM_FILTER, MEM_REVERSE] >>
     strip_tac >> gvs[]) >>
  drule_all ld_annotated_scalar_prov >> simp[]
QED
Resume ld_normal_log_backward[operands]:
  conj_tac
  >- (irule ld_owned_operand_clean >> goal_assum (drule_at Any) >>
      gvs[] >> metis_tac[]) >>
  irule ld_owned_operands_clean >> goal_assum (drule_at Any) >>
  gvs[] >> metis_tac[]
QED
Resume ld_normal_log_backward[target]:
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[Once step_inst_non_invoke, SimpLHS] >>
  asm_rewrite_tac[step_inst_base_def, opcode_case_def] >>
  simp[AllCaseEqs(), REVERSE_APPEND] >> strip_tac >>
  `IS_SOME (eval_operands (Lit tc::REVERSE (off::sz::topics)) t)` by
    (simp[ld_eval_operands_defined, EVERY_REVERSE, eval_operand_def] >>
     metis_tac[ld_eval_operands_defined, optionTheory.IS_SOME_DEF]) >>
  gvs[optionTheory.IS_SOME_DEF] >> metis_tac[]
QED
Resume ld_normal_log_backward[read]:
  irule ld_normal_observation_read >>
  goal_assum (drule_at (Pat `ld_normal_data _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `ld_annotated_reachable _ _ _ _ _ _ _ _ _ _ _`)) >>
  Cases_on `eval_operands topics t` >> gvs[] >>
  Cases_on `topics` >>
  simp[mem_read_ops_def, source_memory_read_ranges_def, REVERSE_APPEND,
       memory_range_of_operands_def] >> gvs[eval_operands_def, REVERSE_APPEND] >> metis_tac[]
QED
Resume ld_normal_log_backward[completion]:
  `!AP AG L. ld_step_prov AP AG L i = AG` by
    simp[ld_step_prov_def, ld_set_prov_def, DRESTRICT_UNIV] >>
  `!st ta logs. step_taint i st (st with vs_logs := logs) ta = ta` by
    (rpt gen_tac >>
     simp[step_taint_def, mem_taint_def, new_site_bytes_def,
          step_writes_def, source_memory_write_ranges_def,
          store_taint_def, imm_taint_def, adopt_reset_def,
          written_taint_def, range_bytes_def, set_var_taint_def,
          DRESTRICT_UNIV, FLOOKUP_DEF, taint_component_equality, EXTENSION] >>
     rpt CASE_TAC >> simp[taint_component_equality, EXTENSION] >> metis_tac[]) >>
  simp[ld_normal_data_logs]
QED
Finalise ld_normal_log_backward

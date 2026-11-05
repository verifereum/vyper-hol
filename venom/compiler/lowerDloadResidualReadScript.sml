Theory lowerDloadResidualRead
Ancestors
  lowerDloadNormalExisting lowerDloadRelocation o1LowerDloadRangeTransport
  venomExecSemantics venomState list rich_list pred_set words byte venomInst lowerDloadReachableDiscipline
  lowerDloadAccessClassification lowerDloadTargetGeometry memLocDefs codegenRel
  ptrDiscipline lowerDloadPairedBoundary lowerDloadOwnership lowerDloadLifetime
  lowerDloadNormalData lowerDloadFrameCertificate finite_map lowerDloadCoverageInvariant

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

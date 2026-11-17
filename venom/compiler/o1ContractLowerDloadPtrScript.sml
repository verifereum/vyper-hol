(*
 * LowerDload against the O1 pass contract: the output keeps the pointer
 * discipline above the same fixed region.
 * Kept in its own theory so its proof can be worked on apart from the
 * other rows; o1ContractLowerDloadStage assembles them.
 *
 * TOP-LEVEL:
 *   lower_dload_stage_ptr
 *)
Theory o1ContractLowerDloadPtr
Ancestors
  o1ContractLowerDload o1PassContract ptrDiscipline unitMemInv
  lowerDloadDefs venomPassSchedule list
  lowerDloadPtrReachableStatic lowerDloadPtrJointSafety

(* The output keeps the pointer discipline above the same fixed region. *)
val stage_ptr_header = ``
  !rpolicy D view C C' vs names lo.
    ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
    dead_wf D /\ o1_ctx_shape C /\ o1_run_state_ok vs /\
    o1_src_inv D C vs /\ callee_first names C.ctx_functions /\
    fixed_region_reserved lo C /\ ptr_discipline lo C vs ==>
    ptr_discipline lo C' vs``;

Theorem lower_dload_stage_ptr_static:
  ^(rhs (concl (DEPTH_CONV BETA_CONV
    (subst [``o1_run_state_ok`` |->
      ``\s. o1_initial_state_ok s /\ s.vs_fmp = s.vs_initial_fmp /\
        code_layout_valid s``] stage_ptr_header))))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_assum `ptr_discipline lo C vs` mp_tac >>
  rewrite_tac[ptr_discipline_def] >> strip_tac >>
  simp[ptr_discipline_def] >> qexists_tac `P` >> conj_tac
  >- (drule_all lower_dload_stage_static_ptr_ok >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `EVERY (fn_ptr_ok P) C.ctx_functions` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  drule_all lower_dload_stage_dynamic_safety_static >> simp[]
QED

Theorem lower_dload_stage_ptr:
  ^stage_ptr_header
Proof
  rpt gen_tac >> disch_tac >> match_mp_tac lower_dload_stage_ptr_static >>
  rule_assum_tac (REWRITE_RULE [o1_run_state_ok_def]) >>
  asm_simp_tac bool_ss [] >>
  qexistsl [`rpolicy`,`D`,`view`,`C`,`names`] >>
  asm_simp_tac bool_ss []
QED

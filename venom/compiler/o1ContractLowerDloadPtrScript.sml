(*
 * LowerDload against the O1 pass contract: the output keeps the pointer
 * discipline above the same fixed region.
 * Kept in its own theory so its proof can be worked on apart from the
 * other rows; o1ContractLowerDloadStage assembles them.
 *
 * TOP-LEVEL:
 *   lower_dload_stage_ptr
 *   lower_dload_stage_ptr_whole
 *)
Theory o1ContractLowerDloadPtr
Ancestors
  o1SafeUpto o1ContractLowerDload o1PassContract ptrDiscipline unitMemInv
  lowerDloadDefs venomPassSchedule list
  lowerDloadPtrReachableStatic lowerDloadPtrJointSafety

(* The output keeps the pointer discipline above the same fixed region,
   up to the same gas cut. *)
Theorem lower_dload_stage_ptr:
  !rpolicy D view C C' vs names lo cut.
    ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
    dead_wf D /\ o1_ctx_shape C /\ o1_run_state_ok vs /\
    o1_safe_upto D lo cut C vs /\ callee_first names C.ctx_functions ==>
    ptr_discipline_upto lo cut C' vs
Proof
  rpt gen_tac >> strip_tac >>
  `ptr_discipline_upto lo cut C vs` by
    fs[o1_safe_upto_def, o1_ptr_safe_upto_def] >>
  pop_assum mp_tac >> rewrite_tac[ptr_discipline_upto_def] >> strip_tac >>
  simp[ptr_discipline_upto_def] >> conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (qexists_tac `P` >> drule_all lower_dload_stage_static_ptr_ok >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `EVERY (fn_ptr_ok P) C.ctx_functions` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  drule_all lower_dload_stage_dynamic_safety >> simp[]
QED

(* The whole-run version, at the cut past every gas reading. *)
Theorem lower_dload_stage_ptr_whole:
  !rpolicy D view C C' vs names lo.
    ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
    dead_wf D /\ o1_ctx_shape C /\ o1_run_state_ok vs /\
    o1_src_inv D C vs /\ callee_first names C.ctx_functions /\
    fixed_region_reserved lo C /\ ptr_discipline lo C vs ==>
    ptr_discipline lo C' vs
Proof
  rpt strip_tac >>
  `!n. o1_safe_upto D lo n C vs` by metis_tac[o1_src_inv_ptr_safe_upto] >>
  irule ptr_discipline_upto_all >> irule lower_dload_stage_ptr >>
  metis_tac[]
QED

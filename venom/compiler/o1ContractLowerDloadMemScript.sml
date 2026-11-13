(*
 * LowerDload against the O1 pass contract: the output keeps raw memory
 * safety on its reachable states.
 * Kept in its own theory so its proof can be worked on apart from the
 * other rows; o1ContractLowerDloadStage assembles them.
 *
 * TOP-LEVEL:
 *   lower_dload_stage_mem
 *)
Theory o1ContractLowerDloadMem
Ancestors
  o1ContractLowerDload o1PassContract ptrDiscipline unitMemInv
  lowerDloadDefs venomPassSchedule list lowerDloadRawCoverage lowerDloadCurrentSafety

(* The output's reachable states keep raw memory safety. *)
Theorem lower_dload_stage_mem:
  !rpolicy D view C C' vs names.
    ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
    dead_wf D /\ o1_ctx_shape C /\ o1_run_state_ok vs /\
    o1_src_inv D C vs /\ callee_first names C.ctx_functions ==>
    mem_inv raw_mem_ok C' vs
Proof
  rpt strip_tac >>
  drule_all lowerDloadStageAmbientTheory.ld_stage_ambient >> strip_tac >>
  `mem_inv raw_mem_ok C vs` by fs[o1_src_inv_def] >>
  RULE_ASSUM_TAC BETA_RULE >>
  rewrite_tac[mem_inv_raw_reachable] >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >>
  drule_all (BETA_RULE ld_raw_coverage_fixed) >> disch_tac >>
  irule (BETA_RULE ld_owned_or_forward_current_raw) >>
  goal_assum (drule_at Any) >>
  drule_all (BETA_RULE ld_raw_fixed_ambient) >> strip_tac >>
  qpat_x_assum `!fn. MEM fn C.ctx_functions ==> _` drule >>
  simp[] >> strip_tac >> simp[] >>
  qpat_x_assum `!fn. MEM fn C.ctx_functions ==> (_ /\ _) /\ _` drule >>
  simp[] >> strip_tac >> simp[]
QED

(* Fail the build if the contract ever regresses to an admitted proof. *)
val _ = let
  val th = lower_dload_stage_mem
  val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
in
  if null (hyp th) andalso null axioms andalso
     List.all (fn s => s = "DISK_THM") oracles then ()
  else raise Fail "lower_dload_stage_mem: non-kernel proof dependency"
end;

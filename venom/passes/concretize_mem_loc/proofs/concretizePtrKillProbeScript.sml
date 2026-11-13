Theory concretizePtrKillProbe
Ancestors
  concretizePtrProtectedPrefix concretizePtrActivationSupport
  concretizePtrReadCoverage
  concretizeMemLocDefs memLocDefs ptrDiscipline codegenRel
  venomExecSemantics venomState venomInst finite_map

Theorem ptr_invoke_never_kills:
  inst.inst_opcode = INVOKE ==> ~ptr_ml_can_kill a bp sizes inst
Proof
  simp[ptr_ml_can_kill_def, inst_write_size_def, mem_write_ops_def]
QED

Theorem ptr_kill_has_write_operand:
  ptr_ml_can_kill a bp sizes inst ==>
  ?ops. mem_write_ops inst = SOME ops /\
        find_base_allocas bp ops.iao_ofst = [a]
Proof
  Cases_on `mem_write_ops inst` >>
  simp[ptr_ml_can_kill_def, inst_write_size_def,
       inst_write_op_def, find_base_allocas_opt_def] >> metis_tac[]
QED

Theorem ptr_successful_missing_store_excluded:
  step_inst fuel ctx (mk_inst 0 MSTORE [Lit 0w; Var "missing"] [])
    (init_venom_state "entry") = Error "undefined operand"
Proof
  EVAL_TAC
QED

Theorem ptr_successful_literal_write_ready:
  !inst s n s'.
  inst_write_size inst = SOME n /\ step_inst_base inst s = OK s' ==>
  ?vals. eval_operands inst.inst_operands s = SOME vals
Proof
  rpt gen_tac >> Cases_on `inst.inst_opcode` >>
  simp[inst_write_size_def, mem_write_ops_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >>
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  pure_asm_rewrite_tac[] >>
  simp[exec_write2_def] >> strip_tac >>
  gvs[AllCaseEqs(), eval_operands_def]
QED

Theorem ptr_kill_has_variable_write_operand:
  ptr_ml_can_kill a bp sizes inst ==>
  ?ops v. mem_write_ops inst = SOME ops /\ ops.iao_ofst = Var v /\
          find_base_allocas bp (Var v) = [a]
Proof
  strip_tac >> drule ptr_kill_has_write_operand >> strip_tac >>
  Cases_on `ops.iao_ofst` >> gvs[find_base_allocas_def] >> metis_tac[]
QED

Theorem ptr_successful_kill_operands_ready:
  ptr_ml_can_kill a bp sizes inst /\ step_inst fuel ctx inst s = OK s' ==>
  ?vals. eval_operands inst.inst_operands s = SOME vals
Proof
  strip_tac >>
  `inst.inst_opcode <> INVOKE` by metis_tac[ptr_invoke_never_kills] >>
  `step_inst_base inst s = OK s'` by
    (qpat_x_assum `step_inst fuel ctx inst s = OK s'` mp_tac >>
     simp[Once step_inst_def]) >>
  irule ptr_successful_literal_write_ready >>
  gvs[ptr_ml_can_kill_def] >> metis_tac[]
QED

Theorem ptr_fixed_literal_write_never_kills:
  mem_write_ops inst = SOME ops /\ ops.iao_ofst = Lit n ==>
  ~ptr_ml_can_kill a bp sizes inst
Proof
  strip_tac >> strip_tac >> drule ptr_kill_has_variable_write_operand >>
  strip_tac >> gvs[]
QED

(* Universal kill-to-footprint premise ledger (C1.5.53).
   CHECKED HERE:
   - INVOKE cannot kill: its mem_write_ops is NONE.
   - A kill selects a Var destination, not a fixed literal address.
   - Successful kill execution supplies all evaluated operands; the old
     missing-value MSTORE example is an Error, not a successful prefix step.
   REUSABLE CHECKED BOUNDARIES:
   - ptr_ready_literal_write_range gives the actual footprint once the
     destination word is available.
   - ptr_guarded_kill_exact identifies that footprint with a supplied
     same-site provenance entry, exact size and non-revert access_ok.
   STILL REQUIRED, NOT ASSUMED OR PROVED BY THESE PROBES:
   - A kill has a singleton BASE list, whereas
     ptr_frame_production_singleton_write_site requires a singleton PTR
     list, including its offset. Production normalisation must bridge this.
   - That identity theorem additionally needs FLOOKUP G v = SOME site.
     It does not derive runtime provenance from the static BP singleton.
     In particular it cannot alone exclude a variable-address write below
     lo with absent provenance, or identify a foreign selected runtime site.
   - fn_defs_reach_uses must enter a static-to-runtime selected-origin
     theorem if needed; it is not a premise of the existing identity lemma.
   - access_ok's range obligation is guarded by ~in_revert_forward.
     A successful ordinary step alone does not discharge that guard.
   - Production size accuracy must identify the actual owner's size.
   No universal kill-to-footprint theorem is claimed here. *)

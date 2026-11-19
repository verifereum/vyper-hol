(* Close a private DLOAD expansion using the actual target MLOAD update. *)
Theory gasFocusLowerDloadScratchFrame
Ancestors
  lowerDloadPtrExpansionNext lowerDloadPtrExpansionTransport
  lowerDloadPtrJointNext lowerDloadPtrReplay lowerDloadPtrRel
  lowerDloadDefs ptrDiscipline unitShapeDefs irSupply
  venomExecSemantics venomInst venomState finite_map pred_set list words

Theorem ld_focus_scratch_actual_next:
  !U. U = set (fn_ir_vars fn) ==>
  !q. q = u with vs_inst_idx := SUC t.vs_inst_idx ==>
  !ss1. ss1 = ss with vs_inst_idx := SUC s.vs_inst_idx ==>
  dload_boundary_core fl lo (r::rs) (U DIFF {v | retpc_var fn v}) Ws PG PH G H0 tn un0 s t0 stk ds /\
  r.dr_scratch = FDOM t0.vs_allocas DIFF orig /\ FDOM s.vs_allocas SUBSET orig /\
  (EL 0 X).inst_id NOTIN orig /\
  (FLOOKUP t0.vs_allocas (EL 0 X).inst_id = NONE ==>
     t0.vs_alloca_next + 32 < dimword (:256) /\ t0.vs_alloca_next + 32 <= fl) /\
  inst.inst_opcode = DLOAD /\ inst.inst_operands = [off] /\ inst.inst_outputs = [out] /\
  lower_dload_inst_supply supply inst = (X,nxt) /\
  (EL 0 X).inst_outputs = [av] /\ (EL 1 X).inst_outputs = [cv] /\
  av <> cv /\ av NOTIN U /\ cv NOTIN U /\ off <> Var av /\
  code_layout_valid s /\ dload_offset_ok C fn inst s /\
  eval_operand off s = SOME x /\ eval_operand off t0 = SOME x /\
  frame_reachable vs C stk PG G tn fn inst s /\
  dload_control_match sigma fn gn s t0 inst X 0 /\
  ALL_DISTINCT (MAP (\b. b.bb_label) gn.fn_blocks) /\
  (!v. v IN U ==> (lookup_var v s = NONE <=> lookup_var v t0 = NONE)) /\
  step_inst 0 C inst s = OK ss /\ dload_prefix_match pf C' PH X 3 t0 H0 un0 t H un /\
  step_inst fuel C' (EL 3 X) t = OK u /\ active_inst gn j q ==>
  ?r1 i Y.
    r1.dr_source = r.dr_source /\ r1.dr_scratch = (EL 0 X).inst_id INSERT r.dr_scratch /\
    dload_boundary_core fl lo (r1::rs) (U DIFF {v | retpc_var fn v}) Ws PG PH
      (step_prov PG G inst ss) (step_prov PH H (EL 3 X) u)
      (step_taint inst s ss tn) (step_taint (EL 3 X) t u un) ss1 q stk ds /\
    frame_reachable vs C stk PG (step_prov PG G inst ss) (step_taint inst s ss tn) fn i ss1 /\
    dload_control_match sigma fn gn ss1 q i Y 0 /\ j = HD Y /\
    (!v. v IN U ==> (lookup_var v ss1 = NONE <=> lookup_var v q = NONE))
Proof
  CONV_TAC (TOP_DEPTH_CONV (Unwind.UNWIND_FORALL_CONV)) >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  `3 < LENGTH X /\ (EL 3 X).inst_opcode <> INVOKE` by
    (drule_all dload_supply_expansion >> strip_tac >> simp[]) >>
  drule_all dload_prefix_extend_mixed >>
  disch_then (assume_tac o REWRITE_RULE [numLib.REDUCE_CONV ``SUC 3``]) >>
  `av NOTIN (set (fn_ir_vars fn) DIFF {v | retpc_var fn v}) /\
   cv NOTIN (set (fn_ir_vars fn) DIFF {v | retpc_var fn v})` by simp[] >>
  drule_all dload_supply_replay_boundary_fresh >>
  disch_then (qx_choose_then `s1` (qx_choose_then `r1` strip_assume_tac)) >>
  `s1 = ss` by gvs[step_inst_non_invoke] >>
  pop_assum SUBST_ALL_TAC >>
  drule_all dload_supply_definedness_control >> strip_tac >>
  drule_all dload_control_emission_next_fields >>
  disch_then (qx_choose_then `i` (qx_choose_then `Y` strip_assume_tac)) >>
  qexistsl [`r1`, `i`, `Y`] >> simp[] >>
  irule frame_reachable_next >> simp[is_terminator_def] >>
  (conj_tac >- (qexists_tac `0` >> simp[])) >>
  metis_tac[dload_control_match_boundary]
QED

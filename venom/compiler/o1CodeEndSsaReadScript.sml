Theory o1CodeEndSsaRead
Ancestors
  makeSsaCurrentLockstep makeSsaCurrentCutInv o1FrameLockstep
  stateFrame finite_map list

(* Recover the source CODECOPY read and its recorded SSA owner. *)
Theorem code_end_ssa_paired_read:
  current_wf_phi_context supply fn renamed supply' A H events /\
  fn' = fn with fn_blocks :=
    simplify_current_phis_if (blocks_have_leading_phi fn.fn_blocks) renamed /\
  entry_block fn = SOME eb /\ ctx_bisim C C' /\
  current_lockstep_rel fn fn' A renamed H events p (inst,s) sg (inst',s') /\
  inst'.inst_opcode = CODECOPY /\
  inst'.inst_operands = [dst; Var n; sz] /\
  eval_operand (Var n) s' = SOME w ==>
  ?a v b token.
    p /\ inst.inst_opcode = CODECOPY /\
    inst.inst_operands = [a; Var v; b] /\
    FLOOKUP sg n = SOME v /\ MEM (token,v,n) H /\
    eval_operand (Var v) s = SOME w /\ s'.vs_labels = s.vs_labels
Proof
  strip_tac >> drule_all current_lockstep_rel_boundary >> strip_tac >>
  `p` by (Cases_on `p` >> gvs[]) >>
  gvs[inst_pair_def] >>
  rename1 `op_rename sg src (Var n)` >>
  gvs[op_rename_def] >>
  `sg = current_cut_sg fn A renamed H events s.vs_current_bb s.vs_inst_idx`
    by gvs[current_lockstep_rel_def] >>
  rename1 `FLOOKUP sg n = SOME v` >>
  `?token. MEM (token,v,n) H` by metis_tac[current_cut_sg_owned_name] >>
  gvs[state_rel_def, execution_frame_def,
      venomStateTheory.venom_state_component_equality] >>
  qexists_tac `token` >> simp[] >>
  gvs[venomStateTheory.eval_operand_def, vars_rel_def] >> metis_tac[]
QED

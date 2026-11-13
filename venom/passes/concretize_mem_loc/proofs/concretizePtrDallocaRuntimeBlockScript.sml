Theory concretizePtrDallocaRuntimeBlock
Ancestors
  concretizePtrDallocaGhostInterface o1FrameLockstep contextCodegenRel
  venomExecSemantics venomState venomInst ptrDiscipline finite_map pred_set list

Theorem ptr_dalloca_eval_phis_effect:
  !insts s s' x op.
    eval_phis s insts = OK s' /\
    phi_eff s.vs_prev_bb x insts = SOME op ==>
    lookup_var x s' = eval_operand op s
Proof
  Induct >> simp[eval_phis_def, phi_eff_def, phi_read_def, eval_operand_def] >>
  rpt gen_tac >> Cases_on `h.inst_opcode <> PHI`
  >- (simp[] >> rpt strip_tac >> gvs[eval_operand_def]) >>
  simp[AllCaseEqs()] >> rpt strip_tac >>
  gvs[eval_one_phi_def, AllCaseEqs()] >>
  Cases_on `x = out` >> gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  first_x_assum irule >> simp[phi_eff_def]
QED

Theorem ptr_dalloca_runtime_phis:
  ptr_dalloca_ghost_vars G tn.t_var s Gt tnt.t_var t /\
  (!v site. FLOOKUP Gt v = SOME site ==> FLOOKUP TG v = NONE) /\
  (!v site. FLOOKUP TG v = NONE /\ FLOOKUP G v = SOME site ==>
     FLOOKUP Gt v = SOME site) /\
  (!v. phi_eff s.vs_prev_bb v ins = phi_eff t.vs_prev_bb v inst) /\
  eval_phis s ins = OK s1 /\ eval_phis t inst = OK t1 ==>
  ptr_dalloca_ghost_vars (phis_prov s.vs_prev_bb G ins)
    (phis_taint s.vs_prev_bb tn ins) s1
    (phis_prov t.vs_prev_bb Gt inst) (phis_taint t.vs_prev_bb tnt inst) t1 /\
  (!v site. FLOOKUP (phis_prov t.vs_prev_bb Gt inst) v = SOME site ==>
     FLOOKUP (phis_prov s.vs_prev_bb TG ins) v = NONE) /\
  (!v site. FLOOKUP (phis_prov s.vs_prev_bb TG ins) v = NONE /\
     FLOOKUP (phis_prov s.vs_prev_bb G ins) v = SOME site ==>
     FLOOKUP (phis_prov t.vs_prev_bb Gt inst) v = SOME site)
Proof
  strip_tac >> fs[ptr_dalloca_ghost_vars_def] >>
  simp[ptr_dalloca_ghost_vars_def, op_taint_var,
       var_taint_phis_taint, FLOOKUP_phis_prov] >>
  rpt conj_tac >> rpt gen_tac >>
  qpat_assum `!v. phi_eff _ _ _ = _` (qspec_then `v` assume_tac) >>
  Cases_on `phi_eff t.vs_prev_bb v inst` >> gvs[] >>
  rename1 `phi_eff t.vs_prev_bb v inst = SOME op` >>
  Cases_on `op` >> gvs[op_prov_def, op_taint_def] >>
  rpt strip_tac >> gvs[]
  >~ [`lookup_var v s1 = lookup_var v t1`]
  >- (rename1 `FLOOKUP Gt u = SOME site` >>
      `lookup_var v s1 = eval_operand (Var u) s` by
        (irule ptr_dalloca_eval_phis_effect >>
         goal_assum (drule_at Any) >> simp[]) >>
      `lookup_var v t1 = eval_operand (Var u) t` by
        (irule ptr_dalloca_eval_phis_effect >>
         goal_assum (drule_at Any) >> simp[]) >>
      gvs[eval_operand_def]) >>
  metis_tac[]
QED

(* Alignment concerns only the selected incoming operand, not values or
   successor ghosts.  In particular it permits unrelated non-PHI rewrites. *)
Theorem ptr_dalloca_runtime_block:
  ptr_dalloca_ghost_vars G tn.t_var s Gt tnt.t_var t /\
  (!v site. FLOOKUP Gt v = SOME site ==> FLOOKUP TG v = NONE) /\
  (!v site. FLOOKUP TG v = NONE /\ FLOOKUP G v = SOME site ==>
     FLOOKUP Gt v = SOME site) /\
  (!v. phi_eff s.vs_prev_bb v (block_insts fn s.vs_current_bb) =
       phi_eff t.vs_prev_bb v (block_insts fnt t.vs_current_bb)) /\
  enters_block fn s s1 /\ enters_block fnt t t1 ==>
  ptr_dalloca_ghost_vars (entry_prov fn s G) (entry_taint_vars fn s tn).t_var s1
    (entry_prov fnt t Gt) (entry_taint_vars fnt t tnt).t_var t1 /\
  (!v site. FLOOKUP (entry_prov fnt t Gt) v = SOME site ==>
     FLOOKUP (entry_prov fn s TG) v = NONE) /\
  (!v site. FLOOKUP (entry_prov fn s TG) v = NONE /\
     FLOOKUP (entry_prov fn s G) v = SOME site ==>
     FLOOKUP (entry_prov fnt t Gt) v = SOME site)
Proof
  strip_tac >>
  qpat_x_assum `enters_block fn s s1` mp_tac >>
  qpat_x_assum `enters_block fnt t t1` mp_tac >>
  simp[enters_block_def] >> rpt strip_tac >> gvs[] >>
  fs[block_insts_def] >>
  drule_all ptr_dalloca_runtime_phis >>
  gvs[block_insts_def, entry_prov_def, entry_taint_vars_def,
      ptr_dalloca_ghost_vars_def, lookup_var_def]
QED

Theorem ptr_dalloca_runtime_block_params:
  enters_block fn s s1 ==> s1.vs_params = s.vs_params
Proof
  simp[enters_block_def] >> strip_tac >> gvs[] >>
  drule venomExecProofsTheory.eval_phis_only_updates_vs_vars >>
  disch_then (fn th => once_rewrite_tac[th]) >> simp[]
QED

(* Two-state semantic entry; PHIs retain their parallel input environment. *)
Theory o1LowerDloadPhiEntry
Ancestors
  o1LowerDloadPhi o1LowerDloadJointEntry o1LowerDloadJointRelation
  o1LowerDloadEnvironment ptrDiscipline contextCodegenRel
  venomExecSemantics venomExecProofs venomInst o1PassContract list

Theorem ld_env_enters_block:
  ir_supply_covers_fn u fn /\
  lower_dload_function_supply u fn = (fn',u') /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
  ld_env_agree sites fn H tn s t /\
  s.vs_labels = t.vs_labels /\
  s.vs_current_bb = t.vs_current_bb /\
  s.vs_prev_bb = t.vs_prev_bb /\
  enters_block fn s s1 /\ active_inst fn inst s1 ==>
  ?t1. enters_block fn' t t1 /\
    ld_env_agree sites fn (entry_prov fn s H)
      (entry_taint_vars fn s tn) s1 t1 /\
    ld_joint_control u fn fn' s1 t1
Proof
  strip_tac >>
  qpat_x_assum `enters_block fn s s1` mp_tac >>
  simp[enters_block_def] >> strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `EVERY (\i. MEM i (fn_insts fn)) bb.bb_instructions` by
    (simp[EVERY_MEM, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
  drule_all ld_env_eval_phis >> strip_tac >>
  qabbrev_tac `r = t1 with vs_inst_idx := phi_prefix_length bb.bb_instructions` >>
  `enters_block fn t r` by
    (simp[enters_block_def, Abbr `r`] >> metis_tac[]) >>
  `s1.vs_current_bb = r.vs_current_bb /\
   s1.vs_prev_bb = r.vs_prev_bb /\ s1.vs_inst_idx = r.vs_inst_idx` by
    (gvs[Abbr `r`] >>
     qpat_assum `eval_phis s _ = _`
       (mp_tac o MATCH_MP eval_phis_only_updates_vs_vars) >>
     disch_then (fn th => once_rewrite_tac[th]) >>
     qpat_assum `eval_phis t _ = _`
       (mp_tac o MATCH_MP eval_phis_only_updates_vs_vars) >>
     disch_then (fn th => once_rewrite_tac[th]) >>
     simp[]) >>
  `active_inst fn inst r` by (gvs[active_inst_def] >> metis_tac[]) >>
  drule_all ld_supply_successful_entry >> strip_tac >>
  qexists_tac `r` >> conj_tac
  >- metis_tac[enters_block_def] >>
  conj_tac
  >- gvs[entry_prov_def, entry_taint_vars_def, ld_env_agree_def, Abbr `r`] >>
  gvs[ld_joint_control_def, Abbr `r`] >> metis_tac[]
QED

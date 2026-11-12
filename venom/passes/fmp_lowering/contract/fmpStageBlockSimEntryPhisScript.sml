Theory fmpStageBlockSimEntryPhis
Ancestors
  fmpStageRel makeSsaCurrentPhiBatchRuntime o1FrameLockstep
  venomExecProofs venomExecSemantics venomState ptrDiscipline
  o1LowerDloadRelocationKernel finite_map list

Theorem fmp_entry_operand_defined:
  fmp_env_rel sm fn live G tv s t /\ s.vs_labels = t.vs_labels /\
  eval_operand op s = SOME x ==>
  ?y. eval_operand op t = SOME y
Proof
  Cases_on `op` >>
  simp[eval_operand_def, lookup_var_def, fmp_env_rel_def] >> metis_tac[]
QED

Theorem fmp_entry_phis_defined:
  !ins s t s1.
  fmp_env_rel sm fn live G tv s t /\
  s.vs_labels = t.vs_labels /\ s.vs_prev_bb = t.vs_prev_bb /\
  eval_phis s ins = OK s1 ==>
  ?t1. eval_phis t ins = OK t1
Proof
  Induct_on `ins` >- simp[eval_phis_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `h.inst_opcode = PHI` >~ [`h.inst_opcode <> PHI`]
  >- gvs[eval_phis_def] >>
  qpat_x_assum `eval_phis s (h::ins) = _` mp_tac >>
  simp[Once eval_phis_def, AllCaseEqs()] >> strip_tac >>
  gvs[eval_one_phi_def, AllCaseEqs()] >>
  `?y. eval_operand val_op t = SOME y` by
    metis_tac[fmp_entry_operand_defined] >>
  `?t1. eval_phis t ins = OK t1` by metis_tac[] >>
  qexists_tac `update_var out y t1` >>
  simp[Once eval_phis_def, eval_one_phi_def]
QED

Theorem fmp_entry_operand_value:
  fmp_env_rel sm fn live G tn.t_var s t /\ s.vs_labels = t.vs_labels /\
  (!v. op = Var v ==> MEM v live /\ ~retpc_var fn v) /\
  eval_operand op s = SOME x /\ eval_operand op t = SOME y ==>
  fmp_value_rel sm (op_prov G op) (op_taint tn op) x y
Proof
  Cases_on `op` >>
  simp[eval_operand_def, lookup_var_def, op_prov_def, op_taint_def] >>
  rpt strip_tac >> gvs[]
  >- simp[fmp_value_rel_def, ld_value_agree_def, word_agree_except_def] >-
  (fs[fmp_env_rel_def, op_taint_def] >>
   first_x_assum (qspec_then `s'` mp_tac) >> simp[] >>
   disch_then (qspec_then `x` mp_tac) >> simp[]) >>
  simp[fmp_value_rel_def, ld_value_agree_def, word_agree_except_def]
QED

Theorem fmp_entry_phis_env:
  fmp_env_rel sm fn live G tn.t_var s t /\
  s.vs_labels = t.vs_labels /\ s.vs_prev_bb = t.vs_prev_bb /\
  (!v u. MEM v next /\ ~retpc_var fn v /\
     phi_eff s.vs_prev_bb v ins = SOME (Var u) ==>
     MEM u live /\ ~retpc_var fn u) /\
  eval_phis s ins = OK s1 ==>
  ?t1. eval_phis t ins = OK t1 /\
    fmp_env_rel sm fn next (phis_prov s.vs_prev_bb G ins)
      (phis_taint s.vs_prev_bb tn ins) s1 t1
Proof
  rpt strip_tac >>
  `?t1. eval_phis t ins = OK t1` by
    metis_tac[fmp_entry_phis_defined] >>
  qexists_tac `t1` >> simp[] >>
  simp[fmp_env_rel_def] >> rpt gen_tac >> strip_tac >>
  `lookup_var v s1 = SOME x` by gvs[lookup_var_def] >>
  `lookup_var v s1 =
    case phi_eff s.vs_prev_bb v ins of
      NONE => NONE | SOME op => eval_operand op s` by
    metis_tac[current_phi_batch_lookup] >>
  Cases_on `phi_eff s.vs_prev_bb v ins` >- gvs[] >>
  rename1 `phi_eff s.vs_prev_bb v ins = SOME op` >>
  fs[] >>
  `?y. eval_operand op t = SOME y` by
    (irule fmp_entry_operand_defined >> goal_assum (drule_at Any) >>
     simp[] >> goal_assum (drule_at Any)) >>
  `lookup_var v t1 = SOME y` by
    (qpat_x_assum `eval_phis t ins = OK t1` mp_tac >>
     disch_then (qspec_then `v` mp_tac o Q.GEN `x` o
                 MATCH_MP current_phi_batch_lookup) >>
     gvs[]) >>
  qexists_tac `y` >> simp[GSYM lookup_var_def] >> strip_tac >>
  gvs[FLOOKUP_phis_prov, op_taint_var, var_taint_phis_taint] >>
  irule fmp_entry_operand_value >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

(* Layout is deliberately an interface premise: the shape theory proves it
   for the lowered successor, independently of this value transport. *)
Theorem fmp_entry_phis_transport:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
  (!u. eval_phis u bb'.bb_instructions = eval_phis u bb.bb_instructions) /\
  phi_prefix_length bb'.bb_instructions = phi_prefix_length bb.bb_instructions /\
  fmp_env_rel sm fn live G tn.t_var s t /\
  s.vs_labels = t.vs_labels /\ s.vs_prev_bb = t.vs_prev_bb /\
  (!v u. MEM v next /\ ~retpc_var fn v /\
    phi_eff s.vs_prev_bb v bb.bb_instructions = SOME (Var u) ==>
    MEM u live /\ ~retpc_var fn u) /\
  enters_block fn s s1 ==>
  ?t1. enters_block fn' t t1 /\
    fmp_env_rel sm fn next (entry_prov fn s G)
      (entry_taint_vars fn s tn).t_var s1 t1 /\
    t1 = t with <|vs_vars := t1.vs_vars;
                  vs_inst_idx := phi_prefix_length bb.bb_instructions|> /\
    (!v. (!i. MEM i bb.bb_instructions /\ i.inst_opcode = PHI ==>
                   ~MEM v i.inst_outputs) ==>
          FLOOKUP t1.vs_vars v = FLOOKUP t.vs_vars v)
Proof
  rpt strip_tac >>
  qpat_x_assum `enters_block fn s s1` mp_tac >>
  simp[contextCodegenRelTheory.enters_block_def] >> strip_tac >> gvs[] >>
  drule fmp_entry_phis_env >>
  disch_then (qspecl_then [`s_phi`, `next`, `bb.bb_instructions`] mp_tac) >>
  simp[] >> (impl_tac >- metis_tac[]) >> strip_tac >>
  rename1 `eval_phis t bb.bb_instructions = OK tphi` >>
  qexists_tac `tphi with vs_inst_idx := phi_prefix_length bb.bb_instructions` >>
  conj_tac
  >- (simp[contextCodegenRelTheory.enters_block_def] >>
      qexists_tac `tphi` >> simp[]) >>
  conj_tac
  >- gvs[entry_prov_def, entry_taint_vars_def, fmp_env_rel_def] >>
  conj_tac
  >- (drule eval_phis_only_updates_vs_vars >>
      disch_then (fn th => once_rewrite_tac[th]) >> simp[]) >>
  simp[] >> rpt strip_tac >>
  irule eval_phis_flookup_not_phi_output >>
  goal_assum (drule_at Any) >> simp[]
QED

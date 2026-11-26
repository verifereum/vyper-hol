(* Chain steps open both JNZ destinations but leave the shared exit external. *)
Theory createSizeBoolChainCutCode
Ancestors
  createSizeCutOpens createSizeCutCode exprLowering compileEnv emitHelper
  venomInst context list pair pred_set

Theorem compile_bool_chain_ops_cut_code:
  (!e s. create_cut_code {} s (SND (lower_value f ce (BaseT BoolT) e s))) ==>
  !es a. create_cut_code {exit_lbl} a
    (SND (compile_bool_chain_ops f ce is_and result exit_lbl es a))
Proof
  strip_tac >> Induct_on `es`
  >- simp[compile_bool_chain_ops_def] >>
  Cases_on `es`
  >- (rpt gen_tac >> pure_rewrite_tac[compile_bool_chain_ops_def, comp_ignore_bind_def] >>
      match_mp_tac create_cut_code_bind_all >>
      conj_tac >- simp[create_cut_code_widen_empty] >>
      rpt gen_tac >> BETA_TAC >> match_mp_tac create_cut_code_bind_all >>
      simp[create_cut_code_emit_inst, create_cut_targets_def]) >>
  rpt gen_tac >> pure_rewrite_tac[compile_bool_chain_ops_def, comp_ignore_bind_def] >>
  match_mp_tac create_cut_code_bind_all >>
  conj_tac >- simp[create_cut_code_widen_empty] >>
  rpt gen_tac >> BETA_TAC >> match_mp_tac create_cut_code_bind_all >>
  conj_tac
  >- (Cases_on `is_and` >> simp[] >> match_mp_tac create_cut_code_bind_all >>
      simp[] >> rpt gen_tac >> BETA_TAC >>
      match_mp_tac create_cut_code_bind_all >> simp[]) >>
  qx_gen_tac `lbls` >> qx_gen_tac `s` >> BETA_TAC >>
  qabbrev_tac `pending = {exit_lbl; FST lbls; SND lbls}` >>
  match_mp_tac (Q.INST [`opened` |-> `{SND lbls} UNION {FST lbls}`,
                       `pending` |-> `pending`] create_cut_opens_close) >>
  reverse conj_tac >- simp[Abbr `pending`, SUBSET_DEF] >>
  match_mp_tac create_cut_opens_bind_keep >> conj_tac
  >- (Cases_on `is_and` >> simp[create_cut_code_emit_inst, create_cut_targets_def,
                               Abbr `pending`, DISJ_IMP_THM]) >>
  rpt gen_tac >> BETA_TAC >> match_mp_tac create_cut_opens_bind >> conj_tac
  >- simp[create_cut_opens_block] >>
  BETA_TAC >> match_mp_tac create_cut_opens_bind_keep >> conj_tac
  >- simp[create_cut_code_emit_inst, create_cut_targets_def] >>
  rpt gen_tac >> BETA_TAC >> match_mp_tac create_cut_opens_bind_keep >> conj_tac
  >- simp[create_cut_code_emit_inst, create_cut_targets_def, Abbr `pending`] >>
  rpt gen_tac >> BETA_TAC >>
  match_mp_tac (REWRITE_RULE [UNION_EMPTY, EMPTY_SUBSET, AND_CLAUSES]
                  (Q.INST [`opened2` |-> `{}`] create_cut_opens_bind)) >>
  conj_tac >- simp[create_cut_opens_block] >>
  BETA_TAC >> irule create_cut_code_weaken >> qexists_tac `{exit_lbl}` >>
  simp[Abbr `pending`, SUBSET_DEF]
QED

(* Bound-label preservation for the short-circuit chain compiler. *)
Theory boundLabelsBoolChainOps
Ancestors
  exprLowering boundLabelRules compileEnv list

Theorem bound_labels_compile_bool_chain_ops:
  (!e t. MEM e es /\ EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
    EVERY P (MAP (\bb. bb.bb_label)
      (all_blocks (SND (lower_value f ce (BaseT BoolT) e t))))) /\
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_bool_chain_ops f ce is_and result exit_lbl es s))))
Proof
  qid_spec_tac `s` >> Induct_on `es`
  >- simp[compile_bool_chain_ops_def, comp_return_def] >>
  rpt gen_tac >> strip_tac >>
  `!t. EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
     EVERY P (MAP (\bb. bb.bb_label)
       (all_blocks (SND (compile_bool_chain_ops f ce is_and result exit_lbl es t))))`
    by (rpt strip_tac >> first_x_assum irule >> simp[] >> metis_tac[MEM]) >>
  Cases_on `es` >> simp[Once compile_bool_chain_ops_def] >>
  irule bound_labels_bind >>
  (reverse conj_tac >- (rpt strip_tac >> first_x_assum irule >> simp[])) >>
  rpt strip_tac >> BETA_TAC
  >- (irule bound_labels_ignore_bind >> simp[bound_labels_emit_inst]) >>
  irule bound_labels_bind_result >> simp[] >>
  qexists_tac `\ls t. P (FST ls) /\ P (SND ls) /\
                         EVERY P (MAP (\bb. bb.bb_label) (all_blocks t))` >>
  BETA_TAC >> conj_tac
  >- (rpt strip_tac >>
      rpt (irule bound_labels_ignore_bind >>
           conj_tac >- simp[bound_labels_emit_inst, bound_labels_new_block] >>
           rpt strip_tac) >>
      first_x_assum irule >> simp[]) >>
  Cases_on `is_and` >> rpt strip_tac >> simp[comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  metis_tac[bound_labels_fresh_label]
QED

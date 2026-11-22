(* Reserved-operand exclusion for the short-circuit chain compiler. *)
Theory runtimeLabelBoolChain
Ancestors
  runtimeLabelPrimitives runtimeLabelInvariant exprLowering compileEnv

Theorem rb_compile_bool_chain_ops_for:
  !es. rb_operand_ok_for source_checks (Label exit_lbl) /\
       (!e. MEM e es ==>
         rb_step_for source_checks (rb_operand_ok_for source_checks)
           (lower_value cfn ce (BaseT BoolT) e)) ==>
    rb_step_for source_checks (K T)
      (compile_bool_chain_ops cfn ce is_and result exit_lbl es)
Proof
  Induct >- simp[compile_bool_chain_ops_def, rb_step_return_for] >>
  rpt gen_tac >> strip_tac >> Cases_on `es` >>
  simp[Once compile_bool_chain_ops_def] >>
  irule rb_step_bind_for >> qexists_tac `rb_operand_ok_for source_checks` >>
  BETA_TAC >>
  (reverse conj_tac >- (first_x_assum irule >> simp[])) >>
  gen_tac >> strip_tac
  >- (irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >>
      simp[rb_emit_inst_for]) >>
  irule rb_step_bind_for >>
  qexists_tac `\lbls. rb_operand_ok_for source_checks (Label (FST lbls)) /\
                     rb_operand_ok_for source_checks (Label (SND lbls))` >>
  BETA_TAC >> reverse conj_tac
  >- (Cases_on `is_and` >> simp[] >>
      ntac 2 (ho_match_mp_tac rb_bind_fresh_label_for >> BETA_TAC >>
              gen_tac >> strip_tac) >>
      ho_match_mp_tac rb_step_return_for >> gvs[]) >>
  gen_tac >> strip_tac >>
  ntac 5 (irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >>
          (conj_tac >- (Cases_on `is_and` >>
             simp[rb_emit_inst_for, rb_new_block_for]))) >>
  first_x_assum irule >> simp[]
QED

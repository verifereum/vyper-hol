Theory symbolicSourceCompilerStmtFrame
Ancestors symbolicSourceCompilerFrame stmtLowering compileEnv

Theorem symbolic_frame_log_save_arg:
  (!c t v. symbolic_frame R (compile_materialize_vv c t v)) ==>
  symbolic_frame R (compile_log_save_arg cenv ty op es)
Proof
  strip_tac >> simp[compile_log_save_arg_def] >> IF_CASES_TAC >> simp[]
QED

Theorem symbolic_frame_log_eval_all:
  (!c t e. symbolic_frame R (lower_value compile_expr c t e)) /\
  (!c t v. symbolic_frame R (compile_materialize_vv c t v)) ==>
  !es cenv. symbolic_frame R (compile_log_eval_all cenv es)
Proof
  strip_tac >> Induct >> simp[compile_log_eval_all_def, comp_ignore_bind_def] >>
  rpt gen_tac >>
  rpt (BETA_TAC >> irule symbolic_frame_bind >> reverse conj_tac
       >- simp[symbolic_frame_log_save_arg] >> gen_tac) >> simp[]
QED

Theorem symbolic_frame_log_topic_ops:
  (!op b. symbolic_frame R (compile_encode_log_topic op b)) ==>
  !ops. symbolic_frame R (compile_log_topic_ops ops)
Proof
  strip_tac >> Induct >> simp[compile_log_topic_ops_def, comp_ignore_bind_def] >>
  rpt gen_tac >>
  rpt (BETA_TAC >> irule symbolic_frame_bind >> reverse conj_tac >- simp[] >> gen_tac) >> simp[]
QED

Theorem symbolic_frame_log_store_data:
  (!op args. symbolic_frame R (emit_op op args)) /\
  (!op args. symbolic_frame R (emit_void op args)) /\
  (!c v b t s. symbolic_frame R (compile_store_memory c v b t s)) ==>
  !ops tys cenv buf off.
    symbolic_frame R (compile_log_store_data cenv ops tys buf off)
Proof
  strip_tac >> Induct >> Cases_on `tys` >>
  simp[compile_log_store_data_def, comp_ignore_bind_def] >>
  rpt gen_tac >>
  rpt (BETA_TAC >> irule symbolic_frame_bind >> reverse conj_tac >- simp[] >> gen_tac) >> simp[]
QED

Theorem symbolic_frame_tuple_load_all:
  (!op args. symbolic_frame R (emit_op op args)) /\
  (!op b. symbolic_frame R (compile_load_memory op b)) ==>
  !tys cenv op off. symbolic_frame R (compile_tuple_load_all cenv op tys off)
Proof
  strip_tac >> Induct >> simp[compile_tuple_load_all_def, comp_ignore_bind_def] >>
  rpt gen_tac >>
  rpt (BETA_TAC >> irule symbolic_frame_bind >> reverse conj_tac >- simp[] >> gen_tac) >> simp[]
QED

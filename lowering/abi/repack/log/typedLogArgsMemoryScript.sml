(* TOP-LEVEL: saved Log values and their separation bounds survive an
   unchanged RAM image and unchanged argument operands. APIs:
   log_args_rel_memory_frame, log_args_safe_operand_frame. *)
Theory typedLogArgsMemory
Ancestors
  typedLogArgs valueLoadProps valueEncoding compileEnv venomState list pair words

Theorem log_args_rel_memory_frame:
  !args atvs values before after.
    after.vs_memory = before.vs_memory /\
    EVERY (\arg. eval_operand (FST arg) after = eval_operand (FST arg) before) args ==>
    (log_args_rel args atvs values after <=> log_args_rel args atvs values before)
Proof
  Induct_on `args`
  >- (rpt gen_tac >> Cases_on `atvs` >> Cases_on `values` >> simp[log_args_rel_def]) >>
  MAP_EVERY qx_gen_tac [`arg`, `atvs`, `values`, `before`, `after`] >>
  Cases_on `arg` >> Cases_on `atvs` >> Cases_on `values` >>
  simp_tac (srw_ss()) [log_args_rel_def] >> strip_tac >>
  rename1 `log_args_rel args rest_tvs rest_values after` >>
  qpat_x_assum `!atvs values before after. _`
    (qspecl_then [`rest_tvs`, `rest_values`, `before`, `after`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  asm_simp_tac bool_ss [lowered_value_rel_def]
QED

Theorem log_args_safe_operand_frame:
  !args atvs before after dst byte_count.
    EVERY (\arg. eval_operand (FST arg) after = eval_operand (FST arg) before) args ==>
    (log_args_safe args atvs after dst byte_count <=> log_args_safe args atvs before dst byte_count)
Proof
  Induct_on `args`
  >- (rpt gen_tac >> Cases_on `atvs` >> simp[log_args_safe_def]) >>
  MAP_EVERY qx_gen_tac [`arg`, `atvs`, `before`, `after`, `dst`, `byte_count`] >>
  Cases_on `arg` >> Cases_on `atvs` >>
  simp_tac (srw_ss()) [log_args_safe_def] >> strip_tac >>
  rename1 `log_args_safe args rest_tvs after dst byte_count` >>
  qpat_x_assum `!atvs before after dst byte_count. _`
    (qspecl_then [`rest_tvs`, `before`, `after`, `dst`, `byte_count`] mp_tac) >>
  impl_tac >- first_assum MATCH_ACCEPT_TAC >> DISCH_TAC >>
  asm_simp_tac bool_ss [log_arg_safe_def]
QED

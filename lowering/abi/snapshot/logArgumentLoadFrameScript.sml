(* TOP-LEVEL: a source argument load retains saved values and their memory
   separation. Operand lifetimes advance monotonically, and the newly saved
   value extends the source-order argument prefix. *)
Theory logArgumentLoadFrame
Ancestors
  typedLogArgs typedLogArgsMemory abiFieldOperands valueLoadProps
  compileEnv venomState list pair

Theorem log_args_load_frame:
  !args atvs values bound before after.
    log_args_rel args atvs values before /\
    EVERY (\arg. abi_operand_before bound (FST arg)) args /\
    after.vs_memory = before.vs_memory /\
    (!arg_op. abi_operand_before bound arg_op ==> eval_operand arg_op after = eval_operand arg_op before) ==>
    log_args_rel args atvs values after /\
    (!dst byte_count. log_args_safe args atvs after dst byte_count = log_args_safe args atvs before dst byte_count)
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY (\arg. eval_operand (FST arg) after = eval_operand (FST arg) before) args` by
    (simp_tac bool_ss [EVERY_MEM] >> qx_gen_tac `arg` >> DISCH_TAC >>
     qpat_x_assum `!arg_op. _` irule >> fs[EVERY_MEM]) >>
  drule_all log_args_rel_memory_frame >> DISCH_TAC >>
  drule_all log_args_safe_operand_frame >> DISCH_TAC >> simp[]
QED

Theorem log_args_before_mono:
  !args bound next_var.
    EVERY (\arg. abi_operand_before bound (FST arg)) args /\ bound <= next_var ==>
    EVERY (\arg. abi_operand_before next_var (FST arg)) args
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [EVERY_MEM] >> qx_gen_tac `arg` >> DISCH_TAC >>
  irule abi_operand_before_mono >> qexists_tac `bound` >> fs[EVERY_MEM]
QED

Theorem log_args_rel_snoc:
  !args atvs values op ty tv v ss.
    log_args_rel args atvs values ss /\ lowered_value_rel ty tv v op ss ==>
    log_args_rel (args ++ [(op,ty)]) (atvs ++ [tv]) (values ++ [v]) ss
Proof
  Induct_on `args`
  >- (rpt gen_tac >> Cases_on `atvs` >> Cases_on `values` >> simp[log_args_rel_def]) >>
  MAP_EVERY qx_gen_tac [`arg`, `atvs`, `values`, `op`, `ty`, `tv`, `v`, `ss`] >>
  Cases_on `arg` >> Cases_on `atvs` >> Cases_on `values` >> simp[log_args_rel_def] >>
  strip_tac >> first_x_assum drule_all >> simp[]
QED

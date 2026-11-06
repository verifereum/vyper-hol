(* TOP-LEVEL: actual allocation cuts split saved-argument freshness.
   A copied subfield's frame preserves saved arguments outside its parent. *)
Theory typedLogRanges
Ancestors
  typedLogArgs typedLogArgsFrames typedCopyOperandFrames typedFieldsMemory
  typedSArrayDynInvariant valueEncoding abiStaticLoopCode
  compileEnv venomState venomInst list arithmetic

Theorem log_args_allocation_split:
  !ops buf var_start var_mid var_end.
    var_start <= var_mid /\ var_mid <= var_end /\
    EVERY (\name. buf <> Var name) (compiler_var_names var_start (var_end - var_start)) /\
    log_args_avoid ops (compiler_var_names var_start (var_end - var_start)) ==>
    EVERY (\name. buf <> Var name) (compiler_var_names var_start (var_mid - var_start)) /\
    log_args_avoid ops (compiler_var_names var_start (var_mid - var_start)) /\
    EVERY (\name. buf <> Var name) (compiler_var_names var_mid (var_end - var_mid)) /\
    log_args_avoid ops (compiler_var_names var_mid (var_end - var_mid))
Proof
  rpt gen_tac >> strip_tac >> rpt conj_tac >|
  [mp_tac (Q.SPECL [`buf`, `var_start`, `var_start`, `var_mid`, `var_end`]
     compiler_operand_avoid_interval) >> simp[],
   mp_tac (Q.SPECL [`ops`, `var_start`, `var_start`, `var_mid`, `var_end`]
     log_args_avoid_interval) >> simp[],
   mp_tac (Q.SPECL [`buf`, `var_start`, `var_mid`, `var_end`, `var_end`]
     compiler_operand_avoid_interval) >> simp[],
   mp_tac (Q.SPECL [`ops`, `var_start`, `var_mid`, `var_end`, `var_end`]
     log_args_avoid_interval) >> simp[]]
QED

Theorem log_args_frame_contained:
  !ops tvs vs before after parent_tv parent_off inner_tv inner_off names.
    log_args_rel ops tvs vs before /\
    log_args_safe ops tvs before parent_off (type_memory_size parent_tv) /\
    log_args_avoid ops names /\
    array_copy_frame inner_tv 1 inner_off before.vs_memory after.vs_memory /\
    parent_off <= inner_off /\
    inner_off + type_memory_size inner_tv <= parent_off + type_memory_size parent_tv /\
    (!arg_op. EVERY (\name. arg_op <> Var name) names ==>
      eval_operand arg_op after = eval_operand arg_op before) ==>
    log_args_rel ops tvs vs after /\
    log_args_safe ops tvs after parent_off (type_memory_size parent_tv)
Proof
  rpt gen_tac >> strip_tac >>
  `array_copy_frame parent_tv 1 parent_off before.vs_memory after.vs_memory` by
    (mp_tac (Q.SPECL [`inner_tv`, `1`, `inner_off`, `parent_tv`, `1`, `parent_off`,
       `before.vs_memory`, `after.vs_memory`] array_copy_frame_contained) >>
     impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, simp[]]) >> simp[]) >>
  mp_tac (Q.SPECL [`ops`, `tvs`, `vs`, `before`, `after`, `parent_tv`, `1`, `parent_off`, `names`]
    log_args_frame) >> simp_tac bool_ss [MULT_CLAUSES] >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]
QED

Theorem log_target_cons_bounds:
  !ftv ftvs dst_off limit.
    dst_off + type_memory_size (TupleTV (ftv::ftvs)) < limit ==>
    dst_off + type_memory_size ftv < limit /\
    dst_off + type_memory_size ftv + type_memory_size (TupleTV ftvs) < limit
Proof
  simp_tac bool_ss [type_memory_size_def] >> decide_tac
QED

(* Aligned compiler projections for staging one held head and its tail. *)
Theory bodyIntCallStageList
Ancestors
  bodyIntCallStageTransport bodyIntCallStageCompile exprLowering
  exprLoweringProps bodyIntCallCompilerStaging fragExec context

Theorem intcall_stage_word_parts:
  compile_stage_intcall_args ce (vv::vals) (T::flags) (ty::tys) sa = (ops,sn) ==>
  ?op sm rest.
    unwrap_value ce vv sa = (op,sm) /\
    compile_stage_intcall_args ce vals flags tys sm = (rest,sn) /\
    ops = op::rest
Proof
  simp[compile_stage_intcall_args_def, compileEnvTheory.comp_bind_def,
       compileEnvTheory.comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[]
QED

Theorem intcall_stage_memory_parts:
  vv_type vv = ty /\
  compile_stage_intcall_args ce (vv::vals) (F::flags) (ty::tys) sa = (ops,sn) ==>
  ?op sm buf si sj rest.
    unwrap_value ce vv sa = (op,sm) /\
    compile_alloc_buffer (MAX 32 (type_memory_bytes ce ty)) sm = (buf,si) /\
    compile_store_memory ce op buf.buf_operand ty ty si = ((),sj) /\
    compile_stage_intcall_args ce vals flags tys sj = (rest,sn) /\
    ops = buf.buf_operand::rest
Proof
  strip_tac >>
  gvs[intcall_stage_memory_cons, compileEnvTheory.comp_bind_def,
      compileEnvTheory.comp_return_def, compileEnvTheory.comp_ignore_bind_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[]
QED

Theorem staged_arg_lower_frontier:
  staged_arg ce func es sm sn s d /\ sa.cs_next_id <= sm.cs_next_id ==>
  staged_arg ce func es sa sn s d
Proof
  PairCases_on `d` >> simp[bodyIntCallStageOwnedTheory.staged_arg_def] >>
  rpt strip_tac >> qexists_tac `w` >> simp[] >>
  Cases_on `d3` >> gvs[] >>
  qexistsl_tac [`inst.inst_id`,`off`,`sz`] >> simp[] >>
  conj_tac >- metis_tac[] >> gvs[]
QED

Theorem intcall_stage_mono:
  compile_stage_intcall_args ce vals flags tys sa = (ops,sn) ==>
  ci_mono sa sn
Proof
  strip_tac >>
  qspecl_then [`ce`,`vals`,`flags`,`tys`,`0`,`sa`] mp_tac
    intcall_interval_stage_intcall_args >>
  simp[bodyIntCallCompilerIntervalTheory.intcall_compiler_interval_def]
QED

Theorem staged_args_lower_frontier:
  EVERY (bodyIntCallStageOwned$staged_arg ce func es sm sn s) ds /\
  sa.cs_next_id <= sm.cs_next_id ==>
  EVERY (bodyIntCallStageOwned$staged_arg ce func es sa sn s) ds
Proof
  simp[listTheory.EVERY_MEM] >> metis_tac[staged_arg_lower_frontier]
QED

Theorem intcall_stage_word_code:
  unwrap_value ce vv sa = (op,sm) /\
  compile_stage_intcall_args ce vals flags tys sm = (rest,sn) /\
  fn_has_code sa sn func ==>
  ci_mono sa sm /\ ci_mono sm sn /\
  fn_has_code sa sm func /\ fn_has_code sm sn func
Proof
  strip_tac >>
  `ci_mono sa sm` by
    (mp_tac (Q.SPECL [`ce`,`vv`,`sa`] ci_mono_unwrap_value) >> simp[]) >>
  drule intcall_stage_mono >> strip_tac >>
  gvs[ci_mono_def] >> metis_tac[fn_has_code_split]
QED

Theorem intcall_stage_memory_code:
  unwrap_value ce vv sa = (op,sm) /\
  compile_alloc_buffer cap sm = (buf,si) /\
  compile_store_memory ce op buf.buf_operand ty ty si = ((),sj) /\
  compile_stage_intcall_args ce vals flags tys sj = (rest,sn) /\
  fn_has_code sa sn func ==>
  ci_mono sa sm /\ ci_mono sm si /\ ci_mono si sj /\ ci_mono sj sn /\
  fn_has_code sa sm func /\ fn_has_code sm si func /\
  fn_has_code si sj func /\ fn_has_code sj sn func
Proof
  strip_tac >>
  `ci_mono sa sm` by
    (mp_tac (Q.SPECL [`ce`,`vv`,`sa`] ci_mono_unwrap_value) >> simp[]) >>
  `ci_mono sm si` by
    (mp_tac (Q.SPECL [`cap`,`sm`] ci_mono_compile_alloc_buffer) >> simp[]) >>
  `ci_mono si sj` by
    (mp_tac (Q.SPECL [`ce`,`op`,`buf.buf_operand`,`ty`,`ty`,`si`]
       ci_mono_compile_store_memory) >> simp[]) >>
  drule intcall_stage_mono >> strip_tac >>
  gvs[ci_mono_def] >>
  metis_tac[fn_has_code_split, compileEnvTheory.cs_extends_trans]
QED

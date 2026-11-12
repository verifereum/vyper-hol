(* Aligned compiler projections for staging one held head and its tail. *)
Theory bodyIntCallStageList
Ancestors
  bodyIntCallStageTransport bodyIntCallStageCompile exprLowering
  exprLoweringProps bodyIntCallCompilerStaging fragExec context

(* RESTATED (train 17): 0.5.0b1 per-argument staging *)
Theorem intcall_stage_word_parts:
  compile_stage_intcall_args cfn ce (e::es) (T::flags) (ty::tys) sa = (ops,sn) ==>
  ?vv s1 op sm rest.
    cfn ce (expr_type e) e sa = (vv,s1) /\
    unwrap_value ce vv s1 = (op,sm) /\
    compile_stage_intcall_args cfn ce es flags tys sm = (rest,sn) /\
    ops = op::rest
Proof
  cheat
QED

(* RESTATED (train 17): 0.5.0b1 per-argument staging *)
Theorem intcall_stage_memory_parts:
  compile_stage_intcall_args cfn ce (e::es) (F::flags) (ty::tys) sa = (ops,sn) ==>
  ?vv s1 buf s2 op s3 s4 rest.
    cfn ce (expr_type e) e sa = (vv,s1) /\
    compile_alloc_buffer (MAX 32 (type_memory_bytes ce ty)) s1 = (buf,s2) /\
    unwrap_value ce vv s2 = (op,s3) /\
    compile_store_memory ce op buf.buf_operand ty (vv_type vv) s3 = ((),s4) /\
    compile_stage_intcall_args cfn ce es flags tys s4 = (rest,sn) /\
    ops = buf.buf_operand::rest
Proof
  cheat
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


Theorem staged_args_lower_frontier:
  EVERY (bodyIntCallStageOwned$staged_arg ce func es sm sn s) ds /\
  sa.cs_next_id <= sm.cs_next_id ==>
  EVERY (bodyIntCallStageOwned$staged_arg ce func es sa sn s) ds
Proof
  simp[listTheory.EVERY_MEM] >> metis_tac[staged_arg_lower_frontier]
QED

(* RESTATED (train 17): 0.5.0b1 per-argument staging *)
Theorem intcall_stage_word_code:
  (!ce' ty' e' s'. ci_mono s' (SND (cfn ce' ty' e' s'))) /\
  cfn ce (expr_type e) e sa = (vv,s1) /\
  unwrap_value ce vv s1 = (op,sm) /\
  compile_stage_intcall_args cfn ce es flags tys sm = (rest,sn) /\
  fn_has_code sa sn func ==>
  ci_mono sa s1 /\ ci_mono s1 sm /\ ci_mono sm sn /\
  fn_has_code sa s1 func /\ fn_has_code s1 sm func /\ fn_has_code sm sn func
Proof
  cheat
QED

(* RESTATED (train 17): 0.5.0b1 per-argument staging *)
Theorem intcall_stage_memory_code:
  (!ce' ty' e' s'. ci_mono s' (SND (cfn ce' ty' e' s'))) /\
  cfn ce (expr_type e) e sa = (vv,s1) /\
  compile_alloc_buffer cap s1 = (buf,s2) /\
  unwrap_value ce vv s2 = (op,s3) /\
  compile_store_memory ce op buf.buf_operand ty sty s3 = ((),s4) /\
  compile_stage_intcall_args cfn ce es flags tys s4 = (rest,sn) /\
  fn_has_code sa sn func ==>
  ci_mono sa s1 /\ ci_mono s1 s2 /\ ci_mono s2 s3 /\ ci_mono s3 s4 /\
  ci_mono s4 sn /\
  fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\ fn_has_code s2 s3 func /\
  fn_has_code s3 s4 func /\ fn_has_code s4 sn func
Proof
  cheat
QED

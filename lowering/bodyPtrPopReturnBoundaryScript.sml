Theory bodyPtrPopReturnBoundary
Ancestors
  exprLowering compileEnv stmtSimForParts context emitHelper

(* lower_value_int_lit already supplies the scalar computational boundary;
   reuse it rather than duplicating that theorem. *)
Theorem pop_literal_stack_no_emit:
  compile_literal_vv ty l sa = (StackValue t (Lit w),sb) ==> sb = sa
Proof
  Cases_on `l` >> simp[compile_literal_vv_def, comp_return_def]
  >- (Cases_on `b` >> simp[compile_literal_vv_def, comp_return_def])
  >- (Cases_on `ty` >> simp[comp_bind_def, comp_return_def] >>
      pairarg_tac >> simp[]) >>
  Cases_on `ty` >> simp[comp_return_def] >>
  Cases_on `b` >> simp[comp_return_def] >>
  Cases_on `b'` >> simp[comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[]
QED

Theorem pop_ptr_load_variable:
  compile_ptr_load ctor imm loc p sa = (op,sb) ==> ?x. op = Var x
Proof
  Cases_on `ctor` >> Cases_on `imm` >> Cases_on `loc` >>
  simp[compile_ptr_load_def, compile_imm_load_word_def, emit_op_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[]
QED

Theorem pop_unwrap_word_variable:
  unwrap_value ce (LocatedValue ty p) sa = (op,sb) /\ is_word_type ty ==>
  ?x. op = Var x
Proof
  simp[unwrap_value_def] >> strip_tac >>
  metis_tac[pop_ptr_load_variable]
QED

Theorem pop_lower_literal_origin:
  lower_value cfn ce ty e sa = (Lit w,sb) /\
  (!vt p sm. cfn ce ty e sa = (LocatedValue vt p,sm) ==> is_word_type vt) ==>
  ?vt. cfn ce ty e sa = (StackValue vt (Lit w),sb)
Proof
  simp[lower_value_def, comp_bind_def] >> pairarg_tac >> simp[] >>
  strip_tac >> Cases_on `vv` >> gvs[unwrap_value_def, comp_return_def] >>
  drule pop_ptr_load_variable >> simp[]
QED

Theory bodyPtrPopReturnBoundary
Ancestors
  exprLowering compileEnv stmtSimForParts context emitHelper bodyPtrPopWindow

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

(* Arbitrary incoming-state probe, not a reachable compiled-unit claim.
   The scalar equation is the existing lower_value_int_lit at n=1. *)
Theorem pop_literal_one_inherits_tail:
  sa.cs_current_insts =
    [mk_inst i0 (if tr then TLOAD else SLOAD) [Var h] [a];
     mk_inst i1 ISZERO [Var a] [b];
     mk_inst i2 ISZERO [Var b] [c];
     mk_inst i3 ASSERT [Var c] []] /\
  lower_value compile_expr ce ty (Literal ety (IntL 1)) sa = (op,sb) ==>
  op = Lit 1w /\ sb = sa /\ tail4 sb.cs_current_insts = sa.cs_current_insts
Proof
  simp[lower_value_int_lit] >> strip_tac >> gvs[tail4_short] >>
  EVAL_TAC >> `~(1:int < 0)` by intLib.ARITH_TAC >> simp[]
QED

(* Return-origin source assessment (not a universal theorem):
   exprLoweringScript locations in current source:
   1453-1481 compile_literal_vv: scalar/fixed-byte/fallback bytes literals
     preserve state; dynamic bytes and strings return LocatedValue.
   1490-1500 compile_name_vv absent local: StackValue Lit0, no emission.
   2996-2999 FlagMember: literal mask, no emission (can be Lit1).
   3000-3009 absent TopLevelName: INVALID then Lit0; not state preserving.
   3341-3353 type builtins: word Empty/MaxValue/MinValue/Epsilon are literal
     returns without emission. Convert zero-capacity bytes/string at 3315-3322
     returns Lit0 AFTER recursive lower_value, so literal return need not
     imply no emitted code or no inherited residual.
   3464 unsupported simple-builtin default: Lit0, state unchanged.

   Call dispatch is not a no-emission interface:
   2636-2667 internal calls lower arguments, stage them and emit INVOKE;
     no-return-buffer path gives StackValue Lit0 after INVOKE.
   2672-2673, 2732-2735, 2761-2762, 2787-2797 malformed/unsupported paths:
     INVALID then Lit0. Valid Send 2717-2731 gives Lit0 after CALL/ASSERT.
   ExtCall 2706-2716 and RawCall 2754-2760 pass through helper result operands;
     those helpers require their own return-origin audit, not an assumption.
   default_ret is passed by the call dispatch but ExtCall defaults are lowered
     through compile_ext_call_kwargs; they do not justify state preservation.

   Indirect literal paths include empty list membership: 3030-3054 lowers
   needle/elements before compile_list_membership_{in,notin}; empty notin at
   717-719 returns Lit1 with no additional code, inheriting needle's suffix.
   compile_binop fallback 674-677 emits INVALID then Lit0. Generic compile
   helpers can also pass through callback operands; the word unwrap boundary
   does not classify their source origin, only their final value constructor.

   Hence literal-result-no-emission is already false at call and Convert
   boundaries; Lit1-specific provenance also needs empty-notin and type/flag
   constants plus propagation cases. The checked scalar probe exhibits an
   actual source expression preserving an arbitrary incoming guarded tail.
   It does NOT show that such an incoming tail is reachable from supported
   initial compilation. A viable invariant must distinguish inherited tail
   from newly created tail and relate its loaded variable to the returned
   operand and earlier left operand. Neither these inspections nor the word
   unwrap inversion supplies that global relational invariant. *)

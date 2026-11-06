Theory bodyPtrPopWindowBoundary
Ancestors
  bodyPtrPopGuardedWindow bodyPtrPopWindow compileEnv emitHelper exprLowering
  venomInst context list rich_list

Theorem pop_window_emit:
  emit i sa = (u,sb) ==>
  (occurs5 winp sb.cs_current_insts <=> occurs5 winp sa.cs_current_insts \/
    (4 <= LENGTH sa.cs_current_insts /\
     winp (tail4 sa.cs_current_insts ++ [i])))
Proof
  simp[emit_def] >> strip_tac >> gvs[occurs5_snoc]
QED

Theorem pop_window_new_block:
  new_block lbl sa = (old,sb) ==>
  ~occurs5 winp sb.cs_current_insts /\ tail4 sb.cs_current_insts = [] /\
  sb.cs_blocks =
    <|bb_label := sa.cs_current_bb; bb_instructions := sa.cs_current_insts|>
      :: sa.cs_blocks /\
  (occurs5 winp (HD sb.cs_blocks).bb_instructions <=>
   occurs5 winp sa.cs_current_insts)
Proof
  simp[new_block_def] >> strip_tac >> gvs[tail4_def]
QED

Theorem pop_window_unsafe_sub_full_word:
  256 <= type_bits ty /\
  compile_binop UnsafeSub x y ty bl el sa = (out,sb) ==>
  (occurs5 pop_guarded5 sb.cs_current_insts <=>
   occurs5 pop_guarded5 sa.cs_current_insts \/
   (?tr h a b c i0 i1 i2 i3.
     4 <= LENGTH sa.cs_current_insts /\
     tail4 sa.cs_current_insts =
       [mk_inst i0 (if tr then TLOAD else SLOAD) [Var h] [a];
        mk_inst i1 ISZERO [Var a] [b];
        mk_inst i2 ISZERO [Var b] [c];
        mk_inst i3 ASSERT [Var c] []] /\
     x = Var a /\ y = Lit 1w))
Proof
  strip_tac >>
  gvs[compile_binop_def, wrap_truncate_def, emit_op_def, comp_bind_def,
      comp_return_def, comp_ignore_bind_def, fresh_var_def, fresh_id_def, emit_def] >>
  simp[pop_guarded5_decrement_residual]
QED

(* This is an unrestricted compiler-interface collision, NOT a compiled-unit
   counterexample: an arbitrary incoming block is not necessarily reachable
   from supported source lowering. *)
Theorem pop_window_unsafe_sub_collision:
  sa.cs_current_insts =
    [mk_inst i0 (if tr then TLOAD else SLOAD) [Var h] [a];
     mk_inst i1 ISZERO [Var a] [b];
     mk_inst i2 ISZERO [Var b] [c];
     mk_inst i3 ASSERT [Var c] []] /\
  256 <= type_bits ty /\
  compile_binop UnsafeSub (Var a) (Lit 1w) ty bl el sa = (out,sb) ==>
  ~occurs5 pop_guarded5 sa.cs_current_insts /\
   occurs5 pop_guarded5 sb.cs_current_insts
Proof
  strip_tac >> drule_all pop_window_unsafe_sub_full_word >>
  simp[occurs5_short, tail4_short] >> metis_tac[]
QED

(* Boundary assessment (not universal producer exclusion).

   Exact residual R(x,y,s): exists tr,h,a,b,c,ids such that tail4 s is
   LOAD[Var h]->a; ISZERO a->b; ISZERO b->c; ASSERT c,
   LENGTH s >= 4, x=Var a, y=Lit 1. See the full-word theorem above.

   Actual bind sites:
   - stmtLowering 884-906: target ptr; cur <- LOAD dst; rhs <- lower_value e;
     res <- compile_binop UnsafeSub cur rhs; STORE dst res.
     Apply R(cur,rhs,state_after_rhs). It is not enough to know absence in
     state_after_rhs: the collision theorem shows why. Need a return-sensitive
     lowering invariant ruling out precisely R for those cur and rhs.
   - exprLowering 3071-3076: v1 <- lower_value e1; v2 <- lower_value e2;
     compile_binop UnsafeSub v1 v2. Apply R(v1,v2,state_after_e2).
     Operand-return facts are indispensable at both binds. No existing window
     theorem supplies these facts for lower_value. In particular it is unsafe
     to assume a returned literal implies no emitted code without a proof.

   SUB producer coverage table, inspected from actual defs (still unproved
   globally; local neighbors alone are not a source-language induction):
   Producer                         Immediate predecessor / remaining gap
   compile_safe_sub                 operand code / same residual as UnsafeSub;
                                    later overflow checks do not erase a window
   compile_binop UnsafeSub          operand code / R above; truncation after SUB
   builtinMath unsafe_sub           operand code / same gap in generic helper
   compile_dynarray_pop             ASSERT / root header Lit vs nested Var
   PrevHash, blockhash              NUMBER / local mismatch
   byte extraction                 left operand Lit 32 / operand mismatch
   compile_negate, abs, sign        left operand Lit 0 / operand mismatch
   uint-to-string positions         ADD (or Var right operand) / local mismatch
   compile_floor                   SLT / local mismatch
   create code_size                EXTCODESIZE / local mismatch
   range rounds                    fresh entry block then ASSIGN / local mismatch

   New-block resets current residual and preserves old instructions exactly,
   as checked above; emission obeys the exact snoc law. Unit packaging must
   preserve this per-block assertion, not concatenate blocks. Remaining work:
   prove return-sensitive invariants through supported expression/statement
   lowering, copies/conversions/ABI guards, calls and internal bodies, function
   entry/exit wrappers and final block packaging from initial_compile_state.
   This table and these primitive equations do not authorize that induction
   or de-risk universal containment by themselves. *)

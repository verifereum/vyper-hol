(*
 * Expression simulation: as_wei_value, floor, uint256_addmod,
 * uint256_mulmod and pow_mod256 (#636)
 *
 * The bodies of exprSimBuiltins' case lemmas for these five.  Each lowers
 * its operands with lower_value and then a straight-line fragment, so
 * exprSimWordArgs' compile_word_builtin_sim applies once the fragment meets
 * word_builtin_frag (compile_*_word_frag).  The forms on names
 * (compile_addmod_names, ...) lower each name as lower_value does.
 *
 * TOP-LEVEL:
 *   word_builtin_case      — expr_vv_case of the five from the operands'
 *                            exprs_case (exprSimHyps)
 *   word_modular_names_sim — expr_vv_ok of addmod, mulmod and pow_mod256
 *                            on names, from exprSim's compile_name_word_sim
 *   compile_modular_word_frag, compile_pow_mod256_word_frag,
 *   compile_as_wei_value_word_frag, compile_floor_word_frag — the fragments
 *
 * Helper:
 *   compile_expr_builtin_dispatch, lower_value_floor,
 *   lower_value_as_wei_value, lower_value_ternary_modular,
 *   lower_value_pow_mod256 — compile_expr's lowering of the five as
 *                            lower_word_args and the fragment
 *   compile_modular_run, compile_pow_mod256_run,
 *   compile_as_wei_value_int_run — the fragments' runs
 *   wb_args_ready_of_case, wb_args_ready_of_ok — wb_args_ready from the
 *                            operands' exprs_case, and from expr_sim_ok
 *   typed_word_args_shape  — wb_args_shape from expr_body_pre
 *   compile_typed_word_builtin_sim — compile_word_builtin_sim on typed
 *                            operands
 *
 * The operands' shape is exprSimOperators' lower_value_word_shape.
 *)

Theory exprSimWordBuiltins
Ancestors
  exprWordOperand
  exprSimSource
  exprSimHypsDefs
  exprSimStack
  list words integer_word vfmExecution valueEncoding loweringSlice
  vyperEvalExprPreservesScopesDom
   exprSimHyps exprSimOperators exprSimWordArgs exprLowering
  vyperTypeSystem vyperTyping vyperInterpreter vyperState vyperContext
  exprBopLowering builtinMath builtinMisc builtinSimple arithmeticProps
  compileEnv exprSimOps freshWrites fragExec varsExt exprLoweringProps
  venomExecSemantics venomState emitHelper emitHelperProps venomInst
  builtinProps
  exprSimNameWord
Libs
  stepInstBaseLib

(* ===== Operand types and the lowering of the five ===== *)

Theorem word_builtin_modular_types:
  !ty bt ts.
    (bt = AddMod \/ bt = MulMod \/ bt = PowMod256) ==>
    well_typed_builtin_app ty bt ts ==>
    ty = BaseT (UintT 256) /\
    ts = (if bt = PowMod256 then
            [BaseT (UintT 256); BaseT (UintT 256)]
          else [BaseT (UintT 256); BaseT (UintT 256); BaseT (UintT 256)])
Proof
  cheat
QED

Theorem compile_expr_unary_builtin:
  !cenv ty ann bt e sa.
    compile_expr cenv ty (Builtin ann bt [e]) sa =
    compile_builtin_dispatch cenv ann ty bt [e] sa
Proof
  cheat
QED

Theorem lower_value_floor:
  !cenv ty ann e sa op sb.
    lower_value compile_expr cenv ty (Builtin ann Floor [e]) sa = (op, sb) ==>
    ?x s1. lower_value compile_expr cenv ty e sa = (x, s1) /\
           compile_floor x 10000000000 s1 = (op, sb)
Proof
  cheat
QED

Theorem lower_value_ceil:
  !cenv ty ann e sa op sb.
    lower_value compile_expr cenv ty (Builtin ann Ceil [e]) sa = (op, sb) ==>
    ?x s1. lower_value compile_expr cenv ty e sa = (x, s1) /\
           compile_ceil x 10000000000 s1 = (op, sb)
Proof
  cheat
QED

Theorem compile_ceil_stack:
  !cenv ty ann e sa vv sb.
    compile_expr cenv ty (Builtin ann Ceil [e]) sa = (vv, sb) ==>
    ?op. vv = StackValue ann op
Proof
  cheat
QED

Theorem straight_fresh_ceil:
  !x d. straight_fresh (compile_ceil x d)
Proof
  cheat
QED

Theorem lower_value_as_wei_value:
  !cenv ty ann d e k sa op sb.
    expr_type e = BaseT (UintT k) /\
    lower_value compile_expr cenv ty (Builtin ann (AsWeiValue d) [e]) sa = (op, sb) ==>
    ?x s1. lower_value compile_expr cenv (expr_type e) e sa = (x, s1) /\
           compile_as_wei_value_int x (denomination_multiplier d) F s1 = (op, sb)
Proof
  cheat
QED



Theorem lower_value_name:
  !cenv ty ann id st.
    lower_value compile_expr cenv ty (Name ann id) st =
    comp_bind (compile_name_vv cenv ann id) (unwrap_value cenv) st
Proof
  cheat
QED

Theorem compile_ternary_modular_names_dispatch:
  !cenv ty ann bt aty a bty b mty m st.
    (bt = AddMod \/ bt = MulMod) ==>
    compile_expr cenv ty (Builtin ann bt [Name aty a; Name bty b; Name mty m]) st =
    compile_builtin_dispatch cenv ann ty bt [Name aty a; Name bty b; Name mty m] st
Proof
  cheat
QED

Theorem compile_powmod256_names_dispatch:
  !cenv ty ann aty a bty b st.
    compile_expr cenv ty (Builtin ann PowMod256 [Name aty a; Name bty b]) st =
    compile_builtin_dispatch cenv ann ty PowMod256 [Name aty a; Name bty b] st
Proof
  cheat
QED

Theorem compile_ternary_modular_dispatch:
  !cenv ty ann bt a b m st.
    (bt = AddMod \/ bt = MulMod) ==>
    compile_expr cenv ty (Builtin ann bt [a; b; m]) st =
    compile_builtin_dispatch cenv ann ty bt [a; b; m] st
Proof
  cheat
QED

Theorem compile_binary_modular_dispatch:
  !cenv ty ann a b st.
    compile_expr cenv ty (Builtin ann PowMod256 [a; b]) st =
    compile_builtin_dispatch cenv ann ty PowMod256 [a; b] st
Proof
  cheat
QED

Theorem lower_value_ternary_modular:
  !cenv ty ann bt a b m sa op sb.
    (bt = AddMod \/ bt = MulMod) /\
    lower_value compile_expr cenv ty (Builtin ann bt [a; b; m]) sa = (op, sb) ==>
    ?x s1 y s2 z s3.
      lower_value compile_expr cenv ty a sa = (x, s1) /\
      lower_value compile_expr cenv ty b s1 = (y, s2) /\
      lower_value compile_expr cenv ty m s2 = (z, s3) /\
      (if bt = AddMod then compile_addmod else compile_mulmod) x y z s3 = (op, sb)
Proof
  cheat
QED

Theorem lower_value_pow_mod256:
  !cenv ty ann a b sa op sb.
    lower_value compile_expr cenv ty (Builtin ann PowMod256 [a; b]) sa = (op, sb) ==>
    ?x s1 y s2.
      lower_value compile_expr cenv ty a sa = (x, s1) /\
      lower_value compile_expr cenv ty b s1 = (y, s2) /\
      compile_pow_mod256 x y s2 = (op, sb)
Proof
  cheat
QED

Theorem compile_word_builtin_dispatch_stack:
  !cenv ann ty bt args sa vv sb.
    (bt = Floor \/ (?d. bt = AsWeiValue d) \/
     bt = AddMod \/ bt = MulMod \/ bt = PowMod256) /\
    compile_builtin_dispatch cenv ann ty bt args sa = (vv, sb) ==>
    ?op. vv = StackValue ann op
Proof
  cheat
QED

Theorem compile_word_builtin_stack:
  !cenv ann ty bt args sa vv sb.
    (((bt = Floor \/ (?d. bt = AsWeiValue d)) /\ LENGTH args = 1) \/
     ((bt = AddMod \/ bt = MulMod) /\ LENGTH args = 3) \/
     (bt = PowMod256 /\ LENGTH args = 2)) /\
    compile_expr cenv ty (Builtin ann bt args) sa = (vv, sb) ==>
    ?op. vv = StackValue ann op
Proof
  cheat
QED

(* ===== Modular word fragments ===== *)
Theorem straight_fresh_compile_modular:
  !a b c.
    straight_fresh (compile_addmod a b c) /\
    straight_fresh (compile_mulmod a b c) /\
    straight_fresh (compile_pow_mod256 a b)
Proof
  cheat
QED

Theorem compile_modular_run:
  !is_mul a b c sa op sb ss va vb vc.
    (if is_mul then compile_mulmod else compile_addmod) a b c sa = (op, sb) /\
    eval_operand a ss = SOME va /\ eval_operand b ss = SOME vb /\
    eval_operand c ss = SOME vc ==>
    (vc <> 0w ==>
      ?ss'. run_inst_seq (emitted_insts sa sb) ss = OK ss' /\
        eval_operand op ss' = SOME ((if is_mul then mulmod else addmod) va vb vc)) /\
    (vc = 0w ==>
      ?ss'. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort ss')
Proof
  cheat
QED

Theorem compile_pow_mod256_run:
  !a b sa op sb ss va vb.
    compile_pow_mod256 a b sa = (op, sb) /\
    eval_operand a ss = SOME va /\ eval_operand b ss = SOME vb ==>
    ?ss'. run_inst_seq (emitted_insts sa sb) ss = OK ss' /\
      eval_operand op ss' = SOME (word_exp va vb)
Proof
  cheat
QED

Theorem word_exp_modexp:
  !a b : bytes32.
    word_exp a b = n2w (modexp (w2n a) (w2n b) (dimword (:256)) 1)
Proof
  cheat
QED

Theorem compile_modular_word_frag:
  !is_mul ctx func cenv cx es ann ts (a:bytes32) (b:bytes32) (c:bytes32).
    word_builtin_frag ctx func cenv cx
      (\xs. (if is_mul then compile_mulmod else compile_addmod)
               (EL 0 xs) (EL 1 xs) (EL 2 xs))
      (builtin_result cx es.accounts ann (if is_mul then MulMod else AddMod) ts
         [IntV (&w2n a); IntV (&w2n b); IntV (&w2n c)])
      [IntV (&w2n a); IntV (&w2n b); IntV (&w2n c)] es
Proof
  cheat
QED

Theorem compile_pow_mod256_word_frag:
  !ctx func cenv cx es ann ts (a:bytes32) (b:bytes32).
    word_builtin_frag ctx func cenv cx
      (\xs. compile_pow_mod256 (EL 0 xs) (EL 1 xs))
      (builtin_result cx es.accounts ann PowMod256 ts
         [IntV (&w2n a); IntV (&w2n b)])
      [IntV (&w2n a); IntV (&w2n b)] es
Proof
  cheat
QED

Theorem uint_value_word_rep:
  !bits v. value_has_type (BaseTV (UintT bits)) v /\ bits <= 256 ==>
    v = IntV (&w2n (val_to_w256 v))
Proof
  cheat
QED

Theorem compile_modular_typed_frag:
  !is_mul ctx func cenv cx es ann ts v1 v2 v3.
    value_has_type (BaseTV (UintT 256)) v1 /\
    value_has_type (BaseTV (UintT 256)) v2 /\
    value_has_type (BaseTV (UintT 256)) v3 ==>
    word_builtin_frag ctx func cenv cx
      (\xs. (if is_mul then compile_mulmod else compile_addmod)
               (EL 0 xs) (EL 1 xs) (EL 2 xs))
      (builtin_result cx es.accounts ann (if is_mul then MulMod else AddMod) ts
         [v1; v2; v3]) [v1; v2; v3] es
Proof
  cheat
QED

Theorem compile_pow_mod256_typed_frag:
  !ctx func cenv cx es ann ts v1 v2.
    value_has_type (BaseTV (UintT 256)) v1 /\
    value_has_type (BaseTV (UintT 256)) v2 ==>
    word_builtin_frag ctx func cenv cx
      (\xs. compile_pow_mod256 (EL 0 xs) (EL 1 xs))
      (builtin_result cx es.accounts ann PowMod256 ts [v1; v2]) [v1; v2] es
Proof
  cheat
QED

(* ===== as_wei_value: unsigned scaling overflow ===== *)
Theorem mul_mod_div_no_overflow:
  !N x m:num. 0 < N /\ x < N /\ 0 < m /\ m < N ==>
    (((x * m MOD N) DIV x = m \/ x = 0) <=> x * m < N)
Proof
  cheat
QED

Theorem denomination_multiplier_bounds:
  !d. 0 < denomination_multiplier d /\ denomination_multiplier d < 2 ** 256
Proof
  cheat
QED

Theorem straight_fresh_as_wei_value_int:
  !x m. straight_fresh (compile_as_wei_value_int x m F)
Proof
  cheat
QED

Theorem word_mul_div_no_overflow:
  !(a:bytes32) m. 0 < m /\ m < dimword (:256) ==>
    (((a * n2w m) // a = n2w m \/ a = 0w) <=> w2n a * m < dimword (:256))
Proof
  cheat
QED

Theorem fresh_vars_wrt_not_fresh_at:
  !sa ss x w.
    fresh_vars_wrt sa ss /\ eval_operand x ss = SOME w ==>
    !z. x = Var z ==> not_fresh_at sa z
Proof
  cheat
QED

Theorem eval_operand_update_not_fresh:
  !sa a ss n w. (!z. a = Var z ==> not_fresh_at sa z) /\ sa.cs_next_var <= n ==>
    eval_operand a (update_var (STRING #"%" (toString n)) w ss) = eval_operand a ss
Proof
  cheat
QED

Theorem compile_as_wei_value_int_run:
  !a m sa op sb ss (va:bytes32).
    compile_as_wei_value_int a m F sa = (op,sb) /\
    eval_operand a ss = SOME va /\
    (!z. a = Var z ==> not_fresh_at sa z) /\
    0 < m /\ m < dimword (:256) ==>
    (w2n va * m < dimword (:256) ==>
      ?ss'. run_inst_seq (emitted_insts sa sb) ss = OK ss' /\
        eval_operand op ss' = SOME (va * n2w m)) /\
    (~(w2n va * m < dimword (:256)) ==>
      ?ss'. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort ss')
Proof
  cheat
QED

Theorem evaluate_as_wei_value_uint:
  !d n. 0 <= n ==>
    evaluate_as_wei_value d (IntV n) =
      if n * &(denomination_multiplier d) < &(2 ** 256) then
        INL (IntV (n * &(denomination_multiplier d)))
      else INR (RuntimeError "ewv bound")
Proof
  cheat
QED

Theorem compile_as_wei_value_word_frag:
  !ctx func cenv cx es ann ts d (a:bytes32).
    word_builtin_frag ctx func cenv cx
      (\xs. compile_as_wei_value_int (EL 0 xs) (denomination_multiplier d) F)
      (builtin_result cx es.accounts ann (AsWeiValue d) ts [IntV (&w2n a)])
      [IntV (&w2n a)] es
Proof
  cheat
QED

(* ===== Ceil arithmetic ===== *)

Theorem int_ceil_via_quot:
  !x d:int. 0 < d ==>
    (if x < 0 then x else x + (d - 1)) quot d = (x + (d - 1)) / d
Proof
  cheat
QED

Theorem decimal_ceil_word:
  !i. within_int_bound (Signed 168) i ==>
    safe_sdiv
      (if w2i (i2w i : bytes32) < 0 then i2w i else
         i2w i + n2w (10000000000 - 1))
      (n2w 10000000000) = i2w ((i + (10000000000 - 1)) / 10000000000)
Proof
  cheat
QED

(* ===== Floor ===== *)

(* Floor by truncation after the negative-input adjustment. *)
Theorem int_floor_via_quot:
  !x d:int. 0 < d ==>
    (if x < 0 then x - (d - 1) else x) quot d = x / d
Proof
  cheat
QED

Theorem straight_fresh_floor:
  !x d. straight_fresh (compile_floor x d)
Proof
  cheat
QED

Theorem word_floor_via_quot:
  !i d. 0 < d /\ &(d) < (2:int) ** 255 /\
    -((2:int) ** 255) <= i - &(d - 1) /\ i < (2:int) ** 255 ==>
    safe_sdiv
      (if w2i (i2w i : bytes32) < 0 then i2w i - n2w (d - 1) else i2w i)
      (n2w d) = i2w (i / &d)
Proof
  cheat
QED

Theorem decimal_floor_word:
  !i. within_int_bound (Signed 168) i ==>
    safe_sdiv
      (if w2i (i2w i : bytes32) < 0 then
         i2w i - n2w (10000000000 - 1) else i2w i)
      (n2w 10000000000) = i2w (i / 10000000000)
Proof
  cheat
QED

Theorem compile_floor_word_frag:
  !ctx func cenv cx es ann ts i.
    within_int_bound (Signed 168) i ==>
    word_builtin_frag ctx func cenv cx
      (\xs. compile_floor (EL 0 xs) 10000000000)
      (builtin_result cx es.accounts ann Floor ts [DecimalV i]) [DecimalV i] es
Proof
  cheat
QED

Theorem compile_ceil_word_frag:
  !ctx func cenv cx es ann ts i.
    within_int_bound (Signed 168) i ==>
    word_builtin_frag ctx func cenv cx
      (\xs. compile_ceil (EL 0 xs) 10000000000)
      (builtin_result cx es.accounts ann Ceil ts [DecimalV i]) [DecimalV i] es
Proof
  cheat
QED

(* ===== Typed composition and the case lemmas ===== *)

(* wb_args_ready from the operands' shared case judgments: each operand
   meets expr_body_pre wherever the invariant holds. *)
Theorem wb_args_ready_of_case:
  !args nocalls ctx func cenv cx env arg_ty.
    (!e s. MEM e args /\ expr_sim_inv cenv cx env s ==>
       expr_body_pre cenv cx env e s /\ (nocalls ==> int_calls_expr e = []) /\
       word_value_type (expr_type e)) /\
    exprs_case nocalls ctx func cenv cx args ==>
    wb_args_ready ctx func cenv cx arg_ty (expr_sim_inv cenv cx env) args
Proof
  cheat
QED

(* The same from expr_sim_ok of each operand, at compile_expr_sim's
   precondition. *)
Theorem wb_args_ready_of_ok:
  !args ctx func cenv cx env arg_ty.
    (!e s. MEM e args /\ expr_sim_inv cenv cx env s ==>
       expr_sim_pre cenv cx env e s /\ word_value_type (expr_type e)) /\
    EVERY (expr_sim_ok cenv) args ==>
    wb_args_ready ctx func cenv cx arg_ty (expr_sim_inv cenv cx env) args
Proof
  cheat
QED

Theorem typed_word_args_shape:
  !cenv cx env ann bt args arg_ty es.
    expr_body_pre cenv cx env (Builtin ann bt args) es /\
    EVERY (\e. word_value_type (expr_type e)) args ==>
    wb_args_shape cenv arg_ty args
Proof
  cheat
QED

Theorem word_args_values_typed:
  !args vs cenv cx env es es'.
    (!e s. MEM e args /\ expr_sim_inv cenv cx env s ==>
       expr_body_pre cenv cx env e s /\ word_value_type (expr_type e)) /\
    expr_sim_inv cenv cx env es /\ eval_exprs cx args es = (INL vs,es') ==>
    LIST_REL (\e v. ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                         value_has_type tv v) args vs
Proof
  cheat
QED

(* The composition on typed word operands, given wb_args_ready at the
   invariant expr_sim_inv. *)
Theorem compile_typed_word_builtin_sim:
  !ctx func cenv cx env ty ann bt args es arg_ty code.
    expr_body_pre cenv cx env (Builtin ann bt args) es /\
    EVERY (\e. word_value_type (expr_type e)) args /\
    wb_args_ready ctx func cenv cx arg_ty (expr_sim_inv cenv cx env) args /\
    bt <> Len /\ bt <> Env MsgGas /\ ~precompile_builtin bt /\
    builtin_args_length_ok bt (LENGTH args) /\ is_word_type ann /\
    (!sa sb op. lower_value compile_expr cenv ty (Builtin ann bt args) sa = (op,sb) ==>
      ?xs sm. lower_word_args cenv arg_ty args sa = (xs,sm) /\ code xs sm = (op,sb)) /\
    (!xs. straight_fresh (code xs)) /\
    (!vs es'. LIST_REL
       (\e v. ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v)
       args vs ==>
       word_builtin_frag ctx func cenv cx code
         (builtin_result cx es'.accounts ann bt (MAP expr_type args) vs) vs es') ==>
    expr_sim ctx func cenv cx ty (Builtin ann bt args) es
Proof
  cheat
QED

(* The five on the operands' wb_args_ready, at every operand type: what
   the shared case lemma and the names form both give. *)
Theorem compile_floor_typed_sim:
  !ctx func cenv cx env ty ann e es.
    expr_body_pre cenv cx env (Builtin ann Floor [e]) es /\
    (!arg_ty. wb_args_ready ctx func cenv cx arg_ty (expr_sim_inv cenv cx env) [e]) ==>
    expr_sim ctx func cenv cx ty (Builtin ann Floor [e]) es
Proof
  cheat
QED

Theorem compile_ceil_typed_sim:
  !ctx func cenv cx env ty ann e es.
    expr_body_pre cenv cx env (Builtin ann Ceil [e]) es /\
    (!arg_ty. wb_args_ready ctx func cenv cx arg_ty (expr_sim_inv cenv cx env) [e]) ==>
    expr_sim ctx func cenv cx ty (Builtin ann Ceil [e]) es
Proof
  cheat
QED

Theorem ceil_ready_vv_sim:
  !ctx func cenv cx env ty ann args es.
    expr_body_pre cenv cx env (Builtin ann Ceil args) es /\
    (!arg_ty. wb_args_ready ctx func cenv cx arg_ty (expr_sim_inv cenv cx env) args) ==>
    expr_vv_sim ctx func cenv cx ty (Builtin ann Ceil args) es
Proof
  cheat
QED

Theorem compile_modular_typed_sim:
  !ctx func cenv cx env ty ann bt a b m es.
    (bt = AddMod \/ bt = MulMod) /\
    expr_body_pre cenv cx env (Builtin ann bt [a; b; m]) es /\
    (!arg_ty. wb_args_ready ctx func cenv cx arg_ty (expr_sim_inv cenv cx env) [a; b; m]) ==>
    expr_sim ctx func cenv cx ty (Builtin ann bt [a; b; m]) es
Proof
  cheat
QED

Theorem compile_pow_mod256_typed_sim:
  !ctx func cenv cx env ty ann a b es.
    expr_body_pre cenv cx env (Builtin ann PowMod256 [a; b]) es /\
    (!arg_ty. wb_args_ready ctx func cenv cx arg_ty (expr_sim_inv cenv cx env) [a; b]) ==>
    expr_sim ctx func cenv cx ty (Builtin ann PowMod256 [a; b]) es
Proof
  cheat
QED

Theorem compile_as_wei_value_typed_sim:
  !ctx func cenv cx env ty ann d e es.
    expr_body_pre cenv cx env (Builtin ann (AsWeiValue d) [e]) es /\
    (!arg_ty. wb_args_ready ctx func cenv cx arg_ty (expr_sim_inv cenv cx env) [e]) ==>
    expr_sim ctx func cenv cx ty (Builtin ann (AsWeiValue d) [e]) es
Proof
  cheat
QED

Theorem word_builtin_sim_stack:
  !ctx func cenv cx ty ann bt args es.
    expr_sim ctx func cenv cx ty (Builtin ann bt args) es /\
    (((bt = Floor \/ (?d. bt = AsWeiValue d)) /\ LENGTH args = 1) \/
     ((bt = AddMod \/ bt = MulMod) /\ LENGTH args = 3) \/
     (bt = PowMod256 /\ LENGTH args = 2)) ==>
    expr_vv_sim ctx func cenv cx ty (Builtin ann bt args) es
Proof
  cheat
QED

(* The five from wb_args_ready at every operand type: their operand
   types, then the typed lemma and the stack lowering. *)
Theorem word_builtin_ready_vv_sim:
  !ctx func cenv cx env ty ann bt args es.
    (bt = Floor \/ (?d. bt = AsWeiValue d) \/ bt = AddMod \/ bt = MulMod \/ bt = PowMod256) /\
    expr_body_pre cenv cx env (Builtin ann bt args) es /\
    (!arg_ty. wb_args_ready ctx func cenv cx arg_ty (expr_sim_inv cenv cx env) args) ==>
    expr_vv_sim ctx func cenv cx ty (Builtin ann bt args) es
Proof
  cheat
QED

(* The operands of the five are word_value_type. *)
Theorem word_builtin_operand_types:
  !cenv cx env ann bt args es.
    (bt = Floor \/ (?d. bt = AsWeiValue d) \/ bt = AddMod \/ bt = MulMod \/ bt = PowMod256) /\
    expr_body_pre cenv cx env (Builtin ann bt args) es ==>
    EVERY (\e. word_value_type (expr_type e)) args
Proof
  cheat
QED

Theorem ceil_operand_types:
  !cenv cx env ann args es.
    expr_body_pre cenv cx env (Builtin ann Ceil args) es ==>
    EVERY (\e. word_value_type (expr_type e)) args
Proof
  cheat
QED

Theorem word_builtin_case:
  !nocalls ctx func cenv cx ann bt args.
    (bt = Floor \/ (?d. bt = AsWeiValue d) \/ bt = AddMod \/ bt = MulMod \/ bt = PowMod256) /\
    exprs_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (Builtin ann bt args)
Proof
  cheat
QED

Theorem word_name_sim_ok:
  !cenv ann id. word_value_type ann ==> expr_sim_ok cenv (Name ann id)
Proof
  cheat
QED

Theorem word_modular_names_sim:
  !cenv ann bt args.
    (bt = AddMod \/ bt = MulMod \/ bt = PowMod256) /\
    EVERY (\e. ?t id. e = Name t id) args ==>
    expr_vv_ok cenv (Builtin ann bt args)
Proof
  cheat
QED

(* Word builtin simulation: typed boundaries and shared fragments. *)
Theory exprSimWordBuiltins
Ancestors
  list exprSim exprSimHyps exprLowering vyperTypeSystem
  vyperInterpreter vyperState vyperContext exprBopLowering
  builtinMath builtinMisc compileEnv

Theorem word_builtin_unary_types:
  !ty bt ts.
    (bt = Floor \/ (?d. bt = AsWeiValue d)) ==>
    well_typed_builtin_app ty bt ts ==>
    ?t. ts = [t] /\
      (if bt = Floor then
         t = BaseT DecimalT /\ ty = BaseT (IntT 256)
       else is_uint_type t /\ ty = BaseT (UintT 256))
Proof
  rpt gen_tac >> strip_tac >> gvs[well_typed_builtin_app_def] >>
  Cases_on `ts` >> gvs[] >>
  rename1 `LENGTH rest = 0` >>
  Cases_on `rest` >> gvs[]
QED

Theorem word_builtin_modular_types:
  !ty bt ts.
    (bt = AddMod \/ bt = MulMod \/ bt = PowMod256) ==>
    well_typed_builtin_app ty bt ts ==>
    ty = BaseT (UintT 256) /\
    ts = (if bt = PowMod256 then
            [BaseT (UintT 256); BaseT (UintT 256)]
          else [BaseT (UintT 256); BaseT (UintT 256); BaseT (UintT 256)])
Proof
  rpt gen_tac >> strip_tac >> simp[well_typed_builtin_app_def] >>
  strip_tac >> gvs[] >>
  Cases_on `ts` >> gvs[] >> rename1 `LENGTH rest` >>
  Cases_on `rest` >> gvs[] >> rename1 `LENGTH rest` >>
  Cases_on `rest` >> gvs[] >> rename1 `LENGTH rest` >>
  Cases_on `rest` >> gvs[]
QED

(* Keep the account parameter: this boundary is valid for every non-Len
   builtin, not only the account-independent arithmetic cases. *)
Definition builtin_result_def:
  builtin_result cx acc ty bt ts vs =
    case evaluate_builtin cx acc ty bt ts vs of
      INL v => INL (Value v)
    | INR err => INR (Error err)
End

Theorem eval_expr_builtin_cases:
  !cx ann bt args es res es'.
    bt <> Len /\ builtin_args_length_ok bt (LENGTH args) /\
    eval_expr cx (Builtin ann bt args) es = (res, es') ==>
    (?exc. eval_exprs cx args es = (INR exc, es') /\ res = INR exc) \/
    ?vs. eval_exprs cx args es = (INL vs, es') /\
         res = builtin_result cx es'.accounts ann bt (MAP expr_type args) vs
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def] >>
  Cases_on `eval_exprs cx args es` >> rename1 `eval_exprs cx args es = (rr, es1)` >>
  Cases_on `rr` >> simp[get_accounts_def, bind_def, return_def,
                          lift_sum_def, builtin_result_def] >>
  rename1 `evaluate_builtin cx _ ann bt _ vs` >>
  Cases_on `evaluate_builtin cx es1.accounts ann bt (MAP expr_type args) vs` >>
  simp[bind_def, return_def, raise_def] >> rw[] >> gvs[]
QED

Theorem compile_expr_unary_builtin:
  !cenv ty ann bt e sa.
    compile_expr cenv ty (Builtin ann bt [e]) sa =
    compile_builtin_dispatch cenv ann ty bt [e] sa
Proof
  rpt gen_tac >>
  simp[Once (CONJUNCT1 compile_expr_raw_def)] >>
  Cases_on `e` >>
  simp[compile_expr_body_def, vyperASTTheory.expr_type_def,
       vyperASTTheory.expr_size_def, list_size_def, basicSizeTheory.option_size_def]
QED

Theorem lower_value_floor:
  !cenv ty ann e sa op sb.
    lower_value compile_expr cenv ty (Builtin ann Floor [e]) sa = (op, sb) ==>
    ?x s1. lower_value compile_expr cenv ty e sa = (x, s1) /\
           compile_floor x 10000000000 s1 = (op, sb)
Proof
  rpt strip_tac >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[Once lower_value_def, comp_bind_def] >>
  simp[compile_expr_unary_builtin] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       compile_builtin_dispatch_body_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp[lower_value_child_call, vyperASTTheory.expr_size_def,
       listTheory.list_size_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rw[] >> gvs[as_stack_val_pair, unwrap_value_def, comp_return_def,
              is_decimal_type_def, is_signed_type_def]
QED

Theorem lower_value_as_wei_value:
  !cenv ty ann d e k sa op sb.
    expr_type e = BaseT (UintT k) /\
    lower_value compile_expr cenv ty (Builtin ann (AsWeiValue d) [e]) sa = (op, sb) ==>
    ?x s1. lower_value compile_expr cenv (expr_type e) e sa = (x, s1) /\
           compile_as_wei_value_int x (denomination_multiplier d) F s1 = (op, sb)
Proof
  rpt strip_tac >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[Once lower_value_def, comp_bind_def, compile_expr_unary_builtin] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       compile_builtin_dispatch_body_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp[lower_value_child_call, vyperASTTheory.expr_size_def,
       listTheory.list_size_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rw[] >> gvs[as_stack_val_pair, unwrap_value_def, comp_return_def,
              is_decimal_type_def, is_signed_type_def]
QED

Theorem compile_expr_body_builtin_dispatch:
  !f g h cenv ty ann bt args st.
    ~names_builtin bt args ==>
    compile_expr_body f g h cenv ty (Builtin ann bt args) st =
    g cenv ann ty bt args st
Proof
  rpt gen_tac >>
  Cases_on `args` >> simp[compile_expr_body_def, names_builtin_def,
                             vyperASTTheory.expr_type_def] >>
  rename1 `names_builtin bt (a::rest)` >>
  Cases_on `a` >> simp[compile_expr_body_def, names_builtin_def,
                       vyperASTTheory.expr_type_def] >>
  Cases_on `rest` >> simp[compile_expr_body_def, names_builtin_def,
                          vyperASTTheory.expr_type_def] >>
  rename1 `names_builtin bt (_::b::rest)` >>
  Cases_on `b` >> simp[compile_expr_body_def, names_builtin_def,
                       vyperASTTheory.expr_type_def] >>
  Cases_on `rest`
  >- (Cases_on `bt` >> simp[compile_expr_body_def, names_builtin_def,
                            vyperASTTheory.expr_type_def]) >>
  simp[compile_expr_body_def, names_builtin_def,
       vyperASTTheory.expr_type_def] >>
  rename1 `names_builtin bt (_::_::c::rest)` >>
  Cases_on `c` >> simp[compile_expr_body_def, names_builtin_def,
                       vyperASTTheory.expr_type_def] >>
  Cases_on `rest` >> simp[compile_expr_body_def, names_builtin_def,
                          vyperASTTheory.expr_type_def] >>
  Cases_on `bt` >> simp[compile_expr_body_def, names_builtin_def,
                        vyperASTTheory.expr_type_def]
QED

Theorem compile_expr_builtin_dispatch:
  !cenv ty ann bt args st.
    ~names_builtin bt args ==>
    compile_expr cenv ty (Builtin ann bt args) st =
    compile_builtin_dispatch cenv ann ty bt args st
Proof
  rpt strip_tac >>
  simp[Once (CONJUNCT1 compile_expr_raw_def),
       compile_expr_body_builtin_dispatch, vyperASTTheory.expr_size_def,
       list_size_def, basicSizeTheory.option_size_def]
QED

Theorem lower_value_name:
  !cenv ty ann id st.
    lower_value compile_expr cenv ty (Name ann id) st =
    (let (v, s1) = compile_name_vv cenv ann id st in unwrap_value cenv v s1)
Proof
  simp[lower_value_def, comp_bind_def,
       Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_def,
       vyperASTTheory.expr_type_def]
QED

Theorem compile_ternary_modular_names_dispatch:
  !cenv ty ann bt aty a bty b mty m st.
    (bt = AddMod \/ bt = MulMod) ==>
    compile_expr cenv ty (Builtin ann bt [Name aty a; Name bty b; Name mty m]) st =
    compile_builtin_dispatch cenv ann ty bt [Name aty a; Name bty b; Name mty m] st
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  simp[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_def,
       vyperASTTheory.expr_type_def, compile_addmod_names_def,
       compile_mulmod_names_def] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       compile_builtin_dispatch_body_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp[lower_value_child_call, vyperASTTheory.expr_size_def, list_size_def,
       lower_value_name] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem compile_powmod256_names_dispatch:
  !cenv ty ann aty a bty b st.
    compile_expr cenv ty (Builtin ann PowMod256 [Name aty a; Name bty b]) st =
    compile_builtin_dispatch cenv ann ty PowMod256 [Name aty a; Name bty b] st
Proof
  rpt gen_tac >>
  simp[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_def,
       vyperASTTheory.expr_type_def, compile_powmod256_names_def] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       compile_builtin_dispatch_body_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp[lower_value_child_call, vyperASTTheory.expr_size_def, list_size_def,
       lower_value_name] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem compile_ternary_modular_dispatch:
  !cenv ty ann bt a b m st.
    (bt = AddMod \/ bt = MulMod) ==>
    compile_expr cenv ty (Builtin ann bt [a; b; m]) st =
    compile_builtin_dispatch cenv ann ty bt [a; b; m] st
Proof
  rpt strip_tac >> gvs[] >>
  Cases_on `a` >>
  simp[compile_expr_builtin_dispatch, names_builtin_def,
       compile_ternary_modular_names_dispatch] >>
  Cases_on `b` >>
  simp[compile_expr_builtin_dispatch, names_builtin_def,
       compile_ternary_modular_names_dispatch] >>
  Cases_on `m` >>
  simp[compile_expr_builtin_dispatch, names_builtin_def,
       compile_ternary_modular_names_dispatch]
QED

Theorem compile_binary_modular_dispatch:
  !cenv ty ann a b st.
    compile_expr cenv ty (Builtin ann PowMod256 [a; b]) st =
    compile_builtin_dispatch cenv ann ty PowMod256 [a; b] st
Proof
  rpt gen_tac >> Cases_on `a` >>
  simp[compile_expr_builtin_dispatch, names_builtin_def,
       compile_powmod256_names_dispatch] >>
  Cases_on `b` >>
  simp[compile_expr_builtin_dispatch, names_builtin_def,
       compile_powmod256_names_dispatch]
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
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[Once lower_value_def, comp_bind_def, compile_ternary_modular_dispatch] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       compile_builtin_dispatch_body_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp[lower_value_child_call, vyperASTTheory.expr_size_def, list_size_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rw[] >> gvs[as_stack_val_pair, unwrap_value_def, comp_return_def]
QED

Theorem lower_value_pow_mod256:
  !cenv ty ann a b sa op sb.
    lower_value compile_expr cenv ty (Builtin ann PowMod256 [a; b]) sa = (op, sb) ==>
    ?x s1 y s2.
      lower_value compile_expr cenv ty a sa = (x, s1) /\
      lower_value compile_expr cenv ty b s1 = (y, s2) /\
      compile_pow_mod256 x y s2 = (op, sb)
Proof
  rpt strip_tac >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[Once lower_value_def, comp_bind_def, compile_binary_modular_dispatch] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       compile_builtin_dispatch_body_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp[lower_value_child_call, vyperASTTheory.expr_size_def, list_size_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rw[] >> gvs[as_stack_val_pair, unwrap_value_def, comp_return_def]
QED

(* Do not materialise an arbitrary top-level value in the composition
   theorem.  The second alternative is ruled out by typed word soundness. *)
Theorem eval_exprs_cons_cases:
  !cx e args es res es'.
    eval_exprs cx (e::args) es = (res, es') ==>
    (?exc. eval_expr cx e es = (INR exc, es') /\ res = INR exc) \/
    (?tv es1. eval_expr cx e es = (INL tv, es1) /\ !v. tv <> Value v) \/
    ?v es1 rr. eval_expr cx e es = (INL (Value v), es1) /\
      eval_exprs cx args es1 = (rr, es') /\
      res = (case rr of INL vs => INL (v::vs) | INR exc => INR exc)
Proof
  rpt gen_tac >> simp[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_expr cx e es` >>
  rename1 `eval_expr cx e es = (rr, es1)` >>
  Cases_on `rr` >> simp[] >>
  rename1 `materialise cx tv es1` >>
  Cases_on `?v. tv = Value v` >> gvs[] >>
  simp[materialise_def, bind_def, return_def] >>
  Cases_on `eval_exprs cx args es1` >>
  rename1 `eval_exprs cx args es1 = (rr, es2)` >>
  Cases_on `rr` >> simp[] >> rw[] >> gvs[]
QED

Theorem compile_word_builtin_dispatch_stack:
  !cenv ann ty bt args sa vv sb.
    (bt = Floor \/ (?d. bt = AsWeiValue d) \/
     bt = AddMod \/ bt = MulMod \/ bt = PowMod256) /\
    compile_builtin_dispatch cenv ann ty bt args sa = (vv, sb) ==>
    ?op. vv = StackValue ann op
Proof
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `compile_builtin_dispatch _ _ _ _ _ _ = _` mp_tac >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       compile_builtin_dispatch_body_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rw[] >> gvs[as_stack_val_pair]
QED

Theorem compile_word_builtin_stack:
  !cenv ann ty bt args sa vv sb.
    (((bt = Floor \/ (?d. bt = AsWeiValue d)) /\ LENGTH args = 1) \/
     ((bt = AddMod \/ bt = MulMod) /\ LENGTH args = 3) \/
     (bt = PowMod256 /\ LENGTH args = 2)) /\
    compile_expr cenv ty (Builtin ann bt args) sa = (vv, sb) ==>
    ?op. vv = StackValue ann op
Proof
  rpt strip_tac >> gvs[LENGTH_EQ_NUM_compute,
       compile_expr_unary_builtin, compile_ternary_modular_dispatch,
       compile_binary_modular_dispatch] >>
  drule_at Any compile_word_builtin_dispatch_stack >> simp[]
QED

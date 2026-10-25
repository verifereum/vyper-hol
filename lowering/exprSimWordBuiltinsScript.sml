(* Word builtin simulation: typed boundaries and shared fragments. *)
Theory exprSimWordBuiltins
Ancestors
  list words integer_word vfmExecution valueEncoding loweringSlice
  exprSim exprSimHyps exprLowering vyperTypeSystem vyperTyping
  vyperInterpreter vyperState vyperContext exprBopLowering
  builtinMath builtinMisc compileEnv exprSimOps freshWrites fragExec varsExt
  exprLoweringProps venomExecSemantics venomState emitHelper emitHelperProps venomInst

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

(* ===== A list-indexed word fragment interface ===== *)
Definition word_builtin_frag_def:
  word_builtin_frag ctx func cenv cx code res vs es0 <=>
    !sa sb xs op s0.
      code xs sa = (op, sb) /\ expr_res_ok res /\
      EVERY (\x. !z. x = Var z ==> not_fresh_at sa z) xs /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa ==>
      frag_exec ctx sa sb
        (\s. s = s0 /\ stmt_state_rel func cenv cx es0 s /\
             LIST_REL (\x v. eval_operand x s = SOME (val_to_w256 v)) xs vs)
        (\s. ?v. res = INL (Value v) /\ word_value v /\
                 stmt_state_rel func cenv cx es0 s /\
                 eval_operand op s = SOME (val_to_w256 v) /\
                 (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
                        lookup_var z s = SOME w) /\
                 (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                          FLOOKUP s.vs_allocas aid = SOME b) /\
                 s.vs_memory = s0.vs_memory)
        (expr_exit res)
End

Theorem word_operands_drop_fresh:
  !xs vs sa ss.
    EVERY (\x. !z. x = Var z ==> not_fresh_at sa z) xs ==>
    (LIST_REL (\x v. eval_operand x (drop_fresh sa ss) = SOME (val_to_w256 v)) xs vs <=>
     LIST_REL (\x v. eval_operand x ss = SOME (val_to_w256 v)) xs vs)
Proof
  Induct >> Cases_on `vs` >> simp[] >> rpt strip_tac >>
  drule eval_operand_drop_fresh >> simp[]
QED

Theorem word_operands_frame:
  !xs vs sa s t.
    EVERY (\x. (!z. x = Var z ==> not_fresh_at sa z) /\ (!l. x <> Label l)) xs /\
    LIST_REL (\x v. eval_operand x s = SOME (val_to_w256 v)) xs vs /\
    (!z w. not_fresh_at sa z /\ lookup_var z s = SOME w ==> lookup_var z t = SOME w) ==>
    LIST_REL (\x v. eval_operand x t = SOME (val_to_w256 v)) xs vs
Proof
  Induct >> Cases_on `vs` >> simp[] >> rpt strip_tac
  >- (drule_all eval_operand_frame >> simp[]) >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[]
QED

Theorem word_builtin_frag_success:
  !ctx func cenv cx code res vs es0 v.
    res = INL (Value v) /\ word_value v /\
    (!xs. straight_fresh (code xs)) /\
    (!xs sa sb op ss.
       code xs sa = (op, sb) /\ fresh_vars_wrt sa ss /\
       LIST_REL (\x v. eval_operand x ss = SOME (val_to_w256 v)) xs vs ==>
       ?ss'. run_inst_seq (emitted_insts sa sb) ss = OK ss' /\
             eval_operand op ss' = SOME (val_to_w256 v)) ==>
    word_builtin_frag ctx func cenv cx code res vs es0
Proof
  rpt gen_tac >> strip_tac >>
  simp[word_builtin_frag_def] >> rpt gen_tac >> strip_tac >>
  ho_match_mp_tac frag_exec_straight_fresh >>
  qexistsl_tac [`code xs`, `\a. F`] >>
  simp[word_operands_drop_fresh] >> rpt strip_tac >>
  first_x_assum irule >>
  goal_assum (drule_at Any) >> qexists_tac `xs` >> simp[]
QED

Theorem word_builtin_frag_revert:
  !ctx func cenv cx code res vs es0 msg.
    res = INR (Error (RuntimeError msg)) /\
    (!xs. straight_fresh (code xs)) /\
    (!xs sa sb op ss.
       code xs sa = (op, sb) /\ fresh_vars_wrt sa ss /\
       LIST_REL (\x v. eval_operand x ss = SOME (val_to_w256 v)) xs vs ==>
       ?ss'. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort ss') ==>
    word_builtin_frag ctx func cenv cx code res vs es0
Proof
  rpt gen_tac >> strip_tac >>
  simp[word_builtin_frag_def] >> rpt gen_tac >> strip_tac >>
  ho_match_mp_tac
    (INST_TYPE [``:'a`` |-> ``:operand``] frag_exec_straight_fresh_abort) >>
  qexistsl_tac [`code xs`, `op`, `\a. a = Revert_abort`] >>
  simp[word_operands_drop_fresh, expr_exit_def] >> rpt strip_tac >>
  first_x_assum irule >>
  goal_assum (drule_at Any) >> qexistsl_tac [`op`, `xs`] >> simp[]
QED

(* No-code probes also cover Wei's scale-one implementation. *)
Theorem word_builtin_frag_constant:
  !ctx func cenv cx vs es v.
    word_value v ==>
    word_builtin_frag ctx func cenv cx
      (\xs. comp_return (Lit (val_to_w256 v))) (INL (Value v)) vs es
Proof
  rpt strip_tac >> irule word_builtin_frag_success >>
  simp[straight_fresh_return, comp_return_def, emitted_insts_refl,
       run_inst_seq_def, eval_operand_def]
QED

Theorem word_builtin_frag_operand:
  !ctx func cenv cx vs es n.
    n < LENGTH vs /\ word_value (EL n vs) ==>
    word_builtin_frag ctx func cenv cx
      (\xs. comp_return (EL n xs)) (INL (Value (EL n vs))) vs es
Proof
  rpt strip_tac >> irule word_builtin_frag_success >>
  simp[straight_fresh_return, comp_return_def, emitted_insts_refl,
       run_inst_seq_def] >> rpt strip_tac >>
  gvs[LIST_REL_EL_EQN]
QED

(* ===== Left-to-right word argument lowering ===== *)
Definition lower_word_args_def:
  (lower_word_args cenv arg_ty [] = comp_return []) /\
  (lower_word_args cenv arg_ty (e::es) =
     do x <- lower_value compile_expr cenv (arg_ty e) e;
        xs <- lower_word_args cenv arg_ty es;
        comp_return (x::xs)
     od)
End

Theorem lower_word_args_nil:
  !cenv arg_ty sa. lower_word_args cenv arg_ty [] sa = ([], sa)
Proof
  simp[lower_word_args_def, comp_return_def]
QED

Theorem lower_word_args_cons:
  !cenv arg_ty e es sa xs sb.
    lower_word_args cenv arg_ty (e::es) sa = (xs, sb) <=>
    ?x s1 ys. lower_value compile_expr cenv (arg_ty e) e sa = (x, s1) /\
      lower_word_args cenv arg_ty es s1 = (ys, sb) /\ xs = x::ys
Proof
  rpt gen_tac >> simp[lower_word_args_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> simp[] >> metis_tac[]
QED

Theorem lower_word_args_shape:
  !args cenv arg_ty.
    (!e sa sb x. MEM e args /\
       lower_value compile_expr cenv (arg_ty e) e sa = (x, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       sa.cs_next_id <= sb.cs_next_id /\
       (!z. x = Var z ==> not_fresh_at sb z) /\ (!l. x <> Label l)) ==>
    !sa sb xs. lower_word_args cenv arg_ty args sa = (xs, sb) ==>
      cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
      sa.cs_next_id <= sb.cs_next_id /\ LENGTH xs = LENGTH args /\
      EVERY (\x. (!z. x = Var z ==> not_fresh_at sb z) /\
                 (!l. x <> Label l)) xs
Proof
  Induct >> simp[lower_word_args_nil, cs_extends_refl] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[lower_word_args_cons] >> strip_tac >> gvs[] >>
  first_assum (drule_at Any) >> simp[] >> strip_tac >>
  first_x_assum (qspecl_then [`cenv`, `arg_ty`] mp_tac) >>
  impl_tac >- metis_tac[] >>
  disch_then drule >> strip_tac >>
  simp[] >> metis_tac[cs_extends_trans, arithmeticTheory.LESS_EQ_TRANS,
                     not_fresh_at_mono]
QED

(* ===== Modular word fragments ===== *)
Theorem straight_fresh_compile_modular:
  !a b c.
    straight_fresh (compile_addmod a b c) /\
    straight_fresh (compile_mulmod a b c) /\
    straight_fresh (compile_pow_mod256 a b)
Proof
  rpt gen_tac >>
  simp[compile_addmod_def, compile_mulmod_def, compile_pow_mod256_def] >>
  rpt conj_tac >>
  rpt (FIRST [irule straight_fresh_ignore_bind >> conj_tac,
              irule straight_fresh_emit_op >> simp[fresh_write_op_def] >> NO_TAC,
              irule straight_fresh_emit_void >> simp[fresh_write_op_def] >> NO_TAC])
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
  Cases_on `is_mul` >> rpt gen_tac >>
  simp[compile_mulmod_def, compile_addmod_def, emit_op_def, emit_void_def,
       emit_inst_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def] >>
  CONV_TAC (DEPTH_CONV (REWR_CONV (GSYM APPEND_ASSOC))) >>
  simp[rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[Once run_inst_seq_def] >>
  simp[Once step_inst_base_def, mk_inst_def] >>
  conj_tac >> strip_tac >> simp[] >>
  simp[Once run_inst_seq_def] >>
  simp[Once step_inst_base_def, mk_inst_def, exec_pure3_def] >>
  simp[run_inst_seq_def, eval_operand_update_var]
QED

Theorem compile_pow_mod256_run:
  !a b sa op sb ss va vb.
    compile_pow_mod256 a b sa = (op, sb) /\
    eval_operand a ss = SOME va /\ eval_operand b ss = SOME vb ==>
    ?ss'. run_inst_seq (emitted_insts sa sb) ss = OK ss' /\
      eval_operand op ss' = SOME (word_exp va vb)
Proof
  rpt gen_tac >>
  simp[compile_pow_mod256_def, emit_op_def, emit_inst_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[Once run_inst_seq_def] >>
  simp[Once step_inst_base_def, mk_inst_def, exec_pure2_def] >>
  simp[run_inst_seq_def, eval_operand_update_var]
QED

Theorem word_exp_modexp:
  !a b : bytes32.
    word_exp a b = n2w (modexp (w2n a) (w2n b) (dimword (:256)) 1)
Proof
  simp[word_exp_def, modexp_exp]
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
  rpt gen_tac >> Cases_on `is_mul` >>
  simp[builtin_result_def, evaluate_builtin_def] >>
  Cases_on `c = 0w` >> gvs[]
  >- (irule word_builtin_frag_revert >>
      simp[straight_fresh_compile_modular] >> rpt strip_tac >>
      gvs[LIST_REL_EL_EQN, val_to_w256_def, i2w_pos] >>
      drule_all (SRULE [] (Q.SPEC `T` compile_modular_run)) >> simp[])
  >- (irule word_builtin_frag_success >>
      simp[straight_fresh_compile_modular, word_value_def] >> rpt strip_tac >>
      gvs[LIST_REL_EL_EQN, val_to_w256_def, i2w_pos] >>
      drule_all (SRULE [] (Q.SPEC `T` compile_modular_run)) >>
      simp[mulmod_def])
  >- (irule word_builtin_frag_revert >>
      simp[straight_fresh_compile_modular] >> rpt strip_tac >>
      gvs[LIST_REL_EL_EQN, val_to_w256_def, i2w_pos] >>
      drule_all (SRULE [] (Q.SPEC `F` compile_modular_run)) >> simp[]) >>
  irule word_builtin_frag_success >>
  simp[straight_fresh_compile_modular, word_value_def] >> rpt strip_tac >>
  gvs[LIST_REL_EL_EQN, val_to_w256_def, i2w_pos] >>
  drule_all (SRULE [] (Q.SPEC `F` compile_modular_run)) >>
  simp[addmod_def]
QED

Theorem compile_pow_mod256_word_frag:
  !ctx func cenv cx es ann ts (a:bytes32) (b:bytes32).
    word_builtin_frag ctx func cenv cx
      (\xs. compile_pow_mod256 (EL 0 xs) (EL 1 xs))
      (builtin_result cx es.accounts ann PowMod256 ts
         [IntV (&w2n a); IntV (&w2n b)])
      [IntV (&w2n a); IntV (&w2n b)] es
Proof
  rpt gen_tac >> simp[builtin_result_def, evaluate_builtin_def] >>
  irule word_builtin_frag_success >>
  simp[straight_fresh_compile_modular, word_value_def] >> rpt strip_tac >>
  gvs[LIST_REL_EL_EQN, val_to_w256_def, i2w_pos] >>
  drule_all compile_pow_mod256_run >>
  simp[word_exp_modexp, dimword_def]
QED

Theorem uint_value_word_rep:
  !bits v. value_has_type (BaseTV (UintT bits)) v /\ bits <= 256 ==>
    v = IntV (&w2n (val_to_w256 v))
Proof
  rpt gen_tac >> Cases_on `v` >> simp[value_has_type_def] >>
  rpt strip_tac >>
  `Num i < 2 ** 256` by
    (irule arithmeticTheory.LESS_LESS_EQ_TRANS >> qexists_tac `2 ** bits` >> simp[]) >>
  `i = &Num i` by simp[] >>
  qpat_x_assum `i = &Num i` (fn th => once_rewrite_tac[th]) >>
  simp[val_to_w256_def, i2w_pos, w2n_n2w, dimword_def] >> gvs[]
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
  rpt strip_tac >>
  `v1 = IntV (&w2n (val_to_w256 v1)) /\
   v2 = IntV (&w2n (val_to_w256 v2)) /\
   v3 = IntV (&w2n (val_to_w256 v3))` by
    metis_tac[uint_value_word_rep, arithmeticTheory.LESS_EQ_REFL] >>
  metis_tac[compile_modular_word_frag]
QED

Theorem compile_pow_mod256_typed_frag:
  !ctx func cenv cx es ann ts v1 v2.
    value_has_type (BaseTV (UintT 256)) v1 /\
    value_has_type (BaseTV (UintT 256)) v2 ==>
    word_builtin_frag ctx func cenv cx
      (\xs. compile_pow_mod256 (EL 0 xs) (EL 1 xs))
      (builtin_result cx es.accounts ann PowMod256 ts [v1; v2]) [v1; v2] es
Proof
  rpt strip_tac >>
  `v1 = IntV (&w2n (val_to_w256 v1)) /\
   v2 = IntV (&w2n (val_to_w256 v2))` by
    metis_tac[uint_value_word_rep, arithmeticTheory.LESS_EQ_REFL] >>
  metis_tac[compile_pow_mod256_word_frag]
QED

(* ===== Composable expression frames ===== *)
Definition wb_frame_def:
  wb_frame cenv es sa s0 s <=>
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
           lookup_var x s = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
             FLOOKUP s.vs_allocas aid = SOME b) /\
    (!aid off sz.
       FLOOKUP s0.vs_allocas aid = SOME (off, sz) /\ aid < sa.cs_next_id /\
       (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
                  off + sz <= b \/ b + sz' <= off) ==>
       mem_bytes_at off sz s.vs_memory = mem_bytes_at off sz s0.vs_memory)
End

Theorem wb_frame_refl:
  !cenv es sa s. wb_frame cenv es sa s s
Proof
  simp[wb_frame_def]
QED

Theorem wb_frame_vars:
  !cenv es sa s0 s x w.
    wb_frame cenv es sa s0 s /\ not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
    lookup_var x s = SOME w
Proof
  simp[wb_frame_def]
QED

Theorem expr_post_frame:
  !func cenv cx e es sa sb s0 es' v op s.
    expr_post func cenv cx e es sa sb s0 es' v op s ==>
    wb_frame cenv es sa s0 s
Proof
  simp[expr_post_def, wb_frame_def] >> metis_tac[]
QED

Theorem expr_post_state:
  !func cenv cx e es sa sb s0 es' v op s.
    expr_post func cenv cx e es sa sb s0 es' v op s ==>
    stmt_state_rel func cenv cx es' s
Proof
  simp[expr_post_def]
QED

Theorem expr_post_word_operand:
  !func cenv cx e es sa sb s0 es' v op s.
    expr_post func cenv cx e es sa sb s0 es' v op s /\
    is_word_type (expr_type e) /\
    IS_SOME (evaluate_type (get_tenv cx) (expr_type e)) /\ word_value v ==>
    eval_operand op s = SOME (val_to_w256 v)
Proof
  rpt strip_tac >> irule expr_val_rel_word >>
  gvs[expr_post_def] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem expr_post_word_intro:
  !func cenv cx e es sa sb s0 es' v op s.
    stmt_state_rel func cenv cx es' s /\ is_word_type (expr_type e) /\ word_value v /\
    eval_operand op s = SOME (val_to_w256 v) /\ wb_frame cenv es sa s0 s ==>
    expr_post func cenv cx e es sa sb s0 es' v op s
Proof
  simp[expr_post_def, wb_frame_def, expr_val_rel_def, expr_val_at_def,
       typed_val_to_w256_word_value] >> metis_tac[]
QED

Theorem wb_frame_readonly_tail:
  !cenv es sa s0 t s1 u.
    wb_frame cenv es sa s0 t /\ sa.cs_next_var <= s1.cs_next_var /\
    (!z w. not_fresh_at s1 z /\ lookup_var z t = SOME w ==> lookup_var z u = SOME w) /\
    (!aid b. FLOOKUP t.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
    u.vs_memory = t.vs_memory ==>
    wb_frame cenv es sa s0 u
Proof
  simp[wb_frame_def] >> rpt strip_tac >>
  metis_tac[not_fresh_at_mono]
QED

Theorem wb_frame_trans:
  !func cenv cx es s0 sa es1 s1 t u.
    stmt_state_rel func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es1.scopes /\
    sa.cs_next_var <= s1.cs_next_var /\ sa.cs_next_id <= s1.cs_next_id /\
    wb_frame cenv es sa s0 t /\ wb_frame cenv es1 s1 t u ==>
    wb_frame cenv es sa s0 u
Proof
  rpt gen_tac >> simp[wb_frame_def] >> strip_tac >>
  conj_tac
  >- (rpt strip_tac >> metis_tac[not_fresh_at_mono]) >>
  rpt strip_tac >>
  qpat_x_assum `!aid off sz. FLOOKUP s0.vs_allocas aid = _ /\ _ ==> _`
    (qspecl_then [`aid`, `off`, `sz`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (fn th => rewrite_tac[GSYM th]) >>
  qpat_x_assum `!aid off sz. FLOOKUP t.vs_allocas aid = _ /\ _ ==> _`
    (qspecl_then [`aid`, `off`, `sz`] mp_tac) >>
  disch_then irule >> rpt conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!n b sz'. local_region _ es.scopes s0 _ _ _ ==> _` irule >>
      qexists_tac `n` >> irule local_region_frame >>
      conj_tac >- (qexistsl_tac [`cx`, `func`] >> first_assum ACCEPT_TAC) >>
      qexistsl_tac [`sa`, `es1.scopes`, `t`] >> simp[]) 
  >- (irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
      qexists_tac `sa.cs_next_id` >> simp[]) >>
  qpat_x_assum `!aid b. FLOOKUP s0.vs_allocas aid = _ ==> _` irule >> simp[]
QED

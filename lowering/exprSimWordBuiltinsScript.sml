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
 *   word_builtin_below_sim — expr_vv_ok of the five from expr_sim_below
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
 *   typed_word_args_ready  — wb_args_ready and wb_args_shape from
 *                            expr_sim_pre and the induction hypothesis
 *   compile_typed_word_builtin_sim — compile_word_builtin_sim on typed
 *                            operands
 *
 * The operands' shape is exprSimOperators' lower_value_word_shape.
 *)

Theory exprSimWordBuiltins
Ancestors
  list words integer_word vfmExecution valueEncoding loweringSlice
  vyperEvalExprPreservesScopesDom
  exprSim exprSimHyps exprSimOperators exprSimWordArgs exprLowering
  vyperTypeSystem vyperTyping vyperInterpreter vyperState vyperContext
  exprBopLowering builtinMath builtinMisc builtinSimple arithmeticProps
  compileEnv exprSimOps freshWrites fragExec varsExt exprLoweringProps
  venomExecSemantics venomState emitHelper emitHelperProps venomInst
  builtinProps

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
  rpt gen_tac >> strip_tac >> simp[well_typed_builtin_app_def] >>
  strip_tac >> gvs[] >>
  Cases_on `ts` >> gvs[] >> rename1 `LENGTH rest` >>
  Cases_on `rest` >> gvs[] >> rename1 `LENGTH rest` >>
  Cases_on `rest` >> gvs[] >> rename1 `LENGTH rest` >>
  Cases_on `rest` >> gvs[]
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
    comp_bind (compile_name_vv cenv ann id) (unwrap_value cenv) st
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
       lower_value_name, comp_bind_def] >>
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
       lower_value_name, comp_bind_def] >>
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

(* ===== as_wei_value: unsigned scaling overflow ===== *)
Theorem mul_mod_div_no_overflow:
  !N x m:num. 0 < N /\ x < N /\ 0 < m /\ m < N ==>
    (((x * m MOD N) DIV x = m \/ x = 0) <=> x * m < N)
Proof
  rpt strip_tac >> Cases_on `x = 0` >- simp[] >>
  `0 < x` by decide_tac >>
  Cases_on `x * m < N`
  >- simp[arithmeticTheory.LESS_MOD, arithmeticTheory.MULT_COMM,
          arithmeticTheory.MULT_DIV] >>
  `x * m MOD N < N` by simp[] >>
  `x * m MOD N < m * x` by
    (simp[arithmeticTheory.MULT_COMM] >> decide_tac) >>
  `x * m MOD N DIV x < m` by
    simp[arithmeticTheory.DIV_LT_X] >> simp[]
QED

Theorem denomination_multiplier_bounds:
  !d. 0 < denomination_multiplier d /\ denomination_multiplier d < 2 ** 256
Proof
  Cases >> EVAL_TAC
QED

Theorem straight_fresh_as_wei_value_int:
  !x m. straight_fresh (compile_as_wei_value_int x m F)
Proof
  rpt gen_tac >> simp[compile_as_wei_value_int_def] >>
  Cases_on `m = 1` >> simp[straight_fresh_return] >>
  rpt (FIRST [CHANGED_TAC (simp[]), irule straight_fresh_bind >> conj_tac,
              irule straight_fresh_ignore_bind >> conj_tac,
              irule straight_fresh_emit_op >> simp[fresh_write_op_def] >> NO_TAC,
              irule straight_fresh_emit_void >> simp[fresh_write_op_def] >> NO_TAC,
              irule straight_fresh_return >> NO_TAC,
              gen_tac])
QED

Theorem word_mul_div_no_overflow:
  !(a:bytes32) m. 0 < m /\ m < dimword (:256) ==>
    (((a * n2w m) // a = n2w m \/ a = 0w) <=> w2n a * m < dimword (:256))
Proof
  rpt strip_tac >>
  `m < 2 ** 256` by gvs[dimword_def] >>
  Cases_on `a = 0w` >- simp[] >>
  `0 < w2n a` by metis_tac[w2n_eq_0, arithmeticTheory.NOT_ZERO_LT_ZERO] >>
  `m * w2n a MOD dimword (:256) DIV w2n a < dimword (:256)` by
    (irule arithmeticTheory.LESS_EQ_LESS_TRANS >>
     qexists_tac `m * w2n a MOD dimword (:256)` >>
     simp[arithmeticTheory.DIV_LESS_EQ]) >>
  once_rewrite_tac[GSYM w2n_11] >>
  simp[word_mul_def, word_div_def, w2n_n2w] >>
  qspec_then `dimword (:256)` mp_tac mul_mod_div_no_overflow >>
  disch_then (qspecl_then [`w2n a`, `m`] mp_tac) >>
  simp[arithmeticTheory.MULT_COMM, w2n_lt]
QED

Theorem fresh_vars_wrt_not_fresh_at:
  !sa ss x w.
    fresh_vars_wrt sa ss /\ eval_operand x ss = SOME w ==>
    !z. x = Var z ==> not_fresh_at sa z
Proof
  rw[not_fresh_at_def] >>
  metis_tac[fresh_vars_wrt_eval_operand, arithmeticTheory.GREATER_EQ]
QED

Theorem eval_operand_update_not_fresh:
  !sa a ss n w. (!z. a = Var z ==> not_fresh_at sa z) /\ sa.cs_next_var <= n ==>
    eval_operand a (update_var (STRING #"%" (toString n)) w ss) = eval_operand a ss
Proof
  gen_tac >> Cases >> simp[eval_operand_def, lookup_var_update_var] >>
  rpt strip_tac >> gvs[not_fresh_at_def] >> metis_tac[]
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
  rpt gen_tac >> Cases_on `m = 1`
  >- (simp[compile_as_wei_value_int_def, comp_return_def] >>
      rpt strip_tac >> gvs[] >> gvs[emitted_insts_def, run_inst_seq_def, WORD_MULT_CLAUSES, w2n_lt]) >>
  simp[compile_as_wei_value_int_def, emit_op_def, emit_void_def,
       emit_inst_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >> simp[emitted_insts_def] >>
  CONV_TAC (DEPTH_CONV (REWR_CONV (GSYM APPEND_ASSOC))) >>
  simp[rich_listTheory.DROP_LENGTH_APPEND] >>
  qspec_then `sa` assume_tac eval_operand_update_not_fresh >>
  `((safe_div (va * n2w m) va = n2w m) \/ va = 0w) <=>
    m * w2n va < dimword (:256)` by
    (qspec_then `va` (qspec_then `m` mp_tac) word_mul_div_no_overflow >>
     Cases_on `va = 0w` >> simp[safe_div_def, arithmeticTheory.MULT_COMM]) >>
  conj_tac >> strip_tac >>
  simp[Once run_inst_seq_def] >>
  simp[Once step_inst_base_def, mk_inst_def, exec_pure2_def, eval_operand_def] >>
  simp[Once run_inst_seq_def] >>
  simp[Once step_inst_base_def, mk_inst_def, exec_pure2_def,
       eval_operand_update_var, eval_operand_update_not_fresh] >>
  simp[Once run_inst_seq_def] >>
  simp[Once step_inst_base_def, mk_inst_def, exec_pure2_def,
       eval_operand_update_var, eval_operand_def, lookup_var_update_var] >>
  simp[Once run_inst_seq_def] >>
  simp[Once step_inst_base_def, mk_inst_def, exec_pure1_def] >>
  simp[] >>
  simp[Once run_inst_seq_def] >>
  simp[Once step_inst_base_def, mk_inst_def, exec_pure2_def,
       eval_operand_def, lookup_var_update_var] >>
  simp[Once run_inst_seq_def] >>
  simp[Once step_inst_base_def, mk_inst_def, eval_operand_def,
       lookup_var_update_var] >>
  Cases_on `va = 0w` >>
  Cases_on `safe_div (va * n2w m) va = n2w m` >>
  gvs[bool_to_word_def, WORD_OR_CLAUSES, run_inst_seq_def, lookup_var_update_var]
QED

Theorem evaluate_as_wei_value_uint:
  !d n. 0 <= n ==>
    evaluate_as_wei_value d (IntV n) =
      if n * &(denomination_multiplier d) < &(2 ** 256) then
        INL (IntV (n * &(denomination_multiplier d)))
      else INR (RuntimeError "ewv bound")
Proof
  rpt strip_tac >> `n = &(Num n)` by simp[] >>
  pop_assum SUBST1_TAC >> Cases_on `d` >>
  simp[vyperValueOperationTheory.evaluate_as_wei_value_def,
       denomination_multiplier_def, vyperValueTheory.within_int_bound_def,
       integerTheory.INT_MUL, integerTheory.NUM_OF_INT]
QED

Theorem compile_as_wei_value_word_frag:
  !ctx func cenv cx es ann ts d (a:bytes32).
    word_builtin_frag ctx func cenv cx
      (\xs. compile_as_wei_value_int (EL 0 xs) (denomination_multiplier d) F)
      (builtin_result cx es.accounts ann (AsWeiValue d) ts [IntV (&w2n a)])
      [IntV (&w2n a)] es
Proof
  rpt gen_tac >>
  qspec_then `d` strip_assume_tac denomination_multiplier_bounds >>
  simp[builtin_result_def, evaluate_builtin_def, evaluate_as_wei_value_uint] >>
  Cases_on `w2n a * denomination_multiplier d < dimword (:256)` >>
  gvs[dimword_def]
  >- (irule word_builtin_frag_success >>
      simp[straight_fresh_as_wei_value_int, word_value_def] >>
      rpt strip_tac >>
      gvs[LIST_REL_EL_EQN, val_to_w256_def, i2w_pos] >>
      `!z. x = Var z ==> not_fresh_at sa z` by
        metis_tac[fresh_vars_wrt_not_fresh_at] >>
      drule_all (SRULE [dimword_def] compile_as_wei_value_int_run) >>
      simp[dimword_def, word_mul_def, w2n_n2w, arithmeticTheory.MULT_COMM]) >>
  irule word_builtin_frag_revert >>
  simp[straight_fresh_as_wei_value_int] >> rpt strip_tac >>
  gvs[LIST_REL_EL_EQN, val_to_w256_def, i2w_pos] >>
  `!z. x = Var z ==> not_fresh_at sa z` by
    metis_tac[fresh_vars_wrt_not_fresh_at] >>
  drule_all (SRULE [dimword_def] compile_as_wei_value_int_run) >> simp[]
QED

(* ===== Floor ===== *)

(* Floor by truncation after the negative-input adjustment. *)
Theorem int_floor_via_quot:
  !x d:int. 0 < d ==>
    (if x < 0 then x - (d - 1) else x) quot d = x / d
Proof
  rpt strip_tac >>
  `d <> 0` by intLib.ARITH_TAC >>
  drule integerTheory.INT_DIVISION >> disch_then (qspec_then `x` strip_assume_tac) >>
  Cases_on `x < 0` >> simp[] >>
  irule integerTheory.INT_QUOT_UNIQUE
  >- (qexists_tac `x % d - (d - 1)` >>
      simp[integerTheory.INT_ABS] >> intLib.ARITH_TAC) >>
  Cases_on `x = 0` >- (qexists_tac `0` >> simp[integerTheory.INT_DIV_0, integerTheory.INT_ABS] >> intLib.ARITH_TAC) >>
  qexists_tac `x % d` >> simp[integerTheory.INT_ABS] >> intLib.ARITH_TAC
QED

Theorem straight_fresh_floor:
  !x d. straight_fresh (compile_floor x d)
Proof
  rpt gen_tac >> simp[compile_floor_def, compile_select_def] >>
  rpt (FIRST [CHANGED_TAC (simp[]), irule straight_fresh_bind >> conj_tac,
              irule straight_fresh_emit_op >> simp[fresh_write_op_def] >> NO_TAC,
              gen_tac])
QED

Theorem word_floor_via_quot:
  !i d. 0 < d /\ &(d) < (2:int) ** 255 /\
    -((2:int) ** 255) <= i - &(d - 1) /\ i < (2:int) ** 255 ==>
    safe_sdiv
      (if w2i (i2w i : bytes32) < 0 then i2w i - n2w (d - 1) else i2w i)
      (n2w d) = i2w (i / &d)
Proof
  rpt strip_tac >>
  gvs[] >>
  `0 <= &(d - 1):int` by simp[] >>
  `w2i (i2w i : bytes32) = i /\
   w2i (i2w (i - &(d - 1)) : bytes32) = i - &(d - 1) /\
   w2i (i2w (&d) : bytes32) = &d` by
    (rpt conj_tac >> irule w2i_i2w >>
     simp[integer_wordTheory.INT_MIN_def, integer_wordTheory.INT_MAX_def,
          wordsTheory.INT_MIN_def, dimword_def] >>
     intLib.ARITH_TAC) >>
  `n2w d <> (0w:bytes32)` by
    simp[n2w_11, dimword_def] >>
  Cases_on `i < 0` >>
  simp[safe_sdiv_def, GSYM i2w_pos, word_i2w_sub, word_quot] >>
  qspec_then `i` (qspec_then `&d` mp_tac) int_floor_via_quot >>
  simp[integerTheory.INT_SUB]
QED

Theorem decimal_floor_word:
  !i. within_int_bound (Signed 168) i ==>
    safe_sdiv
      (if w2i (i2w i : bytes32) < 0 then
         i2w i - n2w (10000000000 - 1) else i2w i)
      (n2w 10000000000) = i2w (i / 10000000000)
Proof
  rpt strip_tac >> irule word_floor_via_quot >>
  gvs[vyperValueTheory.within_int_bound_def] >> intLib.ARITH_TAC
QED

Theorem compile_floor_word_frag:
  !ctx func cenv cx es ann ts i.
    within_int_bound (Signed 168) i ==>
    word_builtin_frag ctx func cenv cx
      (\xs. compile_floor (EL 0 xs) 10000000000)
      (builtin_result cx es.accounts ann Floor ts [DecimalV i]) [DecimalV i] es
Proof
  rpt strip_tac >> simp[builtin_result_def, evaluate_builtin_def] >>
  irule word_builtin_frag_success >>
  simp[straight_fresh_floor, word_value_def] >> rpt strip_tac >>
  gvs[LIST_REL_EL_EQN, val_to_w256_def] >>
  drule_all compile_floor_correct >> strip_tac >>
  qexists_tac `ss'` >> simp[] >>
  drule decimal_floor_word >> simp[WORD_LTi, word_0_w2i]
QED

(* ===== Typed composition and the case lemmas ===== *)

(* Adapter from the public induction predicate to list composition.
   Thread source_supply with expr_sim_inv so each later operand meets
   expr_sim_pre after evaluating the preceding operands. *)
Theorem typed_word_args_ready:
  !ctx func cenv cx env ann bt args arg_ty es.
    expr_sim_pre cenv cx env (Builtin ann bt args) es /\
    EVERY (\e. word_value_type (expr_type e) /\ expr_sim_ok cenv e) args ==>
    wb_args_ready ctx func cenv cx arg_ty
      (\s. expr_sim_inv cenv cx env s /\ source_supply s) args /\
    wb_args_shape cenv arg_ty args
Proof
  rpt strip_tac
  >- (simp[wb_args_ready_def] >> rpt gen_tac >> strip_tac >>
      rename1 `source_supply arg_state` >>
      `word_value_type (expr_type e) /\ expr_sim_ok cenv e` by
        (gvs[EVERY_MEM] >> first_x_assum drule >> simp[]) >>
      `expr_sim_pre cenv cx env e arg_state` by
        (drule_all expr_sim_pre_builtin_arg >> simp[]) >>
      simp[] >> rpt conj_tac
      >- metis_tac[expr_sim_ok_def]
      >- metis_tac[word_value_type_word]
      >- metis_tac[well_typed_expr_type_evaluates]
      >- (rpt strip_tac >> drule_all expr_sim_pre_word_result >> simp[]) >>
      rpt strip_tac >> drule_all expr_sim_pre_word_result >>
      simp[] >> metis_tac[]) >>
  simp[wb_args_shape_def] >> rpt gen_tac >> strip_tac >>
  `word_value_type (expr_type e)` by
    (gvs[EVERY_MEM] >> first_x_assum drule >> simp[]) >>
  `expr_sim_pre cenv cx env e es` by
    (drule expr_sim_pre_builtin_arg >> disch_then irule >>
     gvs[expr_sim_pre_def]) >>
  drule expr_sim_pre_lower_value_word_shape >> disch_then drule >>
  simp[word_value_type_word]
QED

Theorem word_args_values_typed:
  !args vs cenv cx env es es'.
    (!e s. MEM e args /\ expr_sim_inv cenv cx env s /\ source_supply s ==>
       expr_sim_pre cenv cx env e s /\ word_value_type (expr_type e)) /\
    expr_sim_inv cenv cx env es /\ source_supply es /\
    eval_exprs cx args es = (INL vs,es') ==>
    LIST_REL (\e v. ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                         value_has_type tv v) args vs
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- gvs[eval_exprs_nil] >>
  drule eval_exprs_cons_cases >> strip_tac >> gvs[] >>
  `expr_sim_pre cenv cx env h es /\ word_value_type (expr_type h)` by
    (first_x_assum irule >> simp[]) >>
  drule_all expr_sim_pre_word_result >> strip_tac >> gvs[] >>
  Cases_on `rr` >> gvs[] >>
  first_x_assum irule >> goal_assum (drule_at Any) >>
  simp[] >> metis_tac[listTheory.MEM]
QED

Theorem typed_builtin_args_values:
  !cenv cx env ann bt args es vs es'.
    expr_sim_pre cenv cx env (Builtin ann bt args) es /\
    EVERY (\e. word_value_type (expr_type e) /\ expr_sim_ok cenv e) args /\
    eval_exprs cx args es = (INL vs,es') ==>
    LIST_REL (\e v. ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                         value_has_type tv v) args vs
Proof
  rpt strip_tac >> irule word_args_values_typed >> goal_assum (drule_at Any) >>
  qexistsl_tac [`cenv`, `env`] >> conj_tac
  >- (rpt gen_tac >> strip_tac >> conj_tac
      >- (irule expr_sim_pre_builtin_arg >> simp[] >>
          qexistsl_tac [`ann`, `args`, `bt`, `es`] >> simp[]) >>
      gvs[EVERY_MEM] >> first_x_assum drule >> simp[]) >>
  gvs[expr_sim_pre_def]
QED

Theorem compile_typed_word_builtin_sim:
  !ctx func cenv cx env ty ann bt args es arg_ty code.
    expr_sim_pre cenv cx env (Builtin ann bt args) es /\
    EVERY (\e. word_value_type (expr_type e) /\ expr_sim_ok cenv e) args /\
    bt <> Len /\ builtin_args_length_ok bt (LENGTH args) /\ is_word_type ann /\
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
  rpt gen_tac >> strip_tac >> drule_all typed_word_args_ready >>
  disch_then (qspecl_then [`ctx`, `func`, `arg_ty`] strip_assume_tac) >>
  irule compile_word_builtin_sim >> simp[] >>
  qexistsl_tac [`\s. expr_sim_inv cenv cx env s /\ source_supply s`,
               `arg_ty`, `code`] >> simp[] >>
  conj_tac >- gvs[expr_sim_pre_def] >> conj_tac
  >- (rpt strip_tac >> first_x_assum (qspec_then `xs` mp_tac) >>
      simp[straight_fresh_def] >> disch_then drule >> strip_tac >>
      simp[cs_extends_def] >> qexists_tac `[]` >> simp[]) >>
  rpt strip_tac >> first_x_assum irule >>
  irule typed_builtin_args_values >> goal_assum (drule_at Any) >>
  qexistsl_tac [`ann`, `bt`, `cenv`, `env`] >> simp[]
QED

Theorem compile_floor_typed_sim:
  !cenv ann e.
    expr_sim_ok cenv e ==> expr_sim_ok cenv (Builtin ann Floor [e])
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac[expr_sim_ok_def] >> rpt strip_tac >>
  `expr_type e = BaseT DecimalT /\ ann = BaseT (IntT 256)` by
    gvs[expr_sim_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
  irule compile_typed_word_builtin_sim >>
  simp[is_word_type_def, builtin_args_length_ok_def, word_value_type_def] >>
  conj_tac >- (qexistsl_tac [`\e. ty`, `(\xs. compile_floor (EL 0 xs) 10000000000)`] >>
  simp[straight_fresh_floor] >> conj_tac
  >- (rpt strip_tac >> drule lower_value_floor >> strip_tac >>
      qexistsl_tac [`[x]`, `s1`] >>
      simp[lower_word_args_def, comp_bind_def, comp_return_def]) >>
  rpt strip_tac >>
  gvs[LIST_REL_CONS1, vyperValueTheory.evaluate_type_def] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  mp_tac compile_floor_word_frag >> simp[] >> disch_then irule >> simp[]) >>
  qexists_tac `env` >> gvs[]
QED

Theorem compile_modular_typed_sim:
  !cenv ann bt a b m.
    (bt = AddMod \/ bt = MulMod) /\
    expr_sim_ok cenv a /\ expr_sim_ok cenv b /\ expr_sim_ok cenv m ==>
    expr_sim_ok cenv (Builtin ann bt [a; b; m])
Proof
  rpt gen_tac >> strip_tac >> (rewrite_tac[expr_sim_ok_def] >> rpt strip_tac >>
  `ann = BaseT (UintT 256) /\ expr_type a = BaseT (UintT 256) /\
   expr_type b = BaseT (UintT 256) /\ expr_type m = BaseT (UintT 256)` by
    (gvs[expr_sim_pre_def, well_typed_expr_def] >>
     gvs[well_typed_builtin_app_def]) >>
  irule compile_typed_word_builtin_sim >>
  simp[is_word_type_def, builtin_args_length_ok_def, word_value_type_def] >>
  conj_tac
  >- (qexistsl_tac [`\e. ty`, `\xs. (if bt = AddMod then compile_addmod else compile_mulmod)
                                    (EL 0 xs) (EL 1 xs) (EL 2 xs)`] >>
      conj_tac
      >- (rpt strip_tac >> drule_at Any lower_value_ternary_modular >> simp[] >> strip_tac >>
          qexistsl_tac [`[x;y;z]`, `s3`] >>
          simp[lower_word_args_def, comp_bind_def, comp_return_def]) >>
      conj_tac
      >- (gvs[] >> simp[straight_fresh_compile_modular]) >>
      rpt strip_tac >> gvs[LIST_REL_CONS1, vyperValueTheory.evaluate_type_def] >>
      metis_tac[SRULE [] (Q.SPEC `F` compile_modular_typed_frag),
                SRULE [] (Q.SPEC `T` compile_modular_typed_frag)]) >>
  qexists_tac `env` >> gvs[])
QED

Theorem compile_pow_mod256_typed_sim:
  !cenv ann a b.
    expr_sim_ok cenv a /\ expr_sim_ok cenv b ==>
    expr_sim_ok cenv (Builtin ann PowMod256 [a;b])
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac[expr_sim_ok_def] >> rpt strip_tac >>
  `ann = BaseT (UintT 256) /\ expr_type a = BaseT (UintT 256) /\
   expr_type b = BaseT (UintT 256)` by
    gvs[expr_sim_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
  irule compile_typed_word_builtin_sim >>
  simp[is_word_type_def, builtin_args_length_ok_def, word_value_type_def] >>
  conj_tac
  >- (qexistsl_tac [`\e. ty`, `\xs. compile_pow_mod256 (EL 0 xs) (EL 1 xs)`] >>
      simp[straight_fresh_compile_modular] >> conj_tac
      >- (rpt strip_tac >> drule lower_value_pow_mod256 >> strip_tac >>
          qexistsl_tac [`[x;y]`, `s2`] >>
          simp[lower_word_args_def, comp_bind_def, comp_return_def]) >>
      rpt strip_tac >> gvs[LIST_REL_CONS1, vyperValueTheory.evaluate_type_def] >>
      mp_tac compile_pow_mod256_typed_frag >> simp[] >> disch_then irule >> simp[]) >>
  qexists_tac `env` >> gvs[]
QED

Theorem compile_as_wei_value_typed_sim:
  !cenv ann d e.
    expr_sim_ok cenv e ==> expr_sim_ok cenv (Builtin ann (AsWeiValue d) [e])
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac[expr_sim_ok_def] >> rpt strip_tac >>
  `?k. expr_type e = BaseT (UintT k) /\ ann = BaseT (UintT 256)` by
    gvs[expr_sim_pre_def, well_typed_expr_def, well_typed_builtin_app_def,
        is_uint_type_def] >>
  irule compile_typed_word_builtin_sim >>
  simp[is_word_type_def, builtin_args_length_ok_def, word_value_type_def] >>
  conj_tac
  >- (qexistsl_tac [`expr_type`, `\xs. compile_as_wei_value_int (EL 0 xs) (denomination_multiplier d) F`] >>
      simp[straight_fresh_as_wei_value_int] >> conj_tac
      >- (rpt strip_tac >> drule_at Any lower_value_as_wei_value >> simp[] >> strip_tac >>
          qexistsl_tac [`[x]`, `s1`] >>
          simp[lower_word_args_def, comp_bind_def, comp_return_def]) >>
      rpt strip_tac >> gvs[LIST_REL_CONS1, vyperValueTheory.evaluate_type_def] >>
      drule_all uint_value_word_rep >> strip_tac >> gvs[] >>
      qpat_x_assum `v = IntV _` (fn th => once_rewrite_tac[th]) >>
      mp_tac compile_as_wei_value_word_frag >> simp[] >> disch_then irule) >>
  qexists_tac `env` >> gvs[]
QED

Theorem word_builtin_sim_stack:
  !ctx func cenv cx ty ann bt args es.
    expr_sim ctx func cenv cx ty (Builtin ann bt args) es /\
    (((bt = Floor \/ (?d. bt = AsWeiValue d)) /\ LENGTH args = 1) \/
     ((bt = AddMod \/ bt = MulMod) /\ LENGTH args = 3) \/
     (bt = PowMod256 /\ LENGTH args = 2)) ==>
    expr_vv_sim ctx func cenv cx ty (Builtin ann bt args) es
Proof
  rpt gen_tac >> strip_tac >> (irule expr_vv_sim_stack >> simp[] >> conj_tac
  >- (gen_tac >> Cases_on `compile_expr cenv ty (Builtin ann bt args) sa` >>
      drule_at Any compile_word_builtin_stack >> simp[] >> metis_tac[]) >>
  metis_tac[eval_expr_builtin_value])
QED

Theorem word_builtin_args_vv_sim:
  !cenv ann bt args.
    (bt = Floor \/ (?d. bt = AsWeiValue d) \/ bt = AddMod \/ bt = MulMod \/ bt = PowMod256) /\
    EVERY (expr_sim_ok cenv) args ==>
    expr_vv_ok cenv (Builtin ann bt args)
Proof
  rpt gen_tac >> strip_tac >> (rewrite_tac[expr_vv_ok_def] >> rpt strip_tac >>
  `well_typed_builtin_app ann bt (MAP expr_type args)` by
    gvs[expr_sim_pre_def, well_typed_expr_def] >>
  gvs[well_typed_builtin_app_def] >>
  gvs[MAP_EQ_CONS, LENGTH_EQ_NUM_compute] >>
  irule word_builtin_sim_stack >> simp[] >>
  metis_tac[compile_floor_typed_sim, compile_as_wei_value_typed_sim,
            compile_modular_typed_sim, compile_pow_mod256_typed_sim, expr_sim_ok_def])
QED

Theorem word_name_sim_ok:
  !cenv ann id. word_value_type ann ==> expr_sim_ok cenv (Name ann id)
Proof
  rpt strip_tac >> rewrite_tac[expr_sim_ok_def] >> rpt strip_tac >>
  `well_typed_expr env (Name ann id) /\ env_consistent env cx es /\ state_well_typed es` by
    gvs[expr_sim_pre_def, expr_sim_inv_def] >>
  drule_all vyperTypeEnvTheory.well_typed_Name_lookup >> strip_tac >>
  `word_value entry.value` by
    (mp_tac word_value_type_typed >>
     disch_then (qspec_then `ann` mp_tac) >>
     disch_then (qspec_then `env.type_defs` mp_tac) >>
     disch_then (qspecl_then [`tv`, `Value entry.value`] mp_tac) >>
     simp[vyperTypeInvariantsTheory.toplevel_value_typed_def]) >>
  irule compile_name_word_sim >>
  gvs[expr_sim_pre_def, expr_sim_inv_def, well_typed_expr_def] >>
  metis_tac[word_value_type_word]
QED

Theorem word_builtin_below_sim:
  !cenv ann bt args.
    (bt = Floor \/ (?d. bt = AsWeiValue d) \/ bt = AddMod \/ bt = MulMod \/ bt = PowMod256) /\
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (Builtin ann bt args)
Proof
  rpt gen_tac >> strip_tac >> (irule word_builtin_args_vv_sim >> simp[] >>
  simp[EVERY_MEM] >> rpt strip_tac >> drule_all expr_sim_below_mem >>
  simp[expr_ok_def])
QED

Theorem word_modular_names_sim:
  !cenv ann bt args.
    (bt = AddMod \/ bt = MulMod \/ bt = PowMod256) /\
    EVERY (\e. ?t id. e = Name t id) args ==>
    expr_vv_ok cenv (Builtin ann bt args)
Proof
  rpt gen_tac >> strip_tac >> (rewrite_tac[expr_vv_ok_def] >> rpt strip_tac >>
  `well_typed_builtin_app ann bt (MAP expr_type args)` by
    gvs[expr_sim_pre_def, well_typed_expr_def] >>
  drule_at Any word_builtin_modular_types >> simp[] >> strip_tac >>
  `EVERY word_value_type (MAP expr_type args)` by
    gvs[word_value_type_def] >>
  `EVERY (expr_sim_ok cenv) args` by
    (gvs[EVERY_MEM, EVERY_MAP] >> rpt strip_tac >>
     qpat_x_assum `!e. MEM e args ==> ?t id. _` drule >> strip_tac >> gvs[] >>
     first_x_assum drule >> simp[] >> strip_tac >>
     irule word_name_sim_ok >> gvs[vyperASTTheory.expr_type_def]) >>
  irule (SRULE[expr_vv_ok_def] word_builtin_args_vv_sim) >> simp[] >>
  qexists_tac `env` >> gvs[])
QED

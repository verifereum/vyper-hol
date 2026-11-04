(* Ordinary unary expression simulation composition. *)
Theory exprSimUnop
Ancestors
  exprSimUnopProps
  exprSimProps
  exprSimDefs
  loweringPosts
  arithmetic list integer words integer_word byte
  fragExec varsExt  freshWrites
  exprBopLowering loweringSlice
  exprLowering emitHelper emitHelperProps exprLoweringProps
  builtinSimple builtinProps
  compileEnv vyperAST vyperInterpreter vyperState vyperContext vyperValue
  vyperValueOperation valueEncoding venomExecSemantics venomInst venomState
  vyperTyping
Libs
  intLib pairLib


Definition unop_frag_def:
  unop_frag ctx func cenv cx f w1 t res es0 <=>
    !sa sb x op s0.
      f x sa = (op, sb) /\ expr_res_ok res /\
      (!z. x = Var z ==> not_fresh_at sa z) /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa ==>
      frag_exec ctx sa sb
        (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es0 s /\
             eval_operand x s = SOME w1)
        (\s. ?v. res = INL v /\
                 stmt_state_rel ctx func cenv cx es0 s /\
                 expr_val_rel cx t v op s /\
                 (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
                        lookup_var z s = SOME w) /\
                 (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                          FLOOKUP s.vs_allocas aid = SOME b) /\
                 s.vs_memory = s0.vs_memory)
        (expr_exit res)
End

Theorem unop_frag_straight:
  !ctx func cenv cx f w1 t res es0.
    (!x. straight_fresh (f x)) /\ is_word_type t /\
    (expr_res_ok res ==>
     (?v w. res = INL v /\
            (!tv. evaluate_type (get_tenv cx) t = SOME tv ==>
                  w = typed_val_to_w256 tv v) /\
            !x sa sb op ss.
              f x sa = (op, sb) /\ fresh_vars_wrt sa ss /\
              eval_operand x ss = SOME w1 ==>
              ?ss'. run_inst_seq (emitted_insts sa sb) ss = OK ss' /\
                    eval_operand op ss' = SOME w) \/
     (?m. res = INR (Error (RuntimeError m)) /\
          !x sa sb op ss.
            f x sa = (op, sb) /\ fresh_vars_wrt sa ss /\
            eval_operand x ss = SOME w1 ==>
            ?ss'. run_inst_seq (emitted_insts sa sb) ss =
                    Abort Revert_abort ss')) ==>
    unop_frag ctx func cenv cx f w1 t res es0
Proof
  rpt gen_tac >> strip_tac >> simp[unop_frag_def] >> rpt gen_tac >>
  strip_tac >>
  qpat_x_assum `expr_res_ok _ ==> _` drule >> strip_tac
  >- (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es0`, `f x`, `sa`, `sb`,
         `op`, `w`, `\ss. eval_operand x ss = SOME w1`,
         `\a. F`, `expr_exit res`, `s0`]
        mp_tac frag_exec_straight_fresh >>
      (impl_tac
       >- (asm_rewrite_tac[] >> BETA_TAC >> rpt conj_tac >> rpt strip_tac
           >>~- ([`eval_operand _ (drop_fresh _ _) = _`],
                 qspecl_then [`x`, `sa`, `ss`] mp_tac eval_operand_drop_fresh >>
                 asm_simp_tac bool_ss []) >>
           qpat_x_assum `!x sa sb op ss. _`
             (qspecl_then [`x`, `sa`, `sb`, `op`, `ss`] mp_tac) >>
           asm_rewrite_tac[])) >>
      disch_then (fn th => match_mp_tac (MATCH_MP frag_exec_weaken th)) >>
      simp[] >> rpt strip_tac >> gvs[expr_val_rel_def]) >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es0`, `f x`, `sa`, `sb`, `op`,
     `\ss. eval_operand x ss = SOME w1`,
     `\a. a = Revert_abort`, `\s. F`, `expr_exit res`, `s0`]
    mp_tac frag_exec_straight_fresh_abort >>
  (impl_tac
   >- (asm_rewrite_tac[] >> BETA_TAC >> rpt conj_tac >> rpt strip_tac
       >>~- ([`expr_exit _ _`], gvs[expr_exit_def])
       >>~- ([`eval_operand _ (drop_fresh _ _) = _`],
             qspecl_then [`x`, `sa`, `ss`] mp_tac eval_operand_drop_fresh >>
             asm_simp_tac bool_ss []) >>
       qpat_x_assum `!x sa sb op ss. _`
         (qspecl_then [`x`, `sa`, `sb`, `op`, `ss`] mp_tac) >>
       asm_rewrite_tac[] >> metis_tac[])) >>
  disch_then (fn th => match_mp_tac (MATCH_MP frag_exec_weaken th)) >>
  gvs[]
QED

Theorem compile_not_frag:
  !ctx func cenv cx ann tys v1 es0 tv1.
    (is_bool_type ann \/ is_uint256_type ann \/ is_bytes32_type ann \/
     is_flag_type ann) /\
    evaluate_type (get_tenv cx) ann = SOME tv1 /\ value_has_type tv1 v1 /\
    (!nsid m. ann = FlagT nsid /\ tv1 = FlagTV m ==>
              cenv.ce_flag_n_members (nsid_to_string nsid) = m) ==>
    unop_frag ctx func cenv cx
      (\x. if ann = BaseT BoolT then emit_op ISZERO [x]
           else compile_invert x ann cenv)
      (typed_val_to_w256 tv1 v1) ann (unop_result cx ann Not tys v1 es0) es0
Proof
  rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 (strip_assume_tac o MATCH_MP not_type_cases)
                              strip_assume_tac) >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  irule unop_frag_straight >>
  (conj_tac
   >- (gen_tac >> simp[compile_invert_def, LET_THM] >>
       irule straight_fresh_emit_op >> simp[fresh_write_op_def])) >>
  (conj_tac >- simp[is_word_type_def]) >>
  disch_then kall_tac >> disj1_tac >>
  Cases_on `v1` >>
  gvs[value_has_type_def, unop_result_def, evaluate_builtin_def,
      vyperASTTheory.type_to_int_bound_def, typed_val_to_w256_def,
      val_to_w256_def, compile_invert_def, vyperValueTheory.evaluate_type_def]
  >~ [`emit_op ISZERO`]
  >- (rpt strip_tac >> drule_all emit_op_ISZERO_correct_mem >> strip_tac >>
      qexists_tac `ss'` >> asm_rewrite_tac[] >> BasicProvers.every_case_tac >>
      gvs[bool_to_word_def])
  >~ [`i2w _`]
  >- (rename1 `Num i` >> rpt strip_tac >>
      drule_all emit_op_NOT_correct >> rw[] >>
      `~(i < 0)` by intLib.ARITH_TAC >>
      simp[integer_wordTheory.i2w_pos, integer_wordTheory.i2w_def])
  >~ [`PAD_RIGHT`]
  >- (rename1 `LENGTH bs = 32` >> rpt strip_tac >> gvs[listTheory.PAD_RIGHT] >>
      drule_all emit_op_NOT_correct >> rw[] >>
      simp[listTheory.PAD_RIGHT, length_word_to_bytes_be,
           word_of_bytes_be_to_bytes]) >>
  rename1 `k < 2 ** m` >> rpt strip_tac >>
  qspecl_then [`XOR`, `word_xor`, `x`, `Lit (n2w (2 ** m - 1))`, `n2w k`,
               `n2w (2 ** m - 1)`, `sa`, `op`, `sb`, `ss`]
    mp_tac emit_op_pure2_correct >>
  impl_tac
  >- (simp[eval_operand_def] >> irule step_XOR >> simp[eval_operand_def]) >>
  rw[] >> simp[flag_not_xor]
QED

Theorem compile_abs_frag:
  !ctx func cenv cx tys v1 es0.
    value_has_type (BaseTV (IntT 256)) v1 ==>
    unop_frag ctx func cenv cx compile_builtin_abs
      (typed_val_to_w256 (BaseTV (IntT 256)) v1) (BaseT (IntT 256))
      (unop_result cx (BaseT (IntT 256)) Abs tys v1 es0) es0
Proof
  rpt strip_tac >> irule unop_frag_straight >>
  rpt conj_tac
  >- simp[straight_fresh_abs]
  >- simp[is_word_type_def] >>
  disch_then kall_tac >>
  Cases_on `v1` >> gvs[value_has_type_def] >>
  rename1 `within_int_bound _ i` >>
  drule int256_abs_bound >> strip_tac >>
  drule_all abs_i2w >> strip_tac >>
  simp[unop_result_def, evaluate_builtin_def,
       vyperASTTheory.type_to_int_bound_def, bounded_int_op_def,
       typed_val_to_w256_def, val_to_w256_def] >>
  Cases_on `i = INT_MIN (:256)`
  >- (`i2w i = (INT_MINw : bytes32)` by metis_tac[] >>
      qpat_x_assum `i = _`
        (fn th => REWRITE_TAC [EQT_INTRO (SIMP_RULE (srw_ss()) [] th)]) >>
      disj2_tac >> simp[] >>
      rpt strip_tac >> drule_all compile_builtin_abs_run >> simp[]) >>
  `i2w i <> (INT_MINw : bytes32)` by metis_tac[] >>
  qpat_x_assum `i <> _`
    (fn th => REWRITE_TAC [EQF_INTRO (SIMP_RULE (srw_ss()) [] th)]) >>
  disj1_tac >>
  simp[vyperValueTheory.evaluate_type_def, typed_val_to_w256_def,
       val_to_w256_def] >>
  rpt strip_tac >> drule_all compile_builtin_abs_run >>
  disch_then (drule o CONJUNCT1) >> strip_tac >>
  qexists_tac `ss'` >> asm_rewrite_tac[] >> simp[]
QED

Theorem compile_unop_sim:
  !ctx func cenv cx ty ann bi e1 ty1 f es.
    bi <> Len /\ builtin_args_length_ok bi 1 /\
    is_word_type ann /\ is_word_type (expr_type e1) /\
    (!sa sb op.
       lower_value compile_expr cenv ty (Builtin ann bi [e1]) sa = (op, sb) ==>
       ?x s1. lower_value compile_expr cenv ty1 e1 sa = (x, s1) /\
              f x s1 = (op, sb)) /\
    (!sa sb op.
       lower_value compile_expr cenv ty1 e1 sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       (!z. op = Var z ==> not_fresh_at sb z)) /\
    (!x sa sb op. f x sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
    expr_sim ctx func cenv cx ty1 e1 es /\
    (!v1 es1. (do r <- eval_expr cx e1; read_result cx r od) es = (INL v1, es1) ==>
       ?tv1. evaluate_type (get_tenv cx) (expr_type e1) = SOME tv1 /\
             unop_frag ctx func cenv cx f (typed_val_to_w256 tv1 v1) ann
               (unop_result cx ann bi [expr_type e1] v1 es1) es1) ==>
    expr_sim ctx func cenv cx ty (Builtin ann bi [e1]) es
Proof
  rpt gen_tac >> strip_tac >>
  simp[expr_sim_def] >> rpt gen_tac >> strip_tac >>
  reverse (Cases_on `stmt_state_rel ctx func cenv cx es s0`)
  >- (`frag_exec ctx sa sb (\s. F) (\s. F) (\r. F)` by
        simp[frag_exec_false_pre] >>
      pop_assum (fn th => irule (MATCH_MP frag_exec_weaken th)) >>
      simp[]) >>
  qpat_x_assum `!sa sb op. lower_value _ _ ty (Builtin _ _ _) _ = _ ==> _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `!sa sb op. lower_value _ _ ty1 e1 _ = _ ==> _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `!x sa sb op. f _ _ = _ ==> _`
    (drule_then strip_assume_tac) >>
  `fn_has_code sa s1 func /\ fn_has_code s1 sb func` by
    (irule fn_has_code_split >> asm_rewrite_tac[]) >>
  `local_ptrs_reserved cenv s1` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >>
     asm_rewrite_tac[]) >>
  `builtin_args_length_ok bi 1 /\ bi <> Len` by asm_rewrite_tac[] >>
  drule_all eval_expr_unop_cases >> strip_tac
  >- ((* e1 raises *)
      qpat_x_assum `expr_sim _ _ _ _ _ e1 _`
        (mp_tac o REWRITE_RULE [expr_sim_def]) >>
      disch_then (qspecl_then [`sa`, `s1`, `x`, `INR exc`, `es'`, `s0`]
                    mp_tac) >>
      (impl_tac >- gvs[]) >>
      disch_then (mp_tac o MATCH_MP frag_exec_weaken) >>
      disch_then (qspecl_then [`\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s`,
                               `\s. F`, `expr_exit res`] mp_tac) >>
      (impl_tac >- gvs[]) >> strip_tac >>
      irule frag_exec_exit_prefix >> qexists_tac `s1` >> simp[])
  >>
  qpat_x_assum `!v1 es1. bind _ _ es = _ ==> _` drule >>
  strip_tac >>
  qpat_x_assum `expr_sim _ _ _ _ _ e1 _`
    (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`sa`, `s1`, `x`, `INL v1`, `es'`, `s0`]
                mp_tac) >>
  (impl_tac >- simp[expr_res_ok_def]) >>
  disch_then (mp_tac o MATCH_MP frag_exec_pre_exit_c) >>
  disch_then (qspecl_then [`\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s`,
                           `expr_exit res`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (fn th => irule (MATCH_MP frag_exec_then th)) >>
  asm_rewrite_tac[] >> rpt strip_tac >> fs[] >>
  rename1 `expr_post ctx func cenv cx e1 es sa s1 s0 es' v1 x t0` >>
  `stmt_state_rel ctx func cenv cx es' t0 /\
   eval_operand x t0 = SOME (typed_val_to_w256 tv1 v1)` by
    gvs[expr_post_def, expr_val_rel_def] >>
  qpat_x_assum `unop_frag _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [unop_frag_def]) >>
  disch_then (qspecl_then [`s1`, `sb`, `x`, `op`, `t0`] mp_tac) >>
  (impl_tac >- (gvs[] >> metis_tac[not_fresh_at_mono])) >>
  disch_then (fn th => match_mp_tac (MATCH_MP frag_exec_weaken th)) >> gvs[] >>
  rpt strip_tac >> gvs[] >>
  irule expr_post_unop >> simp[] >>
  qexistsl_tac [`s1`, `t0`, `v1`, `x`] >> simp[]
QED

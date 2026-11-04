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

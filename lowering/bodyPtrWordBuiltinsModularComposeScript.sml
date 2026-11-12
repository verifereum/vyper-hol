(* Valid-arity modular builtin instances of counted operand composition. *)
Theory bodyPtrWordBuiltinsModularCompose
Ancestors bodyPtrWordBuiltinsArgsCompose bodyPtrWordBuiltinsModularContinue
  bodyPtrWordBuiltinsTypedShapes bodyPtrDefs bodyPtrPreds bodySim
  exprSimWordBuiltins exprSimWordArgs exprSimPrecompiles exprSimSource
  exprSimHypsDefs exprSimDefs exprPtrUnwrap exprLowering exprLoweringProps
  fragExec fragGasFresh compileEnv vyperAST vyperInterpreter vyperTypeSystem
  vyperTyping vyperValue list loweringPosts ptrDiscipline builtinProps vyperContext

Theorem word_pow_sim_ptr:
  body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env (Builtin ann PowMod256 [a;b]) es /\
  body_exprs_ptr_ok cx [a;b] ==>
  expr_sim_ptr d ctx PG func cenv cx ty (Builtin ann PowMod256 [a;b]) es
Proof
  strip_tac >>
  `ann = BaseT (UintT 256) /\ EVERY (\e. expr_type e = BaseT (UintT 256)) [a;b]` by
    (drule_at Any word_modular_types >> simp[]) >>
  irule word_args_compose_sim_ptr >> simp[is_word_type_def, builtin_args_length_ok_def,
    precompile_builtin_def] >>
  reverse conj_tac >- metis_tac[] >>
  qexists_tac `\xs. compile_pow_mod256 (EL 0 xs) (EL 1 xs)` >> simp[straight_fresh_compile_modular] >>
  reverse conj_tac
  >- (rpt strip_tac >> drule lower_value_pow_mod256 >> strip_tac >>
      qexistsl_tac [`[x;y]`, `s2`] >>
      simp[lower_word_args_def, comp_bind_def, comp_return_def]) >>
  rpt gen_tac >> strip_tac >>
  `LENGTH xs = 2` by gvs[wb_args_post_def, LIST_REL_EL_EQN] >>
  Cases_on `xs` >> gvs[] >> rename1 `LENGTH tail = 1` >> Cases_on `tail` >> gvs[] >>
  gvs[LIST_REL_CONS1] >> irule word_pow_expr_outcome >> simp[] >> metis_tac[]
QED

Theorem word_modular_sim_ptr:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (Builtin ann (if is_mul then MulMod else AddMod) [a;b;m]) es /\
  body_exprs_ptr_ok cx [a;b;m] ==>
  expr_sim_ptr d ctx PG func cenv cx ty (Builtin ann (if is_mul then MulMod else AddMod) [a;b;m]) es
Proof
  strip_tac >>
  `ann = BaseT (UintT 256) /\ EVERY (\e. expr_type e = BaseT (UintT 256)) [a;b;m]` by
    (drule_at Any word_modular_types >>
     `((if is_mul then MulMod else AddMod) = AddMod \/
       (if is_mul then MulMod else AddMod) = MulMod)` by (Cases_on `is_mul` >> simp[]) >>
     simp[]) >>
  irule word_args_compose_sim_ptr >>
  simp[is_word_type_def, builtin_args_length_ok_def, precompile_builtin_def] >>
  reverse conj_tac
  >- (Cases_on `is_mul` >> gvs[precompile_builtin_def, builtin_args_length_ok_def] >> metis_tac[]) >>
  qexists_tac `\xs. (if is_mul then compile_mulmod else compile_addmod)
     (EL 0 xs) (EL 1 xs) (EL 2 xs)` >>
  simp[] >> reverse conj_tac
  >- (conj_tac
      >- (rpt strip_tac >> drule_at Any lower_value_ternary_modular >>
      `((if is_mul then MulMod else AddMod) = AddMod \/
        (if is_mul then MulMod else AddMod) = MulMod)` by (Cases_on `is_mul` >> simp[]) >>
      simp[] >> strip_tac >> qexistsl_tac [`[x;y;z]`, `s3`] >>
      simp[lower_word_args_def, comp_bind_def, comp_return_def] >>
      Cases_on `is_mul` >> gvs[]) >>
      gen_tac >> Cases_on `is_mul` >> simp[straight_fresh_compile_modular]) >>
  rpt gen_tac >> strip_tac >>
  `LENGTH xs = 3` by gvs[wb_args_post_def, LIST_REL_EL_EQN] >>
  Cases_on `xs` >> gvs[] >> rename1 `SUC (LENGTH tail) = 3` >>
  Cases_on `tail` >> gvs[] >> rename1 `SUC (SUC (LENGTH tail)) = 3` >> Cases_on `tail` >> gvs[] >>
  gvs[arithmeticTheory.ADD1, LIST_REL_CONS1] >> irule word_modular_expr_outcome >> simp[] >> metis_tac[]
QED

Theorem word_modular_vv_sim_ptr:
  expr_sim_ptr d ctx PG func cenv cx ty (Builtin ann bt args) es /\
  ((bt = PowMod256 /\ LENGTH args = 2) \/
   ((bt = AddMod \/ bt = MulMod) /\ LENGTH args = 3)) ==>
  expr_vv_sim_ptr d ctx PG func cenv cx ty (Builtin ann bt args) es
Proof
  strip_tac >> (irule expr_vv_sim_ptr_stack >> simp[] >> conj_tac
  >- (gen_tac >> Cases_on `compile_expr cenv ty (Builtin ann bt args) sa` >>
      `?op. q = StackValue ann op` by
        (irule compile_word_builtin_stack >> goal_assum (drule_at Any) >> metis_tac[]) >> gvs[]) >>
  metis_tac[eval_expr_builtin_value])
QED

Theorem body_word_pow_ptr_ok:
  body_exprs_ptr_ok cx [a;b] ==> body_expr_ptr_ok cx (Builtin ann PowMod256 [a;b])
Proof
  strip_tac >> simp[body_expr_ptr_ok_def] >> rpt gen_tac >> strip_tac >>
  drule_all word_pow_sim_ptr >> strip_tac >>
  conj_tac >- simp[] >> irule word_modular_vv_sim_ptr >> simp[]
QED

Theorem body_word_modular_ptr_ok:
  body_exprs_ptr_ok cx [a;b;m] ==>
  body_expr_ptr_ok cx (Builtin ann (if is_mul then MulMod else AddMod) [a;b;m])
Proof
  strip_tac >> simp[body_expr_ptr_ok_def] >> rpt gen_tac >> strip_tac >>
  drule_all word_modular_sim_ptr >> strip_tac >>
  conj_tac >- simp[] >> irule word_modular_vv_sim_ptr >> simp[] >>
  Cases_on `is_mul` >> simp[]
QED

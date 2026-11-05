(*
 * Expression simulation: in and not in on an array literal of words
 * (#569).  The lowering unrolls it to a comparison with each element
 * (compile_multi_exprs, compile_list_membership_in), so it takes the
 * elements' judgments, not the array's.  An array literal of non-words is
 * held for #742 (exprSimBopHeld).
 *
 * TOP-LEVEL:
 *   compile_bop_in_literal_word_case — that case, from the needle's and
 *                                      elements' case judgments (any nocalls)
 *   compile_bop_in_literal_word_sim  — that case at expr_ok
 *)

Theory exprSimBopInLiteralWord
Ancestors
  exprSimUnopCompose exprSimWordArgs loweringPosts valueEncoding
  exprSimBopTyped exprBopSimProps
  exprSimUnopProps
  exprSimSource
  exprSimHypsDefs
  exprSimDefs
  allocLimits
  list finite_map
  fragExec  exprSimHyps exprSimOps exprSimBinopFrag
  exprSimUnop exprSimCompare
  exprBopLowering exprWordOperand
  loweringSlice
  exprLowering compileEnv
  vyperAST vyperInterpreter vyperState vyperContext vyperTypeSystem
  vyperValue vyperValueOperation
  vyperTypeCallGraph
  vyperTyping vyperTypeInvariants vyperTypeExprResult vyperTypeExprSoundness
  vyperStatePreservation

Theorem literal_word_operand:
  expr_val_rel cx ty v op s /\ is_word_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv ==>
  eval_operand op s = SOME (typed_val_to_w256 tv v)
Proof
  simp[expr_val_rel_def] >> metis_tac[]
QED

Theorem literal_word_post_operand:
  expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
  is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
  eval_operand op s = SOME (typed_val_to_w256 tv v)
Proof
  metis_tac[expr_post_def, literal_word_operand]
QED

Theorem literal_word_post_cons:
  expr_post ctx func cenv cx e es sa s1 s0 es1 v x t /\
  stmt_state_rel ctx func cenv cx es' u /\
  LIST_REL (\x v. eval_operand x u = SOME (typed_val_to_w256 tv v)) xs vs /\
  wb_frame cenv es1 s1 t u /\
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= s1.cs_next_var /\ sa.cs_next_id <= s1.cs_next_id /\
  is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\ (!l. x <> Label l) ==>
  stmt_state_rel ctx func cenv cx es' u /\
  LIST_REL (\x v. eval_operand x u = SOME (typed_val_to_w256 tv v)) (x::xs) (v::vs) /\
  wb_frame cenv es sa s0 u
Proof
  strip_tac >>
  `eval_operand x t = SOME (typed_val_to_w256 tv v)` by
    metis_tac[literal_word_post_operand] >>
  `wb_frame cenv es sa s0 t` by metis_tac[expr_post_frame] >>
  simp[] >> conj_tac
  >- (irule eval_operand_frame >> goal_assum (drule_at Any) >>
      simp[] >> metis_tac[wb_frame_vars]) >>
  irule wb_frame_trans >> simp[] >> conj_tac
  >- (qexistsl_tac [`es1`, `s1`, `t`] >> simp[]) >>
  qexistsl_tac [`ctx`, `cx`, `func`] >> simp[]
QED

Definition literal_word_args_ready_def:
  (literal_word_args_ready ctx func cenv cx arg_ty tv Inv [] = T) /\
  (literal_word_args_ready ctx func cenv cx arg_ty tv Inv (e::args) =
    ((!es. Inv es ==>
       expr_sim ctx func cenv cx (arg_ty e) e es /\
       is_word_type (expr_type e) /\
       evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
       (!res es'. (do r <- eval_expr cx e; read_result cx r od) es = (res, es') ==> expr_res_ok res) /\
       (!v es'. (do r <- eval_expr cx e; read_result cx r od) es = (INL v, es') ==> Inv es')) /\
     ((?s r t s1 v t1. eval_expr cx e s = (INL r, t) /\
                       read_result cx r s1 = (INL v, t1)) ==>
       literal_word_args_ready ctx func cenv cx arg_ty tv Inv args)))
End

Theorem literal_word_args_ready_head:
  literal_word_args_ready ctx func cenv cx arg_ty tv Inv (e::args) /\ Inv es ==>
  expr_sim ctx func cenv cx (arg_ty e) e es /\
  is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  (!res es'. (do r <- eval_expr cx e; read_result cx r od) es = (res, es') ==> expr_res_ok res) /\
  (!v es'. (do r <- eval_expr cx e; read_result cx r od) es = (INL v, es') ==> Inv es')
Proof
  simp[literal_word_args_ready_def] >> metis_tac[]
QED

Theorem literal_word_args_ready_tail:
  literal_word_args_ready ctx func cenv cx arg_ty tv Inv (e::args) /\
  eval_expr cx e s = (INL r, t) /\ read_result cx r s1 = (INL v, t1) ==>
  literal_word_args_ready ctx func cenv cx arg_ty tv Inv args
Proof
  simp[literal_word_args_ready_def] >> metis_tac[]
QED

Theorem literal_word_args_ready_nil[simp]:
  literal_word_args_ready ctx func cenv cx arg_ty tv Inv []
Proof
  simp[literal_word_args_ready_def]
QED

Theorem literal_word_post_singleton:
  expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
  is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
  stmt_state_rel ctx func cenv cx es' s /\
  LIST_REL (\x v. eval_operand x s = SOME (typed_val_to_w256 tv v)) [op] [v] /\
  wb_frame cenv es sa s0 s
Proof
  strip_tac >> simp[] >>
  metis_tac[literal_word_post_operand, expr_post_state, expr_post_frame]
QED

Theorem literal_enumerate_membership:
  !vs k. MEM v (MAP SND (enumerate_static_array d k vs)) <=>
          MEM v vs /\ v <> d
Proof
  Induct >> simp[enumerate_static_array_def] >>
  rpt gen_tac >> IF_CASES_TAC >> gvs[] >> metis_tac[]
QED

Theorem literal_enumerate_length:
  !vs k. LENGTH (enumerate_static_array d k vs) <= LENGTH vs /\
    (LENGTH (enumerate_static_array d k vs) < LENGTH vs <=> MEM d vs)
Proof
  Induct >> simp[enumerate_static_array_def] >>
  rpt gen_tac >> IF_CASES_TAC >> gvs[] >>
  first_x_assum (qspec_then `SUC k` mp_tac) >> simp[]
QED

Theorem literal_array_membership:
  compatible_bound bd (LENGTH vs) ==>
  (evaluate_in_array (ArrayTV tv bd) v (make_array_value tv bd vs) <=> MEM v vs)
Proof
  Cases_on `bd` >>
  simp[compatible_bound_def, evaluate_in_array_def, make_array_value_def,
       literal_enumerate_membership, literal_enumerate_length] >>
  metis_tac[]
QED

Theorem literal_membership_typing:
  well_typed_binop ann bop et a /\ (bop = In \/ bop = NotIn) /\
  well_typed_builtin_app a (MakeArray t n) (MAP expr_type elems) ==>
  ann = BaseT BoolT /\ a = ArrayT et n /\ t = SOME et /\
  compatible_bound n (LENGTH elems) /\
  EVERY (\e. expr_type e = et) elems
Proof
  strip_tac >> Cases_on `t` >>
  gvs[well_typed_builtin_app_def, well_typed_binop_def, EVERY_MAP] >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem literal_membership_result:
  compatible_bound bd (LENGTH vs) /\ (bop = In \/ bop = NotIn) ==>
  evaluate_binop u (ArrayTV tv bd) bop v (ArrayV (make_array_value tv bd vs)) =
    INL (BoolV (if bop = In then MEM v vs else ~MEM v vs))
Proof
  strip_tac >> gvs[evaluate_binop_def, binop_negate_def,
                         literal_array_membership]
QED

Theorem literal_body_typing:
  expr_body_pre cenv cx env
    (Builtin ann (Bop bop) [e1; Builtin a (MakeArray t n) elems]) es /\
  (bop = In \/ bop = NotIn) ==>
  ann = BaseT BoolT /\ a = ArrayT (expr_type e1) n /\ t = SOME (expr_type e1) /\
  compatible_bound n (LENGTH elems) /\
  EVERY (\e. expr_type e = expr_type e1) elems
Proof
  simp[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def,
       expr_type_def] >> metis_tac[literal_membership_typing]
QED

Theorem literal_body_operand_pre:
  expr_body_pre cenv cx env
    (Builtin ann (Bop bop) [e1; Builtin a (MakeArray t n) elems]) es /\
  MEM e (e1::elems) /\ expr_sim_inv cenv cx env es' ==>
  expr_body_pre cenv cx env e es'
Proof
  strip_tac >> gvs[]
  >- metis_tac[expr_body_pre_builtin_arg, MEM] >>
  `expr_body_pre cenv cx env (Builtin a (MakeArray t n) elems) es'` by
    metis_tac[expr_body_pre_builtin_arg, MEM] >>
  metis_tac[expr_body_pre_builtin_arg]
QED
Theorem literal_make_array_action:
  compatible_bound n (LENGTH elems) /\
  evaluate_type (get_tenv cx) et = SOME tv ==>
  bind (eval_expr cx (Builtin a (MakeArray (SOME et) n) elems)) (read_result cx) =
  bind (eval_exprs cx elems) (\vs. vyperState$return (ArrayV (make_array_value tv n vs)))
Proof
  strip_tac >>
  `MakeArray (SOME et) n <> Len /\ MakeArray (SOME et) n <> Env MsgGas /\
   ~precompile_builtin (MakeArray (SOME et) n) /\
   builtin_args_length_ok (MakeArray (SOME et) n) (LENGTH elems)` by
    simp[precompile_builtin_def, builtin_args_length_ok_def] >>
  drule_all eval_expr_builtin_action >>
  disch_then (qspecl_then [`cx`, `a`] mp_tac) >>
  simp[builtin_result_def, evaluate_builtin_def] >>
  disch_then SUBST1_TAC >>
  AP_TERM_TAC >> simp[FUN_EQ_THM, vyperStateTheory.return_def]
QED

Theorem literal_make_array_continuation:
  compatible_bound n (LENGTH elems) /\
  evaluate_type (get_tenv cx) et = SOME tv ==>
  vyperState$bind (eval_expr cx (Builtin a (MakeArray (SOME et) n) elems))
    (\r. vyperState$bind (read_result cx r) k) =
  vyperState$bind (eval_exprs cx elems) (\vs. k (ArrayV (make_array_value tv n vs)))
Proof
  strip_tac >> drule_all literal_make_array_action >>
  disch_then (qspec_then `a` mp_tac) >>
  disch_tac >>
  pure_once_rewrite_tac[GSYM vyperStateTheory.bind_assoc] >>
  asm_rewrite_tac[] >>
  simp[vyperStateTheory.bind_assoc, vyperStateTheory.bind_return]
QED

Theorem literal_make_array_value_continuation:
  compatible_bound n (LENGTH elems) /\
  evaluate_type (get_tenv cx) et = SOME tv ==>
  vyperState$bind (eval_expr cx (Builtin a (MakeArray (SOME et) n) elems))
    (\r. vyperState$bind (read_result cx r)
      (k : value -> evaluation_state -> (value + vyperState$exception) # evaluation_state)) =
  vyperState$bind (eval_exprs cx elems) (\vs. k (ArrayV (make_array_value tv n vs)))
Proof
  MATCH_ACCEPT_TAC literal_make_array_continuation
QED

Theorem literal_membership_action_prefix:
  compatible_bound n (LENGTH elems) /\
  evaluate_type (get_tenv cx) et = SOME tv ==>
  bind (eval_expr cx (Builtin ann (Bop bop)
    [e1; Builtin a (MakeArray (SOME et) n) elems])) (read_result cx) =
  bind (bind (eval_expr cx e1) (read_result cx))
    (\v. bind (eval_exprs cx elems)
      (\vs ee. (builtin_result cx ee.accounts ann (Bop bop)
        [expr_type e1; a] [v; ArrayV (make_array_value tv n vs)], ee)))
Proof
  strip_tac >>
  `Bop bop <> Len /\ Bop bop <> Env MsgGas /\
   ~precompile_builtin (Bop bop) /\
   builtin_args_length_ok (Bop bop) 2` by
    simp[precompile_builtin_def, builtin_args_length_ok_def] >>
  `eval_exprs cx [] = vyperState$return []` by
    simp[FUN_EQ_THM, eval_exprs_nil, vyperStateTheory.return_def] >>
  simp[Once eval_expr_builtin_action] >>
  simp[expr_type_def, eval_exprs_cons_action,
       vyperStateTheory.bind_assoc, vyperStateTheory.bind_return] >>
  AP_TERM_TAC >> ABS_TAC >> AP_TERM_TAC >> ABS_TAC >>
  drule_all literal_make_array_value_continuation >>
  disch_then (qspecl_then [
    `\v' ee. (builtin_result cx ee.accounts ann (Bop bop)
      [expr_type e1; a] [v; v'], ee)`, `a`] mp_tac) >> simp[]
QED

Theorem literal_membership_action:
  compatible_bound n (LENGTH elems) /\
  evaluate_type (get_tenv cx) et = SOME tv /\
  evaluate_type (get_tenv cx) (ArrayT et n) = SOME (ArrayTV tv n) /\
  (bop = In \/ bop = NotIn) ==>
  bind (eval_expr cx (Builtin ann (Bop bop)
    [e1; Builtin (ArrayT et n) (MakeArray (SOME et) n) elems])) (read_result cx) =
  bind (bind (eval_expr cx e1) (read_result cx))
    (\v. bind (eval_exprs cx elems)
      (\vs. vyperState$return (BoolV (if bop = In then MEM v vs else ~MEM v vs))))
Proof
  strip_tac >>
  qpat_x_assum `evaluate_type _ (ArrayT _ _) = _` mp_tac >>
  drule_all literal_membership_action_prefix >>
  disch_then (fn th => rewrite_tac[th]) >> disch_tac >>
  AP_TERM_TAC >> ABS_TAC >>
  rewrite_tac[FUN_EQ_THM] >> gen_tac >>
  simp[vyperStateTheory.bind_def, vyperStateTheory.return_def] >>
  rename1 `eval_exprs cx elems st` >>
  Cases_on `eval_exprs cx elems st` >>
  rename1 `eval_exprs cx elems st = (res, st')` >>
  Cases_on `res` >> gvs[] >>
  rename1 `eval_exprs cx elems st = (INL vs, st')` >>
  drule eval_exprs_length >> disch_tac >>
  `compatible_bound n (LENGTH vs)` by metis_tac[] >>
  simp[builtin_result_def, evaluate_builtin_def, literal_membership_result]
QED
Theorem literal_body_evaluate_types:
  expr_body_pre cenv cx env
    (Builtin ann (Bop bop) [e1; Builtin a (MakeArray t n) elems]) es /\
  (bop = In \/ bop = NotIn) ==>
  ?tv. evaluate_type (get_tenv cx) (expr_type e1) = SOME tv /\
       evaluate_type (get_tenv cx) a = SOME (ArrayTV tv n)
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  drule_all literal_body_typing >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    fs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def,
       env_context_consistent_def] >>
  `well_formed_type env.type_defs a` by
    fs[expr_body_pre_def, well_typed_expr_def] >>
  gvs[well_formed_type_def] >>
  qpat_x_assum `IS_SOME _` mp_tac >>
  simp[Once evaluate_type_def] >>
  Cases_on `evaluate_type (get_tenv cx) (expr_type e1)` >> simp[] >>
  simp[Once evaluate_type_def]
QED
Theorem literal_body_action:
  expr_body_pre cenv cx env
    (Builtin ann (Bop bop) [e1; Builtin a (MakeArray t n) elems]) es /\
  (bop = In \/ bop = NotIn) ==>
  bind (eval_expr cx (Builtin ann (Bop bop)
    [e1; Builtin a (MakeArray t n) elems])) (read_result cx) =
  bind (bind (eval_expr cx e1) (read_result cx))
    (\v. bind (eval_exprs cx elems)
      (\vs. vyperState$return (BoolV (if bop = In then MEM v vs else ~MEM v vs))))
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  drule_all literal_body_evaluate_types >> strip_tac >>
  drule_all literal_body_typing >> strip_tac >>
  gvs[] >>
  drule_at (Pat `evaluate_type _ (ArrayT _ _) = _`) literal_membership_action >>
  simp[]
QED

Theorem literal_operand_result:
  expr_body_pre cenv cx env
    (Builtin ann (Bop bop) [e1; Builtin a (MakeArray t n) elems]) es /\
  MEM e (e1::elems) /\ expr_sim_inv cenv cx env es0 /\
  (do r <- eval_expr cx e; read_result cx r od) es0 = (res, es1) ==>
  expr_sim_inv cenv cx env es1 /\ expr_res_ok res /\
  !v tv. res = INL v /\ evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
    value_has_type tv v
Proof
  strip_tac >>
  `expr_body_pre cenv cx env e es0` by metis_tac[literal_body_operand_pre] >>
  `env.type_defs = get_tenv cx` by
    fs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def,
       env_context_consistent_def] >>
  drule_all expr_body_pre_res_ok >> disch_tac >>
  drule_all expr_body_pre_eval >> strip_tac >> simp[] >>
  rpt strip_tac >> first_x_assum drule >>
  gvs[expr_result_typed_def, expr_runtime_typed_def, value_result_typed_def]
QED

Theorem literal_operand_word_type:
  expr_body_pre cenv cx env
    (Builtin ann (Bop bop) [e1; Builtin a (MakeArray t n) elems]) es /\
  (bop = In \/ bop = NotIn) /\ is_word_type (expr_type e1) /\
  MEM e (e1::elems) ==>
  expr_type e = expr_type e1 /\ is_word_type (expr_type e)
Proof
  strip_tac >> drule literal_body_typing >> simp[] >>
  strip_tac >> gvs[EVERY_MEM]
QED

Theorem literal_body_eval_cases:
  expr_body_pre cenv cx env
    (Builtin ann (Bop bop) [e1; Builtin a (MakeArray t n) elems]) es /\
  (bop = In \/ bop = NotIn) /\
  bind (eval_expr cx (Builtin ann (Bop bop)
    [e1; Builtin a (MakeArray t n) elems])) (read_result cx) es = (res, es') ==>
  (?exc. bind (eval_expr cx e1) (read_result cx) es = (INR exc, es') /\
         res = INR exc) \/
  (?v es1 exc. bind (eval_expr cx e1) (read_result cx) es = (INL v, es1) /\
              eval_exprs cx elems es1 = (INR exc, es') /\ res = INR exc) \/
  (?v es1 vs. bind (eval_expr cx e1) (read_result cx) es = (INL v, es1) /\
             eval_exprs cx elems es1 = (INL vs, es') /\
             res = INL (BoolV (if bop = In then MEM v vs else ~MEM v vs)))
Proof
  strip_tac >> gvs[] >> drule literal_body_action >> simp[] >>
  disch_then (fn th => gvs[th]) >>
  gvs[vyperStateTheory.bind_def, vyperStateTheory.return_def, AllCaseEqs()] >>
  metis_tac[]
QED







(* Why it holds.  Typing (well_typed_binop In/NotIn, well_typed_builtin_app
   MakeArray) forces the right operand to be
   Builtin (ArrayT et bd) (MakeArray (SOME et) bd) elems with
   expr_type e1 = et, every element typed et and
   compatible_bound bd (LENGTH elems); MakeArray NONE has a TupleT type and
   is ruled out.  The source then evaluates e1, then the elements left to
   right, and returns BoolV (MEM v vs) (In) or its negation (NotIn): for a
   Fixed bound, make_array_value builds a sparse SArrayV
   (enumerate_static_array drops default values) and evaluate_in_array adds
   back `LENGTH al < n /\ v = default_value t`, which together give MEM v vs.
   The lowering evaluates the needle (lower_value) then the elements
   (compile_multi_exprs = the word-argument lowering, each at its own type)
   and folds EQ/OR (In) or EQ/ISZERO/AND (NotIn) over them.  Word values of
   one type have distinct val_to_w256 encodings, so the EQ chain decides MEM.

   This must not go through compile_expr_sim or body_sim_mutual: their
   admitted ancestry includes this theorem.  The elements' and needle's
   judgments come from the exprs_case hypothesis (any nocalls).

   Gas: the base's expr_sim is gas-counted (gas_outcome).  The template for
   composing word operands with a straight-line fragment under it is
   exprSimWordArgs' compile_word_builtin_sim (lower_word_args_sim,
   word_builtin_frag, word_builtin_frag_success); that theorem is stated for
   `Builtin ann bt args` with lower_word_args over args, which this
   expression's lowering is not (its operands are e1::elems). *)
Theorem compile_bop_in_literal_word_case:
  !nocalls ctx func cenv cx ann bop e1 a t n elems.
    is_word_type (expr_type e1) /\ (bop = In \/ bop = NotIn) /\
    exprs_case nocalls ctx func cenv cx (e1::elems) ==>
    expr_sim_case nocalls ctx func cenv cx
      (Builtin ann (Bop bop) [e1; Builtin a (MakeArray t n) elems]) /\
    expr_vv_case nocalls ctx func cenv cx
      (Builtin ann (Bop bop) [e1; Builtin a (MakeArray t n) elems])
Proof
  cheat
QED

Theorem compile_bop_in_literal_word_sim:
  !cenv ann bop e1 a t n elems.
    is_word_type (expr_type e1) ==>
    expr_sim_below cenv
      (list_size expr_size [e1; Builtin a (MakeArray t n) elems]) /\
    (bop = In \/ bop = NotIn) ==>
    expr_ok cenv (Builtin ann (Bop bop) [e1; Builtin a (MakeArray t n) elems])
Proof
  rpt strip_tac >> simp[expr_ok_case] >> rpt gen_tac >>
  irule compile_bop_in_literal_word_case >> simp[] >>
  irule exprs_case_below >> irule expr_sim_below_mono >>
  goal_assum (drule_at Any) >>
  simp[listTheory.list_size_def, vyperASTTheory.expr_size_def]
QED

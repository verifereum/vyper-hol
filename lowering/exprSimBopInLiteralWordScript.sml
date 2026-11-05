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

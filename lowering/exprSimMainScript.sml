(*
 * The expression simulation theorem (#636)
 *
 * compile_expr_sim: every expression's lowering simulates it (expr_sim,
 * exprSim) at every source state that meets expr_sim_pre (exprSimHyps).
 * It is proved by compile_expr_ind over compile_expr and its two
 * dispatchers, each case by a case lemma of exprSimLeaves,
 * exprSimOperators, exprSimPlaces, exprSimAggregates, exprSimBuiltins or
 * exprSimCalls.  Many of those are cheated; see each theory's header for
 * the #636 rows they stand for.
 *
 * TOP-LEVEL:
 *   compile_expr_sim         — expr_sim_ok of every expression
 *   compile_expr_sim_mutual  — the three conjuncts compile_expr_ind proves
 *   compile_expr_case_sim, compile_builtin_case_sim,
 *   compile_type_builtin_case_sim — one step of the induction each
 *   compile_builtin_case, compile_type_builtin_case — the builtins' steps
 *     over exprSimHyps' shared judgments, which the body simulation uses
 *     too
 *)

Theory exprSimMain
Ancestors
  exprSimTopLevel
  exprSimName
  exprSimHypsDefs
  list  exprSimHyps exprSimLeaves exprSimOperators exprSimPlaces
  exprSimAggregates exprSimBuiltins exprSimCalls exprLowering
  vyperAST vyperTypeCallGraph vyperTypeSystem exprSimWordBuiltins
  exprSimCalldataSlice exprSimPrecompiles exprSimLen

val expr_sizes = [listTheory.list_size_def, vyperASTTheory.expr_size_def,
                  basicSizeTheory.option_size_def];

(* ===== The induction steps ===== *)

(* The builtins but the binary operators, array literals, ecadd and ecmul,
   over exprSimHyps' shared judgments: compile_builtin_case_sim's step
   here, and the body simulation's (bodySimExprCases). *)
Theorem compile_builtin_case:
  !nocalls ctx func cenv cx ann bi args.
    (!bop. bi <> Bop bop) /\ (!t n. bi <> MakeArray t n) /\
    bi <> ECAdd /\ bi <> ECMul /\
    exprs_case nocalls ctx func cenv cx args ==>
    expr_sim_case nocalls ctx func cenv cx (Builtin ann bi args) /\
    expr_vv_case nocalls ctx func cenv cx (Builtin ann bi args)
Proof
  cheat
QED

Theorem compile_builtin_case_sim:
  !cenv ann bi args.
    expr_sim_below cenv (list_size expr_size args) ==>
    builtin_sim_ok cenv ann bi args
Proof
  cheat
QED

Theorem compile_type_builtin_case:
  !nocalls ctx func cenv cx ann tb t args.
    exprs_case nocalls ctx func cenv cx args /\
    (tb = Convert ==> ~nocalls ==>
     !e1 a f cargs d. args = [e1] /\ e1 = Call a (IntCall f) cargs d ==>
       lowered_value_type cenv e1 = expr_type e1) ==>
    expr_sim_case nocalls ctx func cenv cx (TypeBuiltin ann tb t args) /\
    expr_vv_case nocalls ctx func cenv cx (TypeBuiltin ann tb t args)
Proof
  cheat
QED

Theorem compile_type_builtin_case_sim:
  !cenv ann tb t args.
    expr_sim_below cenv (list_size expr_size args) ==>
    type_builtin_sim_ok cenv ann tb t args
Proof
  cheat
QED

Theorem compile_call_case_sim:
  !cenv ann target args dflt.
    expr_sim_below cenv (expr_size (Call ann target args dflt)) ==>
    expr_ok cenv (Call ann target args dflt)
Proof
  cheat
QED

Theorem compile_names_builtin_sim:
  !cenv ann bi args.
    names_builtin bi args ==> expr_ok cenv (Builtin ann bi args)
Proof
  cheat
QED

Theorem compile_expr_case_sim:
  !cenv e.
    expr_sim_below cenv (expr_size e) /\
    (!ann bi args. list_size expr_size args < expr_size e ==>
                   builtin_sim_ok cenv ann bi args) /\
    (!ann tb t args. list_size expr_size args < expr_size e ==>
                     type_builtin_sim_ok cenv ann tb t args) ==>
    expr_ok cenv e
Proof
  cheat
QED

(* ===== The theorem ===== *)

Theorem compile_expr_sim_mutual:
  (!cenv e. expr_ok cenv e) /\
  (!cenv ann bi args. builtin_sim_ok cenv ann bi args) /\
  (!cenv ann tb t args. type_builtin_sim_ok cenv ann tb t args)
Proof
  cheat
QED

Theorem compile_expr_sim:
  !ctx func cenv cx env ty e es.
    expr_sim_pre cenv cx env e es ==> expr_sim ctx func cenv cx ty e es
Proof
  cheat
QED

Theorem compile_expr_vv_sim:
  !ctx func cenv cx env ty e es.
    expr_sim_pre cenv cx env e es ==> expr_vv_sim ctx func cenv cx ty e es
Proof
  cheat
QED

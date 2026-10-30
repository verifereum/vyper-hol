(*
 * The body simulation of S1: its judgments (#636, #637, #638)
 *
 * S1's body simulation is one theorem proved by evaluate_ind
 * (bodySimMain): a predicate for each of evaluate's functions, so the
 * internal-call case can use the callee body's statement predicate.
 *   - Expressions (body_expr_ok): expr_sim and expr_vv_sim, under
 *     expr_sim_pre less its int_calls_expr e = [], in a frame of the
 *     lowered program (body_inv).
 *   - Statements and lists (body_stmt_ok, body_stmts_ok): stmt_frag,
 *     with the frame's RetQ, under the typing of the statement.
 *   - The rest, which evaluate runs inside a statement or an expression
 *     whose code compiles them in place (targets, iterators, a loop's
 *     iterations, the lists of operands): the judgments of the
 *     expressions and statements inside them, each as far as evaluation
 *     reaches it.  The case of the enclosing statement or expression
 *     simulates their code.
 *
 * TOP-LEVEL:
 *   body_inv            — the frame's cenv and ctx are the program's
 *   ce_locals_declared  — every local the compile env binds is one of the
 *                         type environment's
 *   stmt_exprs_ok       — the byte_widths and alloc_limits premises of
 *                         expr_sim_pre for each expression of a statement
 *   same_frame, frame_ret_ok — the frame's RetQ accepts its returns
 *   body_stmt_ok, body_stmts_ok, body_iterator_ok, body_for_ok,
 *   body_expr_ok, body_exprs_ok, body_base_target_ok,
 *   body_tuple_target_ok, body_tuple_targets_ok, body_results_ok
 *                       — the predicates of the induction
 *)

Theory bodySim
Ancestors
  list exprSim exprSimHyps stmtSim compileEnv compileVyper
  supportedProgram supportedStmts supportedStmtTraverse supportedExprTraverse
  vyperAST vyperInterpreter vyperState vyperValue vyperTypeSystem
  vyperTypeCallGraph vyperTypeCallStackSoundness

(* ===== The frame ===== *)

(* A frame of the lowered program: ctx is the context of tops's runtime
   unit, cenv is a runtime function's compile env with the program's
   function ids and parameter types (so compile_call gives an internal
   call the label package_internal_fn gave the callee:
   compile_call_intcall_label), the program's events, and its locals in
   allocas, as build_compile_env makes every body's, and the source finds
   its functions in tops. *)
Definition body_inv_def:
  body_inv tops ctx cenv cx <=>
    supported_program tops /\
    (?rpolicy unit. lower_vyper_runtime_unit tops rpolicy = SOME unit /\
                    ctx = unit.cu_context) /\
    get_module_code cx NONE = SOME tops /\
    cenv.ce_func_ids = build_func_ids 0 tops /\
    cenv.ce_func_param_types = build_func_param_types tops /\
    cenv.ce_event_info = build_event_info (type_env tops) tops (K NONE) /\
    ~cenv.ce_is_ctor /\ cenv.ce_alloca_locals
End

(* The compile env binds no local the typing does not know: every name
   ce_vars binds, but a module variable's key, is a local of the type
   environment.  build_compile_env binds the parameters and the module
   variables' keys, and each declaration binds its name as the typing
   adds it.  A name the typing declares (it is not in env.var_types) is
   then unbound unless it is a module variable's key. *)
Definition ce_locals_declared_def:
  ce_locals_declared cenv env <=>
    !n l. FLOOKUP cenv.ce_vars n = SOME l /\
          (!nsid. n <> module_var_key nsid) ==>
          n IN FDOM env.var_types
End

(* expr_sim_pre's byte_widths_expr and alloc_limits_expr for every
   expression of a statement, targets' keys included. *)
Definition stmt_exprs_ok_def:
  stmt_exprs_ok cenv s <=>
    ~supported_stmt_expr_exists
       (\e. ~(byte_widths_expr e /\ alloc_limits_expr cenv e)) s
End

(* The compile envs of one function's body: cenv' is cenv but for the
   fields a declaration changes, as in cenv_top_ext, and its variables
   differ only at names unbound or held through a pointer on both sides,
   so module variables (immutables above all) keep their bindings. *)
Definition same_frame_def:
  same_frame cenv cenv' <=>
    cenv' with <| ce_vars := cenv.ce_vars; ce_var_type := cenv.ce_var_type;
                  ce_dynarray_capacity := cenv.ce_dynarray_capacity |> =
      cenv /\
    !n. FLOOKUP cenv'.ce_vars n <> FLOOKUP cenv.ce_vars n ==>
        (!l. FLOOKUP cenv.ce_vars n = SOME l ==> ?p sz. l = PtrVar p sz) /\
        (!l. FLOOKUP cenv'.ce_vars n = SOME l ==> ?p sz. l = PtrVar p sz)
End

Theorem same_frame_refl[simp]:
  !cenv. same_frame cenv cenv
Proof
  simp[same_frame_def, compile_env_component_equality]
QED

Theorem cenv_top_ext_same_frame:
  !cenv cenv' scopes. cenv_top_ext cenv cenv' scopes ==> same_frame cenv cenv'
Proof
  rw[cenv_top_ext_def, same_frame_def] >> metis_tac[]
QED

(* The frame's returns: a return statement anywhere in the body, whose
   expression simulates, exits as RetQ accepts.  An internal frame
   discharges it with stmtSimReturn's compile_return_word_int_frag and
   compile_return_tuple_int_frag (RetQ intret_q), an external one with
   the return sequence's (#640).  Not covered yet: a return whose value
   widens to the return type (those lemmas take expr_type e = ty), and a
   memory return as a statement (intCallReturnMem's
   compile_internal_return_memory_frag is the fragment of its store and
   RET, for a value of the return type itself). *)
Definition frame_ret_ok_def:
  frame_ret_ok ctx func cx RetQ cenv ret_ty <=>
    !cenv' env lctx eo es res es'.
      same_frame cenv cenv' /\ expr_sim_inv cenv' cx env es /\
      IS_SOME (type_stmt env ret_ty (Return eo)) /\
      call_evaluation_safe cx (int_calls_stmt (Return eo)) /\
      (!e ty. eo = SOME e ==>
              expr_sim ctx func cenv' cx ty e es /\
              expr_vv_sim ctx func cenv' cx ty e es) /\
      eval_stmt cx (Return eo) es = (res, es') ==>
      stmt_frag ctx func cx lctx RetQ cenv'
        (stmt_env cenv' lctx ret_ty (Return eo)) es res es'
End

(* ===== The predicates of the induction ===== *)

(* An expression of a frame of the lowered program, internal calls
   allowed, simulates as a value and as compile_expr's value_vv. *)
Definition body_expr_ok_def:
  body_expr_ok cx e <=>
    !tops ctx func cenv env ty es.
      body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env e es ==>
      expr_sim ctx func cenv cx ty e es /\ expr_vv_sim ctx func cenv cx ty e es
End

(* A well-typed, supported statement of the frame, with its declaration,
   simulates with the frame's RetQ.  The compile type is the function's
   return type, as the typing has it.  supported_program gives
   supported_stmt for every function body's statements, with the
   body's bindings. *)
Definition body_stmt_ok_def:
  body_stmt_ok cx s <=>
    !tops bindings ctx func cenv env env' ret_ty lctx RetQ es res es'.
      body_inv tops ctx cenv cx /\ supported_stmt tops bindings s /\
      expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
      type_stmt env ret_ty s = SOME env' /\ stmt_exprs_ok cenv s /\
      call_evaluation_safe cx (int_calls_stmt s) /\
      frame_ret_ok ctx func cx RetQ cenv ret_ty /\
      eval_stmt cx s es = (res, es') ==>
      stmt_frag ctx func cx lctx RetQ cenv (stmt_env cenv lctx ret_ty s)
        es res es'
End

Definition body_stmts_ok_def:
  body_stmts_ok cx ss <=>
    !tops bindings ctx func cenv env env' ret_ty lctx RetQ es res es'.
      body_inv tops ctx cenv cx /\ supported_stmts tops bindings ss /\
      expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
      type_stmts env ret_ty ss = SOME env' /\
      EVERY (stmt_exprs_ok cenv) ss /\
      call_evaluation_safe cx (int_calls_stmts ss) /\
      frame_ret_ok ctx func cx RetQ cenv ret_ty /\
      eval_stmts cx ss es = (res, es') ==>
      stmt_frag ctx func cx lctx RetQ cenv (stmts_env cenv lctx ret_ty ss)
        es res es'
End

(* The operands of an expression, evaluated and read in order: each
   simulates if the ones before it can evaluate. *)
Definition body_exprs_ok_def:
  body_exprs_ok cx [] = T /\
  body_exprs_ok cx (e::es) =
    (body_expr_ok cx e /\
     ((?s tv t s1 v t1. eval_expr cx e s = (INL tv, t) /\
                        read_result cx tv s1 = (INL v, t1)) ==>
      body_exprs_ok cx es))
End

(* The same, evaluated without reading (eval_expr_results). *)
Definition body_results_ok_def:
  body_results_ok cx [] = T /\
  body_results_ok cx (e::es) =
    (body_expr_ok cx e /\
     ((?s res t. eval_expr cx e s = (INL res, t)) ==> body_results_ok cx es))
End

(* An iterator's expressions, the end of a range if its start can
   evaluate. *)
Definition body_iterator_ok_def:
  body_iterator_ok cx (Array e) = body_expr_ok cx e /\
  body_iterator_ok cx (Range e1 e2) =
    (body_expr_ok cx e1 /\
     ((?s tv t s1 v t1. eval_expr cx e1 s = (INL tv, t) /\
                        read_result cx tv s1 = (INL v, t1)) ==>
      body_expr_ok cx e2))
End

(* A loop over vs runs its body if vs is not empty. *)
Definition body_for_ok_def:
  body_for_ok cx (tyv : type_value) (nm : identifier) body (vs : value list)
  <=>
    vs <> [] ==> body_stmts_ok cx body
End

(* A target's keys, each if the place before it can evaluate.  It stands
   for both eval_base_place and eval_target_place. *)
Definition body_base_target_ok_def:
  body_base_target_ok cx (NameTarget id) = T /\
  body_base_target_ok cx (TopLevelNameTarget nid) = T /\
  body_base_target_ok cx (AttributeTarget t id) = body_base_target_ok cx t /\
  body_base_target_ok cx (SubscriptTarget t e) =
    (body_base_target_ok cx t /\
     ((?s pv s1. eval_base_place cx t s = (INL pv, s1)) ==>
      body_expr_ok cx e))
End

(* The targets of a tuple assignment, each if the ones before it can be
   assigned. *)
Definition body_tuple_target_ok_def:
  body_tuple_target_ok cx (BaseTarget t) (v : value) =
    body_base_target_ok cx t /\
  body_tuple_target_ok cx (TupleTarget gs) v =
    (!vs. v = ArrayV (TupleV vs) ==> body_tuple_targets_ok cx gs vs) /\
  body_tuple_targets_ok cx [] vs = T /\
  body_tuple_targets_ok cx (g::gs) [] = T /\
  body_tuple_targets_ok cx (g::gs) (v::vs) =
    (body_tuple_target_ok cx g v /\
     ((?s x t. assign_tuple_targets cx g v s = (INL x, t)) ==>
      body_tuple_targets_ok cx gs vs))
Termination
  WF_REL_TAC `measure (\x. case x of
    INL (_,t,_) => assignment_target_size t
  | INR (_,ts,_) => list_size assignment_target_size ts)` >>
  simp[assignment_target_size_def, list_size_def]
End

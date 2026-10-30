(*
 * The body simulation of S1: expression cases (#636, #638)
 *
 * One lemma for each expression case of evaluate_ind that bodySimMain's
 * body_sim_mutual does not close in a line or two.  An expression with
 * no internal call simulates by compile_expr_sim (body_expr_ok_intro);
 * each case's GAP is the expression with one, and the internal call
 * itself is the call step (#638, body_intcall_case).
 *
 * A case proved here instantiates the shared case lemma of exprSim*
 * (exprSimHyps' expr_sim_case and expr_vv_case) that compile_expr_sim
 * uses too, at nocalls = F, from the operands' body_expr_ok
 * (body_expr_ok_case).
 *
 * TOP-LEVEL:
 *   body_expr_ok_intro — an expression with no internal call simulates by
 *                        compile_expr_sim
 *   body_expr_ok_case, body_expr_ok_of_case — body_expr_ok is the shared
 *                        judgments at nocalls = F in every frame
 *   body_*_case        — one case of the induction each
 *)

Theory bodySimExprCases
Ancestors
  list bodySim exprSim exprSimHyps exprSimOperators exprSimMain vyperAST
  vyperInterpreter vyperState vyperContext vyperTypeCallGraph

(* With no internal call in it, an expression simulates by
   compile_expr_sim; what is left is the case with one. *)
Theorem body_expr_ok_intro:
  !cx e.
    (!tops ctx func cenv env ty es.
       body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env e es /\
       int_calls_expr e <> [] ==>
       expr_sim ctx func cenv cx ty e es /\
       expr_vv_sim ctx func cenv cx ty e es) ==>
    body_expr_ok cx e
Proof
  rw[body_expr_ok_def] >> Cases_on `int_calls_expr e = []` >> gvs[] >>
  metis_tac[compile_expr_sim, compile_expr_vv_sim, expr_sim_pre_body]
QED

Theorem body_expr_ok_case:
  !cx e tops ctx func cenv.
    body_expr_ok cx e /\ body_inv tops ctx cenv cx ==>
    expr_sim_case F ctx func cenv cx e /\ expr_vv_case F ctx func cenv cx e
Proof
  rw[body_expr_ok_def, expr_sim_case_def, expr_vv_case_def] >> metis_tac[]
QED

Theorem body_expr_ok_of_case:
  !cx e.
    (!tops ctx func cenv.
       body_inv tops ctx cenv cx ==>
       expr_sim_case F ctx func cenv cx e /\
       expr_vv_case F ctx func cenv cx e) ==>
    body_expr_ok cx e
Proof
  rw[body_expr_ok_def, expr_sim_case_def, expr_vv_case_def] >> metis_tac[]
QED

(* exprSimOperators' compile_ifexp_case, whose aggregate ternaries are
   cheated there (compile_ifexp_aggregate_case) for compile_expr_sim too. *)
Theorem body_ifexp_case:
  !cx v5 e1 e2 e3.
    (!s'' tv t. eval_expr cx e1 s'' = (INL tv,t) ==> body_expr_ok cx e2) /\
    (!s'' tv t. eval_expr cx e1 s'' = (INL tv,t) ==> body_expr_ok cx e3) /\
    body_expr_ok cx e1 ==>
    body_expr_ok cx (IfExp v5 e1 e2 e3)
Proof
  rpt strip_tac >> irule body_expr_ok_of_case >> rpt gen_tac >> strip_tac >>
  irule compile_ifexp_case >> rpt conj_tac
  >- (strip_tac >> metis_tac[body_expr_ok_case]) >>
  metis_tac[body_expr_ok_case]
QED

(* GAP (#636 operands with internal calls): struct literals, as body_builtin_rest_case. *)
Theorem body_structlit_case:
  !cx v7 src_id_opt id kes.
    (!ks. ks = MAP FST kes ==> body_exprs_ok cx (MAP SND kes)) ==>
    body_expr_ok cx (StructLit v7 (src_id_opt,id) kes)
Proof
  rpt strip_tac >> irule body_expr_ok_intro >> cheat
QED

(* GAP (#636 operands with internal calls): subscripts, as body_builtin_rest_case. *)
Theorem body_subscript_case:
  !cx v8 e1 e2.
    (!s'' res t. eval_expr cx e1 s'' = (INL res,t) ==> body_expr_ok cx e2) /\
    body_expr_ok cx e1 ==>
    body_expr_ok cx (Subscript v8 e1 e2)
Proof
  rpt strip_tac >> irule body_expr_ok_intro >> cheat
QED

(* GAP (#636 operands with internal calls): attributes, as body_builtin_rest_case. *)
Theorem body_attribute_case:
  !cx v9 e id. body_expr_ok cx e ==> body_expr_ok cx (Attribute v9 e id)
Proof
  rpt strip_tac >> irule body_expr_ok_intro >> cheat
QED

(* A binary operator: exprSimOperators' compile_bop_case, whose
   == and != on bytestrings and in and not in on arrays are cheated there
   (compile_bop_rest_case) for compile_expr_sim too.  It leaves out in and
   not in on an array literal (body_bop_in_literal_case). *)
Theorem body_bop_case:
  !cx ty bop e1 e2.
    ((bop = In \/ bop = NotIn) ==>
     !a t n elems. e2 <> Builtin a (MakeArray t n) elems) /\
    body_exprs_ok cx [e1; e2] ==> body_expr_ok cx (Builtin ty (Bop bop) [e1; e2])
Proof
  rw[body_exprs_ok_def] >> irule body_expr_ok_of_case >> rpt gen_tac >>
  strip_tac >> irule compile_bop_case >> rpt conj_tac
  >- (strip_tac >> metis_tac[body_expr_ok_case]) >>
  metis_tac[body_expr_ok_case]
QED

(* GAP (#636 operands with internal calls): the builtins other than the
   binary operators: with no internal call,
   compile_expr_sim (body_expr_ok_intro).  With one, the builtins' case
   lemmas (exprSimBuiltins and the theories under it) do not apply: they
   conclude under expr_sim_pre, with int_calls_expr e = [], and take
   expr_sim_below, every smaller expression's simulation.  Restated over
   exprSimHyps' expr_sim_case as compile_bop_case is, they close this as
   body_bop_case.  The other cases marked GAP (#636) stand as this one
   does, but some case lemmas take more than the judgments of the operands
   the induction hypotheses give (a subscript's place chain, a pop's
   target, the calls), so restating alone will not close those. *)
Theorem body_builtin_rest_case:
  !cx ty bt es.
    (!bop. bt <> Bop bop) /\
    (!s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt <> Len ==>
       body_exprs_ok cx es) /\
    (!s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt = Len ==>
       body_expr_ok cx (HD es)) ==>
    body_expr_ok cx (Builtin ty bt es)
Proof
  rpt strip_tac >> irule body_expr_ok_intro >> cheat
QED

(* GAP (#636 operands with internal calls): in and not in on an array
   literal.  Its lowering compiles each element (exprSimOperators'
   compile_bop_in_literal_sim), while the induction hypotheses give the
   judgment of the array only.  As body_builtin_rest_case otherwise. *)
Theorem body_bop_in_literal_case:
  !cx ty bop e1 a t n elems.
    (bop = In \/ bop = NotIn) /\
    body_exprs_ok cx [e1; Builtin a (MakeArray t n) elems] ==>
    body_expr_ok cx
      (Builtin ty (Bop bop) [e1; Builtin a (MakeArray t n) elems])
Proof
  rpt strip_tac >> irule body_expr_ok_intro >> cheat
QED

Theorem body_builtin_case:
  !cx ty bt es.
    (!s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt <> Len ==>
       body_exprs_ok cx es) /\
    (!s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt = Len ==>
       body_expr_ok cx (HD es)) ==>
    body_expr_ok cx (Builtin ty bt es)
Proof
  rpt strip_tac >> reverse (Cases_on `?bop. bt = Bop bop`)
  >- (irule body_builtin_rest_case >> gvs[] >> metis_tac[]) >>
  gvs[] >> Cases_on `?e1 e2. es = [e1; e2]`
  >- (gvs[] >>
      `body_exprs_ok cx [e1; e2]` by
        (first_x_assum irule >>
         simp[type_check_def, assert_def, builtin_args_length_ok_def]) >>
      Cases_on `(bop = In \/ bop = NotIn) /\
                ?a t n elems. e2 = Builtin a (MakeArray t n) elems`
      >- (gvs[] >> irule body_bop_in_literal_case >> simp[]) >>
      irule body_bop_case >> gvs[]) >>
  irule body_expr_ok_of_case >> rpt gen_tac >> strip_tac >>
  irule compile_bop_args_case >> gvs[]
QED

(* GAP (#636 operands with internal calls): pop, as body_builtin_rest_case. *)
Theorem body_pop_case:
  !cx v10 bt. body_base_target_ok cx bt ==> body_expr_ok cx (Pop v10 bt)
Proof
  rpt strip_tac >> irule body_expr_ok_intro >> cheat
QED

(* GAP (#636 operands with internal calls): type builtins, as body_builtin_rest_case. *)
Theorem body_type_builtin_case:
  !cx v11 tb typ es.
    (!s'' x t.
       type_check (type_builtin_args_length_ok tb (LENGTH es))
         "TypeBuiltin args" s'' = (INL x,t) ==>
       body_exprs_ok cx es) ==>
    body_expr_ok cx (TypeBuiltin v11 tb typ es)
Proof
  rpt strip_tac >> irule body_expr_ok_intro >> cheat
QED

(* GAP (#636 operands with internal calls): send, as body_builtin_rest_case. *)
Theorem body_send_case:
  !cx v12 has_gas es v13.
    (!s'' x t.
       type_check (LENGTH es = if has_gas then 3 else 2) "Send args" s'' =
       (INL x,t) ==>
       body_exprs_ok cx es) ==>
    body_expr_ok cx (Call v12 (Send has_gas) es v13)
Proof
  rpt strip_tac >> irule body_expr_ok_intro >> cheat
QED

(* GAP (#636 operands with internal calls): external calls, as body_builtin_rest_case. *)
Theorem body_extcall_case:
  !cx v14 is_static skip_check sig opts es v15.
    (!s'' target t nargs s'3' results t'.
       eval_exprs cx (TAKE 1 es) s'' = (INL target,t) /\
       nargs = LENGTH (FST (SND sig)) /\
       eval_expr_results cx (TAKE nargs (DROP 1 es)) s'3' = (INL results,t') ==>
       body_exprs_ok cx (DROP (1 + nargs) es)) /\
    (!s'' target t nargs.
       eval_exprs cx (TAKE 1 es) s'' = (INL target,t) /\
       nargs = LENGTH (FST (SND sig)) ==>
       body_results_ok cx (TAKE nargs (DROP 1 es))) /\
    body_exprs_ok cx (TAKE 1 es) ==>
    body_expr_ok cx (Call v14 (ExtCall is_static skip_check sig opts) es v15)
Proof
  rpt strip_tac >> irule body_expr_ok_intro >> cheat
QED

(* GAP (#638 the call step): the INVOKE of an internal call.  The IHs
   give the arguments' judgments (body_results_ok), the defaults' at the
   callee's stack (body_exprs_ok), and the callee body's (body_stmts_ok
   at cxf, the callee's context after push_function).  The step:
   - compile_call: intCallStep's compile_call_intcall_shape, the INVOKE
     label by intCallLookup's compile_call_intcall_label (body_inv gives
     its premises), and the callee's code in ctx by
     lower_vyper_runtime_unit_internal_lookup;
   - the arguments: the IH, then intCallArgs' stage_mem_arg_frag for
     the staged memory arguments;
   - the callee's entry: intCallCallee's compile_internal_prologue_entry
     gives stmt_state_rel at the callee's start, at
     vs with scopes := [env];
   - the callee's body: the IH at the callee's compile env, with RetQ
     intret_q (stack returns) or intret_mem_q (memory returns), whose
     frame_ret_ok stmtSimReturn's compile_return_word_int_frag and
     compile_return_tuple_int_frag and intCallReturnMem's
     compile_internal_return_memory_frag give;
   - the return: intCallStep's frag_exec_invoke_intret, intCallReturn's
     eval_expr_intcall_return (source) and invoke_intret_state_rel
     (Venom), with intCallFrame's callee_writes_above for the caller's
     live regions, and intCallResult's store_multi_results_frag for
     stack results.
   Left (the push transfer): the callee body's premises at its entry:
   body_inv and expr_sim_inv for the callee's compile env and env at
   cxf, and frame_ret_ok for the internal return; and that the callee
   body's code in ctx is stmts_env's in that compile env.
   ce_locals_declared there is bodySimEntry's internal_entry_declared and
   ce_locals_declared_params, for an env that has the parameters. *)
Theorem body_intcall_case:
  !cx v16 src_id_opt fn es v17.
    (!s'' x t s'3' ts t' s'4' tup t'' mut stup nr stup2 args sstup dflts sstup2
         ret body' s'5' x' t'3' s'6' results t'4' needed_dflts cxd s'7' prev
         t'5' s'8' dflt_vs t'6' s'9' vs t'7' all_tenv s'10' env t'8' s'11' rtv
         t'9' is_view s'12' x'' t'10' s'13' cxf t'11'.
       type_check (~MEM (src_id_opt,fn) cx.stk) "recursion" s'' = (INL x,t) /\
       lift_option_type (get_module_code cx src_id_opt)
         "IntCall get_module_code" s'3' = (INL ts,t') /\
       lift_option_type (lookup_callable_function cx.in_deploy fn ts)
         "IntCall lookup_function" s'4' = (INL tup,t'') /\ mut = FST tup /\
       stup = SND tup /\ (nr <=> FST stup) /\ stup2 = SND stup /\
       args = FST stup2 /\ sstup = SND stup2 /\ dflts = FST sstup /\
       sstup2 = SND sstup /\ ret = FST sstup2 /\ body' = SND sstup2 /\
       type_check
         (LENGTH es <= LENGTH args /\ LENGTH args - LENGTH es <= LENGTH dflts)
         "IntCall args length" s'5' = (INL x',t'3') /\
       eval_expr_results cx es s'6' = (INL results,t'4') /\
       needed_dflts = DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts /\
       cxd = cx with stk updated_by CONS (src_id_opt,fn) /\
       get_scopes s'7' = (INL prev,t'5') /\
       finally
         (ignore_bind (set_scopes [FEMPTY]) (eval_exprs cxd needed_dflts))
         (set_scopes prev) s'8' = (INL dflt_vs,t'6') /\
       read_results cx results s'9' = (INL vs,t'7') /\
       all_tenv = get_tenv cx /\
       lift_option_type (bind_arguments all_tenv args (vs ++ dflt_vs))
         "IntCall bind_arguments" s'10' = (INL env,t'8') /\
       lift_option_type (evaluate_type all_tenv ret) "IntCall eval ret" s'11' =
       (INL rtv,t'9') /\ (is_view <=> is_view_mut mut) /\
       lock_if_nr cx nr is_view s'12' = (INL x'',t'10') /\
       push_function (src_id_opt,fn) env cx s'13' = (INL cxf,t'11') ==>
       body_stmts_ok cxf body') /\
    (!s'' x t s'3' ts t' s'4' tup t'' mut stup nr stup2 args sstup dflts sstup2
         ret body' s'5' x' t'3' s'6' results t'4' needed_dflts cxd s'7' prev
         t'5' s'8' x'' t'6'.
       type_check (~MEM (src_id_opt,fn) cx.stk) "recursion" s'' = (INL x,t) /\
       lift_option_type (get_module_code cx src_id_opt)
         "IntCall get_module_code" s'3' = (INL ts,t') /\
       lift_option_type (lookup_callable_function cx.in_deploy fn ts)
         "IntCall lookup_function" s'4' = (INL tup,t'') /\ mut = FST tup /\
       stup = SND tup /\ (nr <=> FST stup) /\ stup2 = SND stup /\
       args = FST stup2 /\ sstup = SND stup2 /\ dflts = FST sstup /\
       sstup2 = SND sstup /\ ret = FST sstup2 /\ body' = SND sstup2 /\
       type_check
         (LENGTH es <= LENGTH args /\ LENGTH args - LENGTH es <= LENGTH dflts)
         "IntCall args length" s'5' = (INL x',t'3') /\
       eval_expr_results cx es s'6' = (INL results,t'4') /\
       needed_dflts = DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts /\
       cxd = cx with stk updated_by CONS (src_id_opt,fn) /\
       get_scopes s'7' = (INL prev,t'5') /\
       set_scopes [FEMPTY] s'8' = (INL x'',t'6') ==>
       body_exprs_ok cxd needed_dflts) /\
    (!s'' x t s'3' ts t' s'4' tup t'' mut stup nr stup2 args sstup dflts sstup2
         ret body' s'5' x' t'3'.
       type_check (~MEM (src_id_opt,fn) cx.stk) "recursion" s'' = (INL x,t) /\
       lift_option_type (get_module_code cx src_id_opt)
         "IntCall get_module_code" s'3' = (INL ts,t') /\
       lift_option_type (lookup_callable_function cx.in_deploy fn ts)
         "IntCall lookup_function" s'4' = (INL tup,t'') /\ mut = FST tup /\
       stup = SND tup /\ (nr <=> FST stup) /\ stup2 = SND stup /\
       args = FST stup2 /\ sstup = SND stup2 /\ dflts = FST sstup /\
       sstup2 = SND sstup /\ ret = FST sstup2 /\ body' = SND sstup2 /\
       type_check
         (LENGTH es <= LENGTH args /\ LENGTH args - LENGTH es <= LENGTH dflts)
         "IntCall args length" s'5' = (INL x',t'3') ==>
       body_results_ok cx es) ==>
    body_expr_ok cx (Call v16 (IntCall (src_id_opt,fn)) es v17)
Proof
  rpt strip_tac >> irule body_expr_ok_intro >> cheat
QED

(* GAP (#636 operands with internal calls): raw_call, as body_builtin_rest_case. *)
Theorem body_raw_call_case:
  !cx ty flags es v18.
    body_exprs_ok cx es ==>
    body_expr_ok cx (Call ty (RawCallTarget flags) es v18)
Proof
  rpt strip_tac >> irule body_expr_ok_intro >> cheat
QED

(* GAP (#636 operands with internal calls): raw_call with calldata, as body_builtin_rest_case. *)
Theorem body_raw_call_calldata_case:
  !cx ty flags es v19.
    body_exprs_ok cx es ==>
    body_expr_ok cx (Call ty (RawCallCalldataTarget flags) es v19)
Proof
  rpt strip_tac >> irule body_expr_ok_intro >> cheat
QED

(* GAP (#636 operands with internal calls): raw_log, as body_builtin_rest_case. *)
Theorem body_raw_log_case:
  !cx v20 es v21.
    body_exprs_ok cx es ==> body_expr_ok cx (Call v20 RawLog es v21)
Proof
  rpt strip_tac >> irule body_expr_ok_intro >> cheat
QED

(* GAP (#636 operands with internal calls): raw_revert, as body_builtin_rest_case. *)
Theorem body_raw_revert_case:
  !cx v22 es v23.
    body_exprs_ok cx es ==> body_expr_ok cx (Call v22 RawRevert es v23)
Proof
  rpt strip_tac >> irule body_expr_ok_intro >> cheat
QED

(* GAP (#636 operands with internal calls): selfdestruct, as body_builtin_rest_case. *)
Theorem body_selfdestruct_case:
  !cx v24 es v25.
    body_exprs_ok cx es ==>
    body_expr_ok cx (Call v24 SelfDestructTarget es v25)
Proof
  rpt strip_tac >> irule body_expr_ok_intro >> cheat
QED

(* GAP (#636 operands with internal calls): create, as body_builtin_rest_case. *)
Theorem body_create_case:
  !cx ty kind has_salt rof es v26.
    (!raw_args s'' prefix t s'3' code_size t'.
       kind = CreateFromBlueprint raw_args /\
       eval_exprs cx (TAKE (if has_salt then 4 else 3) es) s'' = (INL prefix,t) /\
       check_create_blueprint has_salt prefix s'3' = (INL code_size,t') ==>
       body_results_ok cx (DROP (if has_salt then 4 else 3) es)) /\
    (!raw_args.
       kind = CreateFromBlueprint raw_args ==>
       body_exprs_ok cx (TAKE (if has_salt then 4 else 3) es)) /\
    (!s'' prefix t ctor_es nargs s'3' results t' s'4' args t''.
       kind = RawCreate /\ eval_exprs cx (TAKE 2 es) s'' = (INL prefix,t) /\
       ctor_es = DROP 2 es /\
       nargs = LENGTH ctor_es - (if has_salt then 1 else 0) /\
       eval_expr_results cx (TAKE nargs ctor_es) s'3' = (INL results,t') /\
       read_results cx results s'4' = (INL args,t'') ==>
       body_exprs_ok cx (DROP nargs ctor_es)) /\
    (!s'' prefix t ctor_es nargs.
       kind = RawCreate /\ eval_exprs cx (TAKE 2 es) s'' = (INL prefix,t) /\
       ctor_es = DROP 2 es /\
       nargs = LENGTH ctor_es - (if has_salt then 1 else 0) ==>
       body_results_ok cx (TAKE nargs ctor_es)) /\
    (kind = CreateCopyOf ==> body_exprs_ok cx es) /\
    (kind = CreateMinimalProxy ==> body_exprs_ok cx es) /\
    (kind = RawCreate ==> body_exprs_ok cx (TAKE 2 es)) ==>
    body_expr_ok cx (Call ty (CreateTarget kind has_salt rof) es v26)
Proof
  rpt strip_tac >> irule body_expr_ok_intro >> cheat
QED

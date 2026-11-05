(* Readiness-parametric composition of argument evaluation and Log emission. *)
Theory stmtSimLogCompose
Ancestors
  exprSimDefs exprSimProps exprSimStack loweringPosts stmtSimDefs stmtSimProps
  stmtSimLogArgsRun stmtSimLogArgsGrowth stmtSimLogSuffix stmtSimLogSource   exprSimWordArgs
  stmtSimLogSuffixActual stmtSimLogSuffixFrame stmtSimLogSuffixCode stmtSimLogArgs freshWrites
  compileEnv stmtLowering fragExec loweringSlice exprLoweringProps emitHelperProps
  vyperInterpreter vyperState vyperTyping list stmtSimLogTrace emitHelper context venomInst
Libs
  monadsyntax

Theorem log_ready_values_typed:
  !args es vs es'.
  (!e tail s. R (e::tail) s ==>
     !v s1. (do r <- eval_expr cx e; read_result cx r od) s = (INL v,s1) ==>
       R tail s1 /\ ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                        value_has_type tv v) /\
  R args es /\ eval_exprs cx args es = (INL vs,es') ==>
  LIST_REL (\ty v. ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
                        value_has_type tv v) (MAP expr_type args) vs
Proof
  cheat
QED

Theorem log_ready_eval_outcome[local]:
  (!e tail s. R (e::tail) s ==>
     !v s1. (do r <- eval_expr cx e; read_result cx r od) s = (INL v,s1) ==>
       R tail s1 /\ ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                        value_has_type tv v) /\
  R args es /\ eval_stmt cx (Log id args) es = (res,es') /\ ~cx.txn.is_static /\
  lookup_event_metadata (get_tenv cx) cx.sources cx.txn.target id = SOME (h,tys,flags) /\
  MAP expr_type args = tys /\ LENGTH flags = LENGTH tys /\
  EVERY supported_scalar_type tys ==>
  (?err. eval_exprs cx args es = (INR err,es') /\ res = INR err) \/
  (?vs mid topics avs. eval_exprs cx args es = (INL vs,mid) /\
    encode_indexed_event_topics flags tys vs = SOME topics /\
    vyper_to_abi_list (get_tenv cx) (log_non_indexed_types flags tys)
      (log_non_indexed_values flags vs) = SOME avs /\ res = INL () /\
    es' = mid with logs := mid.logs ++
      [<|logger := cx.txn.target; topics := n2w h::topics;
         data := enc (Tuple (vyper_to_abi_types (get_tenv cx)
           (log_non_indexed_types flags tys))) (ListV avs)|>])
Proof
  cheat
QED

Theorem log_emit_open[local]:
  emit_inst LOG ops [] sa = ((),sb) ==> ~block_is_terminated sb
Proof
  cheat
QED

Theorem log_compile_structure[local]:
  cenv.ce_event_info (nsid_to_string id) = SOME (h,MAP expr_type args,flags) /\
  LENGTH flags = LENGTH args /\ EVERY supported_scalar_type (MAP expr_type args) /\
  compile_stmt cenv lctx ty (Log id args) sa = ((),sb) /\
  fn_has_code sa sb func ==>
  ?xs sm ops st. compile_log_eval_all cenv args sa = (xs,sm) /\
    compile_log_topic_ops (FST (split_log_ops xs flags)) sm = (ops,st) /\
    MAP SND xs = MAP expr_type args /\ LENGTH flags = LENGTH xs /\
    inst_extends sm sb /\ same_blocks sm sb /\ sm.cs_next_var <= sb.cs_next_var /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sm sb) /\ cs_extends sa sm /\ cs_extends sm sb /\
    fn_has_code sa sm func /\ fn_has_code sm sb func
Proof
  cheat
QED


Theorem compile_log_ready_stmt_frag:
  (!e tail s. R (e::tail) s ==>
    expr_sim ctx func cenv cx (expr_type e) e s /\
    !v s1. (do r <- eval_expr cx e; read_result cx r od) s = (INL v,s1) ==>
      R tail s1 /\ ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                        value_has_type tv v) /\
  R args es /\
  expr_sim_inv cenv cx env es /\ well_typed_exprs env args /\
  (!id t. FLOOKUP env.var_types id = SOME t ==>
     ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)) /\
  cenv.ce_event_info (nsid_to_string id) = SOME (h,tys,flags) /\
  lookup_event_metadata (get_tenv cx) cx.sources cx.txn.target id = SOME (h,tys,flags) /\
  MAP expr_type args = tys /\ LENGTH flags = LENGTH tys /\
  LENGTH (FILTER I flags) <= 3 /\ EVERY supported_scalar_type tys /\
  SUM (MAP (type_memory_bytes cenv) (log_non_indexed_types flags tys)) < dimword (:256) /\
  abi_size_bound cenv.ce_struct_fields (TupleT (log_non_indexed_types flags tys)) < dimword (:256) ==>
  stmt_frag ctx func cx lctx RetQ cenv
    (stmt_env cenv lctx ty (Log id args))
      (eval_stmt cx (Log id args)) es
Proof
  cheat
QED







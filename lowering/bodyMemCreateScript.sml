(* Memory case of the body induction (bodyMemory's body_mem_mutual): create
   (all kinds). *)
Theory bodyMemCreate
Ancestors
  bodyMemoryPreds

Theorem body_create_mem_case:
  !cx ty kind has_salt rof kw_order es v26.
    (!raw_args s'' prefix t s'3' code_size t'.
       kind = CreateFromBlueprint raw_args /\
       eval_exprs cx (TAKE (if has_salt then 4 else 3) es) s'' = (INL prefix,t) /\
       check_create_blueprint has_salt prefix s'3' = (INL code_size,t') ==>
       body_results_mem_ok cx (DROP (if has_salt then 4 else 3) es)) /\
    (!raw_args.
       kind = CreateFromBlueprint raw_args ==>
       body_exprs_mem_ok cx (TAKE (if has_salt then 4 else 3) es)) /\
    (!s'' prefix t ctor_es nargs s'3' results t' s'4' args t''.
       kind = RawCreate /\ eval_exprs cx (TAKE 2 es) s'' = (INL prefix,t) /\
       ctor_es = DROP 2 es /\
       nargs = LENGTH ctor_es - (if has_salt then 1 else 0) /\
       eval_expr_results cx (TAKE nargs ctor_es) s'3' = (INL results,t') /\
       read_results cx results s'4' = (INL args,t'') ==>
       body_exprs_mem_ok cx (DROP nargs ctor_es)) /\
    (!s'' prefix t ctor_es nargs.
       kind = RawCreate /\ eval_exprs cx (TAKE 2 es) s'' = (INL prefix,t) /\
       ctor_es = DROP 2 es /\
       nargs = LENGTH ctor_es - (if has_salt then 1 else 0) ==>
       body_results_mem_ok cx (TAKE nargs ctor_es)) /\
    (kind = CreateCopyOf ==> body_exprs_mem_ok cx es) /\
    (kind = CreateMinimalProxy ==> body_exprs_mem_ok cx es) /\
    (kind = RawCreate ==> body_exprs_mem_ok cx (TAKE 2 es)) ==>
    body_expr_mem_ok cx (Call ty (CreateTarget kind has_salt rof kw_order) es v26)
Proof
  rw[body_expr_mem_ok_def, exprSimHypsDefsTheory.expr_body_pre_def,
     supportedExprTraverseTheory.expr_has_evm_run_thm,
     supportedExprTraverseTheory.expr_evm_run_root_def]
QED

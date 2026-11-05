(* For over a range whose ends are not both literals, memory-safe: the S3
   twin of stmtSimForRange's compile_for_range_checked_frag_active, with
   expr_sim_mem for expr_sim and stmt_frag_mem for stmt_frag.  Admitted:
   held on S1's counted range loop (compile_for_range_checked_frag_active
   and stmtSimForLoop's for_loop), whose proof this one follows with
   fragLoopMemory's frag_exec_loop_mem as the loop step. *)
Theory stmtForRangeMemory
Ancestors
  stmtSimDefs exprSimMemDefs stmtLowering compileEnv vyperInterpreter
  vyperState vyperTypeSystem

Theorem compile_for_range_checked_frag_active_mem:
  !P Q d (ctx, func, cx, lctx, RetQ, cenv, env, ty)
   id fty e1 e2 bound stmts es tyv.
    is_int_type fty /\
    evaluate_type (get_tenv cx) fty = SOME tyv /\
    32 <= type_memory_bytes cenv fty /\
    type_memory_bytes cenv fty < dimword (:256) /\ bound < dimword (:256) /\
    cenv.ce_alloca_locals /\ lookup_scopes id es.scopes = NONE /\
    (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
    (!c lc sa sb. compile_stmts c lc ty stmts sa = ((), sb) ==>
                  cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
    is_word_type (expr_type e1) /\
    evaluate_type (get_tenv cx) (expr_type e1) = SOME tyv /\
    is_word_type (expr_type e2) /\
    evaluate_type (get_tenv cx) (expr_type e2) = SOME tyv /\
    expr_sim_mem ctx func cenv cx fty e1 es /\
    (!gs tv es1.
       (do raw <- eval_expr cx e1; read_result cx raw od)
         (es with gas_obs := gs) = (INL tv, es1) ==>
       ?n1. tv = IntV n1 /\ value_has_type tyv (IntV n1) /\
            expr_sim_mem ctx func cenv cx fty e2 es1 /\
            !gs2 tv2 es2.
              (do raw <- eval_expr cx e2; read_result cx raw od)
                (es1 with gas_obs := gs2) = (INL tv2, es2) ==>
              ?n2. tv2 = IntV n2 /\ value_has_type tyv (IntV n2) /\
                   P es2) /\
    (!gs n1 es1 n2 es2.
       (do raw <- eval_expr cx e1; read_result cx raw od)
         (es with gas_obs := gs) = (INL (IntV n1), es1) /\
       (do raw <- eval_expr cx e2; read_result cx raw od) es1 =
         (INL (IntV n2), es2) /\
       n1 <= n2 /\ Num (n2 - n1) <= bound /\ 0 < Num (n2 - n1) ==> Q) /\
    well_typed_expr env e1 /\ well_typed_expr env e2 /\
    (!x t. FLOOKUP env.var_types x = SOME t ==>
           well_formed_type env.type_defs t) /\
    ~(?a1 n1 a2 n2. e1 = Literal a1 (IntL n1) /\ e2 = Literal a2 (IntL n2)) /\
    (!st0 c st1 ex inc ei n1 j.
       declare_local cenv id fty st0 = (c, st1) /\
       Q /\ P ei /\ lookup_scopes id ei.scopes = NONE /\
       value_has_type tyv (IntV (n1 + &j)) ==>
       stmt_frag_mem d ctx func cx (InLoop ex inc) RetQ c
         (stmts_env c (InLoop ex inc) ty stmts) (eval_stmts cx stmts)
         (ei with scopes :=
            (FEMPTY |+ (id, <| assignable := F; type := tyv;
                               value := IntV (n1 + &j); popped := [] |>)) :: ei.scopes)) /\
    (!ei n1 j gs r2 es2 sc rest.
       Q /\ P ei /\ lookup_scopes id ei.scopes = NONE /\
       value_has_type tyv (IntV (n1 + &j)) /\
       eval_stmts cx stmts
         (ei with <| scopes :=
            (FEMPTY |+ (id, <| assignable := F; type := tyv;
                               value := IntV (n1 + &j); popped := [] |>)) :: ei.scopes;
                     gas_obs := gs |>) =
         (r2, es2) /\
       (r2 = INL () \/ r2 = INR ContinueException) /\
       es2.scopes = sc :: rest ==>
       P (es2 with scopes := rest)) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (For id fty (Range e1 e2) bound stmts))
      (eval_stmt cx (For id fty (Range e1 e2) bound stmts)) es
Proof
  cheat
QED

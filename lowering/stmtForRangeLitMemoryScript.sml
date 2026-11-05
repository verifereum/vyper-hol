(* For over a range of two integer literals, memory-safe: the S3 twin of
   stmtSimFor's compile_for_range_lit_frag, with stmt_frag_mem for
   stmt_frag.  Admitted: held on S1's counted loop lemmas (stmtSimForLoop's
   for_iteration and for_loop, stmtSimFor's compile_for_range_frag), whose
   proofs this one follows with fragLoopMemory's frag_exec_loop_mem as the
   loop step. *)
Theory stmtForRangeLitMemory
Ancestors
  stmtSimDefs exprSimMemDefs stmtLowering compileEnv vyperInterpreter
  vyperState

Theorem compile_for_range_lit_frag_mem:
  !P d ctx func cx lctx RetQ cenv ty id fty a1 n1 a2 n2 bound stmts es tyv.
    evaluate_type (get_tenv cx) fty = SOME tyv /\ type_memory_size tyv = 32 /\
    32 <= type_memory_bytes cenv fty /\
    type_memory_bytes cenv fty < dimword (:256) /\
    n1 <= n2 /\ Num (n2 - n1) <= bound /\ Num (n2 - n1) < dimword (:256) /\
    cenv.ce_alloca_locals /\ lookup_scopes id es.scopes = NONE /\
    (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
    (!c lc sa sb. compile_stmts c lc ty stmts sa = ((), sb) ==>
                  cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
    P (es with gas_obs := []) /\
    (!st0 c st1 ex inc ei j.
       declare_local cenv id fty st0 = (c, st1) /\
       P ei /\ lookup_scopes id ei.scopes = NONE /\ j < Num (n2 - n1) ==>
       stmt_frag_mem d ctx func cx (InLoop ex inc) RetQ c
         (stmts_env c (InLoop ex inc) ty stmts) (eval_stmts cx stmts)
         (ei with scopes :=
            (FEMPTY |+ (id, <| assignable := F; type := tyv;
                               value := IntV (n1 + &j); popped := [] |>)) :: ei.scopes)) /\
    (!ei j gs r2 es2 sc rest.
       P ei /\ lookup_scopes id ei.scopes = NONE /\ j < Num (n2 - n1) /\
       eval_stmts cx stmts
         (ei with <| scopes :=
            (FEMPTY |+ (id, <| assignable := F; type := tyv;
                               value := IntV (n1 + &j); popped := [] |>)) :: ei.scopes;
                     gas_obs := gs |>) = (r2, es2) /\
       (r2 = INL () \/ r2 = INR ContinueException) /\
       es2.scopes = sc :: rest ==>
       P (es2 with scopes := rest)) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty
         (For id fty (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2)))
         bound stmts))
      (eval_stmt cx
         (For id fty (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2)))
         bound stmts)) es
Proof
  cheat
QED

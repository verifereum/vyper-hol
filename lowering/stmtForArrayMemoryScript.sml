(* For over a fixed array, memory-safe: the S3 twin of stmtSimForArrayFrag's
   compile_for_array_frag, with stmt_frag_mem for stmt_frag.  Admitted:
   held on S1's array loop tower (stmtSimForArray*, not built with proofs
   at the base cut), whose proof this one follows with fragLoopMemory's
   frag_exec_loop_mem as the loop step.  Beyond S1's premises, the array's
   region is bounded by the alloca frontier, which the element reads' memory
   safety needs. *)
Theory stmtForArrayMemory
Ancestors
  stmtSimDefs stmtLowering compileEnv valueEncoding vyperInterpreter
  vyperState

Theorem compile_for_array_frag_mem:
  !d ctx func cx cenv lctx RetQ ty id et n name arr_ptr arr_sz stmts tv vs es P.
  (!gs. eval_iterator cx (Array (Name (ArrayT et (Fixed n)) name))
          (es with gas_obs := gs) = (INL vs, es with gas_obs := gs)) /\
  LENGTH vs = n /\
  n < dimword (:256) /\ evaluate_type (get_tenv cx) et = SOME tv /\
  type_memory_bytes cenv et = type_memory_size tv /\
  type_memory_bytes cenv et + 64 < dimword (:256) /\ cenv.ce_alloca_locals /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var arr_ptr) arr_sz) /\
  name <> id /\ lookup_scopes id es.scopes = NONE /\
  (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
  (!c lc sa sb. compile_stmts c lc ty stmts sa = ((),sb) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
  P es /\
  (!k. k < LENGTH vs ==> value_has_type tv (EL k vs) /\ val_wf tv (EL k vs)) /\
  (!ei s. P ei /\ stmt_state_rel ctx func cenv cx ei s ==>
    ?base. eval_operand (Var arr_ptr) s = SOME base /\
      w2n base + LENGTH vs * type_memory_size tv <= s.vs_alloca_next /\
      (!k. k < LENGTH vs ==>
        val_in_memory tv (EL k vs) (w2n base + k * type_memory_size tv) s.vs_memory /\
        w2n base + k * type_memory_size tv < dimword (:256))) /\
  (!st0 bc sd ex inc ei k.
    declare_local cenv id et st0 = (bc,sd) /\
    P ei /\ lookup_scopes id ei.scopes = NONE /\ k < LENGTH vs ==>
    stmt_frag_mem d ctx func cx (InLoop ex inc) RetQ bc
      (stmts_env bc (InLoop ex inc) ty stmts) (eval_stmts cx stmts)
      (ei with scopes :=
        (FEMPTY |+ (id, <|assignable := F; type := tv; value := EL k vs; popped := []|>))
          :: ei.scopes)) /\
  (!ei k gs r es2.
    P ei /\ lookup_scopes id ei.scopes = NONE /\ k < LENGTH vs /\
    eval_stmts cx stmts (ei with <| scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tv; value := EL k vs; popped := []|>))
        :: ei.scopes; gas_obs := gs |>) = (r,es2) ==>
    (!ex inc. stmt_res_ok (InLoop ex inc) r) /\
    ?sc rest. es2.scopes = sc :: rest /\
      (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
      ((r = INL () \/ r = INR ContinueException) ==>
        P (es2 with scopes := rest) /\ lookup_scopes id rest = NONE)) ==>
  stmt_frag_mem d ctx func cx lctx RetQ cenv
    (stmt_env cenv lctx ty (For id et (Array (Name (ArrayT et (Fixed n)) name)) n stmts))
    (eval_stmt cx (For id et (Array (Name (ArrayT et (Fixed n)) name)) n stmts)) es
Proof
  cheat
QED

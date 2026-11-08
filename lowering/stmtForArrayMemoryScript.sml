(* Memory-safe fixed-array statement fragments.  The functional compiler
   layout comes from the existing array tower; memory-safe initialization,
   element copies and counted rounds are established by stmtForArrayMemory*.
   The array region bound keeps each element read below the alloca frontier. *)
Theory stmtForArrayMemory
Ancestors
  stmtSimDefs stmtLowering stmtLoweringMono compileEnv valueEncoding vyperInterpreter
  vyperState stmtForArrayMemoryRounds stmtForArrayMemoryEntry
  stmtForArrayMemorySupport stmtSimForArrayFrag stmtSimForArrayLoop
  loweringPosts bodyMemoryDefs stmtSimProps exprLoweringProps fragGasMode finite_map list arithmetic

Theorem compile_for_array_frag_mem:
  !d ctx func cx cenv lctx RetQ ty id et n name arr_ptr arr_sz stmts tv vs es P.
  (!gs. eval_iterator cx (Array (Name (ArrayT et (Fixed n)) name))
          (es with gas_obs := gs) = (INL (MAP Value vs), es with gas_obs := gs)) /\
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
  rpt gen_tac >> strip_tac >>
  rw[stmt_frag_mem_def] >>
  `compile_stmt cenv lctx ty
    (For id et (Array (Name (ArrayT et (Fixed (LENGTH vs))) name)) (LENGTH vs) stmts) sa = ((),sb)` by
    (gvs[stmt_env_def, declare_stmt_local_def, comp_bind_def, comp_ignore_bind_def,
         comp_return_def, AllCaseEqs()] >>
     pairarg_tac >> gvs[]) >>
  
  drule_all compile_for_array_code_ready_framed >> strip_tac >>
  `?base. eval_operand (Var arr_ptr) s0 = SOME base` by metis_tac[] >>
  `ainst.inst_operands = [Lit (n2w (type_memory_bytes cenv et))] /\
   type_memory_bytes cenv et < dimword (:256)` by simp[venomInstTheory.mk_inst_def] >>
  `lookup_block s0.vs_current_bb func.fn_blocks =
    SOME <|bb_label := sa.cs_current_bb; bb_instructions := sa.cs_current_insts ++
      [ainst; mk_inst (sa.cs_next_id + 1) JMP [Label entry] []]|>` by simp[] >>
  `?s1 dst s.
    exec_alloca ainst s0 (n2w (type_memory_bytes cenv et) : bytes32) = OK s1 /\
    s = jump_to cond (update_var idx 0w (jump_to entry s1)) /\
    array_loop_inv ctx func cenv cx P vs id idx (Var arr_ptr) base' p dst
      (type_memory_bytes cenv et) ainst cond sa 0 es s /\
    gas_path_mem ctx func s0 0 (OK s) /\
    (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x s0) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b) /\
    s.vs_memory = s0.vs_memory /\
    s0.vs_alloca_next <= s.vs_alloca_next /\ alloca_history func s` by
    (irule array_loop_initialize_mem >>
     goal_assum (drule_at Any) >> simp[] >>
     conj_tac >- (qexistsl_tac [`sa.cs_next_id + 2`, `sa.cs_next_id + 3`] >> simp[]) >>
     conj_tac >- (qexists_tac `sa.cs_next_id + 1` >> simp[]) >>
     conj_tac >- (qexistsl_tac [`arr_sz`, `name`] >> simp[]) >>
     gvs[] >> goal_assum (drule_at Any)) >>
  `array_round_inv d ctx func cenv cx P vs id idx (Var arr_ptr) base' p dst
     (type_memory_bytes cenv et) ainst cond sa s0 0 es s` by
    (simp[array_round_inv_def, array_round_frame_def] >>
     irule return_buf_frame_frame >> goal_assum (drule_at Any) >> gvs[]) >>
  `gas_outcome T (cx_tops cx) (ctx,func)
     (eval_for cx tv id stmts (MAP Value (DROP 0 vs))) (es,s)
     (\res ee t. res = INL () /\
       array_round_done d ctx func cenv cx sa s0 exit ee t)
     (\res ee rr. ?ex. res = INR ex /\
       !tail. stmt_exit RetQ (ee with gas_obs := tail) (INR ex) rr)` by
    (drule array_code_loop_outcome_mem >> disch_then irule >>
     gvs[] >> conj_tac
     >- (drule array_for_code_stmts >> strip_tac >>
         drule array_for_code_prefix >> strip_tac >>
         `cs_extends sb0 sb1` by metis_tac[] >>
         drule_all fragExecTheory.fn_has_code_start >> gvs[]) >>
     conj_tac
     >- (qexists_tac `\r. T` >> simp[gasContextTheory.gas_admissible_def]) >>
     qexistsl_tac [`P`, `base'`, `dst`] >> simp[] >>
     conj_tac >- suspend "element_layout" >>
     suspend "body_hypotheses") >>
  suspend "public_outcome"
QED

Resume compile_for_array_frag_mem[element_layout]:
  rpt strip_tac >>
  gvs[array_loop_inv_def] >>
  qpat_x_assum `!ei s. P ei /\ stmt_state_rel _ _ _ _ ei s ==> _`
    (qspecl_then [`ei`, `t`] mp_tac) >>
  simp[] >> strip_tac >> gvs[] >>
  first_x_assum (qspec_then `k` mp_tac) >> simp[]
QED

Resume compile_for_array_frag_mem[body_hypotheses]:
  rpt gen_tac >> strip_tac >>
  conj_tac
  >- (drule array_for_code_copy_reserved >> strip_tac >>
      `FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) (type_memory_size tv))` by
        fs[array_for_code_def] >>
      qpat_x_assum `local_ptrs_reserved bc sa'` mp_tac >>
      qpat_x_assum `FLOOKUP bc.ce_vars id = _` mp_tac >>
      qpat_x_assum `lookup_scopes id ei.scopes = NONE` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >>
      simp[local_ptrs_reserved_def, not_local_ptr_def, lookup_scopes_def] >>
      ntac 3 strip_tac >> conj_tac
      >- (rpt strip_tac >>
          qpat_x_assum `!n1 n2 p sz1 sz2. _` drule >>
          disch_then (qspec_then `id` mp_tac) >> simp[] >>
          qexists_tac `type_memory_size tv` >> simp[] >>
          strip_tac >> gvs[]) >>
      strip_tac >> qpat_x_assum `!x. _` drule >> simp[] >>
      disj2_tac >> qexistsl_tac [`id`, `type_memory_size tv`] >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `!st0 bc sd ex inc ei k. _` drule_all >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!ei k gs r es2. _` drule_all >> simp[]
QED

Resume compile_for_array_frag_mem[public_outcome]:
  irule array_for_source_prefix_mem >> simp[] >>
  `gas_marked_path T ctx func s0 0 (OK s)` by
    (irule gas_marked_path_from_mem >> simp[]) >>
  `gas_outcome T (cx_tops cx) (ctx,func)
     (eval_for cx tv id stmts (MAP Value vs)) (es,s0)
     (\res ee t. res = INL () /\
       array_round_done d ctx func cenv cx sa s0 exit ee t)
     (\res ee rr. ?ex. res = INR ex /\
       !tail. stmt_exit RetQ (ee with gas_obs := tail) (INR ex) rr)` by
    (irule stmtForArrayMemoryRoundSupportTheory.array_round_outcome_prefix_mem >> goal_assum (drule_at Any) >> gvs[]) >>
  ` (\res ee rr. ?ex. res = INR ex /\
       !tail. stmt_exit RetQ (ee with gas_obs := tail) (INR ex) rr) =
    (\res ee rr. !tail. stmt_exit RetQ (ee with gas_obs := tail) res rr)` by
    (simp[FUN_EQ_THM] >> Cases_on `res` >>
     simp[stmt_exit_def, exprSimDefsTheory.expr_exit_def]) >>
  gvs[] >>
  drule exprSimMemDefsTheory.gas_outcome_post_mono >> disch_then irule >>
  rpt strip_tac >>
  `cenv' = cenv` by
    (qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
     simp[stmt_env_def, declare_stmt_local_def, comp_bind_def,
          comp_return_def] >> simp[comp_ignore_bind_def, comp_bind_def, comp_return_def]) >>
  gvs[array_round_done_def, array_round_frame_def] >>
  simp[stmt_lands_def, cenv_top_ext_def, block_is_terminated_def] >>
  `ci_mono sa (SND (compile_stmt cenv lctx ty
     (For id et (Array (Name (ArrayT et (Fixed (LENGTH vs))) name)) (LENGTH vs) stmts) sa))` by
    simp[compile_stmt_ci_mono] >>
  gvs[ci_mono_def] >>
  Cases_on `d` >> gvs[return_buf_frame_def] >>
  Cases_on `x` >> gvs[return_buf_frame_def, not_fresh_at_def]
QED

Finalise compile_for_array_frag_mem

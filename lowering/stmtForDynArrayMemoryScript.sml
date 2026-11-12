Theory stmtForDynArrayMemory
Ancestors
  stmtForDynArrayMemoryEntry stmtForDynArrayMemoryRounds
  stmtForArrayMemorySupport stmtForArrayMemoryRoundSupport stmtForArrayMemoryRounds
  whitelistForIterDynFrag whitelistForIterDynLoop stmtSimForArrayLoop
  stmtSimForArrayFrag stmtSimProps exprLoweringProps stmtLowering stmtLoweringMono
  bodyMemoryDefs stmtSimDefs loweringPosts compileEnv loweringStateRelDefs
  venomState venomInst fragGasMode fragGasPathMem fragExec allocaHistory
  vyperInterpreter vyperState vyperValue gasContext gasOutcome gasSummary
  gasExemptCert stmtSimDeclGas finite_map list arithmetic
Libs
  monadsyntax

val _ = Parse.hide "body";

Theorem dynarray_for_source_prefix_mem[local]:
  evaluate_type (get_tenv cx) et = SOME tv /\ LENGTH vs <= n /\ ~s0.vs_halted /\
  (!gs. eval_iterator cx it (es with gas_obs := gs) =
        (INL vs, es with gas_obs := gs)) /\
  gas_outcome T tops (ctx,func) (eval_for cx tv id body vs) (es,s0) Q R ==>
  gas_outcome T tops (ctx,func) (eval_stmt cx (For id et it n body)) (es,s0) Q R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def] >> strip_tac >> qexists `marks`
  >- (disj1_tac >>
      qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
      simp[gas_summary_at_def, gas_marked_exec_def, Once evaluate_def,
           bind_def, lift_option_type_def, ignore_bind_def, check_def,
           compatible_bound_def, vyperStateTheory.assert_def, return_def]) >>
  disj2_tac >>
  `assert T (Error (RuntimeError "For too long")) = return ()` by
    simp[FUN_EQ_THM, vyperStateTheory.assert_def, return_def] >>
  rename1 `gas_exempt_cert _ _ _ _ _ _ (err,ee) (leaf,target)` >>
  qexistsl_tac [`err`, `ee`, `leaf`, `target`] >>
  simp[Once evaluate_def, lift_option_type_def, bind_return,
       ignore_bind_def, bind_assoc] >>
  `gas_marked_exec T (ctx,func) (eval_iterator cx it) (es,s0)
     [] (INL vs) es (OK s0)` by
    (simp[gas_marked_exec_def, gas_marked_path_def] >>
     irule (cj 1 gas_path_mem_rules) >> simp[]) >>
  drule gas_exempt_cert_bind_results >>
  simp[] >> disch_then irule >>
  simp[check_def, compatible_bound_def, vyperStateTheory.assert_def, bind_return,
       GSYM ignore_bind_def] >>
  drule gas_exempt_cert_start_gas_obs >>
  disch_then (qspec_then `[]` mp_tac) >>
  simp[ignore_bind_def, vyperStateTheory.assert_def, bind_return]
QED

Theorem array_caller_return_buf_frame[local]:
  return_buf_frame d cenv sa s /\ array_caller_frame sa s t /\
  (!x. not_fresh_at sa x ==> not_fresh_at sb x) /\
  s.vs_alloca_next <= t.vs_alloca_next ==>
  return_buf_frame d cenv sb t
Proof
  Cases_on `d` >> simp[return_buf_frame_def] >>
  PairCases_on `x` >> simp[return_buf_frame_def] >>
  strip_tac >> fs[array_caller_frame_def] >>
  qexistsl_tac [`x`, `slot_size`] >> simp[] >> metis_tac[LESS_EQ_TRANS]
QED

Theorem not_fresh_inclusion_counter[local]:
  (!x. not_fresh_at a x ==> not_fresh_at b x) ==>
  a.cs_next_var <= b.cs_next_var
Proof
  strip_tac >> spose_not_then assume_tac >>
  `not_fresh_at a (STRING #"%" (toString b.cs_next_var))` by
    simp[not_fresh_at_def, ASCIInumbersTheory.toString_11] >>
  first_x_assum drule >> rewrite_tac[not_fresh_at_def] >>
  disch_then (qspec_then `b.cs_next_var` mp_tac) >> simp[]
QED

Theorem compile_for_dynarray_frag_mem:
  !d ctx func cx cenv lctx RetQ ty id et c n name arr_ptr arr_sz stmts tv vs es P.
  (!gs. eval_iterator cx (Array (Name (ArrayT et (Dynamic c)) name))
          (es with gas_obs := gs) = (INL (MAP Value vs), es with gas_obs := gs)) /\
  LENGTH vs <= c /\ c <= n /\ c < dimword (:256) /\
  evaluate_type (get_tenv cx) et = SOME tv /\
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
      mload (w2n base) s = n2w (LENGTH vs) /\
      w2n base + 32 + LENGTH vs * type_memory_size tv <= s.vs_alloca_next /\
      (!k. k < LENGTH vs ==>
        val_in_memory tv (EL k vs)
          (w2n base + 32 + k * type_memory_size tv) s.vs_memory /\
        w2n base + 32 + k * type_memory_size tv < dimword (:256))) /\
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
    (stmt_env cenv lctx ty
      (For id et (Array (Name (ArrayT et (Dynamic c)) name)) n stmts))
    (eval_stmt cx (For id et (Array (Name (ArrayT et (Dynamic c)) name)) n stmts)) es
Proof
  rpt gen_tac >> strip_tac >> rw[stmt_frag_mem_def] >>
  `compile_stmt cenv lctx ty
    (For id et (Array (Name (ArrayT et (Dynamic c)) name)) n stmts) sa = ((),sb)` by
    (gvs[stmt_env_def, declare_stmt_local_def, comp_bind_def, comp_ignore_bind_def,
         comp_return_def, AllCaseEqs()] >> pairarg_tac >> gvs[]) >>
  drule_all compile_for_dynarray_code_ready >> strip_tac >>
  qpat_assum `!ei s. P ei /\ stmt_state_rel _ _ _ _ ei s ==> _` drule_all >> strip_tac >>
  rename1 `eval_operand (Var arr_ptr) s0 = SOME arr_base` >>
  `type_memory_bytes cenv et < dimword (:256)` by simp[] >>
  `ainst.inst_operands = [Lit (n2w (type_memory_bytes cenv et))] /\
   ainst.inst_opcode = ALLOCA /\ ainst.inst_outputs = [p]` by simp[mk_inst_def] >>
  `MEM ainst (fn_insts func)` by
    (irule lookup_block_fn_insts >>
     qpat_assum `lookup_block sa.cs_current_bb _ = _` (irule_at (Pos hd)) >> simp[]) >>
  `not_local_ptr cenv es.scopes p` by
    (`bc.ce_imm_alloca = cenv.ce_imm_alloca /\ local_ptrs_reserved bc sa' /\
      FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) (type_memory_bytes cenv et)) /\
      (!name. name <> id ==> FLOOKUP bc.ce_vars name = FLOOKUP cenv.ce_vars name)` by
       fs[dynarray_for_code_def, compile_env_component_equality] >>
     drule_all array_allocation_safe >> simp[]) >>
  `?dst cc s1.
    exec_alloca ainst (update_var lv (n2w (LENGTH vs)) s0)
      (n2w (type_memory_bytes cenv et) : bytes32) = OK s1 /\
    cc = jump_to cond (update_var vld 1w (update_var g 0w
      (update_var idx 0w (jump_to entry s1)))) /\
    array_loop_inv ctx func cenv cx P vs id idx (Var arr_ptr) arr_base p dst
      (type_memory_bytes cenv et) ainst cond sa 0 es cc /\
    lookup_var lv cc = SOME (n2w (LENGTH vs)) /\
    array_caller_frame sa s0 cc /\ gas_marked_path F ctx func s0 0 (OK cc) /\
    gas_path_mem ctx func s0 0 (OK cc) /\ alloca_history func cc /\
    cc.vs_memory = s0.vs_memory /\ s0.vs_alloca_next <= cc.vs_alloca_next` by
    (irule dynarray_loop_initialize_mem >> simp[] >> metis_tac[]) >>
  suspend "loop"
QED
Resume compile_for_dynarray_frag_mem[loop]:
  qpat_x_assum `cc = _` kall_tac >>
  `array_round_inv d ctx func cenv cx P vs id idx (Var arr_ptr) arr_base p dst
     (type_memory_bytes cenv et) ainst cond st1 cc 0 es cc` by
    (pure_rewrite_tac[array_round_inv_def] >> conj_tac
     >- (qhdtm_assum `array_loop_inv` mp_tac >>
         pure_rewrite_tac[array_loop_inv_def, ret_pc_ok_def] >>
         qpat_x_assum `!x. not_fresh_at sa x ==> not_fresh_at st1 x` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
     pure_rewrite_tac[array_round_frame_def] >> simp[] >>
     irule array_caller_return_buf_frame >>
     qexistsl_tac [`s0`, `sa`] >> simp[]) >>
  `?bb. lookup_block bod func.fn_blocks = SOME bb /\
    isPREFIX sb0.cs_current_insts bb.bb_instructions` by
    (`cs_extends sb0 sb1 /\ fn_has_code sb0 sb1 func /\ sb0.cs_current_bb = bod` by
       (fs[dynarray_for_code_def] >> metis_tac[]) >>
     drule_all fn_has_code_start >> simp[]) >>
  `sa.cs_next_var <= sa'.cs_next_var /\ st1.cs_next_var <= sa'.cs_next_var /\
   (!x. not_fresh_at st1 x ==>
     x <> idx /\ x <> dv /\ x <> ov /\ x <> tot /\ x <> ep /\ x <> nv)` by
    (conj_tac
     >- (irule not_fresh_inclusion_counter >>
         qpat_x_assum `!x. not_fresh_at sa x ==> not_fresh_at st1 x` mp_tac >>
         qpat_x_assum `!x. not_fresh_at st1 x ==> not_fresh_at sa' x /\ _` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
     conj_tac
     >- (irule not_fresh_inclusion_counter >>
         qpat_x_assum `!x. not_fresh_at st1 x ==> not_fresh_at sa' x /\ _` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
     qpat_x_assum `!x. not_fresh_at st1 x ==> not_fresh_at sa' x /\ _` mp_tac >>
     qpat_x_assum `!x. not_fresh_at st1 x ==> not_fresh_at sb0 x /\ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `gas_outcome T (cx_tops cx) (ctx,func)
     (eval_for cx tv id stmts (MAP Value (DROP 0 vs))) (es,cc)
     (\res ee t. res = INL () /\
       array_round_done d ctx func cenv cx st1 cc exit ee t)
     (\res ee rr. ?ex. res = INR ex /\
       !tail. stmt_exit RetQ (ee with gas_obs := tail) (INR ex) rr)` by
    (drule dynarray_code_loop_outcome_mem >> disch_then irule >>
     simp[] >> conj_tac
     >- (qhdtm_assum `dynarray_for_code`
           (strip_assume_tac o PURE_REWRITE_RULE [dynarray_for_code_def]) >>
         qpat_x_assum `compile_iter_elem_copy _ _ _ _ _ _ _ _ _ = _` mp_tac >>
         mp_tac (cj 6 ci_mono_stmt_helpers) >>
         POP_ASSUM_LIST (K ALL_TAC) >>
         rpt strip_tac >> fs[ci_mono_def] >> metis_tac[pairTheory.SND]) >>
     conj_tac >- (qexists_tac `\r. T` >> simp[gas_admissible_def]) >>
     qexistsl_tac [`P`, `arr_base`, `dst`] >>
     conj_tac >- suspend "snapshot" >>
     conj_tac >- suspend "callbacks" >>
     gvs[]) >>
  suspend "public"
QED
Resume compile_for_dynarray_frag_mem[callbacks]:
  rpt gen_tac >> strip_tac >> conj_tac
  >- (irule localPtrsPropsTheory.not_local_ptr_name_update >>
      qexistsl_tac [`cenv`, `id`] >> simp[] >>
      conj_tac >- fs[dynarray_for_code_def] >>
      conj_tac >- fs[dynarray_for_code_def, compile_env_component_equality] >>
      irule exprSimOperandsTheory.fresh_not_local_ptr >>
      qexists_tac `sa` >> simp[] >>
      strip_tac >>
      qpat_x_assum `!x. not_fresh_at sa x ==> ~MEM x _` drule >> simp[]) >>
  conj_tac
  >- (qpat_assum `!st0 bc sd ex inc ei k. _` drule_all >> simp[]) >>
  rpt strip_tac >> qpat_assum `!ei k gs r es2. _` drule_all >> simp[]
QED
Resume compile_for_dynarray_frag_mem[snapshot]:
  rpt strip_tac >>
  qhdtm_assum `array_loop_inv`
    (strip_assume_tac o PURE_REWRITE_RULE [array_loop_inv_def]) >>
  qpat_assum `!ei s. P ei /\ stmt_state_rel _ _ _ _ ei s ==> _` drule_all >>
  strip_tac >> gvs[eval_operand_def] >>
  res_tac >> gvs[]
QED
Resume compile_for_dynarray_frag_mem[public]:
  irule dynarray_for_source_prefix_mem >> simp[] >>
  `gas_marked_path T ctx func s0 0 (OK cc)` by
    (irule gas_marked_path_from_mem >> simp[]) >>
  `gas_outcome T (cx_tops cx) (ctx,func)
     (eval_for cx tv id stmts (MAP Value vs)) (es,s0)
     (\res ee t. res = INL () /\
       array_round_done d ctx func cenv cx st1 cc exit ee t)
     (\res ee rr. ?ex. res = INR ex /\
       !tail. stmt_exit RetQ (ee with gas_obs := tail) (INR ex) rr)` by
    (irule array_round_outcome_prefix_mem >> goal_assum (drule_at Any) >> gvs[]) >>
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
          comp_return_def, comp_ignore_bind_def]) >>
  gvs[array_round_done_def, array_round_frame_def] >>
  simp[stmt_lands_def, cenv_top_ext_def, block_is_terminated_def] >>
  conj_tac
  >- (fs[array_caller_frame_def] >> metis_tac[]) >>
  conj_tac
  >- (fs[array_caller_frame_def] >> metis_tac[]) >>
  `ci_mono sa (SND (compile_stmt cenv lctx ty
     (For id et (Array (Name (ArrayT et (Dynamic c)) name)) n stmts) sa))` by
    simp[compile_stmt_ci_mono] >>
  gvs[ci_mono_def] >>
  Cases_on `d` >> gvs[return_buf_frame_def] >>
  Cases_on `x` >> gvs[return_buf_frame_def] >>
  qpat_x_assum `not_fresh_at sa x` mp_tac >>
  qpat_x_assum `sa.cs_next_var <= sb.cs_next_var` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]
QED
Finalise compile_for_dynarray_frag_mem

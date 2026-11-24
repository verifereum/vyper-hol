(* A runtime MethodId visit is owned by its forced child or by the
   administrative suffix after the first exit of that child. *)
Theory entryCreateMethodIdRuntimeVisit
Ancestors
  entryCreateNativeFirstExit entryCreateAdminSequence entryCreateIntervalLayout
  entryCreateFocusSpec entryCreateBodyCut createSizeCutCode
  s1PrefixDefs exprSimHash exprSimSource exprSimUnopComposeProps exprSimUnopProps
  exprSimWordArgs exprSimHypsDefs
  bodyFullShared gasShadowCompileStmtHelpers gasShadowCompilePure gasShadowState
  gasShadow gasExplicitSites exprLoweringProps exprLowering builtinHashing
  context compileEnv fragExec vyperStorageTrace vyperInterpreter vyperContext
  vyperState vyperAST venomInst list

Theorem method_id_split_cut[local]:
  body_inv tops ctx ce cx /\ MEM f ctx.ctx_functions /\
  create_cut_code {} sa sm /\ fn_has_code sa sm f /\
  create_cut_code {} sm sb /\ fn_has_code sm sb f /\
  sb.cs_current_bb = sm.cs_current_bb /\
  sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
  EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
             i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (emitted_insts sm sb) /\
  create_operand_cut sa sm E ctx f tops cx st0 source (es,s) /\
  (!v. storage_trace_frame (next v)) ==>
  create_operand_cut sa sb E ctx f tops cx st0 (bind source next) (es,s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  simp[create_operand_cut_def] >> rpt gen_tac >> strip_tac >>
  drule_all create_interior_visit_first_exit >> strip_tac
  >- (irule create_cut_bind_left >> fs[create_operand_cut_def] >> metis_tac[]) >>
  (* The suffix cannot contain the selected bad CREATE visit, independently
     of the source action or whether the suffix itself completes. *)
  simp[create_body_cut_def] >> rpt strip_tac >>
  `create_operand_cut sm sb E ctx f tops cx st0 (\_. (res,ee)) (es,t)` by
    (irule create_admin_sequence_cut >> simp[]) >>
  qpat_x_assum `create_operand_cut sm sb _ _ _ _ _ _ _ _` mp_tac >>
  simp[create_operand_cut_def,create_body_cut_def] >>
  disch_then (drule_then mp_tac) >> simp[] >> metis_tac[]
QED

Theorem method_id_source_actions[local]:
  eval_expr cx (Builtin ann MethodId [e]) =
    bind (bind (eval_expr cx e) (read_result cx))
      (\v mid. ((case builtin_result cx mid.accounts ann MethodId [expr_type e] [v] of
                    INL r => INL (Value r) | INR ex => INR ex),mid)) /\
  bind (eval_expr cx (Builtin ann MethodId [e])) (read_result cx) =
    bind (bind (eval_expr cx e) (read_result cx))
      (\v mid. (builtin_result cx mid.accounts ann MethodId [expr_type e] [v],mid))
Proof
  conj_tac
  >- (irule eval_expr_unary_builtin_action >>
      simp[builtin_args_length_ok_def,is_self_codesize_def,precompile_builtin_def]) >>
  mp_tac (Q.INST [`bi` |-> `MethodId`, `ann` |-> `ann`, `e` |-> `e`, `cx` |-> `cx`]
    eval_expr_unop_action_general) >>
  simp[builtin_args_length_ok_def,is_self_codesize_def,builtin_result_def,
       unop_result_def,precompile_builtin_def]
QED

Theorem method_id_compile_ends[local]:
  (ann = BaseT (BytesT (Fixed 4)) \/ ~is_word_type ann) /\
  method_id_literal e = NONE /\
  lower_value compile_expr ce (expr_type e) e sa = (x,sm) /\
  compile_method_id_runtime (expr_type e) x (ann = BaseT (BytesT (Fixed 4))) sm = (y,sb) ==>
  SND (compile_expr ce ty (Builtin ann MethodId [e]) sa) = sb /\
  SND (lower_value compile_expr ce ty (Builtin ann MethodId [e]) sa) = sb
Proof
  rpt (disch_then (CONJUNCTS_THEN2 assume_tac mp_tac)) >> strip_tac >>
  Cases_on `ann = BaseT (BytesT (Fixed 4))` >> gvs[] >>
  simp[Once lower_value_def, compile_method_id_singleton_runtime, comp_bind_def,
       as_stack_val_def, as_ptr_val_def, unwrap_value_def, comp_return_def,
       expr_type_def,is_word_type_def,mk_ptr_def]
QED

Theorem method_id_runtime_site_cut[local]:
  (!aty x fixed m b y.
    compile_method_id_runtime aty x fixed m = (y,b) ==>
    create_cut_code {} m b /\ b.cs_current_bb = m.cs_current_bb /\
    b.cs_current_insts = m.cs_current_insts ++ emitted_insts m b /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
               i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (emitted_insts m b)) /\
  body_inv tops ctx ce cx /\ expr_body_pre ce cx env (Builtin ann MethodId [e]) es /\
  method_id_literal e = NONE /\ create_layout sa sb /\
  (!x sm shm.
    expr_body_pre ce cx env e es /\ create_layout sa sm /\
    expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,shf) ce cx (expr_type e) e
      es (st0,sa,sm,sha,shm,x,s,G,tn) ==>
    create_cut_code {} sa sm /\
    create_operand_cut sa sm (gas_explicit_sites ctx shctx) ctx f tops cx st0
      (bind (eval_expr cx e) (read_result cx)) (es,s)) /\
  ((?op. expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,shf) ce cx ty (Builtin ann MethodId [e])
      es (st0,sa,sb,sha,shb,op,s,G,tn)) \/
   (?vv. expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,shf) ce cx ty (Builtin ann MethodId [e])
      es (st0,sa,sb,sha,shb,vv,s,G,tn))) ==>
  create_operand_cut sa sb (gas_explicit_sites ctx shctx) ctx f tops cx st0
    (bind (eval_expr cx (Builtin ann MethodId [e])) (read_result cx)) (es,s) /\
  create_operand_cut sa sb (gas_explicit_sites ctx shctx) ctx f tops cx st0
    (eval_expr cx (Builtin ann MethodId [e])) (es,s)
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac mp_tac) >>
  rpt (disch_then (CONJUNCTS_THEN2 assume_tac mp_tac)) >>
  disch_then (DISJ_CASES_THEN (CHOOSE_THEN
    (strip_assume_tac o REWRITE_RULE [expr_sim_full_pre_def,expr_vv_sim_full_pre_def]))) >>
  `expr_body_pre ce cx env e es` by
    (drule expr_body_pre_builtin_arg >> disch_then irule >> fs[expr_body_pre_def]) >>
  `ann = BaseT (BytesT (Fixed 4)) \/ ~is_word_type ann` by
    (mp_tac (Q.INST [`b` |-> `MethodId`, `ty` |-> `ann`, `ts` |-> `[expr_type e]`]
       hash_builtin_types) >>
     gvs[expr_body_pre_def, cj 9 vyperTypeSystemTheory.well_typed_expr_def] >>
     strip_tac >> gvs[is_word_type_def]) >>
  Cases_on `lower_value compile_expr ce (expr_type e) e sa` >>
  rename1 `lower_value compile_expr ce (expr_type e) e sa = (x,sm)` >>
  Cases_on `lower_value compile_expr (gas_shadow_env T ce) (expr_type e)
      (gas_shadow_expr e) sha` >>
  rename1 `lower_value compile_expr (gas_shadow_env T ce) (expr_type e)
      (gas_shadow_expr e) sha = (sx,shm)` >>
  `sx = x /\ gas_shadow_state sm shm` by
    (irule gas_shadow_step >>
     qpat_assum `lower_value _ _ _ e sa = _` (irule_at Any) >>
     qpat_assum `lower_value _ _ _ (gas_shadow_expr e) sha = _` (irule_at Any) >>
     simp[gas_shadow_stmt_lower_value_env]) >>
  qpat_x_assum `sx = x` SUBST_ALL_TAC >>
  Cases_on `compile_method_id_runtime (expr_type e) x (ann = BaseT (BytesT (Fixed 4))) sm` >>
  rename1 `compile_method_id_runtime _ x _ sm = (y,b)` >>
  Cases_on `compile_method_id_runtime (expr_type e) x (ann = BaseT (BytesT (Fixed 4))) shm` >>
  rename1 `compile_method_id_runtime _ x _ shm = (sy,shb')` >>
  `b = sb` by
    (qpat_assum `compile_method_id_runtime _ _ _ sm = _`
       (mp_then (Pos last) mp_tac method_id_compile_ends) >>
     disch_then (qspecl_then [`ty`,`sa`,`ce`] mp_tac) >> simp[]) >>
  `shb' = shb` by
    (qpat_assum `compile_method_id_runtime _ _ _ shm = _`
       (mp_then (Pos last) mp_tac
          (REWRITE_RULE [gas_shadow_expr_type]
            (Q.INST [`e` |-> `gas_shadow_expr e`] method_id_compile_ends))) >>
     disch_then (qspecl_then [`ty`,`sha`,`gas_shadow_env T ce`] mp_tac) >>
     fs[Once gas_shadow_expr_def,gas_shadow_builtin_def]) >>
  qpat_x_assum `b = sb` SUBST_ALL_TAC >>
  qpat_x_assum `shb' = shb` SUBST_ALL_TAC >>
  `cs_extends sa sm /\ cs_extends sha shm` by metis_tac[cj 2 compile_expr_grows] >>
  `cs_extends sm sb /\ cs_extends shm shb` by
    metis_tac[cj 5 hash_suffix_appends,cs_appends_def] >>
  `fn_has_code sa sm f /\ fn_has_code sm sb f /\ fn_has_code sha shm shf` by
    metis_tac[fn_has_code_split] >>
  `create_layout sa sm` by metis_tac[create_layout_subinterval,cs_extends_refl] >>
  `expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,shf) ce cx (expr_type e) e es
     (st0,sa,sm,sha,shm,x,s,G,tn)` by
    (simp[expr_sim_full_pre_def] >> metis_tac[expr_body_pre_gas_admissible]) >>
  qpat_x_assum `!x sm shm. _` (drule_all_then strip_assume_tac) >>
  qpat_assum `!aty x fixed m b y. _` (drule_then strip_assume_tac) >>
  simp[method_id_source_actions] >> conj_tac >>
  irule method_id_split_cut >> simp[storage_trace_frame_def] >> metis_tac[]
QED

Theorem method_id_runtime_sites_cut_from_layout:
  (!aty x fixed m b y.
    compile_method_id_runtime aty x fixed m = (y,b) ==>
    create_cut_code {} m b /\ b.cs_current_bb = m.cs_current_bb /\
    b.cs_current_insts = m.cs_current_insts ++ emitted_insts m b /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
               i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (emitted_insts m b)) /\
  body_inv tops ctx ce cx /\ expr_body_pre ce cx env (Builtin ann MethodId [e]) es /\
  method_id_literal e = NONE /\
  (!st0 sa sha s G tn x sm shm.
    expr_body_pre ce cx env e es /\ create_layout sa sm /\
    expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,shf) ce cx (expr_type e) e
      es (st0,sa,sm,sha,shm,x,s,G,tn) ==>
    create_cut_code {} sa sm /\
    create_operand_cut sa sm (gas_explicit_sites ctx shctx) ctx f tops cx st0
      (bind (eval_expr cx e) (read_result cx)) (es,s)) ==>
  (!st0 sa sb sha shb op s G tn.
    create_layout sa sb /\
    expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,shf) ce cx ty (Builtin ann MethodId [e])
      es (st0,sa,sb,sha,shb,op,s,G,tn) ==>
    create_operand_cut sa sb (gas_explicit_sites ctx shctx) ctx f tops cx st0
      (bind (eval_expr cx (Builtin ann MethodId [e])) (read_result cx)) (es,s)) /\
  (!st0 sa sb sha shb vv s G tn.
    create_layout sa sb /\
    expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,shf) ce cx ty (Builtin ann MethodId [e])
      es (st0,sa,sb,sha,shb,vv,s,G,tn) ==>
    create_operand_cut sa sb (gas_explicit_sites ctx shctx) ctx f tops cx st0
      (eval_expr cx (Builtin ann MethodId [e])) (es,s))
Proof
  strip_tac >> conj_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!st0 sa sha s G tn x sm shm. _`
    (qspecl_then [`st0`,`sa`,`sha`,`s`,`G`,`tn`] assume_tac) >>
  (Q.SUBGOAL_THEN
    `(?op. expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,shf) ce cx ty (Builtin ann MethodId [e])
        es (st0,sa,sb,sha,shb,op,s,G,tn)) \/
     (?vv. expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,shf) ce cx ty (Builtin ann MethodId [e])
        es (st0,sa,sb,sha,shb,vv,s,G,tn))` assume_tac
  >- metis_tac[]) >>
  mp_tac method_id_runtime_site_cut >> asm_rewrite_tac[] >> simp[]
QED

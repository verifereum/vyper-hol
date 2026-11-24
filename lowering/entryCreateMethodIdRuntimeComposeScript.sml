(* The runtime MethodId suffix starts at the selected value-child exit. *)
Theory entryCreateMethodIdRuntimeCompose
Ancestors
  entryCreateScopedBind entryCreateWordArgsGeometry entryCreateIntervalLayout
  entryCreateFocusSpec entryCreateCompletedCut gasExemptCert gasSummary
  fragGasOriginPtr exprSimDefs s1PrefixDefs gasExplicitSites fragExec
  createSizeOperandCode createSizeCutCode
  bodyFullHashKeccakFixed[qualified,ignore_grammar]
  exprSimHash exprSimSource exprSimWordArgs exprSimUnopComposeProps exprSimUnopProps
  exprSimHyps exprSimHypsDefs exprSimFullBundleProps exprLoweringProps
  gasShadowCompileStmtHelpers gasShadowState gasShadow
  bodyFullShared bodyFullPreds bodyFullGhostFrame bodyPtrDefs
  loweringPosts builtinSimple vyperTypeSystem vyperTyping vyperStorageTrace
  vyperStorageFootprint vyperContext vyperState vyperAST fragGasSeqPtr
  exprLowering compileEnv context list pair

Theorem method_id_value_source[local]:
  bind (eval_expr cx (Builtin ann MethodId [e])) (read_result cx) =
  bind (bind (eval_expr cx e) (read_result cx))
    (\v mid. (builtin_result cx mid.accounts ann MethodId [expr_type e] [v],mid))
Proof
  mp_tac (Q.INST [`bi` |-> `MethodId`, `ann` |-> `ann`, `e` |-> `e`, `cx` |-> `cx`]
    eval_expr_unop_action_general) >>
  simp[builtin_args_length_ok_def, is_self_codesize_def, builtin_result_def,
       unop_result_def, vyperInterpreterTheory.precompile_builtin_def]
QED

Theorem method_id_vv_source[local]:
  eval_expr cx (Builtin ann MethodId [e]) =
  bind (bind (eval_expr cx e) (read_result cx))
    (\v mid. ((case builtin_result cx mid.accounts ann MethodId [expr_type e] [v] of
                 INL r => INL (Value r) | INR ex => INR ex),mid))
Proof
  irule eval_expr_unary_builtin_action >>
  simp[builtin_args_length_ok_def, is_self_codesize_def]
QED

Theorem method_id_child_type[local]:
  expr_body_pre cenv cx env (Builtin ann MethodId [e]) es ==>
  expr_body_pre cenv cx env e es /\
  post_value_type cenv e = expr_type e /\
  is_bytes_or_string_type (expr_type e) /\
  (ann = BaseT (BytesT (Fixed 4)) \/ ann = BaseT (BytesT (Dynamic 4)))
Proof
  strip_tac >>
  `expr_body_pre cenv cx env e es` by
    (drule expr_body_pre_builtin_arg >> disch_then irule >> gvs[expr_body_pre_def]) >>
  `is_bytes_or_string_type (expr_type e) /\
   (ann = BaseT (BytesT (Fixed 4)) \/ ann = BaseT (BytesT (Dynamic 4)))` by
    (mp_tac (Q.INST [`b` |-> `MethodId`, `ty` |-> `ann`, `ts` |-> `[expr_type e]`]
      hash_builtin_types) >>
     gvs[expr_body_pre_def, cj 9 well_typed_expr_def] >> metis_tac[]) >>
  simp[] >>
  `type_widens_to env.type_defs (post_value_type cenv e) (expr_type e)` by
    (irule post_value_type_widens >> gvs[expr_body_pre_def] >> metis_tac[]) >>
  Cases_on `expr_type e` >> gvs[is_bytes_or_string_type_def] >>
  rename1 `expr_type e = BaseT bt` >> Cases_on `bt` >>
  gvs[is_bytes_or_string_type_def, is_bytestring_type_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >> gvs[is_bytestring_type_def] >>
  Cases_on `post_value_type cenv e` >> gvs[type_widens_to_def, arg_type_fits_def] >>
  rename1 `BaseT physical` >> Cases_on `physical` >> gvs[arg_type_fits_def] >>
  rename1 `BytesT physical_bytes` >> Cases_on `physical_bytes` >> gvs[arg_type_fits_def]
QED

(* Normalize the source cursor passed to the successful continuation, without
   changing its path, endpoint, or all-horizon ghosts. *)
Theorem method_id_child_normalized[local]:
  scoped_operand_outcome (DF,lo,E,ctx,func,PG) tops cx st0 a m source start Q R ==>
  scoped_operand_outcome (DF,lo,E,ctx,func,PG) tops cx st0 a m source start
    (\H res ee G tn t. Q H res ee G tn t /\ ee.gas_obs = []) R
Proof
  PairCases_on `start` >> simp[scoped_operand_outcome_def]
QED

Theorem method_id_child_exit_mixed[local]:
  scoped_operand_outcome (DF,lo,E,ctx,func,PG) tops cx st0 a m source
    (es,s,G,tn) Q (create_operand_exit_post ctx cx) ==>
  scoped_operand_outcome (DF,lo,E,ctx,func,PG) tops cx st0 a m source
    (es,s,G,tn) Q (\H (res : value + exception) ee gt r. ?exc. res = INR exc /\
      create_operand_exit_post ctx cx H (INR exc : 'a + exception) ee gt r)
Proof
  simp[scoped_operand_outcome_def] >> strip_tac >> qexists_tac `marks`
  >- (disj1_tac >> simp[] >> qexistsl_tac [`H`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish'`] >> simp[])
  >- (disj2_tac >> disj1_tac >> qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >> simp[] >>
      rpt strip_tac >> first_x_assum drule >> strip_tac >> simp[] >>
      Cases_on `res` >> gvs[create_operand_exit_post_def, halt_exit_def, expr_exit_def] >>
      rename1 `INR ex` >> Cases_on `ex` >> Cases_on `r` >>
      gvs[halt_exit_def, expr_exit_def] >>
      rename1 `Error err` >> Cases_on `err` >> gvs[expr_exit_def]) >>
  disj2_tac >> disj2_tac >>
  qexistsl_tac [`err`,`ee`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish'`] >>
  simp[] >> qexists_tac `H` >> simp[]
QED

Theorem method_id_bind_child[local]:
  body_inv tops ctx cenv cx /\ MEM func ctx.ctx_functions /\
  create_layout sa sb /\ create_operand_at sa s0 /\
  create_cut_code {} sa sm /\ create_cut_code {} sm sb /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\
  scoped_operand_outcome (DF,lo,E,ctx,func,PG) (cx_tops cx) cx st0 sa sm
    (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (expr_sim_full_post (DF,lo,d,ctx,func) cenv cx e (es,sa,sm,s0,x,G0,tn0))
    (create_operand_exit_post ctx cx) /\
  (!v. storage_trace_frame (next v)) /\
  (!marks v mid G tn t.
    (!tail. bind (eval_expr cx e) (read_result cx)
       (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
       (INL v,mid with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\ mid.gas_obs = [] /\
    create_operand_at sm t /\ ~t.vs_halted /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      expr_sim_full_post (DF,lo,d,ctx,func) cenv cx e
        (es,sa,sm,s0,x,G0,tn0) H (INL v : value + exception) mid G tn t) ==>
    scoped_operand_outcome (DF,lo,E,ctx,func,PG) (cx_tops cx) cx st0 sm sb
      (next v) (mid,t,G,tn) Q (create_operand_exit_post ctx cx)) ==>
  scoped_operand_outcome (DF,lo,E,ctx,func,PG) (cx_tops cx) cx st0 sa sb
    (bind (bind (eval_expr cx e) (read_result cx)) next) (es,s0,G0,tn0)
    Q (create_operand_exit_post ctx cx)
Proof
  strip_tac >>
  `cs_extends sa sm /\ cs_extends sm sb /\
   sa.cs_next_id <= sm.cs_next_id /\ sm.cs_next_id <= sb.cs_next_id` by
    fs[create_cut_code_def] >>
  drule_all create_word_args_scope_embeddings >> disch_then (qspec_then `E` strip_assume_tac) >>
  irule scoped_operand_bind_all_mixed >> rpt conj_tac
  >~ [`!v. storage_trace_frame (next v)`] >- first_assum ACCEPT_TAC
  >~ [`storage_trace_frame (bind _ _)`] >-
    (irule storage_trace_frame_bind_all >>
     simp[cj 5 evaluate_storage_trace_frame, storage_trace_frame_read_result])
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`] >-
    (rpt strip_tac >> pure_rewrite_tac[ignore_bind_def] >>
     pure_once_rewrite_tac[bind_assoc] >> irule gas_exempt_cert_bind_value >>
     qexistsl_tac [`mid`,`t`,`v`] >> fs[ignore_bind_def])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`] >-
    (rpt strip_tac >> pure_rewrite_tac[ignore_bind_def] >>
     pure_once_rewrite_tac[bind_assoc] >> irule gas_exempt_cert_error_value >>
     simp[ignore_bind_def]) >>
  qmatch_asmsub_abbrev_tac `scoped_operand_outcome _ _ _ _ sa sm _ _ Qchild _` >>
  drule method_id_child_normalized >> strip_tac >>
  qexistsl_tac [`\H res ee G tn t. Qchild H res ee G tn t /\ ee.gas_obs = []`,`sm`] >>
  BETA_TAC >> reverse (rpt (conj_tac ORELSE first_assum ACCEPT_TAC))
  >- (irule method_id_child_exit_mixed >> first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  `~t.vs_halted` by
    metis_tac[gas_origin_ptr_path_projections, gas_path_ptr_ok_not_halted] >>
  `?v. res = INL v` by fs[Abbr `Qchild`,expr_sim_full_post_def] >>
  qexists_tac `v` >> simp[] >>
  qpat_assum `!marks v mid G tn t. _ ==> _` irule >>
  simp[Abbr `Qchild`] >> conj_tac
  >- (qexists_tac `marks` >> simp[]) >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  qpat_x_assum `res = INL v` SUBST_ALL_TAC >> first_assum ACCEPT_TAC
QED

Theorem method_id_suffix_normal[local]:
  storage_trace_domain cx st0 mid.storage_trace /\
  mid.gas_obs = [] /\
  (!tail. next (mid with gas_obs := tail) = (res,mid with gas_obs := tail)) /\
  create_operand_full_scope sm sb E ctx func t [] (OK z) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,E,ctx,func,PG) (t,G,tn) [] (OK z,G',tn') /\
    Q H res mid G' tn' z) ==>
  scoped_operand_outcome (DF,lo,E,ctx,func,PG) (cx_tops cx) cx st0 sm sb
    next (mid,t,G,tn) Q R
Proof
  strip_tac >> rewrite_tac[scoped_operand_outcome_def] >>
  qexists_tac `[]` >> disj2_tac >> disj1_tac >>
  qexistsl_tac [`res`,`mid`,`OK z`,`G'`,`tn'`] >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  simp[gas_explicit_def] >> rpt strip_tac >> disj1_tac >>
  first_x_assum drule >> simp[]
QED

Theorem method_id_runtime_shadow_pair[local]:
  !sa sha cenv ty. method_id_literal e = NONE /\
  ann = BaseT (BytesT (if fixed then Fixed 4 else Dynamic 4)) /\
  gas_shadow_state sa sha ==>
  ?x sm shm op b hb.
    lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
    lower_value compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) sha = (x,shm) /\
    gas_shadow_state sm shm /\ compile_method_id_runtime (expr_type e) x fixed sm = (op,b) /\
    compile_method_id_runtime (expr_type e) x fixed shm = (op,hb) /\
    compile_expr cenv ty (Builtin ann MethodId [e]) sa =
      ((if fixed then StackValue ann op else LocatedValue ann (mk_ptr op LocMemory)),b) /\
    compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr (Builtin ann MethodId [e])) sha =
      ((if fixed then StackValue ann op else LocatedValue ann (mk_ptr op LocMemory)),hb) /\
    lower_value compile_expr cenv ty (Builtin ann MethodId [e]) sa = (op,b) /\
    lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr (Builtin ann MethodId [e])) sha = (op,hb)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `lower_value compile_expr cenv (expr_type e) e sa` >>
  rename1 `lower_value compile_expr cenv (expr_type e) e sa = (x,sm)` >>
  Cases_on `lower_value compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) sha` >>
  rename1 `lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
    (gas_shadow_expr e) sha = (sx,shm)` >>
  `sx = x /\ gas_shadow_state sm shm` by
    (irule gas_shadow_step >>
     qpat_assum `lower_value _ _ _ e sa = _` (irule_at Any) >>
     qpat_assum `lower_value _ _ _ (gas_shadow_expr e) sha = _` (irule_at Any) >>
     simp[gas_shadow_stmt_lower_value_env]) >>
  qpat_x_assum `sx = x` SUBST_ALL_TAC >>
  Cases_on `compile_method_id_runtime (expr_type e) x fixed sm` >>
  rename1 `compile_method_id_runtime (expr_type e) x fixed sm = (op,b)` >>
  Cases_on `compile_method_id_runtime (expr_type e) x fixed shm` >>
  rename1 `compile_method_id_runtime (expr_type e) x fixed shm = (sop,hb)` >>
  `sop = op /\ gas_shadow_state b hb` by
    (irule gas_shadow_step >>
     qpat_assum `compile_method_id_runtime _ _ _ sm = _` (irule_at Any) >>
     qpat_assum `compile_method_id_runtime _ _ _ shm = _` (irule_at Any) >>
     simp[gasShadowCompileBuiltinHashTheory.gas_shadow_compiles_method_id_runtime]) >>
  qpat_x_assum `sop = op` SUBST_ALL_TAC >>
  qexistsl_tac [`x`,`sm`,`shm`,`op`,`b`,`hb`] >>
  Cases_on `fixed` >>
  gvs[gas_shadow_expr_def, gas_shadow_builtin_def, compile_method_id_singleton_runtime,
      as_stack_val_def, as_ptr_val_def, comp_bind_def, comp_return_def] >>
  rpt conj_tac >>
  simp[Once lower_value_def, compile_method_id_singleton_runtime,
       as_stack_val_def, as_ptr_val_def, comp_bind_def, comp_return_def,
       unwrap_value_def, expr_type_def, is_word_type_def, mk_ptr_def]
QED

(* Match the suffix contract against the selected child in one step, rather
   than letting each premise independently choose a state or ghost pair. *)
Definition method_id_suffix_input_def[local]:
  method_id_suffix_input DF lo d ctx func tops cenv cx env ann e es sa sm sb s0 st0 mid v x s G0 tn0 G tn fixed op <=>
    body_inv tops ctx cenv cx /\ MEM func ctx.ctx_functions /\
    expr_body_pre cenv cx env (Builtin ann MethodId [e]) es /\
    ann = BaseT (BytesT (if fixed then Fixed 4 else Dynamic 4)) /\
    lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
    compile_method_id_runtime (expr_type e) x fixed sm = (op,sb) /\
    create_layout sm sb /\ fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    local_ptrs_reserved cenv sa /\
    (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
    (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
    return_buf_frame d cenv sa s0 /\ storage_trace_domain cx st0 mid.storage_trace /\
    (?xs. !tail. bind (eval_expr cx e) (read_result cx) (es with gas_obs := xs ++ tail) =
      (INL v, mid with gas_obs := tail)) /\
    mid.gas_obs = [] /\ ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      expr_post H ctx func cenv cx e es sa sm s0 mid v x s /\
      expr_store_bound cx (expr_type e) v x s /\ alloca_history func s /\
      s0.vs_alloca_next <= s.vs_alloca_next /\ ghost_inv_at (DF H) lo d cenv cx mid G tn s /\
      ptr_val_ok cx (post_value_type cenv e) v x G tn s /\
      (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e x G s) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
End

Theorem method_id_runtime_sites_scoped_from_suffix:
  (!et x fixed sm op sb. is_bytes_or_string_type et /\
     compile_method_id_runtime et x fixed sm = (op,sb) ==> create_cut_code {} sm sb) ==>
  (!explicit PG DF lo d ctx func tops cenv cx env ann e es sa sm sb s0 st0 mid v x s G0 tn0 G tn fixed op.
    body_inv tops ctx cenv cx /\ MEM func ctx.ctx_functions /\
    expr_body_pre cenv cx env (Builtin ann MethodId [e]) es /\
    ann = BaseT (BytesT (if fixed then Fixed 4 else Dynamic 4)) /\
    lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
    compile_method_id_runtime (expr_type e) x fixed sm = (op,sb) /\
    create_layout sm sb /\ fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    local_ptrs_reserved cenv sa /\
    (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
    (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
    return_buf_frame d cenv sa s0 /\ storage_trace_domain cx st0 mid.storage_trace /\
    (?xs. !tail. bind (eval_expr cx e) (read_result cx) (es with gas_obs := xs ++ tail) =
      (INL v, mid with gas_obs := tail)) /\
    mid.gas_obs = [] /\ ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      expr_post H ctx func cenv cx e es sa sm s0 mid v x s /\
      expr_store_bound cx (expr_type e) v x s /\ alloca_history func s /\
      s0.vs_alloca_next <= s.vs_alloca_next /\ ghost_inv_at (DF H) lo d cenv cx mid G tn s /\
      ptr_val_ok cx (post_value_type cenv e) v x G tn s /\
      (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e x G s) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn) ==>
    ?r z G' tn'.
      builtin_result cx mid.accounts ann MethodId [expr_type e] [v] = INL r /\
      create_operand_full_scope sm sb explicit ctx func s [] (OK z) /\
      ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
      z.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func z /\
      s.vs_alloca_next <= z.vs_alloca_next /\ local_ptrs_reserved cenv sb /\
      return_buf_frame d cenv sb z /\
      (!H. valid_horizon cx st0 H mid.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,G',tn') /\
        expr_post H ctx func cenv cx (Builtin ann MethodId [e]) es sa sb s0 mid r op z /\
        expr_store_bound cx (expr_type (Builtin ann MethodId [e])) r op z /\
        vv_post H ctx func cenv cx (Builtin ann MethodId [e]) es sa sb s0 mid (Value r)
          (if fixed then StackValue ann op else LocatedValue ann (mk_ptr op LocMemory)) z /\
        vv_store_bound cx (expr_type (Builtin ann MethodId [e])) (lowered_value_type cenv (Builtin ann MethodId [e]))
          mid (Value r) (if fixed then StackValue ann op else LocatedValue ann (mk_ptr op LocMemory)) z /\
        s0.vs_alloca_next <= z.vs_alloca_next /\ ghost_inv_at (DF H) lo d cenv cx mid G' tn' z /\
        ptr_val_ok cx (post_value_type cenv (Builtin ann MethodId [e])) r op G' tn' z /\
        ptr_vv_ok cx (post_value_type cenv (Builtin ann MethodId [e])) (Value r)
          (if fixed then StackValue ann op else LocatedValue ann (mk_ptr op LocMemory)) mid G' tn' z /\
        (~fixed ==> ptr_buf_ok cenv (Builtin ann MethodId [e]) op G' z) /\
        ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn')) ==>
  !DF lo d ctx shctx PG tops func shfunc cenv env cx ty ann e es.
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Builtin ann MethodId [e]) es /\ method_id_literal e = NONE /\
    (!st0 sa sm sha shm x s0 G0 tn0.
       create_layout sa sm /\
       expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc)
         cenv cx (expr_type e) e es (st0,sa,sm,sha,shm,x,s0,G0,tn0) ==>
       scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
         (cx_tops cx) cx st0 sa sm (bind (eval_expr cx e) (read_result cx))
         (es,s0,G0,tn0)
         (expr_sim_full_post (DF,lo,d,ctx,func) cenv cx e (es,sa,sm,s0,x,G0,tn0))
         (create_operand_exit_post ctx cx)) ==>
    (!st0 sa sb sha shb op s0 G0 tn0.
       create_layout sa sb /\
       expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc)
         cenv cx ty (Builtin ann MethodId [e]) es (st0,sa,sb,sha,shb,op,s0,G0,tn0) ==>
       scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
         (cx_tops cx) cx st0 sa sb (bind (eval_expr cx (Builtin ann MethodId [e])) (read_result cx))
         (es,s0,G0,tn0)
         (expr_sim_full_post (DF,lo,d,ctx,func) cenv cx (Builtin ann MethodId [e])
           (es,sa,sb,s0,op,G0,tn0)) (create_operand_exit_post ctx cx)) /\
    (!st0 sa sb sha shb vv s0 G0 tn0.
       create_layout sa sb /\
       expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc)
         cenv cx ty (Builtin ann MethodId [e]) es (st0,sa,sb,sha,shb,vv,s0,G0,tn0) ==>
       scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
         (cx_tops cx) cx st0 sa sb (eval_expr cx (Builtin ann MethodId [e])) (es,s0,G0,tn0)
         (\H res ee G tn z.
           create_operand_vv_post (DF,lo,d,ctx,func) cenv cx (Builtin ann MethodId [e])
             (es,sa,sb,s0,vv,G0,tn0) H res ee G tn z /\
           z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts)
         (create_operand_exit_post ctx cx))
Proof
  disch_then (mk_asm "layout") >> disch_then (mk_asm "suffix") >>
  rpt gen_tac >> strip_tac >> drule method_id_child_type >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `fixed = (ann = BaseT (BytesT (Fixed 4)))` >>
  `ann = BaseT (BytesT (if fixed then Fixed 4 else Dynamic 4))` by
    (gvs[Abbr `fixed`] >> metis_tac[]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (irule expr_body_pre_gas_admissible >> qexistsl_tac [`cenv`,`env`] >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `_ \/ _` kall_tac >>
  conj_tac >> rpt gen_tac >> strip_tac >>
  FIRST [qpat_x_assum `expr_sim_full_pre _ _ _ _ _ _ _`
           (strip_assume_tac o REWRITE_RULE[expr_sim_full_pre_def]),
         qpat_x_assum `expr_vv_sim_full_pre _ _ _ _ _ _ _`
           (strip_assume_tac o REWRITE_RULE[expr_vv_sim_full_pre_def])] >>
  mp_tac (Q.SPECL [`sa`,`sha`,`cenv`,`ty`] method_id_runtime_shadow_pair) >>
  qpat_assum `ann = BaseT _` (fn th => REWRITE_TAC [th]) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`x`,`sm`,`shm`,`out`,`b`,`hb`] strip_assume_tac) >>
  gvs[] >>
  rename1 `compile_method_id_runtime (expr_type e) x fixed sm = (op,sb)` >>
  `create_cut_code {} sa sm` by
    (mp_tac (Q.SPECL [`cenv`,`expr_type e`,`e`,`sa`] (cj 2 create_operand_cut_code)) >> simp[]) >>
  `create_cut_code {} sm sb` by
    (asm "layout" irule >> goal_assum (drule_at Any) >> first_assum ACCEPT_TAC) >>
  `cs_extends sa sm /\ cs_extends sm sb` by fs[create_cut_code_def] >>
  `create_layout sa sm /\ create_layout sm sb` by
    (conj_tac >> irule create_layout_subinterval >>
     first_assum (irule_at (Pat `create_layout _ _`)) >> simp[cs_extends_refl]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (drule_all fn_has_code_split >> simp[]) >>
  `cs_extends sha shm /\ cs_extends shm hb` by
    (conj_tac
     >- (qpat_assum `lower_value _ _ _ _ sha = (x,shm)`
           (mp_then Any mp_tac (cj 2 compile_expr_grows)) >> simp[])
     >> `cs_appends (compile_method_id_runtime (expr_type e) x fixed)` by
          simp[cj 5 hash_suffix_appends] >>
     fs[cs_appends_def]) >>
  `fn_has_code sha shm shfunc` by
    (mp_tac (Q.SPECL [`sha`,`shm`,`hb`,`shfunc`] fn_has_code_split) >> simp[]) >>
  qpat_assum `!st0 sa sm sha shm x s0 G0 tn0. create_layout _ _ /\ expr_sim_full_pre _ _ _ _ _ _ _ ==> _`
    (qspecl_then [`st0`,`sa`,`sm`,`sha`,`shm`,`x`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (simp_tac std_ss [expr_sim_full_pre_def] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  FIRST [CHANGED_TAC (pure_once_rewrite_tac[method_id_value_source]),
         pure_once_rewrite_tac[method_id_vv_source]] >>
  irule method_id_bind_child >>
  first_assum (irule_at (Pat `scoped_operand_outcome _ _ _ _ _ _ _ _ _ _`)) >>
  first_assum (irule_at (Pat `body_inv _ _ _ _`)) >>
  simp[create_operand_at_def,storage_trace_frame_def] >>
  rpt gen_tac >> strip_tac >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post H ctx func cenv cx e es sa sm s0 mid v x t /\
    expr_store_bound cx (expr_type e) v x t /\ alloca_history func t /\
    s0.vs_alloca_next <= t.vs_alloca_next /\ ghost_inv_at (DF H) lo d cenv cx mid G tn t /\
    ptr_val_ok cx (post_value_type cenv e) v x G tn t /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e x G t) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> expr_sim_full_post _ _ _ _ _ H _ _ _ _ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     simp_tac std_ss [expr_sim_full_post_def,expr_sim_full_endpoint_def] >>
     strip_tac >>
     qpat_assum `post_value_type cenv e = expr_type e` (fn th => PURE_REWRITE_TAC [GSYM th]) >>
     rpt (conj_tac ORELSE first_assum ACCEPT_TAC)) >>
  `method_id_suffix_input DF lo d ctx func tops cenv cx env
     (BaseT (BytesT (if fixed then Fixed 4 else Dynamic 4)))
     e es sa sm sb s0 st0 mid v x t G0 tn0 G tn fixed op` by
    (pure_rewrite_tac [method_id_suffix_input_def] >>
     rpt (conj_tac ORELSE first_assum ACCEPT_TAC ORELSE REFL_TAC) >>
     qexists_tac `gas_explicit marks s0.vs_gas_readings` >> simp[]) >>
  asm_x "suffix" ((drule_then
    (qspecl_then [`gas_explicit_sites ctx shctx`,`PG`] (qx_choosel_then [`r`,`z`,`G2`,`tn2`] strip_assume_tac)))
    o ONCE_REWRITE_RULE [GSYM method_id_suffix_input_def]) >>
  irule method_id_suffix_normal >>
  first_assum (irule_at (Pat `create_operand_full_scope _ _ _ _ _ _ _ _`)) >>
  simp[] >> qexistsl_tac [`tn2`,`G2`] >>
  qx_gen_tac `H` >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp z` by
    (qpat_assum `expr_post H ctx func cenv cx _ _ _ _ _ mid r op z`
       (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
     drule_then ACCEPT_TAC bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) >>
  Cases_on `fixed` >>
  gvs[expr_sim_full_post_def, expr_sim_full_endpoint_def, create_operand_vv_post_def,
      expr_type_def, is_word_type_def, is_bytestring_type_def, vv_location_def, mk_ptr_def]
QED

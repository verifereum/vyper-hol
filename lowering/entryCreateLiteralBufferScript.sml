(* The literal value and VV cases share the counted buffer run and its ghosts. *)
Theory entryCreateLiteralBuffer
Ancestors
  entryCreateFocusSpec entryCreatePendingScope entryCreateCompletedCut
  bodyFullLiteralNonword literalBufferOpcodeShape exprSimLiteralBuffer
  createSizeBuiltinBodyCode createSizeCutCode exprSimAbiGasBridge
  fragExec fragGasOrigin fragGasOriginPtr gasOutcomeFull gasStorage gasSummary
  gasShadowCompileStmtHelpers gasShadowState exprSimUnwrapProps
  exprSimFullBundleProps exprLoweringProps exprLowering s1PrefixDefs
  loweringPosts bodyPtrDefs exprSimHypsDefs gasShadow context compileEnv
  vyperInterpreter vyperAST vyperState vyperValue vyperStorageTrace
  venomInst venomState venomExecSemantics list pair

(* Use the common administrative sequence rules without a dependency on
   their implementation. The cut half does not ask for a valid horizon. *)
Definition literal_buffer_sequence_laws_def:
  literal_buffer_sequence_laws (ty:'a itself) <=>
    !sa sb ctx func E s.
      fn_has_code sa sb func /\ sb.cs_current_bb = sa.cs_current_bb /\
      sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
      EVERY (\i. i.inst_id IN frag_ids sa sb /\ i.inst_opcode <> INVOKE /\
        i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode /\
        ~MEM i.inst_opcode [CREATE;CREATE2]) (emitted_insts sa sb) /\
      create_operand_at sa s /\ ~s.vs_halted ==>
      (!u. run_inst_seq (emitted_insts sa sb) s = OK u ==>
        create_operand_full_scope sa sb E ctx func s []
          (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))) /\
      (!tops cx st0 (source:evaluation_state -> 'a evaluation_result) es.
        create_operand_cut sa sb E ctx func tops cx st0 source (es,s))
End

Theorem literal_buffer_install[local]:
  compile_bytelike_literal bs (LENGTH bs) sa = (buf,sb) ==>
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_id IN frag_ids sa sb /\ i.inst_opcode <> INVOKE /\
    i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode /\
    ~MEM i.inst_opcode [CREATE;CREATE2]) (emitted_insts sa sb)
Proof
  strip_tac >> drule literal_bytelike_counted_shape >> strip_tac >>
  drule literal_bytelike_emitted_admin >> strip_tac >>
  `create_cut_code {} sa sb` by
    (mp_tac (Q.INST [`exits` |-> `{}`, `a` |-> `sa`, `n` |-> `LENGTH bs`]
       create_bytelike_literal_cut_code) >> simp[]) >>
  `frag_code sa sb = emitted_insts sa sb` by
    fs[same_blocks_def, frag_code_def, emitted_blocks_def] >>
  fs[same_blocks_def, create_cut_code_def, EVERY_MEM, FILTER_EQ_NIL] >>
  metis_tac[]
QED

Theorem scoped_literal_initial_domain[local]:
  ~s.vs_halted /\
  (!tail. source (es with gas_obs := tail) = (res,es with gas_obs := tail)) /\
  (storage_trace_domain cx st0 es.storage_trace ==>
    ?t G' tn'. create_operand_full_scope sa sb E ctx func s [] (OK t) /\
      !H. valid_horizon cx st0 H es.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,E,ctx,func,PG) (s,G,tn) [] (OK t,G',tn') /\
        Q H res (es with gas_obs := []) G' tn' t) ==>
  scoped_operand_outcome (DF,lo,E,ctx,func,PG) tops cx st0 sa sb source (es,s,G,tn) Q R
Proof
  strip_tac >> simp[scoped_operand_outcome_def] >> qexists_tac `[]` >>
  simp[gas_explicit_def] >> Cases_on `storage_trace_domain cx st0 es.storage_trace`
  >- (disj2_tac >> disj1_tac >> res_tac >>
      qexistsl_tac [`res`,`es`,`OK t`,`G'`,`tn'`] >> simp[]) >>
  disj1_tac >> simp[gas_bad_storage_at_def, gas_explicit_def] >>
  conj_tac >- (irule create_operand_focus_scope_caller >> qexists_tac `s` >> simp[]) >>
  qexistsl_tac [`storage_trace_horizon es.storage_trace`,`func`,`PG`,`G`,`tn`,`s`] >>
  simp[gas_origin_ptr_focus_nil]
QED

Theorem literal_buffer_scoped_run[local]:
  literal_buffer_sequence_laws (:'a) /\ literal_buffer_static cenv cx ty ann l bs tv v /\
  expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc)
    cenv cx ty (Literal ann l) es (st0,sa,sb,sha,shb,LocatedValue ann p,s0,G0,tn0) /\
  (!tail. (source:evaluation_state -> 'a evaluation_result) (es with gas_obs := tail) =
    (res,es with gas_obs := tail)) /\
  (!H G' tn' t. literal_buffer_vv_post (DF,lo,d,ctx,func) cenv cx ann l v
      (es,sa,sb,s0,p,G0,tn0) H G' tn' t ==>
    Q H res (es with gas_obs := []) G' tn' t) ==>
  scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
    (cx_tops cx) cx st0 sa sb source (es,s0,G0,tn0) Q R /\
  create_operand_cut sa sb (gas_explicit_sites ctx shctx) ctx func tops cx st0 source (es,s0)
Proof
  simp_tac bool_ss [literal_buffer_static_def,expr_vv_sim_full_pre_def] >> strip_tac >>
  qpat_assum `!sa vv sb. _` drule >> strip_tac >> gvs[] >>
  drule literal_buffer_install >> strip_tac >>
  `create_operand_at sa s0` by simp[create_operand_at_def] >>
  qpat_x_assum `literal_buffer_sequence_laws _`
    (mp_tac o ONCE_REWRITE_RULE [literal_buffer_sequence_laws_def]) >>
  disch_then (qspecl_then [`sa`,`sb`,`ctx`,`func`,`gas_explicit_sites ctx shctx`,`s0`] mp_tac) >>
  simp_tac bool_ss [] >> (impl_tac >- simp[]) >> strip_tac >>
  reverse conj_tac >- simp[] >>
  irule scoped_literal_initial_domain >> simp_tac bool_ss [] >>
  goal_assum (drule_at Any) >> simp[] >> strip_tac >>
  drule_all (SIMP_RULE (srw_ss() ++ ARITH_ss) [] literal_buffer_vv_run) >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shctx`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH sb.cs_current_insts`,`G'`,`tn'`] >>
  conj_tac
  >- (qpat_assum `!u. run_inst_seq _ _ = OK u ==> _`
        (drule_then (assume_tac o REWRITE_RULE [listTheory.LENGTH_APPEND])) >>
      qpat_assum `sb.cs_current_insts = _` (fn th =>
        pure_rewrite_tac [th,listTheory.LENGTH_APPEND]) >> first_assum ACCEPT_TAC) >>
  rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    drule >> simp[]
QED

Theorem literal_buffer_vv_case_at[local]:
  literal_buffer_sequence_laws (:eval_result) /\
  expr_body_pre cenv cx env (Literal ann l) es /\ ~is_word_type ann /\
  expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc)
    cenv cx ty (Literal ann l) es (st0,sa,sb,sha,shb,vv,s0,G0,tn0) ==>
  scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
    (cx_tops cx) cx st0 sa sb (eval_expr cx (Literal ann l)) (es,s0,G0,tn0)
    (\H res ee G tn t.
      create_operand_vv_post (DF,lo,d,ctx,func) cenv cx (Literal ann l)
        (es,sa,sb,s0,vv,G0,tn0) H res ee G tn t /\ create_operand_at sb t)
    (create_operand_exit_post ctx cx) /\
  create_operand_cut sa sb (gas_explicit_sites ctx shctx) ctx func tops cx st0
    (eval_expr cx (Literal ann l)) (es,s0)
Proof
  strip_tac >> drule_all literal_nonword_buffer_static >>
  disch_then (qspec_then `ty` strip_assume_tac) >>
  `?buf. vv = LocatedValue ann (base_ptr buf)` by
    (fs[literal_buffer_static_def,expr_vv_sim_full_pre_def] >>
     qpat_assum `!sa vv sb. _` drule >> metis_tac[]) >> gvs[] >>
  irule literal_buffer_scoped_run >> simp[] >>
  goal_assum (drule_at (Pat `expr_vv_sim_full_pre _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `literal_buffer_static _ _ _ _ _ _ _ _`)) >>
  qexists_tac `INL (Value v)` >>
  fs[literal_buffer_static_def] >> rpt strip_tac >>
  fs[literal_buffer_vv_post_def,create_operand_vv_post_def,create_operand_at_def,
     base_ptr_def,vv_location_def,expr_type_def]
QED

Theorem literal_buffer_read_pre[local]:
  literal_buffer_static cenv cx ty ann l bs tv v /\
  expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc)
    cenv cx ty (Literal ann l) es (st0,sa,sb,sha,shb,op,s0,G0,tn0) ==>
  ?buf. op = (base_ptr buf).ptr_operand /\
    expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc)
      cenv cx ty (Literal ann l) es
      (st0,sa,sb,sha,shb,LocatedValue ann (base_ptr buf),s0,G0,tn0)
Proof
  simp_tac bool_ss [literal_buffer_static_def,expr_sim_full_pre_def,
                    expr_vv_sim_full_pre_def] >> strip_tac >>
  Cases_on `compile_expr cenv ty (Literal ann l) sa` >>
  qpat_assum `!sa vv sb. _` drule >> strip_tac >> gvs[] >>
  `(base_ptr buf).ptr_location = LocMemory` by simp[base_ptr_def] >>
  drule_all lower_value_nonword_memory >> strip_tac >> gvs[] >>
  `?sc. compile_expr (gas_shadow_env T cenv) ty
     (gas_shadow_expr (Literal ann l)) sha = (LocatedValue ann (base_ptr buf),sc)` by
    (mp_tac (Q.INST [`sd` |-> `T`, `e` |-> `Literal ann l`]
       gas_shadow_stmt_compile_expr_env) >>
     pure_rewrite_tac [gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`,`sha`] mp_tac) >>
     Cases_on `compile_expr (gas_shadow_env T cenv) ty
                (gas_shadow_expr (Literal ann l)) sha` >> simp[]) >>
  `sc = shb` by
    (`lower_value compile_expr (gas_shadow_env T cenv) ty
       (gas_shadow_expr (Literal ann l)) sha = ((base_ptr buf).ptr_operand,sc)` by
       (irule lower_value_nonword_memory >> simp[]) >> gvs[]) >>
  qexists_tac `buf` >>
  fs[gasContextTheory.gas_admissible_def,exprSimDefsTheory.expr_vv_res_ok_def] >>
  first_assum ACCEPT_TAC
QED

Theorem literal_buffer_read_post[local]:
  post_value_type cenv (Literal ann l) = ann /\ ~is_word_type ann /\ p.ptr_location = LocMemory /\
  literal_buffer_vv_post (DF,lo,d,ctx,func) cenv cx ann l v
    (es,sa,sb,s0,p,G0,tn0) H G tn t ==>
  expr_sim_full_post (DF,lo,d,ctx,func) cenv cx (Literal ann l)
    (es,sa,sb,s0,p.ptr_operand,G0,tn0) H (INL v) (es with gas_obs := []) G tn t
Proof
  simp[expr_sim_full_post_def,literal_buffer_vv_post_def,expr_sim_full_endpoint_def,
       expr_type_def] >> rpt strip_tac >> gvs[]
  >~ [`expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`] >-
    (drule_all expr_post_of_vv_post_memory >> simp[])
  >~ [`expr_store_bound _ _ _ _ _`] >-
    (gvs[exprSimMemDefsTheory.vv_store_bound_def,exprSimMemDefsTheory.expr_store_bound_def,
         read_result_def,return_def] >> metis_tac[]) >>
  gvs[ptr_vv_ok_def,ptr_val_ok_def,read_result_def,return_def]
QED

Theorem literal_buffer_value_case_at[local]:
  literal_buffer_sequence_laws (:value) /\
  expr_body_pre cenv cx env (Literal ann l) es /\ ~is_word_type ann /\
  expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc)
    cenv cx ty (Literal ann l) es (st0,sa,sb,sha,shb,op,s0,G0,tn0) ==>
  scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
    (cx_tops cx) cx st0 sa sb (bind (eval_expr cx (Literal ann l)) (read_result cx))
    (es,s0,G0,tn0)
    (expr_sim_full_post (DF,lo,d,ctx,func) cenv cx (Literal ann l) (es,sa,sb,s0,op,G0,tn0))
    (create_operand_exit_post ctx cx) /\
  create_operand_cut sa sb (gas_explicit_sites ctx shctx) ctx func tops cx st0
    (bind (eval_expr cx (Literal ann l)) (read_result cx)) (es,s0)
Proof
  strip_tac >> drule_all literal_nonword_buffer_static >>
  disch_then (qspec_then `ty` strip_assume_tac) >>
  drule_all literal_buffer_read_pre >> strip_tac >> gvs[] >>
  irule literal_buffer_scoped_run >> simp[] >>
  goal_assum (drule_at (Pat `expr_vv_sim_full_pre _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `literal_buffer_static _ _ _ _ _ _ _ _`)) >>
  qexists_tac `INL v` >>
  fs[literal_buffer_static_def,bind_def,read_result_def,return_def] >>
  rpt strip_tac >> irule literal_buffer_read_post >> simp[base_ptr_def]
QED

Theorem create_literal_buffer_cases:
  literal_buffer_sequence_laws (:eval_result) /\ literal_buffer_sequence_laws (:value) /\
  expr_body_pre cenv cx env (Literal ann l) es /\ ~is_word_type ann ==>
  expr_vv_sim_scoped (DF,lo,d,ctx,shctx,PG,func,shfunc) cenv cx ty (Literal ann l) es /\
  expr_sim_scoped (DF,lo,d,ctx,shctx,PG,func,shfunc) cenv cx ty (Literal ann l) es /\
  (!st0 sa sb sha shb vv s0 G0 tn0.
    expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc)
      cenv cx ty (Literal ann l) es (st0,sa,sb,sha,shb,vv,s0,G0,tn0) ==>
    create_operand_cut sa sb (gas_explicit_sites ctx shctx) ctx func tops cx st0
      (eval_expr cx (Literal ann l)) (es,s0)) /\
  (!st0 sa sb sha shb op s0 G0 tn0.
    expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc)
      cenv cx ty (Literal ann l) es (st0,sa,sb,sha,shb,op,s0,G0,tn0) ==>
    create_operand_cut sa sb (gas_explicit_sites ctx shctx) ctx func tops cx st0
      (bind (eval_expr cx (Literal ann l)) (read_result cx)) (es,s0))
Proof
  simp[expr_vv_sim_scoped_def,expr_sim_scoped_def,GSYM create_operand_at_def] >>
  strip_tac >> rpt conj_tac >> rpt gen_tac >> strip_tac >>
  FIRST [drule_all literal_buffer_vv_case_at,drule_all literal_buffer_value_case_at] >> simp[]
QED

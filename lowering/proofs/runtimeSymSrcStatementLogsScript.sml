Theory runtimeSymSrcStatementLogs
Ancestors
  runtimeSymSrcInterfaces runtimeSymSrcEmission stmtLowering compileEnv
  context venomInst stackPlanTypes list supportedStmts supportedStmtTraverse
  supportedExprs supportedExprTraverse exprOracleStorageInterfaces

(* External boundary ledger: materialization/store memory are C1.1.3.2;
   topic encoding is C1.1.3.4. Literal contracts keep these dependencies
   visible to the instruction-side discharge join. *)
Theorem runtime_sym_log_save_arg:
  (!t op s v s'. ~is_label_operand op /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_materialize_vv ce t (StackValue t op) s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v) ==>
  !t op es s v s'. ~is_label_operand op /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_log_save_arg ce t op es s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  strip_tac >> rpt gen_tac >> simp[compile_log_save_arg_def] >>
  Cases_on `is_word_type t \/ ~exprs_can_mutate ce es` >>
  simp[comp_return_def] >> metis_tac[]
QED

Theorem runtime_sym_split_log_ops:
  !ops flags. EVERY (\x. ~is_label_operand (FST x)) ops ==>
    EVERY (\x. ~is_label_operand (FST x)) (FST (split_log_ops ops flags)) /\
    EVERY (\x. ~is_label_operand (FST x)) (SND (split_log_ops ops flags))
Proof
  Induct >- (Cases >> simp[split_log_ops_def]) >>
  qx_gen_tac `x` >> PairCases_on `x` >>
  Cases >- simp[split_log_ops_def] >>
  Cases_on `h` >> simp[split_log_ops_def] >>
  pairarg_tac >> gvs[] >> strip_tac >>
  first_x_assum (qspec_then `t` mp_tac) >> simp[]
QED

Theorem runtime_sym_log_topic_ops:
  (!op bs s v s'. ~is_label_operand op /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_encode_log_topic op bs s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v) ==>
  !ops s vs s'. EVERY (\x. ~is_label_operand (FST x)) ops /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_log_topic_ops ops s = (vs,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\
    EVERY (\op. ~is_label_operand op) vs
Proof
  strip_tac >> Induct
  >- (simp[compile_log_topic_ops_def, comp_return_def] >> rpt strip_tac >> gvs[]) >>
  simp[compile_log_topic_ops_def] >>
  rpt gen_tac >> simp[comp_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> rpt strip_tac >> gvs[comp_return_def] >>
  first_assum drule_all >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem runtime_sym_log_store_data:
  (!v d dt st s u s'. ~is_label_operand v /\ ~is_label_operand d /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_store_memory ce v d dt st s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) ==>
  !ops tys buf off s u s'.
    EVERY (\x. ~is_label_operand (FST x)) ops /\ ~is_label_operand buf /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_log_store_data ce ops tys buf off s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')
Proof
  strip_tac >> Induct
  >- (Cases >> simp[compile_log_store_data_def, comp_return_def] >>
      rpt strip_tac >> gvs[] >>
      irule runtime_sym_emit_void >> goal_assum (drule_at Any) >> simp[]) >>
  qx_gen_tac `x` >> PairCases_on `x` >>
  Cases >- (simp[compile_log_store_data_def] >> rpt strip_tac >>
      irule runtime_sym_emit_void >> goal_assum (drule_at Any) >> simp[]) >>
  rpt gen_tac >> simp[compile_log_store_data_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> rpt strip_tac >>
  drule_at (Pat `emit_op _ _ _ = _`) runtime_sym_emit_op >>
  simp[is_label_operand_def] >> strip_tac >>
  first_assum drule_all >> strip_tac >> first_x_assum drule_all >> simp[]
QED

(* lower_value is the open-expression adapter, owned by C1.1.3.6;
   its pointwise premise below is restricted to members of the argument list. *)
Theorem runtime_sym_log_eval_all:
  (!t op s v s'. ~is_label_operand op /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_materialize_vv ce t (StackValue t op) s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v) /\
  (!e s v s'. MEM e args /\ EVERY runtime_sym_inst (state_insts s) /\
    lower_value compile_expr ce (expr_type e) e s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v) ==>
  !s vs s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_log_eval_all ce args s = (vs,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\
    EVERY (\x. ~is_label_operand (FST x)) vs
Proof
  Induct_on `args`
  >- (simp[compile_log_eval_all_def, comp_return_def] >> rpt strip_tac >> gvs[]) >>
  qx_gen_tac `e` >> strip_tac >>
  qpat_x_assum `(_ /\ _) ==> _` mp_tac >>
  (impl_tac >- (conj_tac >- (first_assum ACCEPT_TAC) >>
    rpt gen_tac >> strip_tac >>
    first_x_assum (drule_at (Pat `lower_value _ _ _ _ _ = _`)) >> simp[])) >>
  disch_then (mk_asm "tail") >> rpt gen_tac >>
  simp[Once compile_log_eval_all_def, comp_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[comp_return_def] >>
  `EVERY runtime_sym_inst (state_insts cs') /\ ~is_label_operand v` by
    (first_x_assum irule >> simp[] >> qexists `e` >> simp[] >>
     qexists `s` >> simp[]) >>
  drule runtime_sym_log_save_arg >> disch_then drule_all >> strip_tac >>
  asm "tail" drule_all >> simp[]
QED

(* Guarded lower_value: C1.1.3.6; buffer allocation: C1.1.3.2;
   ABI encoding: C1.1.3.5. No contract for compile_stmt is assumed. *)
Theorem runtime_sym_log_argument:
  (!e t s v s'. runtime_sym_env ce /\ supported_expr tops e /\
    ~supported_expr_exists is_self_code e /\
    EVERY runtime_sym_inst (state_insts s) /\
    lower_value compile_expr ce t e s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v) /\
  runtime_sym_env ce /\ supported_stmt tops bindings (Log id args) /\
  ~supported_stmt_expr_exists is_self_code (Log id args) ==>
  !e s v s'. MEM e args /\ EVERY runtime_sym_inst (state_insts s) /\
    lower_value compile_expr ce (expr_type e) e s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  simp[supported_stmt_def, supported_log_def,
       supported_stmt_expr_exists_def, supported_pure_exprs_every,
       supported_exprs_exists_not_every] >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >>
  qexistsl [`e`, `s`, `expr_type e`] >> simp[] >>
  gvs[EVERY_MEM] >> metis_tac[supported_expr_def]
QED


Theorem runtime_sym_log_execution[local]:
  ce.ce_event_info (nsid_to_string id) = SOME (h,tys,flags) /\
  compile_stmt ce lc ty (Log id args) s = ((),s') ==>
  ?vs s1 ops s2.
    compile_log_eval_all ce args s = (vs,s1) /\
    compile_log_topic_ops (FST (split_log_ops vs flags)) s1 = (ops,s2) /\
    ((NULL (SND (split_log_ops vs flags)) /\
      emit_inst LOG (Lit (n2w (SUC (LENGTH ops))) ::
        (REVERSE ops ++ [Lit (n2w h)]) ++ [Lit 0w; Lit 0w]) [] s2 = ((),s')) \/
     (~NULL (SND (split_log_ops vs flags)) /\
      ?b s3 u s4 ab s5 len s6.
        compile_alloc_buffer
          (MAX 32 (SUM (MAP (type_memory_bytes ce) (log_non_indexed_types flags tys))))
          s2 = (b,s3) /\
        compile_log_store_data ce (SND (split_log_ops vs flags))
          (log_non_indexed_types flags tys) b.buf_operand 0 s3 = (u,s4) /\
        compile_alloc_buffer (MAX 32 (abi_size_bound ce.ce_struct_fields
          (TupleT (log_non_indexed_types flags tys)))) s4 = (ab,s5) /\
        compile_abi_encode_to_buf ab.buf_operand b.buf_operand
          (type_to_abi_enc_info ce.ce_struct_fields ce
            (TupleT (log_non_indexed_types flags tys))) s5 = (len,s6) /\
        emit_inst LOG (Lit (n2w (SUC (LENGTH ops))) ::
          (REVERSE ops ++ [Lit (n2w h)]) ++ [len; ab.buf_operand]) [] s6 = ((),s')))
Proof
  strip_tac >> qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_stmt_def, comp_bind_def, comp_return_def] >>
  Cases_on `compile_log_eval_all ce args s` >> rename1 `_ = (vs,s1)` >>
  Cases_on `compile_log_topic_ops (FST (split_log_ops vs flags)) s1` >>
  rename1 `_ = (ops,s2)` >> simp[] >>
  Cases_on `NULL (SND (split_log_ops vs flags))` >> simp[] >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  Cases_on `compile_alloc_buffer (MAX 32 (SUM (MAP (type_memory_bytes ce)
    (log_non_indexed_types flags tys)))) s2` >> rename1 `_ = (b,s3)` >>
  simp[] >>
  Cases_on `compile_log_store_data ce (SND (split_log_ops vs flags))
    (log_non_indexed_types flags tys) b.buf_operand 0 s3` >>
  rename1 `_ = (u,s4)` >> simp[] >>
  Cases_on `compile_alloc_buffer (MAX 32 (abi_size_bound ce.ce_struct_fields
    (TupleT (log_non_indexed_types flags tys)))) s4` >> rename1 `_ = (ab,s5)` >>
  simp[] >>
  Cases_on `compile_abi_encode_to_buf ab.buf_operand b.buf_operand
    (type_to_abi_enc_info ce.ce_struct_fields ce
      (TupleT (log_non_indexed_types flags tys))) s5` >>
  simp[]
QED

Theorem runtime_sym_log_safe[local]:
  (!s vs s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_log_eval_all ce args s = (vs,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\
    EVERY (\x. ~is_label_operand (FST x)) vs) /\
  (!op bs s v s'. ~is_label_operand op /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_encode_log_topic op bs s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v) /\
  (!v d dt st s u s'. ~is_label_operand v /\ ~is_label_operand d /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_store_memory ce v d dt st s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) /\
  (!sz s b s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_alloc_buffer sz s = (b,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand b.buf_operand) /\
  (!dst src info s v s'. ~is_label_operand dst /\ ~is_label_operand src /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_abi_encode_to_buf dst src info s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v) ==>
  !s s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_stmt ce lc ty (Log id args) s = ((),s') ==>
    EVERY runtime_sym_inst (state_insts s')
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `ce.ce_event_info (nsid_to_string id)`
  >- (qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
      simp[NoAsms, Once compile_stmt_def] >> asm_rewrite_tac[] >> simp[NoAsms] >> strip_tac >>
      irule runtime_sym_emit_inst >> goal_assum (drule_at Any) >> qexists `0` >>
      simp[NoAsms, runtime_sym_ordinary_inst] >> first_assum ACCEPT_TAC) >>
  PairCases_on `x` >> drule_all runtime_sym_log_execution >>
  disch_then (qx_choose_then `vs` (qx_choose_then `s1`
    (qx_choose_then `ops` (qx_choose_then `s2` strip_assume_tac)))) >>
  first_assum (drule_at (Pat `compile_log_eval_all _ _ _ = _`)) >>
  disch_then drule_all >> strip_tac >>
  drule runtime_sym_split_log_ops >> disch_then (qspec_then `x2` strip_assume_tac) >>
  drule runtime_sym_log_topic_ops >> disch_then drule_all >> strip_tac
  >- (irule runtime_sym_emit_inst >> goal_assum (drule_at Any) >> qexists `0` >>
      goal_assum (drule_at Any) >>
      irule runtime_sym_ordinary_inst >>
      simp[NoAsms, EVERY_APPEND, EVERY_MEM, MEM_REVERSE, is_label_operand_def] >>
      qpat_x_assum `EVERY (\op. ~is_label_operand op) ops` mp_tac >>
      simp[NoAsms, EVERY_MEM]) >>
  `EVERY runtime_sym_inst (state_insts s3) /\ ~is_label_operand b.buf_operand` by
    (qpat_assum `!sz s b s'. _ /\ compile_alloc_buffer sz s = (b,s') ==> _` irule >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any)) >>
  drule runtime_sym_log_store_data >> disch_then drule_all >> strip_tac >>
  `EVERY runtime_sym_inst (state_insts s5) /\ ~is_label_operand ab.buf_operand` by
    (qpat_assum `!sz s b s'. _ /\ compile_alloc_buffer sz s = (b,s') ==> _` irule >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any)) >>
  first_assum (drule_at (Pat `compile_abi_encode_to_buf _ _ _ _ = _`)) >>
  disch_then drule_all >> strip_tac >>
  irule runtime_sym_emit_inst >> goal_assum (drule_at Any) >> qexists `0` >>
  goal_assum (drule_at Any) >> irule runtime_sym_ordinary_inst >>
  simp[NoAsms, EVERY_APPEND, EVERY_MEM, MEM_REVERSE, is_label_operand_def] >>
  qpat_x_assum `EVERY (\op. ~is_label_operand op) ops` mp_tac >>
  asm_rewrite_tac[EVERY_MEM] >> simp[NoAsms]
QED

(* The literal lower_value adapter is C1.1.3.6; its callback premise is
   supplied only for members of this Log's argument list. *)
Theorem runtime_sym_stmt_log:
  (!t op s v s'. ~is_label_operand op /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_materialize_vv ce t (StackValue t op) s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v) /\
  (!e t s v s'. runtime_sym_expr_contract tops compile_expr ce t e /\
    runtime_sym_env ce /\ supported_expr tops e /\
    ~supported_expr_exists is_self_code e /\
    EVERY runtime_sym_inst (state_insts s) /\
    lower_value compile_expr ce t e s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v) /\
  (!op bs s v s'. ~is_label_operand op /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_encode_log_topic op bs s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v) /\
  (!v d dt st s u s'. ~is_label_operand v /\ ~is_label_operand d /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_store_memory ce v d dt st s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) /\
  (!sz s b s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_alloc_buffer sz s = (b,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand b.buf_operand) /\
  (!dst src info s v s'. ~is_label_operand dst /\ ~is_label_operand src /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_abi_encode_to_buf dst src info s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v) /\
  (!e. MEM e args ==> runtime_sym_expr_contract tops compile_expr ce (expr_type e) e) ==>
  runtime_sym_stmt_contract tops bindings compile_stmt ce lc ty (Log id args)
Proof
  strip_tac >> pure_rewrite_tac[runtime_sym_stmt_contract_def] >>
  rpt gen_tac >> strip_tac >>
  `!e s v s'. MEM e args /\ EVERY runtime_sym_inst (state_insts s) /\
    lower_value compile_expr ce (expr_type e) e s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v` by
    (rpt gen_tac >> strip_tac >>
     `supported_expr tops e /\ ~supported_expr_exists is_self_code e` by
       (qpat_x_assum `supported_stmt _ _ _` mp_tac >>
        qpat_x_assum `~supported_stmt_expr_exists _ _` mp_tac >>
        simp[NoAsms, supported_stmt_def, supported_log_def,
          supported_stmt_expr_exists_def, supported_pure_exprs_every,
          supported_exprs_exists_not_every, EVERY_MEM] >>
        metis_tac[supported_expr_def]) >>
     `runtime_sym_expr_contract tops compile_expr ce (expr_type e) e` by
       (first_assum irule >> first_assum ACCEPT_TAC) >>
     first_assum (drule_at (Pat `lower_value _ _ _ _ _ = _`)) >>
     disch_then drule_all >> simp[NoAsms]) >>
  drule runtime_sym_log_eval_all >>
  disch_then (qspec_then `args` (mk_asm "eval")) >>
  irule runtime_sym_log_safe >>
  conj_tac >- (first_assum MATCH_ACCEPT_TAC) >>
  conj_tac >- (first_assum MATCH_ACCEPT_TAC) >>
  conj_tac >- (first_assum MATCH_ACCEPT_TAC) >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  conj_tac >- (rpt gen_tac >> strip_tac >> asm "eval" irule >>
    metis_tac[]) >> first_assum MATCH_ACCEPT_TAC
QED

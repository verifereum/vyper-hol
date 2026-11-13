(* Interleaved pointer argument stores, retaining the tuple and its prefix. *)
Theory stmtSimCustomErrorPtrStoreLoop
Ancestors
  stmtSimCustomErrorPtrStoreHead stmtSimCustomErrorPtrUnwrap
  stmtSimCustomErrorStoreLoop typedWordArgsReadyPtr wordArgsPtr
  exprSimPtrTopLevelStorageFrame valueEncoding valueEncodingProps
  valueEncodingProofs bodyPtrDefs venomState finite_map pred_set
  gasSummaryComposePtr stmtFragPtr exprSimWordArgs
  bodySimAugPlaceScopes argsTailPtr

Theorem custom_error_robust_tuple_cons_ptr[local]:
  val_wf tv v /\
  (!m. mem_agree_outside tn mem m ==> val_in_memory tv v a m) /\
  (!i. a <= i /\ i < a+type_memory_size tv ==>
    mem_bytes_at i 1 mem' = mem_bytes_at i 1 mem /\ (i IN tn' ==> i IN tn)) /\
  (!m. mem_agree_outside tn' mem' m ==>
    tuple_in_memory vs tvs (a+type_memory_size tv) m) ==>
  !m. mem_agree_outside tn' mem' m ==>
    tuple_in_memory (v::vs) (tv::tvs) a m
Proof
  strip_tac >>
  `val_footprint tv v <= type_memory_size tv` by simp[exprSimPropsTheory.val_footprint_le] >>
  `!m. mem_agree_outside tn' mem' m ==> val_in_memory tv v a m` by
    (rpt strip_tac >> irule toplevel_robust_exterior_frame >>
     conj_tac >- simp[] >>
     qexistsl [`mem`, `mem'`, `tn`, `tn'`,
               `{i | ~(a <= i /\ i < a+type_memory_size tv)}`] >>
     simp[] >> rpt conj_tac >> rpt strip_tac >> decide_tac) >>
  simp[valueEncodingDefsTheory.val_in_memory_def]
QED

Theorem custom_error_store_args_sim_ptr_conditional:
  (!ce op y typ su st func ctx cx ee s d G tn sr Gref tref sref tv v nb a.
    compile_store_memory ce op (Var y) typ typ su = ((),st) /\
    fn_has_code su st func /\ ~ce.ce_is_ctor /\
    stmt_state_rel ctx func ce cx ee s /\ ghost_inv d ce cx ee G tn s /\
    ghost_kept ce ee sr Gref tref sref G tn /\
    ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
    s.vs_current_bb = su.cs_current_bb /\ s.vs_inst_idx = LENGTH su.cs_current_insts /\
    evaluate_type (get_tenv cx) typ = SOME tv /\ value_has_type tv v /\
    expr_val_rel cx typ v op s /\ ptr_val_ok cx typ v op G tn s /\
    nb = type_memory_bytes ce typ /\ nb = type_memory_size tv /\
    nb < dimword (:256) /\ (is_word_type typ ==> nb = 32) /\
    (~is_word_type typ ==> ?z. op = Var z /\ not_fresh_at su z /\
      (~is_bytestring_type typ /\ nb <> 0 ==> ptr_covers G tn z s nb)) /\
    not_fresh_at su y /\ lookup_var y s = SOME (n2w a) /\
    ptr_covers G tn y s nb /\ a+nb < dimword (:256) /\
    (!n lo sz i. local_region ce ee.scopes s n lo sz /\ lo <= i /\ i < lo+sz ==>
      ~(a <= i /\ i < a+nb)) /\
    (!aid lo sz i. FLOOKUP sref.vs_allocas aid = SOME (lo,sz) /\
      aid < sr.cs_next_id /\ lo <= i /\ i < lo+sz ==> ~(a <= i /\ i < a+nb)) /\
    (!n lo sz i. local_region ce ee.scopes sref n lo sz /\ lo <= i /\ i < lo+sz ==>
      ~(a <= i /\ i < a+nb)) /\
    (!z. not_fresh_at sr z ==> not_fresh_at su z) /\
    (!name entry z sz. lookup_scopes name ee.scopes = SOME entry /\
      FLOOKUP ce.ce_vars name = SOME (PtrVar (Var z) sz) ==> not_fresh_at su z) /\
    (!z sz. ce.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at su z) /\
    (!z sz. ce.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at su z) /\
    (!z. ce.ce_imm_alloca = SOME (Var z) ==> not_fresh_at su z) ==>
    !D PG. ?Gf tf t.
      gas_path_ptr D 0 ctx func PG G tn s 0 Gf tf (OK t) /\
      t.vs_current_bb = st.cs_current_bb /\ t.vs_inst_idx = LENGTH st.cs_current_insts /\
      ~t.vs_halted /\ stmt_state_rel ctx func ce cx ee t /\
      ghost_inv d ce cx ee Gf tf t /\ ghost_kept ce ee sr Gref tref sref Gf tf /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                vs_inst_idx := s.vs_inst_idx|>) = s /\
      tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
      (!z. not_fresh_at su z ==> lookup_var z t = lookup_var z s /\
        FLOOKUP Gf z = FLOOKUP G z /\ op_taint tf (Var z) = op_taint tn (Var z)) /\
      (!i. ~(a <= i /\ i < a+nb) ==>
        mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
        (i IN tf.t_mem <=> i IN tn.t_mem)) /\
      (!m. mem_agree_outside tf.t_mem t.vs_memory m ==> val_in_memory tv v a m)) ==>
  !args ce cx env off sa sb es tvs func inst x b asz s0 ctx tys tops d PG G tn.
  tys = MAP expr_type args /\
  compile_custom_error_store_args ce args tys (Var x) off sa = ((),sb) /\
  OPT_MMAP (evaluate_type (get_tenv cx)) (MAP expr_type args) = SOME tvs /\
  body_inv tops ctx ce cx /\ ~ce.ce_is_ctor /\ ~ctx_has_dalloca ctx /\
  expr_sim_inv ce cx env es /\
  (!e ee. MEM e args /\ expr_sim_inv ce cx env ee ==> expr_body_pre ce cx env e ee) /\
  body_exprs_ptr_ok cx args /\ EVERY (supported_pure_expr tops) args /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ MEM inst (fn_insts func) /\
  inst.inst_outputs = [x] /\ inst.inst_id < sa.cs_next_id /\
  (!ee. expr_sim_inv ce cx env ee ==> not_local_ptr ce ee.scopes x) /\
  not_fresh_at sa x /\ lookup_var x s0 = SOME (n2w b) /\
  FLOOKUP s0.vs_allocas inst.inst_id = SOME (b,asz) /\ ptr_covers G tn x s0 asz /\
  off + type_memory_size_list tvs <= asz /\ b+asz < dimword (:256) /\
  stmt_state_rel ctx func ce cx es s0 /\ ghost_inv d ce cx es G tn s0 /\
  (!n lo sz i. local_region ce es.scopes s0 n lo sz /\ lo <= i /\ i < lo+sz ==>
    ~(b <= i /\ i < b+asz)) /\
  (!z sz. ce.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!z sz. ce.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!z. ce.ce_imm_alloca = SOME (Var z) ==> not_fresh_at sa z) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_ptr (cx_dead cx) tops (ctx,func) PG (eval_exprs cx args) (es,s0,G,tn)
    (\res ee Gf tf r. ?vs.
      res = INL vs /\ r.vs_current_bb = sb.cs_current_bb /\
      r.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~r.vs_halted /\
      expr_sim_inv ce cx env ee /\ stmt_state_rel ctx func ce cx ee r /\
      ghost_inv d ce cx ee Gf tf r /\
      ptr_covers Gf tf x r asz /\ lookup_var x r = SOME (n2w b) /\
      FLOOKUP r.vs_allocas inst.inst_id = SOME (b,asz) /\
      (!mem. mem_agree_outside tf.t_mem r.vs_memory mem ==>
        tuple_in_memory vs tvs (b+off) mem) /\
      tuple_in_memory vs tvs (b+off) r.vs_memory /\
      (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
        lookup_var z r = SOME w) /\
      (!z. not_fresh_at sa z ==> FLOOKUP Gf z = FLOOKUP G z /\
        op_taint tf (Var z) = op_taint tn (Var z)) /\
      (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==> FLOOKUP r.vs_allocas aid = SOME entry) /\
      (!i. b <= i /\ i < b+asz /\ ~(b+off <= i /\ i < b+off+type_memory_size_list tvs) ==>
        mem_bytes_at i 1 r.vs_memory = mem_bytes_at i 1 s0.vs_memory /\
        (i IN tf.t_mem ==> i IN tn.t_mem)))
    (\res ee gt exit. ?exc. res = INR exc /\
      expr_exit (INR exc : eval_result + exception) exit)
Proof
  disch_then (mk_asm "store") >> Induct_on `args`
  >- suspend "nil"
  >> suspend "cons"
QED

Resume custom_error_store_args_sim_ptr_conditional[nil]:
  asm_x "store" kall_tac >> TRY (asm_x "tail" kall_tac) >> rpt gen_tac >>
  simp[stmtLoweringTheory.compile_custom_error_store_args_def,
       compileEnvTheory.comp_return_def] >> strip_tac >> gvs[] >>
  rewrite_tac[fragGasPathPtrTheory.gas_outcome_ptr_def] >>
  qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_ptr_at_marked] >>
  qexistsl_tac [`INL []`, `es`, `G`, `tn`, `OK s0`] >>
  conj_tac >- (irule eval_exprs_nil_marked_ptr >> simp[]) >>
  simp[valueEncodingDefsTheory.val_in_memory_def,
       stmt_state_rel_gas_obs, ghost_inv_gas_obs] >>
  metis_tac[]
QED

Resume custom_error_store_args_sim_ptr_conditional[cons]:
  qpat_x_assum `!ce cx env off sa sb es tvs func inst x b asz s0 ctx tys tops d PG G tn. _`
    (mk_asm "tail") >>
  rpt gen_tac >> strip_tac >> qpat_x_assum `tys = _` SUBST_ALL_TAC >>
  Cases_on `compile_expr ce (expr_type h) h sa` >>
  rename1 `compile_expr ce (expr_type h) h sa = (vv,sm)` >>
  Cases_on `(if off = 0 then comp_return (Var x)
    else emit_op ADD [Var x; Lit (n2w off)]) sm` >>
  rename1 `(if off = 0 then comp_return (Var x)
    else emit_op ADD [Var x; Lit (n2w off)]) sm = (dst,sn)` >>
  Cases_on `unwrap_value ce vv sn` >>
  rename1 `unwrap_value ce vv sn = (op,su)` >>
  Cases_on `compile_store_memory ce op dst (expr_type h) (lowered_value_type ce h) su` >>
  rename1 `compile_store_memory ce op dst (expr_type h) (lowered_value_type ce h) su = (unit,st)` >>
  Cases_on `unit` >>
  qpat_x_assum `compile_custom_error_store_args _ (_::_) _ _ _ _ = _` mp_tac >>
  simp[Once stmtLoweringTheory.compile_custom_error_store_args_def,
       compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def] >>
  strip_tac >> suspend "step"
QED

Resume custom_error_store_args_sim_ptr_conditional[step]:
  `ci_mono sa sm /\ ci_mono sn su /\ ci_mono su st /\ ci_mono st sb` by
    (asm_x "store" kall_tac >> TRY (asm_x "tail" kall_tac) >>
     metis_tac[cj 1 exprLoweringPropsTheory.compile_expr_ci_mono,
       exprLoweringPropsTheory.ci_mono_unwrap_value,
       exprLoweringPropsTheory.ci_mono_compile_store_memory,
       cj 1 stmtLoweringMonoTheory.ci_mono_custom_error, pairTheory.SND]) >>
  `ci_mono sm sn` by
    (asm_x "store" kall_tac >> TRY (asm_x "tail" kall_tac) >> Cases_on `off = 0` >>
     gvs[compileEnvTheory.comp_return_def] >>
     metis_tac[exprLoweringPropsTheory.ci_mono_emit_op, pairTheory.SND,
       exprLoweringPropsTheory.ci_mono_refl]) >>
  `fn_has_code sa sm func /\ fn_has_code st sb func /\ fn_has_code sa st func` by
    (asm_x "store" kall_tac >> TRY (asm_x "tail" kall_tac) >>
     metis_tac[fragExecTheory.fn_has_code_split, exprLoweringPropsTheory.ci_mono_def,
       compileEnvTheory.cs_extends_trans]) >>
  `expr_body_pre ce cx env h es` by
    (asm_x "store" kall_tac >> TRY (asm_x "tail" kall_tac) >> metis_tac[listTheory.MEM]) >>
  `expr_vv_sim_ptr d ctx PG func ce cx (expr_type h) h es` by
    (asm_x "store" kall_tac >> TRY (asm_x "tail" kall_tac) >>
     gvs[bodyPtrPredsTheory.body_exprs_ptr_ok_def] >>
     qpat_x_assum `body_expr_ptr_ok cx h` mp_tac >>
     simp[Once bodyPtrPredsTheory.body_expr_ptr_ok_def] >> metis_tac[]) >>
  `gas_admissible (eval_expr cx h) expr_vv_res_ok es` by
    (asm_x "store" kall_tac >> TRY (asm_x "tail" kall_tac) >>
     metis_tac[exprSimHypsTheory.expr_body_pre_vv_gas_admissible]) >>
  qpat_x_assum `expr_vv_sim_ptr _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[bodyPtrDefsTheory.expr_vv_sim_ptr_def] >>
  disch_then (qspecl_then [`sa`,`sm`,`vv`,`s0`,`G`,`tn`] mp_tac) >>
  impl_tac >- simp[] >>
  strip_tac >> suspend "expression"
QED

Resume custom_error_store_args_sim_ptr_conditional[expression]:
  `cx_tops cx = tops` by
    (irule gasContextTheory.cx_tops_module >> fs[bodySimTheory.body_inv_def]) >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [fragGasPathPtrTheory.gas_outcome_ptr_def])
  >- (qpat_x_assum `gas_summary_ptr_at _ _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_ptr_at_marked])
      >- (gvs[] >> suspend "normal")
      >> suspend "exit") >>
  suspend "exempt"
QED

Resume custom_error_store_args_sim_ptr_conditional[normal]:
  rename1 `evaluate_type (get_tenv cx) (expr_type h) = SOME ht` >>
  rename1 `OPT_MMAP (evaluate_type (get_tenv cx)) (MAP expr_type args) = SOME tt` >>
  `expr_body_pre ce cx env h es` by
    (asm_x "store" kall_tac >> TRY (asm_x "tail" kall_tac) >> metis_tac[listTheory.MEM]) >>
  `type_memory_bytes ce (expr_type h) = type_memory_size ht` by
    (asm_x "store" kall_tac >> TRY (asm_x "tail" kall_tac) >>
     metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size,
       exprSimHypsDefsTheory.expr_body_pre_def]) >>
  drule exprSimAggregateSourceTheory.vv_post_materialises >> strip_tac >>
  `gas_marked_exec F (ctx,func) (eval_expr cx h) (es,s0) marks
    (INL tv) es_end (OK t)` by
    (irule gas_marked_exec_ptr_exec >> goal_assum (drule_at Any)) >>
  drule_all exprSimAggregateBodyCountedTheory.aggregate_body_marked_read_replay >>
  strip_tac >>
  drule exprSimAggregateBodyCountedTheory.aggregate_body_marked_replay >> strip_tac >>
  `value_has_type ht v /\ val_wf ht v` by
    (asm_x "store" kall_tac >> TRY (asm_x "tail" kall_tac) >>
     metis_tac[exprSimAggregateSourceTheory.aggregate_materialised_child_typed,
       exprSimAggregateSourceTheory.aggregate_materialised_child_wf]) >>
  `int_calls_expr h = []` by
    (asm_x "store" kall_tac >> TRY (asm_x "tail" kall_tac) >>
     metis_tac[bodyExprPreFactsTheory.supported_pure_int_calls]) >>
  `post_value_type ce h = expr_type h` by simp[] >>
  qspecl_then [`ce`,`h`,`env`] mp_tac
    exprSimAggregateLoopsTheory.aggregate_elem_lowered_type >>
  (impl_tac >- (asm_x "store" kall_tac >> TRY (asm_x "tail" kall_tac) >>
    fs[exprSimHypsDefsTheory.expr_body_pre_def])) >> disch_tac >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by
    (asm_x "store" kall_tac >> TRY (asm_x "tail" kall_tac) >>
     fs[exprLoweringPropsTheory.ci_mono_def]) >>
  `local_ptrs_reserved ce sm` by
    (asm_x "store" kall_tac >> TRY (asm_x "tail" kall_tac) >>
     metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var]) >>
  `!z. vv_operand vv = Var z ==> not_fresh_at sm z` by
    (asm_x "store" kall_tac >> TRY (asm_x "tail" kall_tac) >>
     metis_tac[cj 1 exprOperandVarTheory.compiler_compile_var]) >>
  `fn_has_code sm sn func /\ fn_has_code sn su func` by
    (asm_x "store" kall_tac >> TRY (asm_x "tail" kall_tac) >>
     metis_tac[fragExecTheory.fn_has_code_split, exprLoweringPropsTheory.ci_mono_def,
       compileEnvTheory.cs_extends_trans]) >>
  `expr_sim_inv ce cx env (es_end with gas_obs := [])` by
    (asm_x "store" kall_tac >> TRY (asm_x "tail" kall_tac) >> metis_tac[exprSimSourceTheory.expr_body_pre_eval]) >>
  `es_end.scopes = es.scopes` by
    (asm_x "store" kall_tac >> TRY (asm_x "tail" kall_tac) >>
     qspecl_then [`cx_tops cx`,`h`] mp_tac
       (cj 1 bodySimAugPlaceScopesTheory.aug_place_pure_scopes_mutual) >>
     simp[] >> disch_then (qspecl_then [`cx`,
       `es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
       `INL tv`, `es_end with gas_obs := []`] mp_tac) >> simp[]) >>
  `~t.vs_halted` by
    (asm_x "store" kall_tac >> TRY (asm_x "tail" kall_tac) >>
     metis_tac[gas_marked_exec_ptr_def, fragGasSeqPtrTheory.gas_path_ptr_ok_not_halted]) >>
  `lookup_var x t = SOME (n2w b) /\
   FLOOKUP t.vs_allocas inst.inst_id = SOME (b,asz) /\
   stmt_state_rel ctx func ce cx (es_end with gas_obs := []) t` by
    (asm_x "store" kall_tac >> TRY (asm_x "tail" kall_tac) >> fs[loweringPostsTheory.vv_post_def]) >>
  `not_fresh_at sm x` by
    (asm_x "store" kall_tac >> TRY (asm_x "tail" kall_tac) >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `FLOOKUP G' x = FLOOKUP G x /\
   op_taint tn' (Var x) = op_taint tn (Var x)` by
    (asm_x "store" kall_tac >> TRY (asm_x "tail" kall_tac) >> fs[bodyPtrDefsTheory.ghost_kept_def]) >>
  `ptr_covers G' tn' x t asz` by
    (asm_x "store" kall_tac >> TRY (asm_x "tail" kall_tac) >>
     qpat_x_assum `ptr_covers G tn x s0 asz` mp_tac >>
     simp[bodyPtrDefsTheory.ptr_covers_def] >> metis_tac[]) >>
  `off + type_memory_size ht <= asz /\
   type_memory_size ht < dimword (:256)` by
    (fs[valueEncodingTheory.type_memory_size_def] >> decide_tac) >>
  `(!z sz. ce.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z) /\
   (!z sz. ce.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z)` by
    (asm_x "store" kall_tac >> TRY (asm_x "tail" kall_tac) >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  mp_tac (Q.INST [`e` |-> `h`, `s` |-> `t`, `sb` |-> `su`,
    `nb` |-> `type_memory_size ht`, `ee` |-> `es_end with gas_obs := []`,
    `raw` |-> `tv`, `G` |-> `G'`, `tn` |-> `tn'`]
    (Q.INST [`tv` |-> `ht`] custom_error_unwrap_path_ptr)) >>
  (impl_tac >- simp[]) >>
  disch_then (qspecl_then [`cx_dead cx`,`PG`] strip_assume_tac) >>
  suspend "store_head"
QED

Resume custom_error_store_args_sim_ptr_conditional[store_head]:
  rename1 `gas_path_ptr (cx_dead cx) 0 ctx func PG G' tn' t 0 G1 tn1 (OK u)` >>
  qpat_x_assum `dst = Var y` SUBST_ALL_TAC >>
  `ci_mono sa sn /\ ci_mono sa su /\ ci_mono sa st` by
    (asm_x "store" kall_tac >> TRY (asm_x "tail" kall_tac) >>
     metis_tac[exprSimAggregateBodyFramesTheory.aggregate_body_ci_mono_trans]) >>
  `fn_has_code su st func` by
    (asm_x "store" kall_tac >> TRY (asm_x "tail" kall_tac) >>
     metis_tac[fragExecTheory.fn_has_code_split, exprLoweringPropsTheory.ci_mono_def]) >>
  `local_ptrs_reserved ce su` by
    (asm_x "store" kall_tac >> TRY (asm_x "tail" kall_tac) >>
     metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var,
       exprLoweringPropsTheory.ci_mono_def]) >>
  `!z. not_fresh_at sa z ==> not_fresh_at su z` by
    (asm_x "store" kall_tac >> TRY (asm_x "tail" kall_tac) >>
     fs[exprLoweringPropsTheory.ci_mono_def] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `not_fresh_at sn y` by
    (asm_x "store" kall_tac >> TRY (asm_x "tail" kall_tac) >>
     Cases_on `off = 0`
     >- (gvs[compileEnvTheory.comp_return_def] >> metis_tac[]) >>
     gvs[] >> drule emitHelperPropsTheory.emitted_insts_emit_op >> strip_tac >>
     gvs[loweringStateRelDefsTheory.not_fresh_at_def, ASCIInumbersTheory.toString_11]) >>
  `not_fresh_at su y` by
    (asm_x "store" kall_tac >> TRY (asm_x "tail" kall_tac) >>
     fs[exprLoweringPropsTheory.ci_mono_def] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `!z. op = Var z ==> not_fresh_at su z` by
    (asm_x "store" kall_tac >> TRY (asm_x "tail" kall_tac) >>
     fs[exprLoweringPropsTheory.ci_mono_def] >>
     metis_tac[exprSimAggregateChildrenTheory.aggregate_child_unwrap_var]) >>
  `stmt_state_rel ctx func ce cx (es_end with gas_obs := []) u /\
   expr_val_rel cx (expr_type h) v op u /\
   lookup_var x u = SOME (n2w b) /\
   FLOOKUP u.vs_allocas inst.inst_id = SOME (b,asz)` by
    (asm_x "store" kall_tac >> TRY (asm_x "tail" kall_tac) >>
     fs[loweringPostsTheory.expr_post_def] >> metis_tac[]) >>
  `ptr_covers G1 tn1 x u asz` by
    (asm_x "store" kall_tac >> TRY (asm_x "tail" kall_tac) >>
     qpat_x_assum `ptr_covers G' tn' x t asz` mp_tac >>
     simp[bodyPtrDefsTheory.ptr_covers_def] >> metis_tac[]) >>
  `!n lo sz i. local_region ce (es_end with gas_obs := []).scopes u n lo sz /\
    lo <= i /\ i < lo+sz ==> ~(b <= i /\ i < b+asz)` by
    (match_mp_tac (Q.SPECL [`ctx`,`func`,`ce`,`cx`,
       `es_end with gas_obs := []`,`u`,`inst`,`x`,`b`,`asz`,`asz`]
       annAssignPtrDestinationFrameTheory.annassign_alloca_window_excludes_locals_ptr) >>
     simp[] >> metis_tac[]) >>
  `compile_store_memory ce op (Var y) (expr_type h) (expr_type h) su = ((),st)` by
    (asm_x "store" kall_tac >> TRY (asm_x "tail" kall_tac) >>
     `well_typed_expr env h` by fs[exprSimHypsDefsTheory.expr_body_pre_def] >>
     metis_tac[bodyMemAggregateStoreTheory.aggregate_mem_store_lowered_elem]) >>
  suspend "store_run"
QED

Resume custom_error_store_args_sim_ptr_conditional[store_run]:
  `?G2 tn2 q.
    gas_path_ptr (cx_dead cx) 0 ctx func PG G1 tn1 u 0 G2 tn2 (OK q) /\
    q.vs_current_bb = st.cs_current_bb /\
    q.vs_inst_idx = LENGTH st.cs_current_insts /\ ~q.vs_halted /\
    stmt_state_rel ctx func ce cx (es_end with gas_obs := []) q /\
    ghost_inv d ce cx (es_end with gas_obs := []) G2 tn2 q /\
    (q with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
              vs_inst_idx := u.vs_inst_idx|>) = u /\
    (!z. not_fresh_at su z ==> lookup_var z q = lookup_var z u /\
      FLOOKUP G2 z = FLOOKUP G1 z /\
      op_taint tn2 (Var z) = op_taint tn1 (Var z)) /\
    (!i. ~(b+off <= i /\ i < b+off+type_memory_size ht) ==>
      mem_bytes_at i 1 q.vs_memory = mem_bytes_at i 1 u.vs_memory /\
      (i IN tn2.t_mem <=> i IN tn1.t_mem)) /\
    (!m. mem_agree_outside tn2.t_mem q.vs_memory m ==>
      val_in_memory ht v (b+off) m)` by
    (Cases_on `type_memory_size ht = 0`
     >- suspend "zero_store"
     >> suspend "nonzero_store") >>
  pop_assum strip_assume_tac >> suspend "tail_setup"
QED

Resume custom_error_store_args_sim_ptr_conditional[zero_store]:
  `~is_word_type (expr_type h)` by
    (asm_x "store" kall_tac >> TRY (asm_x "tail" kall_tac) >>
     strip_tac >> `type_memory_size ht = 32` by
       metis_tac[stmtSimReturnTheory.word_type_sizes] >> decide_tac) >>
  `~is_bytestring_type (expr_type h)` by
    (asm_x "store" kall_tac >> TRY (asm_x "tail" kall_tac) >>
     qspecl_then [`ce`,`expr_type h`] mp_tac
       valueCopyBytesTheory.bytestring_memory_bytes_positive >> simp[]) >>
  `st = su` by
    gvs[contextTheory.compile_store_memory_def, contextPropsTheory.compile_copy_memory_zero] >>
  asm_x "store" kall_tac >> TRY (asm_x "tail" kall_tac) >>
  qexistsl_tac [`G1`,`tn1`,`u`] >> simp[] >>
  conj_tac >- metis_tac[cj 1 fragGasPathPtrTheory.gas_path_ptr_rules] >>
  metis_tac[externalReturnBufferlessNormalizeTheory.return_zero_wf_memory]
QED

Resume custom_error_store_args_sim_ptr_conditional[nonzero_store]:
  `is_word_type (expr_type h) ==> type_memory_size ht = 32` by
    (asm_x "store" kall_tac >> TRY (asm_x "tail" kall_tac) >>
     metis_tac[stmtSimReturnTheory.word_type_sizes]) >>
  `~is_word_type (expr_type h) ==> ?z. op = Var z /\ not_fresh_at su z /\
    (~is_bytestring_type (expr_type h) /\ type_memory_size ht <> 0 ==>
       ptr_covers G1 tn1 z u (type_memory_size ht))` by
    (asm_x "store" kall_tac >> TRY (asm_x "tail" kall_tac) >> strip_tac >>
     `?w. eval_operand op u = SOME w` by fs[loweringPostsTheory.expr_val_rel_def] >>
     Cases_on `is_bytestring_type (expr_type h)`
     >- (`val_footprint ht v <> 0` by
           (drule_all valueCopyBytesTheory.bytestring_type_value >> strip_tac >>
            gvs[] >> Cases_on `v` >>
            simp[loweringPostsTheory.val_footprint_def, valueEncodingTheory.type_memory_size_def]) >>
         fs[bodyPtrDefsTheory.ptr_val_ok_def, bodyPtrDefsTheory.ptr_mem_ok_def] >>
         metis_tac[]) >>
     `lowered_value_type ce h = expr_type h` by metis_tac[] >>
     `ptr_buf_ok ce h op G1 u` by metis_tac[] >>
     qpat_x_assum `ptr_buf_ok ce h op G1 u`
       (mp_tac o REWRITE_RULE [bodyPtrDefsTheory.ptr_buf_ok_def]) >>
     disch_then (qspec_then `w` mp_tac) >> simp[] >> strip_tac >>
     rename1 `op = Var src` >>
     rename1 `FLOOKUP G1 src = SOME (source_base,source_capacity)` >>
     `lookup_var src u = SOME w` by metis_tac[venomStateTheory.eval_operand_def] >>
     `op_taint tn1 (Var src) = {}` by
       (qpat_x_assum `ptr_val_ok _ _ _ _ G1 tn1 u` mp_tac >>
        simp[bodyPtrDefsTheory.ptr_val_ok_def] >> metis_tac[]) >>
     qexists_tac `src` >> conj_tac >- simp[] >> conj_tac >- metis_tac[] >>
     simp[] >> rewrite_tac[bodyPtrDefsTheory.ptr_covers_def] >>
     simp[] >> qexistsl_tac [`w`,`source_base`,`source_capacity`] >> simp[]) >>
  `ptr_val_ok cx (expr_type h) v op G1 tn1 u` by
    (qpat_x_assum `ptr_val_ok _ _ _ _ G1 tn1 u` mp_tac >> simp[]) >>
  `alloca_inv u` by fs[exprLoweringPropsTheory.stmt_state_rel_def] >>
  `!aid lo sz i. FLOOKUP u.vs_allocas aid = SOME (lo,sz) /\
    aid < inst.inst_id /\ lo <= i /\ i < lo+sz ==>
    ~(b <= i /\ i < b+asz)` by
    (qspecl_then [`u`,`u`,`sa with cs_next_id := inst.inst_id`,
       `inst`,`b`,`asz`,`asz`] mp_tac
       annAssignPtrDestinationFrameTheory.annassign_alloca_window_excludes_older_ptr >>
     simp[] >> strip_tac >> rpt gen_tac >> strip_tac >>
     qpat_x_assum
       `!aid off' nsz i. FLOOKUP u.vs_allocas aid = SOME (off',nsz) /\ _ ==> _`
       (qspecl_then [`aid`,`lo`,`sz`,`i`] mp_tac) >>
     simp[arithmeticTheory.ADD_COMM]) >>
  `!i. ~(b <= i /\ i < b+asz) ==>
    ~(b+off <= i /\ i < b+off+type_memory_size ht)` by
    (fs[valueEncodingTheory.type_memory_size_def] >> decide_tac) >>
  asm_x "store" (qspecl_then [`ce`,`op`,`y`,`expr_type h`,`su`,`st`,
    `func`,`ctx`,`cx`,`es_end with gas_obs := []`,`u`,`d`,`G1`,`tn1`,
    `sa with cs_next_id := inst.inst_id`,`G1`,`tn1`,`u`,`ht`,`v`,
    `type_memory_size ht`,`b+off`] mp_tac) >>
  (impl_tac >- (TRY (asm_x "tail" kall_tac) >>
    fs[wordArgsPtrTheory.ghost_kept_refl] >>
    rpt conj_tac >> rpt strip_tac >>
    FIRST [decide_tac, first_x_assum drule_all >> decide_tac,
      fs[loweringStateRelDefsTheory.not_fresh_at_def,
         loweringStateRelDefsTheory.local_ptrs_reserved_def] >> metis_tac[]])) >>
  disch_then (qspecl_then [`cx_dead cx`,`PG`] strip_assume_tac) >>
  rename1 `gas_path_ptr (cx_dead cx) 0 ctx func PG G1 tn1 u 0 H tm (OK z)` >>
  qexistsl_tac [`H`,`tm`,`z`] >> simp[]
QED

Resume custom_error_store_args_sim_ptr_conditional[tail_setup]:
  `q.vs_allocas = u.vs_allocas` by
    fs[venomStateTheory.venom_state_component_equality] >>
  `lookup_var x q = SOME (n2w b) /\
   FLOOKUP q.vs_allocas inst.inst_id = SOME (b,asz) /\
   ptr_covers G2 tn2 x q asz` by
    (asm_x "store" kall_tac >> TRY (asm_x "tail" kall_tac) >>
     `not_fresh_at su x` by metis_tac[] >>
     qpat_x_assum `!z. not_fresh_at su z ==> _`
       (qspec_then `x` mp_tac) >> simp[] >> strip_tac >>
     gvs[bodyPtrDefsTheory.ptr_covers_def] >> metis_tac[]) >>
  `sa.cs_next_var <= st.cs_next_var /\ sa.cs_next_id <= st.cs_next_id` by
    (asm_x "store" kall_tac >> TRY (asm_x "tail" kall_tac) >>
     fs[exprLoweringPropsTheory.ci_mono_def]) >>
  `local_ptrs_reserved ce st` by
    (asm_x "store" kall_tac >> TRY (asm_x "tail" kall_tac) >>
     metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var]) >>
  `not_fresh_at st x /\ inst.inst_id < st.cs_next_id` by
    (asm_x "store" kall_tac >> TRY (asm_x "tail" kall_tac) >>
     metis_tac[freshWritesTheory.not_fresh_at_mono, arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  `!n lo sz i. local_region ce (es_end with gas_obs := []).scopes q n lo sz /\
    lo <= i /\ i < lo+sz ==> ~(b <= i /\ i < b+asz)` by
    (match_mp_tac (Q.SPECL [`ctx`,`func`,`ce`,`cx`,
       `es_end with gas_obs := []`,`q`,`inst`,`x`,`b`,`asz`,`asz`]
       annAssignPtrDestinationFrameTheory.annassign_alloca_window_excludes_locals_ptr) >>
     simp[] >> metis_tac[]) >>
  `body_exprs_ptr_ok cx args` by
    (asm_x "store" kall_tac >> TRY (asm_x "tail" kall_tac) >> metis_tac[wordArgsPtrTheory.body_exprs_ptr_ok_tail]) >>
  asm_x "tail" (qspecl_then [`ce`,`cx`,`env`,`off+type_memory_size ht`,
    `st`,`sb`,`es_end with gas_obs := []`,`tt`,`func`,`inst`,`x`,`b`,`asz`,`q`,
    `ctx`,`MAP expr_type args`,`cx_tops cx`,`d`,`PG`,`G2`,`tn2`] mp_tac) >>
  (impl_tac >- (asm_x "store" kall_tac >> fs[] >>
    rpt conj_tac >> rpt strip_tac >>
    fs[valueEncodingTheory.type_memory_size_def] >> TRY decide_tac >>
    metis_tac[freshWritesTheory.not_fresh_at_mono])) >>
  strip_tac >> suspend "tail_outcome"
QED

Resume custom_error_store_args_sim_ptr_conditional[tail_outcome]:
  `alloca_inv s0 /\ local_ptrs_rel func ce es.scopes s0 /\
   not_local_ptr ce es.scopes x` by
    (asm_x "store" kall_tac >> TRY (asm_x "tail" kall_tac) >>
     fs[exprLoweringPropsTheory.stmt_state_rel_def,
        loweringStateRelDefsTheory.state_rel_def] >> metis_tac[]) >>
  `!name lo sz. local_region ce es.scopes s0 name lo sz ==>
    b+asz <= lo \/ lo+sz <= b` by
    (rpt strip_tac >>
     drule_all localPtrsPropsTheory.local_ptrs_rel_alloca_disjoint >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  `mem_bytes_at b asz u.vs_memory = mem_bytes_at b asz s0.vs_memory` by
    (qpat_x_assum `expr_post _ _ _ _ h _ _ _ _ _ _ _ u` mp_tac >>
     rewrite_tac[loweringPostsTheory.expr_post_def] >> strip_tac >>
     qpat_x_assum `!aid off sz. _ ==> mem_bytes_at off sz u.vs_memory = _`
       (qspecl_then [`inst.inst_id`,`b`,`asz`] mp_tac) >> simp[] >>
     disch_then match_mp_tac >>
     map_every qx_gen_tac [`local_name`,`local_base`,`local_size`] >> strip_tac >>
     qpat_x_assum `!name lo sz. local_region ce es.scopes s0 name lo sz ==> _`
       (qspecl_then [`local_name`,`local_base`,`local_size`] mp_tac) >>
     simp[arithmeticTheory.ADD_COMM]) >>
  `!i. b <= i /\ i < b+asz ==>
    mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 s0.vs_memory /\
    (i IN tn1.t_mem ==> i IN tn.t_mem)` by
    (asm_x "store" kall_tac >> gen_tac >> strip_tac >> conj_tac
     >- metis_tac[representationCleanPtrTheory.mem_bytes_at_eq_byte] >>
     strip_tac >>
     `inst.inst_id < sm.cs_next_id` by decide_tac >>
     `i IN tn'.t_mem` by metis_tac[] >>
     qpat_x_assum `ghost_kept ce es sa G tn s0 G' tn'`
       (mp_tac o CONJUNCT1 o CONJUNCT2 o
        REWRITE_RULE [bodyPtrDefsTheory.ghost_kept_def]) >>
     disch_then (qspecl_then [`inst.inst_id`,`b`,`asz`,`i`] mp_tac) >>
     simp[] >> disch_then match_mp_tac >>
     map_every qx_gen_tac [`local_name`,`local_base`,`local_size`] >> strip_tac >>
     qpat_x_assum `!name lo sz. local_region ce es.scopes s0 name lo sz ==> _`
       (qspecl_then [`local_name`,`local_base`,`local_size`] mp_tac) >>
     simp[arithmeticTheory.ADD_COMM]) >>
  `!i. b <= i /\ i < b+asz /\
    ~(b+off <= i /\ i < b+off+type_memory_size ht) ==>
    mem_bytes_at i 1 q.vs_memory = mem_bytes_at i 1 s0.vs_memory /\
    (i IN tn2.t_mem ==> i IN tn.t_mem)` by
    (asm_x "store" kall_tac >> metis_tac[]) >>
  `!z. not_fresh_at sa z ==> not_fresh_at sm z /\
    not_fresh_at su z /\ not_fresh_at st z` by
    (asm_x "store" kall_tac >> TRY (asm_x "tail" kall_tac) >>
     fs[exprLoweringPropsTheory.ci_mono_def] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
    lookup_var z q = SOME w` by
    (asm_x "store" kall_tac >> fs[loweringPostsTheory.expr_post_def] >> metis_tac[]) >>
  `!z. not_fresh_at sa z ==> FLOOKUP G2 z = FLOOKUP G z /\
    op_taint tn2 (Var z) = op_taint tn (Var z)` by
    (asm_x "store" kall_tac >> fs[bodyPtrDefsTheory.ghost_kept_def] >> metis_tac[]) >>
  `!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
    FLOOKUP q.vs_allocas aid = SOME entry` by
    (asm_x "store" kall_tac >> fs[loweringPostsTheory.expr_post_def] >> metis_tac[]) >>
  suspend "compose_outcome"
QED

Resume custom_error_store_args_sim_ptr_conditional[compose_outcome]:
  TRY (asm_x "store" kall_tac) >> TRY (asm_x "tail" kall_tac) >>
  `gas_path_ptr (cx_dead cx) 0 ctx func PG G' tn' t 0 G2 tn2 (OK q)` by
    (TRY (asm_x "store" kall_tac) >> TRY (asm_x "tail" kall_tac) >>
     metis_tac[fragGasPathPtrTheory.gas_path_ptr_then, arithmeticTheory.ADD]) >>
  `gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG
    (bind (eval_expr cx h) (read_result cx)) (es,s0,G,tn) marks
    (INL v) es_end G2 tn2 (OK q)` by
    (qpat_x_assum `gas_marked_exec_ptr _ _ _ (eval_expr cx h) _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [gas_marked_exec_ptr_def]) >>
     rewrite_tac[gas_marked_exec_ptr_def] >> conj_tac
     >- (qpat_x_assum
           `read_result cx tv (es_end with gas_obs := []) =
            (INL v,es_end with gas_obs := [])`
           (mp_tac o SIMP_RULE (srw_ss()) [] o
            MATCH_MP exprSimMemorySourceTheory.read_result_gas_obs) >>
         strip_tac >>
         simp[vyperStateTheory.bind_def]) >>
     qpat_x_assum `gas_path_ptr _ _ _ _ _ G tn s0 (LENGTH marks) G' tn' (OK t)`
       (fn prefix =>
         qpat_x_assum `gas_path_ptr _ _ _ _ _ G' tn' t 0 G2 tn2 (OK q)`
           (mp_tac o MATCH_MP fragGasPathPtrTheory.gas_path_ptr_then o CONJ prefix)) >>
     simp[]) >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ (eval_exprs cx args) _ _ _`
    (strip_assume_tac o REWRITE_RULE [fragGasPathPtrTheory.gas_outcome_ptr_def])
  >- (qpat_x_assum `gas_summary_ptr_at _ _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_ptr_at_marked])
      >- (gvs[] >> suspend "tail_normal")
      >> suspend "tail_exit") >>
  suspend "tail_exempt"
QED

Resume custom_error_store_args_sim_ptr_conditional[tail_normal]:
  rpt (CHANGED_TAC markerLib.RESUME_TAC) >> (
  rename1 `gas_marked_exec_ptr _ _ _ (eval_exprs cx args) _ right (INL vs) fin H tm (OK r)` >>
  `!m. mem_agree_outside tm.t_mem r.vs_memory m ==>
    tuple_in_memory (v::vs) (ht::tt) (b+off) m` by
    (match_mp_tac (Q.INST [`tv` |-> `ht`, `tn` |-> `tn2.t_mem`,
       `mem` |-> `q.vs_memory`, `mem'` |-> `r.vs_memory`,
       `tn'` |-> `tm.t_mem`, `a` |-> `b+off`, `tvs` |-> `tt`]
       custom_error_robust_tuple_cons_ptr) >>
     rpt conj_tac
     >- first_assum ACCEPT_TAC
     >- first_assum ACCEPT_TAC
     >- (gen_tac >> strip_tac >>
         qpat_x_assum `!i. _ ==> mem_bytes_at i 1 r.vs_memory =
           mem_bytes_at i 1 q.vs_memory /\ _`
           (qspec_then `i` match_mp_tac) >> decide_tac) >>
     pure_rewrite_tac[arithmeticTheory.ADD_ASSOC] >>
     first_assum (ACCEPT_TAC o PURE_REWRITE_RULE [arithmeticTheory.ADD_ASSOC])) >>
  `tuple_in_memory (v::vs) (ht::tt) (b+off) r.vs_memory` by
    (first_x_assum (qspec_then `r.vs_memory` mp_tac) >>
     simp[bodyPtrDefsTheory.mem_agree_outside_def]) >>
  qpat_x_assum `gas_marked_exec_ptr _ _ _ (eval_exprs cx args) _ _ _ _ _ _ _`
    (assume_tac o SIMP_RULE (srw_ss()) [] o MATCH_MP
       (Q.ISPEC `\xs:value list. v::xs`
          (Q.GEN `f` argsTailPtrTheory.gas_marked_exec_ptr_return_map))) >>
  rewrite_tac[fragGasPathPtrTheory.gas_outcome_ptr_def] >>
  qexists_tac `marks ++ right` >> disj1_tac >>
  rewrite_tac[gas_summary_ptr_at_marked] >>
  qexistsl_tac [`INL (v::vs)`,`fin`,`H`,`tm`,`OK r`] >>
  conj_tac
  >- (irule wordArgsPtrTheory.eval_exprs_cons_marked_ptr >>
      goal_assum (drule_at Any) >> simp[]) >>
  suspend "normal_post")
QED

Resume custom_error_store_args_sim_ptr_conditional[normal_post]:
  rpt (CHANGED_TAC markerLib.RESUME_TAC) >> (
  BETA_TAC >> disj1_tac >> qexists_tac `r` >> conj_tac >- REFL_TAC >>
  BETA_TAC >> qexists_tac `v::vs` >> conj_tac >- REFL_TAC >>
  pure_rewrite_tac[exprSimHypsDefsTheory.expr_sim_inv_gas_obs,
    exprSimWordArgsTheory.stmt_state_rel_gas_obs] >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- metis_tac[]
  >- metis_tac[]
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- (rpt strip_tac >> metis_tac[])
  >- (rpt strip_tac >> metis_tac[])
  >- (rpt strip_tac >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  `~(b+off <= i /\ i < b+off+type_memory_size ht) /\
   ~(b+(off+type_memory_size ht) <= i /\
      i < b+(off+type_memory_size ht)+type_memory_size_list tt)` by
    (fs[valueEncodingTheory.type_memory_size_def] >> decide_tac) >>
  qpat_x_assum `!i. _ ==> mem_bytes_at i 1 q.vs_memory =
    mem_bytes_at i 1 s0.vs_memory /\ _` (qspec_then `i` mp_tac) >>
  (impl_tac >- decide_tac) >> strip_tac >>
  qpat_x_assum `!i. _ ==> mem_bytes_at i 1 r.vs_memory =
    mem_bytes_at i 1 q.vs_memory /\ _` (qspec_then `i` mp_tac) >>
  (impl_tac >- decide_tac) >> strip_tac >> metis_tac[])
QED

Resume custom_error_store_args_sim_ptr_conditional[tail_exit]:
  rpt (CHANGED_TAC markerLib.RESUME_TAC) >> (
  gvs[] >>
  rename1 `gas_marked_exec_ptr _ _ _ (eval_exprs cx args) _ right (INR exc) fin H tm r` >>
  rewrite_tac[fragGasPathPtrTheory.gas_outcome_ptr_def] >>
  qexists_tac `marks ++ right` >> disj1_tac >>
  rewrite_tac[gas_summary_ptr_at_marked] >>
  qexistsl_tac [`INR exc`,`fin`,`H`,`tm`,`r`] >> simp[] >>
  irule wordArgsPtrTheory.eval_exprs_cons_marked_ptr >>
  goal_assum (drule_at Any) >>
  irule gas_marked_exec_ptr_bind_exception >> first_assum ACCEPT_TAC)
QED

Resume custom_error_store_args_sim_ptr_conditional[tail_exempt]:
  rpt (CHANGED_TAC markerLib.RESUME_TAC) >> (
  rename1 `gas_exempt_cert F _ _ _ _ right (err,ee) (leaf,tail_finish)` >>
  `gas_marked_exec F (ctx,func) (bind (eval_expr cx h) (read_result cx))
    (es,s0) marks (INL v) es_end (OK q)` by
    (irule gas_marked_exec_ptr_exec >> goal_assum (drule_at Any)) >>
  rewrite_tac[fragGasPathPtrTheory.gas_outcome_ptr_def] >>
  qexists_tac `marks ++ right` >> disj2_tac >>
  qexistsl_tac [`err`,`ee`,`leaf`,`tail_finish`] >>
  pure_rewrite_tac[exprSimWordArgsTheory.eval_exprs_cons_action,
    vyperStateTheory.ignore_bind_def] >>
  pure_once_rewrite_tac[vyperStateTheory.bind_assoc] >>
  irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
  goal_assum (drule_at Any) >>
  gvs[vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_assoc,
      vyperStateTheory.bind_return])
QED

Resume custom_error_store_args_sim_ptr_conditional[exit]:
  rpt (CHANGED_TAC markerLib.RESUME_TAC) >> (
  gvs[] >>
  `?exc. res = INR exc` by
    (TRY (asm_x "store" kall_tac) >> TRY (asm_x "tail" kall_tac) >>
     metis_tac[exprSimDefsTheory.expr_exit_INL, sumTheory.sum_CASES]) >>
  gvs[] >>
  rewrite_tac[fragGasPathPtrTheory.gas_outcome_ptr_def] >>
  qexists_tac `marks` >> disj1_tac >>
  rewrite_tac[gas_summary_ptr_at_marked] >>
  qexistsl_tac [`INR exc`, `es_end`, `G'`, `tn'`, `r`] >>
  simp[] >>
  rewrite_tac[exprSimWordArgsTheory.eval_exprs_cons_action] >>
  irule gas_marked_exec_ptr_bind_exception >>
  irule gas_marked_exec_ptr_bind_exception >>
  first_assum ACCEPT_TAC)
QED

Resume custom_error_store_args_sim_ptr_conditional[exempt]:
  rpt (CHANGED_TAC markerLib.RESUME_TAC) >> (
  rename1 `gas_exempt_cert F _ _ _ _ marks (err,ee) (leaf,fstate)` >>
  rewrite_tac[fragGasPathPtrTheory.gas_outcome_ptr_def] >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `fstate`] >>
  rewrite_tac[exprSimWordArgsTheory.eval_exprs_cons_action,
    vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_assoc] >>
  irule gasExemptCertTheory.gas_exempt_cert_error_result >>
  asm_rewrite_tac[GSYM vyperStateTheory.ignore_bind_def] >> gvs[])
QED
Finalise custom_error_store_args_sim_ptr_conditional

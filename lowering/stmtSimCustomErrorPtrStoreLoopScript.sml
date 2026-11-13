(* Interleaved pointer argument stores.  The tuple allocation is older than
   each expression entry, but younger than the fixed ghost reference. *)
Theory stmtSimCustomErrorPtrStoreLoop
Ancestors
  stmtSimCustomErrorPtrStoreHead stmtSimCustomErrorPtrUnwrap
  stmtSimCustomErrorStoreLoop typedWordArgsReadyPtr wordArgsPtr
  exprSimPtrTopLevelStorageFrame valueEncoding valueEncodingProps
  valueEncodingProofs bodyPtrDefs venomState finite_map pred_set
  gasSummaryComposePtr stmtFragPtr exprSimWordArgs

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
  !args ce cx env off sa sb es tvs func inst x b asz s0 ctx tys tops d PG G tn
    sr Gref tref sref.
  tys = MAP expr_type args /\
  compile_custom_error_store_args ce args tys (Var x) off sa = ((),sb) /\
  OPT_MMAP (evaluate_type (get_tenv cx)) (MAP expr_type args) = SOME tvs /\
  body_inv tops ctx ce cx /\ ~ce.ce_is_ctor /\ ~ctx_has_dalloca ctx /\
  expr_sim_inv ce cx env es /\
  (!e ee. MEM e args /\ expr_sim_inv ce cx env ee ==> expr_body_pre ce cx env e ee) /\
  body_exprs_ptr_ok cx args /\ EVERY (supported_pure_expr tops) args /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ MEM inst (fn_insts func) /\
  inst.inst_outputs = [x] /\ sr.cs_next_id <= inst.inst_id /\ inst.inst_id < sa.cs_next_id /\
  sr.cs_next_var <= sa.cs_next_var /\ sr.cs_next_id <= sa.cs_next_id /\
  (!ee. expr_sim_inv ce cx env ee ==> not_local_ptr ce ee.scopes x) /\
  not_fresh_at sa x /\ lookup_var x s0 = SOME (n2w b) /\
  FLOOKUP s0.vs_allocas inst.inst_id = SOME (b,asz) /\ ptr_covers G tn x s0 asz /\
  off + type_memory_size_list tvs <= asz /\ b+asz < dimword (:256) /\
  stmt_state_rel ctx func ce cx es s0 /\ ghost_inv d ce cx es G tn s0 /\
  ghost_kept ce es sr Gref tref sref G tn /\
  (!aid entry. FLOOKUP sref.vs_allocas aid = SOME entry ==> FLOOKUP s0.vs_allocas aid = SOME entry) /\
  (!n lo sz i. local_region ce es.scopes s0 n lo sz /\ lo <= i /\ i < lo+sz ==>
    ~(b <= i /\ i < b+asz)) /\
  (!aid lo sz i. FLOOKUP sref.vs_allocas aid = SOME (lo,sz) /\ aid < sr.cs_next_id /\
    lo <= i /\ i < lo+sz ==> ~(b <= i /\ i < b+asz)) /\
  (!ee n lo sz i. expr_sim_inv ce cx env ee /\ local_region ce ee.scopes sref n lo sz /\
    lo <= i /\ i < lo+sz ==> ~(b <= i /\ i < b+asz)) /\
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
      ghost_inv d ce cx ee Gf tf r /\ ghost_kept ce ee sr Gref tref sref Gf tf /\
      ptr_covers Gf tf x r asz /\ lookup_var x r = SOME (n2w b) /\
      FLOOKUP r.vs_allocas inst.inst_id = SOME (b,asz) /\
      (!mem. mem_agree_outside tf.t_mem r.vs_memory mem ==>
        tuple_in_memory vs tvs (b+off) mem) /\
      tuple_in_memory vs tvs (b+off) r.vs_memory /\
      tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
      (!z. not_fresh_at sa z ==> lookup_var z r = lookup_var z s0 /\
        FLOOKUP Gf z = FLOOKUP G z /\ op_taint tf (Var z) = op_taint tn (Var z)) /\
      (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==> FLOOKUP r.vs_allocas aid = SOME entry) /\
      (!i. b <= i /\ i < b+asz /\ ~(b+off <= i /\ i < b+off+type_memory_size_list tvs) ==>
        mem_bytes_at i 1 r.vs_memory = mem_bytes_at i 1 s0.vs_memory /\
        (i IN tf.t_mem ==> i IN tn.t_mem)) /\
      (!p n. b <= p /\ p+n <= b+asz /\
        (p+n <= b+off \/ b+off+type_memory_size_list tvs <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      (!aid p n. FLOOKUP s0.vs_allocas aid = SOME (p,n) /\
        aid < sa.cs_next_id /\ (p+n <= b \/ b+asz <= p) /\
        (!name lo sz. local_region ce es.scopes s0 name lo sz ==>
          p+n <= lo \/ lo+sz <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      locals_kept ce es ee s0 r /\
      (EVERY ($~ o expr_has_effect) args ==>
        (!name lo sz. local_region ce es.scopes s0 name lo sz ==>
          mem_bytes_at lo sz r.vs_memory = mem_bytes_at lo sz s0.vs_memory) /\
        (!p n. (p+n <= b \/ b+asz <= p) /\
          (!i c sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
            sa.cs_next_id <= i.inst_id /\
            FLOOKUP r.vs_allocas i.inst_id = SOME (c,sz) ==>
            regions_disjoint p n c sz) ==>
          mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory)))
    (\res ee gt exit. ?exc. res = INR exc /\
      expr_exit (INR exc : eval_result + exception) exit)
Proof
  disch_then (mk_asm "store") >> Induct_on `args`
  >- suspend "nil"
  >> suspend "cons"
QED

Resume custom_error_store_args_sim_ptr_conditional[nil]:
  asm_x "store" kall_tac >> rpt gen_tac >>
  simp[stmtLoweringTheory.compile_custom_error_store_args_def,
       compileEnvTheory.comp_return_def] >> strip_tac >> gvs[] >>
  rewrite_tac[fragGasPathPtrTheory.gas_outcome_ptr_def] >>
  qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_ptr_at_marked] >>
  qexistsl_tac [`INL []`, `es`, `G`, `tn`, `OK s0`] >>
  conj_tac >- (irule eval_exprs_nil_marked_ptr >> simp[]) >>
  simp[valueEncodingDefsTheory.val_in_memory_def,
       stmt_state_rel_gas_obs, ghost_inv_gas_obs] >>
  gvs[bodyPtrDefsTheory.ghost_kept_def] >> metis_tac[]
QED

Resume custom_error_store_args_sim_ptr_conditional[cons]:
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
    (asm_x "store" kall_tac >>
     metis_tac[exprLoweringPropsTheory.compile_expr_ci_mono,
       exprLoweringPropsTheory.ci_mono_unwrap_value,
       exprLoweringPropsTheory.ci_mono_compile_store_memory,
       cj 1 stmtLoweringMonoTheory.ci_mono_custom_error, pairTheory.SND]) >>
  `ci_mono sm sn` by
    (asm_x "store" kall_tac >> Cases_on `off = 0` >>
     gvs[compileEnvTheory.comp_return_def] >>
     metis_tac[exprLoweringPropsTheory.ci_mono_emit_op, pairTheory.SND,
       exprLoweringPropsTheory.ci_mono_refl]) >>
  `fn_has_code sa sm func /\ fn_has_code st sb func /\ fn_has_code sa st func` by
    (asm_x "store" kall_tac >>
     metis_tac[fragExecTheory.fn_has_code_split, exprLoweringPropsTheory.ci_mono_def,
       compileEnvTheory.cs_extends_trans]) >>
  `expr_body_pre ce cx env h es` by
    (asm_x "store" kall_tac >> metis_tac[listTheory.MEM]) >>
  `expr_vv_sim_ptr d ctx PG func ce cx (expr_type h) h es` by
    (asm_x "store" kall_tac >>
     gvs[bodyPtrPredsTheory.body_exprs_ptr_ok_def] >>
     qpat_x_assum `body_expr_ptr_ok cx h` mp_tac >>
     simp[Once bodyPtrPredsTheory.body_expr_ptr_ok_def] >> metis_tac[]) >>
  `gas_admissible (eval_expr cx h) expr_vv_res_ok es` by
    (asm_x "store" kall_tac >>
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
    (asm_x "store" kall_tac >> metis_tac[listTheory.MEM]) >>
  `type_memory_bytes ce (expr_type h) = type_memory_size ht` by
    (asm_x "store" kall_tac >>
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
    (asm_x "store" kall_tac >>
     metis_tac[exprSimAggregateSourceTheory.aggregate_materialised_child_typed,
       exprSimAggregateSourceTheory.aggregate_materialised_child_wf]) >>
  `int_calls_expr h = []` by
    (asm_x "store" kall_tac >>
     metis_tac[bodyExprPreFactsTheory.supported_pure_int_calls]) >>
  `post_value_type ce h = expr_type h` by simp[] >>
  qspecl_then [`ce`,`h`,`env`] mp_tac
    exprSimAggregateLoopsTheory.aggregate_elem_lowered_type >>
  (impl_tac >- (asm_x "store" kall_tac >>
    fs[exprSimHypsDefsTheory.expr_body_pre_def])) >> disch_tac >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by
    fs[exprLoweringPropsTheory.ci_mono_def] >>
  `local_ptrs_reserved ce sm` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `!z. vv_operand vv = Var z ==> not_fresh_at sm z` by
    metis_tac[cj 1 exprOperandVarTheory.compiler_compile_var] >>
  `fn_has_code sm sn func /\ fn_has_code sn su func` by
    (asm_x "store" kall_tac >>
     metis_tac[fragExecTheory.fn_has_code_split, exprLoweringPropsTheory.ci_mono_def,
       compileEnvTheory.cs_extends_trans]) >>
  `expr_sim_inv ce cx env (es_end with gas_obs := [])` by
    (asm_x "store" kall_tac >> metis_tac[exprSimSourceTheory.expr_body_pre_eval]) >>
  FAIL_TAC "unwrap premises"
QED

Resume custom_error_store_args_sim_ptr_conditional[exit]:
  gvs[] >>
  `?exc. res = INR exc` by
    (asm_x "store" kall_tac >>
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
  first_assum ACCEPT_TAC
QED

Resume custom_error_store_args_sim_ptr_conditional[exempt]:
  rename1 `gas_exempt_cert F _ _ _ _ marks (err,ee) (leaf,fstate)` >>
  rewrite_tac[fragGasPathPtrTheory.gas_outcome_ptr_def] >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `fstate`] >>
  rewrite_tac[exprSimWordArgsTheory.eval_exprs_cons_action,
    vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_assoc] >>
  irule gasExemptCertTheory.gas_exempt_cert_error_result >>
  asm_rewrite_tac[GSYM vyperStateTheory.ignore_bind_def] >> gvs[]
QED
Finalise custom_error_store_args_sim_ptr_conditional

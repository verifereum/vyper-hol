(* Full AsWeiValue continuation at one common child midpoint. *)
Theory bodyFullBuiltinWordWeiContinuation
Ancestors
  bodyFullBuiltinWordWeiPrefix bodyFullBuiltinWordWeiSuffix
  bodySimFull exprSimSource gasOutcomeFullCompose exprSimProps
  exprSimWordBuiltins exprSimWordArgs exprLoweringProps exprSimUnopProps fragExec exprSimDefs
  vyperStorageTrace vyperStorageFootprint gasStorage compileEnv vyperTypeSystem
  vyperContext vyperAST list

Theorem as_wei_value_continuation_full:
  expr_type e = BaseT (UintT k) /\
  expr_body_pre cenv cx env e es /\
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (Builtin (BaseT (UintT 256)) (AsWeiValue dn) [e]) es /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,s1) /\
  compile_as_wei_value_int x (denomination_multiplier dn) F s1 = (op,sb) /\
  sa.cs_next_var <= s1.cs_next_var /\
  fn_has_code s1 sb func /\ local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!tail. bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
     (INL v, mid with gas_obs := tail)) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post H ctx func cenv cx e es sa s1 s0 mid v x t /\
    expr_store_bound cx (expr_type e) v x t /\
    t.vs_current_bb = s1.cs_current_bb /\
    t.vs_inst_idx = LENGTH s1.cs_current_insts /\ alloca_history func t /\
    s0.vs_alloca_next <= t.vs_alloca_next /\
    ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t /\
    ptr_val_ok cx (expr_type e) v x G1 tn1 t /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
    ~t.vs_halted /\ mid.gas_obs = []) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    ((\v ee. (builtin_result cx ee.accounts (BaseT (UintT 256))
      (AsWeiValue dn) [expr_type e] [v],ee)) v) (mid,t,G1,tn1)
    (\H res ee G tn u. (?w. res = INL w /\
      expr_post H ctx func cenv cx (Builtin (BaseT (UintT 256)) (AsWeiValue dn) [e])
        es sa sb s0 ee w op u /\
      expr_store_bound cx (BaseT (UintT 256)) w op u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func u /\
      s0.vs_alloca_next <= u.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn u /\
      ptr_val_ok cx (BaseT (UintT 256)) w op G tn u) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
    (\H res ee gt r. expr_exit res r)
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v` by
    (`expr_body_pre cenv cx env e
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
     qpat_assum `!tail. bind _ _ _ = _`
       (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [APPEND_NIL])) >>
     `is_word_type (expr_type e)` by simp[is_word_type_def] >>
     metis_tac[expr_body_pre_word_value]) >>
  `post_value_type cenv e = expr_type e` by
    simp[loweringPostsTheory.post_value_type_word, is_word_type_def] >>
  `op_prov G1 x = NONE /\ op_taint tn1 x = {}` by
    fs[bodyPtrDefsTheory.ptr_val_ok_def, is_word_type_def] >>
  `expr_val_rel cx (expr_type e) v x t` by
    gvs[loweringPostsTheory.expr_post_def] >>
  qpat_x_assum `expr_val_rel _ _ _ _ _` mp_tac >>
  simp[loweringPostsTheory.expr_val_rel_def, is_word_type_def,
       vyperValueTheory.evaluate_type_def] >> strip_tac >>
  gvs[vyperValueTheory.evaluate_type_def] >>
  `v = IntV (&w2n (val_to_w256 v))` by metis_tac[uint_value_word_rep] >>
  `typed_val_to_w256 (BaseTV (UintT k)) v = val_to_w256 v` by
    (Cases_on `v` >> fs[vyperTypingTheory.value_has_type_def,
                        valueEncodingTheory.typed_val_to_w256_def]) >>
  `!z. x = Var z ==> not_fresh_at s1 z` by
    (qpat_assum `lower_value _ _ _ e sa = _`
       (mp_then Any mp_tac expr_body_pre_lower_value_word_shape) >>
     simp[is_word_type_def] >> metis_tac[]) >>
  `0 < denomination_multiplier dn /\ denomination_multiplier dn < dimword (:256)` by
    (qspec_then `dn` mp_tac denomination_multiplier_bounds >> simp[wordsTheory.dimword_def]) >>
  drule_all compile_as_wei_value_int_run >> strip_tac >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >>
     fs[bodyPtrDefsTheory.ghost_inv_at_def]) >>
  Cases_on `w2n (typed_val_to_w256 (BaseTV (UintT k)) v) * denomination_multiplier dn < dimword (:256)`
  >- (first_x_assum drule >> strip_tac >>
      drule_all (as_wei_value_success_full |> Q.INST [`es'` |-> `mid`, `es` |-> `mid`] |> SIMP_RULE (srw_ss()) []) >>
      disch_then (qspecl_then [`mid`, `explicit`, `d`, `cx`, `PG`] strip_assume_tac) >>
      `builtin_result cx mid.accounts (BaseT (UintT 256)) (AsWeiValue dn)
         [BaseT (UintT k)] [v] = INL (IntV (&(w2n (val_to_w256 v) * denomination_multiplier dn)))` by
        (qpat_assum `v = IntV _` (fn th => rewrite_tac[Once th]) >>
         simp[builtin_result_def, evaluate_builtin_def, evaluate_as_wei_value_uint,
              wordsTheory.dimword_def] >>
         gvs[wordsTheory.dimword_def]) >>
      irule gas_outcome_full_intro >>
      qexistsl_tac [`G'`, `mid`, `[]`,
        `OK (ss' with vs_inst_idx := LENGTH sb.cs_current_insts)`,
        `INL (IntV (&(w2n (val_to_w256 v) * denomination_multiplier dn)))`, `tn'`] >>
      `mid with gas_obs := [] = mid` by
        (qpat_assum `mid.gas_obs = []` (fn th => rewrite_tac[GSYM th]) >> simp[]) >>
      simp[] >> rpt strip_tac >>
      `expr_post H ctx func cenv cx e es sa s1 s0 mid v x t /\
       ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t` by metis_tac[] >>
      `ghost_inv_at (DF H) lo d cenv cx mid G' tn'
          (ss' with vs_inst_idx := LENGTH sb.cs_current_insts)` by metis_tac[] >>
      `ss'.vs_current_bb = sb.cs_current_bb` by
        (drule bodyPtrWordBuiltinsScalingTheory.word_scale_current_block >> strip_tac >>
         qpat_assum `ss' = t with vs_vars := _` (fn th => rewrite_tac[Once th]) >> simp[]) >>
      simp[bodyPtrDefsTheory.ptr_val_ok_def, is_word_type_def]
      >~ [`expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`]
      >- (simp[loweringPostsTheory.expr_post_def, expr_type_def,
               loweringPostsTheory.post_value_type_word, is_word_type_def] >>
          conj_tac
          >- (`stmt_state_rel H ctx func cenv cx mid t` by
                fs[loweringPostsTheory.expr_post_def] >>
              simp[stmt_state_rel_inst_idx] >>
              qpat_assum `ss' = t with vs_vars := _` (fn th => rewrite_tac[Once th]) >>
              irule stmt_state_rel_vars_frame >> simp[] >>
              rpt strip_tac >>
              fs[loweringStateRelDefsTheory.local_ptrs_reserved_def] >>
              metis_tac[]) >>
          conj_tac
          >- (`storage_well_formed_on cx mid (FST H)` by
                fs[loweringPostsTheory.expr_post_def] >>
              fs[vyperStorageFootprintTheory.storage_well_formed_on_def]) >>
          conj_tac
          >- (simp[loweringPostsTheory.expr_val_rel_def, is_word_type_def,
                   vyperValueTheory.evaluate_type_def,
                   valueEncodingTheory.typed_val_to_w256_def,
                   valueEncodingTheory.val_to_w256_def] >>
              gvs[integer_wordTheory.i2w_pos, GSYM wordsTheory.word_mul_n2w,
                  arithmeticTheory.MULT_COMM, wordsTheory.WORD_MULT_COMM]) >>
          simp[loweringPostsTheory.expr_val_at_def, is_word_type_def] >>
          conj_tac
          >- (fs[loweringPostsTheory.expr_post_def, venomStateTheory.lookup_var_def] >>
              metis_tac[]) >>
          qpat_assum `ss' = t with vs_vars := _` (fn th => rewrite_tac[Once th]) >>
          simp[loweringPostsTheory.pure_frame_def] >>
          fs[loweringPostsTheory.expr_post_def, loweringPostsTheory.pure_frame_def] >>
          `ss'.vs_memory = t.vs_memory /\ ss'.vs_allocas = t.vs_allocas` by
            (conj_tac >>
             qpat_assum `ss' = t with vs_vars := _` (fn th => rewrite_tac[Once th]) >> simp[]) >>
          fs[loweringPostsTheory.locals_kept_def, loweringPostsTheory.popped_kept_def] >>
          metis_tac[])
      >~ [`expr_store_bound _ _ _ _ _`]
      >- simp[exprSimMemDefsTheory.expr_store_bound_word, is_word_type_def]
      >~ [`alloca_history func _`]
      >- (`sb.cs_current_bb = s1.cs_current_bb` by
            metis_tac[bodyPtrWordBuiltinsScalingTheory.word_scale_current_block] >>
          drule bodyPtrWordBuiltinsScalingTheory.word_scale_code_prefix >> strip_tac >>
          `EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts s1 sb)` by
            (Cases_on `denomination_multiplier dn = 1`
             >- (gvs[] >> drule bodyPtrWordBuiltinsScalingTheory.word_scale_identity >> simp[]) >>
             drule_all bodyPtrWordBuiltinsScalingTheory.word_scale_emitted_shape >>
             strip_tac >> fs[EVERY_MEM] >> rpt strip_tac >>
             first_x_assum drule >> simp[]) >>
          first_x_assum (qspecl_then [`t`, `func`] mp_tac) >>
          simp[] >> strip_tac >>
          qpat_assum `isPREFIX _ _` mp_tac >>
          pure_rewrite_tac[rich_listTheory.IS_PREFIX_APPEND] >> strip_tac >>
          drule bodyPtrWordBuiltinsScalingTheory.word_scale_current_block >> strip_tac >>
          `LENGTH sb.cs_current_insts = t.vs_inst_idx + LENGTH (emitted_insts s1 sb)` by
            simp[] >>
          `ss'.vs_allocas = t.vs_allocas` by
            (qpat_assum `ss' = t with vs_vars := _` (fn th => rewrite_tac[Once th]) >> simp[]) >>
          simp[allocaHistoryTheory.alloca_history_def] >> conj_tac
          >- fs[allocaHistoryTheory.alloca_history_def] >>
          rpt strip_tac >>
          rename1 `get_instruction bb j = SOME inst` >>
          Cases_on `j < LENGTH s1.cs_current_insts`
          >- (fs[allocaHistoryTheory.alloca_history_def] >> metis_tac[]) >>
          `j < LENGTH bb.bb_instructions /\ EL j bb.bb_instructions = inst` by
            fs[venomInstTheory.get_instruction_def] >>
          `j - LENGTH s1.cs_current_insts + LENGTH s1.cs_current_insts = j /\
           j - LENGTH s1.cs_current_insts < LENGTH (emitted_insts s1 sb)` by decide_tac >>
          `EL (j - LENGTH s1.cs_current_insts) (DROP (LENGTH s1.cs_current_insts) bb.bb_instructions) = inst` by
            (qspecl_then [`j - LENGTH s1.cs_current_insts`, `LENGTH s1.cs_current_insts`, `bb.bb_instructions`]
              mp_tac EL_DROP >> simp[]) >>
          `EL (j - LENGTH s1.cs_current_insts) (emitted_insts s1 sb) = inst` by
            (qpat_x_assum `EL _ (DROP _ _) = _` mp_tac >> simp[EL_APPEND_EQN]) >>
          `MEM inst (emitted_insts s1 sb)` by metis_tac[EL_MEM] >>
          fs[EVERY_MEM] >> metis_tac[]) >>
      qpat_assum `ss' = t with vs_vars := _` (fn th => rewrite_tac[Once th]) >> simp[]) >>
  first_x_assum drule >> strip_tac >>
  drule_all (as_wei_value_abort_full |> Q.INST [`es'` |-> `mid`, `es` |-> `mid`] |> SIMP_RULE (srw_ss()) []) >>
  disch_then (qspecl_then [`mid`, `explicit`, `d`, `cx`, `PG`] strip_assume_tac) >>
  `builtin_result cx mid.accounts (BaseT (UintT 256)) (AsWeiValue dn)
      [BaseT (UintT k)] [v] = INR (Error (RuntimeError "ewv bound"))` by
    (qpat_assum `v = IntV _` (fn th => rewrite_tac[Once th]) >>
     simp[builtin_result_def, evaluate_builtin_def, evaluate_as_wei_value_uint,
          wordsTheory.dimword_def] >>
     gvs[wordsTheory.dimword_def]) >>
  irule gas_outcome_full_intro >>
  qexistsl_tac [`G'`, `mid`, `[]`,
    `Abort Revert_abort (ss' with vs_inst_idx := j)`,
    `INR (Error (RuntimeError "ewv bound"))`, `tn'`] >>
  `mid with gas_obs := [] = mid` by
    (qpat_assum `mid.gas_obs = []` (fn th => rewrite_tac[GSYM th]) >> simp[]) >>
  simp[] >> rpt strip_tac >>
  simp[expr_exit_def, exit_result_def] >> metis_tac[]
QED

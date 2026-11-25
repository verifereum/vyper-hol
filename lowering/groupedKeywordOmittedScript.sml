(* Store the value of an omitted keyword in its entry allocation. *)
Theory groupedKeywordOmitted
Libs groupedKeywordOmittedLib
Ancestors
  groupedKeywordStore groupedKeywordOwners runtimeDefaultExpression exprSimFullBundleProps
  exprOperandVar exprLoweringProps emitHelperProps typedMemoryCopy
  loweringPosts bodyPtrDefs loweringStateRelDefs typedCopyOriginPtrBase
  bodyPtrMakeArrayCopyStateFrame bodyFullEmptyFrame bodySimFull robustCopyTransportPtr
  gasOutcomeFullCompose bodyFullPathHistory vyperStorageFootprint vyperTypeExprResult vyperTypeExprSoundness
  exprSimSource valueEncodingTyping vyperContext vyperAST vyperTypeContract
  vyperTypeInvariants loweringShapeDefs ptrDiscipline
  venomState venomMemDefs compileEnv finite_map arithmetic fragExec

val omitted_store_inputs = ``
  runtime_constant_expr mods e /\ expr_type e = ty /\
  lower_value compile_expr (ce with ce_vars := FEMPTY) ty e sa = (src,mid) /\
  (if is_word_type ty then emit_void MSTORE [Var dst;src]
   else if is_bytestring_type ty then compile_store_bytestring src (Var dst)
   else emit_void MCOPY [Var dst;src;Lit (n2w (type_memory_bytes ce ty))])
    mid = ((),last) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ env.type_defs = get_tenv cx /\
  type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_size tv + 64 < dimword (:256) /\
  fn_has_code mid last fn /\ local_ptrs_reserved (ce with ce_vars := FEMPTY) sa /\
  not_fresh_at sa dst /\ lookup_var dst s = SOME b /\
  FLOOKUP s.vs_allocas oid = SOME (w2n b,type_memory_size tv) /\
  ptr_covers G tn dst s (type_memory_size tv) /\
  expr_sim_full_post (DF,0,NONE,ctx,fn) (ce with ce_vars := FEMPTY) cx e
    (es,sa,mid,s,src,G,tn) H (INL v) ee G1 tn1 t /\
  expr_result_typed env e (Value v) /\ ~t.vs_halted``;

val omitted_store_post = ``
    (!D. gas_origin_ptr_path (D,0,explicit,ctx,fn,PG)
      (t,G1,tn1) [] (OK u,G2,tn2)) /\
    (!mem. mem_agree_outside tn2.t_mem u.vs_memory mem ==>
      val_in_memory tv v (w2n (b:256 word)) mem) /\
    value_has_type tv v /\ val_wf tv v /\
    ptr_covers G2 tn2 dst u (type_memory_size tv) /\
    typed_copy_state_frame mid (w2n b) (type_memory_size tv) t u /\
    (!x. not_fresh_at mid x ==> FLOOKUP G2 x = FLOOKUP G1 x /\
      op_taint tn2 (Var x) = op_taint tn1 (Var x)) /\
    (!i. i < w2n b \/ w2n b+type_memory_size tv <= i ==>
       (i IN tn2.t_mem <=> i IN tn1.t_mem)) /\
    tn2.t_stor = tn1.t_stor /\ tn2.t_trans = tn1.t_trans /\ tn2.t_imm = tn1.t_imm /\
    u.vs_current_bb = last.cs_current_bb /\
    u.vs_inst_idx = LENGTH last.cs_current_insts /\ ~u.vs_halted``;

Theorem grouped_keyword_omitted_store_exact[local]:
  ^omitted_store_inputs ==>
  ?u G2 tn2.
    run_inst_seq (emitted_insts mid last) t = OK (u with vs_inst_idx := t.vs_inst_idx) /\
    ^omitted_store_post
Proof
  strip_tac >>
  `post_value_type (ce with ce_vars := FEMPTY) e = ty` by
    (`!t fid args drv. e <> Call t (IntCall fid) args drv` by
       (rpt strip_tac >> gvs[runtime_constant_expr_def]) >>
     qpat_assum `expr_type e = ty` (SUBST1_TAC o SYM) >>
     irule post_value_type_not_int_call >> first_assum ACCEPT_TAC) >>
  qpat_assum `expr_sim_full_post _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [expr_sim_full_post_def]) >>
  qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE bool_ss [expr_post_def]) >>
  `value_has_type tv v` by
    (qpat_assum `expr_result_typed env e (Value v)` mp_tac >>
     simp_tac (srw_ss()) [expr_result_typed_def, expr_runtime_typed_def,
       value_result_typed_def] >>
     qpat_assum `expr_type e = ty` (pure_rewrite_tac o single) >>
     qpat_assum `env.type_defs = get_tenv cx` (pure_rewrite_tac o single) >>
     qpat_assum `evaluate_type (get_tenv cx) ty = SOME tv`
       (simp_tac (srw_ss()) o single)) >>
  `val_wf tv v` by metis_tac[cj 1 value_has_type_val_wf] >>
  `ci_mono sa mid` by
    metis_tac[ci_mono_lower_value_compile_expr, pairTheory.SND] >>
  `not_fresh_at mid dst` by
    (irule not_fresh_at_mono >> qexists_tac `sa` >> fs[ci_mono_def]) >>
  `!x. src = Var x ==> not_fresh_at mid x` by
    (gen_tac >> strip_tac >>
     `!vv sm. compile_expr (ce with ce_vars := FEMPTY) ty e sa = (vv,sm) ==>
       !x. vv_operand vv = Var x ==> not_fresh_at sm x` by
       (rpt gen_tac >> strip_tac >>
        mp_tac (Q.SPECL [`ce with ce_vars := FEMPTY`,`ty`,`e`,`sa`,`vv`,`sm`]
          (cj 1 compiler_compile_var)) >> asm_rewrite_tac[]) >>
     qpat_assum `lower_value compile_expr _ ty e sa = (src,mid)`
       (mp_then Any (qspec_then `x` mp_tac) compiler_lower_value_var) >>
     asm_rewrite_tac[]) >>
  `FLOOKUP t.vs_allocas oid = SOME (w2n b,type_memory_size tv) /\
    lookup_var dst t = SOME b` by
    (conj_tac
     >- (qpat_assum `!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==> _`
           (qspecl_then [`oid`,`(w2n b,type_memory_size tv)`] mp_tac) >> simp[]) >>
     qpat_assum `!x w. not_fresh_at sa x /\ _ ==> _`
       (qspecl_then [`dst`,`b`] mp_tac) >> simp[]) >>
  `ptr_covers G1 tn1 dst t (type_memory_size tv)` by
    (qpat_assum `ghost_kept_at _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >>
     qpat_assum `!p. not_fresh_at sa p ==> _`
       (qspec_then `dst` (drule_then strip_assume_tac)) >>
     pure_rewrite_tac[ptr_covers_def] >>
     MAP_EVERY (fn pat => qpat_assum pat (pure_rewrite_tac o single))
       [`FLOOKUP G1 dst = FLOOKUP G dst`,`op_taint tn1 (Var dst) = op_taint tn (Var dst)`,
        `lookup_var dst t = SOME b`] >>
     qpat_assum `ptr_covers G tn dst s _` mp_tac >>
     pure_rewrite_tac[ptr_covers_def] >>
     qpat_assum `lookup_var dst s = SOME b` (pure_rewrite_tac o single) >>
     simp_tac bool_ss []) >>
  `w2n b + type_memory_size tv <= t.vs_alloca_next` by
    (qpat_assum `stmt_state_rel H ctx fn _ cx ee t`
       (strip_assume_tac o REWRITE_RULE [stmt_state_rel_def, alloca_inv_def,
         alloca_next_valid_def]) >>
     qpat_assum `!id a n. FLOOKUP t.vs_allocas id = SOME (a,n) ==> _`
       (qspecl_then [`oid`,`w2n b`,`type_memory_size tv`] mp_tac) >> simp[]) >>
  drule expr_sim_full_endpoint_fields >> strip_tac >>
  `allocas_from 0 t` by simp[allocas_from_def] >>
  qpat_assum `post_value_type _ e = ty` (RULE_ASSUM_TAC o REWRITE_RULE o single) >>
  mp_tac (Q.INST [`sa` |-> `mid`,`sb` |-> `last`,`s` |-> `t`,
    `G` |-> `G1`,`tn` |-> `tn1`,`lo` |-> `0`]
    (SPEC_ALL grouped_keyword_store_value_exact)) >>
  impl_tac >- asm_simp_tac (srw_ss()) [] >>
  disch_then (qx_choosel_then [`u`,`G2`,`tn2`] strip_assume_tac) >>
  `ptr_covers G2 tn2 dst u (type_memory_size tv)` by
    (qpat_assum `!p. not_fresh_at mid p ==> _`
       (qspec_then `dst` (drule_then strip_assume_tac)) >>
     `lookup_var dst u = SOME b` by
       (qpat_assum `typed_copy_state_frame mid _ _ t u`
          (mp_tac o REWRITE_RULE [typed_copy_state_frame_def]) >>
        strip_tac >>
        qpat_assum `!x. not_fresh_at mid x ==> lookup_var x u = lookup_var x t`
          (qspec_then `dst` (drule_then SUBST1_TAC)) >>
        first_assum ACCEPT_TAC) >>
     pure_rewrite_tac[ptr_covers_def] >>
     MAP_EVERY (fn pat => qpat_assum pat (pure_rewrite_tac o single))
       [`FLOOKUP G2 dst = FLOOKUP G1 dst`,`op_taint tn2 (Var dst) = op_taint tn1 (Var dst)`,
        `lookup_var dst u = SOME b`] >>
     qpat_assum `ptr_covers G1 tn1 dst t _` mp_tac >>
     pure_rewrite_tac[ptr_covers_def] >>
     qpat_assum `lookup_var dst t = SOME b` (pure_rewrite_tac o single) >>
     simp_tac bool_ss []) >>
  qexistsl_tac [`u`,`G2`,`tn2`] >>
  asm_rewrite_tac[] >>
  metis_tac[]
QED

Theorem grouped_keyword_omitted_store:
  ^omitted_store_inputs ==> ?u G2 tn2. ^omitted_store_post
Proof
  disch_tac >> mp_tac (SPEC_ALL grouped_keyword_omitted_store_exact) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (qx_choosel_then [`u`,`G2`,`tn2`] (assume_tac o CONJUNCT2)) >>
  qexistsl_tac [`u`,`G2`,`tn2`] >> first_assum ACCEPT_TAC
QED

Theorem grouped_keyword_store_runtime_state:
  typed_copy_state_frame mid off len t u /\
  ~ce.ce_is_ctor /\ ce.ce_imm_alloca = NONE /\
  stmt_state_rel H ctx fn (ce with ce_vars := FEMPTY) cx es t ==>
  stmt_state_rel H ctx fn (ce with ce_vars := FEMPTY) cx es u
Proof
  strip_tac >>
  fs[typed_copy_state_frame_def, typed_copy_frame_def,
     venom_state_component_equality] >>
  `state_rel H fn (ce with ce_vars := FEMPTY) cx es u` by
    (gvs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def, local_region_def, FLOOKUP_EMPTY,
       immutables_rel_def, storage_rel_def, transient_rel_def, accounts_rel_def,
       contract_storage_def, contract_transient_def, logs_rel_def, LET_THM] >>
    first_assum ACCEPT_TAC) >>
  mp_tac (Q.SPECL [`H`,`fn`,`ce with ce_vars := FEMPTY`,`cx`,
    `es`,`t`,`es`,`u`,`ctx`] stmt_state_rel_allocas_frame) >>
  simp[immutable_alloca_sep_def, immutable_decl_sep_def, immutable_base_zero_alt] >>
  metis_tac[]
QED

Theorem grouped_keyword_store_runtime_ghost:
  typed_copy_state_frame mid off len t u /\
  ce.ce_return_pc = NONE /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
  ghost_inv_at D 0 NONE (ce with ce_vars := FEMPTY) cx es G tn t ==>
  ghost_inv_at D 0 NONE (ce with ce_vars := FEMPTY) cx es G' tn' u
Proof
  rw[typed_copy_state_frame_def, venom_state_component_equality, ghost_inv_at_def,
     return_buf_ptr_def, allocas_from_def, stor_taint_ok_at_def, FLOOKUP_EMPTY] >>
  fs[contract_storage_def, contract_transient_def]
QED

Theorem grouped_keyword_store_owner_frame:
  typed_copy_state_frame mid dst len t u /\
  alloca_inv t /\ FLOOKUP t.vs_allocas did = SOME (dst,len) /\
  FLOOKUP t.vs_allocas oid = SOME (b,n) /\ oid <> did /\
  not_fresh_at mid p /\ lookup_var p t = SOME (n2w b) /\ ptr_covers G tn p t n /\
  FLOOKUP G' p = FLOOKUP G p /\ op_taint tn' (Var p) = op_taint tn (Var p) /\
  (!i. i < dst \/ dst + len <= i ==> (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
  val_wf tv v /\ val_footprint tv v <= n /\
  (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==> val_in_memory tv v b mem) ==>
  FLOOKUP u.vs_allocas oid = SOME (b,n) /\
  lookup_var p u = SOME (n2w b) /\ ptr_covers G' tn' p u n /\
  (!mem. mem_agree_outside tn'.t_mem u.vs_memory mem ==> val_in_memory tv v b mem)
Proof
  strip_tac >>
  qpat_assum `alloca_inv t`
    (strip_assume_tac o REWRITE_RULE [alloca_inv_def, allocas_non_overlapping_def]) >>
  `b + n <= dst \/ dst + len <= b` by metis_tac[ADD_COMM] >>
  fs[typed_copy_state_frame_def, venom_state_component_equality, typed_copy_frame_def] >>
  `lookup_var p u = lookup_var p t` by metis_tac[] >>
  `ptr_covers G' tn' p u n` by fs[ptr_covers_def] >>
  asm_rewrite_tac[] >>
  mp_tac (Q.SPECL [`tv`,`v`,`b`,`b`,`n`,`tn.t_mem`,`tn'.t_mem`,
    `t.vs_memory`,`u.vs_memory`] robust_val_in_memory_decreasing_taint_transport) >>
  impl_tac >-
    (asm_rewrite_tac[] >> conj_tac >- metis_tac[] >>
     rpt strip_tac >>
     `b+i < dst \/ dst+len <= b+i` by decide_tac >>
     metis_tac[]) >>
  simp[]
QED

val omitted_expr_inputs = groupedKeywordOmittedLib.omitted_expr_inputs ();
val omitted_expr_store_post = groupedKeywordOmittedLib.omitted_expr_store_post ();
val omitted_expr_normal_post = groupedKeywordOmittedLib.omitted_expr_normal_post ();

(* At the intrinsic horizon select the store once. The callback can retain
   a horizon-independent property of the exact run and its two cursors. *)
Theorem grouped_keyword_store_normal_witness:
  ^omitted_expr_inputs /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    ^omitted_expr_normal_post H res ee G1 tn1 t) /\
  (!u. ~t.vs_halted /\ t.vs_current_bb = mid.cs_current_bb /\
    t.vs_inst_idx = LENGTH mid.cs_current_insts /\
    run_inst_seq (emitted_insts mid last) t = OK (u with vs_inst_idx := t.vs_inst_idx) /\
    u.vs_inst_idx = LENGTH last.cs_current_insts ==> keep t u) ==>
  ?u J tz. keep t u /\
    !H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,0,gas_explicit_sites ctx shadow_ctx,ctx,fn,PG)
        (t,G1,tn1) [] (OK u,J,tz) /\
      ^omitted_expr_store_post H res ee J tz u
Proof
  CONV_TAC (DEPTH_CONV BETA_CONV) >> strip_tac >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 H0 ee.storage_trace` by
    fs[Abbr `H0`, storage_trace_domain_def] >>
  first_assum (drule_then strip_assume_tac) >>
  fs[expr_sim_full_hypotheses_def] >>
  `fn_inst_ids_distinct fn` by metis_tac[expr_sim_full_code_fields] >>
  qpat_assum `expr_sim_full_post _ _ _ _ _ H0 _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [expr_sim_full_post_def]) >>
  `expr_result_typed env e (Value v)` by
    (qpat_assum `!vv. res = INL vv ==> _` (qspec_then `v` match_mp_tac) >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `res = INL v` SUBST_ALL_TAC >>
  mp_tac (Q.INST [`H` |-> `H0`, `v` |-> `v`, `G1` |-> `G1`, `tn1` |-> `tn1`,
    `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
    (INST_TYPE [alpha |-> ``:256``] (SPEC_ALL grouped_keyword_omitted_store_exact))) >>
  impl_tac >-
    (asm_rewrite_tac[] >> simp[expr_sim_full_post_def] >>
     qexists_tac `v` >> asm_rewrite_tac[]) >>
  disch_then (qx_choosel_then [`u`,`J`,`tz`] strip_assume_tac) >>
  qexistsl_tac [`u`,`J`,`tz`] >> conj_tac
  >- (first_assum match_mp_tac >>
      drule expr_sim_full_endpoint_fields >> simp[]) >>
  gen_tac >> strip_tac >> conj_tac
  >- (qpat_assum `!D. gas_origin_ptr_path _ _ [] _`
        (qspec_then `DF H` ACCEPT_TAC)) >>
  qexists_tac `v` >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qpat_assum `expr_sim_full_post _ _ _ _ _ H _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [expr_sim_full_post_def]) >>
  qpat_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  qpat_assum `ghost_kept_at 0 _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >>
  `ci_mono sa mid` by metis_tac[ci_mono_lower_value_compile_expr, pairTheory.SND] >>
  `not_fresh_at mid dst` by
    (irule not_fresh_at_mono >> qexists_tac `sa` >> fs[ci_mono_def]) >>
  `FLOOKUP t.vs_allocas oid = SOME (w2n b,type_memory_size tv) /\
   lookup_var dst t = SOME b` by metis_tac[] >>
  `alloca_history fn t` by metis_tac[expr_sim_full_endpoint_fields] >>
  `alloca_inv t` by fs[stmt_state_rel_def] >>
  `alloca_history fn u` by metis_tac[body_full_path_alloca_history] >>
  `stmt_state_rel H ctx fn (ce with ce_vars := FEMPTY) cx ee u` by
    metis_tac[grouped_keyword_store_runtime_state] >>
  `ghost_inv_at (DF H) 0 NONE (ce with ce_vars := FEMPTY) cx ee J tz u` by
    metis_tac[grouped_keyword_store_runtime_ghost] >>
  qpat_assum `typed_copy_state_frame mid _ _ t u`
    (assume_tac o MATCH_MP typed_copy_state_frame_allocas_below_fmp) >>
  `!p. not_fresh_at sa p ==> not_fresh_at mid p` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >>
     fs[ci_mono_def]) >>
  `!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP u.vs_allocas aid = SOME entry` by
    (fs[typed_copy_state_frame_def, venom_state_component_equality]) >>
  `!p w. not_fresh_at sa p /\ lookup_var p s = SOME w ==>
    lookup_var p u = SOME w /\ FLOOKUP J p = FLOOKUP G p /\
    op_taint tz (Var p) = op_taint tn (Var p)` by
    (qpat_assum `typed_copy_state_frame mid _ _ t u`
       (strip_assume_tac o REWRITE_RULE[typed_copy_state_frame_def]) >>
     rpt gen_tac >> strip_tac >>
     `not_fresh_at mid p` by (first_assum irule >> simp[]) >>
     rpt conj_tac
     >- (qpat_assum `!x. not_fresh_at mid x ==> lookup_var x u = _`
           (qspec_then `p` (drule_then SUBST1_TAC)) >>
         first_assum irule >> simp[])
     >- (qpat_assum `!x. not_fresh_at mid x ==> FLOOKUP J x = _ /\ _`
           (qspec_then `p` (drule_then strip_assume_tac)) >> simp[])
     >- (qpat_assum `!x. not_fresh_at mid x ==> FLOOKUP J x = _ /\ _`
           (qspec_then `p` (drule_then strip_assume_tac)) >> simp[])) >>
  `lookup_var dst u = SOME b` by
    (qpat_assum `!p w. not_fresh_at sa p /\ lookup_var p s = SOME w ==> _`
       (qspecl_then [`dst`,`b`] mp_tac) >> simp[]) >>
  `FLOOKUP u.vs_allocas oid = SOME (w2n b,type_memory_size tv)` by
    (qpat_assum `!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==> _`
       (qspecl_then [`oid`,`(w2n b,type_memory_size tv)`] mp_tac) >> simp[]) >>
  asm_rewrite_tac[] >> qx_genl_tac [`aid`,`p`,`old_base`,`n`,`otv`,`x`] >> strip_tac >>
      `FLOOKUP t.vs_allocas aid = SOME (old_base,n) /\
       lookup_var p t = SOME (n2w old_base) /\ ptr_covers G1 tn1 p t n /\
       (!mem. mem_agree_outside tn1.t_mem t.vs_memory mem ==>
         val_in_memory otv x old_base mem)` by
        (mp_tac (Q.INST [`oid` |-> `aid`, `b` |-> `old_base:num`, `tv` |-> `otv`,
            `sb` |-> `mid`, `op` |-> `src`, `lo` |-> `0:num`]
          (INST_TYPE [alpha |-> ``:256``] (SPEC_ALL grouped_keyword_expr_owner_frame))) >>
         asm_rewrite_tac[] >> simp[]) >>
      `not_fresh_at mid p` by (first_assum irule >> simp[]) >>
      qpat_assum `!p. not_fresh_at mid p ==> FLOOKUP J p = _ /\ _`
        (qspec_then `p` (drule_then strip_assume_tac)) >>
      mp_tac (INST [``dst:num`` |-> ``w2n (b:256 word)``]
        (Q.INST [`oid` |-> `aid`, `did` |-> `oid`, `b` |-> `old_base:num`,
        `len` |-> `type_memory_size tv`, `G` |-> `G1`,
        `tn` |-> `tn1`, `G'` |-> `J`, `tn'` |-> `tz`, `tv` |-> `otv`,
        `v` |-> `x`] (SPEC_ALL grouped_keyword_store_owner_frame))) >>
      asm_rewrite_tac[] >> simp[]
QED

Theorem grouped_keyword_omitted_expression:
  ^omitted_expr_inputs ==>
  gas_outcome_full (DF,0,gas_explicit_sites ctx shadow_ctx,ctx,fn,PG)
    (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn)
    ^omitted_expr_store_post
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all runtime_default_expr_full >> strip_tac >>
  irule gas_outcome_full_zero_suffix >> goal_assum (drule_at Any) >> simp[] >>
  rpt gen_tac >> strip_tac >>
  mp_tac (SIMP_RULE bool_ss []
    (Q.INST [`keep` |-> `\t u. T`] (SPEC_ALL grouped_keyword_store_normal_witness))) >>
  asm_rewrite_tac[]
QED

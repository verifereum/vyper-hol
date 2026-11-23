(* Store a linked default into its allocated keyword slot. *)
Theory linkedGroupedKeywordOmitted
Ancestors
  groupedKeywordOmitted groupedKeywordOwners linkedRuntimeDefaultExpression
  gasOutcomeFullModsSource exprSimFullBundleProps
  exprOperandVar exprLoweringProps emitHelperProps typedMemoryCopy
  loweringPosts bodyPtrDefs loweringStateRelDefs typedCopyOriginPtrBase
  bodyPtrMakeArrayCopyStateFrame bodyFullEmptyFrame bodySimFull robustCopyTransportPtr
  gasOutcomeFullCompose bodyFullPathHistory vyperStorageFootprint vyperTypeExprResult vyperTypeExprSoundness
  exprSimSource valueEncodingTyping vyperContext vyperAST vyperTypeContract
  vyperTypeInvariants loweringShapeDefs ptrDiscipline
  venomState venomMemDefs compileEnv finite_map arithmetic

Theorem grouped_keyword_omitted_expression_mods:
  runtime_constant_expr mods e /\ expr_type e = ty /\
  expr_body_pre_mods mods (ce with ce_vars := FEMPTY) cx env e es /\
  lower_value compile_expr (ce with ce_vars := FEMPTY) ty e sa = (src,mid) /\
  local_ptrs_reserved (ce with ce_vars := FEMPTY) sa /\ fn_inst_ids_distinct fn /\
  gas_outcome_full_mods (DF,0,explicit,ctx,fn,PG) mods cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn)
    (expr_sim_full_post (DF,0,NONE,ctx,fn) (ce with ce_vars := FEMPTY)
      cx e (es,sa,mid,s,src,G,tn))
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)) /\
  (if is_word_type ty then emit_void MSTORE [Var dst;src]
   else if is_bytestring_type ty then compile_store_bytestring src (Var dst)
   else emit_void MCOPY [Var dst;src;Lit (n2w (type_memory_bytes ce ty))])
    mid = ((),last) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ env.type_defs = get_tenv cx /\
  type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_size tv + 64 < dimword (:256) /\
  fn_has_code mid last fn /\
  ~ce.ce_is_ctor /\ ce.ce_imm_alloca = NONE /\ ce.ce_return_pc = NONE /\
  not_fresh_at sa dst /\ lookup_var dst s = SOME b /\
  FLOOKUP s.vs_allocas oid = SOME (w2n b,type_memory_size tv) /\
  ptr_covers G tn dst s (type_memory_size tv) ==>
  gas_outcome_full_mods (DF,0,explicit,ctx,fn,PG) mods cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn)
    (\H res ee J tz u.
      ?v. res = INL v /\ value_has_type tv v /\ val_wf tv v /\
          (!mem. mem_agree_outside tz.t_mem u.vs_memory mem ==>
            val_in_memory tv v (w2n b) mem) /\
          lookup_var dst u = SOME b /\ FLOOKUP u.vs_allocas oid =
            SOME (w2n b,type_memory_size tv) /\
          ptr_covers J tz dst u (type_memory_size tv) /\
          (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
            FLOOKUP u.vs_allocas aid = SOME entry) /\
          (!p w. not_fresh_at sa p /\ lookup_var p s = SOME w ==>
            lookup_var p u = SOME w /\ FLOOKUP J p = FLOOKUP G p /\
            op_taint tz (Var p) = op_taint tn (Var p)) /\
          (!aid p old_base n otv x. aid <> oid /\ aid < sa.cs_next_id /\
            FLOOKUP s.vs_allocas aid = SOME (old_base,n) /\
            not_fresh_at sa p /\ lookup_var p s = SOME (n2w old_base) /\
            ptr_covers G tn p s n /\ val_wf otv x /\ val_footprint otv x <= n /\
            (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
              val_in_memory otv x old_base mem) ==>
            !mem. mem_agree_outside tz.t_mem u.vs_memory mem ==>
              val_in_memory otv x old_base mem) /\
          stmt_state_rel H ctx fn (ce with ce_vars := FEMPTY) cx ee u /\
          storage_well_formed_on cx ee (FST H) /\
          ghost_inv_at (DF H) 0 NONE (ce with ce_vars := FEMPTY) cx ee J tz u /\
          ee.scopes = es.scopes /\ expr_sim_inv_mods mods (ce with ce_vars := FEMPTY) cx env ee /\
          alloca_history fn u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
          u.vs_current_bb = last.cs_current_bb /\
          u.vs_inst_idx = LENGTH last.cs_current_insts /\ ~u.vs_halted)
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then assume_tac runtime_default_expr_post_mods >>
  irule gas_outcome_full_mods_zero_suffix >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ _ _
    (\H res ee G1 tn1 u. _ /\ ~u.vs_halted /\ _) _` (irule_at Any) >> simp[] >>
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 H0 ee.storage_trace` by
    fs[Abbr `H0`, storage_trace_domain_def] >>
  first_assum (drule_then strip_assume_tac) >>
  qpat_assum `expr_sim_full_post _ _ _ _ _ H0 _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [expr_sim_full_post_def]) >>
  `expr_result_typed env e (Value v)` by
    (qpat_assum `!vv. res = INL vv ==> _` (qspec_then `v` match_mp_tac) >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `res = INL v` SUBST_ALL_TAC >>
  mp_tac (Q.INST [`H` |-> `H0`, `v` |-> `v`, `G1` |-> `G1`, `tn1` |-> `tn1`,
    `explicit` |-> `explicit`]
    (INST_TYPE [alpha |-> ``:256``] (SPEC_ALL grouped_keyword_omitted_store))) >>
  impl_tac >-
    (asm_rewrite_tac[] >> simp[expr_sim_full_post_def] >>
     qexists_tac `v` >> asm_rewrite_tac[]) >>
  disch_then (qx_choosel_then [`u`,`J`,`tz`] strip_assume_tac) >>
  qexistsl_tac [`u`,`J`,`tz`] >> gen_tac >> strip_tac >>
  conj_tac
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

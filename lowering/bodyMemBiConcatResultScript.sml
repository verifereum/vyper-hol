(* The source continuation after concat's operand-list evaluation. *)
Theory bodyMemBiConcatResult
Ancestors
  protectedAllocationFrame bodyMemBiConcatPost loweringStateRelDefs
  bodyMemBiConcatArgs bodyMemBiConcatPrefix bodyMemBiConcatFragments
  bodyMemBiECRecoverCompose exprSimConcatResult gasSummary gasOutcome
  fragGasMode fragGasPathMem exprSimMemDefs vyperState vyperValueOperation
  exprSimWordArgs exprSimDefs list exprSimHyps exprSimHypsDefs
  vyperTyping vyperTypeSystem vyperTypeInvariants exprLowering exprLoweringProps
  allocLimits compileEnv exprSimConcatArgs freshWrites words rich_list
  emitHelperProps context vyperContext exprSimSource fragExec bodyDeclMemoryCompose
  vyperEvalExprPreservesScopesDom venomState venomMemDefs allocaHistoryFragment
  exprSimConcatPath exprSimUint2Str locatedValueStoreBound

Theorem concat_result_summary_mem[local]:
  evaluate_concat n vs = INL v /\
  gas_path_mem ctx func s 0 (OK t) /\
  Q (INL (Value v)) (ee with gas_obs := []) t ==>
  gas_summary_at T (ctx,func) []
    (\st. ((case evaluate_concat n vs of INL v => INL (Value v)
            | INR err => INR (Error err)), st)) (ee,s) Q R
Proof
  strip_tac >> rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INL (Value v)`, `ee`, `OK t`] >>
  simp[gas_marked_exec_def, gas_marked_path_def, gas_explicit_def]
QED

Theorem concat_result_vv_sim_mem:
  body_inv tops ctx cenv cx /\ body_exprs_mem_ok cx args /\
  expr_body_pre cenv cx env (Builtin ann (Concat n) args) es ==>
  expr_vv_sim_mem ctx func cenv cx ty (Builtin ann (Concat n) args) es
Proof
  strip_tac >>
  `!e st. MEM e args /\ expr_sim_inv cenv cx env st ==>
          expr_body_pre cenv cx env e st` by
    (rpt strip_tac >> drule expr_body_pre_builtin_arg >>
     simp[] >> disch_then irule >> simp[]) >>
  `expr_sim_inv cenv cx env es /\ well_typed_expr env (Builtin ann (Concat n) args) /\
   alloc_limits_expr cenv (Builtin ann (Concat n) args)` by fs[expr_body_pre_def] >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `2 <= LENGTH args /\ SUM (MAP bytelike_type_bound (MAP expr_type args)) <= n /\
   well_formed_type env.type_defs ann` by
    (qpat_x_assum `well_typed_expr _ _` mp_tac >>
     simp[Once well_typed_expr_def, well_typed_builtin_app_def] >>
     rpt strip_tac >> fs[]) >>
  Q.SUBGOAL_THEN
   `(ann = BaseT (BytesT (Dynamic n)) /\
    EVERY (\t. ?bd. t = BaseT (BytesT bd)) (MAP expr_type args)) \/
   (ann = BaseT (StringT n) /\
    EVERY (\t. ?m. t = BaseT (StringT m)) (MAP expr_type args))` assume_tac
  >-
    (qpat_x_assum `well_typed_expr _ _` mp_tac >>
     simp[Once well_typed_expr_def, well_typed_builtin_app_def] >>
     rpt strip_tac >> fs[]) >>
  `?tvr. evaluate_type (get_tenv cx) ann = SOME tvr` by
    (qpat_x_assum `well_formed_type _ _` mp_tac >>
     qpat_assum `env.type_defs = _`
       (fn th => simp[th, well_formed_type_def, optionTheory.IS_SOME_EXISTS])) >>
  `EVERY (\e. is_bytestring_type (expr_type e) \/
              ?m. expr_type e = BaseT (BytesT (Fixed m))) args` by
    (qpat_assum `(_ /\ _) \/ (_ /\ _)` strip_assume_tac >>
     fs[EVERY_MEM, MEM_MAP, PULL_EXISTS] >> rpt strip_tac >> res_tac >>
     fs[is_bytestring_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >> fs[is_bytestring_type_def]) >>
  `concat_alloc_size (MAP expr_type args) < 2 ** 64` by
    (qpat_x_assum `alloc_limits_expr _ _` mp_tac >> simp[alloc_limits_expr_def]) >>
  rewrite_tac[expr_vv_sim_mem_def] >> rpt gen_tac >> strip_tac >>
  drule concat_compile_shape >> strip_tac >> suspend "prefix"
QED

Resume concat_result_vv_sim_mem[prefix]:
  qabbrev_tac `bsz = concat_alloc_size (MAP expr_type args)` >>
  `bsz < dimword (:256)` by
    (irule arithmeticTheory.LESS_LESS_EQ_TRANS >> qexists_tac `2 ** 64` >>
     simp[wordsTheory.dimword_def]) >>
  `32 + SUM (MAP concat_payload_capacity (MAP expr_type args)) <= bsz /\
   32 + concat_data_bound 0 (MAP expr_type args) <= bsz` by
    simp[Abbr `bsz`, concat_alloc_size_bounds] >>
  drule_all concat_prefix_code >> strip_tac >>
  `cs_extends sa s4` by
    (irule cs_extends_same_block >> simp[]) >>
  `ci_mono s4 s5` by
    (qpat_assum `compile_concat _ _ _ _ _ _ s4 = _` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     metis_tac[ci_mono_compile_concat_cfn, cj 1 compile_expr_ci_mono,
               pairTheory.SND]) >>
  `cs_extends s4 s5 /\ s4.cs_next_var <= s5.cs_next_var /\
   s4.cs_next_id <= s5.cs_next_id` by fs[ci_mono_def] >>
  qpat_x_assum `buf.buf_operand = _`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >> assume_tac th) >>
  qpat_x_assum `ob.buf_operand = _`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >> assume_tac th) >>
  drule_all concat_suffix_code >> strip_tac >>
  `cs_extends s5 sb` by (irule cs_extends_same_block >> simp[]) >>
  `cs_extends s4 sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa s4 func /\ fn_has_code s4 sb func` by
    (irule fn_has_code_split >> simp[]) >>
  `fn_has_code s4 s5 func /\ fn_has_code s5 sb func` by
    (irule fn_has_code_split >> simp[]) >>
  qpat_assum `buf.buf_operand = _`
    (fn th => mp_tac (REWRITE_RULE [th] concat_prefix_path_mem)) >>
  qpat_assum `ob.buf_operand = _`
    (fn th => PURE_REWRITE_TAC [th]) >>
  disch_then drule_all >>
  disch_then (qx_choosel_then [`t`, `B`, `ow`, `binst`, `oinst`]
    (MAP_EVERY assume_tac o CONJUNCTS)) >> suspend "operands"
QED

Resume concat_result_vv_sim_mem[operands]:
  qpat_x_assum `d = _` SUBST_ALL_TAC >>
  `local_ptrs_reserved cenv s4` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `not_fresh_at s4 (STRING #"%" (toString (sa.cs_next_var + 1))) /\
   not_fresh_at s4 (STRING #"%" (toString (sa.cs_next_var + 2)))` by
    simp[not_fresh_at_def] >>
  qpat_assum `compile_concat _ _ _ _ _ _ s4 = _`
    (mp_then Any mp_tac concat_args_sim_mem) >>
  disch_then (qspecl_then [`0`, `0`, `tops`, `ctx`, `func`, `cx`, `env`, `es`,
    `t`, `ow`, `binst`, `B`, `bsz`, `oinst`] mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[] >> simp[])) >>
  strip_tac >> suspend "bind"
QED

Resume concat_result_vv_sim_mem[bind]:
  qpat_x_assum `vv = _` SUBST_ALL_TAC >>
  irule gas_outcome_zero_prefix_mem >> qexists_tac `t` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qspecl_then [`cx`, `ann`, `n`, `args`] mp_tac eval_expr_concat_bind >>
  (impl_tac >- first_assum ACCEPT_TAC) >> disch_then SUBST1_TAC >>
  irule ecrecover_eval_exprs_suffix_mem >>
  conj_tac >-
    (simp[wb_args_exit_def] >> rpt gen_tac >>
     Cases_on `exc` >> Cases_on `r` >> simp[expr_exit_def] >>
     rename1 `Error err` >> Cases_on `err` >> simp[expr_exit_def]) >>
  `!(rr : value list + exception) ee r.
     (?exc. rr = INR exc /\ expr_exit (INR exc : eval_result + exception) r) =
     wb_args_exit rr r` by
    (rpt gen_tac >> Cases_on `rr` >> simp[wb_args_exit_def] >>
     rename1 `INR exc` >> Cases_on `exc` >> Cases_on `r` >>
     simp[expr_exit_def] >> rename1 `Error err` >> Cases_on `err` >>
     simp[expr_exit_def]) >>
  qmatch_asmsub_abbrev_tac
    `gas_outcome _ _ _ (eval_exprs _ _) _ Post _` >>
  qexists_tac `\vs ee tt. Post (INL vs) ee tt` >> reverse conj_tac
  >- (qpat_x_assum `gas_outcome _ _ _ (eval_exprs _ _) _ _ _` mp_tac >>
      simp[Abbr `Post`]) >>
  simp[Abbr `Post`] >> rpt gen_tac >> strip_tac >> suspend "normal"
QED
Resume concat_result_vv_sim_mem[normal]:
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (qpat_assum `eval_exprs _ _ _ = _` mp_tac >> rpt (pop_assum kall_tac) >>
     strip_tac >> drule eval_exprs_preserves_scopes_dom >> simp[]) >>
  qspecl_then [`ann`, `n`, `MAP expr_type args`, `vs`, `get_tenv cx`, `tvr`]
    mp_tac concat_typed_result >>
  (impl_tac >- (asm_rewrite_tac[] >> simp[LIST_REL_MAP1, combinTheory.o_DEF])) >>
  disch_then (qx_choose_then `v` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  suspend "suffix"
QED

Resume concat_result_vv_sim_mem[suffix]:
  `B < dimword (:256) /\ 32 <= bsz` by decide_tac >>
  `w2n (n2w B : bytes32) = B` by simp[] >>
  `not_fresh_at s4 (STRING #"%" (toString sa.cs_next_var))` by
    simp[not_fresh_at_def] >>
  `not_fresh_at s5 (STRING #"%" (toString sa.cs_next_var))` by
    (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `s4` >> simp[]) >>
  `lookup_var (STRING #"%" (toString sa.cs_next_var)) t' = SOME (n2w B) /\
   lookup_var (STRING #"%" (toString (sa.cs_next_var + 2))) t' = SOME ow` by
    (conj_tac >> first_x_assum irule >> simp[]) >>
  `w2n ow + 32 <= t'.vs_alloca_next /\
   w2n (n2w B : bytes32) + 32 <= t'.vs_alloca_next` by
    (simp[] >> decide_tac) >>
  qpat_assum `emit_op MLOAD _ s5 = _`
    (mp_then Any mp_tac concat_suffix_path_mem) >>
  disch_then drule_all >>
  disch_then (qspec_then `ctx` mp_tac) >>
  qpat_assum `w2n (n2w B : bytes32) = B` (fn th => rewrite_tac[th]) >>
  disch_tac >> suspend "post"
QED

Resume concat_result_vv_sim_mem[post]:
  qpat_x_assum `gas_outcome _ _ _ (eval_exprs _ _) _ _ _` kall_tac >>
  qpat_x_assum `gas_path_mem _ _ s0 _ _` kall_tac >>
  qmatch_asmsub_abbrev_tac `gas_path_mem ctx func t' 0 (OK tf)` >>
  qexists_tac `[]` >> irule concat_result_summary_mem >>
  qexists_tac `tf` >> asm_rewrite_tac[] >>
  `ee with gas_obs := [] = ee` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  simp[] >> suspend "finalpost"
QED

Resume concat_result_vv_sim_mem[finalpost]:
  `alloca_inv t'` by fs[stmt_state_rel_def] >>
  `?bb. lookup_block t'.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts s5 sb)
          (DROP t'.vs_inst_idx bb.bb_instructions)` by
    (irule concat_code_prefix >> simp[]) >>
  `?rest. DROP t'.vs_inst_idx bb.bb_instructions =
          emitted_insts s5 sb ++ rest` by metis_tac[IS_PREFIX_APPEND] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts s5 sb)` by
    simp[venomInstTheory.is_terminator_def] >>
  drule_all concat_suffix_run >>
  qpat_assum `w2n (n2w B : bytes32) = B` (fn th => rewrite_tac[th]) >>
  strip_tac >> drule_all alloca_history_run_inst_seq >>
  disch_tac >>
  `alloca_history func tf` by
    (qpat_x_assum `alloca_history func (_ with vs_inst_idx := _)` mp_tac >>
     simp[Abbr `tf`]) >>
  `tf.vs_current_bb = s5.cs_current_bb /\
   tf.vs_inst_idx = LENGTH s5.cs_current_insts + 2 /\
   alloca_history func tf /\ s0.vs_alloca_next <= tf.vs_alloca_next` by
    (simp[Abbr `tf`, mstore_def, update_var_def] >> decide_tac) >>
  asm_rewrite_tac[] >>
  `wb_frame cenv es es sa s0 t` by
    (irule (INST_TYPE [alpha |-> ``:256``] concat_prefix_frame) >> reverse (rpt conj_tac)
     >- first_assum ACCEPT_TAC
     >- (rpt strip_tac >> first_x_assum drule >> simp[])
     >- (qexists_tac `ow` >> asm_rewrite_tac[] >>
         qpat_x_assum `!name lb lsz. local_region _ _ t _ _ _ ==> _` mp_tac >>
         qpat_x_assum `!aid b len. aid < sa.cs_next_id /\ FLOOKUP s0.vs_allocas aid = _ ==> _` mp_tac >>
         rpt (pop_assum kall_tac) >> metis_tac[arithmeticTheory.ADD_COMM]) >>
     rpt strip_tac >> first_x_assum drule >> simp[]) >>
  suspend "frame"
QED

Resume concat_result_vv_sim_mem[frame]:
  `wb_frame cenv es ee sa s0 t'` by
    (irule (INST_TYPE [alpha |-> ``:256``] concat_prefix_list_frame) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     reverse conj_tac
     >- (qexistsl_tac [`ctx`, `cx`, `func`] >> first_assum ACCEPT_TAC) >>
     qexistsl_tac [`B`, `bsz`, `es`, `ow`, `s4`, `t`] >>
     asm_rewrite_tac[] >> simp[] >> first_assum ACCEPT_TAC) >>
  once_rewrite_tac[vv_post_located_mk_ptr, vv_store_bound_located_mk_ptr] >>
  qpat_assum `buf.buf_operand = _`
    (fn th => pure_rewrite_tac[base_ptr_def, th]) >>
  simp[NoAsms] >>
  qpat_assum `Abbrev (tf = _)`
    (fn th => pure_rewrite_tac[REWRITE_RULE[markerTheory.Abbrev_def] th]) >>
  pure_rewrite_tac[vyperASTTheory.expr_type_def] >>
  irule (BETA_RULE (REWRITE_RULE[LET_THM, vyperASTTheory.expr_type_def,
                                 loweringPostsTheory.post_value_type_def]
    (Q.INST [`e` |-> `Builtin ann (Concat n) args`] (SPEC_ALL concat_suffix_post)))) >>
  asm_rewrite_tac[] >> suspend "suffix_conditions"
QED

Resume concat_result_vv_sim_mem[suffix_conditions]:
  conj_tac
  >- (rpt strip_tac >> fs[not_fresh_at_def] >>
      first_x_assum irule >> decide_tac) >>
  `FLOOKUP t'.vs_allocas sa.cs_next_id = SOME (B,bsz)` by metis_tac[] >>
  conj_tac
  >- (rpt strip_tac >>
      `aid <> sa.cs_next_id` by decide_tac >>
      qpat_x_assum `alloca_inv t'` mp_tac >>
      simp[alloca_inv_def, allocas_non_overlapping_def] >>
      disch_then (mp_tac o CONJUNCT1) >>
      disch_then (qspecl_then [`sa.cs_next_id`, `aid`, `B`, `bsz`, `p`, `n'`] mp_tac) >>
      simp[] >> decide_tac) >>
  conj_tac
  >- (qpat_assum `not_fresh_at s4 (STRING #"%" (toString sa.cs_next_var))` mp_tac >>
      simp[not_fresh_at_def] >> disch_then irule >> decide_tac) >>
  suspend "suffix_value"

QED

Resume concat_result_vv_sim_mem[suffix_value]:
  reverse conj_tac
  >- (irule local_ptrs_reserved_fresh >> qexists_tac `s4` >> simp[]) >>
  qmatch_asmsub_abbrev_tac `val_footprint tvr v = 32 + LENGTH bytes` >>
  qexistsl_tac [`bsz`, `bytes`, `binst`, `tvr`] >>
  asm_rewrite_tac[] >> simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      `local_region cenv es.scopes t name p n'` by
        (irule exprSimPropsTheory.local_region_frame >> conj_tac
         >- (qexists_tac `func` >>
             qpat_assum `stmt_state_rel _ _ _ _ es t` mp_tac >>
             pure_rewrite_tac[stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def] >>
             strip_tac >> first_assum ACCEPT_TAC) >>
         qexistsl_tac [`s4`, `ee.scopes`, `t'`] >>
         asm_rewrite_tac[]) >>
      qpat_x_assum `!name lb lsz. local_region _ _ t _ _ _ ==> _` drule >>
      decide_tac) >>
  suspend "suffix_sizes"
QED

Resume concat_result_vv_sim_mem[suffix_sizes]:
  reverse conj_tac
  >- suspend "suffix_store_size" >>
  qpat_x_assum `(_ /\ _) \/ (_ /\ _)` strip_assume_tac >>
  simp[lowered_value_type_def, concat_buffer_type_def, MAP_MAP_o,
       vyperValueTheory.evaluate_type_def, valueEncodingTheory.type_memory_size_def,
       Abbr `bsz`, concat_alloc_size_def, vfmConstantsTheory.word_size_def,
       AllCaseEqs()]
QED

Resume concat_result_vv_sim_mem[suffix_store_size]:
  reverse conj_tac >- simp[valueEncodingDefsTheory.mem_bytes_at_def] >>
  `LIST_REL (\t v. ?tv. evaluate_type (get_tenv cx) t = SOME tv /\
                          value_has_type tv v) (MAP expr_type args) vs` by
    simp[LIST_REL_MAP1, combinTheory.o_DEF] >>
  qpat_x_assum `(_ /\ _) \/ (_ /\ _)` strip_assume_tac
  >- (drule_all (Q.INST [`ts` |-> `MAP expr_type args`]
        (SPEC_ALL exprSimConcatSourceTheory.evaluate_concat_typed_bytes)
        |> REWRITE_RULE[LENGTH_MAP]) >>
      strip_tac >> suspend "bytes_size") >>
  drule_all (Q.INST [`ts` |-> `MAP expr_type args`]
    (SPEC_ALL exprSimConcatSourceTheory.evaluate_concat_typed_string)
    |> REWRITE_RULE[LENGTH_MAP]) >>
  strip_tac >> suspend "string_size"
QED

Resume concat_result_vv_sim_mem[bytes_size]:
  `v = BytesV (FLAT bss)` by metis_tac[sumTheory.INL_11] >>
  qpat_x_assum `v = _` SUBST_ALL_TAC >>
  qpat_x_assum `evaluate_type _ ann = SOME tvr` mp_tac >>
  simp[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >> strip_tac >>
  qpat_x_assum `_ = tvr` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `val_footprint _ _ = _` mp_tac >>
  simp[loweringPostsTheory.val_footprint_def] >> strip_tac >>
  `word_size (LENGTH (FLAT bss)) <=
     word_size (SUM (MAP concat_payload_capacity (MAP expr_type args)))` by
    (irule exprSimHypsTheory.word_size_monotone >> decide_tac) >>
  qpat_x_assum `word_size _ <= word_size _` mp_tac >>
  simp[exprSimPropsTheory.val_store_size_def, Abbr `bsz`, concat_alloc_size_def,
       vfmConstantsTheory.word_size_def]
QED
Resume concat_result_vv_sim_mem[string_size]:
  `v = StringV (FLAT ss)` by metis_tac[sumTheory.INL_11] >>
  qpat_x_assum `v = _` SUBST_ALL_TAC >>
  qpat_x_assum `evaluate_type _ ann = SOME tvr` mp_tac >>
  simp[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >> strip_tac >>
  qpat_x_assum `_ = tvr` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `val_footprint _ _ = _` mp_tac >>
  simp[loweringPostsTheory.val_footprint_def] >> strip_tac >>
  `word_size (LENGTH (FLAT ss)) <=
     word_size (SUM (MAP concat_payload_capacity (MAP expr_type args)))` by
    (irule exprSimHypsTheory.word_size_monotone >> decide_tac) >>
  qpat_x_assum `word_size _ <= word_size _` mp_tac >>
  simp[exprSimPropsTheory.val_store_size_def, Abbr `bsz`, concat_alloc_size_def,
       vfmConstantsTheory.word_size_def]
QED

Finalise concat_result_vv_sim_mem

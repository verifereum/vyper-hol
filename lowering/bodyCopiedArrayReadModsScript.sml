(* Consume the saved memory element at the ordinary value boundary. *)
Theory bodyCopiedArrayReadMods
Ancestors
  bodyCopiedArrayCutDefsMods bodySubscriptArrayRouteDefsMods
  bodyIfExpWordReadMods bodyLocalCopyPhysicalRhsMods
  bodyInvSplit bodyFullPostsMods exprSimUnwrap exprSimUnwrapProps
  exprSimMemorySource gasShadowCompile gasShadowState gasOutcomeFullBindMods
  gasOutcomeFullPostMods gasExemptCertMods haltExitProj exprBodyPreProps
  vyperTypeEvalCaseProofs vyperStorageTrace vyperStorageFootprint
  exprLowering exprLoweringProps loweringPosts compileEnv fragExec
  bodyPtrDefs exprSimDefs vyperAST vyperInterpreter vyperState
  exprSimHypsDefs bodySimStmtFacts vyperTypeExprSoundness stmtSimProps context fragGasOriginPtr
  exprPtrUnwrapLoad exprPtrUnwrapFacts exprPtrCtorImmStore
  fragGasOriginPtrDead exprSimProps exprOperandVar freshWrites
  valueEncodingDefs venomState venomInst venomExecSemantics finite_map
  loweringStateRelDefs ptrDiscipline bodyFullUnwrapRun pred_set
  exprSimBopRestWordLoadPath exprSimBopRestWordLoadSafety
  allocasBelowFmpUpdatesProps stateRelProj bodyFullShadowBodyInv emitHelperProps exprSimMemDefs
  bodyPtrSignedConvertSourceFrame
Libs monadsyntax

Theorem copied_read_compile_cuts[local]:
  lower_value compile_expr ce ty e sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr e) sha = (op,shb) /\
  gas_shadow_state sa sha /\ fn_has_code sa sb fn /\ fn_has_code sha shb shfn ==>
  ?vv sm shm.
    compile_expr ce ty e sa = (vv,sm) /\
    compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr e) sha = (vv,shm) /\
    gas_shadow_state sm shm /\ fn_has_code sa sm fn /\ fn_has_code sm sb fn /\
    fn_has_code sha shm shfn /\ sa.cs_next_var <= sm.cs_next_var /\
    unwrap_value ce vv sm = (op,sb)
Proof
  strip_tac >> Cases_on `compile_expr ce ty e sa` >>
  rename1 `compile_expr ce ty e sa = (vv,sm)` >>
  `gas_shadow_compiles (compile_expr ce ty e)
    (compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr e))` by
    irule (cj 1 gas_shadow_compile_expr_env |> SPEC_ALL |>
           Q.INST [`shadow` |-> `T`] |> REWRITE_RULE [COND_CLAUSES]) >>
  qpat_x_assum `gas_shadow_compiles _ _`
    (qspecl_then [`sa`,`sha`] mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
  Cases_on `compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr e) sha` >>
  simp[] >> strip_tac >>
  rename1 `compile_expr _ _ (gas_shadow_expr _) sha = (_,shm)` >>
  gvs[] >>
  fs[lower_value_def, comp_bind_def] >>
  `cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var` by
    (qpat_assum `compile_expr ce ty e sa = _`
       (mp_tac o MATCH_MP compile_expr_extends) >> simp[]) >>
  `cs_extends sha shm` by
    (qpat_assum `compile_expr _ _ (gas_shadow_expr _) sha = _`
       (mp_tac o MATCH_MP compile_expr_extends) >> simp[]) >>
  `cs_extends sm sb` by
    (qpat_assum `unwrap_value _ _ sm = _` (mp_tac o MATCH_MP unwrap_value_extends) >> simp[]) >>
  `cs_extends shm shb` by
    (qpat_assum `unwrap_value _ _ shm = _` (mp_tac o MATCH_MP unwrap_value_extends) >> simp[]) >>
  qspecl_then [`sa`,`sm`,`sb`,`fn`] mp_tac fn_has_code_split >> simp[] >>
  qspecl_then [`sha`,`shm`,`shb`,`shfn`] mp_tac fn_has_code_split >> simp[]
QED

Theorem copied_read_source_type[local]:
  expr_body_pre_mods mods ce cx env (Subscript ann obj idx) es /\
  eval_expr cx (Subscript ann obj idx) (es with gas_obs := gs) = (INL tv,ee) /\
  read_result cx tv ee = (INL v,ee) ==>
  ?rt. evaluate_type (get_tenv cx) ann = SOME rt /\ value_has_type rt v
Proof
  strip_tac >>
  `(expr_body_pre_mods mods ce cx env (Subscript ann obj idx) (es with gas_obs := gs) <=>
    expr_body_pre_mods mods ce cx env (Subscript ann obj idx) es)` by
    simp_tac (srw_ss()) [expr_body_pre_mods_def,expr_sim_inv_mods_def] >>
  `expr_body_pre_mods mods ce cx env (Subscript ann obj idx) (es with gas_obs := gs)` by simp[] >>
  `bind (eval_expr cx (Subscript ann obj idx)) (read_result cx)
     (es with gas_obs := gs) = (INL v,ee)` by simp[bind_def] >>
  drule_all_then strip_assume_tac (REWRITE_RULE [ETA_THM] expr_body_pre_eval_mods) >>
  `value_runtime_typed env ann v` by
    (first_x_assum (qspec_then `v` mp_tac) >> simp[expr_type_def]) >>
  `env.type_defs = get_tenv cx` by
    (irule env_consistent_type_defs_get_tenv >> qexists_tac `ee` >>
     drule expr_sim_inv_mods_env >> simp[]) >>
  gvs[value_runtime_typed_def]
QED

Theorem copied_read_identity[local]:
  vv_post_mods H ctx fn ce cx (Subscript ann obj idx) es sa sb s0 ee tv
    (LocatedValue ann (mk_ptr dst LocMemory)) s /\
  vv_store_bound cx ann (lowered_value_type ce (Subscript ann obj idx)) ee tv
    (LocatedValue ann (mk_ptr dst LocMemory)) s /\
  ptr_vv_ok cx ann tv (LocatedValue ann (mk_ptr dst LocMemory)) ee G tn s /\
  ~is_word_type ann /\ ~s.vs_halted /\ read_result cx tv ee = (INL v,ee) ==>
  expr_post_mods H ctx fn ce cx (Subscript ann obj idx) es sa sb s0 ee v dst s /\
  expr_store_bound cx ann v dst s /\ ptr_val_ok cx ann v dst G tn s
Proof
  strip_tac >>
  qpat_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_then Any mp_tac (local_copy_rhs_identity_unwrap_mods |>
       Q.INST [`e` |-> `Subscript ann obj idx`, `op` |-> `dst`, `b` |-> `sb`] |>
       REWRITE_RULE [post_value_type_def,expr_type_def])) >>
  simp[mk_ptr_def,unwrap_value_def,comp_return_def] >>
  disch_then (qspecl_then [`tn`,`0`,`{}`,`ARB`,`G`,`ARB`] mp_tac) >>
  fs[mk_ptr_def]
QED

(* The load changes only the destination register and the instruction cursor. *)
val read_word_frame = ``
  u = s with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|> /\
  (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s /\
         FLOOKUP (Gf : string |-> num # num) x = FLOOKUP G x /\
         op_taint tf (Var x) = op_taint tn (Var x)) /\
  tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
  tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm``;

Theorem copied_read_word_ghost[local]:
  ghost_inv_at_mods D lo d ce cx ee G tn s /\ local_ptrs_reserved ce sm /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  ^read_word_frame ==> ghost_inv_at_mods D lo d ce cx ee Gf tf u
Proof
  strip_tac >>
  `!p sz. not_fresh_at sm p /\ ptr_covers G tn p s sz ==>
          ptr_covers Gf tf p u sz` by (rw[ptr_covers_def] >> metis_tac[]) >>
  `u.vs_memory = s.vs_memory /\ u.vs_call_ctx = s.vs_call_ctx /\
   u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
   u.vs_immutables = s.vs_immutables /\ u.vs_allocas = s.vs_allocas /\
   u.vs_alloca_next = s.vs_alloca_next` by
    (rpt conj_tac >> qpat_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>`
       (fn th => simp[Once th])) >>
  fs[ghost_inv_at_mods_def,stor_taint_ok_at_def,allocas_from_def] >>
  rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `not_fresh_at sm p` by metis_tac[local_ptrs_reserved_def] >>
      first_x_assum drule_all >> metis_tac[])
  >- (Cases_on `d` >> gvs[return_buf_ptr_def] >>
      rename1 `return_buf_ptr (SOME rb)` >> PairCases_on `rb` >>
      gvs[return_buf_ptr_def] >> metis_tac[]) >>
  rpt strip_tac >> gvs[local_ptrs_reserved_def] >> metis_tac[]
QED

Theorem copied_read_word_immutables[local]:
  immutable_frame_mods fn ce cx ee s /\ local_ptrs_reserved ce sm /\
  u = s with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|> /\
  (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s) ==>
  immutable_frame_mods fn ce cx ee u
Proof
  strip_tac >>
  `u.vs_memory = s.vs_memory /\ u.vs_data_section = s.vs_data_section /\
   u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next` by
    (rpt conj_tac >> qpat_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>`
       (fn th => simp[Once th])) >>
  simp[immutable_frame_mods_def] >> conj_tac
  >- (fs[immutable_frame_mods_def,immutables_rel_mods_def,immutables_rel_def] >>
      first_assum ACCEPT_TAC) >>
  fs[immutable_frame_mods_def,immutable_alloca_sep_mods_def] >>
  rpt strip_tac >> irule immutable_alloca_sep_fields >> qexistsl [`s`,`ee`] >>
  simp[] >> rpt strip_tac >> qexists `id` >>
  qmatch_asmsub_rename_tac `local_region (ce with ce_module := src) _ _ _ _ _` >>
  `local_region (ce with ce_module := src) ee.scopes u id b sz <=>
   local_region (ce with ce_module := src) ee.scopes s id b sz` by
    (irule local_region_lookup_cong >> simp[] >> metis_tac[local_ptrs_reserved_def]) >>
  gs[]
QED

Theorem copied_read_memory_vv_post[local]:
  vv_post_mods H ctx fn ce cx e es sa sm s0 ee tv
    (LocatedValue ann (mk_ptr dst LocMemory)) s ==>
  vv_post H ctx fn ce cx e es sa sm s0 ee tv (LocatedValue ann (mk_ptr dst LocMemory)) s
Proof
  simp[vv_post_mods_def,vv_holds_mods_def,mk_ptr_def] >> strip_tac >>
  `vv_place_ptr ce cx ee s tv (LocatedValue ann (mk_ptr dst LocMemory))` by
    (Cases_on `tv` >> gvs[vv_place_ptr_mods_def,vv_place_ptr_def,mk_ptr_def] >>
     rename1 `PlaceR pl` >> Cases_on `pl` >> gvs[vv_place_ptr_mods_def,vv_place_ptr_def]) >>
  rewrite_tac[vv_post_def,mk_ptr_def] >> fs[mk_ptr_def] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

val no_dead = ``<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>``;

Theorem copied_read_word_packet[local]:
  emit_op MLOAD [Var src] sm = (op,sb) /\
  ptr_covers G tn src s 32 /\ lookup_var src s = SOME w /\
  (!i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn.t_mem) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?q Gf tf.
    run_inst_seq (emitted_insts sm sb) s = OK q /\
    inst_seq_ptr ^no_dead lo ctx fn PG G tn (emitted_insts sm sb) s Gf tf /\
    eval_operand op q = SOME (mload (w2n w) s) /\
    op_taint tf op = {} /\ op_prov Gf op = NONE /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. not_fresh_at sm x ==> lookup_var x q = lookup_var x s /\
         FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_then strip_assume_tac emitted_insts_emit_op >>
  qabbrev_tac `out = STRING #"%" (toString sm.cs_next_var)` >>
  qabbrev_tac `q = update_var out (mload (w2n w) s) s` >>
  `run_inst_seq [mk_inst sm.cs_next_id MLOAD [Var src] [out]] s = OK q` by
    simp[Abbr `q`,run_inst_seq_def,mk_inst_def,step_inst_base_opcode_eqs,
         exec_read1_def,eval_operand_def] >>
  `!x. not_fresh_at sm x ==> x <> out` by
    (simp[Abbr `out`,not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  qpat_assum `run_inst_seq [_] s = OK q` (mp_then Any mp_tac ctor_mload_segment) >>
  disch_then (qspecl_then [`w`,`tn`,`lo`,`fn`,`ctx`,`PG`,`not_fresh_at sm`,`G`,`^no_dead`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  `mem_word_taint tn.t_mem (w2n w) = {}` by
    (simp[mem_word_taint_def,EXTENSION] >> gen_tac >> Cases_on `x < 32` >> simp[] >>
     qpat_assum `!i. _ ==> i NOTIN tn.t_mem` (qspec_then `x + w2n w` mp_tac) >>
     `w2n w <= x + w2n w /\ x + w2n w < w2n w + 32` by decide_tac >> simp[]) >>
  `s with vs_inst_idx := s.vs_inst_idx = s` by simp[venom_state_component_equality] >>
  qexistsl [`q`,`Gf`,`tnf`] >>
  qpat_assum `s with vs_inst_idx := s.vs_inst_idx = s` (fn eq =>
    qpat_assum `!k. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
      (qspec_then `s.vs_inst_idx` (assume_tac o PURE_REWRITE_RULE [eq]))) >>
  simp[Abbr `q`,eval_operand_def,update_var_def,lookup_var_def,FLOOKUP_UPDATE] >>
  rpt strip_tac >> `x <> out` by metis_tac[] >> simp[]
QED

Theorem copied_read_word_run[local]:
  is_word_type ann /\ post_value_type ce e = ann /\
  evaluate_type (get_tenv cx) ann = SOME rt /\ value_has_type rt v /\
  read_result cx tv ee = (INL v,ee) /\
  vv_post_mods H ctx fn ce cx e es sa sm s0 ee tv (LocatedValue ann (mk_ptr dst LocMemory)) s /\
  vv_store_bound cx ann (lowered_value_type ce e) ee tv (LocatedValue ann (mk_ptr dst LocMemory)) s /\
  ptr_vv_ok cx ann tv (LocatedValue ann (mk_ptr dst LocMemory)) ee G tn s /\
  unwrap_value ce (LocatedValue ann (mk_ptr dst LocMemory)) sm = (op,sb) /\
  fn_has_code sm sb fn /\ fn_inst_ids_distinct fn /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  alloca_history fn s /\ allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?u Gf tf. (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK u,Gf,tf)) /\
    eval_operand op u = SOME (typed_val_to_w256 rt v) /\
    op_taint tf op = {} /\ op_prov Gf op = NONE /\ alloca_history fn u /\
    u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\ ^read_word_frame
Proof
  strip_tac >> drule_then assume_tac copied_read_memory_vv_post >>
  `!v'. read_result cx tv ee = (INL v',ee) ==> value_has_type rt v'` by simp[] >>
  qpat_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_then Any mp_tac unwrap_memory_word_input) >>
  simp[mk_ptr_def] >> disch_then (qspecl_then [`tn`,`G`] mp_tac) >>
  fs[mk_ptr_def] >> strip_tac >>
  qpat_x_assum `dst = Var src` SUBST_ALL_TAC >>
  `emit_op MLOAD [Var src] sm = (op,sb)` by
    (qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
     simp[unwrap_value_def,compile_ptr_load_def,mk_ptr_def]) >>
  `w2n w + 32 <= s.vs_alloca_next` by
    (drule_all_then (qspec_then `v` strip_assume_tac) word_value_memory_extent >>
     qpat_assum `vv_store_bound _ _ _ _ _ _ _`
       (strip_assume_tac o SIMP_RULE (srw_ss()) [vv_store_bound_def,mk_ptr_def]) >>
     qpat_assum `!v tvt w. read_result _ _ _ = _ /\ _ ==> _`
       (qspecl_then [`v`,`rt`,`w`] mp_tac) >>
     (impl_tac >- asm_rewrite_tac[]) >>
     qpat_assum `val_store_size rt v = 32` (fn th => rewrite_tac[th]) >> simp_tac (srw_ss()) []) >>
  drule_all_then (qspecl_then [`fn`,`PG`] strip_assume_tac) copied_read_word_packet >>
  `compile_ptr_load F NONE LocMemory (Var src) sm = (op,sb)` by simp[compile_ptr_load_def] >>
  `alloca_inv s` by fs[vv_post_mods_def,stmt_state_rel_def] >>
  `!x. not_fresh_at sm x ==> lookup_var x q = lookup_var x s` by
    (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  drule_all_then (qspec_then `explicit` strip_assume_tac)
    (word_arm_loaded_path |> Q.INST [`loc` |-> `LocMemory`] |>
     SIMP_RULE (srw_ss()) []) >>
  qexistsl [`u`,`Gf`,`tf`] >> simp[] >> rpt strip_tac >>
  irule gas_origin_ptr_path_from_no_dead >>
  first_assum ACCEPT_TAC
QED

Theorem copied_read_word_post[local]:
  vv_post_mods H ctx fn ce cx e es sa sm s0 ee tv (LocatedValue ann (mk_ptr dst LocMemory)) s /\
  ghost_inv_at_mods D lo d ce cx ee G tn s /\ ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
  read_result cx tv ee = (INL v,ee) /\ post_value_type ce e = ann /\ is_word_type ann /\
  evaluate_type (get_tenv cx) ann = SOME rt /\ eval_operand op u = SOME (typed_val_to_w256 rt v) /\
  local_ptrs_reserved ce sm /\ sa.cs_next_var <= sm.cs_next_var /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  ^read_word_frame ==>
  expr_post_mods H ctx fn ce cx e es sa sb s0 ee v op u /\
  ghost_inv_at_mods D lo d ce cx ee Gf tf u /\ ghost_kept_at lo ce es sa G0 tn0 s0 Gf tf
Proof
  strip_tac >>
  drule_then assume_tac copied_read_memory_vv_post >>
  drule_all_then assume_tac vv_post_read_result >>
  qpat_x_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
  `stmt_state_rel H ctx fn ce cx ee u` by
    (irule stmt_state_rel_readonly_vars_pc >> qexistsl [`s`,`sm`] >> simp[]) >>
  `u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas` by
    (conj_tac >> qpat_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>`
       (fn th => simp[Once th])) >>
  conj_tac
  >- (simp[expr_post_mods_def] >> conj_tac
      >- (irule expr_post_of_vv_post_load_physical >> simp[] >>
          qexistsl [`mk_ptr dst LocMemory`,`s`,`sm`,`ann`] >> simp[] >>
          rpt strip_tac >> qpat_assum `!x. not_fresh_at sm x ==> _` drule >> simp[])
      >> irule copied_read_word_immutables >> qexistsl [`s`,`sm`] >> simp[]) >>
  conj_tac
  >- (irule copied_read_word_ghost >> qexistsl [`G`,`s`,`sm`,`tn`] >> simp[]) >>
  irule ghost_kept_at_clean_suffix >> qexistsl [`G`,`tn`] >> simp[] >>
  rpt strip_tac >> `not_fresh_at sm x` by metis_tac[not_fresh_at_mono] >>
  qpat_assum `!x. not_fresh_at sm x ==> _` drule >> simp[]
QED

Theorem copied_array_read_located_mods:
  linked_subscript_array_context_mods mods exps cx ann obj idx
    DF lo d PG src tops ctx shctx fn shfn ce env ty es et bd /\
  subscript_reads_base cx obj idx /\
  copied_located_vv_mods (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx ty (ann,obj,idx) es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx ty (Subscript ann obj idx) es
Proof
  simp[expr_sim_full_mods_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
  drule_all_then strip_assume_tac copied_read_compile_cuts >>
  drule_then assume_tac forced_expr_admissible_raw >>
  qpat_x_assum `copied_located_vv_mods _ _ _ _ _ _`
    (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shm`,`vv`,`s0`,`G0`,`tn0`] mp_tac o
     REWRITE_RULE [copied_located_vv_mods_def]) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ childQ childR` >>
  irule gas_outcome_full_mods_bind_all >> BETA_TAC >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_result >>
      qexistsl_tac [`mid`,`t`,`v`] >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_result >> simp[])
  >~ [`storage_trace_frame (eval_expr _ _)`]
  >- simp[evaluate_storage_trace_frame]
  >~ [`!v. storage_trace_frame (read_result _ v)`]
  >- simp[storage_trace_frame_read_result] >>
  qexists_tac `\H res ee G tn u. childQ H res ee G tn u /\ ee.gas_obs = [] /\ ~u.vs_halted` >>
  reverse conj_tac
  >- (irule gas_outcome_full_mods_post_source >>
      qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ childQ childR` (irule_at Any) >>
      conj_tac >- simp[] >>
      rpt gen_tac >> Cases_on `res` >> simp[Abbr `childR`, copied_vv_exit_mods_def, expr_exit_def] >>
      ONCE_REWRITE_TAC [INST_TYPE [beta |-> ``:value``] expr_exit_INR_type,
        INST_TYPE [beta |-> ``:value``] halt_exit_INR_type] >> simp[]) >>
  suspend "read_reached_value"
QED

Resume copied_array_read_located_mods[read_reached_value]:
  qx_genl_tac [`marks`,`res`,`ee`,`G`,`tn`,`s`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qunabbrev_tac `childQ` >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (drule_then (strip_assume_tac o SIMP_RULE (srw_ss()) [copied_located_post_mods_def])) >>
  qpat_x_assum `res = INL tv` SUBST_ALL_TAC >>
  qpat_x_assum `vv = LocatedValue _ _` SUBST_ALL_TAC >>
  `?v. read_result cx tv ee = (INL v,ee)` by
    (qpat_assum `ptr_vv_ok _ _ _ _ _ _ _ _`
       (strip_assume_tac o SIMP_RULE (srw_ss()) [ptr_vv_ok_def,mk_ptr_def]) >>
     goal_assum (drule_at Any)) >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  `eval_expr cx (Subscript ann obj idx)
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL tv,ee)` by
    (qpat_assum `!tail. eval_expr _ _ _ = _`
       (qspec_then `[]` (mp_tac o REWRITE_RULE [listTheory.APPEND_NIL])) >>
     asm_rewrite_tac[]) >>
  `expr_body_pre_mods mods ce cx env (Subscript ann obj idx) es` by
    fs[linked_subscript_array_context_mods_def] >>
  drule_all_then strip_assume_tac copied_read_source_type >>
  disj1_tac >> qexists_tac `tv` >> simp[] >>
  Cases_on `~is_word_type ann`
  >- (`op = dst /\ sb = sm` by fs[unwrap_value_def,comp_return_def,mk_ptr_def] >>
      gvs[] >>
      irule gas_outcome_full_mods_pure >> simp[] >>
      qexistsl_tac [`G`,`ee`,`INL v`,`s`,`tn`] >> simp[read_result_gas_obs] >>
      qx_gen_tac `H` >> strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
        (drule_then (strip_assume_tac o SIMP_RULE (srw_ss()) [copied_located_post_mods_def,mk_ptr_def])) >>
      conj_tac >- simp[cj 1 gas_origin_ptr_path_rules] >>
      simp[] >>
      qpat_x_assum `vv_post_mods (storage_trace_horizon _) _ _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
      gvs[mk_ptr_def,expr_type_def] >>
      drule_all_then strip_assume_tac (REWRITE_RULE [mk_ptr_def] copied_read_identity) >> simp[]) >>
  suspend "load_reached_word"
QED

Resume copied_array_read_located_mods[load_reached_word]:
  `is_word_type ann` by fs[] >>
  `allocas_from lo s` by fs[ghost_inv_at_mods_def] >>
  `local_ptrs_reserved ce sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `(!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x)` by
    metis_tac[not_fresh_at_mono] >>
  gvs[expr_type_def] >>
  drule_all_then
    (qspecl_then [`gas_explicit_sites ctx shctx`,`PG`] strip_assume_tac)
    (copied_read_word_run |> Q.INST [`e` |-> `Subscript ann obj idx`] |>
     REWRITE_RULE [post_value_type_def,expr_type_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (qpat_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>`
       (fn th => PURE_ONCE_REWRITE_TAC [th] >>
                 simp[allocas_below_fmp_updates,allocas_below_fmp_def]) >>
     fs[allocas_below_fmp_def]) >>
  `s0.vs_alloca_next <= u.vs_alloca_next` by
    (qpat_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>` (fn th => simp[Once th])) >>
  irule gas_outcome_full_mods_pure >> simp[] >>
  qexistsl_tac [`Gf`,`ee`,`INL v`,`u`,`tf`] >> simp[read_result_gas_obs] >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (drule_then (strip_assume_tac o SIMP_RULE (srw_ss()) [copied_located_post_mods_def])) >>
  simp[expr_type_def, expr_store_bound_word, ptr_val_ok_word] >>
  qpat_x_assum `vv_post_mods (storage_trace_horizon _) _ _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `ghost_inv_at_mods (DF (storage_trace_horizon _)) _ _ _ _ _ _ _ _` kall_tac >>
  drule_all_then strip_assume_tac
    (copied_read_word_post |> Q.INST [`e` |-> `Subscript ann obj idx`] |>
     REWRITE_RULE [post_value_type_def,expr_type_def]) >> simp[]
QED

Finalise copied_array_read_located_mods

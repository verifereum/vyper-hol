Theory bodyImmCompiledMemory
Ancestors
  bodyImmCopyMemory bodyImmEntryMemory bodyImmLoopMemory
  whitelistForIterImmFrag whitelistForIterImmLoop
  stmtForArrayMemoryRounds stmtSimForArrayLoop stmtSimProps stmtSimDefs
  bodyMemoryDefs loweringStateRelDefs exprLoweringProps exprSimProps
  stmtFragPtr localPtrsProps compileEnv context emitHelper emitHelperProps
  stmtLowering stmtLoweringMono venomInst venomState venomExecSemantics
  fragExec loweringPosts vyperInterpreter vyperState words arithmetic list
  rich_list finite_map allocaHistory gasSummary gasOutcome gasContext
  exprSimCopy stmtSimDeclCompose venomMemDefs
  stmtReasonVvMemory exprSimMemDefs
Libs
  monadsyntax

Theorem immutable_compiled_loop_outcome_mem:
  !d ctx func cx cenv lctx RetQ ty id et bd n src name off stmts tv vs es P st st' s.
  FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
  cenv.ce_alloca_locals /\ FLOOKUP cenv.ce_vars id = NONE /\
  evaluate_type (get_tenv cx) et = SOME tv /\
  elem_size_in_location cenv LocCode et = type_memory_size tv /\
  type_memory_bytes cenv et = type_memory_size tv /\
  0 < type_memory_size tv /\ type_memory_bytes cenv et + 64 < dimword (:256) /\
  LENGTH vs <= bound_length bd /\ bound_length bd < dimword (:256) /\
  (case bd of Fixed cap => LENGTH vs = cap | Dynamic cap => T) /\
  (!c lc sa sb. compile_stmts c lc ty stmts sa = ((),sb) ==> cs_extends sa sb) /\
  (!ei s. P ei /\ stmt_state_rel ctx func cenv cx ei s ==>
    (case bd of Fixed cap => T | Dynamic cap =>
       ?av. immutable_holds cenv cx (ArrayT et (Dynamic cap))
               (Value (ArrayV av)) (n2w off) ei s /\
            value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV av) /\
            LENGTH vs = array_length (ArrayTV tv (Dynamic cap)) av) /\
    (!k. k < LENGTH vs ==> immutable_holds cenv cx et (Value (EL k vs))
      (n2w off + n2w ((case bd of Fixed cap => 0 | Dynamic cap => 32) +
                      k * type_memory_size tv)) ei s)) /\
  (!st0 bc sd ex inc ei k.
    declare_local cenv id et st0 = (bc,sd) /\ P ei /\
    lookup_scopes id ei.scopes = NONE /\ k < LENGTH vs ==>
    stmt_frag_mem d ctx func cx (InLoop ex inc) RetQ bc
      (stmts_env bc (InLoop ex inc) ty stmts) (eval_stmts cx stmts)
      (ei with scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: ei.scopes)) /\
  (!ei k gs r es2. P ei /\ lookup_scopes id ei.scopes = NONE /\ k < LENGTH vs /\
    eval_stmts cx stmts (ei with <|scopes := (FEMPTY |+ (id,
      <|assignable := F; type := tv; value := EL k vs; popped := []|>)) :: ei.scopes;
      gas_obs := gs|>) = (r,es2) ==>
    (!ex inc. stmt_res_ok (InLoop ex inc) r) /\
    ?sc rest. es2.scopes = sc :: rest /\
      (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
      ((r = INL () \/ r = INR ContinueException) ==>
        P (es2 with scopes := rest) /\ lookup_scopes id rest = NONE)) /\
  compile_stmt cenv lctx ty
    (For id et (Array (TopLevelName (ArrayT et bd) (src,name))) n stmts) st = ((),st') /\
  fn_has_code st st' func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv st /\ ret_pc_ok cenv st s /\
  stmt_state_rel ctx func cenv cx es s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts /\
  P es /\ lookup_scopes id es.scopes = NONE /\
  gas_admissible (eval_for cx tv id stmts (MAP Value vs)) (stmt_res_ok lctx) es /\
  alloca_history func s /\ return_buf_frame d cenv st s ==>
  gas_outcome T (cx_tops cx) (ctx,func)
    (eval_for cx tv id stmts (MAP Value vs)) (es,s)
    (\res ee t. res = INL () /\
       t.vs_current_bb = st'.cs_current_bb /\
       t.vs_inst_idx = LENGTH st'.cs_current_insts /\ ~t.vs_halted /\
       stmt_state_rel ctx func cenv cx ee t /\ array_caller_frame st s t /\
       (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
       return_buf_frame d cenv st' t /\ alloca_history func t /\
       s.vs_alloca_next <= t.vs_alloca_next)
    (\res ee r. ?ex. res = INR ex /\
       !tail. stmt_exit RetQ (ee with gas_obs := tail) (INR ex) r)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_for_immutable_entry_code_normalized >> strip_tac >>
  drule_all immutable_optional_load_ready >> strip_tac >>
  `sb0.cs_next_var <= sb1.cs_next_var` by
    (mp_tac (cj 2 compile_stmt_cs_mono) >>
     simp[cs_mono_def] >> disch_then drule >> simp[]) >>
  `sa.cs_next_var <= sj.cs_next_var` by decide_tac >>
  `sa.cs_next_var <= sb0.cs_next_var` by
    (mp_tac (cj 6 ci_mono_stmt_helpers) >>
     qpat_assum `compile_iter_elem_copy _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[ci_mono_def] >> metis_tac[pairTheory.SND]) >>
  qabbrev_tac `tot = STRING #"%" (toString (st1.cs_next_var + 6))` >>
  `tot = STRING #"%" (toString (st1.cs_next_var + 6))` by simp[Abbr `tot`] >>
  drule_all immutable_register_frame >> strip_tac >>
  drule_all immutable_allocation_ready >> strip_tac >>
  drule_all immutable_return_pc_ready >> strip_tac >>
  `fn_has_code st st1 func` by
    (irule (cj 1 fn_has_code_split) >> asm_rewrite_tac [] >>
     qexists_tac `st'` >> asm_rewrite_tac [] >> metis_tac[cs_extends_trans]) >>
  qabbrev_tac `ainst = mk_inst st1.cs_next_id ALLOCA
    [Lit (n2w (type_memory_bytes cenv et))] [p]` >>
  `MEM ainst (fn_insts func)` by
    (irule lookup_block_fn_insts >>
     qpat_assum `lookup_block st1.cs_current_bb _ = _` (irule_at Any) >>
     simp[Abbr `ainst`]) >>
  qabbrev_tac `g = STRING #"%" (toString (st1.cs_next_var + 2))` >>
  qabbrev_tac `vld = STRING #"%" (toString (st1.cs_next_var + 3))` >>
  `ALL_DISTINCT [p;idx;g;vld] /\
   (!scopes. not_local_ptr cenv scopes g /\ not_local_ptr cenv scopes vld) /\
   (!x. not_fresh_at st1 x ==> ~MEM x [p;idx;g;vld])` by
    (simp[Abbr `g`, Abbr `vld`, not_fresh_at_def] >>
     rpt conj_tac >> rpt gen_tac >> rpt strip_tac >>
     irule local_ptrs_reserved_fresh >> qexists_tac `st1` >> simp[]) >>
  `!x. lvo = Var x ==> ~MEM x [p;idx;g;vld]` by metis_tac[] >>
  `?u dst cc.
    array_loop_inv ctx func cenv cx P vs id idx (Lit (n2w off)) (n2w off)
      p dst (type_memory_bytes cenv et) ainst cond st 0 es cc /\
    eval_operand lvo u = SOME (n2w (LENGTH vs)) /\
    eval_operand lvo cc = SOME (n2w (LENGTH vs)) /\
    array_caller_frame st s u /\ array_caller_frame st1 u cc /\
    gas_marked_path T ctx func s 0 (OK cc) /\
    u.vs_memory = s.vs_memory /\ cc.vs_memory = s.vs_memory /\
    s.vs_alloca_next <= u.vs_alloca_next /\ u.vs_alloca_next <= cc.vs_alloca_next /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
    (!aid b. FLOOKUP u.vs_allocas aid = SOME b ==> FLOOKUP cc.vs_allocas aid = SOME b) /\
    alloca_history func u /\ alloca_history func cc /\
    return_buf_frame d cenv st u /\ return_buf_frame d cenv st1 u /\
    return_buf_frame d cenv st cc /\ return_buf_frame d cenv st1 cc` by
    (qpat_assum `!ei s. P ei /\ stmt_state_rel _ _ _ _ _ _ ==> _` drule_all >>
     strip_tac >>
     irule immutable_initialize_post_load_mem >>
     qpat_assum `(if dyn then _ else _) st = (lvo,st1)` (irule_at Any) >>
     qpat_assum `lookup_block entry _ = _` (irule_at Any) >>
     asm_rewrite_tac [] >>
     simp[Abbr `ainst`, mk_inst_def, Abbr `g`, Abbr `vld`] >>
     qexistsl_tac [`tv`, `et`] >>
     qpat_x_assum `case bd of Fixed cap => LENGTH vs = cap | Dynamic cap => T` mp_tac >>
     qpat_x_assum `case bd of Fixed cap => T | Dynamic cap => _` mp_tac >>
     qpat_x_assum `evaluate_type _ et = SOME tv` mp_tac >>
     rpt (pop_assum kall_tac) >>
     Cases_on `bd` >> simp[vyperASTTheory.bound_length_def] >> metis_tac[]) >>
  `st.cs_next_var <= st1.cs_next_var` by simp[cs_extends_def] >>
  `ret_pc_ok cenv st1 u` by
    (qpat_assum `ret_pc_ok cenv st s` mp_tac >>
     qpat_assum `array_caller_frame st s u` mp_tac >>
     qpat_assum `st.cs_next_var <= st1.cs_next_var` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[ret_pc_ok_def, array_caller_frame_def, not_fresh_at_def] >>
     metis_tac[LESS_LESS_EQ_TRANS]) >>
  `ret_pc_ok cenv st1 cc` by
    (qpat_assum `ret_pc_ok cenv st1 u` mp_tac >>
     qpat_assum `array_caller_frame st1 u cc` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[ret_pc_ok_def, array_caller_frame_def] >> metis_tac[]) >>
  `array_round_inv d ctx func cenv cx P vs id idx (Lit (n2w off)) (n2w off)
    p dst (type_memory_bytes cenv et) ainst cond st1 u 0 es cc` by
    (pure_rewrite_tac [array_round_inv_def] >> conj_tac
     >- (qhdtm_x_assum `array_loop_inv` mp_tac >>
         simp[array_loop_inv_def]) >>
     simp[array_round_frame_def] >>
     qpat_x_assum `array_caller_frame st1 u cc` mp_tac >>
     simp[array_caller_frame_def]) >>
  `!ei t k. P ei /\ stmt_state_rel ctx func cenv cx ei t /\ k < LENGTH vs ==>
    immutable_holds cenv cx et (Value (EL k vs))
      (n2w off + n2w ((if dyn then 32 else 0) + k * type_memory_size tv)) ei t` by
    (qpat_x_assum `!ei s. P ei /\ stmt_state_rel _ _ _ _ _ _ ==> _` mp_tac >>
     qpat_x_assum `dyn <=> _` mp_tac >>
     rpt (pop_assum kall_tac) >> Cases_on `bd` >> simp[] >> metis_tac[]) >>
  mp_tac (Q.INST [`ok` |-> `stmt_res_ok lctx`] immutable_code_loop_outcome_mem) >>
  impl_tac >- suspend "round_premises" >>
  disch_then (qspecl_then [`0`, `es`, `cc`, `dst`] mp_tac) >>
  suspend "round_execution"
QED
Resume immutable_compiled_loop_outcome_mem[round_premises]:
  asm_rewrite_tac [] >>
  simp[Abbr `ainst`, Abbr `g`, Abbr `vld`] >>
  conj_tac >-
    (qpat_assum `!x. lvo = Var x ==> not_fresh_at st1 x` mp_tac >>
     rpt (pop_assum kall_tac) >> Cases_on `lvo` >> simp[copy_old_operand_def]) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `compile_iter_elem_copy ce _ _ _ _ _ _ _ cs = _`
    (mp_then Any mp_tac immutable_iter_copy_mem_run) >>
  simp[ADD_COMM] >>
  strip_tac >> first_x_assum irule >> simp[ADD_COMM] >>
  qexistsl_tac [`cxxctx`, `cxx`, `ee`] >> simp[]
QED
Resume immutable_compiled_loop_outcome_mem[round_execution]:
  simp[] >> impl_tac
  >- (qhdtm_x_assum `array_round_inv` mp_tac >> simp[Abbr `ainst`]) >>
  strip_tac >>
  irule gas_outcome_zero_prefix_any >> qexists_tac `cc` >>
  asm_rewrite_tac [] >>
  irule gas_outcome_post_mono >>
  goal_assum (drule_at Any) >>
  rpt gen_tac >> BETA_TAC >>
  simp[array_round_done_def, array_round_frame_def] >> strip_tac >>
  conj_asm1_tac
  >- (qpat_x_assum `array_caller_frame st s u` mp_tac >>
      qpat_x_assum `!x w. not_fresh_at st1 x /\ _ ==> _` mp_tac >>
      qpat_x_assum `st.cs_next_var <= st1.cs_next_var` mp_tac >>
      qpat_x_assum `!aid b. FLOOKUP u.vs_allocas aid = SOME b ==> _` mp_tac >>
      rpt (pop_assum kall_tac) >>
      simp[array_caller_frame_def] >> rpt strip_tac
      >- (first_x_assum irule >> simp[] >>
          fs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
      metis_tac[]) >>
  `st.cs_next_var <= st'.cs_next_var` by
    (mp_tac (cj 1 compile_stmt_cs_mono) >>
     simp[cs_mono_def] >> disch_then drule >> simp[]) >>
  irule return_buf_frame_frame >>
  qexistsl_tac [`cenv`, `s`, `st`] >> simp[] >>
  qpat_x_assum `array_caller_frame st s t` mp_tac >>
  simp[array_caller_frame_def]
QED

Finalise immutable_compiled_loop_outcome_mem

(* One linked Range round on the selected body run and its actual landing. *)
Theory bodyForRangeRoundMods
Ancestors
  bodyForRangeConsEntryMods bodyForRangeBodySuffixMods bodyForRangeIncrementMods
  gasOutcomeFullBindMods gasOutcomeFullPostMods gasExemptCertMods gasStorage
  bodyForRangeHeaderMods bodyFullPredsMods bodyFullPostsMods bodyFullShadowBodyInv
  bodyInvCodeProps bodyInvSplit freshWrites stmtLoweringMono stmtSimForLoop
  stmtSimProps stmtSimDefs loweringPosts loweringStateRelDefs compileEnv
  vyperStorageTrace vyperStorageFootprint vyperInterpreter vyperState
  fragGasOriginPtr fragExec ptrDiscipline venomState venomInst finite_map integer_word gasShadow
Libs
  monadsyntax

val _ = Parse.hide "body";

Theorem range_round_trace_frame[local]:
  storage_trace_frame
    (finally (try (ignore_bind (eval_stmts cx body) (return F))
                  handle_loop_exception) pop_scope)
Proof
  simp[evaluate_storage_trace_frame, storage_trace_frame_ignore_bind,
       storage_trace_frame_finally, storage_trace_frame_pop_scope,
       storage_trace_frame_try, storage_trace_frame_return,
       storage_trace_frame_loop_handler]
QED

Theorem range_round_bad_domain[local]:
  ~s.vs_halted /\ ~storage_trace_domain cx st0 es.storage_trace ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (do v <- read_result cx a;
        push_scope_with_var id tyv v;
        finally (try (do eval_stmts cx body; return F od)
                     handle_loop_exception) pop_scope od) (es,s,G,tn) Q R
Proof
  strip_tac >> irule gas_outcome_full_mods_bad_nil >> simp[] >>
  qabbrev_tac `round = bind (read_result cx a) (\v.
    ignore_bind (push_scope_with_var id tyv v)
      (finally (try (ignore_bind (eval_stmts cx body) (return F))
                    handle_loop_exception) pop_scope))` >>
  `storage_trace_frame round` by
    (simp[Abbr `round`] >> irule storage_trace_frame_bind_all >>
     simp[storage_trace_frame_read_result, storage_trace_frame_ignore_bind,
          storage_trace_frame_state_updates, range_round_trace_frame]) >>
  gen_tac >> Cases_on `round (es with gas_obs := tail)` >> simp[] >>
  irule (INST_TYPE [alpha |-> bool] storage_trace_frame_preserves_bad_domain) >>
  qexistsl_tac [`round`,`q`,`es with gas_obs := tail`] >> simp[]
QED

Theorem range_round_prepend_scope[local]:
  ~s.vs_halted /\
  (!tail. bind (read_result cx (Value v)) (push_scope_with_var id tyv)
       (es with gas_obs := tail) = (INL (),ep with gas_obs := tail)) /\
  ep.gas_obs = [] /\
  (!H. gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
         (s,G,tn) [] (OK u,Gf,tf)) /\
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (finally (try (ignore_bind (eval_stmts cx body) (return F))
                  handle_loop_exception) pop_scope) (ep,u,Gf,tf) Q
    (\H res ee gt r. ?ex. res = INR ex /\ R H ex ee gt r) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (do x <- read_result cx (Value v);
        push_scope_with_var id tyv x;
        finally (try (do eval_stmts cx body; return F od)
                     handle_loop_exception) pop_scope od) (es,s,G,tn) Q
    (\H res ee gt r. ?ex. res = INR ex /\ R H ex ee gt r)
Proof
  strip_tac >> pure_rewrite_tac[ignore_bind_def] >>
  once_rewrite_tac[GSYM bind_assoc] >> irule gas_outcome_full_mods_bind_all >>
  rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_unit >>
      qexistsl_tac [`mid`,`t`,`v'`] >> BETA_TAC >> rpt conj_tac >>
      first_assum (ACCEPT_TAC o BETA_RULE))
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_unit >> first_assum ACCEPT_TAC)
  >~ [`storage_trace_frame (bind _ _)`]
  >- (irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_read_result, storage_trace_frame_state_updates])
  >- simp[GSYM ignore_bind_def, range_round_trace_frame] >>
  qexists_tac `\H res mid G1 tn1 t.
    res = INL () /\ mid = ep /\ G1 = Gf /\ tn1 = tf /\ t = u` >>
  BETA_TAC >> reverse conj_tac
  >- (irule gas_outcome_full_mods_pure >> simp[] >> qexistsl_tac [`Gf`,`ep`,`INL ()`,`u`,`tf`] >>
      simp[] >> `ep with gas_obs := [] = ep` by simp[evaluation_state_component_equality] >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  disj1_tac >> qexists_tac `()` >> gvs[GSYM ignore_bind_def]
QED

Theorem range_cons_round_mods:
  for_code func cenv bc ret_ty body id tyv p sz ainst cv ev dv nv cond_lbl
    exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3 sb0 sb1 sj /\
  declare_local cenv id typ st = (bc,st1) /\ cenv.ce_alloca_locals /\
  evaluate_type (get_tenv cx) typ = SOME tyv /\ id NOTIN FDOM env.var_types /\
  local_ptrs_reserved cenv sa /\ ~not_fresh_at sa dv /\ ~not_fresh_at sa cv /\
  nv = STRING #"%" (toString sj.cs_next_var) /\ sj.cs_next_var = sb1.cs_next_var /\
  sa.cs_next_var <= st.cs_next_var /\ sa.cs_next_var <= sb0.cs_next_var /\
  sa.cs_next_id <= ainst.inst_id /\ sa.cs_next_id <= sb0.cs_next_id /\
  (!x z. cenv.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at sa x) /\
  (!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at sa x) /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  sb.cs_current_bb = exit_lbl /\ sb.cs_current_insts = [] /\
  sb0.cs_next_var <= sb.cs_next_var /\
  stmts_env bc (InLoop exit_lbl incr_lbl) ret_ty body sb0 = (bc_out,sb1) /\
  stmts_env (gas_shadow_env T bc) (InLoop exit_lbl incr_lbl) ret_ty
     (MAP gas_shadow_stmt body) ss0 = (gas_shadow_env T bc_out,ss1) /\
  gas_shadow_state sb0 ss0 /\ gas_shadow_state sb1 ss1 /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code ss0 ss1 shadow_func /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  contract_inv mods exps ctx bc cx /\ module_body_inv mods src tops bc cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\ supported_stmts tops bindings body /\
  (!target. supported_stmts_expr_exists (expr_abi_decode_target_root target) body ==>
     EXISTS (occurs_abi_decode_target target o SND) mods) /\
  ce_locals_declared bc (extend_local env id typ F) /\
  locals_alloc_ok bc (extend_local env id typ F) /\
  type_stmts (extend_local env id typ F) ret_ty body = SOME env_b /\ stmts_exprs_ok bc body /\
  ~supported_stmts_expr_exists (unallocated_bare_global_root bc (extend_local env id typ F)) body /\
  (!key. MEM (vyperSubscriptOverlap$WriteAcc (vyperSubscriptOverlap$StateRef key))
                (vyperSubscriptOverlap$accesses_stmts body) /\
         IS_SOME (FLOOKUP (extend_local env id typ F).bare_global_assignable key) ==>
         IS_SOME (FLOOKUP bc.ce_module_vars key)) /\
  call_evaluation_safe cx (int_calls_stmts body) /\
  frame_ret_ok_full_mods mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx RetQ bc ret_ty /\
  body_for_full_ok_mods mods exps cx tyv id body
    (GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2 - n1))) ==>
  !a rs es s G tn.
    ~s.vs_halted /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      range_header_mods mods DF lo d ctx func cenv cx env id tyv st0
        sa sb0 es0 s0 G0 tn0 n1 n2 bound cond_lbl cv ev p ainst.inst_id sz w
        H (a::rs) es G tn s) /\
    gas_admissible (eval_for cx tyv id body (a::rs)) (stmt_res_ok lctx) es ==>
    gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) mods cx st0
      (do v <- read_result cx a;
          push_scope_with_var id tyv v;
          finally (try (do eval_stmts cx body; return F od)
                       handle_loop_exception) pop_scope od) (es,s,G,tn)
      (\H res ee G1 tn1 t. ee.gas_obs = [] /\ ~t.vs_halted /\ ?b. res = INL b /\
        (b ==> range_done_mods DF lo d ctx func cenv cx lctx sa sb es0 s0 G0 tn0 H ee G1 tn1 t) /\
        (~b ==> range_header_mods mods DF lo d ctx func cenv cx env id tyv st0
          sa sb0 es0 s0 G0 tn0 n1 n2 bound cond_lbl cv ev p ainst.inst_id sz w H rs ee G1 tn1 t))
      (\H res ee gt r. ?ex. res = INR ex /\
        (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) (INR ex) gt r) /\
        halt_exit H cx ee (INR ex : unit + exception) r /\
        (ctx_has_dalloca ctx ==> !z. (r = Halt z \/ ?ir. r = IntRet ir z) ==> allocas_below_fmp z))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `storage_trace_domain cx st0 es.storage_trace`
  >- suspend "round" >>
  irule range_round_bad_domain >> simp[]
QED

Resume range_cons_round_mods[round]:
  drule_all (Q.INST [`explicit` |-> `gas_explicit_sites ctx shadow_ctx`] range_cons_entry_mods) >>
  disch_then (qspecl_then [`shadow_ctx`,`PG`] (qx_choosel_then [`k`,`ep`,`u`,`Gf`,`tf`] strip_assume_tac)) >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _` (drule_then assume_tac) >>
  qhdtm_x_assum `range_header_mods` (strip_assume_tac o REWRITE_RULE [range_header_mods_def]) >>
  qhdtm_assum `for_code` (strip_assume_tac o REWRITE_RULE [for_code_def]) >>
  `stmt_frag_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cx (InLoop exit_lbl incr_lbl) RetQ bc
     (stmts_env bc (InLoop exit_lbl incr_lbl) ret_ty body)
     (stmts_env (gas_shadow_env T bc) (InLoop exit_lbl incr_lbl) ret_ty
       (MAP gas_shadow_stmt body)) (eval_stmts cx body) ep` by
    (qpat_assum `body_stmts_full_ok_mods _ _ _ _`
       (irule o REWRITE_RULE [body_stmts_full_ok_mods_def]) >>
     rpt (first_assum ACCEPT_TAC ORELSE conj_tac)
     >- (qexistsl_tac [`extend_local env id typ F`,`env_b`] >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
     qexistsl_tac [`bindings`,`src`,`tops`] >> simp[]) >>
  `k' = k` by
    (qpat_assum `k + LENGTH _ = _` mp_tac >>
     qpat_assum `k' + LENGTH _ = _` mp_tac >> decide_tac) >>
  qpat_x_assum `k' = k` SUBST_ALL_TAC >>
  `bc.ce_is_ctor = cenv.ce_is_ctor /\ bc.ce_modules = cenv.ce_modules /\
   bc.ce_return_buf = cenv.ce_return_buf` by
    (qpat_assum `bc with <|ce_vars := _; ce_var_type := _; ce_dynarray_capacity := _|> = cenv`
       (mp_tac o GSYM) >> simp[NoAsms, compile_env_component_equality]) >>
  `bc.ce_modules = mods` by (drule contract_inv_cenv_modules >> simp[]) >>
  `!H. dead_lo_ok_mods H (DF H) lo bc cx` by
    (qpat_assum `!H. dead_lo_ok_mods _ _ _ cenv cx` mp_tac >>
     qpat_assum `bc.ce_is_ctor = cenv.ce_is_ctor` (fn ctor =>
       qpat_assum `bc.ce_modules = cenv.ce_modules` (fn mods_eq =>
         simp[NoAsms, dead_lo_ok_mods_def, ctor, mods_eq]))) >>
  `!x z. bc.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at sb0 x` by
    (rpt gen_tac >> strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[] >>
     qpat_assum `!x z. cenv.ce_return_buf = _ ==> _`
       (qspecl_then [`x`,`z`] irule) >>
     qpat_assum `bc.ce_return_buf = cenv.ce_return_buf` (SUBST1_TAC o SYM) >>
     qexists_tac `z` >> first_assum ACCEPT_TAC) >>
  qhdtm_x_assum `stmt_frag_full_mods`
    (drule_all_then assume_tac o REWRITE_RULE [stmt_frag_full_mods_def]) >>
  qpat_x_assum `gas_outcome_full_mods _ bc.ce_modules _ _ _ _ _ _`
    (fn th => qpat_assum `bc.ce_modules = mods`
       (fn eq => assume_tac (REWRITE_RULE [eq] th))) >>
  qpat_x_assum `a = Value _` SUBST_ALL_TAC >>
  ho_match_mp_tac range_round_prepend_scope >>
  rpt conj_tac >- first_assum ACCEPT_TAC
  >- simp[read_result_def, bind_def, return_def, push_scope_with_var_def,
          evaluation_state_component_equality]
  >- simp[] >- (gen_tac >> first_assum irule) >>
  suspend "suffix"
QED

Resume range_cons_round_mods[suffix]:
  `ret_pc_ok cenv sa u` by
    (irule ret_pc_ok_frame >> qexistsl_tac [`cenv`,`s`,`sa`] >> simp[] >>
     rpt strip_tac >> `x <> dv` by (strip_tac >> gvs[]) >>
     qpat_assum `!x. x <> dv ==> _` (drule_then strip_assume_tac) >> simp[]) >>
  `lookup_var cv u = SOME (i2w (n1 + &k)) /\ lookup_var ev u = SOME (i2w n2) /\
   lookup_var p u = SOME w /\ FLOOKUP u.vs_allocas ainst.inst_id = SOME (w2n w,sz) /\
   op_taint tf (Var cv) = {} /\ op_prov Gf (Var cv) = NONE /\
   op_taint tf (Var ev) = {} /\ op_prov Gf (Var ev) = NONE` by
    (`cv <> dv /\ ev <> dv /\ p <> dv` by
       (rpt conj_tac >> once_rewrite_tac[EQ_SYM_EQ] >> first_assum ACCEPT_TAC) >>
     qpat_assum `!x. x <> dv ==> _` (fn th =>
       map_every (fn x => qspec_then x mp_tac th) [`cv`,`ev`,`p`]) >>
     qpat_assum `op_prov G (Var cv) = NONE` (assume_tac o SRULE [op_prov_def]) >>
     qpat_assum `op_prov G (Var ev) = NONE` (assume_tac o SRULE [op_prov_def]) >>
     simp[op_prov_def]) >>
  `sb0.cs_next_var <= sb1.cs_next_var` by
    (qpat_assum `compile_stmts bc _ _ _ sb0 = _`
       (mp_then Any (ACCEPT_TAC o CONJUNCT2)
          (SRULE [cs_mono_def] (cj 2 stmtLoweringMonoTheory.compile_stmt_cs_mono)))) >>
  `~not_fresh_at sa nv` by
    (simp[not_fresh_at_def] >> qexists_tac `sj.cs_next_var` >> simp[]) >>
  irule (Q.INST [`explicit` |-> `gas_explicit_sites ctx shadow_ctx`] range_body_suffix_mods) >>
  rpt (first_assum ACCEPT_TAC ORELSE conj_tac)
  >- (qexistsl_tac [`env_b`,`ret_ty`,`typ`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`bc`,`bc_out`,`es`,`exit_lbl`,`incr_lbl`,`k`,`nv`,`sb1`,`sj`] >>
  rpt (first_assum ACCEPT_TAC ORELSE conj_tac) >>
  suspend "increment"
QED

Resume range_cons_round_mods[increment]:
  rpt gen_tac >> strip_tac >>
  irule (Q.INST [`explicit` |-> `gas_explicit_sites ctx shadow_ctx`] range_increment_header_mods) >>
  rpt (first_assum ACCEPT_TAC ORELSE conj_tac) >>
  TRY (rename1 `(_ : string) <> _` >> once_rewrite_tac[EQ_SYM_EQ] >> first_assum ACCEPT_TAC >> NO_TAC) >>
  reverse all_tac
  >- (qexists_tac `Value (IntV (n1 + &k))` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`i1`,`i2`,`i3`,`incr_lbl`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise range_cons_round_mods

(* The literal and checked Range preludes enter the same linked round driver. *)
Theory bodyForRangeDriverMods
Ancestors
  bodyForRangeRoundMods bodyForRangeNilMods bodyForRoundsBindMods
  bodyForEntryInputsMods bodyFullForFacts bodyFullIfExpReach
  supportedStmts supportedStmtTraverse vyperSubscriptOverlap vyperTypeCallGraph
  vyperTypeCallStackSoundness bodySim compileEnv exprSimHypsDefs bodyInvSplit
  bodyInvCodeProps loweringPosts stmtSimForLoop venomInst venomState
  bodyForRangeHeaderMods gasOutcomeFullPostMods finite_map list bodyInvExecutionProps
Libs
  monadsyntax

val _ = Parse.hide "body";

Theorem range_same_frame_module_vars[local]:
  same_frame cenv bc ==> bc.ce_module_vars = cenv.ce_module_vars
Proof
  simp[same_frame_def, compile_env_component_equality]
QED

Theorem range_body_global_root[local]:
  same_frame cenv bc ==>
  unallocated_bare_global_root bc (extend_local env id typ F) =
    unallocated_bare_global_root cenv env
Proof
  strip_tac >> drule_then assume_tac range_same_frame_module_vars >>
  simp[FUN_EQ_THM] >> Cases >> simp[unallocated_bare_global_root_def]
QED

Theorem range_rounds_from_header_mods:
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  supported_stmt tops bindings (For id typ (Range e1 e2) bound body) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
         (For id typ (Range e1 e2) bound body) ==>
       EXISTS (occurs_abi_decode_target target o SND) mods) /\
  ce_locals_declared cenv env /\ locals_alloc_ok cenv env /\
  type_stmt env ret_ty (For id typ (Range e1 e2) bound body) = SOME env' /\
  stmt_exprs_ok cenv (For id typ (Range e1 e2) bound body) /\
  ~supported_stmt_expr_exists (unallocated_bare_global_root cenv env)
    (For id typ (Range e1 e2) bound body) /\
  (!key. MEM (vyperSubscriptOverlap$WriteAcc (vyperSubscriptOverlap$StateRef key))
                (vyperSubscriptOverlap$accesses_stmt (For id typ (Range e1 e2) bound body)) /\
         IS_SOME (FLOOKUP env.bare_global_assignable key) ==>
         IS_SOME (FLOOKUP cenv.ce_module_vars key)) /\
  call_evaluation_safe cx (int_calls_stmt (For id typ (Range e1 e2) bound body)) /\
  frame_ret_ok_full_mods mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx RetQ cenv ret_ty /\
  for_code func cenv bc ret_ty body id tyv p sz ainst cv ev dv nv cond_lbl
    exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3 sb0 sb1 sj /\
  declare_local cenv id typ st = (bc,st1) /\
  evaluate_type (get_tenv cx) typ = SOME tyv /\
  local_ptrs_reserved cenv sa /\ ~not_fresh_at sa dv /\ ~not_fresh_at sa cv /\
  nv = STRING #"%" (toString sj.cs_next_var) /\ sj.cs_next_var = sb1.cs_next_var /\
  sa.cs_next_var <= st.cs_next_var /\ sa.cs_next_var <= sb0.cs_next_var /\
  sa.cs_next_id <= ainst.inst_id /\ sa.cs_next_id <= sb0.cs_next_id /\
  (!x z. cenv.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at sa x) /\
  ret_pc_ok cenv sa s0 /\
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
  body_for_full_ok_mods mods exps cx tyv id body
    (GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2 - n1))) /\
  ~s.vs_halted /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    range_header_mods mods DF lo d ctx func cenv cx env id tyv st0
      sa sb0 es0 s0 G0 tn0 n1 n2 bound cond_lbl cv ev p ainst.inst_id sz w
      H (GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2 - n1))) es G tn s) /\
  gas_admissible (eval_for cx tyv id body
    (GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2 - n1)))) (stmt_res_ok lctx) es ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) mods cx st0
    (eval_for cx tyv id body (GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2 - n1))))
    (es,s,G,tn)
    (\H res ee G1 tn1 t. res = INL () /\
      range_done_mods DF lo d ctx func cenv cx lctx sa sb es0 s0 G0 tn0 H ee G1 tn1 t)
    (\H res ee gt r.
      (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
      halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !z. (r = Halt z \/ ?ir. r = IntRet ir z) ==> allocas_below_fmp z))
Proof
  strip_tac >>
  drule_all_then strip_assume_tac for_declared_static_inputs_mods >>
  drule_then strip_assume_tac type_stmt_for_projection >>
  qpat_assum `contract_inv _ _ _ cenv _`
    (mp_then Any assume_tac contract_inv_alloca_locals) >>
  drule_then assume_tac supported_loop_body_contract >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> drule_all_then ACCEPT_TAC body_inv_no_phi_mods) >>
  `!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at sa x` by
    fs[ret_pc_ok_def] >>
  `!target. supported_stmts_expr_exists (expr_abi_decode_target_root target) body ==>
     EXISTS (occurs_abi_decode_target target o SND) mods` by
    (qpat_assum `!target. supported_stmt_expr_exists _ (For _ _ _ _ _) ==> _` mp_tac >>
     simp[Once supported_stmt_expr_exists_def] >> metis_tac[]) >>
  `~supported_stmts_expr_exists (unallocated_bare_global_root bc (extend_local env id typ F))
     body` by
    (drule_then (fn th => simp[th]) range_body_global_root >>
     qpat_assum `~supported_stmt_expr_exists _ (For _ _ _ _ _)`
       (mp_tac o ONCE_REWRITE_RULE [supported_stmt_expr_exists_def]) >> simp[]) >>
  `!key. MEM (vyperSubscriptOverlap$WriteAcc (vyperSubscriptOverlap$StateRef key))
               (vyperSubscriptOverlap$accesses_stmts body) /\
         IS_SOME (FLOOKUP (extend_local env id typ F).bare_global_assignable key) ==>
         IS_SOME (FLOOKUP bc.ce_module_vars key)` by
    (drule_then assume_tac range_same_frame_module_vars >>
     qpat_assum `!key. MEM _ (vyperSubscriptOverlap$accesses_stmt _) /\ _ ==> _` mp_tac >>
     simp[Once accesses_stmt_def, MEM_APPEND] >> metis_tac[]) >>
  `call_evaluation_safe cx (int_calls_stmts body)` by
    (qpat_assum `call_evaluation_safe cx (int_calls_stmt _)`
       (mp_then Any ACCEPT_TAC call_evaluation_safe_append_right o
        ONCE_REWRITE_RULE [int_calls_stmt_def])) >>
  suspend "rounds"
QED

Resume range_rounds_from_header_mods[rounds]:
  qabbrev_tac `Inv = range_header_mods mods DF lo d ctx func cenv cx env id tyv st0
    sa sb0 es0 s0 G0 tn0 n1 n2 bound cond_lbl cv ev p ainst.inst_id sz w` >>
  qabbrev_tac `Done = range_done_mods DF lo d ctx func cenv cx lctx sa sb es0 s0 G0 tn0` >>
  qabbrev_tac `R = \H ex ee gt r.
      (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) (INR ex : unit + exception) gt r) /\
      halt_exit H cx ee (INR ex : unit + exception) r /\
      (ctx_has_dalloca ctx ==> !z. (r = Halt z \/ ?ir. r = IntRet ir z) ==> allocas_below_fmp z)` >>
  `gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) mods cx st0
    (eval_for cx tyv id body (GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2 - n1))))
    (es,s,G,tn) (\H res ee G1 tn1 t. res = INL () /\ Done H ee G1 tn1 t)
    (\H res ee gt r. ?ex. res = INR ex /\ R H ex ee gt r)` by
    (irule (Q.INST [`ok` |-> `stmt_res_ok lctx`] for_rounds_bind_mods) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`Inv`,`lctx`] >>
     conj_tac >- suspend "cons" >>
     conj_tac >- suspend "nil" >> simp[]) >>
  drule_then irule gas_outcome_full_mods_post_source >>
  simp[Abbr `Done`, Abbr `R`, PULL_EXISTS] >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Resume range_rounds_from_header_mods[cons]:
  simp[Abbr `Inv`, Abbr `Done`, Abbr `R`] >>
  rpt gen_tac >> strip_tac >>
  irule range_cons_round_mods >>
  rpt (first_assum ACCEPT_TAC ORELSE conj_tac) >>
  goal_assum (drule_at (Pat `for_code _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `type_stmts _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `declare_local _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `frame_ret_ok_full_mods _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `stmts_env _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `fn_has_code _ _ _`)) >>
  goal_assum (drule_at (Pat `module_body_inv _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `supported_stmts _ _ _`)) >>
  qexists_tac `exps` >> simp[]
QED

Resume range_rounds_from_header_mods[nil]:
  simp[Abbr `Inv`, Abbr `Done`] >>
  rpt gen_tac >> strip_tac >>
  qhdtm_assum `for_code` (strip_assume_tac o REWRITE_RULE [for_code_def]) >>
  irule range_nil_exit_mods >>
  rpt (first_assum ACCEPT_TAC ORELSE conj_tac) >>
  goal_assum (drule_at (Pat `lookup_block _ _ = SOME _`)) >>
  goal_assum (drule_at (Pat `_.cs_next_var <= _.cs_next_var`)) >>
  qexistsl_tac [`ainst.inst_id`,`bound`,`env`,`id`,`mods`,`n1`,`n2`,`p`,`sz`,`tyv`,`w`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise range_rounds_from_header_mods

(* Replay the first MsgGas default through marshalling, up to the remaining arguments. *)
Theory s1PrefixBoolChainDefaultStagedReplay
Ancestors
  s1PrefixBoolChainDefaultFirstReplay s1PrefixBoolChainDefaultValueMarshal
  s1PrefixBoolChainDefaultMemoryMarshal s1PrefixBoolChainDefaultMsgGasConcreteStep
  msgGasPairedPlacement exprLoweringProps fragExec fragGasOriginPtr
  compileEnv exprLowering pair list

(* A constant return emits no expression code, so staging still extends the cut. *)
Theorem stage_return_extends[local]:
  cs_extends si
    (SND (compile_stage_intcall_args (\_ _ _. comp_return vv) ce es flags ts si))
Proof
  `ci_mono si
    (SND (compile_stage_intcall_args (\_ _ _. comp_return vv) ce es flags ts si))`
    suffices_by simp[ci_mono_def] >>
  irule ci_mono_compile_stage_intcall_args >> simp[comp_return_def,ci_mono_refl]
QED

Theorem gas_path_append_unmarked[local]:
  gas_origin_ptr_path c (s,G,tn) marks (OK u,G1,tn1) /\
  gas_origin_ptr_path c (u,G1,tn1) [] (OK t,G2,tn2) ==>
  gas_origin_ptr_path c (s,G,tn) marks (OK t,G2,tn2)
Proof
  metis_tac[gas_origin_ptr_path_append,APPEND_NIL]
QED

Theorem bool_chain_first_default_msggas_staged_replay:
  compile_stage_intcall_args compile_expr ce
    (Builtin (env_item_type MsgGas) (Env MsgGas) []::rs)
    (flag::fs) (dt::ts) si = (ops,sf) /\
  compile_stage_intcall_args compile_expr (gas_shadow_env T ce)
    (MAP gas_shadow_expr (Builtin (env_item_type MsgGas) (Env MsgGas) []::rs))
    (flag::fs) (dt::ts) sh_si = (ops,sh_sf) /\
  gas_shadow_state si sh_si /\
  fn_has_code si sf func /\ fn_has_code sh_si sh_sf sh_func /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  MEM func ctx.ctx_functions /\ MEM sh_func shadow_ctx.ctx_functions /\
  gas_shadow_function func sh_func /\
  ~s.vs_halted /\ s.vs_current_bb = si.cs_current_bb /\
  s.vs_inst_idx = LENGTH si.cs_current_insts /\ s.vs_gas_readings = w::ws /\
  (!H bb i. valid_horizon cx st0 H es.storage_trace /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME i ==>
    ptr_inst_ok (DF H) lo 0 ctx func G tn i s) /\
  (~flag ==> type_widens_to (get_tenv cx) (env_item_type MsgGas) dt /\
    is_word_type dt /\ fn_inst_ids_distinct func /\
    storage_trace_domain cx st0 es.storage_trace) /\
  (~flag ==> !out cg bb id.
    compile_env_var MsgGas si = (Var out,cg) /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id GAS [] [out]) ==>
    local_ptrs_reserved ce cg /\
    (!x k. ce.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at cg x) /\
    (!x k. ce.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at cg x) /\
    not_fresh_at cg out /\
    alloca_history func (update_var out w (s with vs_gas_readings := ws)
                         with vs_inst_idx := SUC s.vs_inst_idx) /\
    op_taint (step_taint (mk_inst id GAS [] [out]) s
      (update_var out w (s with vs_gas_readings := ws)) tn) (Var out) = {} /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func ce cx es
        (update_var out w (s with vs_gas_readings := ws)
         with vs_inst_idx := SUC s.vs_inst_idx) /\
      ghost_inv_at (DF H) lo d ce cx es
        (step_prov PG G (mk_inst id GAS [] [out])
          (update_var out w (s with vs_gas_readings := ws)))
        (step_taint (mk_inst id GAS [] [out]) s
          (update_var out w (s with vs_gas_readings := ws)) tn)
        (update_var out w (s with vs_gas_readings := ws)
         with vs_inst_idx := SUC s.vs_inst_idx))) ==>
  ?out id cg sh_cg h cm sh_cm hs t G2 tn2.
    compile_env_var MsgGas si = (Var out,cg) /\
    compile_env_var GasPrice sh_si = (Var out,sh_cg) /\
    gas_shadow_state cg sh_cg /\
    fn_has_code si cg func /\ fn_has_code sh_si sh_cg sh_func /\
    compile_stage_intcall_args compile_expr ce
      [Builtin (env_item_type MsgGas) (Env MsgGas) []] [flag] [dt] si = ([h],cm) /\
    compile_stage_intcall_args compile_expr (gas_shadow_env T ce)
      [gas_shadow_expr (Builtin (env_item_type MsgGas) (Env MsgGas) [])]
      [flag] [dt] sh_si = ([h],sh_cm) /\
    compile_stage_intcall_args compile_expr ce rs fs ts cm = (hs,sf) /\
    compile_stage_intcall_args compile_expr (gas_shadow_env T ce)
      (MAP gas_shadow_expr rs) fs ts sh_cm = (hs,sh_sf) /\
    ops = h::hs /\ gas_shadow_state cm sh_cm /\
    fn_has_code si cm func /\ fn_has_code cm sf func /\
    fn_has_code sh_si sh_cm sh_func /\ fn_has_code sh_cm sh_sf sh_func /\
    (!tail. bind (eval_expr default_cx (Builtin (env_item_type MsgGas) (Env MsgGas) []))
      (read_result default_cx)
      (es with gas_obs := gas_explicit [T] s.vs_gas_readings ++ tail) =
      (INL (IntV (&w2n w)), es with gas_obs := tail)) /\
    ~t.vs_halted /\ t.vs_current_bb = cm.cs_current_bb /\
    t.vs_inst_idx = LENGTH cm.cs_current_insts /\ t.vs_gas_readings = ws /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s,G,tn) [T] (OK t,G2,tn2)) /\
    (flag ==> h = Var out /\ cm = cg /\ sh_cm = sh_cg /\
      t = (update_var out w (s with vs_gas_readings := ws)
           with vs_inst_idx := SUC s.vs_inst_idx) /\
      G2 = step_prov PG G (mk_inst id GAS [] [out])
             (update_var out w (s with vs_gas_readings := ws)) /\
      tn2 = step_taint (mk_inst id GAS [] [out]) s
              (update_var out w (s with vs_gas_readings := ws)) tn /\
      eval_operand h t = SOME w) /\
    (~flag ==> ?q a. h = Var q /\ eval_operand h t = SOME a /\
      ptr_covers G2 tn2 q t 32 /\ mload (w2n a) t = w /\
      (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn2.t_mem) /\
      (!mem. mem_agree_outside tn2.t_mem t.vs_memory mem ==>
        val_in_memory (BaseTV (UintT 256)) (IntV (&w2n w)) (w2n a) mem) /\
      FLOOKUP t.vs_allocas cg.cs_next_id = SOME (w2n a,32))
Proof
  strip_tac >>
  drule_all bool_chain_first_default_msggas_replay >>
  disch_then (qspecl_then [`default_cx`,`PG`]
    (qx_choosel_then [`out`,`raw_id`,`cg`,`sh_cg`,`h`,`cm`,`sh_cm`,`hs`,
                       `raw`,`raw_G`,`raw_tn`] strip_assume_tac)) >>
  drule_all msg_gas_paired_placement >>
  disch_then (qx_choosel_then [`out'`,`id`,`bb`] strip_assume_tac) >>
  `out' = out` by fs[] >>
  qpat_x_assum `out' = out` SUBST_ALL_TAC >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
     ptr_inst_ok (DF H) lo 0 ctx func G tn (mk_inst id GAS [] [out]) s` by
    (rpt strip_tac >> qpat_assum `!H bb i. _` irule >> simp[] >>
     qexists_tac `bb` >> simp[]) >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   get_instruction bb s.vs_inst_idx = SOME (mk_inst id GAS [] [out])` by simp[] >>
  drule_all bool_chain_default_msggas_step_concrete >>
  disch_then (qspec_then `PG` (qx_choosel_then [`u`,`G1`,`tn1`] strip_assume_tac)) >>
  `u.vs_current_bb = cg.cs_current_bb /\ u.vs_inst_idx = LENGTH cg.cs_current_insts` by simp[] >>
  Cases_on `flag`
  >- suspend "value"
  >> suspend "memory"
QED

Resume bool_chain_first_default_msggas_staged_replay[value]:
  drule_all bool_chain_default_msggas_value_marshal >> strip_tac >>
  qexistsl_tac [`out`,`id`,`cg`,`sh_cg`,`h`,`cm`,`sh_cm`,`hs`,`u`,`G1`,`tn1`] >>
  simp[]
QED

Resume bool_chain_first_default_msggas_staged_replay[memory]:
  qpat_x_assum `~F ==> type_widens_to _ _ _ /\ _`
    (strip_assume_tac o SIMP_RULE std_ss []) >>
  qpat_x_assum `~F ==> !out cg bb id. _`
    (qspecl_then [`out`,`cg`,`bb`,`id`] mp_tac o SIMP_RULE std_ss []) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  qpat_assum `u = _` (fn u_eq =>
    qpat_assum `G1 = _` (fn g_eq =>
      qpat_assum `tn1 = _` (fn t_eq =>
        disch_then (strip_assume_tac o PURE_REWRITE_RULE (map SYM [u_eq,g_eq,t_eq]))))) >>
  `cs_extends si cg /\ cs_extends sh_si sh_cg` by
    (fs[compile_env_var_def] >> metis_tac[ci_mono_emit_op,ci_mono_def,SND]) >>
  `cs_extends cg cm /\ cs_extends sh_cg sh_cm` by metis_tac[stage_return_extends,SND] >>
  `fn_has_code cg cm func /\ fn_has_code sh_cg sh_cm sh_func` by metis_tac[fn_has_code_split] >>
  drule_all bool_chain_default_msggas_memory_marshal >>
  disch_then (qspecl_then [`shadow_ctx`,`PG`]
    (qx_choosel_then [`t`,`G2`,`tn2`,`q`,`a`] strip_assume_tac)) >>
  qexistsl_tac [`out`,`id`,`cg`,`sh_cg`,`h`,`cm`,`sh_cm`,`hs`,`t`,`G2`,`tn2`] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >>
      irule gas_path_append_unmarked >>
      qexistsl_tac [`G1`,`tn1`,`u`] >> simp[]) >>
  qexists_tac `q` >> simp[] >> metis_tac[]
QED

Finalise bool_chain_first_default_msggas_staged_replay

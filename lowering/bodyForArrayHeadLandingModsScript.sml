(* A nonempty linked Array loop lands at the first instruction of the
   element address calculation.  The capture observer stays at the header. *)
Theory bodyForArrayHeadLandingMods
Ancestors
  bodyForArrayControlMods bodyForArrayTestPathMods bodyForArrayControlFrameMods
  bodyFullForArrayRound bodyFullIfExpReach bodyFullHashKeccakFixed
  loweringPosts stmtSimProps vyperStorageTrace fragGasOriginPtr fragExec
  bodyForArrayHeaderMods vyperStorageFootprint
  exprLoweringProps venomState venomInst venomExecSemantics
  ptrDiscipline finite_map words list arithmetic

Theorem for_array_head_landing_mods:
  for_nonslot_layout (c,id,fty,e,sty,bd,ret_ty,loop_body) (func,shadow_func)
    (sa0,vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL)
    (bc,saD,saA,xd,capacity,aidItem)
    (entry,cond,bod,incr,exit,idx,invalid,valid,dv,next_var)
    (sa,stride,off_op,sm,sum_op,sn,addr,saCopy,sbCopy)
    (sbBody,sj,sb,shadow_sbCopy,shadow_sbBody) /\
  local_ptrs_reserved c sa0 /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    for_array_header_mods mods DF lo d ctx func c cx env id st0
      (es0,sa0,s0,G0,tn0) (em,sbExpr,saL,u,tu) (xd,dw,capacity,aidItem)
      vs (vv_operand vv,bw,len_op,idx) cond Route H (a::rs) ee G tn s) ==>
  ?k t G1 tn1.
    a::rs = DROP k vs /\ k < LENGTH vs /\ a = EL k vs /\ rs = DROP (SUC k) vs /\
    t = jump_to bod (update_var dv 0w s) /\
    G1 = DRESTRICT G (COMPL {dv}) /\ tn1 = (tn with t_var := tn.t_var |+ (dv,{})) /\
    t.vs_current_bb = sa.cs_current_bb /\ t.vs_inst_idx = LENGTH sa.cs_current_insts /\
    ~t.vs_halted /\ lookup_var idx t = SOME (n2w k) /\
    (!q. q <> dv ==>
      lookup_var q t = lookup_var q s /\ FLOOKUP G1 q = FLOOKUP G q /\
      op_taint tn1 (Var q) = op_taint tn (Var q)) /\
    eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s /\
    op_prov G1 (vv_operand vv) = op_prov G (vv_operand vv) /\
    op_taint tn1 (vv_operand vv) = op_taint tn (vv_operand vv) /\
    eval_operand len_op t = eval_operand len_op s /\
    op_prov G1 len_op = op_prov G len_op /\ op_taint tn1 len_op = op_taint tn len_op /\
    t.vs_memory = s.vs_memory /\ t.vs_data_section = s.vs_data_section /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_fmp = s.vs_fmp /\ t.vs_initial_fmp = s.vs_initial_fmp /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
    t.vs_transient = s.vs_transient /\ t.vs_immutables = s.vs_immutables /\
    t.vs_requests = s.vs_requests /\ t.vs_labels = s.vs_labels /\
    tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
    tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G1,tn1) /\
      for_array_header_mods mods DF lo d ctx func c cx env id st0
        (es0,sa0,s0,G0,tn0) (em,sbExpr,saL,u,tu) (xd,dw,capacity,aidItem)
        vs (vv_operand vv,bw,len_op,idx) bod (\_ _ _ _ _ _. T) H (a::rs) ee G1 tn1 t /\
      Route H (a::rs) ee G tn s)
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  `for_array_index_mods vs idx (a::rs) s /\ ~s.vs_halted` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> _`
      (qspec_then `storage_trace_horizon ee.storage_trace`
        (fn th => drule_then (strip_assume_tac o REWRITE_RULE[for_array_header_mods_def]) th)) >>
     simp[]) >>
  qhdtm_x_assum `for_array_index_mods`
    (strip_assume_tac o REWRITE_RULE[for_array_index_mods_def]) >>
  qpat_assum `a::rs = DROP k vs` (strip_assume_tac o MATCH_MP DROP_EQ_CONS o SYM) >>
  qhdtm_x_assum `for_nonslot_layout`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [for_nonslot_layout_def]) >>
  qabbrev_tac `t = jump_to bod (update_var dv 0w s)` >>
  qabbrev_tac `G1 = DRESTRICT G (COMPL {dv})` >>
  qabbrev_tac `tn1 = tn with t_var := tn.t_var |+ (dv,{})` >>
  qexistsl [`k`,`t`,`G1`,`tn1`] >>
  `!q. q <> dv ==>
      lookup_var q t = lookup_var q s /\ FLOOKUP G1 q = FLOOKUP G q /\
      op_taint tn1 (Var q) = op_taint tn (Var q)` by
    simp[Abbr `t`, Abbr `G1`, Abbr `tn1`, jump_to_def, update_var_def,
         lookup_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_taint_def] >>
  `!op. (!x. op = Var x ==> x <> dv) ==>
    eval_operand op t = eval_operand op s /\ op_prov G1 op = op_prov G op /\
    op_taint tn1 op = op_taint tn op` by
    (gen_tac >> Cases_on `op` >> simp[eval_operand_def, op_prov_def, op_taint_def,
      Abbr `t`, Abbr `tn1`, jump_to_def, update_var_def] >> strip_tac >>
     first_x_assum drule >> simp[lookup_var_def, op_taint_def, Abbr `tn1`]) >>
  `vv_operand vv <> Var dv /\ len_op <> Var dv` by
    (qpat_assum `!p. vv_operand vv = Var p \/ len_op = Var p ==> _`
      (qspec_then `dv` mp_tac) >> simp[]) >>
  `eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s /\
   op_prov G1 (vv_operand vv) = op_prov G (vv_operand vv) /\
   op_taint tn1 (vv_operand vv) = op_taint tn (vv_operand vv)` by
    (first_x_assum irule >> simp[]) >>
  `eval_operand len_op t = eval_operand len_op s /\ op_prov G1 len_op = op_prov G len_op /\
   op_taint tn1 len_op = op_taint tn len_op` by
    (first_x_assum irule >> simp[]) >>
  `lookup_var idx t = SOME (n2w k) /\ FLOOKUP G1 idx = FLOOKUP G idx /\
   op_taint tn1 (Var idx) = op_taint tn (Var idx)` by simp[] >>
  `t = jump_to bod (update_var dv 0w s) /\
   G1 = DRESTRICT G (COMPL {dv}) /\ tn1 = (tn with t_var := tn.t_var |+ (dv,{})) /\
   t.vs_current_bb = sa.cs_current_bb /\ t.vs_inst_idx = LENGTH sa.cs_current_insts /\
   ~t.vs_halted /\ t.vs_memory = s.vs_memory /\ t.vs_data_section = s.vs_data_section /\
   t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
   t.vs_fmp = s.vs_fmp /\ t.vs_initial_fmp = s.vs_initial_fmp /\
   t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
   t.vs_transient = s.vs_transient /\ t.vs_immutables = s.vs_immutables /\
   t.vs_requests = s.vs_requests /\ t.vs_labels = s.vs_labels /\
   tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
   tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm` by
    simp[Abbr `t`, Abbr `G1`, Abbr `tn1`, jump_to_def, update_var_def] >>
  rpt (conj_tac >- (first_assum ACCEPT_TAC ORELSE REFL_TAC ORELSE
                     (sym_tac >> first_assum ACCEPT_TAC))) >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (qspec_then `H` (drule_then assume_tac)) >>
  `lookup_var idx s <> eval_operand len_op s` by
    (drule for_array_control_cons_mods >> strip_tac >> first_assum ACCEPT_TAC) >>
  qhdtm_x_assum `for_array_header_mods`
    (strip_assume_tac o REWRITE_RULE[for_array_header_mods_def]) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G1,tn1)` by
    suspend "condition" >>
  `!fn inst q. frag_reachable ctx func t fn inst q ==> dalloca_fmp_headroom inst q` by
    (drule_at (Pat `gas_origin_ptr_path _ _ _ _`) gas_origin_ptr_path_dalloca_fmp_headroom >>
     disch_tac >> qx_genl_tac [`fn`,`inst`,`q`] >> disch_tac >>
     qpat_x_assum `!fn inst q. _ /\ frag_reachable ctx func t fn inst q ==> _`
       (qspecl_then [`fn`,`inst`,`q`] mp_tac) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then ACCEPT_TAC) >>
  suspend "frame"
QED

Resume for_array_head_landing_mods[condition]:
  qmatch_asmsub_abbrev_tac `lookup_block cond func.fn_blocks = SOME bb` >>
  `get_instruction bb 0 = SOME (mk_inst (sa.cs_next_id - 2) EQ [Var idx;len_op] [dv]) /\
   get_instruction bb 1 = SOME (mk_inst (sa.cs_next_id - 1) JNZ [Var dv;Label exit;Label bod] [])` by
    simp[Abbr `bb`, get_instruction_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    (drule stmt_state_rel_allocas_below_fmp >> simp[]) >>
  `n2w k <> (n2w (LENGTH vs) : bytes32)` by fs[] >>
  simp[Abbr `t`, Abbr `G1`, Abbr `tn1`, NoAsms] >>
  qpat_assum `n2w k <> (n2w (LENGTH vs) : bytes32)` (fn ne =>
    irule (SIMP_RULE bool_ss [LET_THM, ne, bool_to_word_def]
      (Q.INST [`x` |-> `n2w k`, `y` |-> `n2w (LENGTH vs)`,
               `eid` |-> `sa.cs_next_id - 2`, `jid` |-> `sa.cs_next_id - 1`]
        for_array_eq_jnz_path_mods))) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  reverse conj_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
  qexistsl [`bb`,`exit`,`idx`,`len_op`,`sa`] >>
  `op_prov G (Var idx) = NONE` by simp[op_prov_def] >>
  simp[eval_operand_def]
QED

Resume for_array_head_landing_mods[frame]:
  conj_tac >- first_assum ACCEPT_TAC >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  `sa0.cs_next_var <= saL.cs_next_var` by
    (qpat_assum `ci_mono sa0 saL` mp_tac >> simp[ci_mono_def, NoAsms]) >>
  `(!q sz. c.ce_return_buf = SOME (PtrVar (Var q) sz) ==> not_fresh_at sa0 q)` by
    (qpat_assum `return_buf_frame d c sa0 s` mp_tac >>
     Cases_on `d` >> simp[return_buf_frame_def, NoAsms, pairTheory.FORALL_PROD] >>
     PairCases_on `x` >> simp[return_buf_frame_def, NoAsms] >>
     strip_tac >> qx_genl_tac [`q`,`sz`] >>
     simp[] >> strip_tac >> qpat_x_assum `x = q` (SUBST_ALL_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  `(!q sz. c.ce_return_pc = SOME (PtrVar (Var q) sz) ==> not_fresh_at sa0 q)` by
    (qpat_assum `ret_pc_ok c sa0 s` (strip_assume_tac o REWRITE_RULE[ret_pc_ok_def]) >> simp[]) >>
  `update_var dv 0w (update_var dv 0w s) = update_var dv 0w s` by
    simp[update_var_def, NoAsms] >>
  qpat_assum `~not_fresh_at saL dv`
    (mp_then (Pat `~not_fresh_at _ _`) drule_all
      (Q.INST [`y` |-> `x`, `vx` |-> `0w`, `vy` |-> `0w`] for_array_control_scalar_frame_mods)) >>
  disch_then (qspec_then `bod` mp_tac) >>
  simp[LET_THM, pred_setTheory.INTER_IDEMPOT, NoAsms] >>
  qpat_assum `update_var dv 0w (update_var dv 0w s) = _` (pure_rewrite_tac o single) >>
  qpat_assum `t = jump_to bod (update_var dv 0w s)` (pure_rewrite_tac o single o SYM) >>
  qpat_assum `G1 = DRESTRICT G (COMPL {dv})` (pure_rewrite_tac o single o SYM) >>
  qpat_assum `tn1 = (tn with t_var := tn.t_var |+ (dv,{}))` (pure_rewrite_tac o single o SYM) >>
  strip_tac >>
  `for_array_index_mods vs idx (a::rs) t` by
    (pure_rewrite_tac[for_array_index_mods_def] >> qexists_tac `k` >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `eval_operand len_op t = SOME (n2w (LENGTH vs)) /\ op_prov G1 len_op = NONE /\
   op_taint tn1 len_op = {} /\ FLOOKUP G1 idx = NONE /\ op_taint tn1 (Var idx) = {} /\
   eval_operand (vv_operand vv) t = SOME bw /\ op_taint tn1 (vv_operand vv) = {}` by simp[] >>
  pure_rewrite_tac[for_array_header_mods_def, AND_CLAUSES] >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[NoAsms])
QED

Finalise for_array_head_landing_mods

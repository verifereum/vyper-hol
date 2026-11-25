(* One nonempty Array round. The element copy and saved representation
   are supplied at their physical endpoints; the body runs at sbCopy. *)
Theory bodyForArrayBodyLandingMods
Ancestors
  bodyForArrayHeadLandingMods bodyForArrayItemPushMods bodyForArrayBodyPopMods
  bodyForArrayRawLandingMods bodyForArrayDeclaredRunMods bodyForEntryInputsMods
  bodyForRangeRoundMods bodyForRangeConsEntryMods bodyForRangeBodySuffixMods
  bodyForRangeHeaderMods bodyForArrayHeaderMods bodyFullForArrayRound
  bodyFullPostsMods bodyFullPredsMods bodyFullShadowBodyInv bodyInvCodeProps
  bodyInvExecutionProps bodyInvSplit bodyFullIfExpReach bodyFullHashKeccakFixed
  bodyFullPathHistory bodySimFull bodySim bodySimDeclCases bodyFullForFacts
  exprSimOperands exprSimHypsDefs gasOriginPtrLabels gasOutcomeFullPostPathMods
  exprLoweringProps exprOperandVar freshWrites vyperSubscriptOverlap ptrDiscipline
  vyperTypeCallGraph vyperTypeCallStackSoundness supportedStmts supportedStmtTraverse
  stmtSimProps stmtSimDefs loweringPosts loweringHalt loweringStateRelDefs compileEnv emitHelper
  vyperStorageTrace vyperStorageFootprint vyperInterpreter vyperState
  fragGasOriginPtr fragExec venomInst venomState finite_map words list arithmetic
Libs
  monadsyntax

val _ = Parse.hide "body";

Theorem array_cons_jmp_blocks[local]:
  emit_jmp_if_not_terminated lbl st = ((),st') ==> st'.cs_blocks = st.cs_blocks
Proof
  simp[emit_jmp_if_not_terminated_def, comp_bind_def, comp_get_def] >>
  IF_CASES_TAC >> simp[comp_return_def, emit_inst_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[fresh_id_def, emit_def, comp_bind_def, comp_return_def]
QED

Theorem array_cons_saved_operand[local]:
  eval_operand op z = SOME w /\ t.vs_labels = z.vs_labels /\
  (!q. op = Var q ==> not_fresh_at cut q) /\
  (!q. not_fresh_at cut q ==> not_fresh_at sbCopy q) /\
  (!q x. not_fresh_at sbCopy q /\ lookup_var q z = SOME x ==>
         lookup_var q t = SOME x) /\
  (!q. not_fresh_at cut q ==> FLOOKUP G1 q = FLOOKUP G q /\
         op_taint tn1 (Var q) = op_taint tn (Var q)) ==>
  eval_operand op t = SOME w /\ op_prov G1 op = op_prov G op /\
  op_taint tn1 op = op_taint tn op
Proof
  Cases_on `op` >> simp[eval_operand_def, op_prov_def, op_taint_def]
QED

(* The two callbacks supply a physical item copy and the selected route's
   facts after a continuing replay. The linked body judgment is recovered
   at the first read and returned in the continuing post for later rounds. *)
Theorem for_array_cons_from_item_mods:
  for_nonslot_layout (c,id,typ,e,sty,bd,ret_ty,body) (func,shadow_func)
    (sa0,vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL)
    (bc,saD,saA,xd,cap,inst.inst_id)
    (entry,cond,bod,incr,exit,idx,invalid,valid,dv,next_var)
    (sa,stride,off_op,sm,sum_op,sn,addr,saCopy,sbCopy)
    (sbBody,sj,sb,shadow_sbCopy,shadow_sbBody) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [xd] /\
  local_ptrs_reserved c sa0 /\ ~block_is_terminated sbCopy /\
  contract_inv mods exps ctx c cx /\ module_body_inv mods src tops c cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  supported_stmt tops bindings (For id typ (Array e) n body) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
      (For id typ (Array e) n body) ==>
      EXISTS (occurs_abi_decode_target target o SND) mods) /\
  ce_locals_declared c env /\ locals_alloc_ok c env /\
  type_stmt env ret_ty (For id typ (Array e) n body) = SOME env' /\
  stmt_exprs_ok c (For id typ (Array e) n body) /\
  ~supported_stmt_expr_exists (unallocated_bare_global_root c env)
    (For id typ (Array e) n body) /\
  (!key. MEM (vyperSubscriptOverlap$WriteAcc (vyperSubscriptOverlap$StateRef key))
      (vyperSubscriptOverlap$accesses_stmt (For id typ (Array e) n body)) /\
      IS_SOME (FLOOKUP env.bare_global_assignable key) ==>
      IS_SOME (FLOOKUP c.ce_module_vars key)) /\
  call_evaluation_safe cx (int_calls_stmt (For id typ (Array e) n body)) /\
  frame_ret_ok_full_mods mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx RetQ c ret_ty /\
  evaluate_type (get_tenv cx) typ = SOME tyv /\ type_memory_size tyv <= cap /\
  stmts_env bc (InLoop exit incr) ret_ty body sbCopy = (bc_out,sbBody) /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_inst_ids_distinct func /\
  (!H. dead_lo_ok_mods H (DF H) lo c cx) /\
  (!x sz. c.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
  (!x sz. c.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
  body_for_full_ok_mods mods exps cx tyv id body vs /\
  (a::rs = vs \/ body_stmts_full_ok_mods mods exps cx body) /\
  ~s.vs_halted /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    for_array_header_mods mods DF lo d ctx func c cx env id st0
      (es0,sa0,s0,G0,tn0) (em,sbExpr,saL,u,tu) (xd,dw,cap,inst.inst_id)
      vs (vv_operand vv,bw,len_op,idx) cond Route H (a::rs) es G tn s) /\
  gas_admissible (eval_for cx tyv id body (a::rs)) (stmt_res_ok lctx) es /\
  (!k sh Gh th.
    a::rs = DROP k vs /\ k < LENGTH vs /\ a = EL k vs /\ rs = DROP (SUC k) vs /\
    sh.vs_current_bb = sa.cs_current_bb /\ sh.vs_inst_idx = LENGTH sa.cs_current_insts /\
    ~sh.vs_halted /\ lookup_var idx sh = SOME (n2w k) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      for_array_header_mods mods DF lo d ctx func c cx env id st0
        (es0,sa0,s0,G0,tn0) (em,sbExpr,saL,u,tu) (xd,dw,cap,inst.inst_id)
        vs (vv_operand vv,bw,len_op,idx) bod (\_ _ _ _ _ _. T) H (a::rs) es Gh th sh /\
      Route H (a::rs) es G tn s) ==>
    ?v z Gf tf.
      read_result cx a es = (INL v,es) /\ value_has_type tyv v /\ val_wf tyv v /\
      (!mem. mem_agree_outside tf.t_mem z.vs_memory mem ==> val_in_memory tyv v (w2n dw) mem) /\
      z.vs_current_bb = sbCopy.cs_current_bb /\ z.vs_inst_idx = LENGTH sbCopy.cs_current_insts /\
      ~z.vs_halted /\ lookup_var idx z = SOME (n2w k) /\
      FLOOKUP Gf idx = FLOOKUP Gh idx /\ op_taint tf (Var idx) = op_taint th (Var idx) /\
      eval_operand (vv_operand vv) z = eval_operand (vv_operand vv) sh /\
      eval_operand len_op z = eval_operand len_op sh /\
      (!q. not_fresh_at saL q ==>
        FLOOKUP Gf q = FLOOKUP Gh q /\ op_taint tf (Var q) = op_taint th (Var q)) /\
      for_array_item_mods c sa0 sbExpr (xd,dw,cap,inst.inst_id) es Gf tf z /\
      for_array_outer_frame_mods ctx func c sa0 es0 s0 G0 tn0 es Gf tf z /\
      for_array_capture_frame_mods c (em,sbExpr,saL,u,tu) es tf z /\
      immutable_frame_mods func c cx es z /\
      ret_pc_ok c sa0 z /\ return_buf_frame d c sa0 z /\ return_buf_sep d c es z /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
          (sh,Gh,th) [] (OK z,Gf,tf) /\
        stmt_state_rel H ctx func c cx es z /\ storage_well_formed_on cx es (FST H) /\
        ghost_inv_at_mods (DF H) lo d c cx es Gf tf z)) /\
  (!v ep gs raw fin H f G1 tn1.
    read_result cx a es = (INL v,es) /\
    push_scope_with_var id tyv v (es with gas_obs := []) = (INL (),ep) /\
    eval_stmts cx body (ep with gas_obs := gs) = (raw,fin) /\
    (raw = INL () \/ raw = INR ContinueException) /\
    valid_horizon cx st0 H fin.storage_trace /\
    for_array_header_mods mods DF lo d ctx func c cx env id st0
      (es0,sa0,s0,G0,tn0) (em,sbExpr,saL,u,tu) (xd,dw,cap,inst.inst_id)
      vs (vv_operand vv,bw,len_op,idx) cond (\_ _ _ _ _ _. T)
      H rs (fin with scopes := TL fin.scopes) G1 tn1 f /\
    (!q. not_fresh_at saL q ==>
      FLOOKUP G1 q = FLOOKUP G q /\ op_taint tn1 (Var q) = op_taint tn (Var q)) ==>
    Route H rs (fin with scopes := TL fin.scopes) G1 tn1 f) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) mods cx st0
    (do v <- read_result cx a;
        push_scope_with_var id tyv v;
        finally (try (do eval_stmts cx body; return F od)
                     handle_loop_exception) pop_scope od) (es,s,G,tn)
    (\H res ee G1 tn1 t. ee.gas_obs = [] /\ ~t.vs_halted /\ ?b. res = INL b /\
      (b ==> for_array_done_mods DF lo d ctx func c cx lctx sa0 sb es0 s0 G0 tn0 H ee G1 tn1 t) /\
      (~b ==> for_array_header_mods mods DF lo d ctx func c cx env id st0
        (es0,sa0,s0,G0,tn0) (em,sbExpr,saL,u,tu) (xd,dw,cap,inst.inst_id)
        vs (vv_operand vv,bw,len_op,idx) cond Route H rs ee G1 tn1 t /\
        body_stmts_full_ok_mods mods exps cx body))
    (\H res ee gt r. ?ex. res = INR ex /\
      (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) (INR ex) gt r) /\
      halt_exit H cx ee (INR ex : unit + exception) r /\
      (ctx_has_dalloca ctx ==> !z. (r = Halt z \/ ?ir. r = IntRet ir z) ==> allocas_below_fmp z))
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  irule for_read_push_round_prefix_mods >>
  conj_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> drule_all_then ACCEPT_TAC body_inv_no_phi_mods) >>
  `?k sh Gh th.
    a::rs = DROP k vs /\ k < LENGTH vs /\ a = EL k vs /\ rs = DROP (SUC k) vs /\
    sh.vs_current_bb = sa.cs_current_bb /\ sh.vs_inst_idx = LENGTH sa.cs_current_insts /\
    ~sh.vs_halted /\ lookup_var idx sh = SOME (n2w k) /\
    (!q. q <> dv ==> lookup_var q sh = lookup_var q s /\ FLOOKUP Gh q = FLOOKUP G q /\
                      op_taint th (Var q) = op_taint tn (Var q)) /\
    eval_operand (vv_operand vv) sh = eval_operand (vv_operand vv) s /\
    eval_operand len_op sh = eval_operand len_op s /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s,G,tn) [] (OK sh,Gh,th) /\
      for_array_header_mods mods DF lo d ctx func c cx env id st0
        (es0,sa0,s0,G0,tn0) (em,sbExpr,saL,u,tu) (xd,dw,cap,inst.inst_id)
        vs (vv_operand vv,bw,len_op,idx) bod (\_ _ _ _ _ _. T) H (a::rs) es Gh th sh /\
      Route H (a::rs) es G tn s)` by suspend "test" >>
  suspend "copy"
QED

Resume for_array_cons_from_item_mods[test]:
  markerLib.RESUME_TAC >>
  drule_all for_array_head_landing_mods >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`k`,`t`,`G1`,`tn1`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume for_array_cons_from_item_mods[copy]:
  qpat_assum `!k sh Gh th. _ ==> ?v z Gf tf. _`
    (qspecl_then [`k`,`sh`,`Gh`,`th`] mp_tac) >>
  (impl_tac >- (rpt (conj_tac >- first_assum ACCEPT_TAC) >>
    gen_tac >> strip_tac >>
    qpat_assum `!H. _ ==> gas_origin_ptr_path _ (s,G,tn) [] _ /\ _`
      (drule_then strip_assume_tac) >> simp[])) >>
  strip_tac >>
  qabbrev_tac `H0 = storage_trace_horizon es.storage_trace` >>
  `valid_horizon cx st0 H0 es.storage_trace` by simp[Abbr `H0`, GSYM storage_trace_domain_def] >>
  qpat_assum `!H. _ ==> for_array_header_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cond Route H (a::rs) es G tn s`
    (qspec_then `H0` (drule_then (strip_assume_tac o REWRITE_RULE [for_array_header_mods_def]))) >>
  qhdtm_assum `for_nonslot_layout` (strip_assume_tac o REWRITE_RULE [for_nonslot_layout_def]) >>
  suspend "push"
QED

Resume for_array_cons_from_item_mods[push]:
  drule_then assume_tac contract_inv_alloca_locals >>
  drule_then strip_assume_tac type_stmt_for_projection >>
  `FLOOKUP c.ce_vars id = NONE` by
    (irule declared_name_unbound >>
     goal_assum (drule_at (Pat `type_stmt _ _ _ = _`)) >> simp[]) >>
  `body_stmts_full_ok_mods mods exps cx body` by
    (qpat_assum `a::rs = vs \/ body_stmts_full_ok_mods _ _ _ _` strip_assume_tac
     >- (qhdtm_assum `body_for_full_ok_mods` (irule o REWRITE_RULE [body_for_full_ok_mods_def]) >>
         qexistsl_tac [`es`,`v`,`es`] >> qpat_assum `a::rs = vs` (pure_once_rewrite_tac o single o SYM) >> simp[NoAsms] >> first_assum ACCEPT_TAC) >>
     first_assum ACCEPT_TAC) >>
  qabbrev_tac `ep = es with <|scopes := (FEMPTY |+ (id,<|assignable := F; type := tyv;
                                  value := v; popped := []|>))::es.scopes;
                             gas_obs := []|>` >>
  `ep.gas_obs = [] /\ ep.storage_trace = es.storage_trace /\ ep.scopes <> []` by simp[Abbr `ep`] >>
  `push_scope_with_var id tyv v (es with gas_obs := []) = (INL (),ep)` by
    simp[Abbr `ep`, push_scope_with_var_def, return_def, evaluation_state_component_equality] >>
  `(!tail. bind (read_result cx a) (push_scope_with_var id tyv)
      (es with gas_obs := tail) = (INL (),ep with gas_obs := tail)) /\
   gas_admissible (eval_stmts cx body) (stmt_res_ok (InLoop exit incr)) ep /\
   expr_sim_inv_mods mods bc cx (extend_local env id typ F) ep /\
   body_const_cells_agree_mods mods cx (extend_local env id typ F) ep` by suspend "source" >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (s,G,tn) [] (OK z,Gf,tf)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. _ ==> gas_origin_ptr_path _ (s,G,tn) [] _ /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!H. _ ==> gas_origin_ptr_path _ (sh,Gh,th) [] _ /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `gas_origin_ptr_path _ (s,G,tn) [] (OK sh,Gh,th)`
       (mp_then (Pos hd) mp_tac gas_origin_ptr_path_append) >> simp[]) >>
  qexistsl_tac [`ep`,`z`,`Gf`,`tf`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >> suspend "physical"
QED

Resume for_array_cons_from_item_mods[source]:
  markerLib.RESUME_TAC >>
  irule for_item_push_source_mods >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- (qexists_tac `v` >> simp[Abbr `ep`, NoAsms] >> simp[]) >>
  conj_tac >- (qexistsl_tac [`lctx`,`rs`] >> first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`c`,`saL`,`saD`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume for_array_cons_from_item_mods[physical]:
  `ci_mono sbExpr saL` by
    (qpat_assum `(case bd of Fixed _ => _ | Dynamic _ => _) sbExpr = _` mp_tac >>
     Cases_on `bd` >> simp[NoAsms] >> strip_tac
     >- (qpat_assum `comp_return _ sbExpr = _` (fn eq =>
           qspecl_then [`Lit (n2w n')`,`sbExpr`]
             (ACCEPT_TAC o REWRITE_RULE [eq,pairTheory.SND]) ci_mono_comp_return)) >>
     qpat_assum `compile_ptr_load _ _ _ _ sbExpr = _` (fn eq =>
       qspecl_then [`c.ce_is_ctor`,`c.ce_imm_alloca`,`loc`,`vv_operand vv`,`sbExpr`]
         (ACCEPT_TAC o REWRITE_RULE [eq,pairTheory.SND]) ci_mono_compile_ptr_load)) >>
  `ci_mono saL sa` by (irule ci_mono_trans >> qexists_tac `saA` >> simp[]) >>
  `ci_mono sa sbCopy` by (irule ci_mono_trans >> qexists_tac `saCopy` >> simp[]) >>
  `ci_mono saL sbCopy` by (irule ci_mono_trans >> qexists_tac `sa` >> simp[]) >>
  `ci_mono sa0 sbCopy /\ ci_mono sbExpr sbCopy` by
    (conj_tac >> irule ci_mono_trans >> qexists_tac `saL` >> simp[]) >>
  `ci_mono sbCopy sb` by
    (irule ci_mono_trans >> qexists_tac `sbBody` >> simp[] >>
     irule ci_mono_trans >> qexists_tac `sj` >> simp[]) >>
  `sa0.cs_next_var <= saL.cs_next_var /\ sa0.cs_next_var <= sbCopy.cs_next_var /\
   sa0.cs_next_id <= sbCopy.cs_next_id /\ sbExpr.cs_next_id <= sbCopy.cs_next_id /\
   saL.cs_next_var <= sbCopy.cs_next_var /\ sa0.cs_next_var <= sb.cs_next_var` by
    (fs[ci_mono_def] >> decide_tac) >>
  `!H. valid_horizon cx st0 H ep.storage_trace ==>
    cenv_top_ext c bc ep.scopes /\
    stmt_state_rel H ctx func bc cx ep z /\ immutable_frame_mods func bc cx ep z /\
    storage_well_formed_on cx ep (FST H) /\ ghost_inv_at_mods (DF H) lo d bc cx ep Gf tf z /\
    ret_pc_ok bc sbCopy z /\ return_buf_frame d bc sbCopy z /\ return_buf_sep d bc ep z /\
    alloca_frame c es0 sa0 s0 bc ep z /\ alloca_frame c em sbExpr u bc ep z` by suspend "push_frame" >>
  qpat_assum `!H. valid_horizon _ _ H ep.storage_trace ==> _`
    (qspec_then `H0` mp_tac) >> simp[] >> strip_tac >>
  qpat_assum `for_array_outer_frame_mods _ _ _ _ _ _ _ _ es Gf tf z`
    (strip_assume_tac o REWRITE_RULE [for_array_outer_frame_mods_def, range_outer_frame_mods_def]) >>
  `!fn inst q. frag_reachable ctx func z fn inst q ==> dalloca_fmp_headroom inst q` by
    (qpat_assum `!H. _ ==> gas_origin_ptr_path _ (s,G,tn) [] (OK z,Gf,tf)`
       (qspec_then `H0` (drule_then (mp_then (Pos hd) mp_tac gas_origin_ptr_path_dalloca_fmp_headroom))) >>
     qpat_assum `!fn inst q. frag_reachable ctx func s fn inst q ==> _`
       (pure_rewrite_tac o single o EQT_INTRO) >> simp[]) >>
  suspend "invoke"
QED

Resume for_array_cons_from_item_mods[push_frame]:
  markerLib.RESUME_TAC >> gen_tac >> strip_tac >>
  `valid_horizon cx st0 H es.storage_trace` by
    (qpat_assum `valid_horizon cx st0 H ep.storage_trace` mp_tac >>
     qpat_assum `ep.storage_trace = es.storage_trace` (pure_rewrite_tac o single) >> simp[NoAsms]) >>
  qpat_assum `!H. _ ==> gas_origin_ptr_path _ (sh,Gh,th) [] _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  irule for_array_item_push_frame_mods >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`G0`,`cap`,`dw`,`es`,`id`,`inst`,`saD`,`saL`,`tn0`,`tu`,`typ`,`tyv`,`v`,`xd`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >> simp[Abbr `ep`]
QED

Resume for_array_cons_from_item_mods[invoke]:
  qabbrev_tac `BodyQ = \H raw pre G1 tn1 t. ?cb.
      stmt_lands (InLoop exit incr) sbBody raw t /\ ~t.vs_halted /\
      (raw = INL () ==> ~block_is_terminated sbBody /\ cb = bc_out) /\
      cenv_top_ext bc cb pre.scopes /\
      stmt_state_rel H ctx func cb cx pre t /\ immutable_frame_mods func cb cx pre t /\
      storage_well_formed_on cx pre (FST H) /\ return_buf_frame d cb sbBody t /\
      alloca_history func t /\ return_buf_sep d cb pre t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ z.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d cb cx pre G1 tn1 t /\
      (!x w. not_fresh_at sbCopy x /\ lookup_var x z = SOME w ==> lookup_var x t = SOME w) /\
      (!a b. FLOOKUP z.vs_allocas a = SOME b ==> FLOOKUP t.vs_allocas a = SOME b) /\
      (!x. not_fresh_at sbCopy x ==>
           FLOOKUP G1 x = FLOOKUP Gf x /\ op_taint tn1 (Var x) = op_taint tf (Var x)) /\
      alloca_frame bc ep sbCopy z cb pre t /\
      (!aid off sz i. FLOOKUP z.vs_allocas aid = SOME (off,sz) /\ aid < sbCopy.cs_next_id /\
         (!name b len. local_region bc ep.scopes z name b len ==>
                       off + sz <= b \/ b + len <= off) /\
         off <= i /\ i < off + sz /\ i IN tn1.t_mem ==> i IN tf.t_mem)` >>
  qabbrev_tac `BodyR = \H raw pre gt r.
      (!tail. stmt_exit_ptr (RetQ H) (pre with gas_obs := tail) raw gt r) /\
      halt_exit H cx pre raw r /\
      (ctx_has_dalloca ctx ==> !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s)` >>
  qabbrev_tac `cfg = (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)` >>
  `gas_outcome_full_mods cfg mods cx st0 (eval_stmts cx body) (ep,z,Gf,tf) BodyQ BodyR`
    by suspend "body_run" >>
  qabbrev_tac `Q = \H raw pre G1 tn1 t. BodyQ H raw pre G1 tn1 t /\ t.vs_labels = z.vs_labels` >>
  `gas_outcome_full_mods cfg mods cx st0 (eval_stmts cx body) (ep,z,Gf,tf) Q BodyR` by
    (simp[Abbr `cfg`, Abbr `Q`, NoAsms] >> irule gas_outcome_full_mods_post_path >>
     qexists_tac `BodyQ` >> conj_tac
     >- (BETA_TAC >> rpt gen_tac >> strip_tac >>
         conj_tac >- first_assum ACCEPT_TAC >>
         qpat_assum `gas_origin_ptr_path _ (z,Gf,tf) _ _`
           (mp_then Any ACCEPT_TAC gas_origin_ptr_path_preserves_labels)) >>
     first_assum ACCEPT_TAC) >>
  drule_all_then strip_assume_tac for_declared_static_inputs_mods >>
  `call_evaluation_safe cx (int_calls_stmts body)` by
    (qpat_assum `call_evaluation_safe cx (int_calls_stmt _)`
       (mp_then Any ACCEPT_TAC call_evaluation_safe_append_right o ONCE_REWRITE_RULE [int_calls_stmt_def])) >>
  `~not_fresh_at saL xd` by
    (qpat_assum `compile_alloc_buffer _ saL = (_,saA)`
       (mp_then Any mp_tac compile_alloc_buffer_insts) >> simp[not_fresh_at_def]) >>
  `!scopes. not_local_ptr c scopes xd` by
    (gen_tac >> irule fresh_not_local_ptr >> qexists_tac `saL` >> simp[]) >>
  `not_fresh_at sbCopy idx /\ not_fresh_at sbCopy xd` by
    (conj_tac >> irule compiler_ci_mono_not_fresh >> qexists_tac `sa` >> simp[]) >>
  qpat_assum `emit_jmp_if_not_terminated _ _ = (_,sj)`
    (mp_then Any assume_tac array_cons_jmp_blocks) >>
  suspend "cleanup"
QED

Resume for_array_cons_from_item_mods[body_run]:
  markerLib.RESUME_TAC >>
  simp[Abbr `cfg`, Abbr `BodyQ`, Abbr `BodyR`, NoAsms] >>
  irule for_array_declared_body_run_mods >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac
  >- (gen_tac >> strip_tac >>
      qpat_assum `!H. _ ==> cenv_top_ext c bc ep.scopes /\ _`
        (drule_then strip_assume_tac) >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`bindings`,`c`,`e`,`env`,`env'`,`exps`,`id`,`n`,`ret_ty`,`sa0`,`saD`,
                `saL`,`shadow_func`,`shadow_sbBody`,`shadow_sbCopy`,`src`,`tops`,`typ`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume for_array_cons_from_item_mods[cleanup]:
  simp[Abbr `cfg`, NoAsms] >>
  ho_match_mp_tac for_raw_body_cleanup_suffix_mods >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac
  >- (qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ Q BodyR` mp_tac >>
      simp[Abbr `BodyR`, NoAsms]) >>
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `ee = pre with scopes := rest` >>
  `ee = pre with scopes := TL pre.scopes` by simp[Abbr `ee`] >>
  `ee.storage_trace = pre.storage_trace` by simp[Abbr `ee`] >>
  qabbrev_tac `ep0 = es with scopes := ep.scopes` >>
  `ep0.scopes = ep.scopes` by simp[Abbr `ep0`] >>
  `push_scope_with_var id tyv v es = (INL (),ep0)` by
    simp[push_scope_with_var_def, return_def, Abbr `ep0`, Abbr `ep`,
         evaluation_state_component_equality] >>
  `eval_stmts cx body (ep0 with gas_obs := gs) = (raw,pre)` by
    (qpat_assum `eval_stmts cx body (ep with gas_obs := gs) = _` mp_tac >>
     simp[Abbr `ep0`, Abbr `ep`, NoAsms, evaluation_state_component_equality]) >>
  `(!q. not_fresh_at saL q ==> not_fresh_at sbCopy q)` by
    (gen_tac >> disch_tac >> irule compiler_ci_mono_not_fresh >> qexists_tac `saL` >> simp[]) >>
  `idx <> dv /\ xd <> idx /\ xd <> next_var` by
    (qpat_assum `ALL_DISTINCT [xd;idx;dv;next_var]`
       (strip_assume_tac o SIMP_RULE (srw_ss()) [ALL_DISTINCT]) >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `~not_fresh_at saL idx /\ ~not_fresh_at saL dv /\ ~not_fresh_at saL next_var` by
    (qpat_assum `EVERY (\q. ~not_fresh_at saL q) [idx;dv;next_var]` mp_tac >> simp[EVERY_DEF, NoAsms]) >>
  `FLOOKUP Gf idx = NONE /\ op_taint tf (Var idx) = {}` by
    (qpat_assum `!q. q <> dv ==> _` (qspec_then `idx` mp_tac) >> simp[]) >>
  `!q. not_fresh_at saL q ==> FLOOKUP Gf q = FLOOKUP G q /\
      op_taint tf (Var q) = op_taint tn (Var q)` by
    (gen_tac >> strip_tac >>
     `q <> dv` by
       (CCONTR_TAC >> pop_assum (fn th => qpat_assum `not_fresh_at saL q`
          (mp_tac o REWRITE_RULE [REWRITE_RULE [] th])) >> simp[]) >>
     qpat_assum `!q. q <> dv ==> _` (qspec_then `q` (drule_then strip_assume_tac)) >>
     qpat_assum `!q. not_fresh_at saL q ==> FLOOKUP Gf q = FLOOKUP Gh q /\ _`
       (qspec_then `q` (drule_then strip_assume_tac)) >> simp[]) >>
  qabbrev_tac `land = if raw = INL () then jump_to incr t else t` >>
  qabbrev_tac `w = n2w k + 1w : 256 word` >>
  qexistsl_tac [`if raw = INR BreakException then t else
                  jump_to cond (update_var idx w (update_var next_var w land))`,
                `if raw = INR BreakException then G1 else
                  DRESTRICT (DRESTRICT G1 (COMPL {next_var})) (COMPL {idx})`,
                `if raw = INR BreakException then tn1 else
                  tn1 with t_var := tn1.t_var |+ (next_var,{}) |+ (idx,{})`] >>
  gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon cx st0 H pre.storage_trace ==> _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qpat_x_assum `Q H raw pre G1 tn1 t` mp_tac >>
  simp[Abbr `Q`, Abbr `BodyQ`, NoAsms] >> strip_tac >>
  suspend "suffix"
QED

Resume for_array_cons_from_item_mods[suffix]:
  `alloca_frame c es0 sa0 s0 bc ep0 z /\ alloca_frame c em sbExpr u bc ep0 z /\
   alloca_frame bc ep0 sbCopy z cb pre t` by
    (qpat_assum `alloca_frame c es0 sa0 s0 bc ep z` mp_tac >>
     qpat_assum `alloca_frame c em sbExpr u bc ep z` mp_tac >>
     qpat_assum `alloca_frame bc ep sbCopy z cb pre t` mp_tac >>
     qpat_assum `ep0.scopes = ep.scopes`
       (fn th => pure_rewrite_tac[stmtSimDefsTheory.alloca_frame_def,th]) >>
     ntac 3 disch_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `(stmt_state_rel H ctx func c cx ee t /\ immutable_frame_mods func c cx ee t /\
    storage_well_formed_on cx ee (FST H) /\ return_buf_sep d c ee t /\
    ghost_inv_at_mods (DF H) lo d c cx ee G1 tn1 t /\
    ret_pc_ok c sa0 t /\ return_buf_frame d c sa0 t /\ return_buf_frame d c sbCopy t /\
    allocas_from lo t /\ lo <= t.vs_alloca_next /\
    for_array_outer_frame_mods ctx func c sa0 es0 s0 G0 tn0 ee G1 tn1 t /\
    for_array_capture_frame_mods c (em,sbExpr,saL,u,tu) ee tn1 t /\
    for_array_item_mods c sa0 sbExpr (xd,dw,cap,inst.inst_id) ee G1 tn1 t /\
    (!q w. not_fresh_at sbCopy q /\ lookup_var q z = SOME w ==>
          lookup_var q t = SOME w /\ FLOOKUP G1 q = FLOOKUP Gf q /\
          op_taint tn1 (Var q) = op_taint tf (Var q)) /\
    (!q. not_fresh_at saL q ==> FLOOKUP G1 q = FLOOKUP Gf q /\
         op_taint tn1 (Var q) = op_taint tf (Var q)) /\
    ((raw = INL () \/ raw = INR ContinueException) ==>
      body_const_cells_agree_mods mods cx env ee /\ expr_sim_inv_mods mods c cx env ee /\
      lookup_scopes id ee.scopes = NONE))` by suspend "pop" >>
  suspend "land"
QED

Resume for_array_cons_from_item_mods[pop]:
  markerLib.RESUME_TAC >>
  irule for_array_body_pop_live_mods >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- qpat_assum `!scopes. not_local_ptr c scopes xd` irule >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`bc`,`body`,`cb`,`body_env'`,`ep0`,`es`,`pre`,`gs`,`ret_ty`,`typ`,`tyv`,`v`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (qpat_assum `!aid off sz i. FLOOKUP z.vs_allocas aid = SOME (off,sz) /\ _ ==> i IN tf.t_mem`
        mp_tac >> qpat_assum `ep0.scopes = ep.scopes` (pure_rewrite_tac o single) >> simp[NoAsms]) >>
  rpt conj_tac >>
  (first_assum ACCEPT_TAC ORELSE
   (qpat_assum `ep0.scopes = ep.scopes` (pure_rewrite_tac o single) >> first_assum ACCEPT_TAC))
QED

Resume for_array_cons_from_item_mods[land]:
  `valid_horizon cx st0 H ee.storage_trace /\ storage_trace_domain cx st0 ee.storage_trace` by simp[] >>
  `(raw = INL () ==> ~block_is_terminated sbBody) /\
   (raw <> INR BreakException ==> raw = INL () \/ raw = INR ContinueException)` by
    (conj_tac
     >- (strip_tac >> qpat_assum `raw = INL () ==> ~block_is_terminated sbBody /\ _`
           (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
     qpat_assum `stmt_lands (InLoop exit incr) sbBody raw t` mp_tac >>
     simp[stmt_lands_def, NoAsms] >> strip_tac >> simp[]) >>
  `!q. not_fresh_at saL q ==> FLOOKUP G1 q = FLOOKUP G q /\
          op_taint tn1 (Var q) = op_taint tn (Var q)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!q. not_fresh_at saL q ==> FLOOKUP G1 q = FLOOKUP Gf q /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!q. not_fresh_at saL q ==> FLOOKUP Gf q = FLOOKUP G q /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `lookup_var idx t = SOME (n2w k) /\ FLOOKUP G1 idx = NONE /\ op_taint tn1 (Var idx) = {}` by
    (qpat_assum `!q x. not_fresh_at sbCopy q /\ lookup_var q z = SOME x ==> lookup_var q t = SOME x /\ _`
       (qspecl_then [`idx`,`n2w k`] mp_tac) >> simp[]) >>
  `eval_operand (vv_operand vv) z = SOME bw /\ eval_operand len_op z = SOME (n2w (LENGTH vs))` by simp[] >>
  `!op word. eval_operand op z = SOME word /\ (!q. op = Var q ==> not_fresh_at saL q) ==>
     eval_operand op t = SOME word /\ op_prov G1 op = op_prov G op /\ op_taint tn1 op = op_taint tn op` by
    (rpt gen_tac >> strip_tac >> irule array_cons_saved_operand >>
     qexistsl_tac [`saL`,`sbCopy`,`z`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `eval_operand (vv_operand vv) t = SOME bw /\ op_taint tn1 (vv_operand vv) = {} /\
   eval_operand len_op t = SOME (n2w (LENGTH vs)) /\ op_prov G1 len_op = NONE /\
   op_taint tn1 len_op = {}` by
    (qpat_assum `!op word. eval_operand op z = SOME word /\ _ ==> _`
      (fn th => map_every (fn args => qspecl_then args mp_tac th)
        [[`vv_operand vv`,`bw`],[`len_op`,`n2w (LENGTH vs)`]]) >>
     simp[]) >>
  qabbrev_tac `fback = jump_to cond (update_var idx w (update_var next_var w land))` >>
  qabbrev_tac `Gr = DRESTRICT G1 (COMPL {next_var} INTER COMPL {idx})` >>
  qabbrev_tac `tr = tn1 with t_var := tn1.t_var |+ (next_var,{}) |+ (idx,{})` >>
  `(if raw = INR BreakException then
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (t,G1,tn1) [] (OK t,G1,tn1) /\
      for_array_done_mods DF lo d ctx func c cx lctx sa0 sb es0 s0 G0 tn0 H ee G1 tn1 t
    else
      (raw = INL () \/ raw = INR ContinueException) /\
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (t,G1,tn1) [] (OK fback,Gr,tr) /\
      for_array_header_mods mods DF lo d ctx func c cx env id st0
        (es0,sa0,s0,G0,tn0) (em,sbExpr,saL,u,tu) (xd,dw,cap,inst.inst_id)
        vs (vv_operand vv,bw,len_op,idx) cond (\H rs ee G tn t. T) H (DROP (SUC k) vs) ee Gr tr fback)`
    by suspend "land_common" >>
  suspend "route"
QED

Resume for_array_cons_from_item_mods[land_common]:
  markerLib.RESUME_TAC >>
  simp[Abbr `fback`, Abbr `land`, Abbr `w`, Abbr `Gr`, Abbr `tr`, NoAsms] >>
  irule (SIMP_RULE (srw_ss()) [LET_THM, DRESTRICT_DRESTRICT]
                   for_array_raw_landing_mods) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac
  >- (qexistsl_tac [`exit`,`rs`,`sbBody`,`sj`] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- simp[NoAsms] >>
      conj_tac
      >- (strip_tac >>
          qpat_assum `~block_is_terminated sbBody ==> sj.cs_current_bb = _ /\ _`
            (drule_then strip_assume_tac) >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
      conj_tac
      >- (strip_tac >>
          qpat_assum `raw <> INR BreakException ==> raw = INL () \/ raw = INR ContinueException`
            (drule_then assume_tac) >>
          qpat_assum `(raw = INL () \/ raw = INR ContinueException) ==> body_const_cells_agree_mods _ _ _ _ /\ _`
            (drule_then strip_assume_tac) >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
      conj_tac >> first_assum ACCEPT_TAC) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume for_array_cons_from_item_mods[route]:
  qpat_x_assum `if raw = INR BreakException then _ else _` mp_tac >>
  Cases_on `raw = INR BreakException`
  >- asm_simp_tac bool_ss [] >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  `!q. not_fresh_at saL q ==> FLOOKUP Gr q = FLOOKUP G q /\
      op_taint tr (Var q) = op_taint tn (Var q)` by
    (gen_tac >> strip_tac >>
     `q <> idx /\ q <> next_var` by
       (conj_tac >> CCONTR_TAC >>
        pop_assum (fn th => qpat_assum `not_fresh_at saL q`
          (mp_tac o REWRITE_RULE [REWRITE_RULE [] th])) >> simp[]) >>
     qpat_assum `!q. not_fresh_at saL q ==> FLOOKUP G1 q = FLOOKUP G q /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `op_taint tn1 (Var q) = op_taint tn (Var q)`
       (assume_tac o SIMP_RULE (srw_ss()) [op_taint_def]) >>
     simp[Abbr `Gr`, Abbr `tr`, FLOOKUP_DRESTRICT, op_taint_def, FLOOKUP_UPDATE] >>
     first_assum ACCEPT_TAC) >>
  `Route H rs ee Gr tr fback` by suspend "replay_route" >>
  qpat_assum `for_array_header_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H _ _ Gr tr fback` mp_tac >>
  simp[for_array_header_mods_def, NoAsms] >> strip_tac >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `rs = DROP (SUC k) vs` (pure_rewrite_tac o single o SYM) >>
  simp[Abbr `ee`, NoAsms] >> first_assum ACCEPT_TAC
QED

Resume for_array_cons_from_item_mods[replay_route]:
  markerLib.RESUME_TAC >>
  qpat_assum `ee = pre with scopes := TL pre.scopes` SUBST1_TAC >>
  qpat_assum `!v ep gs raw fin H f G1 tn1. _ ==> Route _ _ _ _ _ _` irule >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (qexistsl_tac [`ep`,`gs`,`raw`,`v`] >> rpt (conj_tac >- first_assum ACCEPT_TAC) >>
      qpat_assum `raw <> INR BreakException ==> _` (drule_then ACCEPT_TAC)) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `rs = DROP (SUC k) vs` (pure_rewrite_tac o single) >>
  qpat_assum `pre.scopes = sc::rest` (pure_rewrite_tac o single) >>
  qpat_assum `cap = type_memory_bytes c typ` (pure_rewrite_tac o single) >>
  qpat_assum `inst.inst_id = saL.cs_next_id` (pure_rewrite_tac o single) >>
  first_assum ACCEPT_TAC
QED

Finalise for_array_cons_from_item_mods

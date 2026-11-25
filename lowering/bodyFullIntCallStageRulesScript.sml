(* Shared staging rules, parameterized by the final answer and the evidence
   carried by a completed segment. The value and VV binds instantiate the
   same rule at different source result types. *)
Theory bodyFullIntCallStageRules
Ancestors
  exprSimFullBundleProps bodyFullPreds bodySimFull gasOutcomeFullCompose
  gasOutcomeFullGuarded gasExemptCert fragGasOriginPtr loweringPosts exprSimMemDefs
  bodyPtrDefs vyperStorageFootprint vyperStorageTrace vyperState fragExec compileEnv
  exprLoweringProps haltExitProj stmtSimProps gasOutcomeFull

Definition intcall_stage_bind_def:
  intcall_stage_bind A Seg (DF,lo,explicit,ctx,func,PG) cx st0 i j exit_ci
      source (es,s,G,tn) Q1
      (next : 'head -> evaluation_state -> ('answer + exception) # evaluation_state)
      (Q : ((bool # 256 word # type_value) list # num list) ->
        ('answer + exception) -> evaluation_state -> (string |-> num # num) ->
        taint -> venom_state -> bool)
      (R : ((bool # 256 word # type_value) list # num list) ->
        ('answer + exception) -> evaluation_state -> ((string |-> num # num) # taint) ->
        exec_result -> bool) <=>
    (!marks res mid G1 tn1 t.
       (!tail. source (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
          (res,mid with gas_obs := tail)) /\
       storage_trace_domain cx st0 mid.storage_trace /\
       (!H. valid_horizon cx st0 H mid.storage_trace ==> Q1 H res mid G1 tn1 t) /\
       (!H. valid_horizon cx st0 H mid.storage_trace ==>
          gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
            (s,G,tn) marks (OK t,G1,tn1)) /\
       Seg explicit ctx func i j s marks t ==>
       ?v. res = INL v /\
         A (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0 j exit_ci
           (next v) (mid,t,G1,tn1) Q R) /\
    storage_trace_frame source /\
    (!v. storage_trace_frame (next v)) /\
    (!marks err ee leaf stop_state.
       gas_exempt_cert T (cx_tops cx) (ctx,func) (ignore_bind source (return ()))
         (es,s) marks (err,ee) (leaf,stop_state) ==>
       gas_exempt_cert T (cx_tops cx) (ctx,func)
         (bind source (\v. ignore_bind (next v) (return ())))
         (es,s) marks (err,ee) (leaf,stop_state)) /\
    (!left v mid t right err ee leaf stop_state.
       gas_marked_exec T (ctx,func) source (es,s) left (INL v) mid (OK t) /\
       gas_exempt_cert T (cx_tops cx) (ctx,func) (ignore_bind (next v) (return ()))
         (mid with gas_obs := [],t) right (err,ee) (leaf,stop_state) ==>
       gas_exempt_cert T (cx_tops cx) (ctx,func)
         (bind source (\v. ignore_bind (next v) (return ())))
         (es,s) (left ++ right) (err,ee) (leaf,stop_state)) /\
    (!H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
       (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s) ==>
       R H res ee gt r) ==>
    A (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0 i exit_ci
      (bind source next) (es,s,G,tn) Q R
End

Definition intcall_stage_value_post_def:
  intcall_stage_value_post (DF,lo,d,ctx,func) cenv cx e (es,sa,sb,s0,op,G0,tn0) =
    \H res ee G tn t. ?v. res = INL v /\
      expr_post H ctx func cenv cx e es sa sb s0 ee v op t /\
      expr_store_bound cx (post_value_type cenv e) v op t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      ptr_val_ok cx (post_value_type cenv e) v op G tn t /\
      (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G t) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn
End

Definition intcall_stage_vv_post_def:
  intcall_stage_vv_post (DF,lo,d,ctx,func) cenv cx e (es,sa,sb,s0,vv,G0,tn0) =
    \H res ee G tn t. ?tv. res = INL tv /\
      vv_post H ctx func cenv cx e es sa sb s0 ee tv vv t /\
      vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee tv vv t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn t /\
      (!v. tv = Value v /\ ~is_word_type (post_value_type cenv e) /\
           ~is_bytestring_type (post_value_type cenv e) ==>
           vv_own cenv cx (post_value_type cenv e) sa sb ee tv vv t /\
           (!ty p. vv = LocatedValue ty p ==> p.ptr_location = LocMemory)) /\
      (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
       ?val. read_result cx tv ee = (INL val,ee) /\
          !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
                 eval_operand (vv_operand vv) t = SOME w ==>
                 w2n w + type_memory_size rt <= lo /\
                 (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
                        val_in_memory rt val (w2n w) mem)) /\
      (!ty op. vv = StackValue ty op /\ ~is_word_type (post_value_type cenv e) ==>
               ptr_buf_ok cenv e op G t) /\
      (!ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
               ptr_buf_ok cenv e p.ptr_operand G t) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn
End

Definition intcall_stage_vv_pre_def:
  intcall_stage_vv_pre (DF,lo,d,ctx,shctx,PG,func,shfunc)
      cenv cx e es (st0,sa,sb,sha,shb,vv,s0,G0,tn0) <=>
    compile_expr cenv (expr_type e) e sa = (vv,sb) /\
    compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) sha = (vv,shb) /\
    expr_sim_full_code (ctx,shctx,func,shfunc) (sa,sb,sha,shb) /\
    local_ptrs_reserved cenv sa /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    gas_admissible (eval_expr cx e) expr_vv_res_ok es /\
    return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
    (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es s0 /\ storage_well_formed_on cx es (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
    ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts
End

Definition intcall_stage_head_rules_def:
  intcall_stage_head_rules A Seg (DF,lo,d,ctx,shctx,PG,func,shfunc)
      tops cenv cx tenv st0 exit_ci e <=>
    (!es i j shi shj op s G tn.
      expr_sim_full_hypotheses (DF,lo,d,ctx,shctx,PG,func,shfunc) cenv cx (expr_type e) e es
        (st0,i,j,shi,shj,op,s,G,tn) /\
      expr_body_pre cenv cx tenv e es /\ body_const_cells_agree [(NONE,tops)] cx tenv es /\
      expr_sim_full (DF,lo,d,ctx,shctx,PG,func,shfunc) cenv cx (expr_type e) e es /\
      ci_mono j exit_ci ==>
      !next Q R. intcall_stage_bind A Seg
        (DF,lo,gas_explicit_sites ctx shctx,ctx,func,PG) cx st0 i j exit_ci
        (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn)
        (intcall_stage_value_post (DF,lo,d,ctx,func) cenv cx e (es,i,j,s,op,G,tn))
        next Q R) /\
    (!es i j shi shj vv s G tn.
      intcall_stage_vv_pre (DF,lo,d,ctx,shctx,PG,func,shfunc) cenv cx e es
        (st0,i,j,shi,shj,vv,s,G,tn) /\
      expr_body_pre cenv cx tenv e es /\ body_const_cells_agree [(NONE,tops)] cx tenv es /\
      expr_vv_sim_full (DF,lo,d,ctx,shctx,PG,func,shfunc) cenv cx (expr_type e) e es /\
      ci_mono j exit_ci ==>
      !next Q R. intcall_stage_bind A Seg
        (DF,lo,gas_explicit_sites ctx shctx,ctx,func,PG) cx st0 i j exit_ci
        (eval_expr cx e) (es,s,G,tn)
        (intcall_stage_vv_post (DF,lo,d,ctx,func) cenv cx e (es,i,j,s,vv,G,tn))
        next Q R)
End

Definition intcall_stage_neutral_rules_def:
  intcall_stage_neutral_rules A Seg (DF,lo,explicit,ctx,func,PG) cx st0 exit_ci <=>
    (!i s. ~s.vs_halted /\ s.vs_current_bb = i.cs_current_bb /\
       s.vs_inst_idx = LENGTH i.cs_current_insts ==> Seg explicit ctx func i i s [] s) /\
    (!i j k s u t left right.
       ci_mono i j /\ ci_mono j k /\ fn_has_code i k func /\
       Seg explicit ctx func i j s left u /\ Seg explicit ctx func j k u right t ==>
       Seg explicit ctx func i k s (left ++ right) t) /\
    (!i source es s G tn Q R.
       storage_trace_frame source /\ ~s.vs_halted /\
       s.vs_current_bb = i.cs_current_bb /\ s.vs_inst_idx = LENGTH i.cs_current_insts /\
       ci_mono i exit_ci /\
       (storage_trace_domain cx st0 es.storage_trace ==>
        A (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0 i exit_ci
          source (es,s,G,tn) Q R) ==>
       A (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0 i exit_ci
         source (es,s,G,tn) Q R) /\
    (!i tv v es s G tn k Q R.
       ~s.vs_halted /\ read_result cx tv es = (INL v,es) /\
       (!x. storage_trace_frame (k x)) /\
       A (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0 i exit_ci
         (k v) (es with gas_obs := [],s,G,tn) Q R ==>
       A (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0 i exit_ci
         (bind (read_result cx tv) k) (es,s,G,tn) Q R) /\
    (!i j source es s G tn t G1 tn1 Q R.
       storage_trace_frame source /\ storage_trace_domain cx st0 es.storage_trace /\
       ci_mono i j /\ ci_mono j exit_ci /\ fn_has_code i j func /\
       (!H. valid_horizon cx st0 H es.storage_trace ==>
          gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G1,tn1)) /\
       Seg explicit ctx func i j s [] t /\
       A (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0 j exit_ci
         source (es,t,G1,tn1) Q R ==>
       A (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0 i exit_ci
         source (es,s,G,tn) Q R)
End

(* These are the three actual emitted fragments, not a rule turning an
   arbitrary origin path into a confined segment. *)
Definition intcall_stage_buffer_rules_def:
  intcall_stage_buffer_rules Seg (DF,lo,explicit,ctx,func,PG) cenv cx st0 <=>
    !ci ca cu cs vv buf op dty es t G tn a aG atn u uG utn w wG wtn.
      compile_alloc_buffer (MAX 32 (type_memory_bytes cenv dty)) ci = (buf,ca) /\
      unwrap_value cenv vv ca = (op,cu) /\
      (if is_word_type dty then emit_void MSTORE [buf.buf_operand;op]
       else if is_bytestring_type dty then
         comp_ignore_bind (compile_store_bytestring op buf.buf_operand) (comp_return ())
       else compile_store_memory cenv op buf.buf_operand dty (vv_type vv)) cu = ((),cs) /\
      fn_has_code ci ca func /\ fn_has_code ca cu func /\ fn_has_code cu cs func /\
      ci_mono ci ca /\ ci_mono ca cu /\ ci_mono cu cs /\
      fn_inst_ids_distinct func /\
      (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
      t.vs_current_bb = ci.cs_current_bb /\ t.vs_inst_idx = LENGTH ci.cs_current_insts /\
      a.vs_current_bb = ca.cs_current_bb /\ a.vs_inst_idx = LENGTH ca.cs_current_insts /\
      u.vs_current_bb = cu.cs_current_bb /\ u.vs_inst_idx = LENGTH cu.cs_current_insts /\
      w.vs_current_bb = cs.cs_current_bb /\ w.vs_inst_idx = LENGTH cs.cs_current_insts /\
      storage_trace_domain cx st0 es.storage_trace /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK a,aG,atn) /\
        gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (a,aG,atn) [] (OK u,uG,utn) /\
        gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (u,uG,utn) [] (OK w,wG,wtn)) ==>
      Seg explicit ctx func ci cs t [] w
End

(* Forget the compiler cursors in the ordinary interpretation. *)
Definition intcall_stage_ordinary_def:
  intcall_stage_ordinary data tops cx st0 (i:compile_state) (j:compile_state)
      source entry Q R <=> gas_outcome_full data tops cx st0 source entry Q R
End

Theorem intcall_stage_bind_ordinary[local]:
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0 source
    (es,s,G,tn) Q1
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
       (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)) /\
  (!H res ee G1 tn1 t. Q1 H res ee G1 tn1 t ==> ?v. res = INL v) ==>
  intcall_stage_bind intcall_stage_ordinary (\ex c f a b x m y. T)
    (DF,lo,explicit,ctx,func,PG) cx st0 i j exit_ci source (es,s,G,tn) Q1 next Q R
Proof
  strip_tac >> simp[intcall_stage_bind_def, intcall_stage_ordinary_def] >> strip_tac >>
  match_mp_tac (GEN_ALL gas_outcome_full_bind_all_path) >> qexists_tac `Q1` >>
  rpt conj_tac >> TRY (first_assum MATCH_ACCEPT_TAC)
  >- (irule gas_outcome_full_post_mono >>
      goal_assum (drule_at Any) >> conj_tac >- simp[] >>
      BETA_TAC >> rpt strip_tac >>
      `?exc. res = INR exc` by (Cases_on `res` >> fs[exprSimDefsTheory.expr_exit_def,AllCaseEqs()]) >>
      qexists_tac `exc` >> simp[] >>
      qpat_assum `!H res ee gt r. expr_exit res r /\ _ ==> R H res ee gt r` irule >>
      metis_tac[expr_exit_INR_type,halt_exit_INR_type]) >>
  rpt strip_tac >> disj1_tac >> first_assum (irule_at Any) >>
  conj_tac >- (qexists_tac `marks` >> simp[]) >> simp[]
QED

Theorem intcall_stage_head_rules_ordinary:
  intcall_stage_head_rules intcall_stage_ordinary (\ex c f a b x m y. T)
    (DF,lo,d,ctx,shctx,PG,func,shfunc) tops cenv cx tenv st0 exit_ci e
Proof
  simp[intcall_stage_head_rules_def] >> conj_tac
  >- (rpt strip_tac >> match_mp_tac intcall_stage_bind_ordinary >> conj_tac
      >- (qpat_assum `expr_sim_full _ _ _ _ _ _`
            (mp_tac o REWRITE_RULE[expr_sim_full_via_bundle]) >>
          disch_then drule >>
          simp[expr_sim_full_post_def,intcall_stage_value_post_def,
               expr_sim_full_endpoint_def,AC CONJ_ASSOC CONJ_COMM]) >>
      simp[intcall_stage_value_post_def] >> metis_tac[]) >>
  rpt strip_tac >> match_mp_tac intcall_stage_bind_ordinary >> conj_tac
  >- (qpat_assum `expr_vv_sim_full _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE[expr_vv_sim_full_def]) >>
      qpat_x_assum `intcall_stage_vv_pre _ _ _ _ _ _` mp_tac >>
      simp[intcall_stage_vv_pre_def,expr_sim_full_code_def,intcall_stage_vv_post_def,
           arithmeticTheory.ADD_COMM] >>
      strip_tac >> disch_then irule >> simp[] >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      qexistsl_tac [`shi`,`shj`] >> simp[]) >>
  simp[intcall_stage_vv_post_def] >> metis_tac[]
QED

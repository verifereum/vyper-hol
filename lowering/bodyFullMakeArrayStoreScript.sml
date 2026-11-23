(* The actual child, ADD, unwrap and store continuation of MakeArray. *)
Theory bodyFullMakeArrayStore
Ancestors
  bodyFullShadowBodyInv exprSimFullBundleProps exprBodyPreProps bodyInvCodeProps
  bodyFullMakeArrayInputs wideningZeroLayout exprSimAggregateChildren
  bodyFullPreds bodyFullUnwrap gasOutcomeFullCompose bodyFullUnwrapRun
  logStoreDataOriginPtr typedCopyOriginPtr wordArgsPtr
  gasShadowCompileHelpers exprLoweringProps exprSimHyps compileEnv
  bodySimFull loweringStateRelDefs context gasShadowState
  gasShadowCompileStmtHelpers fragExec exprSimUnwrap externalEntryShape
  freshWrites gasExemptCert vyperStorageTrace gasOutcomeFull
  bodyFullAttributeAdd loweringPosts bodyPtrDefs venomExecSemantics exprSimVVFrame
  emitHelper venomInst venomState typedCopyCompatibility
  logBytesRobustSeqPtr bodyCopyMemoryBase fragGasCopyLoop fragGasOriginPtrDead
  fragGasCopySeqLiftProps
  exprSimBufferStore reasonCopySourcePtr
  bodyMemAggregatePath fragGasPathFrameMem logValueFramePtr internalReturnImmutableTypes
  bodyFullBuiltinWordPowCompose stateRelProj immutableDeployAssignFacts

val _ = Parse.hide "base";

Theorem make_array_slot_full_bundled:
    (
        body_inv tops ctx cenv cx /\
        shadow_body_inv tops ctx shadow_ctx /\ expr_sim_inv cenv cx env ebase /\
        csbase.cs_next_id <= aid /\ csbase.cs_next_id <= sa.cs_next_id /\
        csbase.cs_next_var <= sa.cs_next_var /\
        local_ptrs_reserved cenv csbase /\ local_ptrs_reserved cenv sa /\
        (!fn inst z. frag_reachable ctx func s fn inst z ==> dalloca_fmp_headroom inst z) /\
        (!H. dead_lo_ok H (DF H) lo cenv cx) /\
        (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==>
               not_fresh_at csbase x) /\
        (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==>
               not_fresh_at csbase x) /\
        (!H. valid_horizon cx st0 H ebase.storage_trace ==>
             stmt_state_rel H ctx func cenv cx ebase sbase)) /\ body_expr_full_ok cx e /\ expr_body_pre cenv cx env e es /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    arg_type_fits (expr_type e) dty /\
    evaluate_type (get_tenv cx) dty = SOME dtv /\
    type_memory_bytes cenv dty = type_memory_size dtv /\
    off + type_memory_size dtv <= cap /\
    (\cs ee s G tn.
        (?events. ee.storage_trace = ebase.storage_trace ++ events) /\
        FLOOKUP s.vs_allocas aid = SOME (base,cap) /\
        lookup_var q s = SOME (n2w base) /\
        ptr_covers G tn q s cap /\ not_fresh_at cs q /\
        aid < cs.cs_next_id /\ base+cap < dimword (:256) /\
        base+cap <= s.vs_alloca_next /\
        (!name b n. local_region cenv ee.scopes s name b n ==>
                    loweringStateRelDefs$regions_disjoint base cap b n) /\
        (!a b. FLOOKUP sbase.vs_allocas a = SOME b ==>
               FLOOKUP s.vs_allocas a = SOME b) /\
        MAP FDOM ebase.scopes = MAP FDOM ee.scopes /\
        wb_frame cenv ebase ee csbase sbase s /\
        ghost_kept_at lo cenv ebase csbase Gbase tnbase sbase G tn /\
        return_buf_frame d cenv cs s /\ ~s.vs_halted /\
        expr_sim_full_endpoint func cs sbase s /\
        (!H. valid_horizon cx st0 H ee.storage_trace ==>
             stmt_state_rel H ctx func cenv cx ee s /\
             storage_well_formed_on cx ee (FST H) /\
             ghost_inv_at (DF H) lo d cenv cx ee G tn s)) sa es s G tn /\ (\ps (off:num) s tn.
        EVERY (\(rt,v,p,n).
          val_wf rt v /\ val_footprint rt v <= n /\
          base <= p /\ p+n <= (base:num)+(off:num) /\
          (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
               val_in_memory rt v p m)) ps) ps off s tn /\
    gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
    (do vv <- compile_expr cenv (expr_type e) e;
        dst <- emit_op ADD [Var q; Lit (n2w off)];
        src <- unwrap_value cenv vv;
        compile_store_memory cenv src dst dty (lowered_value_type cenv e)
     od) sa = ((),sb) /\
    (do vv <- compile_expr (gas_shadow_env T cenv) (expr_type (gas_shadow_expr e)) (gas_shadow_expr e);
        dst <- emit_op ADD [Var q; Lit (n2w off)];
        src <- unwrap_value cenv vv;
        compile_store_memory cenv src dst dty
          (lowered_value_type cenv (gas_shadow_expr e))
     od) shadow_sa = ((),shadow_sb) /\
    expr_sim_full_code (ctx,shadow_ctx,func,shadow_func)
      (sa,sb,shadow_sa,shadow_sb) ==>
    gas_outcome_full
      (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx))
      (es,s,G,tn)
      (\H res ee Gf tnf t.
        ?v. res = INL v /\ value_has_type dtv v /\ val_wf dtv v /\
            (\cs ee s G tn.
        (?events. ee.storage_trace = ebase.storage_trace ++ events) /\
        FLOOKUP s.vs_allocas aid = SOME (base,cap) /\
        lookup_var q s = SOME (n2w base) /\
        ptr_covers G tn q s cap /\ not_fresh_at cs q /\
        aid < cs.cs_next_id /\ base+cap < dimword (:256) /\
        base+cap <= s.vs_alloca_next /\
        (!name b n. local_region cenv ee.scopes s name b n ==>
                    loweringStateRelDefs$regions_disjoint base cap b n) /\
        (!a b. FLOOKUP sbase.vs_allocas a = SOME b ==>
               FLOOKUP s.vs_allocas a = SOME b) /\
        MAP FDOM ebase.scopes = MAP FDOM ee.scopes /\
        wb_frame cenv ebase ee csbase sbase s /\
        ghost_kept_at lo cenv ebase csbase Gbase tnbase sbase G tn /\
        return_buf_frame d cenv cs s /\ ~s.vs_halted /\
        expr_sim_full_endpoint func cs sbase s /\
        (!H. valid_horizon cx st0 H ee.storage_trace ==>
             stmt_state_rel H ctx func cenv cx ee s /\
             storage_well_formed_on cx ee (FST H) /\
             ghost_inv_at (DF H) lo d cenv cx ee G tn s)) sb ee t Gf tnf /\ (\ps (off:num) s tn.
        EVERY (\(rt,v,p,n).
          val_wf rt v /\ val_footprint rt v <= n /\
          base <= p /\ p+n <= (base:num)+(off:num) /\
          (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
               val_in_memory rt v p m)) ps) ps off t tnf /\
            (!m. mem_agree_outside tnf.t_mem t.vs_memory m ==>
                 val_in_memory dtv v ((base:num)+(off:num)) m) /\
            (!(p:num) (n:num). (base:num)+(off:num)+type_memory_size dtv <= p /\ p+n <= base+cap ==>
                   mem_bytes_at p n t.vs_memory = mem_bytes_at p n s.vs_memory) /\
            (~expr_has_effect e ==>
              (!name b n. local_region cenv es.scopes s name b n ==>
                mem_bytes_at b n t.vs_memory = mem_bytes_at b n s.vs_memory) /\
              !p n. (p+n <= base \/ base+cap <= p) /\
                (!inst b sz. MEM inst (fn_insts func) /\
                  inst.inst_opcode = ALLOCA /\ sa.cs_next_id <= inst.inst_id /\
                  FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) ==>
                  loweringStateRelDefs$regions_disjoint p n b sz) ==>
                mem_bytes_at p n t.vs_memory = mem_bytes_at p n s.vs_memory))
      (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
        (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  REWRITE_TAC [expr_sim_full_code_def, expr_sim_full_endpoint_def] >>
  BETA_TAC >> strip_tac >>
  irule gas_outcome_full_initial_domain >>
  simp[vyperStorageTraceTheory.storage_trace_frame_bind_all,
       cj 5 vyperStorageTraceTheory.evaluate_storage_trace_frame,
       storage_trace_frame_read_result] >>
  strip_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    (`valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
       fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H ctx func cenv cx es s /\ _`
       (qspec_then `storage_trace_horizon es.storage_trace` (drule_then strip_assume_tac)) >>
     qpat_assum `stmt_state_rel _ ctx func cenv cx es s`
       (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  Cases_on `compile_expr cenv (expr_type e) e sa` >>
  rename1 `compile_expr cenv (expr_type e) e sa = (vv,sm)` >>
  Cases_on `emit_op ADD [Var q; Lit (n2w off)] sm` >>
  rename1 `emit_op ADD [Var q; Lit (n2w off)] sm = (dst,sn)` >>
  Cases_on `unwrap_value cenv vv sn` >>
  rename1 `unwrap_value cenv vv sn = (src,sc)` >>
  gvs[comp_bind_def] >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e) e es` by
    (qpat_x_assum `body_expr_full_ok cx e`
       (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_def]) >>
     qpat_assum `!DF lo d PG tops ctx shadow_ctx func shadow_func cenv env ty es.
         _ ==> expr_sim_full _ _ _ _ _ _ /\ expr_vv_sim_full _ _ _ _ _ _`
       drule_all >> simp[]) >>
  `gas_shadow_compiles (compile_expr cenv (expr_type e) e)
     (compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e))` by
     irule gas_shadow_stmt_compile_expr_env >>
  qpat_x_assum `gas_shadow_compiles _ _`
    (mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
  disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) shadow_sa` >>
  gvs[] >>
  rename1 `compile_expr cenv (expr_type e) e sa = (vv,sm)` >>
  rename1 `gas_shadow_state sm shadow_sm` >>
  `cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var /\
   sa.cs_next_id <= sm.cs_next_id` by metis_tac[compile_expr_extends] >>
  `cs_extends sm sn` by
    (mp_tac (cj 2 cs_appends_emit_helpers) >>
     simp[cs_appends_def] >> metis_tac[]) >>
  `cs_extends sn sc` by metis_tac[unwrap_value_extends] >>
  `cs_extends sc sb` by
    (qspec_then `sc` mp_tac
      (Q.SPECL [`cenv`,`src`,`dst`,`dty`,`lowered_value_type cenv e`]
        compile_store_memory_labels) >> simp[]) >>
  `cs_extends sm sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa sm func` by metis_tac[fn_has_code_split] >>
  Cases_on `emit_op ADD [Var q; Lit (n2w off)] shadow_sm` >>
  rename1 `emit_op ADD [Var q; Lit (n2w off)] shadow_sm = (shadow_dst,shadow_sn)` >>
  Cases_on `unwrap_value cenv vv shadow_sn` >>
  rename1 `unwrap_value cenv vv shadow_sn = (shadow_src,shadow_sc)` >>
  gvs[] >>
  `cs_extends shadow_sa shadow_sm` by metis_tac[compile_expr_extends] >>
  `cs_extends shadow_sm shadow_sn` by
    (mp_tac (cj 2 cs_appends_emit_helpers) >>
     simp[cs_appends_def] >> metis_tac[]) >>
  `cs_extends shadow_sn shadow_sc` by metis_tac[unwrap_value_extends] >>
  `cs_extends shadow_sc shadow_sb` by
    (qspec_then `shadow_sc` mp_tac
      (Q.SPECL [`cenv`,`shadow_src`,`shadow_dst`,`dty`,`lowered_value_type cenv e`]
        compile_store_memory_labels) >> simp[]) >>
  `cs_extends shadow_sm shadow_sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code shadow_sa shadow_sm shadow_func` by metis_tac[fn_has_code_split] >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    metis_tac[expr_body_pre_vv_gas_admissible] >>
  `!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  qpat_x_assum `expr_vv_sim_full _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_full_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,`vv`,`s`,`G`,`tn`] mp_tac) >>
  simp[] >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ childQ childR` >>
  irule gas_outcome_full_bind_all >> rpt conj_tac
  >~ [`storage_trace_frame (eval_expr _ _)`]
  >- simp[cj 5 vyperStorageTraceTheory.evaluate_storage_trace_frame]
  >~ [`!v. storage_trace_frame (read_result cx v)`]
  >- simp[storage_trace_frame_read_result]
  >~ [`gas_marked_exec _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> drule gas_exempt_cert_bind_result >> simp[] >>
      disch_then irule >> simp[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_result >> first_assum ACCEPT_TAC) >>
  qexists `\H res ee G tn t. childQ H res ee G tn t /\ ee.gas_obs = [] /\ ~t.vs_halted` >>
  reverse conj_tac
  >- (irule gas_outcome_full_post_source >>
      first_assum (irule_at Any) >> simp[Abbr `childR`] >>
      rpt strip_tac >>
      qpat_x_assum `expr_exit res r` mp_tac >>
      qpat_x_assum `halt_exit H cx ee res r` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >>
      Cases_on `res` >> simp[exprSimDefsTheory.halt_exit_def] >>
      Cases_on `r` >> Cases_on `y` >> simp[exprSimDefsTheory.expr_exit_def] >>
      rename1 `Error err` >> Cases_on `err` >> simp[exprSimDefsTheory.expr_exit_def]) >>
  suspend "slot"
QED

Resume make_array_slot_full_bundled[slot]:
  qx_genl_tac [`marks`,`res`,`ee`,`G1`,`tn1`,`t`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _ /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  qunabbrev_tac `childQ` >> disch_then (strip_assume_tac o BETA_RULE) >> gvs[] >>
  qpat_assum `!tail. eval_expr _ _ _ = _`
    (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
  `ee with gas_obs := [] = ee` by
    simp[vyperStateTheory.evaluation_state_component_equality] >> gvs[] >>
  `vv_post (storage_trace_horizon ee.storage_trace) ctx func cenv cx e es sa sm s ee tv vv t` by
    metis_tac[] >>
  `lookup_var q t = SOME (n2w base)` by
    metis_tac[vv_post_def] >>
  `ptr_covers G1 tn1 q t cap` by
    (qpat_x_assum `ghost_kept_at lo cenv es sa G tn s G1 tn1`
       (mp_tac o REWRITE_RULE [ghost_kept_at_def]) >>
     strip_tac >>
     qpat_x_assum `ptr_covers G tn q s cap`
       (mp_tac o REWRITE_RULE [ptr_covers_def]) >>
     simp[ptr_covers_def] >> metis_tac[]) >>
  `fn_has_code sm sn func` by metis_tac[fn_has_code_split,cs_extends_trans] >>
  qabbrev_tac `out = STRING #"%" (toString sm.cs_next_var)` >>
  qabbrev_tac `ai = mk_inst sm.cs_next_id ADD [Var q; Lit (n2w off)] [out]` >>
  qabbrev_tac `au = update_var out (n2w base + n2w off) t` >>
  qabbrev_tac `at = au with vs_inst_idx := SUC t.vs_inst_idx` >>
  qabbrev_tac `Ga = step_prov PG G1 ai au` >>
  qabbrev_tac `tna = step_taint ai t au tn1` >>
  `dst = Var out /\
   (!D lo explicit. allocas_from lo t ==>
      gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (t,G1,tn1) [] (OK at,Ga,tna)) /\
   FLOOKUP Ga out = op_prov G1 (Var q) /\
   op_taint tna dst = {} /\ tna.t_mem = tn1.t_mem /\
   tna.t_stor = tn1.t_stor /\ tna.t_trans = tn1.t_trans /\ tna.t_imm = tn1.t_imm /\
   (!p. p <> out ==> FLOOKUP Ga p = FLOOKUP G1 p /\
      op_taint tna (Var p) = op_taint tn1 (Var p))` by
    (irule attribute_add_full_frame >>
     simp[Abbr `out`,Abbr `ai`,Abbr `au`,Abbr `at`,Abbr `Ga`,Abbr `tna`,
          venomStateTheory.eval_operand_def] >>
     conj_tac
     >- (qpat_x_assum `ptr_covers G1 tn1 q t cap` mp_tac >> simp[ptr_covers_def]) >>
     qexistsl_tac [`n2w off`,`sm`,`sn`] >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       vv_post H ctx func cenv cx e es sa sm s ee tv vv at` by
    (rpt strip_tac >> simp[Abbr `at`,Abbr `au`,Abbr `out`] >>
     irule make_array_add_original_post >>
     goal_assum (drule_at Any) >>
     reverse conj_tac >- (simp[] >> metis_tac[]) >>
     qexistsl_tac [`Var q`,`dst`,`sn`] >> simp[venomStateTheory.eval_operand_def]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       ghost_inv_at (DF H) lo d cenv cx ee Ga tna at` by
    (rpt strip_tac >> simp[Abbr `at`,Abbr `au`,Abbr `out`] >>
     irule (cj 1 attribute_fresh_full_ghost_update) >>
     conj_tac
     >- (qexists_tac `sa` >> simp[]) >>
     qexistsl_tac [`G1`,`tn1`] >> simp[] >> metis_tac[]) >>
  mp_tac (Q.INST [`ce` |-> `cenv`, `G` |-> `G1`, `tn` |-> `tn1`]
    make_array_add_value_inputs) >>
  impl_tac >- simp[Abbr `out`,Abbr `ai`,Abbr `au`,Abbr `at`,Abbr `Ga`,Abbr `tna`] >>
  strip_tac >>
  `ghost_kept_at lo cenv es sa G tn s Ga tna` by
    (irule (cj 2 attribute_fresh_full_ghost_update) >>
     simp[] >> qexistsl_tac [`G1`,`sm`,`tn1`] >> simp[Abbr `out`]) >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sm x` by
    metis_tac[exprOperandVarTheory.compiler_compile_var] >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (drule vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom >> simp[]) >>
  drule post_type_evaluates >> strip_tac >>
  rename1 `evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME ptv` >>
  `sn.cs_current_bb = sm.cs_current_bb` by
    (qpat_x_assum `emit_op _ _ sm = _` mp_tac >>
     simp[emit_op_def,comp_bind_def,fresh_var_def,fresh_id_def,
          comp_ignore_bind_def,comp_return_def,emit_def] >> strip_tac >> gvs[]) >>
  `LENGTH sn.cs_current_insts = SUC t.vs_inst_idx` by
    (qpat_assum `emit_op _ _ sm = _`
      (mp_tac o MATCH_MP emitHelperPropsTheory.emitted_insts_emit_op) >> simp[]) >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx ee t` by
    (qpat_assum `vv_post _ _ _ _ _ e es sa sm s ee tv vv t`
       (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE [vv_post_def])) >>
  `alloca_history func at` by
    (`alloca_inv t` by
       (qpat_assum `stmt_state_rel _ _ _ _ _ ee t`
          (ACCEPT_TAC o CONJUNCT2 o MATCH_MP stmt_state_rel_local_ptrs_alloca)) >>
     `run_inst_seq [ai] t = OK au` by
       simp[run_inst_seq_def,Abbr `ai`,Abbr `au`,Abbr `out`,
            step_inst_base_opcode_eqs,mk_inst_def,exec_pure2_def,eval_operand_def] >>
     `alloca_history func (au with vs_inst_idx := LENGTH sn.cs_current_insts)` by
       (irule emitted_alloca_history >> simp[] >>
        qexistsl_tac [`[ai]`,`t`,`sm`] >>
        qpat_assum `emit_op _ _ sm = _`
          (mp_tac o MATCH_MP emitHelperPropsTheory.emitted_insts_emit_op) >>
        simp[Abbr `ai`,Abbr `out`,mk_inst_def,is_terminator_def]) >>
     simp[Abbr `at`] >>
     qpat_assum `alloca_history func (_ with vs_inst_idx := _)` mp_tac >>
     qpat_assum `LENGTH sn.cs_current_insts = SUC t.vs_inst_idx` mp_tac >>
     qpat_assum `t.vs_inst_idx = LENGTH sm.cs_current_insts` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  suspend "unwrap"
QED

Resume make_array_slot_full_bundled[unwrap]:
  `fn_has_code sn sc func` by metis_tac[fn_has_code_split,cs_extends_trans] >>
  mp_tac (Q.INST [`sb` |-> `sn`, `op` |-> `src`, `s` |-> `at`,
    `s0` |-> `s`, `G` |-> `Ga`, `tn` |-> `tna`, `Gi` |-> `G`, `ti` |-> `tn`,
    `rty` |-> `ptv`, `ty` |-> `expr_type e`,
    `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
    (SPEC_ALL unwrap_value_origin_ptr)) >>
  impl_tac >-
    (simp[Abbr `at`,Abbr `au`,update_var_def] >> rpt conj_tac
     >- (qpat_assum `emit_op _ _ sm = _`
           (mp_tac o MATCH_MP emitHelperPropsTheory.emitted_insts_emit_op) >> simp[])
     >- (qpat_assum `emit_op _ _ sm = _`
           (mp_tac o MATCH_MP emitHelperPropsTheory.emitted_insts_emit_op) >> simp[])
     >- (drule aggregateEvaluatedLayoutTheory.body_post_type_allocation_bound >>
         disch_then (qspec_then `ptv` mp_tac) >> simp[])
     >- (rpt strip_tac >>
         `value_runtime_typed env (post_value_type cenv e) v` by
           (irule memory_rhs_read_post_typed >>
            qexistsl_tac [`cx`,`es with gas_obs := gas_explicit marks s.vs_gas_readings`,`ee`] >>
            simp[vyperStateTheory.bind_def,exprSimSourceTheory.expr_body_pre_gas_obs]) >>
         `env.type_defs = get_tenv cx` by
           metis_tac[expr_body_pre_env_type_defs] >>
         gvs[vyperTypeExprSoundnessTheory.value_runtime_typed_def])
     >- (qpat_x_assum `cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==> _` mp_tac >>
         simp[update_var_def])
     ) >>
  strip_tac >>
  `expr_body_pre cenv cx env e (es with gas_obs := gas_explicit marks s.vs_gas_readings)` by
    simp[exprSimSourceTheory.expr_body_pre_gas_obs] >>
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s.vs_gas_readings) = (INL v,ee)` by
    simp[vyperStateTheory.bind_def] >>
  `env.type_defs = get_tenv cx` by
    metis_tac[expr_body_pre_env_type_defs] >>
  `value_runtime_typed env (lowered_value_type cenv e) v` by
    (irule memory_rhs_read_lowered_typed_unwidened >>
     qexistsl_tac [`cx`,`es with gas_obs := gas_explicit marks s.vs_gas_readings`,`ee`] >> simp[vyperStateTheory.bind_def]) >>
  `value_runtime_typed env (expr_type e) v` by
    (irule memory_rhs_read_annotation_typed >>
     qexistsl_tac [`cenv`,`cx`,`es with gas_obs := gas_explicit marks s.vs_gas_readings`,`ee`] >> simp[vyperStateTheory.bind_def]) >>
  qpat_x_assum `value_runtime_typed env (lowered_value_type cenv e) v` mp_tac >>
  qpat_x_assum `value_runtime_typed env (expr_type e) v` mp_tac >>
  simp[vyperTypeExprSoundnessTheory.value_runtime_typed_def] >>
  strip_tac >> strip_tac >>
  rename1 `evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv` >>
  `value_has_type dtv v` by
    metis_tac[cj 1 vyperTypeArgFitsTheory.arg_type_fits_value_has_type] >>
  `type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size stv` by
    metis_tac[expr_sim_inv_memory_size] >>
  `val_wf dtv v /\ val_wf stv v` by
    metis_tac[cj 1 valueEncodingTypingTheory.value_has_type_val_wf] >>
  `fn_has_code sc sb func` by metis_tac[fn_has_code_split,cs_extends_trans] >>
  `not_fresh_at sn out` by
    (qpat_assum `emit_op _ _ sm = _`
       (mp_tac o MATCH_MP emitHelperPropsTheory.emitted_insts_emit_op) >>
     simp[Abbr `out`,not_fresh_at_def] >> strip_tac >> gvs[]) >>
  `lookup_var out at = SOME (n2w (base + off))` by
    simp[Abbr `at`,Abbr `au`,update_var_def,lookup_var_def,finite_mapTheory.FLOOKUP_UPDATE,wordsTheory.word_add_n2w] >>
  `lookup_var out z = SOME (n2w (base + off)) /\
   FLOOKUP G' out = FLOOKUP Ga out /\ op_taint tn' (Var out) = {}` by
    metis_tac[] >>
  `base + off < dimword (:256)` by decide_tac >>
  `ptr_covers G' tn' out z (type_memory_size dtv)` by
    (qpat_assum `ptr_covers G1 tn1 q t cap` mp_tac >>
     qpat_assum `lookup_var q t = _` mp_tac >>
     qpat_assum `FLOOKUP Ga out = _` mp_tac >>
     qpat_assum `FLOOKUP G' out = _` mp_tac >>
     qpat_assum `lookup_var out z = _` mp_tac >>
     qpat_assum `op_taint tn' (Var out) = {}` mp_tac >>
     qpat_assum `base + off < _` mp_tac >>
     qpat_assum `base + cap < _` mp_tac >>
     qpat_assum `off + type_memory_size dtv <= cap` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[ptr_covers_def,ptrDisciplineTheory.op_prov_def] >> rpt strip_tac >>
     qexistsl_tac [`b`,`sz'`] >> simp[] >> decide_tac) >>
  `arg_type_fits (lowered_value_type cenv e) (expr_type e)` by
    metis_tac[expr_body_pre_lowered_fits] >>
  `arg_type_fits (lowered_value_type cenv e) dty` by
    metis_tac[cj 1 typedCopyCompatibilityTheory.arg_type_fits_trans] >>
  `type_widens_to (get_tenv cx) (lowered_value_type cenv e) dty` by
    simp[vyperTypeSystemTheory.type_widens_to_def,
         vyperTypeSystemTheory.well_formed_type_def] >>
  `sn.cs_next_var <= sc.cs_next_var` by
    (qspecl_then [`cenv`,`vv`,`sn`] mp_tac ci_mono_unwrap_value >> simp[ci_mono_def]) >>
  `sm.cs_next_var <= sn.cs_next_var` by
    (mp_tac (Q.SPECL [`ADD`,`[Var q; Lit (n2w off)]`,`sm`,`dst`,`sn`]
      emitHelperPropsTheory.emitted_insts_emit_op) >> simp[]) >>
  `sm.cs_next_var <= sc.cs_next_var` by decide_tac >>
  `local_ptrs_reserved cenv sc` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sm` >> simp[]) >>
  `not_fresh_at sc out` by
    (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sn` >> simp[]) >>
  `expr_post (storage_trace_horizon ee.storage_trace) ctx func cenv cx e
     es sa sc s ee v src z` by metis_tac[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp z` by
    (qpat_assum `expr_post (storage_trace_horizon ee.storage_trace)
       ctx func cenv cx e es sa sc s ee v src z`
       (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp o
        MATCH_MP exprSimWordArgsTheory.expr_post_state)) >>
  `FLOOKUP z.vs_allocas aid = SOME (base,cap)` by metis_tac[expr_post_def] >>
  `allocas_from lo z` by metis_tac[ghost_inv_at_def] >>
  `lo <= base` by metis_tac[ptrDisciplineTheory.allocas_from_def] >>
  `lo <= z.vs_alloca_next` by decide_tac >>
  `~z.vs_halted` by
    (qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path _ (at,Ga,tna) [] (OK z,G',tn') /\ _`
       (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
     qpat_assum `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace)
       ee.storage_trace` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_projections,
       fragGasSeqPtrTheory.gas_path_ptr_ok_not_halted]) >>
  `?u Gf tnf.
    (!D. gas_origin_ptr_path
      (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (z,G',tn') [] (OK u,Gf,tnf)) /\
    typed_copy_state_frame sc (base+off) (type_memory_size dtv) z u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    tnf.t_imm = tn'.t_imm /\ tnf.t_stor = tn'.t_stor /\
    tnf.t_trans = tn'.t_trans /\
    (!i. ~(base+off <= i /\ i < base+off+type_memory_size dtv) ==>
       (i IN tnf.t_mem <=> i IN tn'.t_mem)) /\
    (!mem. mem_agree_outside tnf.t_mem u.vs_memory mem ==>
       val_in_memory dtv v (base+off) mem) /\
    (!p. not_fresh_at sc p ==>
       FLOOKUP Gf p = FLOOKUP G' p /\
       op_taint tnf (Var p) = op_taint tn' (Var p))`
    suffices_by suspend "finish" >>
  Cases_on `is_word_type dty`
  >- suspend "word_store" >>
  suspend "memory_store"
QED

Resume make_array_slot_full_bundled[word_store]:
  `type_widens_to (get_tenv cx) (expr_type e) dty` by
    simp[vyperTypeSystemTheory.type_widens_to_def,
         vyperTypeSystemTheory.well_formed_type_def] >>
  `expr_type e = dty` by metis_tac[type_widens_to_word] >>
  `post_value_type cenv e = dty` by metis_tac[post_value_type_word] >>
  `type_memory_size dtv = 32` by metis_tac[exprSimPropsTheory.word_tv_memory_size] >>
  `ptv = dtv` by
    (qpat_assum `evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME ptv` mp_tac >>
     qpat_assum `evaluate_type (get_tenv cx) dty = SOME dtv` mp_tac >>
     qpat_assum `post_value_type cenv e = dty` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  `eval_operand src z = SOME (typed_val_to_w256 dtv v)` by
    (qpat_assum `expr_post (storage_trace_horizon ee.storage_trace)
       ctx func cenv cx e es sa sc s ee v src z`
       (mp_tac o REWRITE_RULE [expr_post_def,expr_val_rel_def]) >> simp[]) >>
  `op_taint tn' src = {}` by
    (qpat_assum `ptr_val_ok cx (post_value_type cenv e) v src G' tn' z`
       (mp_tac o REWRITE_RULE [ptr_val_ok_def]) >> simp[]) >>
  `w2n (n2w (base+off):bytes32) = base+off` by simp[] >>
  `base+off+32 < dimword (:256) /\ base+off+32 <= z.vs_alloca_next` by decide_tac >>
  `compile_store_memory cenv src (Var out) dty (lowered_value_type cenv e) sc = ((),sb)` by
    (qpat_assum `compile_store_memory cenv src dst dty (lowered_value_type cenv e) sc = ((),sb)` mp_tac >>
     qpat_assum `dst = Var out` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  `ptr_covers G' tn' out z 32` by
    (qpat_assum `ptr_covers G' tn' out z (type_memory_size dtv)` mp_tac >>
     qpat_assum `type_memory_size dtv = 32` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  mp_tac (Q.INST [`sa` |-> `sc`, `s` |-> `z`, `G` |-> `G'`, `tn` |-> `tn'`,
    `xd` |-> `out`, `dw` |-> `n2w (base+off)`,
    `sty` |-> `lowered_value_type cenv e`, `tenv` |-> `get_tenv cx`,
    `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
    compile_store_memory_word_origin_ptr_path) >>
  impl_tac >- simp[] >> strip_tac >>
  qpat_assum `w2n (n2w (base+off):bytes32) = base+off`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  qexistsl_tac [`t'`,`Gf`,`tnf`] >> simp[]
QED

Resume make_array_slot_full_bundled[memory_store]:
  `~is_word_type (expr_type e)` by
    metis_tac[aggregateEvaluatedLayoutTheory.arg_type_fits_word_type] >>
  `~is_word_type (post_value_type cenv e)` by
    metis_tac[exprSimIfExpWidenedPhysicalTypeTheory.post_value_type_nonword] >>
  `?sw. eval_operand src z = SOME sw` by
    (qpat_assum `expr_post (storage_trace_horizon ee.storage_trace)
       ctx func cenv cx e es sa sc s ee v src z`
       (mp_tac o REWRITE_RULE [expr_post_def,expr_val_rel_def]) >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  Cases_on `type_memory_size stv = 0`
  >- suspend "zero_store" >>
  suspend "positive_store"
QED

Resume make_array_slot_full_bundled[zero_store]:
  `lowered_value_type cenv e = dty` by metis_tac[type_widens_to_zero_layout] >>
  `stv = dtv /\ type_memory_size dtv = 0` by
    (qpat_assum `evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv` mp_tac >>
     qpat_assum `evaluate_type (get_tenv cx) dty = SOME dtv` mp_tac >>
     qpat_assum `lowered_value_type cenv e = dty` mp_tac >>
     qpat_assum `type_memory_size stv = 0` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  `~is_bytestring_type dty` by
    (mp_tac (Q.SPECL [`cenv`,`dty`] valueCopyBytesTheory.bytestring_memory_bytes_positive) >> simp[]) >>
  `post_value_type cenv e = dty` by
    metis_tac[abiEncodeMaterializeTheory.materialize_post_lowered_classify] >>
  `ptv = dtv` by
    (qpat_assum `evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME ptv` mp_tac >>
     qpat_assum `evaluate_type (get_tenv cx) dty = SOME dtv` mp_tac >>
     qpat_assum `post_value_type cenv e = dty` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  `sb = sc` by
    (qpat_x_assum `compile_store_memory cenv src dst dty (lowered_value_type cenv e) sc = ((),sb)` mp_tac >>
     simp[compile_store_memory_def,compile_copy_memory_def,comp_return_def]) >>
  `!mem. mem_agree_outside tn'.t_mem z.vs_memory mem ==>
      val_in_memory dtv v (w2n sw) mem` by
    (qpat_assum `ptr_val_ok cx (post_value_type cenv e) v src G' tn' z`
       (mp_tac o REWRITE_RULE [ptr_val_ok_def,ptr_mem_ok_def]) >>
     simp[] >> metis_tac[]) >>
  `val_footprint dtv v = 0` by
    (`val_footprint dtv v <= type_memory_size dtv` by
       metis_tac[exprSimPropsTheory.val_footprint_le] >> decide_tac) >>
  `!mem. mem_agree_outside tn'.t_mem z.vs_memory mem ==>
      val_in_memory dtv v (base+off) mem` by
    (mp_tac (Q.SPECL [`dtv`,`v`,`w2n (sw:bytes32)`,`base+off`,`0`,
       `tn'.t_mem`,`tn'.t_mem`,`z.vs_memory`,`z.vs_memory`]
       robustCopyTransportPtrTheory.robust_val_in_memory_copy_transport) >>
     simp[valueEncodingDefsTheory.mem_bytes_at_def]) >>
  qexistsl_tac [`z`,`G'`,`tn'`] >> simp[typedMemoryCopyTheory.typed_copy_state_frame_refl] >>
  gen_tac >> irule (cj 1 fragGasOriginPtrTheory.gas_origin_ptr_path_rules) >> simp[]
QED

Resume make_array_slot_full_bundled[positive_store]:
  `ptr_buf_ok cenv e src G' z` by metis_tac[] >>
  `?xs. src = Var xs` by
    (qpat_assum `ptr_buf_ok cenv e src G' z`
       (mp_tac o REWRITE_RULE [ptr_buf_ok_def]) >>
     disch_then (qspec_then `sw` mp_tac) >>
     qpat_assum `type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size stv` mp_tac >>
     qpat_assum `type_memory_size stv <> 0` mp_tac >>
     qpat_assum `eval_operand src z = SOME sw` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[] >> metis_tac[]) >>
  qpat_x_assum `src = Var xs` SUBST_ALL_TAC >>
  `lookup_var xs z = SOME sw` by
    (qpat_assum `eval_operand (Var xs) z = SOME sw`
       (mp_tac o REWRITE_RULE [eval_operand_def]) >> simp[]) >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sn x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sm` >> simp[] >> metis_tac[]) >>
  `not_fresh_at sc xs` by
    (qpat_assum `unwrap_value cenv vv sn = (Var xs,sc)` mp_tac >>
     qpat_assum `!x. vv_operand vv = Var x ==> not_fresh_at sn x` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     mp_tac (Q.INST [`sa` |-> `sn`, `sb` |-> `sc`, `op` |-> `Var xs`]
       exprOperandVarTheory.compiler_unwrap_value_var) >>
     impl_tac >- (simp[] >> Cases_on `vv` >> gvs[contextTheory.vv_operand_def]) >>
     simp[]) >>
  mp_tac (Q.INST [`ce` |-> `cenv`, `G` |-> `G'`, `tn` |-> `tn'`,
    `pt` |-> `ptv`, `lt` |-> `stv`] make_array_physical_store_input) >>
  impl_tac >- simp[] >> strip_tac >>
  `ptr_covers G' tn' xs z (type_memory_size stv)` by metis_tac[] >>
  Cases_on `is_bytestring_type dty`
  >- suspend "bytes_store" >>
  suspend "aggregate_store"
QED

Resume make_array_slot_full_bundled[bytes_store]:
  `is_bytestring_type (lowered_value_type cenv e)` by
    metis_tac[compileEnvTheory.arg_type_fits_bytestring_source] >>
  `compile_store_bytestring (Var xs) (Var out) sc = ((),sb)` by
    gvs[compile_store_memory_def] >>
  `?len. ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
          (?str. v = StringV str /\ len = LENGTH str)) /\
      val_store_size stv v = 32 + 32 * ((len+31) DIV 32) /\
      val_store_size dtv v = 32 + 32 * ((len+31) DIV 32)` by
    (qpat_assum `is_bytestring_type dty` mp_tac >>
     qpat_assum `evaluate_type (get_tenv cx) dty = SOME dtv` mp_tac >>
     qpat_assum `value_has_type dtv v` mp_tac >>
     `val_store_size stv v = val_store_size dtv v` by
       metis_tac[valueCopyBytesTheory.bytestring_val_store_size_eq] >>
     pop_assum mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     rpt strip_tac >>
     drule_all valueCopyBytesTheory.bytestring_type_value >> strip_tac >>
     Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def,
       exprSimPropsTheory.val_store_size_def] >>
     simp[vfmConstantsTheory.word_size_def] >> metis_tac[]) >>
  qabbrev_tac `n = 32 + 32 * ((len+31) DIV 32)` >>
  `n <= type_memory_size stv /\ n <= type_memory_size dtv` by
    metis_tac[exprSimPropsTheory.val_store_size_le] >>
  `n < dimword (:256)` by decide_tac >>
  `len+31 < dimword (:256)` by
    (mp_tac (Q.SPEC `len` exprSimPropsTheory.le_word_size_mul) >>
     qpat_assum `n < dimword (:256)` mp_tac >>
     qpat_assum `Abbrev (n = _)` (mp_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[vfmConstantsTheory.word_size_def] >> decide_tac) >>
  `ptr_covers G' tn' xs z n /\ ptr_covers G' tn' out z n` by
    (conj_tac
     >- (irule reasonCopySourcePtrTheory.ptr_covers_mono >>
         qexists_tac `type_memory_size stv` >> simp[]) >>
     irule reasonCopySourcePtrTheory.ptr_covers_mono >>
     qexists_tac `type_memory_size dtv` >> simp[]) >>
  mp_tac (Q.INST [`sa` |-> `sc`, `s` |-> `z`, `G` |-> `G'`, `tn` |-> `tn'`,
    `src` |-> `xs`, `dst` |-> `out`, `a` |-> `sw`, `b` |-> `n2w (base+off)`,
    `sty` |-> `lowered_value_type cenv e`, `tenv` |-> `get_tenv cx`,
    `fn` |-> `func`,
    `D` |-> `<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |>`]
    compile_store_bytestring_robust_seq_ptr) >>
  (impl_tac >- (simp[Abbr `n`] >> metis_tac[])) >> strip_tac >>
  `w2n (n2w (base+off):bytes32) = base+off` by simp[] >>
  qpat_assum `w2n (n2w (base+off):bytes32) = base+off`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  `val_in_memory stv v (w2n sw) z.vs_memory` by
    (qpat_assum `!mem. mem_agree_outside tn'.t_mem z.vs_memory mem ==>
       val_in_memory stv v (w2n sw) mem` irule >>
     simp[mem_agree_outside_def]) >>
  mp_tac (Q.SPECL [`get_tenv cx`,`lowered_value_type cenv e`,`stv`,`v`,
    `w2n (sw:bytes32)`,`z`] buffer_typed_bytestring_header) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `hlen` strip_assume_tac) >>
  `n = 32 + 32 * word_size hlen` by metis_tac[] >>
  `w2n sw + type_memory_size stv <= z.vs_alloca_next` by metis_tac[] >>
  `w2n sw+n <= z.vs_alloca_next /\ base+off+n <= z.vs_alloca_next` by decide_tac >>
  mp_tac (Q.INST [`src` |-> `Var xs`, `dst` |-> `Var out`,
    `sa` |-> `sc`, `s` |-> `z`, `w` |-> `sw`,
    `d` |-> `n2w (base+off)`, `len` |-> `hlen`]
    compile_store_bytestring_body_mem_ok) >>
  (impl_tac >-
    (simp[eval_operand_def] >>
     qpat_assum `not_fresh_at sc xs` mp_tac >>
     qpat_assum `not_fresh_at sc out` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[])) >> disch_tac >>
  drule buffer_store_bytestring_shape >> strip_tac >>
  `?codebb. lookup_block z.vs_current_bb func.fn_blocks = SOME codebb /\
     isPREFIX (emitted_insts sc sb) (DROP z.vs_inst_idx codebb.bb_instructions)` by
    (qpat_assum `fn_has_code sc sb func` mp_tac >>
     qpat_assum `same_blocks sc sb` mp_tac >>
     qpat_assum `sb.cs_current_insts = sc.cs_current_insts ++ emitted_insts sc sb` mp_tac >>
     qpat_assum `z.vs_current_bb = sc.cs_current_bb` mp_tac >>
     qpat_assum `z.vs_inst_idx = LENGTH sc.cs_current_insts` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[fn_has_code_def,same_blocks_def,rich_listTheory.IS_PREFIX_APPEND] >>
     rpt strip_tac >> gvs[] >>
     simp[listTheory.APPEND_ASSOC,rich_listTheory.DROP_APPEND1]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
     i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS /\
     i.inst_opcode <> DALLOCA) (emitted_insts sc sb)` by
    (mp_tac (Q.INST [`src` |-> `Var xs`, `dst` |-> `Var out`, `sa` |-> `sc`]
       logBytesCodePtrTheory.compile_store_bytestring_opcodes) >>
     (impl_tac >- simp[]) >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[listTheory.EVERY_MEM] >> strip_tac >> qx_gen_tac `inst` >> strip_tac >>
     qpat_x_assum `!i. MEM i (emitted_insts sc sb) ==> _` drule >>
     strip_tac >> gvs[is_terminator_def]) >>
  mp_tac (Q.INST [`s` |-> `z`, `t` |-> `sf`, `G` |-> `G'`, `tn` |-> `tn'`,
    `G'` |-> `Gf`, `tn'` |-> `tnf`, `code` |-> `emitted_insts sc sb`,
    `bb` |-> `codebb`, `explicit` |-> `gas_explicit_sites ctx shadow_ctx`,
    `D` |-> `<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |>`]
    run_inst_seq_origin_ptr_lift) >>
  (impl_tac >-
    (simp[] >> conj_tac
     >- (qpat_assum `EVERY _ (emitted_insts sc sb)` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> simp[listTheory.EVERY_MEM] >> metis_tac[]) >>
     rpt strip_tac >>
     irule memSafeRunTheory.dalloca_no_wrap_non_dalloca >>
     qpat_assum `EVERY _ (emitted_insts sc sb)` mp_tac >>
     qpat_assum `emitted_insts sc sb = _ ++ [i] ++ _` (fn th =>
       pure_once_rewrite_tac [th]) >>
     simp[listTheory.EVERY_APPEND])) >>
  strip_tac >>
  suspend "bytes_finish"
QED

Resume make_array_slot_full_bundled[bytes_finish]:
  markerLib.RESUME_TAC >>
  mp_tac (Q.SPECL [`Var xs`,`Var out`,`sc`,`sb`,`z`,`sw`,
    `n2w (base+off)`,`hlen`] buffer_store_bytestring_run) >>
  (impl_tac >-
    (simp[eval_operand_def] >>
     qpat_assum `not_fresh_at sc xs` mp_tac >>
     qpat_assum `not_fresh_at sc out` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[])) >>
  disch_then (qx_choose_then `copy_raw` strip_assume_tac) >>
  `copy_raw = sf` by
    (qpat_assum `run_inst_seq (emitted_insts sc sb) z = OK copy_raw` mp_tac >>
     qpat_assum `run_inst_seq (emitted_insts sc sb) z = OK sf` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[]) >>
  qpat_x_assum `copy_raw = sf` SUBST_ALL_TAC >>
  `z.vs_inst_idx + LENGTH (emitted_insts sc sb) = LENGTH sb.cs_current_insts` by
    (qpat_assum `sb.cs_current_insts = sc.cs_current_insts ++ emitted_insts sc sb` mp_tac >>
     qpat_assum `z.vs_inst_idx = LENGTH sc.cs_current_insts` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> simp[]) >>
  `!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (z,G',tn') [] (OK (sf with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tnf)` by
    (gen_tac >> irule gas_origin_ptr_path_from_no_dead >>
     qpat_assum `gas_origin_ptr_path _ (z,G',tn') []
       (OK (sf with vs_inst_idx := _),Gf,tnf)` mp_tac >>
     qpat_assum `z.vs_inst_idx + LENGTH (emitted_insts sc sb) = LENGTH sb.cs_current_insts` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[]) >>
  `typedMemoryCopy$typed_copy_frame (base+off) n z.vs_memory sf.vs_memory` by
    (mp_tac (Q.INST [`sa` |-> `sc`, `dst` |-> `base+off`,
       `src` |-> `w2n (sw:bytes32)`, `s` |-> `z`, `idx` |-> `0`]
       typedMemoryCopyTheory.typed_copy_mcopy_state_frame) >>
     qpat_assum `sf.vs_memory = (mcopy (base+off) (w2n sw) n z).vs_memory` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[typedMemoryCopyTheory.typed_copy_state_frame_def] >>
     rpt strip_tac >> gvs[]) >>
  `typed_copy_state_frame sc (base+off) (type_memory_size dtv) z
     (sf with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule typedMemoryCopyTheory.typed_copy_state_frame_subinterval >>
     qexistsl_tac [`base+off`,`n`] >> simp[] >>
     simp[typedMemoryCopyTheory.typed_copy_state_frame_def] >>
     conj_tac
     >- (qpat_assum `(sf with <|vs_vars := z.vs_vars; vs_memory := z.vs_memory|>) = z` mp_tac >>
         qpat_assum `z.vs_current_bb = sc.cs_current_bb` mp_tac >>
         qpat_assum `z.vs_inst_idx = LENGTH sc.cs_current_insts` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[venom_state_component_equality] >> rpt strip_tac >> simp[]) >>
     conj_tac
     >- (qx_gen_tac `old` >> strip_tac >>
         qpat_assum `!p. not_fresh_at sc p ==> lookup_var p sf = lookup_var p z /\ _` mp_tac >>
         qpat_assum `not_fresh_at sc old` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> simp[lookup_var_def] >> metis_tac[]) >>
     qpat_assum `typedMemoryCopy$typed_copy_frame (base+off) n z.vs_memory sf.vs_memory` mp_tac >>
     qpat_assum `sf.vs_memory = (mcopy (base+off) (w2n sw) n z).vs_memory` mp_tac >>
     qpat_assum `n = 32 + 32 * word_size hlen` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     `32 * word_size hlen + 32 = n` by decide_tac >>
     pop_assum SUBST1_TAC >>
     qpat_assum `sf.vs_memory = (mcopy (base+off) (w2n sw) n z).vs_memory`
       (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  `~sf.vs_halted /\ sf.vs_current_bb = sb.cs_current_bb` by
    (qpat_assum `(sf with <|vs_vars := z.vs_vars; vs_memory := z.vs_memory|>) = z` mp_tac >>
     qpat_assum `~z.vs_halted` mp_tac >>
     qpat_assum `z.vs_current_bb = sc.cs_current_bb` mp_tac >>
     qpat_assum `same_blocks sc sb` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[same_blocks_def,venom_state_component_equality] >> rpt strip_tac >> simp[]) >>
  qexistsl_tac [`sf with vs_inst_idx := LENGTH sb.cs_current_insts`,`Gf`,`tnf`] >> simp[] >>
  qx_gen_tac `i` >> strip_tac >>
  qpat_assum `!i. ~(base+off <= i /\ i < base+off+n) ==> _` irule >>
  qpat_assum `n <= type_memory_size dtv` mp_tac >>
  qpat_assum `~(base+off <= i /\ i < base+off+type_memory_size dtv)` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> decide_tac
QED

Resume make_array_slot_full_bundled[aggregate_store]:
  `post_value_type cenv e = lowered_value_type cenv e` by
    (qpat_assum `~is_word_type (expr_type e)` mp_tac >>
     qpat_assum `arg_type_fits (lowered_value_type cenv e) (expr_type e)` mp_tac >>
     qpat_assum `arg_type_fits (lowered_value_type cenv e) dty` mp_tac >>
     qpat_assum `~is_bytestring_type dty` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[abiEncodeMaterializeTheory.materialize_post_lowered_classify,
       valueCopyBytesTheory.arg_type_fits_bytestring_target]) >>
  `ptv = stv` by
    (qpat_assum `evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME ptv` mp_tac >>
     qpat_assum `evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv` mp_tac >>
     qpat_assum `post_value_type cenv e = lowered_value_type cenv e` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  `expr_val_at cenv cx (lowered_value_type cenv e) sa sc ee v (Var xs) z` by
    metis_tac[expr_post_def] >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx ee z` by
    metis_tac[expr_post_def] >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by metis_tac[expr_post_def] >>
  `?observations. ee.storage_trace = es.storage_trace ++ observations` by
    (qpat_assum `eval_expr cx e (es with gas_obs := _) = (INL tv,ee)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> strip_tac >>
     `storage_trace_frame (eval_expr cx e)` by simp[cj 5 vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
     drule_all storage_trace_frame_prefix >> simp[]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) es.storage_trace` by
    metis_tac[valid_horizon_append] >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx es s` by
    metis_tac[] >>
  `local_ptrs_rel func cenv es.scopes s` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ es s`
       (ACCEPT_TAC o CONJUNCT1 o MATCH_MP stmt_state_rel_local_ptrs_alloca)) >>
  `!name b n. local_region cenv ee.scopes z name b n ==>
     loweringStateRelDefs$regions_disjoint base cap b n` by
    (rpt strip_tac >>
     `local_region cenv es.scopes s name b n` by
       (mp_tac (Q.SPECL [`func`,`cenv`,`es.scopes`,`s`,`sa`,
          `ee.scopes`,`z`,`name`,`b`,`n`] exprSimPropsTheory.local_region_frame) >>
        (impl_tac >- (simp[] >> metis_tac[expr_post_def])) >> simp[]) >> metis_tac[]) >>
  `~is_bytestring_type (lowered_value_type cenv e)` by
    (qpat_assum `~is_bytestring_type dty` mp_tac >>
     qpat_assum `arg_type_fits (lowered_value_type cenv e) dty` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[valueCopyBytesTheory.arg_type_fits_bytestring_target]) >>
  `~is_word_type (lowered_value_type cenv e)` by
    metis_tac[aggregateEvaluatedLayoutTheory.arg_type_fits_word_type] >>
  (Q.SUBGOAL_THEN
   `w2n sw + type_memory_size stv < dimword (:256) /\
   (w2n sw + type_memory_size stv <= w2n (n2w (base+off):bytes32) \/
    w2n (n2w (base+off):bytes32)+type_memory_size dtv <= w2n sw)`
   (CONJUNCTS_THEN assume_tac) >-
    (irule (INST_TYPE [alpha |-> ``:256``] aggregate_physical_source_slot_bounds) >>
     qpat_assum `expr_val_at cenv cx (lowered_value_type cenv e) sa sc ee v (Var xs) z`
       (irule_at Any) >>
     qexistsl_tac [`cap`,`func`,`dty`,`aid`,`ctx`,`base`,
       `storage_trace_horizon ee.storage_trace`] >>
     simp[] >> rpt strip_tac >>
     qpat_assum `!name b n. local_region cenv ee.scopes z name b n ==> _` drule >>
     qpat_assum `off + type_memory_size dtv <= cap` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac)) >>
  `acyclic_struct_metadata cenv.ce_struct_fields` by
    (qpat_assum `body_inv tops ctx cenv cx`
       (ACCEPT_TAC o MATCH_MP contract_inv_acyclic_struct_metadata o
        MATCH_MP bodySimTheory.body_inv_contract)) >>
  `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
   (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !rt. evaluate_type (get_tenv cx) fty = SOME rt ==>
       sz = type_memory_size rt) fields)` by
    (qpat_assum `expr_sim_inv cenv cx env ebase` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     REWRITE_TAC[exprSimHypsDefsTheory.expr_sim_inv_def] >>
     strip_tac >> conj_tac >> first_assum ACCEPT_TAC) >>
  `compile_store_memory cenv (Var xs) (Var out) dty (lowered_value_type cenv e) sc = ((),sb)` by
    (qpat_assum `compile_store_memory cenv (Var xs) dst dty (lowered_value_type cenv e) sc = ((),sb)` mp_tac >>
     qpat_assum `dst = Var out` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  `w2n (n2w (base+off):bytes32) = base+off` by simp[] >>
  `base+off+type_memory_size dtv < dimword (:256) /\
   base+off+type_memory_size dtv <= z.vs_alloca_next` by decide_tac >>
  `w2n sw+type_memory_size stv <= z.vs_alloca_next` by metis_tac[] >>
  mp_tac (Q.INST [`sa` |-> `sc`, `s` |-> `z`, `G` |-> `G'`, `tn` |-> `tn'`,
    `xd` |-> `out`, `dw` |-> `n2w (base+off)`,
    `sty` |-> `lowered_value_type cenv e`, `tenv` |-> `get_tenv cx`,
    `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
    compile_store_memory_origin_ptr_path) >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qpat_assum `w2n (n2w (base+off):bytes32) = base+off`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  qexistsl_tac [`t'`,`Gf`,`tnf`] >> simp[]
QED

Resume make_array_slot_full_bundled[finish]:
  markerLib.RESUME_TAC >> strip_tac >>
  qpat_assum `typed_copy_state_frame sc (base+off) (type_memory_size dtv) z u`
    (strip_assume_tac o REWRITE_RULE
      [typedMemoryCopyTheory.typed_copy_state_frame_def,
       typedMemoryCopyTheory.typed_copy_frame_def]) >>
  `u.vs_allocas = z.vs_allocas /\ u.vs_alloca_next = z.vs_alloca_next /\
   u.vs_accounts = z.vs_accounts /\ u.vs_transient = z.vs_transient /\
   u.vs_requests = z.vs_requests /\ u.vs_call_ctx = z.vs_call_ctx /\
   u.vs_immutables = z.vs_immutables` by
    (qpat_assum `(u with <|vs_vars := z.vs_vars; vs_memory := z.vs_memory;
       vs_prev_bb := z.vs_prev_bb; vs_current_bb := z.vs_current_bb;
       vs_inst_idx := z.vs_inst_idx|>) = z` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[venom_state_component_equality] >> strip_tac >> simp[]) >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx ee z` by
    metis_tac[expr_post_def] >>
  `alloca_inv z` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ ee z`
       (ACCEPT_TAC o CONJUNCT2 o MATCH_MP stmt_state_rel_local_ptrs_alloca)) >>
  `gas_path_mem ctx func z 0 (OK u)` by
    (qpat_assum `!D. gas_origin_ptr_path _ (z,G',tn') [] (OK u,Gf,tnf)`
       (qspec_then `DF (storage_trace_horizon ee.storage_trace)` mp_tac) >>
     POP_ASSUM_LIST (K all_tac) >> strip_tac >>
     drule fragGasOriginPtrTheory.gas_origin_ptr_path_projections >> strip_tac >>
     drule fragGasOriginTheory.gas_origin_path_erase >>
     simp[fragGasModeTheory.gas_marked_path_def]) >>
  `alloca_history func u` by
    (irule gas_path_mem_zero_history >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`ctx`,`z`] >> simp[] >>
     rpt strip_tac >> irule aggregate_mem_path_alloca_inv >>
     goal_assum (drule_at Any) >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (t,G1,tn1) [] (OK u,Gf,tnf)` by
    (rpt strip_tac >>
     `gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (t,G1,tn1) [] (OK at,Ga,tna)` by
       metis_tac[ghost_inv_at_def] >>
     `gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (at,Ga,tna) [] (OK z,G',tn')` by metis_tac[] >>
     qpat_assum `gas_origin_ptr_path _ (t,G1,tn1) [] (OK at,Ga,tna)` mp_tac >>
     qpat_assum `gas_origin_ptr_path _ (at,Ga,tna) [] (OK z,G',tn')` mp_tac >>
     qpat_assum `!D. gas_origin_ptr_path _ (z,G',tn') [] (OK u,Gf,tnf)`
       (qspec_then `DF H` mp_tac) >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_append,listTheory.APPEND_NIL]) >>
  irule gas_outcome_full_pure >> simp[] >>
  qexistsl_tac [`Gf`,`ee`,`INL v`,`u`,`tnf`] >>
  conj_tac >- metis_tac[exprSimMemorySourceTheory.read_result_gas_obs] >>
  rpt strip_tac >> simp[] >>
  suspend "finish_frame"
QED

Resume make_array_slot_full_bundled[finish_frame]:
  markerLib.RESUME_TAC >>
  `mem_bytes_at base cap z.vs_memory = mem_bytes_at base cap s.vs_memory` by
    (qpat_assum `expr_post (storage_trace_horizon ee.storage_trace)
       ctx func cenv cx e es sa sc s ee v src z` mp_tac >>
     qpat_assum `FLOOKUP s.vs_allocas aid = SOME (base,cap)` mp_tac >>
     qpat_assum `aid < sa.cs_next_id` mp_tac >>
     qpat_assum `!name b n. local_region cenv es.scopes s name b n ==> _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     REWRITE_TAC[expr_post_def,loweringStateRelDefsTheory.regions_disjoint_def] >>
     metis_tac[]) >>
  `EVERY (\(rt,pv,p,n).
     val_wf rt pv /\ val_footprint rt pv <= n /\
     base <= p /\ n+p <= base+off /\
     !mem. mem_agree_outside tnf.t_mem u.vs_memory mem ==>
       val_in_memory rt pv p mem) ps` by
    (REWRITE_TAC[listTheory.EVERY_MEM] >> qx_gen_tac `cell` >>
     PairCases_on `cell` >> BETA_TAC >> strip_tac >>
     rename1 `MEM (rt,pv,p,n) ps` >>
     qpat_assum `EVERY _ ps` (mp_tac o REWRITE_RULE[listTheory.EVERY_MEM]) >>
     disch_then (qspec_then `(rt,pv,p,n)` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
     `base+(p-base) = p /\ p-base+val_footprint rt pv <= cap /\
      p+val_footprint rt pv <= base+off /\ off <= cap` by decide_tac >>
     `mem_bytes_at p (val_footprint rt pv) z.vs_memory =
      mem_bytes_at p (val_footprint rt pv) s.vs_memory` by
       (mp_tac (Q.SPECL [`base`,`base`,`cap`,`z.vs_memory`,`s.vs_memory`,
          `p-base`,`val_footprint rt pv`]
          valueEncodingPropsTheory.mem_bytes_at_translated_window) >> simp[]) >>
     `!i. p <= i /\ i < p+val_footprint rt pv /\ i IN tn'.t_mem ==>
       i IN tn.t_mem` by
       (qpat_assum `ghost_kept_at lo cenv es sa G tn s G' tn'`
          (strip_assume_tac o REWRITE_RULE[ghost_kept_at_def]) >>
        rpt strip_tac >>
        qpat_assum `!aid b n i. FLOOKUP s.vs_allocas aid = SOME (b,n) /\ _ ==> _`
          (qspecl_then [`aid`,`base`,`cap`,`i`] mp_tac) >>
        (impl_tac >- (simp[loweringStateRelDefsTheory.regions_disjoint_def] >>
          metis_tac[loweringStateRelDefsTheory.regions_disjoint_def])) >> simp[]) >>
     `!mem. mem_agree_outside tn'.t_mem z.vs_memory mem ==>
       val_in_memory rt pv p mem` by
       (mp_tac (Q.SPECL [`rt`,`pv`,`p`,`tn.t_mem`,`tn'.t_mem`,
          `s.vs_memory`,`z.vs_memory`]
          logValueFramePtrTheory.robust_val_in_memory_footprint_frame) >> simp[]) >>
     `!mem. mem_agree_outside tnf.t_mem u.vs_memory mem ==>
       val_in_memory rt pv p mem` by
       (mp_tac (Q.SPECL [`tn'.t_mem`,`tnf.t_mem`,`z.vs_memory`,`u.vs_memory`,
          `{i | base+off <= i /\ i < base+off+type_memory_size dtv}`,
          `rt`,`pv`,`p`]
          robustCopyTransportPtrTheory.robust_val_in_memory_exterior_frame) >>
        (impl_tac >-
          (rpt conj_tac
           >- first_assum ACCEPT_TAC
           >- (simp[pred_setTheory.GSPECIFICATION] >> rpt strip_tac >> decide_tac)
           >- (simp[pred_setTheory.GSPECIFICATION] >> rpt strip_tac >>
               qpat_assum `!a k. _ ==> mem_bytes_at a k u.vs_memory =
                 mem_bytes_at a k z.vs_memory`
                 (qspecl_then [`i`,`1`] mp_tac) >>
               (impl_tac >- decide_tac) >> simp[])
           >- simp[pred_setTheory.GSPECIFICATION]
           >- first_assum ACCEPT_TAC)) >> simp[]) >> simp[]) >>
  `!p n. base+off+type_memory_size dtv <= p /\ p+n <= base+cap ==>
    mem_bytes_at p n z.vs_memory = mem_bytes_at p n s.vs_memory` by
    (rpt strip_tac >>
     `base <= p /\ base+(p-base) = p /\ p-base+n <= cap` by decide_tac >>
     mp_tac (Q.SPECL [`base`,`base`,`cap`,`z.vs_memory`,`s.vs_memory`,
       `p-base`,`n`] valueEncodingPropsTheory.mem_bytes_at_translated_window) >> simp[]) >>
  simp[] >> suspend "finish_parent"
QED

Resume make_array_slot_full_bundled[finish_parent]:
  markerLib.RESUME_TAC >>
  `?observations. ee.storage_trace = es.storage_trace ++ observations` by
    (qpat_assum `eval_expr cx e (es with gas_obs := _) = (INL tv,ee)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> strip_tac >>
     `storage_trace_frame (eval_expr cx e)` by simp[cj 5 vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
     drule_all storage_trace_frame_prefix >> simp[]) >>
  `?events'. ee.storage_trace = ebase.storage_trace ++ events'` by
    (qpat_assum `ee.storage_trace = es.storage_trace ++ observations` mp_tac >>
     qpat_assum `es.storage_trace = ebase.storage_trace ++ events` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[listTheory.APPEND_ASSOC]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ebase.storage_trace` by
    metis_tac[valid_horizon_append] >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx ebase sbase` by
    metis_tac[] >>
  `wb_frame cenv es ee sa s z` by metis_tac[exprSimWordArgsTheory.expr_post_frame] >>
  `wb_frame cenv ebase ee csbase sbase z` by
    (mp_tac (Q.INST [`H` |-> `storage_trace_horizon ee.storage_trace`]
       (Q.SPECL [`func`,`cenv`,`cx`,`ebase`,`sbase`,`csbase`,`es`,`ee`,`sa`,`s`,`z`,`ctx`]
         (INST_TYPE [alpha |-> ``:256``] exprSimWordArgsTheory.wb_frame_trans))) >>
     (impl_tac >- simp[]) >> simp[]) >>
  `ghost_kept_at lo cenv ebase csbase Gbase tnbase sbase G' tn'` by
    (mp_tac (Q.SPECL [`lo`,`cenv`,`ebase`,`csbase`,`Gbase`,`tnbase`,`sbase`,
       `G`,`tn`,`es`,`sa`,`G'`,`tn'`,`s`,`storage_trace_horizon ee.storage_trace`,
       `ctx`,`func`,`cx`,`es`]
       (INST_TYPE [alpha |-> ``:num # num``, ``:'b`` |-> ``:256``]
         wordArgsPtrTheory.ghost_kept_at_wb_trans)) >>
     (impl_tac >- simp[]) >> simp[]) >>
  `~expr_has_effect e ==> pure_frame cenv func es sa s z` by
    metis_tac[exprSimWordArgsTheory.expr_post_pure_frame] >>
  `~expr_has_effect e ==>
    (!name b n. local_region cenv es.scopes s name b n ==>
      mem_bytes_at b n u.vs_memory = mem_bytes_at b n s.vs_memory) /\
    !p n. (p+n <= base \/ base+cap <= p) /\
      (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
        sa.cs_next_id <= inst.inst_id /\
        FLOOKUP u.vs_allocas inst.inst_id = SOME (b,sz) ==>
        loweringStateRelDefs$regions_disjoint p n b sz) ==>
      mem_bytes_at p n u.vs_memory = mem_bytes_at p n s.vs_memory` by
    (strip_tac >>
     mp_tac (Q.SPECL [`cenv`,`func`,`es`,`sa`,`s`,`z`,`u`,`base`,`cap`,
       `base+off`,`type_memory_size dtv`] aggregate_pure_frame_store) >>
     (impl_tac >-
       (simp[] >>
        qpat_assum `!name b n. local_region cenv es.scopes s name b n ==> _` mp_tac >>
        qpat_assum `!a k. _ ==> mem_bytes_at a k u.vs_memory =
          mem_bytes_at a k z.vs_memory` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >>
        REWRITE_TAC[loweringStateRelDefsTheory.regions_disjoint_def,arithmeticTheory.ADD_ASSOC] >>
        metis_tac[])) >> simp[]) >>
  `ci_mono sm sn` by
    (mp_tac (Q.SPECL [`ADD`,`[Var q; Lit (n2w off)]`,`sm`] ci_mono_emit_op) >> simp[]) >>
  `ci_mono sn sc` by
    (mp_tac (Q.SPECL [`cenv`,`vv`,`sn`] ci_mono_unwrap_value) >> simp[]) >>
  `ci_mono sc sb` by
    (mp_tac (Q.SPECL [`cenv`,`src`,`dst`,`dty`,`lowered_value_type cenv e`,`sc`]
      ci_mono_compile_store_memory) >> simp[]) >>
  `sa.cs_next_var <= sc.cs_next_var /\ csbase.cs_next_var <= sc.cs_next_var /\
   sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id` by
    (fs[ci_mono_def] >> decide_tac) >>
  `!x. not_fresh_at csbase x ==>
    lookup_var x u = lookup_var x z /\
    FLOOKUP Gf x = FLOOKUP G' x /\ op_taint tnf (Var x) = op_taint tn' (Var x)` by
    (rpt strip_tac >>
     `not_fresh_at sc x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >> metis_tac[]) >>
  `not_fresh_at sc q /\ not_fresh_at sb q` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `lookup_var q z = SOME (n2w base) /\ lookup_var q u = SOME (n2w base)` by
    metis_tac[expr_post_def] >>
  `ptr_covers Gf tnf q u cap` by
    (qpat_assum `ptr_covers G tn q s cap` mp_tac >>
     qpat_assum `ghost_kept_at lo cenv es sa G tn s G' tn'` mp_tac >>
     qpat_assum `!p. not_fresh_at sc p ==> FLOOKUP Gf p = FLOOKUP G' p /\ _` mp_tac >>
     qpat_assum `not_fresh_at sa q` mp_tac >>
     qpat_assum `not_fresh_at sc q` mp_tac >>
     qpat_assum `lookup_var q s = SOME (n2w base)` mp_tac >>
     qpat_assum `lookup_var q u = SOME (n2w base)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[ptr_covers_def,ghost_kept_at_def] >> metis_tac[]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) es.storage_trace` by
    metis_tac[valid_horizon_append] >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx es s` by
    metis_tac[] >>
  `local_ptrs_rel func cenv es.scopes s` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ es s`
       (ACCEPT_TAC o CONJUNCT1 o MATCH_MP stmt_state_rel_local_ptrs_alloca)) >>
  `!name b n. local_region cenv ee.scopes z name b n ==>
    loweringStateRelDefs$regions_disjoint base cap b n` by
    (rpt strip_tac >>
     `local_region cenv es.scopes s name b n` by
       (mp_tac (Q.SPECL [`func`,`cenv`,`es.scopes`,`s`,`sa`,
         `ee.scopes`,`z`,`name`,`b`,`n`] exprSimPropsTheory.local_region_frame) >>
        (impl_tac >- (simp[] >> metis_tac[expr_post_def])) >> simp[]) >> metis_tac[]) >>
  `local_ptrs_rel func cenv ee.scopes z` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ ee z`
       (ACCEPT_TAC o CONJUNCT1 o MATCH_MP stmt_state_rel_local_ptrs_alloca)) >>
  `!name b n. local_region cenv ee.scopes u name b n ==>
    loweringStateRelDefs$regions_disjoint base cap b n` by
    (rpt strip_tac >>
     `local_region cenv ee.scopes z name b n` by
       (mp_tac (Q.SPECL [`func`,`cenv`,`ee.scopes`,`z`,`sc`,
         `ee.scopes`,`u`,`name`,`b`,`n`] exprSimPropsTheory.local_region_frame) >>
        (impl_tac >- (simp[] >> metis_tac[])) >> simp[]) >> metis_tac[]) >>
  `!id b n. FLOOKUP z.vs_allocas id = SOME (b,n) /\ id < csbase.cs_next_id ==>
    b+n <= base+off \/ base+off+type_memory_size dtv <= b` by
    (rpt strip_tac >>
     `id <> aid` by decide_tac >>
     `b+n <= base \/ base+cap <= b` by
       (qpat_assum `alloca_inv z` mp_tac >>
        qpat_assum `FLOOKUP z.vs_allocas id = SOME (b,n)` mp_tac >>
        qpat_assum `FLOOKUP z.vs_allocas aid = SOME (base,cap)` mp_tac >>
        qpat_assum `id <> aid` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >>
        REWRITE_TAC[venomMemDefsTheory.alloca_inv_def,
          venomMemDefsTheory.allocas_non_overlapping_def] >> metis_tac[]) >>
     FIRST [qpat_assum `b+n <= base` mp_tac,
       qpat_assum `base+cap <= b` mp_tac] >>
     qpat_assum `off+type_memory_size dtv <= cap` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  `!name b n. local_region cenv ee.scopes z name b n ==>
    b+n <= base+off \/ base+off+type_memory_size dtv <= b` by
    (rpt strip_tac >>
     qpat_assum `!name b n. local_region cenv ee.scopes z name b n ==> _`
       (qspecl_then [`name`,`b`,`n`] mp_tac) >>
     (impl_tac >- simp[]) >>
     qpat_assum `off+type_memory_size dtv <= cap` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     REWRITE_TAC[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `wb_frame cenv ee ee csbase z u` by
    (mp_tac (Q.INST [`s` |-> `z`, `z` |-> `u`, `sa` |-> `csbase`,
       `es` |-> `ee`, `start` |-> `base+off`, `nb` |-> `type_memory_size dtv`]
       bodyFullUnwrapSlotPostTheory.unwrap_slot_copy_wb_frame) >>
     (impl_tac >-
       (qpat_assum `!x. not_fresh_at csbase x ==> lookup_var x u = lookup_var x z /\ _` mp_tac >>
        qpat_assum `!id b n. FLOOKUP z.vs_allocas id = SOME (b,n) /\ _ ==> _` mp_tac >>
        qpat_assum `!name b n. local_region cenv ee.scopes z name b n ==>
          b+n <= base+off \/ _` mp_tac >>
        qpat_assum `!a k. _ ==> mem_bytes_at a k u.vs_memory =
          mem_bytes_at a k z.vs_memory` mp_tac >>
        qpat_assum `u.vs_allocas = z.vs_allocas` mp_tac >>
        qpat_assum `off+type_memory_size dtv <= cap` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >>
        REWRITE_TAC[loweringStateRelDefsTheory.regions_disjoint_def,arithmeticTheory.ADD_ASSOC] >>
        metis_tac[])) >> simp[]) >>
  `wb_frame cenv ebase ee csbase sbase u` by
    (mp_tac (Q.INST [`H` |-> `storage_trace_horizon ee.storage_trace`]
       (Q.SPECL [`func`,`cenv`,`cx`,`ebase`,`sbase`,`csbase`,`ee`,`ee`,
         `csbase`,`z`,`u`,`ctx`]
         (INST_TYPE [alpha |-> ``:256``] exprSimWordArgsTheory.wb_frame_trans))) >>
     (impl_tac >- simp[]) >> simp[]) >>
  `ghost_kept_at lo cenv ee csbase G' tn' z Gf tnf` by
    (mp_tac (Q.INST [`Gi` |-> `G'`, `ti` |-> `tn'`, `s0` |-> `z`,
       `G` |-> `G'`, `tn` |-> `tn'`, `H` |-> `Gf`, `tf` |-> `tnf`,
       `es` |-> `ee`, `sa` |-> `csbase`]
       (INST_TYPE [alpha |-> ``:num # num``]
         bodyFullUnwrapSlotPostTheory.unwrap_slot_copy_ghost_kept_at)) >>
     (impl_tac >-
       (rpt conj_tac
        >- simp[ghost_kept_at_def]
        >- (qpat_assum `!x. not_fresh_at csbase x ==> lookup_var x u = lookup_var x z /\ _` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >> metis_tac[])
        >- (qx_genl_tac [`id`,`b`,`n`,`i`] >> strip_tac >>
            `b+n <= base+off \/ base+off+type_memory_size dtv <= b` by
              (qpat_assum `!id b n. FLOOKUP z.vs_allocas id = SOME (b,n) /\ _ ==> _`
                 (qspecl_then [`id`,`b`,`n`] mp_tac) >> simp[]) >>
            qpat_assum `!i. _ ==> (i IN tnf.t_mem <=> i IN tn'.t_mem)`
              (qspec_then `i` mp_tac) >>
            (impl_tac >- decide_tac) >> simp[])
        >- (qx_genl_tac [`name`,`b`,`n`,`i`] >> strip_tac >>
            `loweringStateRelDefs$regions_disjoint base cap b n` by
              (qpat_assum `!name b n. local_region cenv ee.scopes z name b n ==>
                 loweringStateRelDefs$regions_disjoint base cap b n`
                 (qspecl_then [`name`,`b`,`n`] mp_tac) >> simp[]) >>
            qpat_assum `!i. _ ==> (i IN tnf.t_mem <=> i IN tn'.t_mem)`
              (qspec_then `i` mp_tac) >>
            (impl_tac >-
              (qpat_assum `loweringStateRelDefs$regions_disjoint base cap b n` mp_tac >>
               qpat_assum `off+type_memory_size dtv <= cap` mp_tac >>
               qpat_assum `b <= i` mp_tac >> qpat_assum `i < b+n` mp_tac >>
               POP_ASSUM_LIST (K all_tac) >>
               REWRITE_TAC[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac)) >> simp[])
        >- (qx_gen_tac `i` >> strip_tac >>
            qpat_assum `!i. _ ==> (i IN tnf.t_mem <=> i IN tn'.t_mem)`
              (qspec_then `i` mp_tac) >>
            (impl_tac >- decide_tac) >> simp[]))) >> simp[]) >>
  `ghost_kept_at lo cenv ebase csbase Gbase tnbase sbase Gf tnf` by
    (mp_tac (Q.SPECL [`lo`,`cenv`,`ebase`,`csbase`,`Gbase`,`tnbase`,`sbase`,
       `G'`,`tn'`,`ee`,`csbase`,`Gf`,`tnf`,`z`,
       `storage_trace_horizon ee.storage_trace`,`ctx`,`func`,`cx`,`ee`]
       (INST_TYPE [alpha |-> ``:num # num``, ``:'b`` |-> ``:256``]
         wordArgsPtrTheory.ghost_kept_at_wb_trans)) >>
     (impl_tac >- simp[]) >> simp[]) >>
  suspend "finish_post"
QED

Resume make_array_slot_full_bundled[finish_post]:
  markerLib.RESUME_TAC >>
  `!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
    lookup_var x z = SOME w` by
    (qpat_assum `expr_post (storage_trace_horizon ee.storage_trace)
       ctx func cenv cx e es sa sc s ee v src z` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> REWRITE_TAC[expr_post_def] >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  `!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
    lookup_var x u = SOME w` by
    (rpt strip_tac >>
     `not_fresh_at sc x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
     qpat_assum `!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==> _` mp_tac >>
     qpat_assum `!p. not_fresh_at sc p ==> lookup_var p u = lookup_var p z` mp_tac >>
     qpat_assum `not_fresh_at sc x` mp_tac >>
     qpat_assum `not_fresh_at sa x` mp_tac >>
     qpat_assum `lookup_var x s = SOME w` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `return_buf_frame d cenv sb u` by
    (mp_tac (Q.SPECL [`d`,`cenv`,`cenv`,`sa`,`sb`,`s`,`u`]
      bodyMemoryDefsTheory.return_buf_frame_frame) >>
     (impl_tac >- simp[]) >> simp[]) >>
  `expr_sim_inv cenv cx env ee` by
    (qpat_assum `expr_body_pre cenv cx env e (es with gas_obs := _)` mp_tac >>
     qpat_assum `bind (eval_expr cx e) (read_result cx) _ = (INL v,ee)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[exprSimSourceTheory.expr_body_pre_eval]) >>
  `env_consistent env cx ee` by
    (qpat_assum `expr_sim_inv cenv cx env ee` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[exprSimHypsDefsTheory.expr_sim_inv_def]) >>
  `cenv.ce_module = NONE /\ cenv.ce_module_vars =
    add_immutable_locations (get_struct_fields (make_struct_fields_map tops))
      tops 0 (add_module_var_locations tops FEMPTY)` by
    (drule body_inv_module_locations >> simp[]) >>
  `cenv.ce_is_ctor ==> !nm io ity itv.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,nm) = SOME (ImmutableLoc io) /\
    cenv.ce_module_var_type (cenv.ce_module,nm) = SOME ity /\
    evaluate_type (get_tenv cx) ity = SOME itv ==>
    loweringStateRelDefs$regions_disjoint io (type_memory_size itv) base cap` by
    (qpat_assum `stmt_state_rel (storage_trace_horizon ee.storage_trace)
       ctx func cenv cx ee z` mp_tac >>
     qpat_assum `FLOOKUP z.vs_allocas aid = SOME (base,cap)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[immutable_assign_declared_region]) >>
  `cenv.ce_is_ctor ==> !name itv iv io.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (itv,iv) ==>
    loweringStateRelDefs$regions_disjoint io (type_memory_size itv)
      (base+off) (type_memory_size dtv)` by
    (strip_tac >>
     mp_tac (Q.INST [`es` |-> `ebase`, `b` |-> `base+off`,
       `cap` |-> `type_memory_size dtv`] internal_return_immutable_separation) >>
     (impl_tac >-
       (simp[] >> rpt strip_tac >>
        `loweringStateRelDefs$regions_disjoint io (type_memory_size itv) base cap` by
          metis_tac[] >>
        qpat_assum `loweringStateRelDefs$regions_disjoint io (type_memory_size itv) base cap` mp_tac >>
        qpat_assum `off+type_memory_size dtv <= cap` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >>
        REWRITE_TAC[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac)) >> simp[]) >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx ee u` by
    (mp_tac (Q.INST [`H` |-> `storage_trace_horizon ee.storage_trace`,
       `s` |-> `z`, `q` |-> `u`, `ce` |-> `cenv`, `es` |-> `ee`,
       `sa` |-> `sc`, `dst` |-> `base+off`, `n` |-> `type_memory_size dtv`]
       (INST_TYPE [alpha |-> ``:256``] aggregate_store_control_frame)) >>
     (impl_tac >-
       (qpat_assum `stmt_state_rel (storage_trace_horizon ee.storage_trace)
          ctx func cenv cx ee z` mp_tac >>
        qpat_assum `local_ptrs_reserved cenv sc` mp_tac >>
        qpat_assum `(u with <|vs_vars := z.vs_vars; vs_memory := z.vs_memory;
          vs_prev_bb := z.vs_prev_bb; vs_current_bb := z.vs_current_bb;
          vs_inst_idx := z.vs_inst_idx|>) = z` mp_tac >>
        qpat_assum `!x. not_fresh_at sc x ==> lookup_var x u = lookup_var x z` mp_tac >>
        qpat_assum `!a k. _ ==> mem_bytes_at a k u.vs_memory =
          mem_bytes_at a k z.vs_memory` mp_tac >>
        qpat_assum `!name b n. local_region cenv ee.scopes z name b n ==>
          b+n <= base+off \/ _` mp_tac >>
        qpat_assum `LENGTH z.vs_memory <= LENGTH u.vs_memory` mp_tac >>
        qpat_assum `cenv.ce_is_ctor ==> !name itv iv io. _ ==>
          loweringStateRelDefs$regions_disjoint io (type_memory_size itv)
            (base+off) (type_memory_size dtv)` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> REWRITE_TAC[arithmeticTheory.ADD_ASSOC] >>
        metis_tac[])) >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee u` by
    (qx_gen_tac `hh` >> strip_tac >>
     `stmt_state_rel hh ctx func cenv cx ee z` by metis_tac[expr_post_def] >>
     qpat_assum `stmt_state_rel (storage_trace_horizon ee.storage_trace)
       ctx func cenv cx ee u` mp_tac >>
     qpat_assum `stmt_state_rel hh ctx func cenv cx ee z` mp_tac >>
     qpat_assum `u.vs_accounts = z.vs_accounts` mp_tac >>
     qpat_assum `u.vs_transient = z.vs_transient` mp_tac >>
     qpat_assum `u.vs_requests = z.vs_requests` mp_tac >>
     qpat_assum `u.vs_call_ctx = z.vs_call_ctx` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[exprLoweringPropsTheory.stmt_state_rel_fields_transport]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stor_taint_ok_at (DF H) tnf u` by
    (qx_gen_tac `hh` >> strip_tac >>
     `ghost_inv_at (DF hh) lo d cenv cx ee G' tn' z` by metis_tac[] >>
     qpat_assum `ghost_inv_at (DF hh) lo d cenv cx ee G' tn' z` mp_tac >>
     qpat_assum `u.vs_accounts = z.vs_accounts` mp_tac >>
     qpat_assum `u.vs_transient = z.vs_transient` mp_tac >>
     qpat_assum `u.vs_call_ctx = z.vs_call_ctx` mp_tac >>
     qpat_assum `u.vs_immutables = z.vs_immutables` mp_tac >>
     qpat_assum `tnf.t_stor = tn'.t_stor` mp_tac >>
     qpat_assum `tnf.t_trans = tn'.t_trans` mp_tac >>
     qpat_assum `tnf.t_imm = tn'.t_imm` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[ghost_inv_at_def,stor_taint_ok_at_def]) >>
  `allocas_from lo u /\ lo <= u.vs_alloca_next` by
    (qpat_assum `allocas_from lo z` mp_tac >>
     qpat_assum `lo <= z.vs_alloca_next` mp_tac >>
     qpat_assum `u.vs_allocas = z.vs_allocas` mp_tac >>
     qpat_assum `u.vs_alloca_next = z.vs_alloca_next` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[ptrDisciplineTheory.allocas_from_def]) >>
  suspend "finish_ghost"
QED

Resume make_array_slot_full_bundled[finish_ghost]:
  markerLib.RESUME_TAC >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x)` by
    (conj_tac >> rpt strip_tac >>
     `not_fresh_at csbase x` by metis_tac[] >>
     irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `csbase` >> simp[]) >>
  `!x. not_fresh_at sc x ==> lookup_var x u = lookup_var x z /\
    FLOOKUP Gf x = FLOOKUP G' x /\ op_taint tnf (Var x) = op_taint tn' (Var x)` by
    (qpat_assum `!x. not_fresh_at sc x ==> lookup_var x u = lookup_var x z` mp_tac >>
     qpat_assum `!p. not_fresh_at sc p ==> FLOOKUP Gf p = FLOOKUP G' p /\ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `!j. j < base+off \/ base+off+type_memory_size dtv <= j ==>
    (j IN tnf.t_mem <=> j IN tn'.t_mem)` by
    (rpt strip_tac >>
     qpat_assum `!i. ~(base+off <= i /\ i < base+off+type_memory_size dtv) ==> _` irule >>
     decide_tac) >>
  `lo <= base+off` by decide_tac >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    ghost_inv_at (DF H) lo d cenv cx ee Gf tnf u` by
    (qx_gen_tac `hh` >> strip_tac >>
     `ghost_inv_at (DF hh) lo d cenv cx ee G' tn' z` by metis_tac[] >>
     `stor_taint_ok_at (DF hh) tnf u` by metis_tac[] >>
     mp_tac (Q.INST [`D` |-> `DF (hh : (bool # bytes32 # type_value) list # num list)`,
       `G` |-> `G'`, `tn` |-> `tn'`,
       `s` |-> `z`, `H` |-> `Gf`, `tf` |-> `tnf`, `z` |-> `u`,
       `es` |-> `ee`, `sa` |-> `sc`, `start` |-> `base+off`,
       `nb` |-> `type_memory_size dtv`]
       (INST_TYPE [alpha |-> ``:num # num``]
         bodyFullUnwrapSlotPostTheory.unwrap_slot_copy_ghost_inv_at)) >>
     (impl_tac >-
       (qpat_assum `ghost_inv_at (DF hh) lo d cenv cx ee G' tn' z` mp_tac >>
        qpat_assum `local_ptrs_reserved cenv sc` mp_tac >>
        qpat_assum `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sc x` mp_tac >>
        qpat_assum `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sc x` mp_tac >>
        qpat_assum `local_ptrs_rel func cenv ee.scopes z` mp_tac >>
        qpat_assum `!name b n. local_region cenv ee.scopes z name b n ==>
          b+n <= base+off \/ _` mp_tac >>
        qpat_assum `!x. not_fresh_at sc x ==> lookup_var x u = lookup_var x z /\ _` mp_tac >>
        qpat_assum `!a k. _ ==> mem_bytes_at a k u.vs_memory =
          mem_bytes_at a k z.vs_memory` mp_tac >>
        qpat_assum `!j. j < base+off \/ base+off+type_memory_size dtv <= j ==> _` mp_tac >>
        qpat_assum `lo <= base+off` mp_tac >>
        qpat_assum `stor_taint_ok_at (DF hh) tnf u` mp_tac >>
        qpat_assum `allocas_from lo u` mp_tac >>
        qpat_assum `lo <= u.vs_alloca_next` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> REWRITE_TAC[arithmeticTheory.ADD_ASSOC] >>
        metis_tac[])) >> simp[]) >>
  `!a b. FLOOKUP sbase.vs_allocas a = SOME b ==> FLOOKUP z.vs_allocas a = SOME b` by
    (qpat_assum `wb_frame cenv ebase ee csbase sbase z` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> REWRITE_TAC[wb_frame_def] >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  `!hh. valid_horizon cx st0 hh ee.storage_trace ==>
    stmt_state_rel hh ctx func cenv cx ee u /\ storage_well_formed_on cx ee (FST hh) /\
    ghost_inv_at (DF hh) lo d cenv cx ee Gf tnf u` by
    (qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path _ (at,Ga,tna) [] (OK z,G',tn') /\ _` mp_tac >>
     qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ee u` mp_tac >>
     qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==>
       ghost_inv_at (DF H) lo d cenv cx ee Gf tnf u` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> REWRITE_TAC[expr_post_def] >> metis_tac[]) >>
  simp[] >> rpt conj_tac >> suspend "finish_close"
QED

Resume make_array_slot_full_bundled[finish_close]:
  markerLib.RESUME_TAC >- first_assum ACCEPT_TAC >>
  strip_tac >>
  qpat_assum `~expr_has_effect e ==> _ /\ _` mp_tac >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qx_genl_tac [`p`,`n`] >> disch_then (CONJUNCTS_THEN assume_tac) >>
  qpat_assum `!p n. (p+n <= base \/ base+cap <= p) /\ _ ==> _`
    (qspecl_then [`p`,`n`] mp_tac) >>
  (impl_tac >-
    (conj_tac
     >- (qpat_assum `n+p <= base \/ base+cap <= p` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
     qpat_assum `u.vs_allocas = z.vs_allocas` mp_tac >>
     qpat_assum `!inst b sz. _ ==> loweringStateRelDefs$regions_disjoint p n b sz` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[])) >> simp[]
QED

Finalise make_array_slot_full_bundled

Theorem make_array_slot_full:
    (
        body_inv tops ctx cenv cx /\
        shadow_body_inv tops ctx shadow_ctx /\ expr_sim_inv cenv cx env ebase /\
        csbase.cs_next_id <= aid /\ csbase.cs_next_id <= sa.cs_next_id /\
        csbase.cs_next_var <= sa.cs_next_var /\
        local_ptrs_reserved cenv csbase /\ local_ptrs_reserved cenv sa /\
        ctx_inst_ids_distinct ctx /\ fn_inst_ids_distinct func /\
        gas_shadow_context ctx shadow_ctx /\
        gas_shadow_function func shadow_func /\
        MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
        (!fn inst z. frag_reachable ctx func s fn inst z ==> dalloca_fmp_headroom inst z) /\
        (!H. dead_lo_ok H (DF H) lo cenv cx) /\
        (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==>
               not_fresh_at csbase x) /\
        (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==>
               not_fresh_at csbase x) /\
        (!H. valid_horizon cx st0 H ebase.storage_trace ==>
             stmt_state_rel H ctx func cenv cx ebase sbase)) /\ body_expr_full_ok cx e /\ expr_body_pre cenv cx env e es /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    arg_type_fits (expr_type e) dty /\
    evaluate_type (get_tenv cx) dty = SOME dtv /\
    type_memory_bytes cenv dty = type_memory_size dtv /\
    off + type_memory_size dtv <= cap /\
    (\cs ee s G tn.
        (?events. ee.storage_trace = ebase.storage_trace ++ events) /\
        FLOOKUP s.vs_allocas aid = SOME (base,cap) /\
        lookup_var q s = SOME (n2w base) /\
        ptr_covers G tn q s cap /\ not_fresh_at cs q /\
        aid < cs.cs_next_id /\ base+cap < dimword (:256) /\
        base+cap <= s.vs_alloca_next /\
        (!name b n. local_region cenv ee.scopes s name b n ==>
                    loweringStateRelDefs$regions_disjoint base cap b n) /\
        alloca_history func s /\ sbase.vs_alloca_next <= s.vs_alloca_next /\
        (!a b. FLOOKUP sbase.vs_allocas a = SOME b ==>
               FLOOKUP s.vs_allocas a = SOME b) /\
        MAP FDOM ebase.scopes = MAP FDOM ee.scopes /\
        wb_frame cenv ebase ee csbase sbase s /\
        ghost_kept_at lo cenv ebase csbase Gbase tnbase sbase G tn /\
        return_buf_frame d cenv cs s /\ ~s.vs_halted /\
        s.vs_current_bb = cs.cs_current_bb /\
        s.vs_inst_idx = LENGTH cs.cs_current_insts /\
        (!H. valid_horizon cx st0 H ee.storage_trace ==>
             stmt_state_rel H ctx func cenv cx ee s /\
             storage_well_formed_on cx ee (FST H) /\
             ghost_inv_at (DF H) lo d cenv cx ee G tn s)) sa es s G tn /\ (\ps (off:num) s tn.
        EVERY (\(rt,v,p,n).
          val_wf rt v /\ val_footprint rt v <= n /\
          base <= p /\ p+n <= (base:num)+(off:num) /\
          (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
               val_in_memory rt v p m)) ps) ps off s tn /\
    gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
    (do vv <- compile_expr cenv (expr_type e) e;
        dst <- emit_op ADD [Var q; Lit (n2w off)];
        src <- unwrap_value cenv vv;
        compile_store_memory cenv src dst dty (lowered_value_type cenv e)
     od) sa = ((),sb) /\
    (do vv <- compile_expr (gas_shadow_env T cenv) (expr_type (gas_shadow_expr e)) (gas_shadow_expr e);
        dst <- emit_op ADD [Var q; Lit (n2w off)];
        src <- unwrap_value cenv vv;
        compile_store_memory cenv src dst dty
          (lowered_value_type cenv (gas_shadow_expr e))
     od) shadow_sa = ((),shadow_sb) /\
    gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
    fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func ==>
    gas_outcome_full
      (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx))
      (es,s,G,tn)
      (\H res ee Gf tnf t.
        ?v. res = INL v /\ value_has_type dtv v /\ val_wf dtv v /\
            (\cs ee s G tn.
        (?events. ee.storage_trace = ebase.storage_trace ++ events) /\
        FLOOKUP s.vs_allocas aid = SOME (base,cap) /\
        lookup_var q s = SOME (n2w base) /\
        ptr_covers G tn q s cap /\ not_fresh_at cs q /\
        aid < cs.cs_next_id /\ base+cap < dimword (:256) /\
        base+cap <= s.vs_alloca_next /\
        (!name b n. local_region cenv ee.scopes s name b n ==>
                    loweringStateRelDefs$regions_disjoint base cap b n) /\
        alloca_history func s /\ sbase.vs_alloca_next <= s.vs_alloca_next /\
        (!a b. FLOOKUP sbase.vs_allocas a = SOME b ==>
               FLOOKUP s.vs_allocas a = SOME b) /\
        MAP FDOM ebase.scopes = MAP FDOM ee.scopes /\
        wb_frame cenv ebase ee csbase sbase s /\
        ghost_kept_at lo cenv ebase csbase Gbase tnbase sbase G tn /\
        return_buf_frame d cenv cs s /\ ~s.vs_halted /\
        s.vs_current_bb = cs.cs_current_bb /\
        s.vs_inst_idx = LENGTH cs.cs_current_insts /\
        (!H. valid_horizon cx st0 H ee.storage_trace ==>
             stmt_state_rel H ctx func cenv cx ee s /\
             storage_well_formed_on cx ee (FST H) /\
             ghost_inv_at (DF H) lo d cenv cx ee G tn s)) sb ee t Gf tnf /\ (\ps (off:num) s tn.
        EVERY (\(rt,v,p,n).
          val_wf rt v /\ val_footprint rt v <= n /\
          base <= p /\ p+n <= (base:num)+(off:num) /\
          (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
               val_in_memory rt v p m)) ps) ps off t tnf /\
            (!m. mem_agree_outside tnf.t_mem t.vs_memory m ==>
                 val_in_memory dtv v ((base:num)+(off:num)) m) /\
            (!(p:num) (n:num). (base:num)+(off:num)+type_memory_size dtv <= p /\ p+n <= base+cap ==>
                   mem_bytes_at p n t.vs_memory = mem_bytes_at p n s.vs_memory) /\
            (~expr_has_effect e ==>
              (!name b n. local_region cenv es.scopes s name b n ==>
                mem_bytes_at b n t.vs_memory = mem_bytes_at b n s.vs_memory) /\
              !p n. (p+n <= base \/ base+cap <= p) /\
                (!inst b sz. MEM inst (fn_insts func) /\
                  inst.inst_opcode = ALLOCA /\ sa.cs_next_id <= inst.inst_id /\
                  FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) ==>
                  loweringStateRelDefs$regions_disjoint p n b sz) ==>
                mem_bytes_at p n t.vs_memory = mem_bytes_at p n s.vs_memory))
      (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
        (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  SIMP_TAC bool_ss [AC CONJ_ASSOC CONJ_COMM] >>
  ACCEPT_TAC (SIMP_RULE bool_ss [AC CONJ_ASSOC CONJ_COMM]
    (REWRITE_RULE [expr_sim_full_code_def, expr_sim_full_endpoint_def]
      make_array_slot_full_bundled))
QED

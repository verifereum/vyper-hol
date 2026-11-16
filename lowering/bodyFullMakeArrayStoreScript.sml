(* The actual child, ADD, unwrap and store continuation of MakeArray. *)
Theory bodyFullMakeArrayStore
Ancestors
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
  exprSimBufferStore reasonCopySourcePtr
  bodyMemAggregatePath fragGasPathFrameMem logValueFramePtr internalReturnImmutableTypes

val _ = Parse.hide "base";

Theorem make_array_slot_full:
    (
        body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env ebase /\
        csbase.cs_next_id <= aid /\ csbase.cs_next_id <= sa.cs_next_id /\
        csbase.cs_next_var <= sa.cs_next_var /\
        local_ptrs_reserved cenv csbase /\ local_ptrs_reserved cenv sa /\
        ctx_inst_ids_distinct ctx /\ fn_inst_ids_distinct func /\
        gas_shadow_context ctx shadow_ctx /\
        gas_shadow_function func shadow_func /\
        MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
        ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
        (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==>
               not_fresh_at csbase x) /\
        (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==>
               not_fresh_at csbase x) /\
        (!H. valid_horizon cx st0 H ebase.storage_trace ==>
             stmt_state_rel H ctx func cenv cx ebase sbase)) /\ body_expr_full_ok cx e /\ expr_body_pre cenv cx env e es /\
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
    (do vv <- compile_expr cenv (expr_type (gas_shadow_expr e)) (gas_shadow_expr e);
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
      (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r)
Proof
  BETA_TAC >> strip_tac >>
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
       (mp_tac o CONJUNCT1 o ONCE_REWRITE_RULE [body_expr_full_ok_def]) >>
     disch_then drule_all >> simp[]) >>
  `gas_shadow_compiles (compile_expr cenv (expr_type e) e)
     (compile_expr cenv (expr_type e) (gas_shadow_expr e))` by
     irule gas_shadow_stmt_compile_expr >>
  qpat_x_assum `gas_shadow_compiles _ _`
    (mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
  disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `compile_expr cenv (expr_type e) (gas_shadow_expr e) shadow_sa` >>
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
  simp[] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ childQ childR` >>
  irule gas_outcome_full_bind_all >> rpt conj_tac
  >~ [`storage_trace_frame (eval_expr _ _)`]
  >- simp[evaluate_storage_trace_frame]
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

Resume make_array_slot_full[slot]:
  cheat
QED
Finalise make_array_slot_full

(*
 * The extcall full case's call step over the finite-horizon joint judgment.
 *
 * TOP-LEVEL:
 *   extcall_call_full
 *)
Theory bodyFullExtCallStep
Ancestors
  bodyFullPreds bodySimFull gasOutcomeFull exprSimExtCallCase bodyPtrDefs
  oracleCallOriginPtr gasOutcomeFullCompose
  bodyFullExtCallPrefix bodyFullExtCallCallGhost bodyFullExtCallCallPath
  bodyFullExtCallExit bodyFullExtCallSuccess bodyFullExtCallBoundary
  ptrDiscipline gasShadow exprSimHypsDefs exprLowering
  vyperInterpreter vyperAST list vyperStorageTrace vyperStorageFootprint
  vyperState

val _ = Parse.hide "body";

Theorem extcall_take_tail[local]:
  !target cd vo st tail.
    take_call_outcome target cd vo (st with gas_obs := tail) =
      (FST (take_call_outcome target cd vo st),
       SND (take_call_outcome target cd vo st) with gas_obs := tail)
Proof
  rpt gen_tac >>
  simp[vyperCallOutcomeTheory.take_call_outcome_def,
       vyperCallOutcomeTheory.take_request_outcome_def,
       vyperCallOutcomeTheory.call_outcome_request_def] >>
  Cases_on `st.outcomes` >> simp[] >> pairarg_tac >> simp[] >>
  IF_CASES_TAC >> simp[]
QED

Theorem extcall_success_tail[local]:
  ee.outcomes = SOME os /\ ~cx.txn.is_static /\
  ext_call_precheck_ok skip ret_type target ee.accounts /\
  take_call_outcome target calldata value_opt ee = (INL (rq,oc),consumed) /\
  oc.co_success /\ ee' = SND (adopt_call_outcome rq oc consumed) ==>
  !tail.
    (do accounts <- get_accounts;
        check (ext_call_precheck_ok skip ret_type target accounts)
          "ExtCall target has no code";
        value_opt' <- frame_call_value cx value_opt;
        rd <- eval_ext_call_effects cx target calldata value_opt' gas accounts;
        k rd od) (ee with gas_obs := tail) =
    k oc.co_returnData (ee' with gas_obs := tail)
Proof
  strip_tac >> gen_tac >>
  `take_call_outcome target calldata value_opt (ee with gas_obs := tail) =
    (INL (rq,oc),consumed with gas_obs := tail)` by simp[extcall_take_tail] >>
  simp[get_accounts_def, bind_def, ignore_bind_def, return_def,
       check_def, assert_def, frame_call_value_def, eval_ext_call_effects_def] >>
  gvs[vyperCallOutcomeTheory.adopt_call_outcome_equation] >>
  Cases_on `rq.cr_static` >> simp[]
QED

(* (2) The call step, at (DF H, lo).  From a ready request at sp (source,
   memory and pointer facts at t): the extcodesize check against the
   source's precheck, the CALL or STATICCALL as an oracle step, a failed
   call's returndata copy and REVERT; a successful call reaches sr with
   the returndata in the buffer and the pointer facts kept. *)
Theorem extcall_call_full_default_frame:
  !DF lo d explicit ctx PG func cenv cx es st0 sa s0 G0 tn0 sp sr u
   is_static skip ret_type addr_op value_op gas_op buf_op call_offset
   call_len cap target value_opt calldata gas has_default default_op
   default_ty default_opt ee t G tn k Q.
    comp_ignore_bind
      (if ret_type = NoneT /\ ~skip then compile_extcodesize_check addr_op
       else comp_return ())
      (comp_bind
         (if is_static then
            emit_op STATICCALL
              [gas_op; addr_op; call_offset; call_len; buf_op; Lit (n2w cap)]
          else
            emit_op CALL
              [gas_op; addr_op; value_op; call_offset; call_len; buf_op;
               Lit (n2w cap)])
      (\success. comp_bind (fresh_label "extcall_fail") (\fail_lbl.
       comp_bind (fresh_label "extcall_cont") (\cont_lbl.
       comp_ignore_bind
         (emit_inst JNZ [success; Label cont_lbl; Label fail_lbl] [])
       (comp_ignore_bind (new_block fail_lbl)
       (comp_bind (emit_op RETURNDATASIZE []) (\rds.
       comp_bind (compile_alloc_buffer 0) (\fail_buf.
       comp_ignore_bind
         (emit_void RETURNDATACOPY [fail_buf.buf_operand; Lit 0w; rds])
       (comp_ignore_bind (emit_inst REVERT [fail_buf.buf_operand; rds] [])
          (new_block cont_lbl)))))))))) sp = (u, sr) /\
    fn_has_code sp sr func /\ fn_inst_ids_distinct func /\
    MEM func ctx.ctx_functions /\ ~ctx_has_dalloca ctx /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
            not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
            not_fresh_at sa x) /\
    extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sp is_static
      addr_op value_op gas_op buf_op call_offset call_len cap
      target value_opt calldata has_default default_op default_ty default_opt
      ee t /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       ghost_inv_at (DF H) lo d cenv cx ee G tn t) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
    EVERY (\op. op_taint tn op = {})
      [addr_op; value_op; gas_op; buf_op; call_offset; call_len; default_op] /\
    (?ao az. eval_operand call_offset t = SOME ao /\
       eval_operand call_len t = SOME az /\
       (w2n az <> 0 ==> w2n ao + w2n az <= t.vs_alloca_next) /\
       (!i. w2n ao <= i /\ i < w2n ao + w2n az ==> i NOTIN tn.t_mem) /\
       (w2n az <> 0 ==>
        ?v b sz. call_offset = Var v /\ FLOOKUP G v = SOME (b,sz) /\
                 b <= w2n ao /\ w2n ao + w2n az <= b + sz)) /\
    (!dv. default_opt = SOME dv /\ ~is_word_type default_ty ==>
       ptr_mem_ok cx default_ty dv default_op G tn t /\
       (type_memory_bytes cenv default_ty <> 0 ==>
        ?x b sz w. default_op = Var x /\ FLOOKUP G x = SOME (b,sz) /\
          eval_operand default_op t = SOME w /\ b <= w2n w /\
          w2n w + type_memory_bytes cenv default_ty <= b + sz)) /\
    (cap <> 0 ==>
     ?v b sz ro. buf_op = Var v /\ FLOOKUP G v = SOME (b,sz) /\
       eval_operand buf_op t = SOME ro /\ b <= w2n ro /\
       w2n ro + cap <= b + sz) /\
    (!returnData. storage_trace_frame (k returnData)) /\
    (!returnData ee' t' G' tn'.
       extcall_returned st0 ctx func cenv cx ret_type es sa s0 sr addr_op
         buf_op cap target has_default default_op default_ty default_opt
         returnData ee' t' /\
       t.vs_alloca_next <= t'.vs_alloca_next /\
       eval_operand default_op t' = eval_operand default_op t /\
       alloca_history func t' /\ s0.vs_alloca_next <= t'.vs_alloca_next /\
       (!H. valid_horizon cx st0 H ee'.storage_trace ==>
          ghost_inv_at (DF H) lo d cenv cx ee' G' tn' t') /\
       ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn' /\
       EVERY (\op. op_taint tn' op = {}) [addr_op; buf_op; default_op] /\
       (!dv. default_opt = SOME dv /\ ~is_word_type default_ty ==>
          ptr_mem_ok cx default_ty dv default_op G' tn' t' /\
          (type_memory_bytes cenv default_ty <> 0 ==>
           ?x b sz w. default_op = Var x /\ FLOOKUP G' x = SOME (b,sz) /\
             eval_operand default_op t' = SOME w /\ b <= w2n w /\
             w2n w + type_memory_bytes cenv default_ty <= b + sz)) /\
       (cap <> 0 ==>
        ?v b sz ro. buf_op = Var v /\ FLOOKUP G' v = SOME (b,sz) /\
          eval_operand buf_op t' = SOME ro /\ b <= w2n ro /\
          w2n ro + cap <= b + sz /\
          (!i. w2n ro <= i /\ i < w2n ro + MIN cap (LENGTH returnData) ==>
              i NOTIN tn'.t_mem)) ==>
       ?res r G'' tn''.
         (!tail. k returnData (ee' with gas_obs := tail) =
           (res, ee' with gas_obs := tail)) /\
         (!H. valid_horizon cx st0 H ee'.storage_trace ==>
           gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
             (t', G', tn') [] (r, G'', tn'') /\
           ((?t''. r = OK t'' /\
               Q H res (ee' with gas_obs := []) G'' tn'' t'') \/
            (exit_result r /\ expr_exit res r)))) ==>
    gas_outcome_full (DF, lo, explicit, ctx, func, PG) (cx_tops cx) cx st0
      (do accounts <- get_accounts;
          check (ext_call_precheck_ok skip ret_type target accounts)
                "ExtCall target has no code";
          value_opt' <- frame_call_value cx value_opt;
          returnData <- eval_ext_call_effects cx target calldata value_opt'
                          gas accounts;
          k returnData
       od) (ee, t, G, tn) Q (\H res ee gt r. expr_exit res r)
Proof
  rpt gen_tac >> strip_tac >>
  irule gas_outcome_full_initial_domain >>
  conj_tac
  >- (irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_state_reads] >> gen_tac >>
      irule storage_trace_frame_ignore_bind >>
      simp[storage_trace_frame_checks] >>
      irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_call_value] >> gen_tac >>
      irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_ext_effects]) >>
  conj_tac >- fs[extcall_request_ready_def] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace)
     ee.storage_trace` by fs[storage_trace_domain_def] >>
  drule_all extcall_call_source_boundary >> strip_tac >>
  drule extcall_call_layout >> strip_tac >>
  drule_all extcall_suffix_code >>
  disch_then (qspec_then `func` strip_assume_tac) >>
  drule_all extcall_check_code_split >> strip_tac >>
  `fn_has_code s1 s2 func /\ fn_has_code s4 s5 func` by metis_tac[] >>
  Cases_on `ext_call_precheck_ok skip ret_type target ee.accounts`
  >- (fs[EVERY_DEF] >>
      drule_all extcall_precheck_success_boundary >>
      disch_then (qspecl_then [`tn0`, `explicit`, `PG`, `G0`] strip_assume_tac) >>
      `outcomes_accounts_typed ee.outcomes /\
       accounts_runtime_well_typed ee.accounts` by
        fs[extcall_request_ready_def] >>
      `?rq oc consumed. take_call_outcome target calldata value_opt ee =
         (INL (rq,oc),consumed)` by
        (simp[vyperCallOutcomeTheory.take_call_outcome_def,
              vyperCallOutcomeTheory.take_request_outcome_def] >>
         pairarg_tac >> simp[] >>
         `~(outcome.co_success /\
             ~accounts_runtime_well_typed outcome.co_accounts)` by
           (gvs[outcomes_accounts_typed_def, extCallOracleTheory.take_outcome_def] >>
            Cases_on `t.vs_outcomes` >> gvs[extCallOracleTheory.failed_outcome_def] >>
            Cases_on `computed_precompile (call_outcome_request target calldata value_opt ee)` >>
            gvs[AllCaseEqs(), extCallOracleTheory.failed_outcome_def,
                vyperCallOutcomeTheory.call_outcome_request_def] >> metis_tac[]) >>
         IF_CASES_TAC >> gvs[] >> metis_tac[]) >>
      qpat_assum `emit_op _ _ s1 = _`
        (strip_assume_tac o MATCH_MP compilerInstructionSuffixTheory.added_insts_emit_op) >>
      qmatch_asmsub_abbrev_tac `added_insts s1 s2 = [inst]` >>
      `inst.inst_outputs = [q]` by simp[Abbr `inst`, venomInstTheory.mk_inst_def] >>
      `s0.vs_alloca_next <= t1.vs_alloca_next` by simp[] >>
      drule_all bodyFullExtCallFramesTheory.extcall_request_oracle_endpoint_initial_domain >>
      strip_tac >>
      `EVERY (safe_operand sp) [addr_op; buf_op; default_op]` by
        fs[extcall_request_ready_def] >>
      `ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1` by metis_tac[] >>
      `EVERY (\op. op_taint tn1 op = {}) [addr_op; buf_op; default_op]` by
        (fs[EVERY_DEF] >> metis_tac[]) >>
      `!dv. default_opt = SOME dv /\ ~is_word_type default_ty ==>
        ptr_mem_ok cx default_ty dv default_op G1 tn1 t1 /\
        (type_memory_bytes cenv default_ty <> 0 ==>
         ?x b sz w. default_op = Var x /\ FLOOKUP G1 x = SOME (b,sz) /\
           eval_operand default_op t1 = SOME w /\ b <= w2n w /\
           w2n w + type_memory_bytes cenv default_ty <= b + sz)` by
        (fs[EVERY_DEF] >> metis_tac[]) >>
      `(cap <> 0 ==> ?v b sz rw. buf_op = Var v /\
         FLOOKUP G1 v = SOME (b,sz) /\ eval_operand buf_op t1 = SOME rw /\
         b <= w2n rw /\ w2n rw + cap <= b + sz)` by
        (strip_tac >> qpat_x_assum `cap <> 0 ==> _` drule >> strip_tac >>
         qpat_assum `!op. safe_operand sp op ==> _`
           (qspec_then `buf_op` mp_tac) >>
         fs[EVERY_DEF] >> strip_tac >>
         qexistsl_tac [`b`, `sz`] >> metis_tac[]) >>
      qabbrev_tac `z = update_var q (if oc.co_success then 1w else 0w) u'` >>
      `z.vs_allocas = t1.vs_allocas /\ z.vs_fmp = t1.vs_fmp /\
       z.vs_memory = (write_memory_with_expansion (w2n ro)
         (TAKE cap oc.co_returnData) t1).vs_memory /\
       z.vs_returndata = oc.co_returnData` by
        (simp[Abbr `z`, venomStateTheory.update_var_def] >>
         qpat_x_assum `u' = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
      `!x. not_fresh_at s1 x ==> lookup_var x z = lookup_var x t1` by
        (rpt strip_tac >> `x <> q` by metis_tac[] >>
         simp[Abbr `z`, emitHelperPropsTheory.lookup_var_update_var] >>
         qpat_x_assum `u' = _` (fn th => once_rewrite_tac[th]) >>
         simp[venomStateTheory.lookup_var_def]) >>
      `((inst.inst_opcode = CALL /\ inst.inst_operands =
          [gas_op; addr_op; value_op; call_offset; call_len; buf_op; Lit (n2w cap)]) \/
        (inst.inst_opcode = STATICCALL /\ inst.inst_operands =
          [gas_op; addr_op; call_offset; call_len; buf_op; Lit (n2w cap)]))` by
        (Cases_on `is_static'` >> simp[Abbr `inst`, venomInstTheory.mk_inst_def]) >>
      `ghost_kept_at lo cenv es sa G0 tn0 s0
         (step_prov PG G1 inst z) (step_taint inst t1 z tn1) /\
       EVERY (\op. op_taint (step_taint inst t1 z tn1) op = {})
         [addr_op; buf_op; default_op] /\
       (!dv. default_opt = SOME dv /\ ~is_word_type default_ty ==>
         ptr_mem_ok cx default_ty dv default_op (step_prov PG G1 inst z)
           (step_taint inst t1 z tn1) z /\
         (type_memory_bytes cenv default_ty <> 0 ==>
          ?x b sz w. default_op = Var x /\
            FLOOKUP (step_prov PG G1 inst z) x = SOME (b,sz) /\
            eval_operand default_op z = SOME w /\ b <= w2n w /\
            w2n w + type_memory_bytes cenv default_ty <= b + sz)) /\
       (cap <> 0 ==> ?v b sz rw. buf_op = Var v /\
         FLOOKUP (step_prov PG G1 inst z) v = SOME (b,sz) /\
         eval_operand buf_op z = SOME rw /\ b <= w2n rw /\ w2n rw + cap <= b + sz /\
         (!i. w2n rw <= i /\ i < w2n rw + MIN cap (LENGTH oc.co_returnData) ==>
           i NOTIN (step_taint inst t1 z tn1).t_mem))` by
        (irule (INST_TYPE [alpha |-> ``:160``] extcall_call_ghost_boundary) >> simp[] >>
         goal_assum (drule_at (Pat `extcall_request_ready _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
         simp[]) >>
      `az' <> 0w ==> w2n ao' + w2n az' <= t1.vs_alloca_next` by
        (qpat_assum `!op. safe_operand sp op ==> _`
           (qspec_then `call_offset` mp_tac) >>
         qpat_assum `!op. safe_operand sp op ==> _`
           (qspec_then `call_len` mp_tac) >>
         fs[extcall_request_ready_def, EVERY_DEF] >> metis_tac[]) >>
      `w2n ro + cap <= t1.vs_alloca_next` by
        (qpat_assum `extcall_request_ready _ _ _ _ _ _ _ _ _ s1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
           (strip_assume_tac o REWRITE_RULE[extcall_request_ready_def]) >>
         `alloca_next_valid t1` by
           (qpat_assum `!H. valid_horizon _ _ H _ ==> ghost_inv_at _ _ _ _ _ _ G1 tn1 t1` kall_tac >>
            fs[exprLoweringPropsTheory.stmt_state_rel_def,
               venomMemDefsTheory.alloca_inv_def] >> metis_tac[]) >>
         fs[venomMemDefsTheory.alloca_next_valid_def] >>
         first_x_assum drule >> gvs[] >> decide_tac) >>
      `(az' <> 0w ==> ?v b sz. call_offset = Var v /\
          FLOOKUP G1 v = SOME (b,sz) /\ b <= w2n ao' /\
          w2n ao' + w2n az' <= b + sz) /\
       (!i. w2n ao' <= i /\ i < w2n ao' + w2n az' ==> i NOTIN tn1.t_mem) /\
       EVERY (\op. op_taint tn1 op = {}) inst.inst_operands` by
        (`EVERY (safe_operand sp)
            [gas_op; addr_op; value_op; call_offset; call_len; buf_op]` by
           fs[extcall_request_ready_def, EVERY_DEF] >>
         `ao' = ao /\ az' = az` by
           (qpat_assum `!op. safe_operand sp op ==> _`
              (qspec_then `call_offset` mp_tac) >>
            qpat_assum `!op. safe_operand sp op ==> _`
              (qspec_then `call_len` mp_tac) >> fs[EVERY_DEF]) >>
         simp[] >> reverse conj_tac
         >- (fs[EVERY_DEF, ptrDisciplineTheory.op_taint_def] >> metis_tac[]) >>
         strip_tac >> qpat_x_assum `az <> 0w ==> ?v b sz. _` drule >>
         strip_tac >> qexistsl_tac [`v`, `b`, `sz`] >>
         fs[EVERY_DEF] >> metis_tac[]) >>
      `w2n (n2w cap : bytes32) = cap` by fs[extcall_request_ready_def] >>
      `!H. valid_horizon cx st0 H ee.storage_trace ==>
        access_ok lo G1 func inst t1 /\ taint_ok func tn1 inst t1 /\
        inst_mem_below_frontier inst t1 /\ allocas_from lo t1 /\
        stor_taint_ok_at (DF H) tn1 t1` by
        (gen_tac >> disch_tac >> irule bodyFullExtCallGhostTheory.extcall_call_pointer_conditions >>
         simp[] >>
         reverse conj_tac
         >- (qexistsl_tac [`cenv`, `cx`, `d`, `ee`] >> simp[]) >>
         qexists_tac `n2w cap` >> simp[venomStateTheory.eval_operand_def] >>
         conj_tac >- metis_tac[] >>
         conj_tac >- metis_tac[] >>
         strip_tac >>
         `cap <> 0` by (strip_tac >> fs[]) >>
         qpat_x_assum `cap <> 0 ==> ?v b sz rw. buf_op = Var v /\ FLOOKUP G1 v = _ /\ _`
           drule >> strip_tac >>
         qexistsl_tac [`v`, `b`, `sz`] >> gvs[]) >>
      `!H. valid_horizon cx st0 H ee.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t1,G1,tn1) []
          (OK (next_inst z), step_prov PG G1 inst z, step_taint inst t1 z tn1) /\
        s2.cs_current_bb = t1.vs_current_bb /\
        LENGTH s2.cs_current_insts = SUC t1.vs_inst_idx /\
        ~not_fresh_at s1 q /\ ~z.vs_halted` by
        (gen_tac >> disch_tac >>
         `access_ok lo G1 func inst t1 /\ taint_ok func tn1 inst t1 /\
          inst_mem_below_frontier inst t1 /\ allocas_from lo t1 /\
          stor_taint_ok_at (DF H) tn1 t1` by metis_tac[] >>
         qpat_assum `extcall_request_ready _ _ _ _ _ _ _ _ _ s1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
           (strip_assume_tac o REWRITE_RULE[extcall_request_ready_def]) >>
         `is_static' ==> vw = 0w` by (strip_tac >> gvs[wordsTheory.w2n_eq_0]) >>
         `eval_operand (Lit (n2w cap)) t1 = SOME (n2w cap)` by
           simp[venomStateTheory.eval_operand_def] >>
         `emit_op (if is_static' then STATICCALL else CALL)
           (if is_static' then [gas_op; addr_op; call_offset; call_len; buf_op; Lit (n2w cap)]
            else [gas_op; addr_op; value_op; call_offset; call_len; buf_op; Lit (n2w cap)])
           s1 = (Var q,s2)` by metis_tac[] >>
         `inst = mk_inst s1.cs_next_id (if is_static' then STATICCALL else CALL)
           (if is_static' then [gas_op; addr_op; call_offset; call_len; buf_op; Lit (n2w cap)]
            else [gas_op; addr_op; value_op; call_offset; call_len; buf_op; Lit (n2w cap)]) [q]`
           by simp[Abbr `inst`] >>
         `exec_ext_call inst t1 gas' aw (if is_static' then 0w else vw)
            ao' az' ro (n2w cap : bytes32) is_static' = OK z` by
           (`(if is_static' then 0w else vw) = vw` by
              (qpat_assum `is_static' ==> vw = 0w` mp_tac >>
               rpt (pop_assum kall_tac) >> Cases_on `is_static'` >> simp[]) >>
            qpat_assum `exec_ext_call inst t1 _ _ _ _ _ _ _ _ = OK z` mp_tac >>
            qpat_assum `is_static' <=> value_opt = NONE` mp_tac >>
            qpat_assum `(if is_static' then 0w else vw) = vw` mp_tac >>
            rpt (pop_assum kall_tac) >>
            disch_then SUBST1_TAC >> disch_then SUBST1_TAC >> simp[]) >>
         `z.vs_inst_idx = t1.vs_inst_idx` by
           (simp[Abbr `z`, venomStateTheory.update_var_def] >>
            qpat_x_assum `u' = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
         `~t1.vs_call_ctx.cc_static` by
           (qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel _ _ _ _ _ _ t1 /\ _`
              (qspec_then `H` mp_tac) >>
            (impl_tac >- first_assum ACCEPT_TAC) >>
            pure_rewrite_tac[ghost_inv_at_def, exprLoweringPropsTheory.stmt_state_rel_def,
              loweringStateRelDefsTheory.state_rel_def] >>
            rpt strip_tac >> first_assum ACCEPT_TAC) >>
         pure_rewrite_tac[venomStateTheory.next_inst_def] >>
         qpat_assum `z.vs_inst_idx = t1.vs_inst_idx`
           (fn th => pure_rewrite_tac[th]) >>
         pure_rewrite_tac[GSYM arithmeticTheory.ADD1] >>
         irule bodyFullExtCallCallPathTheory.extcall_checked_oracle_call >>
         rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
           goal_assum (drule_at Any) >>
           goal_assum (drule_at Any) >> rpt conj_tac >> first_assum ACCEPT_TAC]) >>
      `~z.vs_halted` by metis_tac[] >>
      `z.vs_alloca_next = t1.vs_alloca_next` by
        (simp[Abbr `z`, venomStateTheory.update_var_def] >>
         qpat_x_assum `u' = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
      (Cases_on `oc.co_success`
      >- (`eval_ext_call_effects cx target calldata value_opt gas ee.accounts ee =
              (INL oc.co_returnData, SND (adopt_call_outcome rq oc consumed))` by
            (simp[eval_ext_call_effects_def, bind_def, ignore_bind_def, return_def] >>
             qpat_assum `take_call_outcome target calldata value_opt ee = _`
               (fn th => rewrite_tac[th]) >>
             simp[vyperCallOutcomeTheory.adopt_call_outcome_equation] >>
             Cases_on `rq.cr_static` >> simp[]) >>
          `s1.cs_next_var <= sr.cs_next_var /\ s1.cs_next_id <= sr.cs_next_id` by
            (qpat_assum `emit_op _ _ s1 = _` mp_tac >>
             qpat_assum `fresh_label _ s2 = _` mp_tac >>
             qpat_assum `fresh_label _ s3 = _` mp_tac >>
             qpat_assum `emit_inst _ _ _ s4 = _` mp_tac >>
             qpat_assum `new_block _ s5 = _` mp_tac >>
             qpat_assum `emit_op _ _ s6 = _` mp_tac >>
             qpat_assum `compile_alloc_buffer _ s7 = _` mp_tac >>
             qpat_assum `emit_void _ _ s8 = _` mp_tac >>
             qpat_assum `emit_inst _ _ _ s9 = _` mp_tac >>
             qpat_assum `new_block _ s10 = _` mp_tac >>
             rpt (pop_assum kall_tac) >> rpt strip_tac >>
             gvs[compileEnvTheory.new_block_def, compileEnvTheory.fresh_label_def,
                 emitHelperTheory.emit_inst_def, emitHelperTheory.emit_void_def,
                 emitHelperTheory.emit_op_def, compileEnvTheory.comp_bind_def,
                 compileEnvTheory.comp_ignore_bind_def, compileEnvTheory.comp_return_def,
                 contextTheory.compile_alloc_buffer_def,
                 compileEnvTheory.fresh_var_def, compileEnvTheory.fresh_id_def,
                 compileEnvTheory.emit_def]) >>
          drule_at (Pat `eval_ext_call_effects _ _ _ _ _ _ _ = _`)
            extcall_success_return_boundary >>
          simp[] >>
          disch_then (drule_at (Pat `extcall_request_ready _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
          disch_then (drule_at (Pat `wb_frame _ _ _ _ _ _`)) >> simp[] >>
          disch_then (drule_at (Pat `new_block _ _ = _`)) >> simp[] >>
          strip_tac >>
          `eval_operand (Var q) (next_inst z) = SOME 1w /\
           op_taint (step_taint inst t1 z tn1) (Var q) = {}` by
            (drule_at (Pat `_.inst_outputs = _`)
               (Q.INST [`success` |-> `T`, `u` |-> `u'`, `s` |-> `t1`, `tn` |-> `tn1`]
                 extcall_call_result_observations) >>
             simp[Abbr `z`]) >>
          `!H. valid_horizon cx st0 H ee.storage_trace ==>
            gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t1,G1,tn1) []
              (OK (jump_to cont_lbl (next_inst z)),
               step_prov PG G1 inst z, step_taint inst t1 z tn1)` by
            (rpt strip_tac >>
             qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> gas_origin_ptr_path _ (t1,G1,tn1) _ _ /\ _`
               (qspec_then `H` mp_tac) >> simp[] >> strip_tac >>
             `allocas_from lo (next_inst z)` by
               (qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> access_ok _ _ _ _ _ /\ _`
                  (qspec_then `H` mp_tac) >>
                simp[ptrDisciplineTheory.allocas_from_def, venomStateTheory.next_inst_def] >>
                metis_tac[]) >>
             irule extcall_checked_success_path >>
             simp[venomStateTheory.next_inst_def] >>
             qexistsl_tac [`fail_lbl`, `q`, `s4`, `s5`] >>
             simp[venomStateTheory.next_inst_def] >>
             `s4.cs_current_bb = s2.cs_current_bb /\
              s4.cs_current_insts = s2.cs_current_insts` by
               (qpat_assum `fresh_label _ s2 = _` mp_tac >>
                qpat_assum `fresh_label _ s3 = _` mp_tac >>
                rpt (pop_assum kall_tac) >>
                simp[compileEnvTheory.fresh_label_def] >> rpt strip_tac >> gvs[]) >>
             `z.vs_current_bb = t1.vs_current_bb /\ z.vs_inst_idx = t1.vs_inst_idx` by
               (simp[Abbr `z`, venomStateTheory.update_var_def] >>
                qpat_assum `u' = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
             gvs[venomStateTheory.next_inst_def, arithmeticTheory.ADD1]) >>
          `z.vs_call_ctx = t1.vs_call_ctx /\ z.vs_immutables = t1.vs_immutables` by
            (simp[Abbr `z`, venomStateTheory.update_var_def] >>
             qpat_assum `u' = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
          `~(inst.inst_opcode = CALL /\ ~t1.vs_call_ctx.cc_static /\
              z.vs_requests <> t1.vs_requests /\ z.vs_outcomes <> t1.vs_outcomes /\
              (HD t1.vs_outcomes).co_success) ==>
            z.vs_accounts = t1.vs_accounts /\ z.vs_transient = t1.vs_transient` by
            (drule oracleCallStepPtrTheory.exec_ext_call_storage_cases >>
             strip_tac >> simp[] >>
             gvs[Abbr `inst`, venomInstTheory.mk_inst_def] >>
             Cases_on `value_opt` >> gvs[]) >>
          `!H. valid_horizon cx st0 H (SND (adopt_call_outcome rq oc consumed)).storage_trace ==>
            ghost_inv_at (DF H) lo d cenv cx (SND (adopt_call_outcome rq oc consumed))
              (step_prov PG G1 inst z) (step_taint inst t1 z tn1) z` by
            (rpt strip_tac >>
             `adopt_call_outcome rq oc consumed = (INL (), SND (adopt_call_outcome rq oc consumed))` by
               simp[vyperCallOutcomeTheory.adopt_call_outcome_equation] >>
             `valid_horizon cx st0 H consumed.storage_trace` by
               (qpat_assum `adopt_call_outcome _ _ _ = _`
                  (mp_then Any mp_tac valid_horizon_frame) >>
                simp[storage_trace_frame_adopt]) >>
             `valid_horizon cx st0 H ee.storage_trace` by
               (qpat_assum `take_call_outcome _ _ _ _ = _`
                  (mp_then Any mp_tac valid_horizon_frame) >>
                simp[storage_trace_frame_take_call]) >>
             ` (SND (adopt_call_outcome rq oc consumed)).scopes = ee.scopes` by
               (drule rawCallMemoryFramePtrTheory.oracle_take_adoption_locals >> metis_tac[]) >>
             irule (INST_TYPE [alpha |-> ``:160``] extcall_call_invariant) >>
             simp[] >>
             goal_assum (drule_at (Pat `extcall_request_ready _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
             qexists_tac `H` >> simp[]) >>
          `t.vs_alloca_next <= (jump_to cont_lbl (next_inst z)).vs_alloca_next` by
            simp[venomStateTheory.jump_to_def, venomStateTheory.next_inst_def] >>
          `safe_operand s1 default_op /\ safe_operand sp default_op` by
            fs[extcall_request_ready_def, EVERY_DEF] >>
          `eval_operand default_op z = eval_operand default_op t1` by
            (qpat_assum `!x. not_fresh_at s1 x ==> lookup_var x z = _` mp_tac >>
             qpat_assum `safe_operand s1 default_op` mp_tac >>
             rpt (pop_assum kall_tac) >> Cases_on `default_op` >>
             simp[venomStateTheory.eval_operand_def, exprSafeOperandTheory.safe_operand_def] >>
             metis_tac[]) >>
          `eval_operand default_op t1 = eval_operand default_op t` by
            (qpat_assum `!op. safe_operand sp op ==> _`
               (qspec_then `default_op` mp_tac) >> simp[]) >>
          `eval_operand default_op (jump_to cont_lbl (next_inst z)) =
             eval_operand default_op t` by
            (qpat_assum `eval_operand default_op z = eval_operand default_op t1` mp_tac >>
             qpat_assum `eval_operand default_op t1 = eval_operand default_op t` mp_tac >>
             rpt (pop_assum kall_tac) >> Cases_on `default_op` >>
             simp[venomStateTheory.jump_to_def, venomStateTheory.next_inst_def,
               venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def]) >>
          qpat_assum `!returnData ee' t' G' tn'. _`
            (qspecl_then [`oc.co_returnData`, `SND (adopt_call_outcome rq oc consumed)`,
              `jump_to cont_lbl (next_inst z)`, `step_prov PG G1 inst z`,
              `step_taint inst t1 z tn1`] mp_tac) >>
          (impl_tac >-
            (simp[bodyFullSharedTheory.ghost_inv_at_jump, extcall_ghost_inv_next_inst] >>
             rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
               (fs[EVERY_DEF] >> NO_TAC),
               (qpat_assum `!dv. _ ==> ptr_mem_ok _ _ _ _ (step_prov _ _ _ _) _ z /\ _` mp_tac >>
                rpt (pop_assum kall_tac) >>
                simp[venomStateTheory.jump_to_def, venomStateTheory.next_inst_def,
                  bodyPtrDefsTheory.ptr_mem_ok_def, venomStateTheory.eval_operand_def,
                  venomStateTheory.lookup_var_def] >>
                Cases_on `default_op` >>
                simp[venomStateTheory.eval_operand_def, venomStateTheory.next_inst_def,
                  venomStateTheory.lookup_var_def] >> NO_TAC),
               gvs[venomStateTheory.jump_to_def, venomStateTheory.next_inst_def,
                 bodyPtrDefsTheory.ptr_mem_ok_def, venomStateTheory.eval_operand_def,
                 venomStateTheory.lookup_var_def]])) >>
          strip_tac >>
          drule_at (Pat `take_call_outcome _ _ _ _ = _`) extcall_success_tail >>
          simp[] >>
          disch_then (qspecl_then [`skip`, `ret_type`, `k`, `gas`, `cx`] mp_tac) >>
          simp[] >> strip_tac >>
          Cases_on `storage_trace_domain cx st0 (SND (adopt_call_outcome rq oc consumed)).storage_trace`
          >- (irule gas_outcome_full_intro >>
              qexistsl_tac [`G''`, `SND (adopt_call_outcome rq oc consumed)`,
                `[]`, `r`, `res`, `tn''`] >>
              simp[] >> rpt strip_tac >>
              `adopt_call_outcome rq oc consumed = (INL (), SND (adopt_call_outcome rq oc consumed))` by
                simp[vyperCallOutcomeTheory.adopt_call_outcome_equation] >>
              `valid_horizon cx st0 H consumed.storage_trace` by
                (qpat_assum `adopt_call_outcome _ _ _ = _`
                   (mp_then Any mp_tac valid_horizon_frame) >>
                 simp[storage_trace_frame_adopt]) >>
              `valid_horizon cx st0 H ee.storage_trace` by
                (qpat_assum `take_call_outcome _ _ _ _ = _`
                   (mp_then Any mp_tac valid_horizon_frame) >>
                 simp[storage_trace_frame_take_call]) >>
              qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> gas_origin_ptr_path _ (t,G,tn) _ _`
                (qspec_then `H` mp_tac) >>
              (impl_tac >- first_assum ACCEPT_TAC) >>
              disch_then (mp_then Any mp_tac fragGasOriginPtrTheory.gas_origin_ptr_path_append) >>
              simp[] >> disch_then irule >>
              qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> gas_origin_ptr_path _ (t1,G1,tn1) _ (OK (jump_to _ _),_,_)`
                (qspec_then `H` mp_tac) >>
              (impl_tac >- first_assum ACCEPT_TAC) >>
              disch_then (mp_then Any mp_tac fragGasOriginPtrTheory.gas_origin_ptr_path_append) >>
              simp[] >> disch_then irule >> simp[]) >>
          irule gas_outcome_full_bad_nil >>
          simp[] >>
          fs[extcall_request_ready_def]) >>
      `eval_operand (Var q) (next_inst z) = SOME 0w /\
       op_taint (step_taint inst t1 z tn1) (Var q) = {}` by
        (drule_at (Pat `_.inst_outputs = _`)
           (Q.INST [`success` |-> `F`, `u` |-> `u'`, `s` |-> `t1`, `tn` |-> `tn1`]
             extcall_call_result_observations) >> simp[Abbr `z`]) >>
      `LENGTH oc.co_returnData < dimword (:256)` by
        (irule rawCallOutcomeLengthPtrTheory.take_call_outcome_returnData_length >>
         goal_assum (drule_at Any) >> simp[]) >>
      `allocas_from lo (next_inst z) /\ lo <= (next_inst z).vs_alloca_next` by
        (qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> ghost_inv_at _ _ _ _ _ _ _ _ t1`
           (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
         (impl_tac >- first_assum ACCEPT_TAC) >>
         pure_rewrite_tac[ghost_inv_at_def] >> strip_tac >>
         simp[venomStateTheory.next_inst_def] >>
         qpat_assum `allocas_from lo t1` mp_tac >>
         pure_rewrite_tac[ptrDisciplineTheory.allocas_from_def] >>
         qpat_assum `t1.vs_allocas = t.vs_allocas` (fn th => pure_rewrite_tac[th]) >>
         simp[]) >>
      `s4.cs_current_bb = s2.cs_current_bb /\
       s4.cs_current_insts = s2.cs_current_insts` by
        (qpat_assum `fresh_label _ s2 = _` mp_tac >>
         qpat_assum `fresh_label _ s3 = _` mp_tac >>
         rpt (pop_assum kall_tac) >>
         simp[compileEnvTheory.fresh_label_def] >> rpt strip_tac >> gvs[]) >>
      `z.vs_current_bb = s4.cs_current_bb /\
       (next_inst z).vs_inst_idx = LENGTH s4.cs_current_insts` by
        (qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> gas_origin_ptr_path _ (t1,G1,tn1) _ _ /\ _`
           (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
         (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
         `z.vs_current_bb = t1.vs_current_bb /\ z.vs_inst_idx = t1.vs_inst_idx` by
           (simp[Abbr `z`, venomStateTheory.update_var_def] >>
            qpat_assum `u' = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
         simp[venomStateTheory.next_inst_def, arithmeticTheory.ADD1]) >>
      qpat_assum `frame_call_value cx value_opt = _`
        (fn th => irule (REWRITE_RULE [th] extcall_failed_call_exit_full)) >>
      simp[] >>
      (conj_tac >- fs[extcall_request_ready_def]) >>
      goal_assum (drule_at (Pat `emit_inst JNZ _ _ _ = _`)) >>
      simp[venomStateTheory.next_inst_def] >>
      qexistsl_tac [`step_prov PG G1 inst z`, `[]`, `next_inst z`,
        `step_taint inst t1 z tn1`] >>
      simp[] >>
      (conj_tac >-
        (rpt strip_tac >>
         `valid_horizon cx st0 H ee.storage_trace` by
           (qpat_assum `take_call_outcome _ _ _ _ = _`
              (mp_then Any mp_tac valid_horizon_frame) >>
            simp[storage_trace_frame_take_call]) >>
         qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> gas_origin_ptr_path _ (t,G,tn) _ _`
           (qspec_then `H` mp_tac) >>
         (impl_tac >- first_assum ACCEPT_TAC) >>
         disch_then (mp_then Any mp_tac fragGasOriginPtrTheory.gas_origin_ptr_path_append) >>
         simp[] >> disch_then irule >> simp[])) >>
      simp[venomStateTheory.next_inst_def] >>
      `s4.cs_blocks = s1.cs_blocks` by
        (qpat_assum `emit_op _ _ s1 = _` mp_tac >>
         qpat_assum `fresh_label _ s2 = _` mp_tac >>
         qpat_assum `fresh_label _ s3 = _` mp_tac >>
         rpt (pop_assum kall_tac) >>
         simp[emitHelperTheory.emit_op_def, compileEnvTheory.emit_def,
           compileEnvTheory.fresh_id_def,
           compileEnvTheory.fresh_var_def, compileEnvTheory.fresh_label_def,
           compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
           compileEnvTheory.comp_return_def] >>
         rpt strip_tac >> gvs[]) >>
      fs[fragExecTheory.fn_has_code_def, fragExecTheory.emitted_blocks_def])) >>
  irule (INST_TYPE [alpha |-> ``:256``] extcall_precheck_exit_full) >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> ghost_inv_at _ _ _ _ _ _ _ _ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  pure_rewrite_tac[ghost_inv_at_def] >> strip_tac >>
  fs[extcall_request_ready_def, EVERY_DEF] >>
  conj_tac
  >- (qexistsl_tac [`addr_op`, `aw`, `s1`, `sp`] >> simp[]) >>
  qexistsl_tac [`storage_trace_horizon ee.storage_trace`, `cenv`] >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >> simp[]
QED

Theorem extcall_call_full:
  !DF lo d explicit ctx PG func cenv cx es st0 sa s0 G0 tn0 sp sr u
   is_static skip ret_type addr_op value_op gas_op buf_op call_offset
   call_len cap target value_opt calldata gas has_default default_op
   default_ty default_opt ee t G tn k Q.
    comp_ignore_bind
      (if ret_type = NoneT /\ ~skip then compile_extcodesize_check addr_op
       else comp_return ())
      (comp_bind
         (if is_static then
            emit_op STATICCALL
              [gas_op; addr_op; call_offset; call_len; buf_op; Lit (n2w cap)]
          else
            emit_op CALL
              [gas_op; addr_op; value_op; call_offset; call_len; buf_op;
               Lit (n2w cap)])
      (\success. comp_bind (fresh_label "extcall_fail") (\fail_lbl.
       comp_bind (fresh_label "extcall_cont") (\cont_lbl.
       comp_ignore_bind
         (emit_inst JNZ [success; Label cont_lbl; Label fail_lbl] [])
       (comp_ignore_bind (new_block fail_lbl)
       (comp_bind (emit_op RETURNDATASIZE []) (\rds.
       comp_bind (compile_alloc_buffer 0) (\fail_buf.
       comp_ignore_bind
         (emit_void RETURNDATACOPY [fail_buf.buf_operand; Lit 0w; rds])
       (comp_ignore_bind (emit_inst REVERT [fail_buf.buf_operand; rds] [])
          (new_block cont_lbl)))))))))) sp = (u, sr) /\
    fn_has_code sp sr func /\ fn_inst_ids_distinct func /\
    MEM func ctx.ctx_functions /\ ~ctx_has_dalloca ctx /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
            not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
            not_fresh_at sa x) /\
    extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sp is_static
      addr_op value_op gas_op buf_op call_offset call_len cap
      target value_opt calldata has_default default_op default_ty default_opt
      ee t /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       ghost_inv_at (DF H) lo d cenv cx ee G tn t) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
    EVERY (\op. op_taint tn op = {})
      [addr_op; value_op; gas_op; buf_op; call_offset; call_len; default_op] /\
    (?ao az. eval_operand call_offset t = SOME ao /\
       eval_operand call_len t = SOME az /\
       (w2n az <> 0 ==> w2n ao + w2n az <= t.vs_alloca_next) /\
       (!i. w2n ao <= i /\ i < w2n ao + w2n az ==> i NOTIN tn.t_mem) /\
       (w2n az <> 0 ==>
        ?v b sz. call_offset = Var v /\ FLOOKUP G v = SOME (b,sz) /\
                 b <= w2n ao /\ w2n ao + w2n az <= b + sz)) /\
    (!dv. default_opt = SOME dv /\ ~is_word_type default_ty ==>
       ptr_mem_ok cx default_ty dv default_op G tn t /\
       (type_memory_bytes cenv default_ty <> 0 ==>
        ?x b sz w. default_op = Var x /\ FLOOKUP G x = SOME (b,sz) /\
          eval_operand default_op t = SOME w /\ b <= w2n w /\
          w2n w + type_memory_bytes cenv default_ty <= b + sz)) /\
    (cap <> 0 ==>
     ?v b sz ro. buf_op = Var v /\ FLOOKUP G v = SOME (b,sz) /\
       eval_operand buf_op t = SOME ro /\ b <= w2n ro /\
       w2n ro + cap <= b + sz) /\
    (!returnData. storage_trace_frame (k returnData)) /\
    (!returnData ee' t' G' tn'.
       extcall_returned st0 ctx func cenv cx ret_type es sa s0 sr addr_op
         buf_op cap target has_default default_op default_ty default_opt
         returnData ee' t' /\
       alloca_history func t' /\ s0.vs_alloca_next <= t'.vs_alloca_next /\
       (!H. valid_horizon cx st0 H ee'.storage_trace ==>
          ghost_inv_at (DF H) lo d cenv cx ee' G' tn' t') /\
       ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn' /\
       EVERY (\op. op_taint tn' op = {}) [addr_op; buf_op; default_op] /\
       (!dv. default_opt = SOME dv /\ ~is_word_type default_ty ==>
          ptr_mem_ok cx default_ty dv default_op G' tn' t' /\
          (type_memory_bytes cenv default_ty <> 0 ==>
           ?x b sz w. default_op = Var x /\ FLOOKUP G' x = SOME (b,sz) /\
             eval_operand default_op t' = SOME w /\ b <= w2n w /\
             w2n w + type_memory_bytes cenv default_ty <= b + sz)) /\
       (cap <> 0 ==>
        ?v b sz ro. buf_op = Var v /\ FLOOKUP G' v = SOME (b,sz) /\
          eval_operand buf_op t' = SOME ro /\ b <= w2n ro /\
          w2n ro + cap <= b + sz /\
          (!i. w2n ro <= i /\ i < w2n ro + MIN cap (LENGTH returnData) ==>
              i NOTIN tn'.t_mem)) ==>
       ?res r G'' tn''.
         (!tail. k returnData (ee' with gas_obs := tail) =
           (res, ee' with gas_obs := tail)) /\
         (!H. valid_horizon cx st0 H ee'.storage_trace ==>
           gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
             (t', G', tn') [] (r, G'', tn'') /\
           ((?t''. r = OK t'' /\
               Q H res (ee' with gas_obs := []) G'' tn'' t'') \/
            (exit_result r /\ expr_exit res r)))) ==>
    gas_outcome_full (DF, lo, explicit, ctx, func, PG) (cx_tops cx) cx st0
      (do accounts <- get_accounts;
          check (ext_call_precheck_ok skip ret_type target accounts)
                "ExtCall target has no code";
          value_opt' <- frame_call_value cx value_opt;
          returnData <- eval_ext_call_effects cx target calldata value_opt'
                          gas accounts;
          k returnData
       od) (ee, t, G, tn) Q (\H res ee gt r. expr_exit res r)
Proof
  rpt gen_tac >> strip_tac >>
  match_mp_tac (Q.SPECL
    [`DF`,`lo`,`d`,`explicit`,`ctx`,`PG`,`func`,`cenv`,`cx`,`es`,`st0`,
     `sa`,`s0`,`G0`,`tn0`,`sp`,`sr`,`u`,`is_static'`,`skip`,`ret_type`,
     `addr_op`,`value_op`,`gas_op`,`buf_op`,`call_offset`,`call_len`,`cap`,
     `target`,`value_opt`,`calldata`,`gas`,`has_default`,`default_op`,
     `default_ty`,`default_opt`,`ee`,`t`,`G`,`tn`,`k`,`Q`]
    extcall_call_full_default_frame) >>
  simp[] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!returnData ee' t' G' tn'. _`
    (qspecl_then [`returnData`,`ee'`,`t'`,`G'`,`tn'`] mp_tac) >> simp[]
QED

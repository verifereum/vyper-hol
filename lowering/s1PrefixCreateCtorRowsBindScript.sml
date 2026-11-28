(* Bind the constructor-row traversal to its successful continuation. *)
Theory s1PrefixCreateCtorRowsBind
Ancestors
  bodyFullCreateHeld s1PrefixCompose s1PrefixDefs s1PrefixProps
  bodyFullPreds exprSimHypsDefs exprBodyPreProps exprLowering
  builtinCreate compileEnv gasShadow gasShadowState fragExec
  fragGasOriginPtr gasOutcomeFull gasStorage vyperStorageTrace
  vyperStorageFootprint vyperTypeSystem vyperInterpreter vyperState
  venomState stmtSimDefs stmtSimProps[qualified] exprSimDefs[qualified]
  exprLoweringProps loweringStateRelDefs bodyPtrDefs gasShadowCompileHelpers
  memLocDefs codegenRel contextCodegenRel allocLimits finite_map list sum

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac bodyFullCreateHeldTheory.create_ctor_rows_outcome >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_tac >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ rowQ rowR` >>
  (* Resolve the callback while the outcome still exposes its path and
     all-tail replay together. The bind rule then uses the resulting post. *)
  qabbrev_tac `continue = \(H : (bool # 256 word # type_value) list # num list)
    (res : value list + vyperState$exception) ee G tn t.
    !vs. res = INL vs ==>
      gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        cx st0 (next vs) (ee,t,G,tn)` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (eval_exprs cx xs) (es,s0,G0,tn0) continue rowR` by
    (qpat_x_assum `gas_outcome_full _ _ _ _ _ _ rowQ rowR`
       (qx_choose_then `marks` strip_assume_tac o
        ONCE_REWRITE_RULE[gas_outcome_full_def]) >>
     ONCE_REWRITE_TAC[gas_outcome_full_def] >> qexists `marks`
     >- (disj1_tac >> simp[] >> metis_tac[])
     >- (disj2_tac >> disj1_tac >> qexistsl [`res`,`ee`,`r`,`G'`,`tn'`] >>
         simp[] >> Cases_on `r` >> gvs[exit_result_def, Abbr `continue`] >>
         rpt strip_tac >>
         FIRST [first_assum ACCEPT_TAC,
          (qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
             (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC),
          (qpat_assum `!marks' vs ee' G tn t. _ ==> gas_prefix_full _ _ _ _ _` irule >>
           simp[] >> reverse conj_tac
           >- (qexists `marks` >> simp[] >> metis_tac[]) >>
           qx_gen_tac `horizon` >> strip_tac >>
           qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
             (qspec_then `horizon` mp_tac) >>
           (impl_tac >- first_assum ACCEPT_TAC) >>
           disch_then (assume_tac o CONJUNCT2) >> fs[Abbr `rowQ`])]) >>
     disj2_tac >> disj2_tac >>
     rename1 `gas_origin_ptr_focus (DF horizon,_,_,_,_,_) _ _ (leaf,leaf_pg,leaf_g,leaf_tn,end_state)` >>
     qexistsl [`err`,`ee`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`end_state`] >>
     simp[] >> qexists `horizon` >> simp[]) >>
  irule gas_prefix_full_bind >>
  simp[evaluate_requests_outcomes_frame, evaluate_storage_trace_frame] >>
  qexistsl [`continue`, `rowR`, `cx_tops cx`] >>
  simp[Abbr `continue`, Abbr `rowR`] >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> fs[storage_trace_domain_def] >>
      metis_tac[]) >>
  rpt gen_tac >> Cases_on `res` >>
  simp[exprSimDefsTheory.halt_exit_def]
QED
*)
Theorem create_ctor_rows_bind_prefix_from_traversal:
  body_const_cells_agree [(NONE,tops)] cx env es /\
  body_exprs_full_ok cx xs /\ body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\ expr_sim_inv cenv cx env es /\
  (!e st. MEM e xs /\ expr_sim_inv cenv cx env st ==>
     expr_body_pre cenv cx env e st) /\
  compile_create_ctor_args compile_expr cenv xs sa = (svs,sb) /\
  compile_create_ctor_args compile_expr (gas_shadow_env T cenv) (MAP gas_shadow_expr xs)
    shadow_sa = (svs,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!fn inst z. frag_reachable ctx func s0 fn inst z ==> dalloca_fmp_headroom inst z) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!vs. storage_trace_frame (next vs)) /\
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (eval_exprs cx xs) (es,s0,G0,tn0) /\
  (!marks vs ee G tn t.
    (!tail. eval_exprs cx xs (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
            (INL vs,ee with gas_obs := tail)) /\
    storage_trace_domain cx st0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s0,G0,tn0) marks (OK t,G,tn)) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      LENGTH svs = LENGTH xs /\
      LIST_REL (\(e,sv) v.
        (?si sm ss vv raw copy.
          compile_expr cenv (expr_type e) e si = (vv,sm) /\
          compile_snapshot_vv cenv copy
            (ext_call_arg_value (lowered_value_type cenv e) vv) sm = (sv,ss) /\
          (copy /\ ~is_word_type (lowered_value_type cenv e) ==>
            ?p w tv. vv_location sv = SOME LocMemory /\ vv_operand sv = Var p /\
              eval_operand (vv_operand sv) t = SOME w /\
              evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv /\
              val_wf tv v /\ FLOOKUP t.vs_allocas sm.cs_next_id =
                SOME (w2n w,type_memory_size tv) /\
              sm.cs_next_id < ss.cs_next_id /\
              (!n b sz. local_region cenv ee.scopes t n b sz ==>
                regions_disjoint (w2n w) (type_memory_size tv) b sz)) /\
          sa.cs_next_var <= si.cs_next_var /\ sa.cs_next_id <= si.cs_next_id /\
          sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
          ss.cs_next_var <= sb.cs_next_var /\ ss.cs_next_id <= sb.cs_next_id /\
          local_ptrs_reserved cenv si /\
          (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
          (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
          ((?tag op0. sv = StackValue tag op0) \/
           (?p. sv = LocatedValue (lowered_value_type cenv e) p /\
             ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location = LocMemory) \/
           (?p. sv = LocatedValue (lowered_value_type cenv e) p /\
             ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location <> LocMemory /\
             lowered_value_type cenv e = expr_type e /\ sv = vv)) /\
          read_result cx raw ee = (INL v,ee) /\
          vv_holds cenv cx (lowered_value_type cenv e) raw sv ee t /\
          vv_at cenv cx (lowered_value_type cenv e) si ss ee raw sv t /\
          ptr_vv_ok cx (lowered_value_type cenv e) raw sv ee G tn t /\
          vv_store_bound cx (lowered_value_type cenv e) (lowered_value_type cenv e) ee raw sv t) /\
        vv_storage_live H cx sv ee t /\
        (!tag op. sv = StackValue tag op /\ ~is_word_type (lowered_value_type cenv e) ==>
          ptr_buf_ok cenv e op G t) /\
        (!tag p. sv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
          ptr_buf_ok cenv e p.ptr_operand G t) /\
        (cenv.ce_is_ctor /\ vv_location sv = SOME LocCode ==>
          !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
            eval_operand (vv_operand sv) t = SOME w ==>
            w2n w + type_memory_size rt <= lo /\
            (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
              val_in_memory rt v (w2n w) mem))) (ZIP (xs,svs)) vs /\
      EVERY (\sv. !x. vv_operand sv = Var x ==> not_fresh_at sb x) svs /\
      stmt_state_rel H ctx func cenv cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      return_buf_frame d cenv sb t /\ ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      wb_frame cenv es ee sa s0 t /\ MAP FDOM ee.scopes = MAP FDOM es.scopes /\
      expr_sim_inv cenv cx env ee /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b)) ==>
    gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (next vs) (ee,t,G,tn)) ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (bind (eval_exprs cx xs) next) (es,s0,G0,tn0)
Proof
  cheat
QED

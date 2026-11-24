(* Scoped simulation of the constructor row fold. The head source action
   returns a value; the complete fold returns a list of values. *)
Theory entryCreateCtorRowsScope
Ancestors
  entryCreateCompositeFocus entryCreateFocusSpec entryCreatePendingScope entryCreatePathScope
  createSizeOperandCode createSizeConcreteSnapshots createSizeCreateLayoutCode
  bodyFullCreateHeld bodyFullPreds bodyFullShadowBodyInv bodyFullForArrayRound
  exprLowering exprLoweringProps gasShadow gasShadowState gasShadowCompile
  gasShadowCompileConvert gasShadowCompileHelpers gasShadowCompilePure
  exprSimSource exprBodyPreProps exprSimWordArgs fragExec gasExemptCert vyperStorageTrace
  vyperStorageFootprint vyperInterpreter vyperState compileEnv
  bodyPtrDefs wordArgsPtr exprSimHypsDefs loweringPosts finite_map list
  entryCreateCompletedCut fragGasOriginPtr gasSummary fragGasOrigin

Definition create_ctor_head_post_def:
  create_ctor_head_post (DF,lo,d,ctx,func) cenv cx e (es,sa,sm,ss,vv,sv,copy,s0,G0,tn0)
    H res ee G tn t <=> ?v. res = INL v /\
      ((?tag op. sv = StackValue tag op) \/
       (?p. sv = LocatedValue (lowered_value_type cenv e) p /\
         ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location = LocMemory) \/
       (?p. sv = LocatedValue (lowered_value_type cenv e) p /\
         ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location <> LocMemory /\
         lowered_value_type cenv e = expr_type e /\ sv = vv)) /\
      (?raw. read_result cx raw ee = (INL v,ee) /\
        vv_holds cenv cx (lowered_value_type cenv e) raw sv ee t /\
        vv_at cenv cx (lowered_value_type cenv e) sa ss ee raw sv t /\
        ptr_vv_ok cx (lowered_value_type cenv e) raw sv ee G tn t /\
        vv_store_bound cx (lowered_value_type cenv e) (lowered_value_type cenv e) ee raw sv t) /\
      vv_storage_live H cx sv ee t /\
      ((case sv of StackValue _ _ => ~is_word_type (lowered_value_type cenv e)
                  | LocatedValue _ p => p.ptr_location = LocMemory) ==>
        ptr_buf_ok cenv e (vv_operand sv) G t) /\
      (copy /\ ~is_word_type (lowered_value_type cenv e) ==>
        ?x w tv. vv_location sv = SOME LocMemory /\ vv_operand sv = Var x /\
          eval_operand (vv_operand sv) t = SOME w /\
          evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv /\ val_wf tv v /\
          FLOOKUP t.vs_allocas sm.cs_next_id = SOME (w2n w,type_memory_size tv) /\
          sm.cs_next_id < ss.cs_next_id /\
          (!n b len. local_region cenv ee.scopes t n b len ==>
             regions_disjoint (w2n w) (type_memory_size tv) b len)) /\
      stmt_state_rel H ctx func cenv cx ee t /\ storage_well_formed_on cx ee (FST H) /\
      return_buf_frame d cenv ss t /\ ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\ alloca_history func t /\
      s0.vs_alloca_next <= t.vs_alloca_next /\ ~t.vs_halted /\
      t.vs_current_bb = ss.cs_current_bb /\ t.vs_inst_idx = LENGTH ss.cs_current_insts /\
      wb_frame cenv es ee sa s0 t /\ MAP FDOM ee.scopes = MAP FDOM es.scopes
End

Definition create_ctor_saved_at_def:
  create_ctor_saved_at (H,lo,cenv,cx,sa,sb,ee,G,tn,t) (e,sv) v <=>
    (?si sm ss vv raw copy.
      compile_expr cenv (expr_type e) e si = (vv,sm) /\
      compile_snapshot_vv cenv copy
        (ext_call_arg_value (lowered_value_type cenv e) vv) sm = (sv,ss) /\
      (copy /\ ~is_word_type (lowered_value_type cenv e) ==>
        ?p w tv. vv_location sv = SOME LocMemory /\ vv_operand sv = Var p /\
          eval_operand (vv_operand sv) t = SOME w /\
          evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv /\
          val_wf tv v /\ FLOOKUP t.vs_allocas sm.cs_next_id = SOME (w2n w,type_memory_size tv) /\
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
          val_in_memory rt v (w2n w) mem))
End

Definition create_ctor_rows_post_def:
  create_ctor_rows_post (DF,lo,d,ctx,func) cenv cx env (xs,svs) (es,sa,sb,s0,G0,tn0)
    H res ee G tn t <=>
      ?vs. res = INL vs /\ LENGTH svs = LENGTH xs /\
      LIST_REL (create_ctor_saved_at (H,lo,cenv,cx,sa,sb,ee,G,tn,t)) (ZIP (xs,svs)) vs /\
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
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b)
End

Theorem create_ctor_rows_scoped_nil[local]:
  expr_sim_inv cenv cx env es /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ create_operand_at sa s0 ==>
  scoped_operand_outcome (DF,lo,E,ctx,func,PG) tops cx st0 sa sa
    (eval_exprs cx []) (es,s0,G0,tn0)
    (create_ctor_rows_post (DF,lo,d,ctx,func) cenv cx env ([],[]) (es,sa,sa,s0,G0,tn0)) R
Proof
  strip_tac >> irule scoped_operand_pure >>
  simp[] >> qexistsl_tac [`es`,`INL ([]:value list)`] >>
  simp[evaluate_def,return_def,create_ctor_rows_post_def,ghost_kept_at_refl] >>
  rpt strip_tac >>
  `storage_well_formed_on cx (es with gas_obs := []) (FST H) <=>
   storage_well_formed_on cx es (FST H)` by
    (irule storage_well_formed_on_backends >> simp[]) >>
  qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  fs[ghost_inv_at_def,wb_frame_refl,create_operand_at_def] >>
  first_assum ACCEPT_TAC
QED

Theorem create_ctor_scope_compile_cons[local]:
  gas_shadow_state sa sha /\
  compile_create_ctor_args compile_expr cenv (e::xs) sa = (svs,sc) /\
  compile_create_ctor_args compile_expr (gas_shadow_env T cenv)
    (MAP gas_shadow_expr (e::xs)) sha = (svs,shc) ==>
  ?vv sm shm sv ss shs tail_svs.
    compile_expr cenv (expr_type e) e sa = (vv,sm) /\
    compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) sha = (vv,shm) /\
    gas_shadow_state sm shm /\ gas_shadow_state ss shs /\
    compile_snapshot_vv cenv (exprs_can_mutate cenv xs)
      (ext_call_arg_value (lowered_value_type cenv e) vv) sm = (sv,ss) /\
    compile_snapshot_vv cenv (exprs_can_mutate cenv xs)
      (ext_call_arg_value (lowered_value_type cenv e) vv) shm = (sv,shs) /\
    compile_create_ctor_args compile_expr cenv xs ss = (tail_svs,sc) /\
    compile_create_ctor_args compile_expr (gas_shadow_env T cenv)
      (MAP gas_shadow_expr xs) shs = (tail_svs,shc) /\ svs = sv::tail_svs
Proof
  strip_tac >>
  Cases_on `compile_expr cenv (expr_type e) e sa` >>
  rename1 `compile_expr cenv (expr_type e) e sa = (vv,sm)` >>
  Cases_on `compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) sha` >>
  rename1 `compile_expr _ (expr_type e) (gas_shadow_expr e) sha = (svv,shm)` >>
  `svv = vv /\ gas_shadow_state sm shm` by
    (`gas_shadow_compiles (compile_expr cenv (expr_type e) e)
        (compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e))` by
       irule (cj 1 gas_shadow_compile_expr_env |> SPEC_ALL |>
              Q.INST [`shadow` |-> `T`] |> SIMP_RULE (srw_ss()) []) >>
     drule_all nonslot_shadow_cut >> simp[]) >>
  qpat_x_assum `svv = vv` SUBST_ALL_TAC >>
  qabbrev_tac `snap = compile_snapshot_vv cenv (exprs_can_mutate cenv xs)
                        (ext_call_arg_value (lowered_value_type cenv e) vv)` >>
  Cases_on `snap sm` >> rename1 `snap sm = (sv,ss)` >>
  Cases_on `snap shm` >> rename1 `snap shm = (ssv,shs)` >>
  `ssv = sv /\ gas_shadow_state ss shs` by
    (`gas_shadow_compiles snap snap` by simp[Abbr `snap`,gas_shadow_compiles_snapshot_vv] >>
     drule_all nonslot_shadow_cut >> simp[]) >>
  qpat_x_assum `ssv = sv` SUBST_ALL_TAC >>
  Cases_on `compile_create_ctor_args compile_expr cenv xs ss` >>
  Cases_on `compile_create_ctor_args compile_expr (gas_shadow_env T cenv) (MAP gas_shadow_expr xs) shs` >>
  qpat_x_assum `compile_create_ctor_args _ _ (e::xs) sa = _`
    (mp_tac o ONCE_REWRITE_RULE [compile_create_ctor_args_def]) >>
  qpat_x_assum `compile_create_ctor_args _ _ (MAP _ (e::xs)) sha = _`
    (mp_tac o ONCE_REWRITE_RULE [compile_create_ctor_args_def] o REWRITE_RULE [MAP]) >>
  simp[comp_bind_def,comp_return_def,gas_shadow_expr_type,gas_shadow_expr_can_mutate,
       gas_shadow_lowered_value_type,Abbr `snap`] >>
  rpt strip_tac >> gvs[]
QED

(* A law antecedent, specialized only at its two success types.  It can
   be discharged by scoped_operand_bind_all_mixed at the assembly site. *)
Definition create_ctor_mixed_bind_law_def:
  create_ctor_mixed_bind_law DF lo explicit ctx func PG tops cx st0 <=>
  !a m b (source:evaluation_state -> (value + exception) # evaluation_state)
     (next:value -> evaluation_state -> (value list + exception) # evaluation_state)
     es s G tn Q1 Q R.
    scoped_operand_outcome (DF,lo,explicit,ctx,func,PG) tops cx st0 a m
      source (es,s,G,tn) Q1 (\H res ee gt r. ?exc. res = INR exc /\ R H (INR exc) ee gt r) /\
    (!marks res mid G1 tn1 t.
       (!tail. source (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
           (res, mid with gas_obs := tail)) /\
       storage_trace_domain cx st0 mid.storage_trace /\
       create_operand_at m t /\
       create_operand_full_scope a m explicit ctx func s marks (OK t) /\
       (!H. valid_horizon cx st0 H mid.storage_trace ==>
         Q1 H res mid G1 tn1 t /\ gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
                                     (s,G,tn) marks (OK t,G1,tn1)) ==>
       ?v. res = INL v /\ scoped_operand_outcome (DF,lo,explicit,ctx,func,PG)
               tops cx st0 m b (next v) (mid,t,G1,tn1) Q R) /\
    storage_trace_frame source /\ (!v. storage_trace_frame (next v)) /\
    (!marks err ee leaf finish.
       gas_exempt_cert T tops (ctx,func) (ignore_bind source (return ()))
         (es,s) marks (err,ee) (leaf,finish) ==>
       gas_exempt_cert T tops (ctx,func) (ignore_bind (bind source next) (return ()))
         (es,s) marks (err,ee) (leaf,finish)) /\
    (!left v mid t right err ee leaf finish.
       gas_marked_exec T (ctx,func) source (es,s) left (INL v) mid (OK t) /\
       gas_exempt_cert T tops (ctx,func) (ignore_bind (next v) (return ()))
         (mid with gas_obs := [],t) right (err,ee) (leaf,finish) ==>
       gas_exempt_cert T tops (ctx,func) (ignore_bind (bind source next) (return ()))
         (es,s) (left ++ right) (err,ee) (leaf,finish)) /\
    (!marks. create_operand_focus_scope a m explicit ctx func s marks ==>
       create_operand_focus_scope a b explicit ctx func s marks) /\
    (!marks r. exit_result r /\ create_operand_full_scope a m explicit ctx func s marks r ==>
       create_operand_full_scope a b explicit ctx func s marks r) /\
    (!left t right. create_operand_full_scope a m explicit ctx func s left (OK t) /\
       create_operand_focus_scope m b explicit ctx func t right ==>
       create_operand_focus_scope a b explicit ctx func s (left ++ right)) /\
    (!left t right r. create_operand_full_scope a m explicit ctx func s left (OK t) /\
       create_operand_full_scope m b explicit ctx func t right r ==>
       create_operand_full_scope a b explicit ctx func s (left ++ right) r) ==>
    scoped_operand_outcome (DF,lo,explicit,ctx,func,PG) tops cx st0 a b
      (bind source next) (es,s,G,tn) Q R
End

(* The head rule is guarded at the *actual* ordinary and shadow row cuts.
   Its three specializations share both the normal and the terminal post. *)
Definition create_ctor_scoped_head_def:
  create_ctor_scoped_head (DF,lo,d,ctx,shadow_ctx,func,shadow_func,PG) tops cenv cx env xs guard <=>
  !e es sa sm ss sha shm shs vv sv copy s0 G0 tn0 st0.
    MEM e xs /\ guard e copy /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    body_expr_full_ok cx e /\ body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\ expr_body_pre cenv cx env e es /\
    compile_expr cenv (expr_type e) e sa = (vv,sm) /\
    compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) sha = (vv,shm) /\
    compile_snapshot_vv cenv copy (ext_call_arg_value (lowered_value_type cenv e) vv) sm = (sv,ss) /\
    compile_snapshot_vv cenv copy (ext_call_arg_value (lowered_value_type cenv e) vv) shm = (sv,shs) /\
    gas_shadow_state sa sha /\ gas_shadow_state ss shs /\
    gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
    gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
    MEM shadow_func shadow_ctx.ctx_functions /\ fn_has_code sa ss func /\
    fn_has_code sha shs shadow_func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    (!fn inst z. frag_reachable ctx func s0 fn inst z ==> dalloca_fmp_headroom inst z) /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es s0 /\
      storage_well_formed_on cx es (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
    ~s0.vs_halted /\ create_operand_at sa s0 ==>
    scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 sa ss (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
      (create_ctor_head_post (DF,lo,d,ctx,func) cenv cx e (es,sa,sm,ss,vv,sv,copy,s0,G0,tn0))
      (create_operand_exit_post ctx cx)
End

Theorem create_ctor_scoped_head_subset[local]:
  (!e. MEM e ys ==> MEM e xs) /\ create_ctor_scoped_head cfg tops cenv cx env xs guard ==>
  create_ctor_scoped_head cfg tops cenv cx env ys guard
Proof
  PairCases_on `cfg` >> simp[create_ctor_scoped_head_def] >> strip_tac >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `MEM e xs` by metis_tac[] >>
  first_x_assum irule >> simp[] >>
  rpt conj_tac >> TRY (qexistsl_tac [`sha`,`shm`,`shs`] >> simp[] >> NO_TAC) >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

Theorem create_ctor_scoped_head_error[local]:
  scoped_operand_outcome (DF,lo,E,ctx,f,PG) tops cx st0 a m source inp Q1
    (create_operand_exit_post ctx cx) ==>
  scoped_operand_outcome (DF,lo,E,ctx,f,PG) tops cx st0 a m source inp Q1
    (\H (res:value + exception) ee gt r.
      ?exc. res = INR exc /\ create_operand_exit_post ctx cx H (INR exc:value list + exception) ee gt r)
Proof
  PairCases_on `inp` >> simp[scoped_operand_outcome_def] >> strip_tac >>
  qexists_tac `marks`
  >- (disj1_tac >> simp[] >> metis_tac[])
  >- (disj2_tac >> disj1_tac >> qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >> simp[] >>
      rpt strip_tac >> res_tac >> simp[] >>
      Cases_on `res` >>
      gvs[create_operand_exit_post_def,stmtSimPropsTheory.expr_exit_INR_type,
          exprSimDefsTheory.halt_exit_def]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

(* The all-tails source equation is used only in the normal head callback. *)
Theorem create_ctor_rows_source_advance[local]:
  body_const_cells_agree mods cx env es /\
  expr_body_pre cenv cx env e es /\ body_exprs_full_ok cx (e::xs) /\
  (!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := prefix ++ tail) = (INL v,mid with gas_obs := tail)) ==>
  body_const_cells_agree mods cx env mid /\ expr_sim_inv cenv cx env mid /\
  body_exprs_full_ok cx xs
Proof
  strip_tac >>
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := prefix) =
     (INL v,mid with gas_obs := [])` by
    (qpat_assum `!tail. bind _ _ _ = _`
      (qspec_then `[]` (ACCEPT_TAC o REWRITE_RULE [APPEND_NIL]))) >>
  conj_tac
  >- (qpat_assum `expr_body_pre _ _ _ _ _`
        (strip_assume_tac o MATCH_MP expr_body_pre_static_facts) >>
      `body_const_cells_agree mods cx env (mid with gas_obs := [])` suffices_by simp[] >>
      irule body_const_cells_agree_expr_read >>
      qexistsl_tac [`e`,`INL v`,`es with gas_obs := prefix`] >> simp[]) >>
  conj_tac
  >- (`expr_body_pre cenv cx env e (es with gas_obs := prefix)` by simp[] >>
      drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_eval) >> simp[]) >>
  drule_at (Pat `bind _ _ _ = _`) (REWRITE_RULE [ETA_AX] eval_expr_read_INL) >>
  strip_tac >> fs[Once body_exprs_full_ok_def] >> metis_tac[]
QED

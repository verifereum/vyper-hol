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
  bodySingletonCallSupport context entryCreateIntervalLayout createSizeCutRegion
  createSizeCutCode createSizePrefixReplay createMarkedPath relation arithmetic
  venomExecSemantics abiEncoderProps entryCreateOperandReplay stmtLoweringMono

Definition create_ctor_head_post_def:
  create_ctor_head_post (DF,lo,d,ctx,func) cenv cx e (es,sa,sm,ss,vv,sv,copy,s0,G0,tn0)
    (H:(bool # bytes32 # type_value) list # num list) (res:value + exception) ee G tn t <=> ?v. res = INL v /\
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
    (H:(bool # bytes32 # type_value) list # num list) (res:value list + exception) ee G tn t <=>
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

Theorem create_ctor_saved_at_weaken_start[local]:
  ci_mono sa ss /\ create_ctor_saved_at (H,lo,cenv,cx,ss,sc,ee,G,tn,t) row v ==>
  create_ctor_saved_at (H,lo,cenv,cx,sa,sc,ee,G,tn,t) row v
Proof
  PairCases_on `row` >> simp[create_ctor_saved_at_def,ci_mono_def] >> strip_tac >>
  rename1 `compile_expr cenv _ _ si = (vv,sm)` >>
  rename1 `compile_snapshot_vv cenv copy _ sm = (_,sr)` >>
  qexistsl_tac [`si`,`sm`,`sr`,`vv`,`raw`,`copy`] >> simp[] >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

(* Transport the chosen head over a successful tail. This theorem has no
   scoped premise: the same post transport also applies to ordinary paths. *)
Theorem create_ctor_rows_post_cons:
  body_inv tops ctx cenv cx /\ body_exprs_full_ok cx xs /\
  expr_body_pre cenv cx env e es /\ expr_sim_inv cenv cx env mid /\
  (!e st. MEM e xs /\ expr_sim_inv cenv cx env st ==> expr_body_pre cenv cx env e st) /\
  copy = exprs_can_mutate cenv xs /\
  compile_expr cenv (expr_type e) e sa = (vv,sm) /\
  compile_snapshot_vv cenv copy (ext_call_arg_value (lowered_value_type cenv e) vv) sm = (sv,ss) /\
  ci_mono sa sm /\ ci_mono sm ss /\ ci_mono sa ss /\ ci_mono ss sc /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv ss /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  stmt_state_rel H ctx func cenv cx es s0 /\ dead_lo_ok H (DF H) lo cenv cx /\
  eval_exprs cx xs (mid with gas_obs := obs) = (INL vs,ee) /\ u.vs_labels = t.vs_labels /\
  create_ctor_head_post (DF,lo,d,ctx,func) cenv cx e (es,sa,sm,ss,vv,sv,copy,s0,G0,tn0)
    H (INL v) mid G1 tn1 t /\
  create_ctor_rows_post (DF,lo,d,ctx,func) cenv cx env (xs,tail_svs) (mid,ss,sc,t,G1,tn1)
    H (INL vs) ee G2 tn2 u ==>
  create_ctor_rows_post (DF,lo,d,ctx,func) cenv cx env (e::xs,sv::tail_svs) (es,sa,sc,s0,G0,tn0)
    H (INL (v::vs)) ee G2 tn2 u
Proof
  simp[create_ctor_head_post_def,create_ctor_rows_post_def] >>
  disch_then (map_every (REPEAT_TCL CHOOSE_THEN assume_tac) o CONJUNCTS) >>
  `wb_frame cenv es ee sa s0 u` by
    (irule (INST_TYPE [alpha |-> ``:256``] wb_frame_trans) >> simp[] >> conj_tac
     >- (qexistsl_tac [`mid`,`ss`,`t`] >> fs[ci_mono_def]) >>
     qexistsl_tac [`H`,`ctx`,`cx`,`func`] >> simp[]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2` by
    (irule (INST_TYPE [beta |-> ``:256``] ghost_kept_at_wb_trans) >>
     qpat_assum `stmt_state_rel H ctx func cenv cx es s0` (irule_at Any) >>
     qpat_assum `ghost_kept_at lo cenv mid ss G1 tn1 t G2 tn2` (irule_at Any) >>
     qpat_assum `wb_frame cenv es mid sa s0 t` (irule_at Any) >> fs[ci_mono_def]) >>
  `!n b sz. local_region cenv mid.scopes t n b sz <=> local_region cenv ee.scopes u n b sz` by
    (irule (INST_TYPE [alpha |-> ``:256``] wb_frame_local_regions) >>
     qpat_assum `stmt_state_rel H ctx func cenv cx mid t` (irule_at Any) >>
     qpat_assum `wb_frame cenv mid ee ss t u` (irule_at Any) >> simp[]) >>
  `~copy ==> ee.scopes = mid.scopes /\ ee.immutables = mid.immutables /\
     !tr. get_storage cx ee tr = get_storage cx mid tr` by
    (strip_tac >>
     `EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_exprs xs)` by
       (simp[bodyStorageCasesTheory.body_exprs_main_calls_every,EVERY_MEM] >> rpt strip_tac >>
        `expr_body_pre cenv cx env e' mid` by metis_tac[] >>
        drule_all_then assume_tac body_inv_expr_pre_calls >> fs[EVERY_MEM] >> res_tac) >>
     `~exprs_can_mutate cenv xs` by (qpat_assum `copy <=> _` mp_tac >> simp[]) >>
     drule_all targetPureWalkSourceTheory.nonmutating_exprs_source_frame >>
     simp[vyperMachineFrameTheory.machine_frame_def] >> strip_tac >> gen_tac >>
     Cases_on `tr` >> simp[vyperStorageBackendTheory.get_storage_def]) >>
  suspend "transport"
QED

Resume create_ctor_rows_post_cons[transport]:
  `!tag p. sv = LocatedValue tag p ==> tag = lowered_value_type cenv e /\
      ~is_word_type (lowered_value_type cenv e)` by
    (qpat_assum `(?tag op. sv = StackValue tag op) \/ _` mp_tac >> Cases_on `sv` >> dsimp[]) >>
  `vv_type (ext_call_arg_value (lowered_value_type cenv e) vv) = lowered_value_type cenv e` by
    (drule_all create_ctor_snapshot_retag >> simp[]) >>
  `(?raw. read_result cx raw ee = (INL v,ee) /\
      vv_holds cenv cx (lowered_value_type cenv e) raw sv ee u /\
      vv_at cenv cx (lowered_value_type cenv e) sa ss ee raw sv u /\
      ptr_vv_ok cx (lowered_value_type cenv e) raw sv ee G2 tn2 u /\
      vv_store_bound cx (lowered_value_type cenv e) (lowered_value_type cenv e) ee raw sv u) /\
    vv_storage_live H cx sv ee u /\
    ((case sv of StackValue _ _ => ~is_word_type (lowered_value_type cenv e)
                | LocatedValue _ p => p.ptr_location = LocMemory) ==>
      ptr_buf_ok cenv e (vv_operand sv) G2 u)` by
    (mp_tac (Q.INST [`si` |-> `sa`, `D` |-> `DF H`] create_ctor_saved_row_suffix) >>
     impl_tac >- (simp[] >> rpt conj_tac
       >- (rule_assum_tac (REWRITE_RULE [ci_mono_def]) >>
           rpt (qpat_x_assum `cs_extends _ _ /\ _ /\ _`
             (map_every assume_tac o CONJUNCTS)) >> first_assum ACCEPT_TAC)
       >- (qexists_tac `raw` >> simp[])
       >- (strip_tac >> `copy` by (qpat_assum `copy <=> _` mp_tac >> simp[]) >>
           qpat_assum `copy /\ _ ==> ?x w tv. _`
             (drule_all_then (qx_choosel_then [`x`,`w`,`tv`] strip_assume_tac)) >>
           qexistsl_tac [`x`,`w`,`tv`] >> simp[] >>
           qpat_assum `!n b len. local_region cenv mid.scopes t n b len <=> _`
             (fn eq => qpat_assum `!n b len. local_region cenv mid.scopes t n b len ==> _`
               (ACCEPT_TAC o REWRITE_RULE [eq]))) >>
       rpt strip_tac >> `~copy` by (qpat_assum `copy <=> _` mp_tac >> simp[]) >>
       res_tac >> simp[]) >> simp[]) >>
  qpat_assum `wb_frame cenv es ee sa s0 u`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [wb_frame_def]) >>
  `!x. vv_operand sv = Var x ==> not_fresh_at ss x` by
    (rpt strip_tac >> irule bodyFullExtCallSavedOperandTheory.extcall_saved_operand_not_fresh >>
     qpat_assum `compile_snapshot_vv _ _ _ sm = _` (irule_at Any) >>
     qpat_assum `compile_expr cenv _ e sa = _` (irule_at Any) >> simp[]) >>
  `(!x. vv_operand sv = Var x ==> not_fresh_at sc x) /\
    s0.vs_alloca_next <= u.vs_alloca_next /\ MAP FDOM ee.scopes = MAP FDOM es.scopes` by
    (conj_tac
     >- (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `ss` >>
         fs[ci_mono_def] >> metis_tac[bodyFullExtCallSavedOperandTheory.extcall_saved_operand_not_fresh]) >>
     fs[]) >>
  suspend "pack"
QED

Resume create_ctor_rows_post_cons[pack]:
  `(copy /\ ~is_word_type (lowered_value_type cenv e) ==>
    ?p w tv. vv_location sv = SOME LocMemory /\ vv_operand sv = Var p /\
      eval_operand (vv_operand sv) u = SOME w /\
      evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv /\
      val_wf tv v /\ FLOOKUP u.vs_allocas sm.cs_next_id = SOME (w2n w,type_memory_size tv) /\
      sm.cs_next_id < ss.cs_next_id /\
      (!n b sz. local_region cenv ee.scopes u n b sz ==>
        regions_disjoint (w2n w) (type_memory_size tv) b sz))` by
    (strip_tac >>
     qpat_assum `copy /\ _ ==> ?x w tv. _`
       (drule_all_then (qx_choosel_then [`x`,`w`,`tv`] (map_every assume_tac o CONJUNCTS))) >>
     `lookup_var x t = SOME w` by
       (qpat_assum `vv_operand sv = Var x` (fn th =>
          qpat_assum `eval_operand (vv_operand sv) t = SOME w`
            (mp_tac o REWRITE_RULE [th,venomStateTheory.eval_operand_def])) >> simp[]) >>
     `lookup_var x u = SOME w` by
       (qpat_assum `!x w. not_fresh_at ss x /\ lookup_var x t = SOME w ==> _`
         (qspecl_then [`x`,`w`] mp_tac) >>
        simp[]) >>
     `!n b sz. local_region cenv ee.scopes u n b sz ==>
        regions_disjoint (w2n w) (type_memory_size tv) b sz` by
       (qpat_assum `!n b sz. local_region cenv mid.scopes t n b sz <=> _`
          (fn eq => qpat_assum `!n b sz. local_region cenv mid.scopes t n b sz ==> _`
            (ACCEPT_TAC o REWRITE_RULE [eq]))) >>
     qexistsl_tac [`x`,`w`,`tv`] >> simp[venomStateTheory.eval_operand_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `(cenv.ce_is_ctor /\ vv_location sv = SOME LocCode ==>
      !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
        eval_operand (vv_operand sv) u = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        !mem. mem_agree_outside tn2.t_mem u.vs_memory mem ==>
          val_in_memory rt v (w2n w) mem)` by
    (namedCases_on `sv` ["tag op","tag p"] >> simp[vv_location_def,vv_operand_def] >>
     strip_tac >> `tag = lowered_value_type cenv e /\ ~is_word_type (lowered_value_type cenv e)` by simp[] >>
     qpat_x_assum `tag = _` SUBST_ALL_TAC >>
     `~copy` by
       (strip_tac >> qpat_assum `copy /\ _ ==> ?x w tv. _` mp_tac >> simp[vv_location_def]) >>
     `ee.immutables = mid.immutables` by simp[] >>
     `!rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
       eval_operand p.ptr_operand u = SOME w ==>
       w2n w + type_memory_size rt <= lo /\
       !mem. mem_agree_outside tn2.t_mem u.vs_memory mem ==>
         val_in_memory rt v (w2n w) mem` suffices_by simp[arithmeticTheory.ADD_COMM] >>
     qpat_assum `stmt_state_rel H ctx func cenv cx ee u`
       (mp_then Any mp_tac bodyFullExtCallPosTransportTheory.extcall_request_saved_ctor_read) >>
     disch_then (qspecl_then [`v`,`lowered_value_type cenv e`,`tops`,`tn2`,`p`,`lo`,
                              `env`,`mid`,`d`,`G2`,`DF H`] mp_tac) >>
     simp[] >> `?raw. read_result cx raw ee = (INL v,ee) /\
                    vv_holds cenv cx (lowered_value_type cenv e) raw
                      (LocatedValue (lowered_value_type cenv e) p) ee u` by
        (qexists_tac `raw'` >> simp[]) >>
     disch_tac >> rpt gen_tac >> strip_tac >>
     first_x_assum (qspecl_then [`rt`,`w`] mp_tac) >> simp[] >>
     disch_then irule >> qexists_tac `raw'` >> simp[]) >>
  simp[ZIP] >>
  conj_tac
  >- (simp[create_ctor_saved_at_def] >> conj_tac
      >- (qpat_assum `ci_mono sm ss` (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
          qpat_assum `ci_mono ss sc` (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
          `sm.cs_next_var <= sc.cs_next_var /\ sm.cs_next_id <= sc.cs_next_id` by decide_tac >>
          qexistsl_tac [`sa`,`sm`,`ss`,`vv`,`raw'`,`copy`] >> simp[]) >>
      rpt conj_tac >> rpt strip_tac >>
      qpat_assum `sv = _` (fn th =>
        qpat_assum `_ ==> ptr_buf_ok cenv e (vv_operand sv) G2 u`
          (mp_tac o REWRITE_RULE [th,vv_operand_def])) >> simp[]) >>
  irule LIST_REL_mono >>
  qpat_assum `LIST_REL _ (ZIP (xs,tail_svs)) vs` (irule_at Any) >>
  simp[] >> metis_tac[create_ctor_saved_at_weaken_start]
QED
Finalise create_ctor_rows_post_cons

(* Mapping a returned tail list does not move the cursor, consume more
   gas observations or change any storage horizon. *)
Theorem create_ctor_rows_map_tail[local]:
  scoped_operand_outcome (DF,lo,E,ctx,func,PG) tops cx st0 a b
    (eval_exprs cx xs) (mid,t,G1,tn1) Q (create_operand_exit_post ctx cx) /\
  (!H exc ee G tn u. ~Q H (INR exc) ee G tn u) /\
  (!marks vs ee G2 tn2 u H.
    (!rest. eval_exprs cx xs
       (mid with gas_obs := gas_explicit marks t.vs_gas_readings ++ rest) =
       (INL vs,ee with gas_obs := rest)) /\
    valid_horizon cx st0 H ee.storage_trace /\
    Q H (INL vs) (ee with gas_obs := []) G2 tn2 u /\
    gas_origin_ptr_path (DF H,lo,E,ctx,func,PG) (t,G1,tn1) marks (OK u,G2,tn2) ==>
    P H (INL (v::vs)) (ee with gas_obs := []) G2 tn2 u) ==>
  scoped_operand_outcome (DF,lo,E,ctx,func,PG) tops cx st0 a b
    (bind (eval_exprs cx xs) (\vs. return (v::vs))) (mid,t,G1,tn1) P
    (create_operand_exit_post ctx cx)
Proof
  strip_tac >>
  `!e. bind (eval_exprs cx xs) (\vs. return (v::vs)) e =
      (SUM_MAP (CONS v) I (FST (eval_exprs cx xs e)),SND (eval_exprs cx xs e))` by
    (gen_tac >> Cases_on `eval_exprs cx xs e` >>
     rename1 `eval_exprs cx xs e = (res,ee)` >>
     Cases_on `res` >> simp[bind_def,return_def,sumTheory.SUM_MAP_def]) >>
  `ignore_bind (bind (eval_exprs cx xs) (\vs. return (v::vs))) (return ()) =
   ignore_bind (eval_exprs cx xs) (return ())` by
    (simp[FUN_EQ_THM,ignore_bind_def,bind_def] >> gen_tac >>
     Cases_on `eval_exprs cx xs x` >> rename1 `eval_exprs cx xs x = (rs,ee)` >>
     Cases_on `rs` >> simp[return_def]) >>
  qpat_x_assum `scoped_operand_outcome _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [scoped_operand_outcome_def]) >>
  rewrite_tac[scoped_operand_outcome_def] >> qexists_tac `marks`
  >- (disj1_tac >> simp[] >>
      fs[gasStorageTheory.gas_bad_storage_at_def] >> metis_tac[])
  >- (disj2_tac >> disj1_tac >>
      qexistsl_tac [`SUM_MAP (CONS v) I res`,`ee`,`r`,`G'`,`tn'`] >>
      simp[] >> rpt strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
        (drule_then strip_assume_tac) >> simp[] >>
      Cases_on `res` >> gvs[sumTheory.SUM_MAP_def,create_operand_exit_post_def,
                            stmtSimPropsTheory.expr_exit_INR_type,exprSimDefsTheory.halt_exit_def] >>
      metis_tac[]) >>
  disj2_tac >> disj2_tac >> asm_rewrite_tac[] >> metis_tac[]
QED

(* Widen only the reachable left spine. A numeric band alone need not
   characterize every instruction of an unrelated block in the function. *)
Theorem create_ctor_left_spine[local]:
  body_inv tops ctx cenv cx /\ MEM func ctx.ctx_functions /\
  fn_has_code a m func /\ create_cut_code {} a m /\
  cs_extends m b /\ create_layout a b /\ m.cs_next_id <= b.cs_next_id ==>
  !x y. RTC (create_marked_edge (create_prefix_step a m E ctx func)) x y ==>
    create_cut_region a m (FST x) ==>
    RTC (create_marked_edge (create_prefix_step a b E ctx func)) x y /\
    create_cut_region a m (FST y)
Proof
  strip_tac >>
  `cs_extends a m` by fs[create_cut_code_def] >>
  ho_match_mp_tac RTC_INDUCT >> simp[] >>
  simp[pairTheory.FORALL_PROD,create_marked_edge_def] >>
  rpt gen_tac >> strip_tac >> strip_tac >>
  rename1 `create_prefix_step a m E ctx func p chunk q` >>
  `~create_operand_at m p` by fs[create_prefix_step_def,create_operand_at_def] >>
  `~create_operand_at b p` by metis_tac[create_layout_left_stop] >>
  `create_prefix_step a b E ctx func p chunk q` by
    (fs[create_prefix_step_def,create_operand_at_def,frag_ids_def] >>
     metis_tac[LESS_TRANS,LESS_LESS_EQ_TRANS]) >>
  `create_cut_region a m q` by
    (qpat_assum `create_prefix_step a m E ctx func p chunk q`
       (strip_assume_tac o REWRITE_RULE [create_prefix_step_def]) >>
     metis_tac[operand_cut_region_edge]) >>
  qpat_assum `create_cut_region a m q ==> _` (drule_then strip_assume_tac) >>
  `create_marked_edge (create_prefix_step a b E ctx func) (p,p_2) (q,p_2')` by
    simp[create_marked_edge_def,PULL_EXISTS] >>
  metis_tac[cj 2 RTC_RULES]
QED

Theorem create_ctor_region_step_back[local]:
  create_cut_code {} x y /\ fn_has_code x y func /\ create_cut_region x y u /\
  ~create_operand_at y u /\ create_prefix_step a b E ctx func u chunk v ==>
  create_prefix_step x y E ctx func u chunk v
Proof
  simp[create_prefix_step_def,create_operand_at_def] >> strip_tac >>
  drule_all create_cut_region_rules >> strip_tac >> metis_tac[]
QED

Theorem create_ctor_scope_focus_lift[local]:
  create_cut_code {} x y /\ fn_has_code x y func /\
  (!left u. create_expr_prefix x y E ctx func s left u ==>
    create_expr_prefix a b E ctx func s left u /\ create_cut_region x y u /\
    (~create_operand_at y u ==> ~create_operand_at b u)) /\
  create_operand_focus_scope x y E ctx func s marks ==>
  create_operand_focus_scope a b E ctx func s marks
Proof
  simp[create_operand_focus_scope_def] >>
  disch_then (map_every strip_assume_tac o CONJUNCTS) >>
  rename1 `create_expr_prefix x y E ctx func s left u` >>
  qpat_assum `!left u. create_expr_prefix x y E ctx func s left u ==> _`
    (drule_then strip_assume_tac) >>
  qexistsl_tac [`left`,`u`,`pending`] >> simp[] >>
  disj2_tac >> conj_tac >- fs[create_operand_at_def] >>
  rpt strip_tac >>
  `~create_operand_at y u` by simp[create_operand_at_def] >>
  metis_tac[create_ctor_region_step_back]
QED

Theorem create_ctor_scope_terminal_lift[local]:
  (!left u. create_expr_prefix x y E ctx func s left u ==>
    create_expr_prefix a b E ctx func s left u /\
    (~create_operand_at y u ==> ~create_operand_at b u)) /\
  exit_result r /\ create_operand_full_scope x y E ctx func s marks r ==>
  create_operand_full_scope a b E ctx func s marks r
Proof
  Cases_on `r` >>
  simp[create_operand_full_scope_def,create_operand_at_def,exit_result_def] >>
  metis_tac[]
QED

Theorem create_ctor_right_spine[local]:
  a.cs_next_id <= m.cs_next_id /\ create_expr_prefix m b E ctx func u right t ==>
  create_expr_prefix a b E ctx func u right t
Proof
  strip_tac >> irule create_expr_prefix_mono >>
  first_assum (irule_at Any) >>
  simp[create_prefix_step_def,frag_ids_def] >> metis_tac[LESS_EQ_TRANS]
QED

Theorem create_ctor_scope_split[local]:
  body_inv tops ctx cenv cx /\ MEM func ctx.ctx_functions /\
  create_cut_code {} a m /\ create_cut_code {} m b /\
  fn_has_code a m func /\ fn_has_code m b func /\ create_layout a b /\
  create_operand_at a s ==>
  (!marks. create_operand_focus_scope a m E ctx func s marks ==>
           create_operand_focus_scope a b E ctx func s marks) /\
  (!marks r. exit_result r /\ create_operand_full_scope a m E ctx func s marks r ==>
             create_operand_full_scope a b E ctx func s marks r) /\
  (!left t right. create_operand_full_scope a m E ctx func s left (OK t) /\
                  create_operand_focus_scope m b E ctx func t right ==>
                  create_operand_focus_scope a b E ctx func s (left ++ right)) /\
  (!left t right r. create_operand_full_scope a m E ctx func s left (OK t) /\
                    create_operand_full_scope m b E ctx func t right r ==>
                    create_operand_full_scope a b E ctx func s (left ++ right) r)
Proof
  strip_tac >>
  `cs_extends a m /\ cs_extends m b /\ a.cs_next_id <= m.cs_next_id /\
   m.cs_next_id <= b.cs_next_id` by fs[create_cut_code_def] >>
  `create_cut_region a m s` by
    (metis_tac[create_cut_region_rules,create_operand_at_def]) >>
  `!left u. create_expr_prefix a m E ctx func s left u ==>
      create_expr_prefix a b E ctx func s left u /\ create_cut_region a m u /\
      (~create_operand_at m u ==> ~create_operand_at b u)` by
    (rpt gen_tac >> strip_tac >>
     `create_expr_prefix a b E ctx func s left u /\ create_cut_region a m u` by
       (fs[create_expr_prefix_marked] >> metis_tac[create_ctor_left_spine,pairTheory.FST]) >>
     metis_tac[create_layout_left_stop]) >>
  conj_tac >- metis_tac[create_ctor_scope_focus_lift] >>
  conj_tac >- metis_tac[create_ctor_scope_terminal_lift] >>
  simp[create_operand_full_scope_def] >> conj_tac
  >- (rpt strip_tac >>
      `create_operand_focus_scope a b E ctx func t right` suffices_by
        metis_tac[create_operand_focus_scope_prepend] >>
      irule create_ctor_scope_focus_lift >>
      qexistsl_tac [`m`,`b`] >> simp[] >> rpt strip_tac
      >- metis_tac[create_ctor_right_spine] >>
      irule create_expr_prefix_cut_region >> rpt (goal_assum (drule_at Any)) >>
      drule_all create_cut_region_rules >> simp[]) >>
  qx_genl_tac [`left`,`t`,`right`,`r`] >> Cases_on `r` >>
  simp[create_operand_full_scope_def] >> rpt strip_tac >>
  metis_tac[create_expr_prefix_append,create_ctor_right_spine,APPEND_ASSOC]
QED

Theorem create_ctor_read_storage_frame[local]:
  storage_trace_frame (bind (eval_expr cx e) (read_result cx))
Proof
  irule storage_trace_frame_bind_all >>
  simp[evaluate_storage_trace_frame,storage_trace_frame_read_result]
QED

Theorem create_ctor_rows_finish_normal[local]:
  body_inv tops ctx cenv cx /\ body_exprs_full_ok cx xs /\
  expr_body_pre cenv cx env e es /\ expr_sim_inv cenv cx env mid /\
  (!x st. MEM x xs /\ expr_sim_inv cenv cx env st ==> expr_body_pre cenv cx env x st) /\
  copy = exprs_can_mutate cenv xs /\
  compile_expr cenv (expr_type e) e sa = (vv,sm) /\
  compile_snapshot_vv cenv copy (ext_call_arg_value (lowered_value_type cenv e) vv) sm = (sv,ss) /\
  ci_mono sa sm /\ ci_mono sm ss /\ ci_mono sa ss /\ ci_mono ss sc /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv ss /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!rest. bind (eval_expr cx e) (read_result cx) (es with gas_obs := left ++ rest) =
          (INL v,mid with gas_obs := rest)) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    create_ctor_head_post (DF,lo,d,ctx,func) cenv cx e (es,sa,sm,ss,vv,sv,copy,s0,G0,tn0)
      H (INL v) mid G1 tn1 t) /\
  (!rest. eval_exprs cx xs (mid with gas_obs := right ++ rest) = (INL vs,ee with gas_obs := rest)) /\
  valid_horizon cx st0 H ee.storage_trace /\
  create_ctor_rows_post (DF,lo,d,ctx,func) cenv cx env (xs,tail_svs) (mid,ss,sc,t,G1,tn1)
    H (INL vs) (ee with gas_obs := []) G2 tn2 u /\
  gas_origin_ptr_path (DF H,lo,E,ctx,func,PG) (t,G1,tn1) marks (OK u,G2,tn2) ==>
  create_ctor_rows_post (DF,lo,d,ctx,func) cenv cx env (e::xs,sv::tail_svs) (es,sa,sc,s0,G0,tn0)
    H (INL (v::vs)) (ee with gas_obs := []) G2 tn2 u
Proof
  strip_tac >>
  qpat_assum `!rest. eval_exprs _ _ _ = _` (qspec_then `[]` (assume_tac o REWRITE_RULE [APPEND_NIL])) >>
  `valid_horizon cx st0 H mid.storage_trace` by
    (`valid_horizon cx st0 H (mid with gas_obs := right).storage_trace` suffices_by simp[] >>
     irule (INST_TYPE [alpha |-> ``:value list``] valid_horizon_frame) >>
     qexistsl_tac [`eval_exprs cx xs`,`INL vs`,`ee with gas_obs := []`] >> simp[evaluate_storage_trace_frame]) >>
  qpat_assum `!rest. bind _ _ _ = _` (qspec_then `[]` (assume_tac o REWRITE_RULE [APPEND_NIL])) >>
  `valid_horizon cx st0 H es.storage_trace` by
    (`valid_horizon cx st0 H (es with gas_obs := left).storage_trace` suffices_by simp[] >>
     irule (INST_TYPE [alpha |-> ``:value``] valid_horizon_frame) >>
     qexistsl_tac [`bind (eval_expr cx e) (read_result cx)`,`INL v`,`mid with gas_obs := []`] >>
     simp[create_ctor_read_storage_frame]) >>
  drule gasOriginPtrLabelsTheory.gas_origin_ptr_path_preserves_labels >> strip_tac >>
  qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _` (drule_then assume_tac) >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _` (drule_then assume_tac) >>
  irule create_ctor_rows_post_cons >>
  qpat_assum `create_ctor_rows_post _ _ _ _ (xs,tail_svs) _ _ _ _ _ _ _`
    (irule_at Any) >>
  qpat_assum `create_ctor_head_post _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `body_inv tops ctx cenv cx` (irule_at Any) >>
  qpat_assum `eval_exprs cx xs (mid with gas_obs := right) = _` (irule_at Any) >> simp[]
QED

Theorem create_ctor_rows_scoped_of_heads:
  !xs svs sa sc sha shc es s0 G0 tn0.
  body_const_cells_agree [(NONE,tops)] cx env es /\
  body_exprs_full_ok cx xs /\ body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\ expr_sim_inv cenv cx env es /\
  (!e st. MEM e xs /\ expr_sim_inv cenv cx env st ==> expr_body_pre cenv cx env e st) /\
  compile_create_ctor_args compile_expr cenv xs sa = (svs,sc) /\
  compile_create_ctor_args compile_expr (gas_shadow_env T cenv) (MAP gas_shadow_expr xs)
    sha = (svs,shc) /\
  gas_shadow_state sa sha /\ gas_shadow_state sc shc /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sc func /\ fn_has_code sha shc shadow_func /\ create_layout sa sc /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!fn inst z. frag_reachable ctx func s0 fn inst z ==> dalloca_fmp_headroom inst z) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ create_operand_at sa s0 /\
  create_ctor_scoped_head (DF,lo,d,ctx,shadow_ctx,func,shadow_func,PG) tops cenv cx env xs
    (\e copy. is_word_type (lowered_value_type cenv e)) /\
  create_ctor_scoped_head (DF,lo,d,ctx,shadow_ctx,func,shadow_func,PG) tops cenv cx env xs
    (\e copy. ~is_word_type (lowered_value_type cenv e) /\ ~copy) /\
  create_ctor_scoped_head (DF,lo,d,ctx,shadow_ctx,func,shadow_func,PG) tops cenv cx env xs
    (\e copy. ~is_word_type (lowered_value_type cenv e) /\ copy) /\
  create_ctor_mixed_bind_law DF lo (gas_explicit_sites ctx shadow_ctx) ctx func PG (cx_tops cx) cx st0 ==>
  scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 sa sc (eval_exprs cx xs) (es,s0,G0,tn0)
    (create_ctor_rows_post (DF,lo,d,ctx,func) cenv cx env (xs,svs) (es,sa,sc,s0,G0,tn0))
    (create_operand_exit_post ctx cx)
Proof
  Induct_on `xs`
  >- (simp[compile_create_ctor_args_def,comp_return_def] >> rpt strip_tac >>
      irule create_ctor_rows_scoped_nil >> simp[]) >>
  qx_genl_tac [`e`,`svs`,`sa`,`sc`,`sha`,`shc`,`es`,`s0`,`G0`,`tn0`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_body_pre cenv cx env e es` by (first_x_assum irule >> simp[]) >>
  `body_expr_full_ok cx e` by fs[Once body_exprs_full_ok_def] >>
  drule_all_then (qx_choosel_then [`vv`,`sm`,`shm`,`sv`,`ss`,`shs`,`tail_svs`]
    (map_every assume_tac o CONJUNCTS)) create_ctor_scope_compile_cons >>
  qpat_x_assum `svs = _` SUBST_ALL_TAC >>
  qabbrev_tac `copy = exprs_can_mutate cenv xs` >>
  `ci_mono sa sm /\ ci_mono sha shm` by
    (conj_tac
     >- (qspecl_then [`cenv`,`expr_type e`,`e`,`sa`] mp_tac (cj 1 ci_mono_compile_expr_sa) >> simp[]) >>
     qspecl_then [`gas_shadow_env T cenv`,`expr_type e`,`gas_shadow_expr e`,`sha`] mp_tac
       (cj 1 ci_mono_compile_expr_sa) >> simp[]) >>
  `ci_mono sm ss /\ ci_mono shm shs` by
    (qmatch_asmsub_abbrev_tac `compile_snapshot_vv cenv copy arg sm` >>
     conj_tac
     >- (qspecl_then [`cenv`,`copy`,`arg`,`sm`] mp_tac ci_mono_compile_snapshot_vv >> simp[]) >>
     qspecl_then [`cenv`,`copy`,`arg`,`shm`] mp_tac ci_mono_compile_snapshot_vv >> simp[]) >>
  `ci_mono sa ss /\ ci_mono sha shs` by metis_tac[ci_mono_trans] >>
  `ci_mono ss sc /\ ci_mono shs shc` by
    (qspec_then `compile_expr` mp_tac ci_mono_compile_create_ctor_args >>
     disch_then (fn th => conj_tac
       >- (qspecl_then [`cenv`,`xs`,`ss`] mp_tac th >> simp[ci_mono_compile_expr_sa]) >>
       qspecl_then [`gas_shadow_env T cenv`,`MAP gas_shadow_expr xs`,`shs`] mp_tac th >>
       simp[ci_mono_compile_expr_sa])) >>
  `fn_has_code sa ss func /\ fn_has_code ss sc func` by
    metis_tac[fn_has_code_split,ci_mono_def] >>
  `fn_has_code sha shs shadow_func /\ fn_has_code shs shc shadow_func` by
    metis_tac[fn_has_code_split,ci_mono_def] >>
  `create_layout ss sc` by
    metis_tac[create_layout_subinterval,cs_extends_refl,ci_mono_def] >>
  `create_cut_code {} sa ss` by
    (irule create_cut_code_join >> qexists_tac `sm` >> conj_tac
     >- (qspecl_then [`cenv`,`expr_type e`,`e`,`sa`] mp_tac (cj 1 create_operand_cut_code) >> simp[]) >>
     qmatch_asmsub_abbrev_tac `compile_snapshot_vv cenv copy arg sm` >>
     mp_tac (Q.INST [`ce` |-> `cenv`,`vv` |-> `arg`,`a` |-> `sm`] create_vv_snapshot_cut_code) >> simp[]) >>
  `create_cut_code {} ss sc` by
    (qspec_then `compile_expr` mp_tac (GEN_ALL create_ctor_args_cut) >>
     simp[create_operand_cut_code,create_vv_snapshot_cut_code] >>
     disch_then (qspecl_then [`cenv`,`xs`,`ss`] mp_tac) >> simp[]) >>
  `local_ptrs_reserved cenv ss` by metis_tac[ci_mono_def,local_ptrs_reserved_next_var] >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ss x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ss x)` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> fs[ci_mono_def]) >>
  qabbrev_tac `headQ = create_ctor_head_post (DF,lo,d,ctx,func) cenv cx e
    (es,sa,sm,ss,vv,sv,copy,s0,G0,tn0)` >>
  `scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 sa ss (bind (eval_expr cx e) (read_result cx))
    (es,s0,G0,tn0) headQ (create_operand_exit_post ctx cx)` by
    (simp[Abbr `headQ`] >>
     Cases_on `is_word_type (lowered_value_type cenv e)`
     >- (qpat_assum `create_ctor_scoped_head _ _ _ _ _ _ (\e copy. is_word_type _)`
           (irule o REWRITE_RULE [create_ctor_scoped_head_def]) >>
         simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
         qexistsl_tac [`sha`,`shm`,`shs`] >> simp[]) >>
     Cases_on `copy`
     >- (qpat_assum `create_ctor_scoped_head _ _ _ _ _ _ (\e copy. ~is_word_type _ /\ copy)`
           (irule o REWRITE_RULE [create_ctor_scoped_head_def]) >>
         simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
         qexistsl_tac [`sha`,`shm`,`shs`] >> simp[]) >>
     qpat_assum `create_ctor_scoped_head _ _ _ _ _ _ (\e copy. ~is_word_type _ /\ ~copy)`
       (irule o REWRITE_RULE [create_ctor_scoped_head_def]) >>
     simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
         qexistsl_tac [`sha`,`shm`,`shs`] >> simp[]) >>
  rewrite_tac[eval_exprs_cons_action] >>
  qpat_assum `create_ctor_mixed_bind_law _ _ _ _ _ _ _ _ _`
    (irule o REWRITE_RULE [create_ctor_mixed_bind_law_def]) >>
  rpt conj_tac
  >- (rpt strip_tac >> pure_rewrite_tac[ignore_bind_def] >> once_rewrite_tac[bind_assoc] >>
      irule gas_exempt_cert_error_value >> simp[])
  >- (rpt strip_tac >> pure_rewrite_tac[ignore_bind_def] >> once_rewrite_tac[bind_assoc] >>
      irule gas_exempt_cert_bind_value >> qexistsl_tac [`mid`,`t`,`v`] >>
      fs[ignore_bind_def])
  >- (gen_tac >> BETA_TAC >> irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame,storage_trace_frame_return])
  >- simp[create_ctor_read_storage_frame] >>
  qexistsl_tac [`headQ`,`ss`] >>
  mp_tac (Q.INST [`a` |-> `sa`,`m` |-> `ss`,`b` |-> `sc`,`s` |-> `s0`,
                  `E` |-> `gas_explicit_sites ctx shadow_ctx`] create_ctor_scope_split) >>
  (impl_tac >- simp[]) >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt conj_tac >>
  TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (irule create_ctor_scoped_head_error >> simp[] >> NO_TAC) >>
  qx_genl_tac [`left_marks`,`res`,`mid`,`G1`,`tn1`,`t`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qunabbrev_tac `headQ` >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  reverse (Cases_on `res`)
  >- gvs[create_ctor_head_post_def] >>
  qmatch_goalsub_rename_tac `INL (v:value) = _` >> qexists_tac `v` >> simp[] >>
  qpat_assum `!H. _ ==> create_ctor_head_post _ _ _ _ _ H (INL _) _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace`
       (drule_then (assume_tac o CONJUNCT2))) >>
  `body_const_cells_agree [(NONE,tops)] cx env mid /\
   expr_sim_inv cenv cx env mid /\ body_exprs_full_ok cx xs` by
    (irule create_ctor_rows_source_advance >>
     qexistsl_tac [`e`,`es`,`gas_explicit left_marks s0.vs_gas_readings`,`v`] >> simp[]) >>
  `!fn inst z. frag_reachable ctx func t fn inst z ==> dalloca_fmp_headroom inst z` by
    (`!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
       metis_tac[bodyFullIfExpReachTheory.body_inv_no_phi] >>
     qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) left_marks (OK t,G1,tn1)`
       (mp_then Any mp_tac bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom) >>
     simp[] >> metis_tac[]) >>
  `return_buf_frame d cenv ss t /\ alloca_history func t /\ ~t.vs_halted` by
    (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
       (qspec_then `storage_trace_horizon mid.storage_trace`
          (drule_then (strip_assume_tac o REWRITE_RULE [create_ctor_head_post_def]))) >> simp[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid t /\
    storage_well_formed_on cx mid (FST H) /\ ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
       (qspec_then `H` (drule_then (strip_assume_tac o REWRITE_RULE [create_ctor_head_post_def]))) >>
     simp[]) >>
  `scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 ss sc (eval_exprs cx xs) (mid,t,G1,tn1)
    (create_ctor_rows_post (DF,lo,d,ctx,func) cenv cx env (xs,tail_svs) (mid,ss,sc,t,G1,tn1))
    (create_operand_exit_post ctx cx)` by
    (qpat_assum `!svs sa sc sha shc es s0 G0 tn0. _ ==>
        scoped_operand_outcome _ _ _ _ _ _ (eval_exprs cx xs) _ _ _` irule >>
     simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (qexistsl_tac [`shs`,`shc`] >> simp[]) >>
     rpt conj_tac >> irule create_ctor_scoped_head_subset >> qexists_tac `e::xs` >> simp[]) >>
  irule create_ctor_rows_map_tail >>
  qpat_assum `scoped_operand_outcome _ _ _ _ _ _ (eval_exprs cx xs) _ _ _` (irule_at Any) >>
  reverse conj_tac >- simp[create_ctor_rows_post_def] >>
  qx_genl_tac [`right_marks`,`vs`,`ee`,`G2`,`tn2`,`u`,`H`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule create_ctor_rows_finish_normal >>
  qpat_assum `create_ctor_rows_post _ _ _ _ (xs,tail_svs) _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `gas_origin_ptr_path _ (t,G1,tn1) right_marks (OK u,G2,tn2)` (irule_at Any) >>
  qpat_assum `valid_horizon cx st0 H ee.storage_trace` (irule_at Any) >>
  qpat_assum `body_inv tops ctx cenv cx` (irule_at Any) >>
  simp[Abbr `copy`] >>
  qexistsl_tac [`gas_explicit right_marks t.vs_gas_readings`,
                `gas_explicit left_marks s0.vs_gas_readings`] >> simp[]
QED

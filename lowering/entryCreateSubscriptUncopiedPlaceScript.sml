(* Scope the physical selector chosen at the post-index live-place landing. *)
Theory entryCreateSubscriptUncopiedPlace
Ancestors
  entryCreateSubscriptArrayRun entryCreateSubscriptUncopiedMemory
  bodyFullSubscriptLiveSlotSelect bodyFullSubscriptLiveImmSelect
  bodyFullSubscriptSlotRun bodyFullSubscriptLiveLanding arrayAbortItinerary
  entryCreateFocusSpec fragGasOriginPtr exprSimSubscriptArraySource
  exprSimSubscriptArrayCompose exprSimSubscriptArrayFramed exprReasonOperand exprSimCopy
  bodyFullPreds exprSimHypsDefs exprSimSource vyperTypeConstantFold
  vyperTypeSystem context compileEnv exprLoweringProps exprOperandVar
  loweringPosts bodyPtrDefs fragExec gasExplicitSites vyperStorageFootprint
  vyperState vyperAST

Theorem selector_itinerary_raw_abort[local]:
  array_abort_itinerary code fn s err raw t ==>
  run_inst_seq code s = Abort err raw
Proof
  rw[array_abort_itinerary_def] >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
  drule run_inst_seq_append >> disch_then (fn th => rewrite_tac[th]) >>
  simp[run_inst_seq_def]
QED

Theorem live_selector_length_code[local]:
  (if dyn then compile_ptr_load ctor imm loc bop
   else comp_return (Lit (n2w cnt))) sn = (len,sl) ==>
  array_selector_code sn sl
Proof
  Cases_on `dyn` >> simp[comp_return_def] >> metis_tac[array_length_selector_code]
QED

Theorem live_selector_oob_scope[local]:
  array_selector_code sn sl /\ array_selector_code sl sc /\
  array_selector_code sc sb /\ fn_has_code sn sb fn /\ create_operand_at sn u /\
  run_inst_seq (emitted_insts sn sl) u = OK raw /\
  ul = (raw with vs_inst_idx := LENGTH sl.cs_current_insts) /\
  array_abort_itinerary (emitted_insts sl sc) fn ul Revert_abort aborted q /\
  gas_origin_ptr_path (D,lo,E,C,fn,PG) (u,G,tn) [] (OK ul,Gl,tl) /\
  gas_origin_ptr_path (D,lo,E,C,fn,PG) (ul,Gl,tl) [] (Abort Revert_abort q,Gq,tq) ==>
  create_operand_full_scope sn sb E C fn u [] (Abort Revert_abort q)
Proof
  strip_tac >>
  drule selector_itinerary_raw_abort >> strip_tac >>
  imp_res_tac gas_origin_ptr_path_projections >> gvs[] >>
  irule array_selector_oob_scope_itinerary >>
  first_assum (irule_at Any) >>
  goal_assum (drule_at Any) >> qexistsl [`aborted`,`sc`] >> simp[]
QED

Theorem live_select_landing_scoped[local]:
  live_select_landing (DF,lo,E,C,f,PG) cx st0 source (fin,s,G,tn) Q R
    (create_operand_full_scope sn sb E C f s []) ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 sn sb
    source (fin,s,G,tn) Q R
Proof
  rw[live_select_landing_def] >> irule nocopy_selector_scoped_landing >>
  first_assum (irule_at Any) >> qexistsl [`tn'`,`res`,`r`,`G'`] >> simp[]
QED

(* Interpret the runner's observation before forgetting its itinerary. *)
Theorem live_slot_selector_scoped_run[local]:
  compile_array_subscript bop iop dyn cnt 1 (type_slot_size etv) sgn
    (compile_ptr_load ctor imm (slot_loc tr)) sn = (dst,sb) /\
  fn_has_code sn sb fn /\
  eval_operand bop u = SOME slot /\ eval_operand iop u = SOME iw /\
  nw = (if dyn then (if tr then tload slot u else sload slot u) else n2w cnt) /\
  op_taint tn bop = {} /\ op_taint tn iop = {} /\ op_prov G iop = NONE /\
  (dyn ==> key_taint (if tr then tn.t_trans else tn.t_stor) slot = {}) /\
  (!x. bop = Var x ==> not_fresh_at sn x) /\
  (!x. iop = Var x ==> not_fresh_at sn x) /\
  allocas_from lo u /\ alloca_history fn u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  ~u.vs_halted /\ u.vs_current_bb = sn.cs_current_bb /\
  u.vs_inst_idx = LENGTH sn.cs_current_insts ==>
  ?q H tm.
    create_operand_full_scope sn sb explicit ctx fn u []
      (if idx_in_range sgn iw nw then OK q else Abort Revert_abort q) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (u,G,tn) []
      (if idx_in_range sgn iw nw then OK q else Abort Revert_abort q,H,tm)) /\
    (idx_in_range sgn iw nw ==>
      ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
      q.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history fn q /\
      eval_operand dst q = SOME
        ((if dyn then slot + 1w else slot) + iw * n2w (type_slot_size etv)) /\
      op_prov H dst = op_prov G bop /\ op_taint tm dst = {} /\
      array_length_frame sn u G tn q H tm)
Proof
  strip_tac >> drule_all subscript_slot_array_execution_run >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  `create_operand_at sn u` by simp[create_operand_at_def] >>
  drule_then assume_tac live_selector_length_code >>
  drule_then assume_tac array_bounds_selector_code >>
  drule_then assume_tac array_elem_selector_code >>
  qexistsl [`q`,`H`,`tm`] >> simp[] >>
  Cases_on `idx_in_range sgn iw nw` >> gvs[]
  >- (irule array_selector_ok_scope_itinerary >> simp[] >>
      qexistsl [`sl`,`sc`,`checked`,`raw`] >> simp[]) >>
  irule live_selector_oob_scope >>
  first_assum (irule_at Any) >>
  goal_assum (drule_at Any) >>
  metis_tac[]
QED

Theorem live_imm_selector_scoped_run[local]:
  compile_array_subscript arg idx dyn (if dyn then 0 else cnt) 32 esz sgn
    (compile_ptr_load ctor imm LocCode) sa = (dst,sb) /\
  fn_has_code sa sb func /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  eval_operand arg s = SOME a /\ copy_old_operand sa arg /\
  op_taint tn arg = {} /\ op_prov G arg = NONE /\
  eval_operand idx s = SOME (n2w i) /\ copy_old_operand sa idx /\
  op_taint tn idx = {} /\ op_prov G idx = NONE /\
  (!l. arg <> Label l /\ idx <> Label l) /\
  (dyn ==> immutable_copy_read ctor a s = n2w cnt /\
    (ctor ==> w2n a + 32 <= lo /\ mem_word_taint tn.t_mem (w2n a) = {} /\
      (!region. imm = SOME region ==> eval_operand region s = SOME 0w /\
         copy_old_operand sa region /\ op_taint tn region = {} /\ op_prov G region = NONE)) /\
    (~ctor ==> w2n a <= LENGTH s.vs_data_section)) ==>
  ?Gf tnf q.
    create_operand_full_scope sa sb explicit ctx func s []
      (if idx_in_range sgn (n2w i) (n2w cnt) then OK q else Abort Revert_abort q) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      ((if idx_in_range sgn (n2w i) (n2w cnt) then OK q else Abort Revert_abort q),Gf,tnf)) /\
    q.vs_immutables = s.vs_immutables /\ q.vs_memory = s.vs_memory /\
    q.vs_allocas = s.vs_allocas /\ q.vs_alloca_next = s.vs_alloca_next /\
    q.vs_fmp = s.vs_fmp /\ q.vs_accounts = s.vs_accounts /\
    q.vs_transient = s.vs_transient /\ q.vs_call_ctx = s.vs_call_ctx /\
    q.vs_requests = s.vs_requests /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!v. not_fresh_at sa v ==> lookup_var v q = lookup_var v s /\
      FLOOKUP Gf v = FLOOKUP G v /\ op_taint tnf (Var v) = op_taint tn (Var v)) /\
    (idx_in_range sgn (n2w i) (n2w cnt) ==>
      q.vs_current_bb = sb.cs_current_bb /\ q.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~q.vs_halted /\
      eval_operand dst q = SOME (a + n2w ((if dyn then 32 else 0) + i * esz)) /\
      op_taint tnf dst = {} /\ op_prov Gf dst = NONE /\
      !(H:(bool # bytes32 # type_value) list # num list) cenv cx es.
        stmt_state_rel H ctx func cenv cx es s /\ local_ptrs_reserved cenv sa ==>
        stmt_state_rel H ctx func cenv cx es q)
Proof
  strip_tac >> drule_all live_code_select_joint_run >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  `create_operand_at sa s` by simp[create_operand_at_def] >>
  drule_then assume_tac (SIMP_RULE (srw_ss()) [compile_ptr_load_def]
    (Q.INST [`loc` |-> `LocCode`] live_selector_length_code)) >>
  drule_then assume_tac array_bounds_selector_code >>
  drule_then assume_tac array_elem_selector_code >>
  qexistsl [`Gf`,`tnf`,`q`] >> simp[] >>
  Cases_on `idx_in_range sgn (n2w i) (n2w cnt)` >> gvs[]
  >- (gvs[bodyFullSubscriptArrayCodeBoundsTheory.array_bounds_native_run_def] >>
      irule array_selector_ok_scope_itinerary >> simp[] >>
      qexistsl [`sh`,`sk`,`u`,`rawh`] >> simp[]) >>
  irule live_selector_oob_scope >>
  first_assum (irule_at Any) >>
  goal_assum (drule_at Any) >>
  metis_tac[]
QED

(* The ordinary producer puts the cursor inside the result existential. *)
Theorem live_select_landing_scoped_vv[local]:
  live_select_landing (DF,lo,E,ctx,func,PG) cx st0 source (fin,u,Gi,tni)
    (\H res ee G tn t. ?tv. res = INL tv /\
      vv_post H ctx func cenv cx e es sa sb s0 ee tv vv t /\
      vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee tv vv t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\ ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn t /\
      (!v. tv = Value v /\ ~is_word_type (post_value_type cenv e) /\
        ~is_bytestring_type (post_value_type cenv e) ==>
        vv_own cenv cx (post_value_type cenv e) sa sb ee tv vv t /\
        (!t' p. vv = LocatedValue t' p ==> p.ptr_location = LocMemory)) /\
      (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
        ?val. read_result cx tv ee = (INL val,ee) /\
          !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
                 eval_operand (vv_operand vv) t = SOME w ==>
                 w2n w + type_memory_size rt <= lo /\
                 (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
                        val_in_memory rt val (w2n w) mem)) /\
      (!t' op. vv = StackValue t' op /\ ~is_word_type (post_value_type cenv e) ==>
        ptr_buf_ok cenv e op G t) /\
      (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
        ptr_buf_ok cenv e p.ptr_operand G t) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
    (create_operand_full_scope sn sb E ctx func u []) ==>
  scoped_operand_outcome (DF,lo,E,ctx,func,PG) tops cx st0 sn sb source (fin,u,Gi,tni)
    (\H res ee G tn t.
      create_operand_vv_post (DF,lo,d,ctx,func) cenv cx e (es,sa,sb,s0,vv,G0,tn0)
        H res ee G tn t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts)
    (create_operand_exit_post ctx cx)
Proof
  rw[live_select_landing_def] >> irule live_select_landing_scoped >>
  rw[live_select_landing_def] >>
  qexistsl [`r`,`G'`,`tn'`] >> simp[] >>
  gen_tac >> strip_tac >> first_x_assum (drule_then strip_assume_tac) >>
  simp[create_operand_vv_post_def, create_operand_exit_post_def] >>
  qexists_tac `t` >> simp[] >> qexists_tac `tv` >> simp[]
QED

(* Continue from the actual post-index state, not from the earlier base cut. *)
Theorem nocopy_live_place_select_at:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (Subscript ann obj idx) es /\
  expr_type obj = ArrayT et bd /\ place_type cenv obj = ValPT (ArrayT et bd) /\
  post_value_type cenv obj = expr_type obj /\ ~subscript_reads_base cx obj idx /\
  ((?tr slot vt. raw = PlaceR (StoragePlace tr slot vt)) \/
   (?src id path. raw = PlaceR (ImmutablePlace src id path))) /\
  compile_expr cenv ty obj sa = (bvv,sm) /\
  lower_value compile_expr cenv ty idx sm = (iop,sn) /\
  loc = (case vv_location bvv of SOME l => l | NONE => LocMemory) /\
  compile_array_subscript (vv_operand bvv) iop
    (case bd of Fixed _ => F | Dynamic _ => T)
    (case bd of Fixed n => n | Dynamic _ => 0)
    (word_scale loc) (elem_size_in_location cenv loc et)
    (is_signed_type (expr_type idx))
    (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc) sn = (dst,sb) /\
  fn_has_code sn sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\ local_ptrs_reserved cenv sn /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id <= sn.cs_next_id /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  eval_expr cx obj (es with gas_obs := gs1) = (INL raw,mid) /\
  bind (eval_expr cx idx) (read_result cx) (mid with gas_obs := gs2) = (INL key,fin) /\
  storage_trace_domain cx st0 fin.storage_trace /\ fin.gas_obs = [] /\
  ~it.vs_halted /\ create_operand_at sn it /\ alloca_history func it /\
  s0.vs_alloca_next <= s.vs_alloca_next /\ s.vs_alloca_next <= it.vs_alloca_next /\
  ptr_vv_ok cx (post_value_type cenv obj) raw bvv mid G1 tn1 s /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
  ptr_val_ok cx (post_value_type cenv idx) key iop Gi tni it /\
  ghost_kept_at lo cenv mid sm G1 tn1 s Gi tni /\
  (!H. valid_horizon cx st0 H fin.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    vv_post H ctx func cenv cx obj es sa sm s0 mid raw bvv s /\
    expr_post H ctx func cenv cx idx mid sm sn s fin key iop it /\
    ghost_inv_at (DF H) lo d cenv cx fin Gi tni it) ==>
  scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 sn sb (select_result cx (ArrayT et bd) raw (ValueSubscript key))
    (fin,it,Gi,tni)
    (\H res ee G tn t.
      create_operand_vv_post (DF,lo,d,ctx,func) cenv cx (Subscript ann obj idx)
        (es,sa,sb,s0,LocatedValue ann (mk_ptr dst loc),G0,tn0) H res ee G tn t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts)
    (create_operand_exit_post ctx cx)
Proof
  strip_tac >> qpat_x_assum `raw = PlaceR _` SUBST_ALL_TAC >>
  qpat_x_assum `create_operand_at _ _` (strip_assume_tac o
    REWRITE_RULE [create_operand_at_def]) >>
  irule live_select_landing_scoped_vv
  >- suspend "slot" >>
  suspend "immutable"
QED

Resume nocopy_live_place_select_at[slot]:
  irule (CONV_RULE (DEPTH_CONV ETA_CONV) (BETA_RULE
    (Q.INST [`observes` |-> `\a b u r. create_operand_full_scope a b
      (gas_explicit_sites ctx shadow_ctx) ctx func u [] r`]
      subscript_live_slot_select_observed))) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (qexists_tac `env` >> first_assum ACCEPT_TAC) >>
  qpat_assum `compile_expr _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `lower_value _ _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `eval_expr _ _ _ = _` (irule_at Any) >>
  qpat_assum `bind (eval_expr _ _) _ _ = _` (irule_at Any) >>
  qpat_assum `ptr_vv_ok _ _ _ _ _ _ _ _` (irule_at Any) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  rpt gen_tac >> MATCH_ACCEPT_TAC live_slot_selector_scoped_run
QED

Resume nocopy_live_place_select_at[immutable]:
  `expr_body_pre cenv cx env obj es` by
    (qpat_assum `expr_body_pre _ _ _ (Subscript _ _ _) _`
       (mp_then Any irule expr_body_pre_array_subscript_base_eval) >>
     qpat_assum `eval_expr cx obj _ = _` (irule_at Any) >> simp[]) >>
  `well_typed_expr env (Subscript ann obj idx) /\
   well_typed_expr env obj /\ well_typed_expr env idx` by
    fs[expr_body_pre_def, vyperTypeSystemTheory.well_typed_expr_def] >>
  `ann = et` by
    (drule_all vyperTypeConstantFoldTheory.constant_subscript_type_ok >>
     simp[vyperTypeSystemTheory.subscript_type_ok_def]) >>
  qpat_x_assum `ann = et` SUBST_ALL_TAC >>
  `valid_horizon cx st0 (storage_trace_horizon fin.storage_trace) fin.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  `vv_type bvv = ArrayT et bd` by
    (drule_all exprSimSubscriptArrayTheory.compile_array_vv_type >> simp[]) >>
  `?p. bvv = LocatedValue (ArrayT et bd) p /\ p.ptr_location = LocCode` by
    (qpat_assum `vv_post _ _ _ _ _ obj _ _ _ _ _ _ bvv s`
       (mp_tac o PURE_REWRITE_RULE [vv_post_def]) >>
     Cases_on `bvv` >> fs[vv_type_def, vv_at_def, vv_place_ptr_def, is_word_type_def]) >>
  qpat_x_assum `bvv = LocatedValue _ _` SUBST_ALL_TAC >>
  `loc = LocCode` by fs[vv_location_def] >>
  qpat_x_assum `loc = LocCode` SUBST_ALL_TAC >>
  `!id t. FLOOKUP env.var_types id = SOME t ==>
          ?q sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var q) sz)` by
    fs[expr_body_pre_def, expr_sim_inv_def] >>
  `!l. p.ptr_operand <> Label l` by
    (qpat_assum `compile_expr cenv ty obj sa = _`
       (mp_then Any mp_tac exprSimSubscriptArrayOriginTheory.compile_array_pointer_not_label) >>
     disch_then (qspecl_then [`et`,`env`,`bd`] mp_tac) >> simp[]) >>
  drule_all_then assume_tac lower_compile_expr_not_label >>
  `copy_old_operand sm p.ptr_operand` by
    (qpat_assum `compile_expr cenv ty obj sa = _`
       (mp_then Any mp_tac (CONJUNCT1 compiler_compile_var)) >>
     simp[vv_operand_def, copy_old_operand_def]) >>
  `copy_old_operand sn iop` by
    (qpat_assum `lower_value compile_expr cenv ty idx sm = _`
       (mp_then Any mp_tac compile_lower_value_var) >> simp[copy_old_operand_def]) >>
  irule (CONV_RULE (DEPTH_CONV ETA_CONV) (BETA_RULE
    (Q.INST [`certify` |-> `\a b u r. create_operand_full_scope a b explicit ctx func u [] r`]
      subscript_live_immutable_select_observed))) >>
  qpat_assum `body_inv _ _ _ _` (irule_at Any) >>
  qpat_assum `expr_body_pre _ _ _ (Subscript _ _ _) _` (irule_at Any) >>
  qpat_assum `eval_expr cx obj _ = _` (irule_at Any) >>
  qpat_assum `bind (eval_expr cx idx) _ _ = _` (irule_at Any) >>
  qpat_assum `ptr_vv_ok _ _ _ _ _ _ _ _` (irule_at Any) >>
  `s0.vs_alloca_next <= it.vs_alloca_next` by decide_tac >>
  qexistsl [`sm`,`iop`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (rpt gen_tac >> MATCH_ACCEPT_TAC live_imm_selector_scoped_run)
  >- (gen_tac >> strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> _`
        (drule_then (map_every assume_tac o CONJUNCTS)) >>
      simp[expr_post_initial_gas]) >>
  fs[word_scale_def, elem_size_in_location_def, is_slot_addressed_def, vv_operand_def]
QED

Finalise nocopy_live_place_select_at

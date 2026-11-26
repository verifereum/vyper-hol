(* Apply the stipulated Slice window run at the last reached operand cut. *)
Theory bodySliceOrdinaryTerminalOutcomeMods
Ancestors
  bodySliceOrdinaryWindowRebaseMods bodyFullPredsMods bodyForcedStorageFrameMods
  gasOutcomeFullPostMods exprSimSliceSource stateRelProj allocLimits
  vyperStorageFootprint vyperContext vyperState vyperAST words
  bodyFullHashKeccakFixed exprLoweringProps exprSimHypsDefs compileEnv loweringPosts exprLowering
Libs monadsyntax

val finish = ``\v v1 v2. do
  acc <- get_accounts;
  r <- lift_sum (evaluate_builtin cx acc ann (Slice n)
                  (MAP expr_type [src;start;len]) [v;v1;v2]);
  return (Value r)
  od``;

val exit_post = ``\(H:(bool # bytes32 # type_value) list # num list)
    (res:eval_result + vyperState$exception) ee
    (gt:(string |-> num # num) # taint) r.
  expr_exit res r /\ halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u)``;

val window_supplier = ``
  !limit root start cnt N sa out sb func cenv ctx s bs p G tn i k n a result
    e args cx st0 es DF lo d explicit mods source PG.
  compile_slice_data limit (Var root) start cnt N sa = (out,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size func s <= w2n s.vs_initial_fmp) /\
  eval_operand limit s = SOME (n2w (LENGTH bs)) /\
  lookup_var root s = SOME p /\ ptr_covers G tn root s (LENGTH bs) /\
  op_prov G limit = NONE /\ op_taint tn limit = {} /\
  eval_operand start s = SOME (n2w i) /\ eval_operand cnt s = SOME (n2w k) /\
  op_prov G start = NONE /\ op_taint tn start = {} /\
  op_prov G cnt = NONE /\ op_taint tn cnt = {} /\
  (!op x. MEM op [limit;Var root;start;cnt] /\ op = Var x ==>
     not_fresh_at sa x) /\
  (!l. limit <> Label l /\ start <> Label l /\ cnt <> Label l) /\
  mem_bytes_at (w2n p) (LENGTH bs) s.vs_memory = bs /\
  (!j. w2n p <= j /\ j < w2n p + LENGTH bs ==> j NOTIN tn.t_mem) /\
  w2n p + LENGTH bs < dimword (:256) /\ w2n p + LENGTH bs <= s.vs_alloca_next /\
  i < dimword (:256) /\ k < dimword (:256) /\ (i+k <= LENGTH bs ==> k <= n) /\
  ((a = BaseT (BytesT (Dynamic n)) /\ result = BytesV (TAKE k (DROP i bs))) \/
   (?str. a = BaseT (StringT n) /\ bs = MAP (n2w o ORD) str /\
      result = StringV (TAKE k (DROP i str)))) /\
  e = Builtin a (Slice n) args /\
  N = type_memory_bytes cenv a /\ 32+n <= N /\ N < dimword (:256) /\
  storage_trace_domain cx st0 es.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\
    immutable_frame_mods func cenv cx es s /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx es G tn s) /\
  es.gas_obs = [] /\ alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!tail. source (es with gas_obs := tail) =
    ((if i+k <= LENGTH bs then INL (Value result)
      else INR (Error (RuntimeError "evaluate_slice range"))), es with gas_obs := tail)) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 source (es,s,G,tn)
    (\H res ee HG tm t.
      res = INL (Value result) /\
      vv_post_mods H ctx func cenv cx e es sa sb s ee (Value result)
        (LocatedValue a (mk_ptr out LocMemory)) t /\
      vv_store_bound cx a a ee (Value result) (LocatedValue a (mk_ptr out LocMemory)) t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee HG tm t /\
      ptr_vv_ok cx a (Value result) (LocatedValue a (mk_ptr out LocMemory)) ee HG tm t /\
      ptr_buf_ok cenv e out HG t /\ ghost_kept_at lo cenv es sa G tn s HG tm /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t))
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))``;

val read_cut = ``\arg ea a s (G:string |-> num # num) tn eb b t G' tn' v op.
  (!H. valid_horizon cx st0 H eb.storage_trace ==>
    expr_post_mods H ctx func cenv cx arg ea a b s eb v op t /\
    s.vs_alloca_next <= t.vs_alloca_next /\ ghost_kept_at lo cenv ea a G tn s G' tn') /\
  MAP FDOM ea.scopes = MAP FDOM eb.scopes /\
  a.cs_next_var <= b.cs_next_var /\ a.cs_next_id <= b.cs_next_id``;

val reached = ``\arg ea eb u obs.
  !tail. bind (eval_expr cx arg) (read_result cx)
    (ea with gas_obs := obs ++ tail) = (INL u,eb with gas_obs := tail)``;

val bytes_or_string = ``
  (ann = BaseT (BytesT (Dynamic n)) /\ v = BytesV bs) \/
  (?str. ann = BaseT (StringT n) /\ v = StringV str /\ bs = MAP (n2w o ORD) str)``;

val result_shape = ``\result.
  (ann = BaseT (BytesT (Dynamic n)) /\ result = BytesV (TAKE k (DROP i bs))) \/
  (?str. ann = BaseT (StringT n) /\ bs = MAP (n2w o ORD) str /\
    result = StringV (TAKE k (DROP i str)))``;

val action = ``\result.
  !tail. ^finish v (IntV (&i)) (IntV (&k)) (e2 with gas_obs := tail) =
    ((if i+k <= LENGTH (bs:word8 list) then INL (Value result)
      else INR (Error (RuntimeError "evaluate_slice range"))), e2 with gas_obs := tail)``;

Triviality ordinary_slice_terminal_action:
  ^bytes_or_string /\ (i+k <= LENGTH bs ==> k <= n) ==>
  ?result. ^result_shape result /\ ^action result
Proof
  BETA_TAC >> disch_then (CONJUNCTS_THEN2 strip_assume_tac assume_tac)
  >- (qexists_tac `BytesV (TAKE k (DROP i bs))` >>
      Cases_on `i+k <= LENGTH bs` >>
      simp[evaluate_builtin_def,slice_bytes_nat,get_accounts_def,bind_def,
           vyperStateTheory.lift_sum_def,return_def,raise_def]) >>
  qexists_tac `StringV (TAKE k (DROP i str))` >>
  conj_tac >- (disj2_tac >> qexists_tac `str` >> simp[]) >>
  Cases_on `i+k <= LENGTH str` >>
  fs[evaluate_builtin_def,slice_string_nat,get_accounts_def,bind_def,
     vyperStateTheory.lift_sum_def,return_def,raise_def]
QED

Triviality slice_read_earlier_horizon:
  ^reached arg ea eb u obs /\ valid_horizon cx st0 H eb.storage_trace ==>
  valid_horizon cx st0 H ea.storage_trace
Proof
  BETA_TAC >> strip_tac >>
  qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` assume_tac) >>
  qpat_assum `bind _ _ _ = _` (mp_then (Pat `f st = _`) mp_tac valid_horizon_frame) >>
  simp[bodyForcedStorageFrameModsTheory.bop_forced_storage_frame]
QED

Triviality slice_terminal_room:
  stmt_state_rel H ctx func cenv cx es s /\ ctx_has_dalloca ctx ==>
  allocas_below_fmp s /\
  s.vs_alloca_next + pending_alloca_size func s <= w2n s.vs_initial_fmp
Proof
  strip_tac >> drule_then assume_tac stmt_state_rel_allocas_below_fmp >>
  drule stmt_state_rel_fmp_room >> simp[fmp_room_def] >> decide_tac
QED

Triviality slice_terminal_type_bounds:
  ((ann = BaseT (BytesT (Dynamic n))) \/ (ann = BaseT (StringT n))) /\
  expr_body_pre_mods mods cenv cx env (Builtin ann (Slice n) args) es ==>
  is_bytestring_type ann /\ 32+n <= type_memory_bytes cenv ann /\
  type_memory_bytes cenv ann < dimword (:256)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `alloc_limits_expr cenv (Builtin ann (Slice n) args)` by fs[expr_body_pre_mods_def] >>
  qpat_x_assum `expr_body_pre_mods _ _ _ _ _ _` kall_tac >>
  qspec_then `n` assume_tac valueTypingMemoryPropsTheory.word_size_capacity >>
  qpat_x_assum `ann = _ \/ ann = _` (DISJ_CASES_THEN SUBST_ALL_TAC) >>
  fs[Once alloc_limits_expr_def,type_alloc_ok_def,is_word_type_def,
     is_bytestring_type_def,type_memory_bytes_def,vfmConstantsTheory.word_size_def,dimword_def] >>
  decide_tac
QED

val parent_post = ``\(H:(bool # bytes32 # type_value) list # num list)
    (res:eval_result + vyperState$exception) ee G tn t.
  let e = Builtin ann (Slice n) [src;start;len]; vv = LocatedValue ann (mk_ptr out LocMemory) in
  ?tv. res = INL tv /\
    vv_post_mods H ctx func cenv cx e es sa sb s0 ee tv vv t /\
    vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee tv vv t /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    s0.vs_alloca_next <= t.vs_alloca_next /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
    ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn t /\
    (!v. tv = Value v /\ ~is_word_type (post_value_type cenv e) /\
         ~is_bytestring_type (post_value_type cenv e) ==>
      vv_own cenv cx (post_value_type cenv e) sa sb ee tv vv t /\
      (!a p. vv = LocatedValue a p ==> p.ptr_location = LocMemory)) /\
    (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
      ?val. read_result cx tv ee = (INL val,ee) /\
        !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
          eval_operand (vv_operand vv) t = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
            val_in_memory rt val (w2n w) mem)) /\
    (!a op. vv = StackValue a op /\ ~is_word_type (post_value_type cenv e) ==>
      ptr_buf_ok cenv e op G t) /\
    (!a p. vv = LocatedValue a p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok cenv e p.ptr_operand G t) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn``;

Theorem slice_ordinary_terminal_outcome_mods:
  ^window_supplier /\
  ^bytes_or_string /\
  expr_body_pre_mods mods cenv cx env (Builtin ann (Slice n) [src;start;len]) es /\
  ^reached src es ec v obs0 /\ ^reached start ec e1 (IntV (&i)) obs1 /\
  ^reached len e1 e2 (IntV (&k)) obs2 /\
  ^read_cut src es sa s0 G0 tn0 ec sm sms Gm tm v op0 /\
  ^read_cut start ec sc scs Gc tc e1 sd sds Gd td (IntV (&i)) x /\
  ^read_cut len e1 sd sds Gd td e2 se ses Ge te (IntV (&k)) y /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0) /\
  (!H. valid_horizon cx st0 H ec.storage_trace ==> stmt_state_rel H ctx func cenv cx ec scs) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  local_ptrs_reserved cenv sc /\ local_ptrs_reserved cenv sd /\
  sm.cs_next_var <= sc.cs_next_var /\ sm.cs_next_id <= sc.cs_next_id /\
  (!z. not_fresh_at sm z ==> lookup_var z scs = lookup_var z sms /\
       FLOOKUP Gc z = FLOOKUP Gm z /\ op_taint tc (Var z) = op_taint tm (Var z)) /\
  ((scs.vs_memory = sms.vs_memory /\ scs.vs_allocas = sms.vs_allocas /\
    scs.vs_alloca_next = sms.vs_alloca_next /\ tc.t_mem = tm.t_mem) \/
   (compile_alloc_buffer 32 sm = (buf,stage) /\ fn_has_code sm stage func /\
    fn_inst_ids_distinct func /\ sms.vs_alloca_next <= scs.vs_alloca_next /\
    FLOOKUP scs.vs_allocas sm.cs_next_id = SOME (w2n p,32) /\
    (!aid entry. FLOOKUP sms.vs_allocas aid = SOME entry ==>
          FLOOKUP scs.vs_allocas aid = SOME entry) /\
    (!aid b len. aid < sm.cs_next_id /\ FLOOKUP sms.vs_allocas aid = SOME (b,len) ==>
          mem_bytes_at b len scs.vs_memory = mem_bytes_at b len sms.vs_memory) /\
    (!name b len. local_region cenv ec.scopes scs name b len ==>
          mem_bytes_at b len scs.vs_memory = mem_bytes_at b len sms.vs_memory) /\
    (!b len. b+len <= w2n p \/ w2n p+32 <= b ==>
          mem_bytes_at b len scs.vs_memory = mem_bytes_at b len sms.vs_memory) /\
    (!j. j < sms.vs_alloca_next /\ ~(w2n p <= j /\ j < w2n p+32) ==>
          (j IN tc.t_mem <=> j IN tm.t_mem)))) /\
  compile_slice_data limit (Var root) x y (type_memory_bytes cenv ann) se = (out,sb) /\
  fn_has_code se sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv se /\
  eval_operand limit ses = SOME (n2w (LENGTH bs)) /\
  lookup_var root ses = SOME p /\ ptr_covers Ge te root ses (LENGTH bs) /\
  op_prov Ge limit = NONE /\ op_taint te limit = {} /\
  eval_operand x ses = SOME (n2w i) /\ eval_operand y ses = SOME (n2w k) /\
  op_prov Ge x = NONE /\ op_taint te x = {} /\
  op_prov Ge y = NONE /\ op_taint te y = {} /\
  (!z. limit = Var z ==> not_fresh_at se z) /\ not_fresh_at se root /\
  (!z. x = Var z ==> not_fresh_at se z) /\ (!z. y = Var z ==> not_fresh_at se z) /\
  (!l. limit <> Label l) /\ (!l. x <> Label l) /\ (!l. y <> Label l) /\
  mem_bytes_at (w2n p) (LENGTH bs) ses.vs_memory = bs /\
  (!j. w2n p <= j /\ j < w2n p + LENGTH bs ==> j NOTIN te.t_mem) /\
  w2n p + LENGTH bs < dimword (:256) /\ w2n p + LENGTH bs <= ses.vs_alloca_next /\
  i < dimword (:256) /\ k < dimword (:256) /\ (i+k <= LENGTH bs ==> k <= n) /\
  storage_trace_domain cx st0 e2.storage_trace /\
  (!H. valid_horizon cx st0 H e2.storage_trace ==>
    stmt_state_rel H ctx func cenv cx e2 ses /\ immutable_frame_mods func cenv cx e2 ses /\
    storage_well_formed_on cx e2 (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx e2 Ge te ses) /\
  e2.gas_obs = [] /\ alloca_history func ses /\ ~ses.vs_halted /\
  ses.vs_current_bb = se.cs_current_bb /\ ses.vs_inst_idx = LENGTH se.cs_current_insts /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at se z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at se z) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (^finish v (IntV (&i)) (IntV (&k))) (e2,ses,Ge,te) ^parent_post ^exit_post
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (BETA_RULE ordinary_slice_terminal_action) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `result` (map_every assume_tac o CONJUNCTS)) >>
  mp_tac (Q.INST [`args` |-> `[src;start;len]`] slice_terminal_type_bounds) >>
  (impl_tac >- (reverse conj_tac >- first_assum ACCEPT_TAC >>
    qpat_assum `(ann = _ /\ result = _) \/ _` mp_tac >>
    POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[])) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon e2.storage_trace) e2.storage_trace` by
    fs[storage_trace_domain_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp ses /\
    ses.vs_alloca_next + pending_alloca_size func ses <= w2n ses.vs_initial_fmp` by
    (strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H e2.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     drule_all_then ACCEPT_TAC slice_terminal_room) >>
  suspend "window"
QED

Resume slice_ordinary_terminal_outcome_mods[window]:
  qmatch_goalsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ source _ _ _` >>
  `!tail. source (e2 with gas_obs := tail) =
    ((if i+k <= LENGTH bs then INL (Value result)
      else INR (Error (RuntimeError "evaluate_slice range"))),e2 with gas_obs := tail)` by
    (qunabbrev_tac `source` >> first_assum ACCEPT_TAC) >>
  irule gas_outcome_full_mods_post_source >> BETA_TAC >>
  qexistsl_tac [`\H res ee G tn t.
      res = INL (Value result) /\
      vv_post_mods H ctx func cenv cx (Builtin ann (Slice n) [src;start;len])
        e2 se sb ses ee (Value result) (LocatedValue ann (mk_ptr out LocMemory)) t /\
      vv_store_bound cx ann ann ee (Value result) (LocatedValue ann (mk_ptr out LocMemory)) t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ ses.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
      ptr_vv_ok cx ann (Value result) (LocatedValue ann (mk_ptr out LocMemory)) ee G tn t /\
      ptr_buf_ok cenv (Builtin ann (Slice n) [src;start;len]) out G t /\
      ghost_kept_at lo cenv e2 se Ge te ses G tn /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t)`, `^exit_post`] >> BETA_TAC >>
  conj_tac >- (pure_rewrite_tac [LET_THM] >> BETA_TAC >> suspend "rebase") >>
  suspend "apply_window"
QED

Resume slice_ordinary_terminal_outcome_mods[apply_window]:
  conj_tac >- simp_tac bool_ss [] >>
  qpat_assum `!limit root start cnt N sa out sb func cenv ctx s bs p G tn i k n a result e args cx st0 es DF lo d explicit mods source PG. _`
    irule >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`type_memory_bytes cenv ann`,`[src;start;len]`,`bs`,`y`,`i`,`k`,
                `limit`,`n`,`p`,`root`,`x`] >>
  asm_rewrite_tac[] >>
  simp[listTheory.MEM,DISJ_IMP_THM,FORALL_AND_THM]
QED

Resume slice_ordinary_terminal_outcome_mods[rebase]:
  qx_genl_tac [`H`,`res`,`ee`,`Gz`,`tz`,`z`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ee.storage_trace = e2.storage_trace` by
    (qpat_x_assum `?xs. !tail. source _ = _` (qx_choose_then `xs` (qspec_then `[]` assume_tac)) >>
     qpat_assum `!tail. source _ = _` (qspec_then `xs ++ []` mp_tac) >>
     qpat_assum `source (e2 with gas_obs := _) = _` (pure_once_rewrite_tac o single) >>
     disch_then (mp_tac o AP_TERM ``SND : (eval_result + vyperState$exception) # evaluation_state -> evaluation_state``) >>
     simp_tac bool_ss [pairTheory.SND] >>
     disch_then (mp_tac o AP_TERM ``\s:evaluation_state. s.storage_trace``) >> simp[]) >>
  `valid_horizon cx st0 H e2.storage_trace` by fs[] >>
  `valid_horizon cx st0 H e1.storage_trace` by
    (irule (BETA_RULE slice_read_earlier_horizon) >>
     qexistsl_tac [`len`,`e2`,`obs2`,`IntV (&k)`] >> asm_rewrite_tac[]) >>
  `valid_horizon cx st0 H ec.storage_trace` by
    (irule (BETA_RULE slice_read_earlier_horizon) >>
     qexistsl_tac [`start`,`e1`,`obs1`,`IntV (&i)`] >> asm_rewrite_tac[]) >>
  `valid_horizon cx st0 H es.storage_trace` by
    (irule (BETA_RULE slice_read_earlier_horizon) >>
     qexistsl_tac [`src`,`ec`,`obs0`,`v`] >> asm_rewrite_tac[]) >>
  map_every (fn pat => qpat_assum pat (drule_then (map_every assume_tac o CONJUNCTS)))
    [`!H. valid_horizon cx st0 H ec.storage_trace ==> expr_post_mods _ _ _ _ _ src _ _ _ _ _ _ _ _ /\ _`,
     `!H. valid_horizon cx st0 H e1.storage_trace ==> expr_post_mods _ _ _ _ _ start _ _ _ _ _ _ _ _ /\ _`,
     `!H. valid_horizon cx st0 H e2.storage_trace ==> expr_post_mods _ _ _ _ _ len _ _ _ _ _ _ _ _ /\ _`,
     `!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel _ _ _ _ _ es s0`,
     `!H. valid_horizon cx st0 H ec.storage_trace ==> stmt_state_rel _ _ _ _ _ ec scs`] >>
  suspend "apply_rebase"
QED

Resume slice_ordinary_terminal_outcome_mods[apply_rebase]:
  qmatch_asmsub_rename_tac `compile_slice_data limit (Var root) op1 op2 _ se = (out,sb)` >>
  qmatch_asmsub_rename_tac `expr_post_mods H ctx func cenv cx src es sa sm s0 ec v0 op0 sms` >>
  qmatch_asmsub_rename_tac `lookup_var root ses = SOME slice_ptr` >>
  mp_tac (slice_ordinary_window_rebase_mods |> Q.INST
    [`ef` |-> `ee`, `p` |-> `w2n (slice_ptr:bytes32)`,
     `v1` |-> `IntV (&(i:num))`, `v2` |-> `IntV (&(k:num))`]) >>
  pure_rewrite_tac [LET_THM] >> BETA_TAC >>
  pure_rewrite_tac [post_value_type_def,expr_type_def,lowered_value_type_def] >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qexists_tac `Value result` >>
  asm_rewrite_tac[post_value_type_def,expr_type_def,lowered_value_type_def]
QED

Finalise slice_ordinary_terminal_outcome_mods

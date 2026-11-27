(* The common ordinary Slice continuation after either source capture. *)
Theory bodySliceOrdinaryCapturedWordsMods
Ancestors
  bodySliceOrdinaryWordsBindMods bodySliceOrdinarySavedDescriptorMods
  bodySliceOrdinaryTerminalPrefixMods bodySliceOrdinaryTerminalOutcomeMods
  gasOutcomeFullZeroPrefixMods bodyForcedStorageFrameMods
  exprSimFullBundleProps exprSimWordArgs loweringPosts vyperStorageFootprint vyperStorageTrace
  exprLoweringProps bodyFullPredsMods vyperState vyperAST words list
  bodyFullHashKeccakFixed exprSimHypsDefs compileEnv exprLowering finite_map
  ptrDiscipline venomState
Libs monadsyntax

val finish = ``\v v1 v2. do
  acc <- get_accounts;
  r <- lift_sum (evaluate_builtin cx acc ann (Slice n)
                  (MAP expr_type [src;start;len]) [v;v1;v2]);
  return (Value r)
  od``;
val next = ``\v. bind (bind (eval_expr cx start) (read_result cx))
    (\v1. bind (bind (eval_expr cx len) (read_result cx)) (^finish v v1))``;
val exit_post = ``\(H:(bool # bytes32 # type_value) list # num list)
    (res:eval_result + vyperState$exception) ee
    (gt:(string |-> num # num) # taint) r.
  expr_exit res r /\ halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u)``;
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

(* The standalone suffix contract is an input, not an imported machine run. *)
val window_supplier =
  fst (dest_conj (fst (dest_imp (concl slice_ordinary_terminal_outcome_mods))));

val entry = ``\ee a t G tn.
  local_ptrs_reserved cenv a /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at a z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at a z) /\
  return_buf_frame d cenv a t /\ alloca_history func t /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  (!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee t /\ immutable_frame_mods func cenv cx ee t /\
    storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t) /\
  ~t.vs_halted /\ t.vs_current_bb = a.cs_current_bb /\ t.vs_inst_idx = LENGTH a.cs_current_insts``;
val child = ``\ty e a b sha shb op.
  lower_value compile_expr cenv ty e a = (op,b) /\
  lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e) sha = (op,shb) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (a,b,sha,shb) /\
  a.cs_next_var <= b.cs_next_var``;
val reached = ``\arg ea eb u obs.
  !tail. bind (eval_expr cx arg) (read_result cx)
    (ea with gas_obs := obs ++ tail) = (INL u,eb with gas_obs := tail)``;
val read_post = ``\arg ea a s (G:string |-> num # num) tn eb b t G' tn' v op.
  !H. valid_horizon cx st0 H eb.storage_trace ==>
    expr_post_mods H ctx func cenv cx arg ea a b s eb v op t /\
    s.vs_alloca_next <= t.vs_alloca_next /\ ghost_kept_at lo cenv ea a G tn s G' tn'``;
val capture_frame = ``
  (!z. not_fresh_at sm z ==> lookup_var z scs = lookup_var z sms /\
       FLOOKUP (Gc:string |-> num # num) z = FLOOKUP (Gm:string |-> num # num) z /\ op_taint tc (Var z) = op_taint tm (Var z)) /\
  ((scs.vs_memory = sms.vs_memory /\ scs.vs_allocas = sms.vs_allocas /\
    scs.vs_alloca_next = sms.vs_alloca_next /\ tc.t_mem = tm.t_mem) \/
   (compile_alloc_buffer 32 sm = (buf,stage) /\ fn_has_code sm stage func /\
    fn_inst_ids_distinct func /\ sms.vs_alloca_next <= scs.vs_alloca_next /\
    FLOOKUP scs.vs_allocas sm.cs_next_id = SOME (w2n (p:bytes32),32) /\
    (!aid ent. FLOOKUP sms.vs_allocas aid = SOME ent ==>
          FLOOKUP scs.vs_allocas aid = SOME ent) /\
    (!aid b len. aid < sm.cs_next_id /\ FLOOKUP sms.vs_allocas aid = SOME (b,len) ==>
          mem_bytes_at b len scs.vs_memory = mem_bytes_at b len sms.vs_memory) /\
    (!name b len. local_region cenv ec.scopes scs name b len ==>
          mem_bytes_at b len scs.vs_memory = mem_bytes_at b len sms.vs_memory) /\
    (!b len. b+len <= w2n p \/ w2n p+32 <= b ==>
          mem_bytes_at b len scs.vs_memory = mem_bytes_at b len sms.vs_memory) /\
    (!j. j < sms.vs_alloca_next /\ ~(w2n p <= j /\ j < w2n p+32) ==>
          (j IN tc.t_mem <=> j IN tm.t_mem))))``;

Triviality slice_captured_earlier_horizon:
  ^reached arg ea eb u obs /\ valid_horizon cx st0 H eb.storage_trace ==>
  valid_horizon cx st0 H ea.storage_trace
Proof
  BETA_TAC >> strip_tac >>
  qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` assume_tac) >>
  qpat_assum `bind _ _ _ = _` (mp_then (Pat `f st = _`) mp_tac valid_horizon_frame) >>
  simp[bodyForcedStorageFrameModsTheory.bop_forced_storage_frame]
QED

Triviality slice_captured_cons:
  ^reached arg ea eb u obs /\
  (!tail. eval_exprs cx rest (eb with gas_obs := obs' ++ tail) =
           (INL us,ee with gas_obs := tail)) ==>
  !tail. eval_exprs cx (arg::rest) (ea with gas_obs := (obs ++ obs') ++ tail) =
           (INL (u::us),ee with gas_obs := tail)
Proof
  BETA_TAC >> strip_tac >> gen_tac >>
  pure_once_rewrite_tac[eval_exprs_cons_action] >>
  qpat_assum `!tail. bind _ _ _ = _` (qspec_then `obs' ++ tail` assume_tac) >>
  qpat_assum `!tail. eval_exprs _ _ _ = _` (qspec_then `tail` assume_tac) >>
  pure_once_rewrite_tac[GSYM APPEND_ASSOC] >>
  qpat_assum `bind _ _ _ = _` (fn th => simp_tac (srw_ss()) [Once bind_def,th]) >>
  qpat_assum `eval_exprs _ _ _ = _` (fn th => simp_tac (srw_ss()) [Once bind_def,th,return_def])
QED

Theorem slice_ordinary_captured_words_reached_mods:
  ^window_supplier /\
  ((ann = BaseT (BytesT (Dynamic n)) /\ expr_type src = BaseT (BytesT bd) /\ v = BytesV bs) \/
   (?m str. ann = BaseT (StringT n) /\ expr_type src = BaseT (StringT m) /\
             v = StringV str /\ bs = MAP (n2w o ORD) str)) /\
  code_slice_source (Slice n) [src;start;len] = NONE /\
  slice_operands_ok (Slice n) [src;start;len] /\ value_runtime_typed env (expr_type src) v /\
  expr_body_pre_mods mods cenv cx env (Builtin ann (Slice n) [src;start;len]) es /\
  ^reached src es ec v obs0 /\ ^read_post src es sa s0 G0 tn0 ec sm sms Gm tm v op0 /\
  MAP FDOM es.scopes = MAP FDOM ec.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  sm.cs_next_var <= sc.cs_next_var /\ sm.cs_next_id <= sc.cs_next_id /\
  (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
           (sms,Gm,tm) [] (OK scs,Gc,tc)) /\ ^capture_frame /\
  not_fresh_at sc root /\ (!z. limit = Var z ==> not_fresh_at sc z) /\
  (!l. limit <> Label l) /\ eval_operand limit scs = SOME (n2w (LENGTH bs)) /\
  op_prov Gc limit = NONE /\ op_taint tc limit = {} /\
  lookup_var root scs = SOME p /\ ptr_covers Gc tc root scs (LENGTH bs) /\
  w2n p + LENGTH bs < dimword (:256) /\ w2n p + LENGTH bs <= scs.vs_alloca_next /\
  (!H e1 e2 v1 v2 sds ses Gd Ge td te.
    expr_sim_inv_mods mods cenv cx env e1 /\
    valid_horizon cx st0 H ec.storage_trace /\ sc.cs_next_id <= sd.cs_next_id /\
    MAP FDOM ec.scopes = MAP FDOM e1.scopes /\ MAP FDOM e1.scopes = MAP FDOM e2.scopes /\
    expr_post_mods H ctx func cenv cx start ec sc sd scs e1 v1 x sds /\
    expr_post_mods H ctx func cenv cx len e1 sd se sds e2 v2 y ses /\
    ghost_kept_at lo cenv ec sc Gc tc scs Gd td /\ ghost_kept_at lo cenv e1 sd Gd td sds Ge te ==>
    mem_bytes_at (w2n p) (LENGTH bs) ses.vs_memory = bs /\
    (!j. w2n p <= j /\ j < w2n p + LENGTH bs ==> j NOTIN te.t_mem)) /\
  expr_sim_inv_mods mods cenv cx env ec /\
  (!e mid. MEM e [start;len] /\ expr_sim_inv_mods mods cenv cx env mid ==>
    expr_body_pre_mods mods cenv cx env e mid) /\
  expr_type start = BaseT (UintT 256) /\ expr_type len = BaseT (UintT 256) /\
  body_const_cells_agree_mods mods cx env ec /\ body_exprs_full_ok_mods mods exps cx [start;len] /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods msrc tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  ^child ty1 start sc sd shc shd x /\ ^child ty2 len sd se shd she y /\
  sc.cs_next_id <= sd.cs_next_id /\ sd.cs_next_id <= se.cs_next_id /\
  ^entry ec sc scs Gc tc /\ local_ptrs_reserved cenv sd /\ local_ptrs_reserved cenv se /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  compile_slice_data limit (Var root) x y (type_memory_bytes cenv ann) se = (out,sb) /\
  fn_has_code se sb func /\ fn_inst_ids_distinct func /\
  gas_admissible (^next v) expr_vv_res_ok ec ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cenv.ce_modules cx st0 (^next v) (ec,sms,Gm,tm) ^parent_post ^exit_post
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  irule gas_outcome_full_mods_zero_prefix >>
  qexistsl_tac [`Gc`,`scs`,`tc`] >>
  conj_tac >- (gen_tac >> qpat_assum `!D. gas_origin_ptr_path _ _ _ _` (irule o SPEC_ALL)) >>
  irule (BETA_RULE (Q.INST [`k` |-> `^finish v`] slice_ordinary_words_bind_mods)) >> BETA_TAC >>
  asm_rewrite_tac[] >>
  conj_tac >- simp[storage_trace_frame_bind_all,storage_trace_frame_state_reads,
                  storage_trace_frame_lifts,storage_trace_frame_return] >>
  qexistsl_tac [`d`,`env`,`exps`,`mods`,`sd`,`se`,`sc`,`shd`,`she`,`shc`,
                `shadow_func`,`msrc`,`tops`,`ty1`,`ty2`,`x`,`y`] >>
  asm_rewrite_tac[] >>
  qx_genl_tac [`marks1`,`v1`,`e1`,`Gd`,`td`,`sds`,`marks2`,`v2`,`e2`,`Ge`,`te`,`ses`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  suspend "reached"
QED

Resume slice_ordinary_captured_words_reached_mods[reached]:
  qabbrev_tac `i = w2n (val_to_w256 v1)` >>
  qabbrev_tac `k = w2n (val_to_w256 v2)` >>
  `v1 = IntV (&i)` by (simp_tac bool_ss [Abbr `i`] >> first_assum ACCEPT_TAC) >>
  `v2 = IntV (&k)` by (simp_tac bool_ss [Abbr `k`] >> first_assum ACCEPT_TAC) >>
  `i < dimword (:256) /\ k < dimword (:256)` by simp[Abbr `i`,Abbr `k`,w2n_lt] >>
  `eval_operand x ses = SOME (n2w i) /\ eval_operand y ses = SOME (n2w k)` by
    simp[Abbr `i`,Abbr `k`] >>
  `valid_horizon cx st0 (storage_trace_horizon e2.storage_trace) e2.storage_trace` by
    fs[storage_trace_domain_def] >>
  `valid_horizon cx st0 (storage_trace_horizon e2.storage_trace) e1.storage_trace` by
    (irule (BETA_RULE slice_captured_earlier_horizon) >>
     qexistsl_tac [`len`,`e2`,`gas_explicit marks2 sds.vs_gas_readings`,`v2`] >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `valid_horizon cx st0 (storage_trace_horizon e2.storage_trace) ec.storage_trace` by
    (irule (BETA_RULE slice_captured_earlier_horizon) >>
     qexistsl_tac [`start`,`e1`,`gas_explicit marks1 scs.vs_gas_readings`,`v1`] >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `!H. valid_horizon _ _ H e1.storage_trace ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H e2.storage_trace ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `MAP FDOM ec.scopes = MAP FDOM e1.scopes /\ MAP FDOM e1.scopes = MAP FDOM e2.scopes` by simp[] >>
  qpat_assum `!H e1 e2 v1 v2 sds ses Gd Ge td te. _ ==> mem_bytes_at _ _ _ = _ /\ _`
    (drule_all_then strip_assume_tac) >>
  `wb_frame cenv ec e1 sc scs sds` by
    (qpat_assum `expr_post_mods _ _ _ _ _ start _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [bodyFullPostsModsTheory.expr_post_mods_def]) >>
     drule_then ACCEPT_TAC expr_post_frame) >>
  `wb_frame cenv e1 e2 sd sds ses` by
    (qpat_assum `expr_post_mods _ _ _ _ _ len _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [bodyFullPostsModsTheory.expr_post_mods_def]) >>
     drule_then ACCEPT_TAC expr_post_frame) >>
  mp_tac (Q.INST [`data` |-> `Var root`,`es0` |-> `ec`,`es1` |-> `e1`,`es2` |-> `e2`]
    (INST_TYPE [alpha |-> ``:word8``] slice_ordinary_saved_descriptor_mods)) >>
  (impl_tac >- (rpt conj_tac >> (REFL_TAC ORELSE first_assum ACCEPT_TAC))) >>
  disch_then strip_assume_tac >>
  suspend "terminal"
QED

Resume slice_ordinary_captured_words_reached_mods[terminal]:
  `!tail. eval_exprs cx [src;start;len]
      (es with gas_obs := (obs0 ++ (gas_explicit marks1 scs.vs_gas_readings ++
                                    gas_explicit marks2 sds.vs_gas_readings)) ++ tail) =
      (INL [v;v1;v2],e2 with gas_obs := tail)` by
    (irule (BETA_RULE slice_captured_cons) >> qexists_tac `ec` >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `!tail. eval_exprs cx [start;len] _ = _` mp_tac >>
     simp_tac std_ss [GSYM APPEND_ASSOC]) >>
  `i+k <= LENGTH bs ==> k <= n` by
    (mp_tac (Q.INST [`prefix` |-> `obs0 ++ (gas_explicit marks1 scs.vs_gas_readings ++
                                    gas_explicit marks2 sds.vs_gas_readings)`, `ee` |-> `e2`]
       slice_ordinary_terminal_prefix_mods) >>
     impl_tac >- (rpt (conj_tac ORELSE first_assum ACCEPT_TAC)
       >- (qpat_assum `(ann = _ /\ _ /\ _) \/ _` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
       qpat_assum `!tail. eval_exprs cx [src;start;len] _ = _` mp_tac >>
       qpat_assum `v1 = IntV (&i)` (fn th => pure_once_rewrite_tac [GSYM th]) >>
       qpat_assum `v2 = IntV (&k)` (fn th => pure_once_rewrite_tac [GSYM th]) >> simp_tac bool_ss []) >>
     disch_then (ACCEPT_TAC o CONJUNCT1)) >>
  `cenv.ce_modules = mods` by (drule_then ACCEPT_TAC bodyInvCodePropsTheory.contract_inv_cenv_modules) >>
  qpat_assum `cenv.ce_modules = mods` (pure_once_rewrite_tac o single) >>
  qpat_assum `v1 = IntV (&i)` (pure_once_rewrite_tac o single) >>
  qpat_assum `v2 = IntV (&k)` (pure_once_rewrite_tac o single) >>
  mp_tac (BETA_RULE (Q.INST [`obs1` |-> `gas_explicit marks1 scs.vs_gas_readings`,
                             `obs2` |-> `gas_explicit marks2 sds.vs_gas_readings`,
                             `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
    slice_ordinary_terminal_outcome_mods)) >>
  (impl_tac >-
    (rpt (conj_tac ORELSE first_assum ACCEPT_TAC)
     >- (qpat_assum `(ann = _ /\ _ /\ _) \/ _` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[])
     >- (qpat_assum `v1 = IntV (&i)` (fn th => pure_once_rewrite_tac [GSYM th]) >>
         first_assum ACCEPT_TAC)
     >- (qpat_assum `v2 = IntV (&k)` (fn th => pure_once_rewrite_tac [GSYM th]) >>
         first_assum ACCEPT_TAC)
     >- (qpat_assum `v1 = IntV (&i)` (fn th => pure_once_rewrite_tac [GSYM th]) >>
         rpt strip_tac >> qpat_assum `!H. valid_horizon _ _ H e1.storage_trace ==> _ /\ _`
           (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC)
     >- (qpat_assum `v2 = IntV (&k)` (fn th => pure_once_rewrite_tac [GSYM th]) >>
         rpt strip_tac >> qpat_assum `!H. valid_horizon _ _ H e2.storage_trace ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
           (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC)
     >- (rpt strip_tac >> qpat_assum `!H. valid_horizon _ _ H ec.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
           (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
     rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sc` >> conj_tac
     >- (qpat_assum `sc.cs_next_var <= sd.cs_next_var` mp_tac >>
         qpat_assum `sd.cs_next_var <= se.cs_next_var` mp_tac >> decide_tac) >>
     qpat_assum `!z. limit = Var z ==> not_fresh_at sc z` irule >>
     first_assum ACCEPT_TAC)) >>
  disch_then ACCEPT_TAC
QED

Finalise slice_ordinary_captured_words_reached_mods

(* The lean callback remains available when the payload uses only the frames. *)
Theorem slice_ordinary_captured_words_mods:
  ^window_supplier /\
  ((ann = BaseT (BytesT (Dynamic n)) /\ expr_type src = BaseT (BytesT bd) /\ v = BytesV bs) \/
   (?m str. ann = BaseT (StringT n) /\ expr_type src = BaseT (StringT m) /\
             v = StringV str /\ bs = MAP (n2w o ORD) str)) /\
  code_slice_source (Slice n) [src;start;len] = NONE /\
  slice_operands_ok (Slice n) [src;start;len] /\ value_runtime_typed env (expr_type src) v /\
  expr_body_pre_mods mods cenv cx env (Builtin ann (Slice n) [src;start;len]) es /\
  ^reached src es ec v obs0 /\ ^read_post src es sa s0 G0 tn0 ec sm sms Gm tm v op0 /\
  MAP FDOM es.scopes = MAP FDOM ec.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  sm.cs_next_var <= sc.cs_next_var /\ sm.cs_next_id <= sc.cs_next_id /\
  (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
           (sms,Gm,tm) [] (OK scs,Gc,tc)) /\ ^capture_frame /\
  not_fresh_at sc root /\ (!z. limit = Var z ==> not_fresh_at sc z) /\
  (!l. limit <> Label l) /\ eval_operand limit scs = SOME (n2w (LENGTH bs)) /\
  op_prov Gc limit = NONE /\ op_taint tc limit = {} /\
  lookup_var root scs = SOME p /\ ptr_covers Gc tc root scs (LENGTH bs) /\
  w2n p + LENGTH bs < dimword (:256) /\ w2n p + LENGTH bs <= scs.vs_alloca_next /\
  (!H e1 e2 v1 v2 sds ses Gd Ge td te.
    valid_horizon cx st0 H ec.storage_trace /\ sc.cs_next_id <= sd.cs_next_id /\
    MAP FDOM ec.scopes = MAP FDOM e1.scopes /\ MAP FDOM e1.scopes = MAP FDOM e2.scopes /\
    expr_post_mods H ctx func cenv cx start ec sc sd scs e1 v1 x sds /\
    expr_post_mods H ctx func cenv cx len e1 sd se sds e2 v2 y ses /\
    ghost_kept_at lo cenv ec sc Gc tc scs Gd td /\ ghost_kept_at lo cenv e1 sd Gd td sds Ge te ==>
    mem_bytes_at (w2n p) (LENGTH bs) ses.vs_memory = bs /\
    (!j. w2n p <= j /\ j < w2n p + LENGTH bs ==> j NOTIN te.t_mem)) /\
  expr_sim_inv_mods mods cenv cx env ec /\
  (!e mid. MEM e [start;len] /\ expr_sim_inv_mods mods cenv cx env mid ==>
    expr_body_pre_mods mods cenv cx env e mid) /\
  expr_type start = BaseT (UintT 256) /\ expr_type len = BaseT (UintT 256) /\
  body_const_cells_agree_mods mods cx env ec /\ body_exprs_full_ok_mods mods exps cx [start;len] /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods msrc tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  ^child ty1 start sc sd shc shd x /\ ^child ty2 len sd se shd she y /\
  sc.cs_next_id <= sd.cs_next_id /\ sd.cs_next_id <= se.cs_next_id /\
  ^entry ec sc scs Gc tc /\ local_ptrs_reserved cenv sd /\ local_ptrs_reserved cenv se /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  compile_slice_data limit (Var root) x y (type_memory_bytes cenv ann) se = (out,sb) /\
  fn_has_code se sb func /\ fn_inst_ids_distinct func /\
  gas_admissible (^next v) expr_vv_res_ok ec ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cenv.ce_modules cx st0 (^next v) (ec,sms,Gm,tm) ^parent_post ^exit_post
Proof
  mp_tac slice_ordinary_captured_words_reached_mods >>
  BETA_TAC >> disch_then (fn th => disch_then (fn h =>
    MATCH_MP_TAC th >> map_every assume_tac (CONJUNCTS h))) >>
  rpt (conj_tac ORELSE first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!H e1 e2 v1 v2 sds ses Gd Ge td te. _ ==> mem_bytes_at _ _ _ = _ /\ _`
    (drule_all_then ACCEPT_TAC)
QED

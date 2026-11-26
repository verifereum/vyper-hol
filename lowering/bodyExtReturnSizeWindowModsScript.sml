(* The source window uses the copied length, not the size of returndata. *)
Theory bodyExtReturnSizeWindowMods
Ancestors
  bodyFullExtCallReturnSizeRoute bodyForRangeScalarFrameMods
  bodyExtSizeSuccessExactMods abiDecodePtrMemberFrame extcallReturnDefaultTypes
  bodyFullPostsMods bodyFullShadowBodyInv
  extcallReturnEntryBridge abiReturnSize bodyPtrDefs ptrDiscipline venomState venomMemDefs
  fragGasOriginPtr fragGasOrigin fragGasMode fragGasPathFrameMem bodyMemAggregatePath
  decoderGhostFramePtr exprSimWordArgs bodyFullUnwrapRun freshWrites exprLoweringProps
  finite_map words arithmetic list pred_set

Theorem extcall_clipped_ptr_window[local]:
  eval_operand (Var source) t = SOME ro /\
  FLOOKUP G source = SOME (prov_base,span) /\
  op_taint tn (Var source) = {} /\
  prov_base <= w2n ro /\ w2n ro + cap <= prov_base + span /\
  alloca_inv t /\ FLOOKUP t.vs_allocas live = SOME (w2n ro,bufsz) /\
  cap <= bufsz /\
  (!i. w2n ro <= i /\ i < w2n ro + MIN cap (LENGTH bs) ==>
       i NOTIN tn.t_mem) /\
  lookup_var source u = lookup_var source t /\
  FLOOKUP Gf source = FLOOKUP G source /\
  op_taint tm (Var source) = op_taint tn (Var source) /\
  (!i. i < t.vs_alloca_next ==> (i IN tm.t_mem <=> i IN tn.t_mem)) ==>
  abi_decode_ptr_window Gf tm u source ro (LENGTH (TAKE cap bs))
Proof
  strip_tac >>
  `LENGTH (TAKE cap bs) = MIN cap (LENGTH bs)` by
    (Cases_on `cap <= LENGTH bs` >> simp[LENGTH_TAKE_EQ, MIN_DEF] >> decide_tac) >>
  `LENGTH (TAKE cap bs) <= cap` by simp[MIN_LE] >>
  `w2n ro + bufsz <= t.vs_alloca_next` by
    (fs[alloca_inv_def, alloca_next_valid_def] >> metis_tac[ADD_COMM]) >>
  `lookup_var source t = SOME ro` by fs[eval_operand_def] >>
  simp[abi_decode_ptr_window_def, ptr_covers_def] >>
  rpt strip_tac >>
  `i < t.vs_alloca_next` by decide_tac >> simp[]
QED

Theorem extcall_size_window_kept_mods:
  rt = (if needs_external_call_wrap ret_type then TupleT [ret_type] else ret_type) /\
  evaluate_type (get_tenv cx) ret_type = SOME tv /\
  low = abi_static_size cenv.ce_struct_fields rt /\
  low = abi_static_length (vyper_to_abi_type (get_tenv cx) rt) /\
  cap = abi_size_bound cenv.ce_struct_fields rt /\
  compile_return_value_decode low cap k = (hi,hs) /\ fn_has_code k hs func /\
  low < dimword (:256) /\ cap < dimword (:256) /\
  p.vs_returndata = bs /\ LENGTH bs < dimword (:256) /\
  ~p.vs_halted /\ (ctx_has_dalloca ctx ==> allocas_below_fmp p) /\ allocas_from lo p /\
  p.vs_current_bb = k.cs_current_bb /\ p.vs_inst_idx = LENGTH k.cs_current_insts /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK p,Gp,tp)) /\
  compile_abi_decode_to_buf (Var output) (Lit 0w) MLOAD (Var source) hi
    (type_to_abi_dec_info cenv.ce_struct_fields cenv rt) hs = ((),de) /\
  fn_has_code hs de func /\ fn_inst_ids_distinct func /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     abi_return_decode_ready H ctx func cenv cx ee k
       (abi_malformed_scratch_sites hs de func) dstid live (Var source) (Var output)
       (w2n ro) cap bs dest (type_memory_bytes cenv rt) p /\
     storage_well_formed_on cx ee (FST H) /\
     ghost_inv_at_mods (DF H) lo rb cenv cx ee Gp tp p) /\
  immutable_frame_mods func cenv cx ee p /\
  local_ptrs_reserved cenv k /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at k x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at k x) /\
  eval_operand (Var source) t = SOME ro /\
  FLOOKUP G source = SOME (prov_base,span) /\
  op_taint tn (Var source) = {} /\
  prov_base <= w2n ro /\ w2n ro + cap <= prov_base + span /\
  alloca_inv t /\ FLOOKUP t.vs_allocas live = SOME (w2n ro,bufsz) /\ cap <= bufsz /\
  (!i. w2n ro <= i /\ i < w2n ro + MIN cap (LENGTH bs) ==> i NOTIN tn.t_mem) /\
  lookup_var source p = lookup_var source t /\ FLOOKUP Gp source = FLOOKUP G source /\
  op_taint tp (Var source) = op_taint tn (Var source) /\
  (!i. i < t.vs_alloca_next ==> (i IN tp.t_mem <=> i IN tn.t_mem)) /\
  not_fresh_at k source /\ not_fresh_at k output /\
  ptr_covers Gp tp output p (type_memory_bytes cenv rt) /\
  alloca_history func p /\ alloca_inv p /\
  wb_frame cenv es ee sa s0 p /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_id <= dstid /\ dstid < sb.cs_next_id /\
  sa.cs_next_id <= k.cs_next_id /\ sa.cs_next_var <= k.cs_next_var /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  s0.vs_alloca_next <= p.vs_alloca_next /\
  ghost_kept_at lo cenv es sa Gi ti si Gp tp ==>
  if LENGTH bs < low then
    ?err z Gf tm. evaluate_abi_decode_return (get_tenv cx) ret_type bs = INR err /\
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (t,G,tn) [] (Abort Revert_abort z,Gf,tm))
  else
    ?u Gf tm. abi_static_size cenv.ce_struct_fields rt <= LENGTH bs /\
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK u,Gf,tm)) /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
         abi_malformed_entry H ctx func cenv cx ee hs (abi_malformed_scratch_sites hs de func)
           dstid live (Var source) hi (Lit 0w) (Var output) (w2n ro)
           (LENGTH (TAKE cap bs)) (TAKE cap bs) 0 dest (type_memory_bytes cenv rt) u /\
         storage_well_formed_on cx ee (FST H) /\
         ghost_inv_at_mods (DF H) lo rb cenv cx ee Gf tm u) /\
      ~u.vs_halted /\ u.vs_current_bb = hs.cs_current_bb /\
      u.vs_inst_idx = LENGTH hs.cs_current_insts /\
      lookup_var source u = lookup_var source t /\ FLOOKUP Gf source = FLOOKUP G source /\
      op_taint tm (Var source) = op_taint tn (Var source) /\
      (!i. i < t.vs_alloca_next ==> (i IN tm.t_mem <=> i IN tn.t_mem)) /\
      abi_decode_ptr_window Gf tm u source ro (LENGTH (TAKE cap bs)) /\
      ptr_covers Gf tm output u (type_memory_bytes cenv rt) /\
      op_prov Gf hi = NONE /\ op_taint tm hi = {} /\
      alloca_history func u /\ allocas_from lo u /\
      wb_frame cenv es ee sa s0 u /\
      sa.cs_next_id <= hs.cs_next_id /\ sa.cs_next_var <= hs.cs_next_var /\
      s0.vs_alloca_next <= u.vs_alloca_next /\
      ghost_kept_at lo cenv es sa Gi ti si Gf tm /\
      immutable_frame_mods func cenv cx ee u
Proof
  strip_tac >> Cases_on `LENGTH bs < low`
  >- (drule_at (Pat `compile_return_value_decode _ _ _ = _`) extcall_return_size_route >>
      disch_then (drule_all_then mp_tac) >> asm_rewrite_tac[] >> strip_tac >>
      goal_assum (drule_at Any) >>
      Cases_on `evaluate_abi_decode_return (get_tenv cx) ret_type bs` >> simp[] >>
      drule_all return_default_source_success >>
      qpat_assum `rt = (if _ then _ else _)` (fn th => rewrite_tac[GSYM th]) >>
      qpat_assum `low = abi_static_length _` (fn th => rewrite_tac[GSYM th]) >>
      decide_tac) >>
  `low <= LENGTH bs` by decide_tac >>
  `LENGTH p.vs_returndata < dimword (:256)` by simp[] >>
  drule_all return_size_actual_run >>
  qpat_assum `p.vs_returndata = bs` (pure_rewrite_tac o single) >>
  qpat_assum `~(LENGTH bs < low)` (fn th => pure_rewrite_tac [th, COND_CLAUSES]) >>
  strip_tac >>
  rename1 `run_inst_seq (emitted_insts k hs) p = OK v` >>
  drule_all ext_size_success_exact_mods >>
  disch_then (qspecl_then [`tp`,`explicit`,`PG`,`Gp`] strip_assume_tac) >>
  rename1 `op_prov Gf hi = NONE` >> rename1 `op_taint tm hi = {}` >>
  qabbrev_tac `u = v with vs_inst_idx := LENGTH hs.cs_current_insts` >>
  `!x. not_fresh_at k x ==> lookup_var x u = lookup_var x p /\
    FLOOKUP Gf x = FLOOKUP Gp x /\ op_taint tm (Var x) = op_taint tp (Var x)` by
    (gen_tac >> disch_tac >> simp[] >>
     qpat_x_assum `!x. not_fresh_at k x ==> lookup_var x v = _`
       (qspec_then `x` mp_tac) >> simp[Abbr `u`, lookup_var_def]) >>
  qpat_x_assum `v = p with vs_vars := _`
    (strip_assume_tac o SRULE [venom_state_component_equality]) >>
  drule abi_return_size_code >> strip_tac >>
  `~u.vs_halted /\ u.vs_current_bb = hs.cs_current_bb /\
   u.vs_inst_idx = LENGTH hs.cs_current_insts /\
   u.vs_memory = p.vs_memory /\ u.vs_allocas = p.vs_allocas /\
   u.vs_alloca_next = p.vs_alloca_next /\ u.vs_data_section = p.vs_data_section /\
   u.vs_call_ctx = p.vs_call_ctx /\ u.vs_accounts = p.vs_accounts /\
   u.vs_transient = p.vs_transient /\ u.vs_immutables = p.vs_immutables` by
    fs[Abbr `u`, same_blocks_def] >>
  `allocas_from lo u` by
    (qpat_x_assum `allocas_from lo p` mp_tac >> simp[allocas_from_def]) >>
  `lookup_var source u = lookup_var source t /\
   FLOOKUP Gf source = FLOOKUP G source /\
   op_taint tm (Var source) = op_taint tn (Var source)` by simp[] >>
  `sa.cs_next_id <= hs.cs_next_id /\ sa.cs_next_var <= hs.cs_next_var` by
    (qspecl_then [`low`,`cap`,`k`] mp_tac ci_mono_compile_return_value_decode >>
     simp[ci_mono_def] >> decide_tac) >>
  `abi_static_size cenv.ce_struct_fields rt <= LENGTH bs` by metis_tac[] >>
  qexistsl_tac [`u`,`Gf`,`tm`] >> simp[] >>
  qpat_assum `rt = (if _ then _ else _)` (pure_rewrite_tac o single o GSYM) >>
  qpat_assum `cap = abi_size_bound _ _` (pure_rewrite_tac o single o GSYM) >>
  conj_tac
  >- (qx_gen_tac `D` >>
      qpat_assum `!D. gas_origin_ptr_path _ (t,G,tn) [] _`
        (qspec_then `D` (mp_tac o MATCH_MP gas_origin_ptr_path_append)) >> simp[]) >>
  conj_tac
  >- (qx_gen_tac `H` >> strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> _`
        (qspec_then `H` drule) >> strip_tac >>
      conj_tac
      >- (drule_all return_decode_ready_entry >> strip_tac >> gvs[Abbr `u`]) >>
      irule ghost_inv_at_mods_exterior_frame >>
      goal_assum (drule_at (Pat `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`)) >>
      qexists_tac `k` >> simp[]) >>
  conj_tac
  >- (irule extcall_clipped_ptr_window >> conj_tac
      >- (goal_assum (drule_at (Pat `FLOOKUP _ source = SOME _`)) >> simp[]) >>
      goal_assum (drule_at (Pat `FLOOKUP t.vs_allocas _ = SOME _`)) >>
      qexists_tac `tn` >> simp[]) >>
  conj_tac
  >- (irule ptr_covers_frame >> goal_assum (drule_at (Pat `ptr_covers _ _ _ _ _`)) >> simp[]) >>
  conj_tac
  >- (`gas_path_mem ctx func p 0 (OK u)` by
        (qpat_assum `!D. gas_origin_ptr_path _ (p,Gp,tp) [] _`
           (qspec_then `ARB` (mp_tac o MATCH_MP gas_origin_ptr_path_projections)) >>
         strip_tac >> drule gas_origin_path_erase >> simp[gas_marked_path_def]) >>
      irule gas_path_mem_zero_history >> simp[] >> qexistsl_tac [`ctx`,`p`] >>
      simp[] >> metis_tac[aggregate_mem_path_alloca_inv]) >>
  conj_tac
  >- (irule wb_frame_readonly_tail >>
      goal_assum (drule_at (Pat `wb_frame _ _ _ _ _ _`)) >> qexists_tac `k` >> simp[]) >>
  conj_tac
  >- (irule ghost_kept_at_clean_suffix >>
      goal_assum (drule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`)) >> simp[] >>
      qx_gen_tac `x` >> disch_tac >>
      `not_fresh_at k x` by
        (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
      simp[]) >>
  irule immutable_frame_mods_exterior_frame >>
  goal_assum (drule_at (Pat `immutable_frame_mods _ _ _ _ _`)) >>
  qexists_tac `k` >> simp[]
QED

Theorem extcall_size_window_mods:
  rt = (if needs_external_call_wrap ret_type then TupleT [ret_type] else ret_type) /\
  evaluate_type (get_tenv cx) ret_type = SOME tv /\
  low = abi_static_size cenv.ce_struct_fields rt /\
  low = abi_static_length (vyper_to_abi_type (get_tenv cx) rt) /\
  cap = abi_size_bound cenv.ce_struct_fields rt /\
  compile_return_value_decode low cap k = (hi,hs) /\ fn_has_code k hs func /\
  low < dimword (:256) /\ cap < dimword (:256) /\
  p.vs_returndata = bs /\ LENGTH bs < dimword (:256) /\
  ~p.vs_halted /\ (ctx_has_dalloca ctx ==> allocas_below_fmp p) /\ allocas_from lo p /\
  p.vs_current_bb = k.cs_current_bb /\ p.vs_inst_idx = LENGTH k.cs_current_insts /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK p,Gp,tp)) /\
  compile_abi_decode_to_buf (Var output) (Lit 0w) MLOAD (Var source) hi
    (type_to_abi_dec_info cenv.ce_struct_fields cenv rt) hs = ((),de) /\
  fn_has_code hs de func /\ fn_inst_ids_distinct func /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     abi_return_decode_ready H ctx func cenv cx ee k
       (abi_malformed_scratch_sites hs de func) dstid live (Var source) (Var output)
       (w2n ro) cap bs dest (type_memory_bytes cenv rt) p /\
     storage_well_formed_on cx ee (FST H) /\
     ghost_inv_at_mods (DF H) lo rb cenv cx ee Gp tp p) /\
  immutable_frame_mods func cenv cx ee p /\
  local_ptrs_reserved cenv k /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at k x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at k x) /\
  eval_operand (Var source) t = SOME ro /\
  FLOOKUP G source = SOME (prov_base,span) /\
  op_taint tn (Var source) = {} /\
  prov_base <= w2n ro /\ w2n ro + cap <= prov_base + span /\
  alloca_inv t /\ FLOOKUP t.vs_allocas live = SOME (w2n ro,bufsz) /\ cap <= bufsz /\
  (!i. w2n ro <= i /\ i < w2n ro + MIN cap (LENGTH bs) ==> i NOTIN tn.t_mem) /\
  lookup_var source p = lookup_var source t /\ FLOOKUP Gp source = FLOOKUP G source /\
  op_taint tp (Var source) = op_taint tn (Var source) /\
  (!i. i < t.vs_alloca_next ==> (i IN tp.t_mem <=> i IN tn.t_mem)) /\
  not_fresh_at k source /\ not_fresh_at k output /\
  ptr_covers Gp tp output p (type_memory_bytes cenv rt) /\
  alloca_history func p /\ alloca_inv p /\
  wb_frame cenv es ee sa s0 p /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_id <= dstid /\ dstid < sb.cs_next_id /\
  sa.cs_next_id <= k.cs_next_id /\ sa.cs_next_var <= k.cs_next_var /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  s0.vs_alloca_next <= p.vs_alloca_next /\
  ghost_kept_at lo cenv es sa G tn t Gp tp ==>
  if LENGTH bs < low then
    ?err z Gf tm. evaluate_abi_decode_return (get_tenv cx) ret_type bs = INR err /\
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (t,G,tn) [] (Abort Revert_abort z,Gf,tm))
  else
    ?u Gf tm. abi_static_size cenv.ce_struct_fields rt <= LENGTH bs /\
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK u,Gf,tm)) /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
         abi_malformed_entry H ctx func cenv cx ee hs (abi_malformed_scratch_sites hs de func)
           dstid live (Var source) hi (Lit 0w) (Var output) (w2n ro)
           (LENGTH (TAKE cap bs)) (TAKE cap bs) 0 dest (type_memory_bytes cenv rt) u /\
         storage_well_formed_on cx ee (FST H) /\
         ghost_inv_at_mods (DF H) lo rb cenv cx ee Gf tm u) /\
      ~u.vs_halted /\ u.vs_current_bb = hs.cs_current_bb /\
      u.vs_inst_idx = LENGTH hs.cs_current_insts /\
      lookup_var source u = lookup_var source t /\ FLOOKUP Gf source = FLOOKUP G source /\
      op_taint tm (Var source) = op_taint tn (Var source) /\
      (!i. i < t.vs_alloca_next ==> (i IN tm.t_mem <=> i IN tn.t_mem)) /\
      abi_decode_ptr_window Gf tm u source ro (LENGTH (TAKE cap bs)) /\
      ptr_covers Gf tm output u (type_memory_bytes cenv rt) /\
      op_prov Gf hi = NONE /\ op_taint tm hi = {} /\
      alloca_history func u /\ allocas_from lo u /\
      wb_frame cenv es ee sa s0 u /\
      sa.cs_next_id <= hs.cs_next_id /\ sa.cs_next_var <= hs.cs_next_var /\
      s0.vs_alloca_next <= u.vs_alloca_next /\
      ghost_kept_at lo cenv es sa G tn t Gf tm /\
      immutable_frame_mods func cenv cx ee u
Proof
  MATCH_ACCEPT_TAC extcall_size_window_kept_mods
QED

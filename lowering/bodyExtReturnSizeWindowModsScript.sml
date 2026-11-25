(* The source window uses the copied length, not the size of returndata. *)
Theory bodyExtReturnSizeWindowMods
Ancestors
  bodyFullExtCallReturnSizeRoute bodyForRangeScalarFrameMods
  abiDecodePtrMemberFrame extcallReturnDefaultTypes
  bodyFullPostsMods bodyFullShadowBodyInv
  bodyPtrDefs ptrDiscipline venomState venomMemDefs
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
  strip_tac >>
  drule_at (Pat `compile_return_value_decode _ _ _ = _`) extcall_return_size_route >>
  disch_then (drule_all_then mp_tac) >>
  Cases_on `LENGTH bs < low`
  >- (asm_rewrite_tac[] >> strip_tac >>
      goal_assum (drule_at Any) >>
      Cases_on `evaluate_abi_decode_return (get_tenv cx) ret_type bs` >> simp[] >>
      drule_all return_default_source_success >>
      qpat_assum `rt = (if _ then _ else _)` (fn th => rewrite_tac[GSYM th]) >>
      qpat_assum `low = abi_static_length _` (fn th => rewrite_tac[GSYM th]) >>
      decide_tac) >>
  FAIL_TAC "size route success"
QED

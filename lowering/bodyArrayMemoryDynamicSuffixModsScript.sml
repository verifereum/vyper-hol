(* Counted selection from a reached dynamic memory place. *)
Theory bodyArrayMemoryDynamicSuffixMods
Ancestors
  bodyArrayNoCopyCutsMods bodyFullSubscriptCapturedDynamicRun
  exprSimSubscriptArraySource bodyFullTargetArrayLoad loweringPosts
  bodyPtrSignedConvertSourceFrame bodyForRangeScalarFrameMods
  bodyFullUnwrapRun bodyFullHashKeccakFixed gasOutcomeFullPostMods
  exprSimHash exprSimWordArgs exprSimProps exprSimMemDefs exprOperandVar
  exprLoweringProps valueEncodingProps ptrDiscipline bodyPtrDefs
  vyperAST vyperState vyperStorageFootprint venomState words
  context exprLowering vyperInterpreter vyperValue vyperTypeSystem vyperTyping
  venomInst fragExec gasExplicitSites loweringStateRelDefs bodyFullPostsMods
  freshWrites exprSimDefs

Theorem dynamic_place_fields[local]:
  evaluate_type (get_tenv cx) et = SOME tv /\
  value_has_type tv v /\ read_result cx r fin = (INL v,fin) /\
  eval_operand dst q = SOME w /\ op_taint tm dst = {} /\
  op_prov Gq dst = SOME (b,sz) /\ b <= w2n w /\
  w2n w + type_memory_size tv <= b + sz /\
  w2n w + type_memory_size tv <= q.vs_alloca_next /\
  type_memory_bytes ce et = type_memory_size tv /\
  (!m. mem_agree_outside tm.t_mem q.vs_memory m ==>
       val_in_memory tv v (w2n w) m) ==>
  vv_holds ce cx et r (LocatedValue et (mk_ptr dst LocMemory)) fin q /\
  ptr_vv_ok cx et r (LocatedValue et (mk_ptr dst LocMemory)) fin Gq tm q /\
  vv_store_bound cx et et fin r (LocatedValue et (mk_ptr dst LocMemory)) q /\
  ptr_buf_ok ce (Subscript et obj idx) dst Gq q
Proof
  strip_tac >>
  `val_wf tv v` by metis_tac[valueEncodingTypingTheory.value_has_type_val_wf] >>
  `val_store_size tv v <= type_memory_size tv` by simp[val_store_size_le] >>
  `val_in_memory tv v (w2n w) q.vs_memory` by simp[mem_agree_outside_def] >>
  conj_tac
  >- (simp[vv_holds_def, mk_ptr_def] >> metis_tac[val_in_memory_word_type]) >>
  Cases_on `dst` >> gvs[op_prov_def] >>
  simp[ptr_vv_ok_def, ptr_mem_ok_def, ptr_buf_ok_def, mk_ptr_def,
       vv_store_bound_def, lowered_value_type_def, expr_type_def]
QED

Theorem dynamic_place_geometry[local]:
  evaluate_type (get_tenv cx) et = SOME tv /\
  read_result cx (PlaceR (MemoryPlace id path)) fin = (INL v,fin) /\
  value_has_type tv v /\ lookup_scopes id fin.scopes = SOME entry /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var root) ssz) /\
  lookup_var root q = SOME bw /\
  ce.ce_var_type id = SOME rt /\ evaluate_type (get_tenv cx) rt = SOME entry.type /\
  mem_path_offset entry.type path = SOME (k,tv) /\
  eval_operand dst q = SOME w /\ w2n w = w2n bw + k /\
  k + type_memory_size tv <= ssz ==>
  vv_at ce cx et sa sb fin (PlaceR (MemoryPlace id path))
    (LocatedValue et (mk_ptr dst LocMemory)) q /\
  vv_place_ptr_mods ce cx fin q (PlaceR (MemoryPlace id path))
    (LocatedValue et (mk_ptr dst LocMemory))
Proof
  strip_tac >>
  `val_wf tv v` by metis_tac[valueEncodingTypingTheory.value_has_type_val_wf] >>
  drule_then assume_tac val_footprint_le >>
  conj_tac
  >- (simp[vv_at_def, mk_ptr_def] >>
      disj2_tac >> disj1_tac >> qexistsl [`id`,`w2n bw`,`ssz`] >>
      simp[local_region_def, local_val_at_def, local_place_at_def, local_path_at_def] >>
      `w2n w - w2n bw = k` by decide_tac >>
      simp[] >> disj1_tac >> qexists `path` >> simp[]) >>
  `w = bw + n2w k` by
    (qpat_assum `w2n w = _` (mp_tac o Q.AP_TERM `n2w : num -> 256 word`) >>
     rewrite_tac[GSYM word_add_n2w, n2w_w2n]) >>
  simp[vv_place_ptr_mods_def, vv_place_ptr_def, mk_ptr_def] >> metis_tac[]
QED

Theorem dynamic_suffix_frame[local]:
  array_length_frame sn u G tn q Gq tm /\
  sa.cs_next_var <= sn.cs_next_var /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  stmt_state_rel hor ctx fn ce cx fin u /\ immutable_frame_mods fn ce cx fin u /\
  wb_frame ce es fin sa s0 u /\ (~expr_has_effect e ==> pure_frame ce fn es sa s0 u) /\
  ghost_inv_at_mods D lo d ce cx fin G tn u /\ ghost_kept_at lo ce es sa G0 tn0 s0 G tn ==>
  stmt_state_rel hor ctx fn ce cx fin q /\ immutable_frame_mods fn ce cx fin q /\
  wb_frame ce es fin sa s0 q /\ (~expr_has_effect e ==> pure_frame ce fn es sa s0 q) /\
  ghost_inv_at_mods D lo d ce cx fin Gq tm q /\ ghost_kept_at lo ce es sa G0 tn0 s0 Gq tm
Proof
  simp[array_length_frame_def] >> strip_tac >>
  `q = u with <|vs_vars := q.vs_vars; vs_inst_idx := q.vs_inst_idx|>` by
    (qpat_assum `q with <|vs_vars := _; vs_inst_idx := _|> = u`
       (fn th => CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [GSYM th]))) >> simp[]) >>
  `q.vs_memory = u.vs_memory /\ q.vs_allocas = u.vs_allocas /\
   q.vs_alloca_next = u.vs_alloca_next /\ q.vs_data_section = u.vs_data_section /\
   q.vs_call_ctx = u.vs_call_ctx /\ q.vs_accounts = u.vs_accounts /\
   q.vs_transient = u.vs_transient /\ q.vs_immutables = u.vs_immutables` by
    (qpat_assum `q = u with <|vs_vars := _; vs_inst_idx := _|>`
       (fn th => once_rewrite_tac [th]) >> simp[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x u /\
        FLOOKUP Gq x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >>
     `not_fresh_at sn x` by metis_tac[not_fresh_at_mono] >> simp[op_taint_def]) >>
  conj_tac
  >- (irule stmt_state_rel_readonly_vars_pc >> qexistsl [`u`,`sa`] >> simp[]) >>
  conj_tac
  >- (irule immutable_frame_mods_exterior_frame >> qexistsl [`fin`,`u`,`sa`] >> simp[]) >>
  conj_tac
  >- (irule wb_frame_readonly_tail >> qexistsl [`sa`,`u`] >> simp[]) >>
  conj_tac >- (strip_tac >> irule pure_frame_mem_tail >> qexists `u` >> simp[]) >>
  conj_tac
  >- (irule ghost_inv_at_mods_exterior_frame >> qexistsl [`G`,`fin`,`u`,`sa`,`tn`] >> simp[]) >>
  irule ghost_kept_at_clean_suffix >> qexistsl [`G`,`tn`] >> simp[]
QED

Theorem dynamic_place_post[local]:
  stmt_state_rel H ctx fn ce cx fin q /\ immutable_frame_mods fn ce cx fin q /\
  storage_well_formed_on cx fin (FST H) /\
  vv_holds ce cx et (PlaceR (MemoryPlace id path)) (LocatedValue et (mk_ptr dst LocMemory)) fin q /\
  vv_at ce cx et sa sb fin (PlaceR (MemoryPlace id path)) (LocatedValue et (mk_ptr dst LocMemory)) q /\
  vv_place_ptr_mods ce cx fin q (PlaceR (MemoryPlace id path)) (LocatedValue et (mk_ptr dst LocMemory)) /\
  wb_frame ce es fin sa s0 q /\
  (~expr_has_effect (Subscript et obj idx) ==> pure_frame ce fn es sa s0 q) ==>
  vv_post_mods H ctx fn ce cx (Subscript et obj idx) es sa sb s0 fin
    (PlaceR (MemoryPlace id path)) (LocatedValue et (mk_ptr dst LocMemory)) q
Proof
  simp[vv_post_mods_def, wb_frame_def, vv_holds_mods_def, expr_type_def, mk_ptr_def] >>
  strip_tac >> simp[]
QED

Theorem array_memory_dynamic_suffix_mods:
  compile_array_subscript bop iop T cnt 32 (type_memory_size tv)
    (is_signed_type (expr_type idx)) (\op. emit_op MLOAD [op]) sn = (dst,sb) /\
  fn_has_code sn sb fn /\
  eval_operand bop u = SOME a /\ eval_operand iop u = SOME iw /\
  i = (if is_signed_type (expr_type idx) then w2i iw else &(w2n iw)) /\
  evaluate_type (get_tenv cx) et = SOME tv /\
  lookup_scopes id fin.scopes = SOME entry /\
  subscripts_type entry.type path = SOME (ArrayTV tv (Dynamic cap)) /\
  read_memory_path entry path = INL (ArrayV (DynArrayV vs)) /\
  value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  LENGTH vs < dimword (:256) /\
  (!m. mem_agree_outside tn.t_mem u.vs_memory m ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n a) m) /\
  op_prov G bop = SOME (b,sz) /\ op_prov G iop = NONE /\ b <= w2n a /\
  w2n a + (32 + cap * type_memory_size tv) <= b + sz /\
  w2n a + (32 + cap * type_memory_size tv) < dimword (:256) /\
  w2n a + (32 + cap * type_memory_size tv) <= u.vs_alloca_next /\
  op_taint tn bop = {} /\ op_taint tn iop = {} /\
  mem_word_taint tn.t_mem (w2n a) = {} /\
  (!x. bop = Var x ==> not_fresh_at sn x) /\
  (!x. iop = Var x ==> not_fresh_at sn x) /\
  allocas_from lo u /\ alloca_history fn u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\ ~u.vs_halted /\
  u.vs_current_bb = sn.cs_current_bb /\ u.vs_inst_idx = LENGTH sn.cs_current_insts /\
  type_memory_bytes ce et = type_memory_size tv /\
  (0 <= i /\ Num i < LENGTH vs ==>
    ?v root ssz bw rt k.
      read_result cx (PlaceR (MemoryPlace id (path ++ [ValueSubscript (IntV i)]))) fin =
        (INL v,fin) /\ value_has_type tv v /\
      (!m. mem_agree_outside tn.t_mem u.vs_memory m ==>
        val_in_memory tv v (w2n a + 32 + Num i * type_memory_size tv) m) /\
      FLOOKUP ce.ce_vars id = SOME (PtrVar (Var root) ssz) /\
      lookup_var root u = SOME bw /\
      ce.ce_var_type id = SOME rt /\ evaluate_type (get_tenv cx) rt = SOME entry.type /\
      mem_path_offset entry.type (path ++ [ValueSubscript (IntV i)]) = SOME (k,tv) /\
      w2n a + 32 + Num i * type_memory_size tv = w2n bw + k /\
      k + type_memory_size tv <= ssz) /\
  sa.cs_next_var <= sn.cs_next_var /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  s0.vs_alloca_next <= u.vs_alloca_next /\
  storage_trace_domain cx st0 fin.storage_trace /\ fin.gas_obs = [] /\
  wb_frame ce es fin sa s0 u /\ ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
  (~expr_has_effect (Subscript et obj idx) ==> pure_frame ce fn es sa s0 u) /\
  (!H. valid_horizon cx st0 H fin.storage_trace ==>
    stmt_state_rel H ctx fn ce cx fin u /\ immutable_frame_mods fn ce cx fin u /\
    storage_well_formed_on cx fin (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx fin G tn u) ==>
  array_select_outcome_mods (DF,lo,d,ctx,shadow_ctx,PG,fn) ce cx et obj idx et (Dynamic cap) st0
    (es,s0,G0,tn0) (sa,sb,dst,LocMemory) (PlaceR (MemoryPlace id path),IntV i) (fin,u,G,tn)
Proof
  DISCH_THEN (MAP_EVERY assume_tac o CONJUNCTS) >>
  `w2n a + 32 <= u.vs_alloca_next` by decide_tac >>
  drule_all subscript_captured_dynamic_execution >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`] strip_assume_tac) >>
  qpat_x_assum `i = if _ then _ else _` kall_tac >>
  qabbrev_tac `child = PlaceR (MemoryPlace id (path ++ [ValueSubscript (IntV i)]))` >>
  `!gs. select_result cx (ArrayT et (Dynamic cap)) (PlaceR (MemoryPlace id path))
         (ValueSubscript (IntV i)) (fin with gas_obs := gs) =
       (if idx_in_range (is_signed_type (expr_type idx)) iw (n2w (LENGTH vs)) then
          INL child else INR (Error (RuntimeError "evaluate_subscripts array_index")),
        fin with gas_obs := gs)` by
    (gen_tac >>
     `lookup_scopes id (fin with gas_obs := gs).scopes = SOME entry` by simp[] >>
     drule_all_then assume_tac (Q.INST [`ty` |-> `ArrayT et (Dynamic cap)`,
                                       `sb` |-> `ValueSubscript (IntV i)`] select_memory_result) >>
     Cases_on `idx_in_range (is_signed_type (expr_type idx)) iw (n2w (LENGTH vs))` >>
     gvs[Abbr `child`, bind_def, return_def, lift_sum_def, raise_def]) >>
  `fin with gas_obs := [] = fin` by simp[evaluation_state_component_equality] >>
  rewrite_tac[array_select_outcome_mods_def, LET_THM] >> BETA_TAC >>
  reverse (Cases_on `idx_in_range (is_signed_type (expr_type idx)) iw (n2w (LENGTH vs))`)
  >- suspend "reject" >>
  suspend "accept"
QED

Resume array_memory_dynamic_suffix_mods[reject]:
  fs[] >> irule gas_outcome_full_mods_exit >> simp[] >>
  qexistsl [`H`,`fin`,`Abort Revert_abort q`,
            `INR (Error (RuntimeError "evaluate_subscripts array_index"))`,`tm`] >>
  simp[exit_result_def, expr_exit_def, halt_exit_def]
QED

Resume array_memory_dynamic_suffix_mods[accept]:
  fs[] >>
  `q.vs_alloca_next = u.vs_alloca_next /\ q.vs_memory = u.vs_memory /\ tm.t_mem = tn.t_mem` by
    (fs[array_length_frame_def] >>
     qpat_assum `q with <|vs_vars := _; vs_inst_idx := _|> = u`
       (fn th => once_rewrite_tac [GSYM th]) >> simp[]) >>
  `LENGTH vs <= cap` by fs[vyperTypingTheory.value_has_type_def] >>
  `SUC (Num i) * type_memory_size tv <= cap * type_memory_size tv` by
    (irule arithmeticTheory.LESS_MONO_MULT >> decide_tac) >>
  `w2n a + 32 + Num i * type_memory_size tv + type_memory_size tv <= u.vs_alloca_next` by
    (qpat_assum `SUC (Num i) * _ <= _` mp_tac >>
     rewrite_tac[arithmeticTheory.MULT_CLAUSES] >> decide_tac) >>
  qabbrev_tac `w = a + 32w + iw * n2w (type_memory_size tv)` >>
  `b <= w2n w /\ w2n w + type_memory_size tv <= b + sz /\
   w2n w + type_memory_size tv <= q.vs_alloca_next` by (rpt conj_tac >> decide_tac) >>
  rename1 `lookup_var row_var u = SOME (row_word:256 word)` >>
  `!m. mem_agree_outside tm.t_mem q.vs_memory m ==> val_in_memory tv v (w2n w) m` by
    (qpat_assum `q.vs_memory = _` SUBST1_TAC >> qpat_assum `tm.t_mem = _` SUBST1_TAC >>
     qpat_assum `w2n w = _` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `read_result cx child fin = (INL v,fin)` by simp[Abbr `child`] >>
  drule_all_then (qspecl_then [`obj`,`idx`] strip_assume_tac) dynamic_place_fields >>
  `lookup_var row_var q = SOME row_word` by
    (`local_ptrs_reserved ce sn` by metis_tac[local_ptrs_reserved_next_var] >>
     drule_all_then assume_tac environment_var_not_fresh >> fs[array_length_frame_def]) >>
  `w2n w = w2n row_word + k` by decide_tac >>
  `read_result cx (PlaceR (MemoryPlace id (path ++ [ValueSubscript (IntV i)]))) fin =
      (INL v,fin)` by gvs[Abbr `child`] >>
  drule_all_then (qspecl_then [`sb`,`sa`] strip_assume_tac) dynamic_place_geometry >>
  irule gas_outcome_full_mods_pure >> simp[] >>
  qexistsl [`H`,`fin`,`INL child`,`q`,`tm`] >> simp[] >>
  qx_gen_tac `hor` >> disch_tac >>
  qpat_assum `!h. valid_horizon _ _ h _ ==> _`
    (qspec_then `hor` (strip_assume_tac o UNDISCH)) >>
  drule_all_then strip_assume_tac
    (SIMP_RULE (srw_ss()) [] (Q.INST [`e` |-> `Subscript et obj idx`] dynamic_suffix_frame)) >>
  qpat_assum `stmt_state_rel hor _ _ _ _ _ q`
    (mp_then Any assume_tac stmt_state_rel_allocas_below_fmp) >>
  `vv_post_mods hor ctx fn ce cx (Subscript et obj idx) es sa sb s0 fin child
       (LocatedValue et (mk_ptr dst LocMemory)) q` by
    (gvs[Abbr `child`] >> irule dynamic_place_post >> simp[]) >>
  `vv_location (LocatedValue et (mk_ptr dst LocMemory)) = SOME LocMemory` by
    simp[vv_location_def, mk_ptr_def] >>
  `(mk_ptr dst LocMemory).ptr_operand = dst` by simp[mk_ptr_def] >>
  simp[Abbr `child`, lowered_value_type_def, expr_type_def] >>
  rpt strip_tac >> gvs[Abbr `child`]
QED

Finalise array_memory_dynamic_suffix_mods

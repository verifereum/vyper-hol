(* Preserve the linked RawCreate window through the final length ADD.
   With no constructor arguments the saved bytecode window suffices. *)
Theory bodyCreateRawWindowMods
Ancestors
  bodyFullCreateHeld bodyFullExtCallDirectState bodyForRangeScalarFrameMods
  decoderNavigationPtr assignTuplePtrLoadStep assignTuplePtrCopyLen
  bodyFullUnwrapRun bodyFullPathHistory exprSimWordArgs
  emitHelperProps loweringShapeRules exprLoweringProps
  bodyFullPostsMods bodyFullShadowBodyInv bodyMemoryDefs bodyPtrDefs
  fragGasOriginPtr fragExec freshWrites stateFrame
  venomExecSemantics venomInst venomState ptrDiscipline words arithmetic list finite_map
  vyperStorageFootprint loweringPosts

Theorem raw_total_length_step[local]:
  emit_op ADD [left;right] a = (dst,b) /\ fn_has_code a b func /\
  eval_operand left z = SOME l /\ eval_operand right z = SOME r /\
  op_taint tz left = {} /\ op_taint tz right = {} /\
  op_prov Gz left = NONE /\ op_prov Gz right = NONE /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\ allocas_from lo z /\
  ~z.vs_halted /\ z.vs_current_bb = a.cs_current_bb /\
  z.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?out t Gt tt. dst = Var out /\ not_fresh_at b out /\
    t = (update_var out (l+r) z with vs_inst_idx := LENGTH b.cs_current_insts) /\
    t.vs_current_bb = b.cs_current_bb /\ eval_operand dst t = SOME (l+r) /\
    op_taint tt dst = {} /\ op_prov Gt dst = NONE /\
    tt.t_mem = tz.t_mem /\ tt.t_stor = tz.t_stor /\
    tt.t_trans = tz.t_trans /\ tt.t_imm = tz.t_imm /\
    (!x. not_fresh_at a x ==> lookup_var x t = lookup_var x z /\
      FLOOKUP Gt x = FLOOKUP Gz x /\ op_taint tt (Var x) = op_taint tz (Var x)) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (z,Gz,tz) [] (OK t,Gt,tt))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule emitted_insts_emit_op >> strip_tac >>
  rename1 `dst = Var out` >>
  qabbrev_tac `u = update_var out (l+r) z` >>
  `run_inst_seq (emitted_insts a b) z = OK u` by
    simp[Abbr `u`,run_inst_seq_def,step_inst_base_opcode_eqs,mk_inst_def,exec_pure2_def] >>
  drule_all (SIMP_RULE bool_ss [] (Q.SPEC `ADD` emit_scalar_binop_endpoint_ptr_origin_core_exact_frame)) >>
  disch_then (qspecl_then [`H`,`cx`,`ctx`,`PG`,`R`] strip_assume_tac) >>
  rename1 `op_taint tt dst = {}` >> rename1 `op_prov gf dst = NONE` >>
  `a.cs_current_bb = b.cs_current_bb` by (drule emit_op_same_blocks >> simp[same_blocks_def]) >>
  `~not_fresh_at a out /\ not_fresh_at b out` by
    (qpat_assum `emit_op ADD _ a = _` (mp_tac o MATCH_MP emitted_insts_emit_op) >>
     strip_tac >> gvs[] >> metis_tac[fresh_output_props]) >>
  `!x. not_fresh_at a x ==> out <> x` by metis_tac[] >>
  qexistsl [`out`,`u with vs_inst_idx := LENGTH b.cs_current_insts`,`gf`,`tt`] >>
  simp[Abbr `u`,update_var_def,lookup_var_def,eval_operand_def,FLOOKUP_UPDATE,
       loweringShapeRulesTheory.fresh_output_props] >>
  rpt strip_tac >>
  qpat_assum `!D lo expl C f. _ ==> gas_origin_ptr_path _ _ _ _` irule >>
  simp[]
QED

(* The reference encoder landing supplies the concatenated bytes. This edge
   turns the two scalar lengths into the actual dispatch length, without
   changing any window or linked frame at the landing. *)
Theorem raw_create_total_window_mods:
  emit_op ADD [Var root;len] sm = (Var dst,st) /\ fn_has_code sm st func /\
  compile_abi_encode_values_to_buf ce (Var dst) rows st = (alen,en) /\
  fn_has_code st en func /\ emit_op ADD [len;alen] en = (total_op,sb) /\ fn_has_code en sb func /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (initial,Gi,ti) [] (OK z,Gz,tz)) /\
  abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst (LENGTH bs) bs en z Gz tz /\
  local_ptrs_reserved ce se /\ fn_inst_ids_distinct func /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  return_buf_frame d ce se s /\
  (!x. len = Var x ==> not_fresh_at se x) /\ (!l. len <> Label l) /\
  eval_operand len s = SOME (n2w (LENGTH bs)) /\ op_taint tn len = {} /\ op_prov G len = NONE /\
  eval_operand alen z = SOME (n2w (LENGTH args_bytes)) /\ op_taint tz alen = {} /\
  LENGTH bs + LENGTH args_bytes <= capacity /\
  read_memory pbase (LENGTH (bs ++ args_bytes)) z = bs ++ args_bytes /\
  (!i. pbase <= i /\ i < pbase + LENGTH (bs ++ args_bytes) ==> i NOTIN tz.t_mem) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
       ghost_inv_at_mods (DF H) lo d ce cx ee Gz tz z /\
       immutable_frame_mods func ce cx ee z) ==>
  ?out t gf tf. total_op = Var out /\ not_fresh_at sb out /\ not_fresh_at sb root /\
    shared < sb.cs_next_id /\ FLOOKUP t.vs_allocas shared = SOME (pbase,capacity) /\
    lookup_var root t = SOME (n2w pbase) /\ ptr_covers gf tf root t capacity /\
    pbase + capacity <= t.vs_alloca_next /\ pbase + capacity < dimword (:256) /\
    LENGTH (bs ++ args_bytes) <= capacity /\ LENGTH (bs ++ args_bytes) < dimword (:256) /\
    eval_operand total_op t = SOME (n2w (LENGTH (bs ++ args_bytes))) /\
    op_taint tf total_op = {} /\ op_prov gf total_op = NONE /\
    read_memory pbase (LENGTH (bs ++ args_bytes)) t = bs ++ args_bytes /\
    (!i. pbase <= i /\ i < pbase + LENGTH (bs ++ args_bytes) ==> i NOTIN tf.t_mem) /\
    wb_frame ce ee ee se s t /\ ghost_kept_at lo ce ee se G tn s gf tf /\
    return_buf_frame d ce sb t /\ alloca_history func t /\ allocas_from lo t /\
    lo <= t.vs_alloca_next /\ s.vs_alloca_next <= t.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func ce cx ee t /\ storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at_mods (DF H) lo d ce cx ee gf tf t /\
      immutable_frame_mods func ce cx ee t) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (z,Gz,tz) [] (OK t,gf,tf))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  drule abi_encode_saved_state_resources >>
  (impl_tac >- (qexists `storage_trace_horizon ee.storage_trace` >> first_assum ACCEPT_TAC)) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `abi_encode_saved_state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [abi_encode_saved_state_def]) >>
  `op_prov Gz alen = NONE` by
    (qpat_assum `!D. gas_origin_ptr_path _ (initial,Gi,ti) [] _`
       (qspec_then `DF (storage_trace_horizon ee.storage_trace)` assume_tac) >>
     irule create_encoded_length_no_prov >>
     qpat_assum `emit_op ADD [Var root;len] sm = (Var dst,st)` (irule_at Any) >>
     qpat_assum `compile_abi_encode_values_to_buf _ _ _ _ = _` (irule_at Any) >>
     qpat_assum `gas_origin_ptr_path _ (initial,Gi,ti) [] (OK z,Gz,tz)` (irule_at Any) >> simp[]) >>
  suspend "length"
QED

Resume raw_create_total_window_mods[length]:
  `eval_operand len z = SOME (n2w (LENGTH bs)) /\ op_taint tz len = {} /\ op_prov Gz len = NONE` by
    (Cases_on `len` >> gvs[wb_frame_def,ghost_kept_at_def,eval_operand_def,op_taint_def,op_prov_def] >>
     metis_tac[]) >>
  `pbase + capacity <= z.vs_alloca_next` by
    (irule allocaSiteResourceTheory.alloca_site_registered_below >> conj_tac
     >- first_assum ACCEPT_TAC >> qexists `shared` >> first_assum ACCEPT_TAC) >>
  `pbase + capacity < dimword (:256)` by
    (irule LESS_EQ_LESS_TRANS >> qexists `z.vs_alloca_next` >>
     simp[] >> drule_all_then ACCEPT_TAC alloca_room_next_lt) >>
  `LENGTH (bs ++ args_bytes) < dimword (:256)` by
    (qpat_assum `pbase+capacity < dimword (:256)` mp_tac >>
     qpat_assum `LENGTH bs + LENGTH args_bytes <= capacity` mp_tac >>
     rewrite_tac[LENGTH_APPEND] >> numLib.ARITH_TAC) >>
  drule_all raw_total_length_step >> disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  suspend "finish"
QED

Resume raw_create_total_window_mods[finish]:
  rename1 `op_prov gf total_op = NONE` >>
  rename1 `op_taint tf total_op = {}` >>
  `ci_mono en sb` by (qspecl_then [`ADD`,`[len;alen]`,`en`] mp_tac ci_mono_emit_op >> simp[]) >>
  `en.cs_next_var <= sb.cs_next_var /\ en.cs_next_id <= sb.cs_next_id` by fs[ci_mono_def] >>
  `t.vs_memory = z.vs_memory /\ t.vs_data_section = z.vs_data_section /\
   t.vs_allocas = z.vs_allocas /\ t.vs_alloca_next = z.vs_alloca_next /\
   t.vs_call_ctx = z.vs_call_ctx /\ t.vs_accounts = z.vs_accounts /\
   t.vs_transient = z.vs_transient /\ t.vs_immutables = z.vs_immutables /\
   ~t.vs_halted /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
   allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
   state_frame t = state_frame (z with vs_inst_idx := t.vs_inst_idx)` by
    (qpat_assum `t = _` SUBST1_TAC >>
     simp[update_var_def,allocas_from_def,allocas_below_fmp_def,state_frame_def]) >>
  `lookup_var root t = SOME (n2w pbase) /\ ptr_covers gf tf root t capacity` by
    (qpat_assum `!x. not_fresh_at en x ==> _`
       (qspec_then `root` (drule_then strip_assume_tac)) >>
     conj_tac >- fs[eval_operand_def] >>
     irule ptr_covers_lookup_frame >>
     qpat_assum `ptr_covers Gz tz root z capacity` (irule_at Any) >> simp[]) >>
  `!x. not_fresh_at se x ==> not_fresh_at en x` by metis_tac[not_fresh_at_mono] >>
  `wb_frame ce ee ee se s t` by
    (irule wb_frame_readonly_tail >> qpat_assum `wb_frame ce ee ee se s z` (irule_at Any) >>
     qexists `en` >> simp[IgnAsm `t = _`] >> rpt strip_tac >>
     qpat_assum `!x. not_fresh_at en x ==> _` (drule_then strip_assume_tac) >> simp[]) >>
  `ghost_kept_at lo ce ee se G tn s gf tf` by
    (irule ghost_kept_at_clean_suffix >>
     qpat_assum `ghost_kept_at lo ce ee se G tn s Gz tz` (irule_at Any) >>
     simp[] >> rpt strip_tac >>
     qpat_assum `!x. not_fresh_at se x ==> not_fresh_at en x` (drule_then assume_tac) >>
     qpat_assum `!x. not_fresh_at en x ==> _` (drule_then strip_assume_tac) >> simp[]) >>
  suspend "framed"
QED

Resume raw_create_total_window_mods[framed]:
  `se.cs_next_var <= sb.cs_next_var` by (irule LESS_EQ_TRANS >> qexists `en.cs_next_var` >> simp[]) >>
  `return_buf_frame d ce sb t` by
    (irule return_buf_frame_frame >>
     qpat_assum `return_buf_frame d ce se s` (irule_at Any) >>
     simp[IgnAsm `t = _`] >> rpt strip_tac >>
     irule wb_frame_vars >> qexistsl [`ce`,`ee`,`ee`,`s`,`se`] >> simp[]) >>
  `alloca_history func t` by
    (irule body_full_path_alloca_history >>
     qpat_assum `!D. gas_origin_ptr_path _ (z,Gz,tz) [] (OK t,gf,tf)`
       (qspec_then `DF (storage_trace_horizon ee.storage_trace)` (irule_at Any)) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `local_ptrs_reserved ce en` by metis_tac[local_ptrs_reserved_next_var] >>
  `(!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at en x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at en x)` by metis_tac[] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee t /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at_mods (DF H) lo d ce cx ee gf tf t /\ immutable_frame_mods func ce cx ee t` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!H. _ ==> stmt_state_rel H _ _ _ _ _ z /\ _` (drule_then strip_assume_tac) >>
     qpat_assum `!H. _ ==> ghost_inv_at_mods (DF H) _ _ _ _ _ _ _ z /\ _` (drule_then strip_assume_tac) >>
     conj_tac
     >- (irule stmt_state_rel_old_vars_frame_ptr >> qpat_assum `state_frame t = _` (irule_at Any) >>
         qexists `en` >> simp[IgnAsm `t = _`]) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac
     >- (irule ghost_inv_at_mods_exterior_frame >>
         qpat_assum `ghost_inv_at_mods (DF H) _ _ _ _ _ _ _ z` (irule_at Any) >>
         qexists `en` >> simp[IgnAsm `t = _`]) >>
     irule immutable_frame_mods_exterior_frame >>
     qpat_assum `immutable_frame_mods func ce cx ee z` (irule_at Any) >>
     qexists `en` >> simp[IgnAsm `t = _`]) >>
  `not_fresh_at sb root` by metis_tac[not_fresh_at_mono] >>
  `shared < sb.cs_next_id` by (irule LESS_LESS_EQ_TRANS >> qexists `en.cs_next_id` >> simp[]) >>
  `read_memory pbase (LENGTH (bs ++ args_bytes)) t = bs ++ args_bytes` by
    fs[IgnAsm `t = _`,read_memory_def] >>
  qexistsl [`out`,`t`,`gf`,`tf`] >>
  simp[IgnAsm `t = _`,LENGTH_APPEND,word_add_n2w] >>
  rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ t /\ _`
    (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC
QED

Finalise raw_create_total_window_mods

(* No encoder is run: dispatch from the payload already owned by the
   length-prefixed bytecode snapshot, after the scalar suffix. *)
Theorem raw_create_no_ctor_window_mods:
  stmt_state_rel H ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [root] /\ not_local_ptr ce es.scopes root /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (pbase,cap) /\ inst.inst_id < sa.cs_next_id /\
  pbase + cap <= s.vs_alloca_next /\ s.vs_alloca_next <= t.vs_alloca_next /\
  pbase + cap < dimword (:256) /\ 32 + LENGTH bs <= cap /\
  not_fresh_at sa p /\ lookup_var p s = SOME (n2w (pbase + 32)) /\
  ptr_covers G tn p s (LENGTH bs) /\ op_taint tn (Var p) = {} /\
  (!x. len = Var x ==> not_fresh_at sa x) /\ (!l. len <> Label l) /\
  eval_operand len s = SOME (n2w (LENGTH bs)) /\ op_taint tn len = {} /\ op_prov G len = NONE /\
  read_memory (pbase + 32) (LENGTH bs) s = bs /\
  (!i. pbase + 32 <= i /\ i < pbase + 32 + LENGTH bs ==> i NOTIN tn.t_mem) /\
  wb_frame ce es ef sa s t /\ ghost_kept_at lo ce es sa G tn s Gtail tt ==>
  FLOOKUP t.vs_allocas inst.inst_id = SOME (pbase,cap) /\
  lookup_var p t = SOME (n2w (pbase + 32)) /\
  ptr_covers Gtail tt p t (LENGTH bs) /\ op_taint tt (Var p) = {} /\
  eval_operand len t = SOME (n2w (LENGTH bs)) /\ op_taint tt len = {} /\ op_prov Gtail len = NONE /\
  pbase + 32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
  pbase + 32 + LENGTH bs <= t.vs_alloca_next /\
  read_memory (pbase + 32) (LENGTH bs) t = bs /\
  (!i. pbase + 32 <= i /\ i < pbase + 32 + LENGTH bs ==> i NOTIN tt.t_mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `pbase + 32 < dimword (:256) /\ LENGTH bs < dimword (:256)` by
    (qpat_assum `pbase + cap < _` mp_tac >> qpat_assum `32 + LENGTH bs <= cap` mp_tac >>
     numLib.ARITH_TAC) >>
  `w2n (n2w (pbase + 32) :bytes32) = pbase + 32` by simp[w2n_n2w] >>
  drule_all (Q.INST [`off` |-> `32`] raw_create_owned_window_frame) >> simp[]
QED

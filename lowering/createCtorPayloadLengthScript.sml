(* The observed constructor snapshots and preparation, before the outer CREATE. *)
Theory createCtorPayloadLength
Ancestors
  createCtorSavedRows createCtorPrivateSnapshot createCtorRawEntry createCtorBlueprintEntry
  venomInst words exprLowering exprLoweringProps fragExec compileEnv emitHelper stmtLoweringMono
  exprSimFullBundleProps exprSimExtract32Post exprSimMemDefs bodyPtrDefs
  loweringStateRelDefs stateRelProj assignTuplePtrCopyLen bodyMemoryDefs
  createMarkedPath relation arithmetic finite_map context
  createCtorEncoderActualLength createSizeCtorPayload createSizeItinerary
  exprSimIfExpWidenedPhysicalType exprSimSubscriptArrayCompose aggregateEvaluatedLayout
  bodyFullExtCallPosList bodyFullExtCallDirectState bodyFullExtCallPackingReady abiEncodeArgsCase loweringPosts exprSimHyps
  exprSimWordArgs
  vyperStorageFootprint vyperStorageTrace vyperState freshWrites list rich_list

(* The VV replay supplies the pre-copy ghosts. The copy theorem, not the
   replay, advances those ghosts to the observed snapshot endpoint. *)
Theorem ctor_payload_copy_row[local]:
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  compile_snapshot_vv ce (exprs_can_mutate ce xs)
    (ext_call_arg_value (lowered_value_type ce e) vv) sm = (saved,sb) /\
  exprs_can_mutate ce xs /\ ~is_word_type (lowered_value_type ce e) /\
  expr_body_pre ce cx env e es /\
  eval_expr cx e es = (INL raw,ee) /\ read_result cx raw ee = (INL v,ee) /\
  local_ptrs_reserved ce sa /\ fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post H ctx func ce cx e es sa sm s0 ee raw vv s /\
    vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee raw vv s /\
    ptr_vv_ok cx (post_value_type ce e) raw vv ee G tn s /\
    alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
    ghost_inv_at (DF H) lo d ce cx ee G tn s /\
    ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
    (!tag op. vv = StackValue tag op /\ ~is_word_type (post_value_type ce e) ==>
       ptr_buf_ok ce e op G s) /\
    (!tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
       ptr_buf_ok ce e p.ptr_operand G s) /\
    (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
       ?val. read_result cx raw ee = (INL val,ee) /\
       !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
         eval_operand (vv_operand vv) s = SOME w ==>
         w2n w + type_memory_size rt <= lo /\
         (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
           val_in_memory rt val (w2n w) mem))) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  return_buf_frame d ce sa s0 /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  RTC (\u r. (u.vs_current_bb,u.vs_inst_idx) <>
                (sb.cs_current_bb,LENGTH sb.cs_current_insts) /\
       ?i ms. ctor_segment_fetch func u = SOME i /\
              sm.cs_next_id <= i.inst_id /\ i.inst_id < sb.cs_next_id /\
              gas_origin_edge F explicit ctx func u ms (OK r)) s t /\
  t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  ctor_segment_fetch func t = SOME last /\ last.inst_opcode <> PHI /\
  sb.cs_next_id <= last.inst_id ==>
  ?Gt tt. !H. valid_horizon cx st0 H ee.storage_trace ==>
    extcall_positional_post T DF lo d ctx func ce cx env xs [e] [saved]
      sa sb es s0 G0 tn0 H (INL [v] : value list + exception) ee Gt tt t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `?H. valid_horizon _ _ H _` (qx_choose_then `H0` assume_tac) >>
  qpat_assum `!H. _ ==> vv_post H ctx func ce cx e es sa sm s0 ee raw vv s /\ _`
     (qspec_then `H0` (drule_then (MAP_EVERY assume_tac o CONJUNCTS))) >>
  `storage_trace_domain cx st0 ee.storage_trace` by metis_tac[extcall_packing_observed_domain] >>
  `~is_word_type (post_value_type ce e)` by
    metis_tac[expr_body_pre_lowered_fits,arg_type_fits_word_type,post_value_type_nonword] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post H ctx func ce cx e es sa sm s0 ee raw vv s /\
    ghost_inv_at (DF H) lo d ce cx ee G tn s` by
    (rpt strip_tac >> first_x_assum (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `compile_snapshot_vv ce T (ext_call_arg_value (lowered_value_type ce e) vv) sm = (saved,sb)` by fs[] >>
  `eval_expr cx e (es with gas_obs := es.gas_obs) = (INL raw,ee)` by simp[] >>
  `!tag op. vv = StackValue tag op ==> ptr_buf_ok ce e op G s` by simp[] >>
  drule_all (INST_TYPE [alpha |-> ``:exception``] ctor_private_snapshot_actual) >>
  simp[] >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
  qpat_x_assum `!H. _ ==> gas_origin_ptr_path _ _ _ _ /\ _` mp_tac >>
  rpt (pop_assum kall_tac) >> metis_tac[]
QED

(* Allocation is always observed at the same caller state; raw preparation
   then executes its byte copy and destination ADD before the encoder. *)
Theorem ctor_payload_preparation[local]:
  compile_alloc_buffer capacity se = (buf,a) /\ fn_has_code se a func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce se /\
  capacity < dimword (:256) /\
  (!x z. ce.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at se x) /\
  (!x z. ce.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at se x) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee s /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d ce cx ee G tn s) /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = se.cs_current_bb /\ s.vs_inst_idx = LENGTH se.cs_current_insts /\
  gas_origin_edge F explicit ctx func s am (OK sa') /\
  (if raw then
    compile_copy_memory_dynamic buf.buf_operand (Var src) (Var len) a = ((),b) /\
    fn_has_code a b func /\ emit_op ADD [buf.buf_operand;Var len] b = (dst_op,st) /\
    fn_has_code b st func /\ w2n nword <= capacity /\
    not_fresh_at se src /\ not_fresh_at se len /\
    lookup_var src s = SOME p /\ lookup_var len s = SOME nword /\
    ptr_covers G tn src s (w2n nword) /\ op_taint tn (Var len) = {} /\
    w2n p + w2n nword <= s.vs_alloca_next /\
    gas_origin_edge F explicit ctx func sa' bm (OK sb') /\
    gas_origin_edge F explicit ctx func sb' cm (OK u)
   else st = a /\ dst_op = buf.buf_operand /\ u = sa') ==>
  ?root dst pbase inst Gu tu.
    buf.buf_operand = Var root /\ dst_op = Var dst /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id = se.cs_next_id /\ inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\
    abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
      se.cs_next_id pbase capacity root dst (if raw then w2n nword else 0) [] st u Gu tu /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gu,tu))
Proof
  Cases_on `raw` >> simp_tac bool_ss [] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS)
  >- (drule_all ctor_raw_destination_actual >>
      disch_then (qspec_then `PG` (qx_choosel_then [`root`,`pbase`,`out`,`Gu`,`tu`,`inst`]
        (MAP_EVERY assume_tac o CONJUNCTS))) >>
      qexistsl_tac [`root`,`out`,`pbase`,`inst`,`Gu`,`tu`] >> simp[mk_inst_def]) >>
  drule_all ctor_encoder_blueprint_entry >>
  disch_then (qspecl_then [`explicit`,`PG`] (qx_choosel_then [`root`,`pbase`,`u0`,`Gu`,`tu`,`inst`]
    (MAP_EVERY assume_tac o CONJUNCTS))) >>
  `sa' = u0` by metis_tac[] >>
  qexistsl_tac [`root`,`root`,`pbase`,`inst`,`Gu`,`tu`] >> simp[mk_inst_def]
QED

Theorem ctor_payload_scalar_gas[local]:
  expr_sim_full_post (DF,lo,d,ctx,func) ce cx e
    (es,sa,sb,s,op,G0,tn0) H res (ee with gas_obs := gs) G tn t <=>
  expr_sim_full_post (DF,lo,d,ctx,func) ce cx e
    (es,sa,sb,s,op,G0,tn0) H res ee G tn t
Proof
  simp[expr_sim_full_post_def, extract32_expr_post_end_gas_obs, ghost_inv_at_def,
       ghost_inv_def, local_region_def]
QED

Theorem ctor_payload_vv_gas[local]:
  (vv_store_bound cx ty lt (ee with gas_obs := gs) raw vv t <=>
   vv_store_bound cx ty lt ee raw vv t) /\
  (ptr_vv_ok cx ty raw vv (ee with gas_obs := gs) G tn t <=>
   ptr_vv_ok cx ty raw vv ee G tn t) /\
  (ghost_inv_at D lo d ce cx (ee with gas_obs := gs) G tn t <=>
   ghost_inv_at D lo d ce cx ee G tn t)
Proof
  Cases_on `vv` >>
  simp[vv_store_bound_def, ptr_vv_ok_def, read_result_success_gas_iff,
       ghost_inv_at_def, ghost_inv_def, local_region_def]
QED

Theorem ctor_payload_row_horizons[local]:
  (!i. i < n ==> vyperState$bind (eval_expr cx (A i)) (read_result cx) (E i) =
       (INL (V i),E (SUC i))) /\ valid_horizon cx st0 H (E n).storage_trace ==>
  !i. i <= n ==> valid_horizon cx st0 H (E i).storage_trace
Proof
  strip_tac >>
  `!k j. j + k = n ==> valid_horizon cx st0 H (E j).storage_trace` suffices_by
    (strip_tac >> rpt strip_tac >> first_x_assum irule >> qexists_tac `n - i` >> decide_tac) >>
  Induct >> simp[] >> rpt strip_tac >>
  `valid_horizon cx st0 H (E (SUC j)).storage_trace` by
    (first_x_assum irule >> decide_tac) >>
  `j < n` by decide_tac >>
  qpat_assum `!i. i < n ==> _` (qspec_then `j` (drule_then assume_tac)) >>
  `storage_trace_frame (vyperState$bind (eval_expr cx (A j)) (read_result cx))` by
    simp[storage_trace_frame_bind_all, cj 5 evaluate_storage_trace_frame,
         storage_trace_frame_read_result] >>
  drule_all_then ACCEPT_TAC valid_horizon_frame
QED

(* All actual cut segments are read at the states provided by the caller.
   In the raw branch the prefix length and pointer are old at the first
   constructor row, not supplied anew at the encoder entry. *)
Theorem create_ctor_payload_length:
  LENGTH args = LENGTH vs /\ LENGTH svs = LENGTH args /\
  compile_create_ctor_args compile_expr ce args (C 0) = (svs,C (LENGTH args)) /\
  (args = [] ==> ~raw ==>
    compile_create_blueprint_args compile_expr ce F later args (C 0) = ((dst_op,alen),en)) /\
  (args <> [] ==>
    body_inv tops ctx ce cx /\ (!K. dead_lo_ok K (DF K) lo ce cx) /\
    EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal))
      (int_calls_exprs args) /\
    (?H. valid_horizon cx st0 H (E (LENGTH args)).storage_trace) /\
    fn_inst_ids_distinct func /\
    (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
    sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
    (!i. i < LENGTH args ==>
      compile_expr ce (expr_type (EL i args)) (EL i args) (C i) = (V i,M i) /\
      compile_snapshot_vv ce (exprs_can_mutate ce (DROP (SUC i) args))
        (ext_call_arg_value (lowered_value_type ce (EL i args)) (V i)) (M i) =
        (EL i svs,C (SUC i)) /\
      vyperState$bind (eval_expr cx (EL i args)) (read_result cx) (E i) =
        (INL (EL i vs),E (SUC i)) /\
      (expr_sim_inv ce cx env (E i) ==> expr_body_pre ce cx env (EL i args) (E i)) /\
      (?tv ann. evaluate_type (get_tenv cx) (lowered_value_type ce (EL i args)) = SOME tv /\
        evaluate_type (get_tenv cx) (expr_type (EL i args)) = SOME ann /\
        arg_type_fits (lowered_value_type ce (EL i args)) (expr_type (EL i args)) /\
        value_has_type tv (EL i vs) /\ value_has_type ann (EL i vs)) /\
      local_ptrs_reserved ce (C i) /\
      (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at (C i) x) /\
      (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at (C i) x) /\
      (St (SUC i)).vs_labels = (St i).vs_labels /\
      ~(St (SUC i)).vs_halted /\ (St (SUC i)).vs_current_bb = (C (SUC i)).cs_current_bb /\
      (St (SUC i)).vs_inst_idx = LENGTH (C (SUC i)).cs_current_insts /\
      (~is_word_type (lowered_value_type ce (EL i args)) ==>
        (if exprs_can_mutate ce (DROP (SUC i) args) then
          fn_has_code (M i) (C (SUC i)) func /\ ~(Mid i).vs_halted /\
          (Mid i).vs_current_bb = (M i).cs_current_bb /\
          (Mid i).vs_inst_idx = LENGTH (M i).cs_current_insts /\
          RTC (\p q. (p.vs_current_bb,p.vs_inst_idx) <>
               ((C (SUC i)).cs_current_bb,LENGTH (C (SUC i)).cs_current_insts) /\
            ?j ms. ctor_segment_fetch func p = SOME j /\
              (M i).cs_next_id <= j.inst_id /\ j.inst_id < (C (SUC i)).cs_next_id /\
              gas_origin_edge F explicit ctx func p ms (OK q)) (Mid i) (St (SUC i)) /\
          (?j. ctor_segment_fetch func (St (SUC i)) = SOME j /\ j.inst_opcode <> PHI /\
               (C (SUC i)).cs_next_id <= j.inst_id)
         else Mid i = St (SUC i)))) /\
    expr_sim_inv ce cx env (E 0) /\ return_buf_frame d ce (C 0) (St 0) /\
    alloca_history func (St 0) /\ ~(St 0).vs_halted /\
    (St 0).vs_current_bb = (C 0).cs_current_bb /\ (St 0).vs_inst_idx = LENGTH (C 0).cs_current_insts /\
    (!K. valid_horizon cx st0 K (E 0).storage_trace ==>
      stmt_state_rel K ctx func ce cx (E 0) (St 0) /\
      storage_well_formed_on cx (E 0) (FST K) /\
      ghost_inv_at (DF K) lo d ce cx (E 0) G0 tn0 (St 0)) /\
    (!i g h. i < LENGTH args /\ expr_sim_inv ce cx env (E i) /\
      return_buf_frame d ce (C i) (St i) /\ alloca_history func (St i) /\
      ~(St i).vs_halted /\ (St i).vs_current_bb = (C i).cs_current_bb /\
      (St i).vs_inst_idx = LENGTH (C i).cs_current_insts /\
      (!K. valid_horizon cx st0 K (E i).storage_trace ==>
        stmt_state_rel K ctx func ce cx (E i) (St i) /\
        storage_well_formed_on cx (E i) (FST K) /\
        ghost_inv_at (DF K) lo d ce cx (E i) g h (St i)) ==>
      (is_word_type (lowered_value_type ce (EL i args)) ==>
        ?g' h'. !K op. valid_horizon cx st0 K (E (SUC i)).storage_trace /\
          lower_value compile_expr ce (expr_type (EL i args)) (EL i args) (C i) =
            (op,C (SUC i)) ==>
          expr_sim_full_post (DF,lo,d,ctx,func) ce cx (EL i args)
            (E i,C i,C (SUC i),St i,op,g,h) K (INL (EL i vs) : value + exception)
              ((E (SUC i)) with gas_obs := []) g' h' (St (SUC i))) /\
      (~is_word_type (lowered_value_type ce (EL i args)) ==>
        ?g' h' raw_value. eval_expr cx (EL i args) (E i) = (INL raw_value,E (SUC i)) /\
         !K. valid_horizon cx st0 K (E (SUC i)).storage_trace ==>
          vv_post K ctx func ce cx (EL i args) (E i) (C i) (M i) (St i)
            ((E (SUC i)) with gas_obs := []) raw_value (V i) (Mid i) /\
          vv_store_bound cx (post_value_type ce (EL i args)) (lowered_value_type ce (EL i args))
            ((E (SUC i)) with gas_obs := []) raw_value (V i) (Mid i) /\
          ptr_vv_ok cx (post_value_type ce (EL i args)) raw_value (V i)
            ((E (SUC i)) with gas_obs := []) g' h' (Mid i) /\
          alloca_history func (Mid i) /\ (St i).vs_alloca_next <= (Mid i).vs_alloca_next /\
          ghost_inv_at (DF K) lo d ce cx ((E (SUC i)) with gas_obs := []) g' h' (Mid i) /\
          ghost_kept_at lo ce (E i) (C i) g h (St i) g' h' /\
          (!tag op. V i = StackValue tag op /\ ~is_word_type (post_value_type ce (EL i args)) ==>
            ptr_buf_ok ce (EL i args) op g' (Mid i)) /\
          (!tag p. V i = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
            ptr_buf_ok ce (EL i args) p.ptr_operand g' (Mid i)) /\
          (ce.ce_is_ctor /\ vv_location (V i) = SOME LocCode ==>
            ?val. read_result cx raw_value ((E (SUC i)) with gas_obs := []) =
                (INL val,(E (SUC i)) with gas_obs := []) /\
              !rt w. evaluate_type (get_tenv cx) (post_value_type ce (EL i args)) = SOME rt /\
                eval_operand (vv_operand (V i)) (Mid i) = SOME w ==>
                w2n w + type_memory_size rt <= lo /\
                (!mem. mem_agree_outside h'.t_mem (Mid i).vs_memory mem ==>
                       val_in_memory rt val (w2n w) mem)))) /\
    se = C (LENGTH args) /\ s = St (LENGTH args) /\ ee = E (LENGTH args) /\
    local_ptrs_reserved ce se /\ ci_mono (C 0) se /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
    capacity = (if raw then prefix_bound else 0) +
      abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) args)) /\
    capacity < dimword (:256) /\
    compile_alloc_buffer capacity se = (buf,a) /\ fn_has_code se a func /\
    gas_origin_edge F explicit ctx func s am (OK su) /\
    (if raw then
      compile_copy_memory_dynamic buf.buf_operand (Var src) (Var len) a = ((),b) /\
      fn_has_code a b func /\ emit_op ADD [buf.buf_operand;Var len] b = (dst_op,st) /\
      fn_has_code b st func /\ w2n nword <= prefix_bound /\
      not_fresh_at (C 0) src /\ not_fresh_at (C 0) len /\
      lookup_var src (St 0) = SOME p /\ lookup_var len (St 0) = SOME nword /\
      ptr_covers G0 tn0 src (St 0) (w2n nword) /\ op_taint tn0 (Var len) = {} /\
      w2n p + w2n nword <= (St 0).vs_alloca_next /\
      gas_origin_edge F explicit ctx func su bm (OK sv) /\
      gas_origin_edge F explicit ctx func sv cm (OK u)
     else st = a /\ dst_op = buf.buf_operand /\ u = su) /\
    compile_abi_encode_values_to_buf ce dst_op (ZIP (svs,MAP (lowered_value_type ce) args))
      st = (alen,en) /\ fn_has_code st en func /\
    RTC (create_marked_edge (\p ms q. ?bb i.
      (p.vs_current_bb,p.vs_inst_idx) <> (en.cs_current_bb,LENGTH en.cs_current_insts) /\
      lookup_block p.vs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb p.vs_inst_idx = SOME i /\ i.inst_id IN frag_ids st en /\
      gas_origin_edge F explicit ctx func p ms (OK q))) (u,[]) (t,encmarks) /\
    (t.vs_current_bb,t.vs_inst_idx) = (en.cs_current_bb,LENGTH en.cs_current_insts) /\
    c 0 = en /\ r 0 = t /\ r n = bad /\
    (!k. k < n ==>
      (c k).cs_next_id <= (c (SUC k)).cs_next_id /\
      RTC (create_marked_edge (\p ms q. ?bb i.
        (p.vs_current_bb,p.vs_inst_idx) <>
          ((c (SUC k)).cs_current_bb,LENGTH (c (SUC k)).cs_current_insts) /\
        lookup_block p.vs_current_bb func.fn_blocks = SOME bb /\
        get_instruction bb p.vs_inst_idx = SOME i /\
        i.inst_id IN frag_ids (c k) (c (SUC k)) /\
        gas_origin_edge F explicit ctx func p ms (OK q))) (r k,[]) (r (SUC k),chunk k)) /\
    lookup_block bad.vs_current_bb func.fn_blocks = SOME bbad /\
    get_instruction bbad bad.vs_inst_idx = SOME dispatch /\
    ((dispatch.inst_opcode = CREATE /\ dispatch.inst_operands = [value;off;sz]) \/
     (dispatch.inst_opcode = CREATE2 /\ dispatch.inst_operands = [value;off;sz;salt])) /\
    eval_operand sz bad = SOME w /\ 2 * max_code_size < w2n w) ==>
  ?bytes. encode_create_ctor_args (get_tenv cx) (MAP expr_type args) vs = SOME bytes /\
    (if args = [] then bytes = [] /\ (~raw ==> alen = Lit 0w /\ en = C 0)
     else eval_operand alen t = SOME (n2w (LENGTH bytes)) /\
       (!x. alen = Var x ==> not_fresh_at en x) /\
       ?G tn Gt tt pbase root dst Gu tu.
         buf.buf_operand = Var root /\ dst_op = Var dst /\ op_taint tt alen = {} /\
         pure_frame ce func ee se u t /\ wb_frame ce ee ee se u t /\
         wb_frame ce (E 0) ee (C 0) (St 0) t /\ return_buf_frame d ce en t /\
         expr_sim_inv ce cx env ee /\ (St 0).vs_alloca_next <= t.vs_alloca_next /\
         mem_bytes_at (pbase + (if raw then w2n nword else 0)) (LENGTH bytes) t.vs_memory = bytes /\
         (!j. pbase + (if raw then w2n nword else 0) <= j /\
              j < pbase + (if raw then w2n nword else 0) + LENGTH bytes ==> j NOTIN tt.t_mem) /\
         abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
           se.cs_next_id pbase capacity root dst (if raw then w2n nword else 0) [] en t Gt tt /\
         (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gu,tu) /\
              gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK t,Gt,tt)))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> Cases_on `args = []`
  >- (Cases_on `raw` >> gvs[compile_create_blueprint_args_def, comp_return_def]) >>
  qpat_x_assum `args <> [] ==> _` (drule_then (MAP_EVERY assume_tac o CONJUNCTS)) >>
  `0 < LENGTH args` by (Cases_on `args` >> fs[]) >>
  `?G tn. !K. valid_horizon cx st0 K (E (LENGTH args)).storage_trace ==>
    extcall_positional_post T DF lo d ctx func ce cx env [] args svs
      (C 0) (C (LENGTH args)) (E 0) (St 0) G0 tn0 K (INL vs : value list + exception)
      (E (LENGTH args)) G tn (St (LENGTH args))` by suspend "rows" >>
  suspend "encode"
QED

Resume create_ctor_payload_length[rows]:
  `LENGTH vs = LENGTH args` by simp[] >>
  qpat_assum `?H. valid_horizon cx st0 H _` (qx_choose_then `H0` assume_tac) >>
  `!i. i <= LENGTH args ==> valid_horizon cx st0 H0 (E i).storage_trace` by
    (match_mp_tac (Q.INST [`A` |-> `\i. EL i args`, `V` |-> `\i. EL i vs`] ctor_payload_row_horizons) >>
     simp_tac bool_ss [] >> qpat_assum `!i. i < LENGTH args ==> compile_expr _ _ _ _ = _ /\ _`
       (fn th => rpt strip_tac >> qspec_then `i` (drule_then strip_assume_tac) th) >>
     first_assum ACCEPT_TAC) >>
  irule ctor_saved_rows_at_last_cut >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
  >- (qexistsl_tac [`M`,`V`] >> conj_tac
      >- suspend "replay"
      >> rpt strip_tac >>
      qpat_assum `!i. i < LENGTH args ==> compile_expr _ _ _ _ = _ /\ _`
        (qspec_then `i` (drule_then strip_assume_tac)) >>
      TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
      metis_tac[ci_mono_trans,ci_mono_compile_expr_sa,ci_mono_compile_snapshot_vv,pairTheory.SND]) >>
  qexists_tac `tops` >> asm_rewrite_tac[]
QED

Resume create_ctor_payload_length[replay]:
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `!i g h. i < LENGTH args /\ _ ==> _`
    (qspecl_then [`i`,`g`,`h`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  conj_tac
  >- (disch_tac >> qpat_x_assum `is_word_type _ ==> ?g' h'. _` (drule_then strip_assume_tac) >>
      qexistsl_tac [`g'`,`h'`] >> rpt strip_tac >>
      qpat_x_assum `!K op. _ ==> expr_sim_full_post _ _ _ _ _ K _ _ _ _ _`
        (irule o REWRITE_RULE [ctor_payload_scalar_gas]) >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `!i. i < LENGTH args ==> compile_expr _ _ _ _ = _ /\ _`
    (qspec_then `i` (drule_then (MAP_EVERY assume_tac o CONJUNCTS))) >>
  conj_tac
  >- suspend "retained"
  >> suspend "copied"
QED

Resume create_ctor_payload_length[retained]:
  strip_tac >>
  `Mid i = St (SUC i)` by
    (qpat_x_assum `~is_word_type (lowered_value_type ce (EL i args)) ==> if _ then _ else _` mp_tac >>
     asm_simp_tac bool_ss [] >> metis_tac[]) >>
  qpat_x_assum `~is_word_type _ ==> ?g' h' raw_value. _`
    (drule_then (qx_choosel_then [`gv`,`hv`,`rv`] strip_assume_tac)) >>
  qexistsl_tac [`gv`,`hv`] >> rpt strip_tac >> qexists_tac `rv` >>
  qpat_x_assum `!K. _ ==> vv_post K ctx func ce cx _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then mp_tac o REWRITE_RULE [vv_post_final_gas,ctor_payload_vv_gas,read_result_success_gas_iff]) >>
  asm_rewrite_tac[]
QED

Resume create_ctor_payload_length[copied]:
  strip_tac >>
  qpat_x_assum `~is_word_type _ ==> if _ then _ else _`
    (drule_then (fn th => qpat_assum `exprs_can_mutate ce (DROP (SUC i) args)`
      (fn m => strip_assume_tac (SIMP_RULE bool_ss [m] th)))) >>
  qpat_x_assum `~is_word_type _ ==> ?g' h' raw_value. _`
    (drule_then (qx_choosel_then [`gv`,`hv`,`rv`]
     (strip_assume_tac o REWRITE_RULE [vv_post_final_gas,ctor_payload_vv_gas,read_result_success_gas_iff]))) >>
  `SUC i <= LENGTH args` by decide_tac >>
  `read_result cx rv (E (SUC i)) = (INL (EL i vs),E (SUC i))` by
    (qpat_assum `eval_expr cx (EL i args) (E i) = _` (fn ev =>
       qpat_assum `vyperState$bind _ _ _ = _`
         (ACCEPT_TAC o SIMP_RULE bool_ss [bind_def,ev,pairTheory.pair_case_def,sumTheory.sum_case_def]))) >>
  `expr_body_pre ce cx env (EL i args) (E i)` by simp[] >>
  irule ctor_payload_copy_row >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
  >- (qexists_tac `H0` >> simp[])
  >- (qexists_tac `j` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`gv`,`explicit`,`rv`,`Mid i`,`M i`,`hv`,`V i`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume create_ctor_payload_length[encode]:
  `!K. valid_horizon cx st0 K ee.storage_trace ==>
    extcall_positional_post T DF lo d ctx func ce cx env [] args svs
      (C 0) se (E 0) (St 0) G0 tn0 K (INL vs : value list + exception) ee G tn s` by
    (qpat_assum `se = _` (fn hc => qpat_assum `s = _` (fn hs =>
       qpat_assum `ee = _` (fn he => pure_rewrite_tac [hc,hs,he]))) >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `!K. _ ==> extcall_positional_post T DF lo d ctx func ce cx env [] args svs _ _ _ _ _ _ K _ (E (LENGTH args)) _ _ _` kall_tac >>
  qpat_assum `ee = _` (fn h => qpat_x_assum `?H. valid_horizon cx st0 H (E (LENGTH args)).storage_trace`
    (assume_tac o PURE_REWRITE_RULE [GSYM h])) >>
  `!K. valid_horizon cx st0 K ee.storage_trace ==>
     stmt_state_rel K ctx func ce cx ee s /\ storage_well_formed_on cx ee (FST K) /\
     ghost_inv_at (DF K) lo d ce cx ee G tn s` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!K. _ ==> extcall_positional_post T DF lo d ctx func ce cx env [] args svs _ se _ _ _ _ K _ ee _ _ s`
       (drule_then (strip_assume_tac o SIMP_RULE bool_ss [extcall_positional_post_def,sumTheory.INL_11])) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `?H. valid_horizon cx st0 H ee.storage_trace` (qx_choose_then `H0` assume_tac) >>
  qpat_assum `!K. _ ==> extcall_positional_post T DF lo d ctx func ce cx env [] args svs _ se _ _ _ _ K _ ee _ _ s`
     (qspec_then `H0` (drule_then (strip_assume_tac o SIMP_RULE bool_ss
        [extcall_positional_post_def,sumTheory.INL_11]))) >>
  `expr_sim_inv ce cx env ee` by
    (drule_then assume_tac bodySimTheory.body_inv_contract >>
     drule_then strip_assume_tac bodyInvCodePropsTheory.body_inv_module_locations >>
     drule_then assume_tac bodyInvCodePropsTheory.body_inv_unit_immutable_layout >>
     drule_then assume_tac bodyInvCodePropsTheory.contract_inv_cenv_modules >>
     drule_then assume_tac contractInvContextPropsTheory.contract_inv_singleton_source_modules >>
     fs[bodyFullPostsModsTheory.expr_sim_inv_mods_singleton]) >>
  `storage_trace_domain cx st0 ee.storage_trace` by (irule extcall_packing_observed_domain >> qexists_tac `H0` >> first_assum ACCEPT_TAC) >>
  `!e. MEM e args ==> ?es'. expr_body_pre ce cx env e es'` by suspend "source_pre" >>
  `!i. i < LENGTH args ==> ?tv ann.
      evaluate_type (get_tenv cx) (lowered_value_type ce (EL i args)) = SOME tv /\
      evaluate_type (get_tenv cx) (expr_type (EL i args)) = SOME ann /\
      arg_type_fits (lowered_value_type ce (EL i args)) (expr_type (EL i args)) /\
      value_has_type tv (EL i vs) /\ value_has_type ann (EL i vs)` by
     (rpt gen_tac >> disch_tac >> qpat_assum `!i. i < LENGTH args ==> compile_expr _ _ _ _ = _ /\ _`
        (drule_then (MAP_EVERY assume_tac o CONJUNCTS)) >> first_assum ACCEPT_TAC) >>
  `LENGTH args = LENGTH svs` by simp[] >>
  drule_all_then (qx_choosel_then [`avs`,`ats`,`bytes`] (MAP_EVERY assume_tac o CONJUNCTS))
    create_ctor_payload_layout >>
  qexists_tac `bytes` >> conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `args <> []` (simp_tac bool_ss o single) >>
  qpat_x_assum `!i g h. i < LENGTH args /\ _ ==> _` kall_tac >>
  qpat_x_assum `LIST_REL _ (ZIP (args,svs)) vs` kall_tac >>
  suspend "entry"
QED

Resume create_ctor_payload_length[source_pre]:
  `!i. i <= LENGTH args ==> expr_sim_inv ce cx env (E i)` by
    (Induct_on `i` >- simp[] >> rpt strip_tac >>
     `i < LENGTH args /\ i <= LENGTH args` by decide_tac >>
     qpat_assum `!i. i < LENGTH args ==> compile_expr _ _ _ _ = _ /\ _`
       (qspec_then `i` (drule_then (MAP_EVERY assume_tac o CONJUNCTS))) >>
     `expr_body_pre ce cx env (EL i args) (E i)` by metis_tac[] >>
     drule_all_then (ACCEPT_TAC o CONJUNCT1) (REWRITE_RULE [ETA_AX] abi_args_success_ready)) >>
  pure_rewrite_tac [MEM_EL] >> rpt gen_tac >>
  disch_then (qx_choose_then `i` strip_assume_tac) >> qexists_tac `E i` >>
  `i <= LENGTH args` by decide_tac >>
  qpat_assum `!i. i < LENGTH args ==> compile_expr _ _ _ _ = _ /\ _`
    (qspec_then `i` (drule_then (MAP_EVERY assume_tac o CONJUNCTS))) >>
  asm_rewrite_tac[] >> metis_tac[]
QED

Resume create_ctor_payload_length[entry]:
  `?root dst pbase inst Gu tu.
     buf.buf_operand = Var root /\ dst_op = Var dst /\
     MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
     inst.inst_id = se.cs_next_id /\ inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\
     abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
       se.cs_next_id pbase capacity root dst (if raw then w2n nword else 0) [] st u Gu tu /\
     (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gu,tu))` by suspend "prep" >>
  suspend "finish"
QED

Resume create_ctor_payload_length[prep]:
  irule ctor_payload_preparation >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  qexistsl_tac [`a`,`am`,`b`,`bm`,`cm`,`len`,`p`,`su`,`sv`,`src`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  Cases_on `raw` >> simp_tac bool_ss []
  >- (qpat_x_assum `if T then _ else _` (strip_assume_tac o SIMP_RULE bool_ss []) >>
      qpat_x_assum `capacity = _` (assume_tac o SIMP_RULE bool_ss []) >>
      `w2n nword <= capacity` by decide_tac >>
      `lookup_var src s = SOME p /\ lookup_var len s = SOME nword` by
        (rpt conj_tac >> first_assum irule >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
      qpat_assum `ghost_kept_at _ _ _ _ _ _ _ _ _` (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >>
      `FLOOKUP G src = FLOOKUP G0 src /\ op_taint tn (Var src) = op_taint tn0 (Var src)` by
        (first_assum irule >> first_assum ACCEPT_TAC) >>
      `op_taint tn (Var len) = op_taint tn0 (Var len)` by
        (qpat_assum `!x. not_fresh_at (C 0) x ==> FLOOKUP _ x = _ /\ _`
          (qspec_then `len` (drule_then (ACCEPT_TAC o CONJUNCT2)))) >>
      `ptr_covers G tn src s (w2n nword)` by
        (irule ptr_covers_lookup_frame >> qexistsl_tac [`G0`,`St 0`,`tn0`] >>
         rpt conj_tac >> asm_rewrite_tac[]) >>
      `((C 0):compile_state).cs_next_var <= se.cs_next_var` by fs[ci_mono_def] >>
      `not_fresh_at se src /\ not_fresh_at se len` by
        (rpt conj_tac >> irule freshWritesTheory.not_fresh_at_mono >>
         qexists_tac `C 0` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
      `w2n p + w2n nword <= s.vs_alloca_next` by decide_tac >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
      metis_tac[]) >>
  qpat_x_assum `if F then _ else _` (strip_assume_tac o SIMP_RULE bool_ss []) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume create_ctor_payload_length[finish]:
  `LENGTH bytes <= capacity - (if raw then w2n nword else 0)` by
    (Cases_on `raw` >> simp_tac bool_ss [] >>
     qpat_x_assum `capacity = _` (assume_tac o SIMP_RULE bool_ss [])
     >- (qpat_x_assum `if T then _ else _` (strip_assume_tac o SIMP_RULE bool_ss []) >> decide_tac) >>
     decide_tac) >>
  `!i. i < LENGTH args ==> ?tv ann.
      evaluate_type (get_tenv cx) (lowered_value_type ce (EL i args)) = SOME tv /\
      evaluate_type (get_tenv cx) (expr_type (EL i args)) = SOME ann /\
      value_has_type tv (EL i vs)` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!i. i < LENGTH args ==> ?tv ann. _`
       (drule_then (qx_choosel_then [`tv`,`ann`] strip_assume_tac)) >>
     qexistsl_tac [`tv`,`ann`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `dst_op = Var dst` (fn h => qpat_x_assum `compile_abi_encode_values_to_buf ce dst_op _ st = _`
     (assume_tac o PURE_REWRITE_RULE [h])) >>
  drule_all (REWRITE_RULE [REFL_CLAUSE,AND_CLAUSES]
    (Q.INST [`keep` |-> `T`, `rows` |-> `ZIP (svs,MAP (lowered_value_type ce) args)`]
      (INST_TYPE [alpha |-> ``:exception``] ctor_encoder_length_at_marked_cut))) >>
  disch_tac >>
  qpat_x_assum `!PG. ?Gt tt. _` (qspec_then `PG` mp_tac) >>
  disch_then (qx_choosel_then [`Genc`,`tenc`] strip_assume_tac) >>
  qpat_assum `abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
    _ _ _ _ _ _ _ en t Genc tenc`
    (strip_assume_tac o REWRITE_RULE [abi_encode_saved_state_def]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  qexistsl_tac [`G`,`tn`,`Genc`,`tenc`,`pbase`,`root`,`dst`,`Gu`,`tu`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
  >- suspend "writeback"
  >- suspend "return_frame"
  >- suspend "frontier"
  >> rpt gen_tac >> conj_tac >> first_assum irule
QED

Resume create_ctor_payload_length[writeback]:
  `local_ptrs_reserved ce (C 0)` by
    (qpat_assum `!i. i < LENGTH args ==> compile_expr _ _ _ _ = _ /\ _`
       (qspec_then `0` (drule_then strip_assume_tac)) >> first_assum ACCEPT_TAC) >>
  `valid_horizon cx st0 H0 (E 0).storage_trace` by
    (`!i. i <= LENGTH args ==> valid_horizon cx st0 H0 (E i).storage_trace` by
       (match_mp_tac (Q.INST [`A` |-> `\i. EL i args`, `V` |-> `\i. EL i vs`] ctor_payload_row_horizons) >>
        simp_tac bool_ss [] >> conj_tac
        >- (rpt strip_tac >>
            qpat_assum `!i. i < LENGTH args ==> compile_expr _ _ _ _ = _ /\ _`
              (qspec_then `i` (drule_then strip_assume_tac)) >> first_assum ACCEPT_TAC) >>
        metis_tac[]) >>
     first_assum irule >> simp[]) >>
  qpat_assum `!K. valid_horizon cx st0 K (E 0).storage_trace ==> _`
    (qspec_then `H0` (drule_then strip_assume_tac)) >>
  qpat_assum `ci_mono (C 0) se` (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
  irule (INST_TYPE [alpha |-> ``:256``] wb_frame_trans) >>
  `MAP FDOM (E 0).scopes = MAP FDOM ee.scopes` by (sym_tac >> first_assum ACCEPT_TAC) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
  >- (qexistsl_tac [`ee`,`se`,`s`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`H0`,`ctx`,`cx`,`func`] >> first_assum ACCEPT_TAC
QED

Resume create_ctor_payload_length[return_frame]:
  irule return_buf_frame_frame >>
  qexistsl_tac [`ce`,`s`,`se`] >>
  simp_tac bool_ss [] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  rpt strip_tac >>
  qpat_assum `wb_frame ce ee ee se s t`
    (irule o cj 1 o REWRITE_RULE [wb_frame_def]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume create_ctor_payload_length[frontier]:
  decide_tac
QED

Finalise create_ctor_payload_length

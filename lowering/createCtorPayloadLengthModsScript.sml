(* The observed constructor snapshots and preparation, before the outer CREATE. *)
Theory createCtorPayloadLengthMods
Ancestors
  createCtorPayloadLength createExprSizeExitDefsMods
  createCtorSavedRowsMods createCtorPrivateSnapshotMods createCtorRawEntryMods createCtorBlueprintEntryMods
  venomInst words exprLowering exprLoweringProps fragExec compileEnv emitHelper stmtLoweringMono
  exprSimFullBundleProps exprSimExtract32Post exprSimMemDefs bodyPtrDefs
  loweringStateRelDefs stateRelProj assignTuplePtrCopyLen bodyMemoryDefs
  createMarkedPath relation arithmetic finite_map context
  createCtorEncoderActualLengthMods createSizeCtorPayload createSizeItinerary
  exprSimIfExpWidenedPhysicalType exprSimSubscriptArrayCompose aggregateEvaluatedLayout
  bodyFullExtCallPosList bodyFullExtCallDirectState bodyFullExtCallPackingReady abiEncodeArgsCase loweringPosts exprSimHyps
  exprSimWordArgs
  vyperStorageFootprint vyperStorageTrace vyperState freshWrites list rich_list

(* The VV replay supplies the pre-copy ghosts. The copy theorem, not the
   replay, advances those ghosts to the observed snapshot endpoint. *)

Theorem ctor_payload_copy_row_mods[local]:
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  compile_snapshot_vv ce (exprs_can_mutate ce xs)
    (ext_call_arg_value (lowered_value_type ce e) vv) sm = (saved,sb) /\
  exprs_can_mutate ce xs /\ ~is_word_type (lowered_value_type ce e) /\
  expr_body_pre_mods mods ce cx env e es /\
  eval_expr cx e es = (INL raw,ee) /\ read_result cx raw ee = (INL v,ee) /\
  local_ptrs_reserved ce sa /\ fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func ce cx e es sa sm s0 ee raw vv s /\
    vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee raw vv s /\
    ptr_vv_ok cx (post_value_type ce e) raw vv ee G tn s /\
    alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn s /\
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
    extcall_positional_post_mods mods T DF lo d ctx func ce cx env xs [e] [saved]
      sa sb es s0 G0 tn0 H (INL [v] : value list + exception) ee Gt tt t
Proof
  cheat
QED

Theorem ctor_payload_preparation_mods[local]:
  compile_alloc_buffer capacity se = (buf,a) /\ fn_has_code se a func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce se /\
  capacity < dimword (:256) /\
  (!x z. ce.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at se x) /\
  (!x z. ce.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at se x) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee s /\
    immutable_frame_mods func ce cx ee s /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
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
    abi_encode_saved_state_mods ctx func ce cx st0 ee DF lo d se s G tn
      se.cs_next_id pbase capacity root dst (if raw then w2n nword else 0) [] st u Gu tu /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gu,tu))
Proof
  cheat
QED

Theorem ctor_payload_scalar_gas_mods[local]:
  expr_sim_full_post_mods (DF,lo,d,ctx,func) ce cx e
    (es,sa,sb,s,op,G0,tn0) H res (ee with gas_obs := gs) G tn t <=>
  expr_sim_full_post_mods (DF,lo,d,ctx,func) ce cx e
    (es,sa,sb,s,op,G0,tn0) H res ee G tn t
Proof
  cheat
QED

Theorem ctor_payload_vv_gas_mods[local]:
  (vv_store_bound cx ty lt (ee with gas_obs := gs) raw vv t <=>
   vv_store_bound cx ty lt ee raw vv t) /\
  (ptr_vv_ok cx ty raw vv (ee with gas_obs := gs) G tn t <=>
   ptr_vv_ok cx ty raw vv ee G tn t) /\
  (ghost_inv_at_mods D lo d ce cx (ee with gas_obs := gs) G tn t <=>
   ghost_inv_at_mods D lo d ce cx ee G tn t)
Proof
  cheat
QED

Theorem create_ctor_payload_length_mods:
  LENGTH args = LENGTH vs /\ LENGTH svs = LENGTH args /\
  compile_create_ctor_args compile_expr ce args (C 0) = (svs,C (LENGTH args)) /\
  (args = [] ==> ~raw ==>
    compile_create_blueprint_args compile_expr ce F later args (C 0) = ((dst_op,alen),en)) /\
  (args <> [] ==>
    contract_inv mods exps ctx ce cx /\
    module_body_inv mods module_src tops ce cx /\ (!K. dead_lo_ok_mods K (DF K) lo ce cx) /\
    EVERY (source_body_call_supported cx)
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
      (expr_sim_inv_mods mods ce cx env (E i) ==> expr_body_pre_mods mods ce cx env (EL i args) (E i)) /\
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
    expr_sim_inv_mods mods ce cx env (E 0) /\ return_buf_frame d ce (C 0) (St 0) /\
    alloca_history func (St 0) /\ ~(St 0).vs_halted /\
    (St 0).vs_current_bb = (C 0).cs_current_bb /\ (St 0).vs_inst_idx = LENGTH (C 0).cs_current_insts /\
    (!K. valid_horizon cx st0 K (E 0).storage_trace ==>
      stmt_state_rel K ctx func ce cx (E 0) (St 0) /\
      storage_well_formed_on cx (E 0) (FST K) /\
      ghost_inv_at_mods (DF K) lo d ce cx (E 0) G0 tn0 (St 0)) /\
    (!i g h. i < LENGTH args /\ expr_sim_inv_mods mods ce cx env (E i) /\
      return_buf_frame d ce (C i) (St i) /\ alloca_history func (St i) /\
      ~(St i).vs_halted /\ (St i).vs_current_bb = (C i).cs_current_bb /\
      (St i).vs_inst_idx = LENGTH (C i).cs_current_insts /\
      (!K. valid_horizon cx st0 K (E i).storage_trace ==>
        stmt_state_rel K ctx func ce cx (E i) (St i) /\
        storage_well_formed_on cx (E i) (FST K) /\
        ghost_inv_at_mods (DF K) lo d ce cx (E i) g h (St i)) ==>
      (is_word_type (lowered_value_type ce (EL i args)) ==>
        ?g' h'. !K op. valid_horizon cx st0 K (E (SUC i)).storage_trace /\
          lower_value compile_expr ce (expr_type (EL i args)) (EL i args) (C i) =
            (op,C (SUC i)) ==>
          expr_sim_full_post_mods (DF,lo,d,ctx,func) ce cx (EL i args)
            (E i,C i,C (SUC i),St i,op,g,h) K (INL (EL i vs) : value + exception)
              ((E (SUC i)) with gas_obs := []) g' h' (St (SUC i))) /\
      (~is_word_type (lowered_value_type ce (EL i args)) ==>
        ?g' h' raw_value. eval_expr cx (EL i args) (E i) = (INL raw_value,E (SUC i)) /\
         !K. valid_horizon cx st0 K (E (SUC i)).storage_trace ==>
          vv_post_mods K ctx func ce cx (EL i args) (E i) (C i) (M i) (St i)
            ((E (SUC i)) with gas_obs := []) raw_value (V i) (Mid i) /\
          vv_store_bound cx (post_value_type ce (EL i args)) (lowered_value_type ce (EL i args))
            ((E (SUC i)) with gas_obs := []) raw_value (V i) (Mid i) /\
          ptr_vv_ok cx (post_value_type ce (EL i args)) raw_value (V i)
            ((E (SUC i)) with gas_obs := []) g' h' (Mid i) /\
          alloca_history func (Mid i) /\ (St i).vs_alloca_next <= (Mid i).vs_alloca_next /\
          ghost_inv_at_mods (DF K) lo d ce cx ((E (SUC i)) with gas_obs := []) g' h' (Mid i) /\
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
         expr_sim_inv_mods mods ce cx env ee /\ (St 0).vs_alloca_next <= t.vs_alloca_next /\
         mem_bytes_at (pbase + (if raw then w2n nword else 0)) (LENGTH bytes) t.vs_memory = bytes /\
         (!j. pbase + (if raw then w2n nword else 0) <= j /\
              j < pbase + (if raw then w2n nword else 0) + LENGTH bytes ==> j NOTIN tt.t_mem) /\
         abi_encode_saved_state_mods ctx func ce cx st0 ee DF lo d se s G tn
           se.cs_next_id pbase capacity root dst (if raw then w2n nword else 0) [] en t Gt tt /\
         (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gu,tu) /\
              gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK t,Gt,tt)))
Proof
  cheat
QED

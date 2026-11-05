(*
 * Children of aggregate literals (#636)
 *
 * Each child is evaluated, unwrapped and stored at its offset in the
 * parent's buffer.  This covers the child's vv_post when materialise turns
 * a storage ArrayRef into a Value, framing locals and older allocations
 * across the child's code, the ADD-unwrap-store step, and the buffer's
 * ALLOCA and final vv_post.
 *
 * TOP-LEVEL:
 *   buffer_alloc_frag — the buffer's ALLOCA, disjoint from older
 *     allocations and locals
 *   aggregate_buffer_clearance — carry buffer clearance through aggregate children
 *   buffer_loop_memory_vv_post — a filled buffer is the parent's vv_post
 *   aggregate_child_unwrap_var, aggregate_child_add_then,
 *   aggregate_unwrap_store_slice_sim — the per-child step
 *   vv_post_old_buffer — an older allocation outside the locals keeps its
 *     bytes
 *   vv_post_local_region_backward — local
 *     regions after a child were there before it
 *
 * Helpers: the *_materialise lemmas, vv_*_vars_frame, vv_post_rebase,
 *   the *_rebased_* and aggregate_store_* lemmas, buffer_alloc_provenance.
 *)
Theory exprSimAggregateChildren
Ancestors
  exprSimVVFrame
  exprSimProps
  loweringPosts
  exprSimAlloc
   exprSimHyps exprSimUnwrap exprSimBufferStore exprSimBuffer
  vyperInterpreter vyperValueOperation vyperState fragExec
  compileEnv context exprSimLiteralBuffer exprSimOps venomState
  exprSimHash exprOperandVar emitHelperProps ASCIInumbers exprLoweringProps venomInst
  vyperEvalExprPreservesScopesDom vyperEvalPreservesScopes oracleExecProps

Theorem vv_holds_materialise:
  read_result cx tv es = (INL v,es) /\
  vv_holds cenv cx t tv vv es s ==>
  vv_holds cenv cx t (Value v) vv es s
Proof
  cheat
QED

Theorem vv_at_materialise:
  read_result cx tv es = (INL v,es) /\
  vv_holds cenv cx t tv vv es s /\
  vv_at cenv cx t sa sb es tv vv s ==>
  vv_at cenv cx t sa sb es (Value v) vv s
Proof
  cheat
QED

Theorem vv_post_materialise:
  read_result cx tv es' = (INL v,es') /\
  vv_post ctx func cenv cx e es sa sb s0 es' tv vv s ==>
  vv_post ctx func cenv cx e es sa sb s0 es' (Value v) vv s
Proof
  cheat
QED

Theorem unwrap_value_materialise_sim:
  !ctx func cenv cx e es sa sm sb s0 es' tv v vv op R.
    unwrap_value cenv vv sm = (op,sb) /\
    local_ptrs_reserved cenv sa /\ MAP FDOM es.scopes = MAP FDOM es'.scopes /\
    sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\
    read_result cx tv es' = (INL v,es') /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
    (!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
           ~is_word_type (expr_type e) ==>
           type_memory_bytes cenv (expr_type e) = type_memory_size tvt /\
           type_memory_size tvt < 2 ** 64) ==>
    frag_exec ctx sm sb
      (\s. vv_post ctx func cenv cx e es sa sm s0 es' tv vv s)
      (\s. expr_post ctx func cenv cx e es sa sb s0 es' v op s) R
Proof
  cheat
QED

Theorem vv_post_old_buffer:
  vv_post ctx func cenv cx e es sa sb s0 es' tv vv s /\
  FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
  (!n b k. local_region cenv es.scopes s0 n b k ==>
    off + sz <= b \/ b + k <= off) ==>
  mem_bytes_at off sz s.vs_memory = mem_bytes_at off sz s0.vs_memory
Proof
  cheat
QED

Theorem vv_post_local_region_backward:
  eval_expr cx e es = (res,es1) /\
  stmt_state_rel ctx func ce cx es s0 /\ local_ptrs_reserved ce sa /\
  vv_post ctx func ce cx e es sa sb s0 es1 tv vv s1 /\
  local_region ce es1.scopes s1 name b sz ==>
  local_region ce es.scopes s0 name b sz
Proof
  cheat
QED









(* The aggregate compiler emits the destination ADD before unwrapping the
   child.  Preserve its value judgment across precisely that update. *)
Theorem buffer_emit_add_vv_post:
  compile_expr cenv (expr_type e) e sa = (vv,sm) /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
  emit_op ADD [buf; Lit (n2w off)] sm = (dst,sn) /\
  vv_post ctx func cenv cx e es sa sm s0 es' tv vv s /\
  eval_operand buf s = SOME w ==>
  ?q. run_inst_seq (emitted_insts sm sn) s = OK q /\
    vv_post ctx func cenv cx e es sa sn s0 es' tv vv q /\
    eval_operand dst q = SOME (w + n2w off) /\
    (q with vs_vars := s.vs_vars) = s /\
    (!x. not_fresh_at sm x ==> lookup_var x q = lookup_var x s)
Proof
  cheat
QED

Theorem buffer_emit_add_vv_sim:
  compile_expr cenv (expr_type e) e sa = (vv,sm) /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
  emit_op ADD [buf; Lit (n2w off)] sm = (dst,sn) ==>
  frag_exec ctx sm sn
    (\s. vv_post ctx func cenv cx e es sa sm s0 es' tv vv s /\
         eval_operand buf s = SOME w)
    (\s. vv_post ctx func cenv cx e es sa sn s0 es' tv vv s /\
         eval_operand dst s = SOME (w + n2w off)) R
Proof
  cheat
QED

(* Provenance follows the actual compile/ADD/unwrap order, not lower_value. *)
Theorem aggregate_child_unwrap_var:
  compile_expr ce ty e sa = (vv,sm) /\ local_ptrs_reserved ce sa /\
  sm.cs_next_var <= sadd.cs_next_var /\
  unwrap_value ce vv sadd = (op,su) ==>
  !x. op = Var x ==> not_fresh_at su x
Proof
  cheat
QED

(* Placement uses allocation IDs, independently of the variable watermark. *)
Theorem expr_val_at_start_var[simp]:
  expr_val_at ce cx ty (sa with cs_next_var := n) sb es v op s <=>
  expr_val_at ce cx ty sa sb es v op s
Proof
  cheat
QED

Theorem vv_at_start_var[simp]:
  vv_at ce cx ty (sa with cs_next_var := n) sb es tv vv s <=>
  vv_at ce cx ty sa sb es tv vv s
Proof
  cheat
QED

Theorem vv_post_rebase:
  vv_post ctx func ce cx e es sa sm s0 es' tv vv r ==>
  vv_post ctx func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
    sm r es' tv vv r
Proof
  cheat
QED

Theorem unwrap_value_rebased_sim:
  unwrap_value ce vv sm = (op,su) /\ local_ptrs_reserved ce sm /\
  sa.cs_next_id <= sm.cs_next_id /\
  read_result cx tv es' = (INL v,es') /\
  vv_post ctx func ce cx e es sa sm s0 es' tv vv r /\
  fn_has_code sm su func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
    (!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
           ~is_word_type (expr_type e) ==>
           type_memory_bytes ce (expr_type e) = type_memory_size tvt /\
           type_memory_size tvt < 2 ** 64) ==>
  frag_exec ctx sm su (\s. s = r)
    (\s. expr_post ctx func ce cx e es'
      (sa with cs_next_var := sm.cs_next_var) su r es' v op s) R
Proof
  cheat
QED

Theorem expr_post_rebased_lookup:
  expr_post ctx func ce cx e es (sa with cs_next_var := sm.cs_next_var)
    su r es' v op s /\
  not_fresh_at sm x /\ lookup_var x r = SOME w ==>
  lookup_var x s = SOME w
Proof
  cheat
QED

(* Store the just-unwrapped value.  Both reference-state frames are composed
   here, so consumers need not inspect the rebased expr_post. *)
Theorem aggregate_store_rebased_slice_run:
  compile_store_memory ce op (Var x) (expr_type e) (expr_type e) su = ((),sb) /\
  expr_post ctx func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
    su r es' v op s /\
  not_fresh_at sm x /\ lookup_var x r = SOME w /\
  sm.cs_next_var <= su.cs_next_var /\
  (!z. op = Var z ==> not_fresh_at su z) /\
  local_ptrs_reserved ce sm /\ local_ptrs_reserved ce su /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes ce (expr_type e) = type_memory_size tv /\
  type_memory_size tv < dimword (:256) /\
  stmt_state_rel ctx func ce cx es' r /\
  (!n b k. local_region ce es'.scopes r n b k ==>
    b + k <= w2n w \/ w2n w + type_memory_size tv <= b) /\
  (ce.ce_is_ctor ==> !name itv iv off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es'.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) (w2n w) (type_memory_size tv)) ==>
  ?q. run_inst_seq (emitted_insts su sb) s = OK q /\
    val_in_memory tv v (w2n w) q.vs_memory /\
    stmt_state_rel ctx func ce cx es' q /\
    (!z a. not_fresh_at sm z /\ lookup_var z r = SOME a ==>
      lookup_var z q = SOME a) /\
    (!aid b. FLOOKUP r.vs_allocas aid = SOME b ==>
      FLOOKUP q.vs_allocas aid = SOME b) /\
    (!aid off sz a k.
      FLOOKUP r.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
      (!n b len. local_region ce es'.scopes r n b len ==>
        off + sz <= b \/ b + len <= off) /\
      off <= a /\ a + k <= off + sz /\
      (a + k <= w2n w \/ w2n w + type_memory_size tv <= a) ==>
      mem_bytes_at a k q.vs_memory = mem_bytes_at a k r.vs_memory) /\
    locals_kept ce es' r q
Proof
  cheat
QED

Theorem aggregate_store_memory_straight:
  compile_store_memory ce src dst ty ty sa = ((),sb) ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)
Proof
  cheat
QED

Theorem aggregate_store_rebased_slice_sim:
  compile_store_memory ce op (Var x) (expr_type e) (expr_type e) su = ((),sb) /\
  not_fresh_at sm x /\ lookup_var x r = SOME w /\
  sm.cs_next_var <= su.cs_next_var /\
  (!z. op = Var z ==> not_fresh_at su z) /\
  local_ptrs_reserved ce sm /\ local_ptrs_reserved ce su /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes ce (expr_type e) = type_memory_size tv /\
  type_memory_size tv < dimword (:256) /\
  stmt_state_rel ctx func ce cx es' r /\
  (!n b k. local_region ce es'.scopes r n b k ==>
    b + k <= w2n w \/ w2n w + type_memory_size tv <= b) /\
  (ce.ce_is_ctor ==> !name itv iv off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es'.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) (w2n w) (type_memory_size tv)) ==>
  frag_exec ctx su sb
    (\s. expr_post ctx func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
      su r es' v op s)
    (\q. val_in_memory tv v (w2n w) q.vs_memory /\
      stmt_state_rel ctx func ce cx es' q /\
      (!z a. not_fresh_at sm z /\ lookup_var z r = SOME a ==>
        lookup_var z q = SOME a) /\
      (!aid b. FLOOKUP r.vs_allocas aid = SOME b ==>
        FLOOKUP q.vs_allocas aid = SOME b) /\
      (!aid off sz a k.
        FLOOKUP r.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
        (!n b len. local_region ce es'.scopes r n b len ==>
          off + sz <= b \/ b + len <= off) /\
        off <= a /\ a + k <= off + sz /\
        (a + k <= w2n w \/ w2n w + type_memory_size tv <= a) ==>
        mem_bytes_at a k q.vs_memory = mem_bytes_at a k r.vs_memory) /\
      locals_kept ce es' r q) R
Proof
  cheat
QED

Theorem aggregate_child_add_then:
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  local_ptrs_reserved ce sa /\ sa.cs_next_var <= sm.cs_next_var /\
  emit_op ADD [buf; Lit (n2w off)] sm = (dst,sn) /\
  cs_extends sa sm /\ cs_extends sm sn /\ cs_extends sn sb /\
  frag_exec ctx sa sm P
    (\s. ?tv. res = INL tv /\
      vv_post ctx func ce cx e es sa sm s0 es' tv vv s) R /\
  (!tv r. res = INL tv /\
    vv_post ctx func ce cx e es sa sm s0 es' tv vv r ==>
    eval_operand buf r = SOME w) /\
  (!tv r. res = INL tv /\
    vv_post ctx func ce cx e es sa sn s0 es' tv vv r /\
    eval_operand dst r = SOME (w + n2w off) ==>
    frag_exec ctx sn sb (\s. s = r) Q R) ==>
  frag_exec ctx sa sb P Q R
Proof
  cheat
QED

Theorem aggregate_unwrap_store_slice_sim:
  unwrap_value ce vv sm = (op,su) /\
  compile_store_memory ce op (Var x) (expr_type e) (expr_type e) su = ((),sb) /\
  local_ptrs_reserved ce sm /\ local_ptrs_reserved ce su /\
  sa.cs_next_id <= sm.cs_next_id /\
  sm.cs_next_var <= su.cs_next_var /\
  (!z. op = Var z ==> not_fresh_at su z) /\
  cs_extends sm su /\ cs_extends su sb /\
  read_result cx tvv es' = (INL v,es') /\
  vv_post ctx func ce cx e es sa sm s0 es' tvv vv r /\
  not_fresh_at sm x /\ lookup_var x r = SOME w /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes ce (expr_type e) = type_memory_size tv /\
  type_memory_size tv < dimword (:256) /\
  (~is_word_type (expr_type e) ==> type_memory_size tv < 2 ** 64) /\
  fn_has_code sm su func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  stmt_state_rel ctx func ce cx es' r /\
  (!n b k. local_region ce es'.scopes r n b k ==>
    b + k <= w2n w \/ w2n w + type_memory_size tv <= b) /\
  (ce.ce_is_ctor ==> !name itv iv off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es'.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) (w2n w) (type_memory_size tv)) /\
  (!q. val_in_memory tv v (w2n w) q.vs_memory /\
      stmt_state_rel ctx func ce cx es' q /\
      (!z a. not_fresh_at sm z /\ lookup_var z r = SOME a ==>
        lookup_var z q = SOME a) /\
      (!aid b. FLOOKUP r.vs_allocas aid = SOME b ==>
        FLOOKUP q.vs_allocas aid = SOME b) /\
      (!aid off sz a k.
        FLOOKUP r.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
        (!n b len. local_region ce es'.scopes r n b len ==>
          off + sz <= b \/ b + len <= off) /\
        off <= a /\ a + k <= off + sz /\
        (a + k <= w2n w \/ w2n w + type_memory_size tv <= a) ==>
        mem_bytes_at a k q.vs_memory = mem_bytes_at a k r.vs_memory) /\
      locals_kept ce es' r q ==>
      Q q) ==>
  frag_exec ctx sm sb (\s. s = r) Q R
Proof
  cheat
QED

(* Allocation's static provenance is independent of the source expression. *)
Theorem buffer_alloc_provenance:
  compile_alloc_buffer sz sa = (buf,sm) /\
  fn_has_code sa sm func /\ local_ptrs_reserved ce sa ==>
  ?inst x. buf.buf_operand = Var x /\ MEM inst (fn_insts func) /\
    inst.inst_id = sa.cs_next_id /\ inst.inst_outputs = [x] /\
    inst.inst_id < sm.cs_next_id /\ not_fresh_at sm x /\
    local_ptrs_reserved ce sm /\
    (!scopes. not_local_ptr ce scopes x) /\
    sm.cs_blocks = sa.cs_blocks /\ sm.cs_current_bb = sa.cs_current_bb /\
    isPREFIX sa.cs_current_insts sm.cs_current_insts /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sm)
Proof
  cheat
QED

Theorem buffer_local_region_inst_idx[local]:
  local_region ce scopes (t with vs_inst_idx := k) name p n <=>
  local_region ce scopes t name p n
Proof
  cheat
QED

(* Code without GAS leaves the gas readings alone. *)
Theorem buffer_run_gas_readings[local]:
  !code s t. EVERY (\i. i.inst_opcode <> GAS) code /\
    run_inst_seq code s = OK t ==> t.vs_gas_readings = s.vs_gas_readings
Proof
  cheat
QED

Theorem buffer_alloc_frag:
  compile_alloc_buffer sz sa = (buf,sm) /\ fn_has_code sa sm func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  sz < dimword (:256) ==>
  ?inst x. buf.buf_operand = Var x /\ MEM inst (fn_insts func) /\
    inst.inst_id = sa.cs_next_id /\ inst.inst_outputs = [x] /\
    inst.inst_id < sm.cs_next_id /\ not_fresh_at sm x /\
    local_ptrs_reserved ce sm /\ (!scopes. not_local_ptr ce scopes x) /\
    frag_exec ctx sa sm (\s. s = s0 /\ stmt_state_rel ctx func ce cx es s)
      (\t. ?b. stmt_state_rel ctx func ce cx es t /\
        lookup_var x t = SOME (n2w b) /\
        FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) /\
        b + sz < dimword (:256) /\ t.vs_memory = s0.vs_memory /\
        t.vs_gas_readings = s0.vs_gas_readings /\
        (!z. not_fresh_at sa z ==> lookup_var z t = lookup_var z s0) /\
        (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==>
          FLOOKUP t.vs_allocas aid = SOME a) /\
        (!aid p n. aid < sa.cs_next_id /\
          FLOOKUP s0.vs_allocas aid = SOME (p,n) ==>
          regions_disjoint b sz p n) /\
        (!name p n. local_region ce es.scopes t name p n ==>
          regions_disjoint b sz p n) /\
        (!name p n. local_region ce es.scopes t name p n <=>
          local_region ce es.scopes s0 name p n)) R
Proof
  cheat
QED

(* Compose the allocation-entry and aggregate-loop frames once for all
   fresh-buffer constructors. *)
Theorem aggregate_buffer_clearance:
  stmt_state_rel ctx func ce cx es t /\
  local_ptrs_reserved ce sm /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  (!z w. not_fresh_at sm z /\ lookup_var z t = SOME w ==>
         lookup_var z r = SOME w) /\
  (!name lb len. local_region ce es.scopes t name lb len <=>
                  local_region ce es.scopes s0 name lb len) /\
  (!name lb len. local_region ce es.scopes s0 name lb len ==>
                  regions_disjoint b sz lb len)
  ==>
  !name lb len. local_region ce es'.scopes r name lb len ==>
                 b + sz <= lb \/ lb + len <= b
Proof
  cheat
QED

Theorem buffer_loop_memory_vv_post:
  ~is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  val_wf tv v /\ val_in_memory tv v b r.vs_memory /\
  val_footprint tv v <= sz /\ stmt_state_rel ctx func ce cx es' r /\
  p.ptr_location = LocMemory /\
  eval_operand p.ptr_operand r = SOME (n2w b) /\
  ci_mono sa sm /\ ci_mono sm sb /\ sa.cs_next_id < sm.cs_next_id /\
  b + sz < dimword (:256) /\
  (!name lb len. local_region ce es'.scopes r name lb len ==>
    b + sz <= lb \/ lb + len <= b) /\
  FLOOKUP t.vs_allocas sa.cs_next_id = SOME (b,sz) /\
  (!z. not_fresh_at sa z ==> lookup_var z t = lookup_var z s0) /\
  (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==>
    FLOOKUP t.vs_allocas aid = SOME a) /\
  (!aid a n. aid < sa.cs_next_id /\
    FLOOKUP s0.vs_allocas aid = SOME (a,n) ==> regions_disjoint b sz a n) /\
  (!name a n. local_region ce es.scopes t name a n <=>
    local_region ce es.scopes s0 name a n) /\
  (!z w. not_fresh_at sm z /\ lookup_var z t = SOME w ==>
    lookup_var z r = SOME w) /\
  (!aid a. FLOOKUP t.vs_allocas aid = SOME a ==>
    FLOOKUP r.vs_allocas aid = SOME a) /\
  (!aid a n. FLOOKUP t.vs_allocas aid = SOME (a,n) /\
    aid < sm.cs_next_id /\ (a+n <= b \/ b+sz <= a) /\
    (!name lo k. local_region ce es.scopes t name lo k ==>
      a+n <= lo \/ lo+k <= a) ==>
    mem_bytes_at a n r.vs_memory = mem_bytes_at a n t.vs_memory) /\
  t.vs_memory = s0.vs_memory /\ locals_kept ce es t r ==>
  vv_post ctx func ce cx e es sa sb s0 es' (Value v)
    (LocatedValue (expr_type e) p) r
Proof
  cheat
QED

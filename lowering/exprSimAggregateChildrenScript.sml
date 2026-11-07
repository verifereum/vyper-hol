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
  loweringPosts vyperTypeSystem vyperValue valueEncoding valueEncodingProofs vyperTyping
  exprSimAlloc typedMemoryCopy
   exprSimHyps exprSimHypsDefs exprSimUnwrap exprSimUnwrapProps exprSimBufferStore exprSimBuffer
  vyperInterpreter vyperValueOperation vyperState fragExec
  compileEnv context exprSimLiteralBuffer exprSimOps venomState
  exprSimHash exprOperandVar emitHelperProps ASCIInumbers exprLoweringProps venomInst
  vyperEvalExprPreservesScopesDom vyperEvalPreservesScopes oracleExecProps

Theorem typed_value_wf:
  (!ty v. value_has_type ty v ==> val_wf ty v) /\
  (!tvs vs. values_have_types tvs vs ==> tuple_val_wf vs tvs) /\
  (!tv n kvs. sparse_has_type tv n kvs ==> kvs_val_wf kvs tv n) /\
  (!tv vs. all_have_type tv vs ==> elems_val_wf vs tv) /\
  (!ftvs fields. struct_has_type ftvs fields ==> fields_val_wf fields ftvs)
Proof
  cheat
QED

Theorem nonbytes_val_footprint:
  (!n. tv <> BaseTV (BytesT (Dynamic n))) /\
  (!n. tv <> BaseTV (StringT n)) ==>
  val_footprint tv v = type_memory_size tv
Proof
  cheat
QED

Theorem evaluated_nonbytes_footprint:
  ~is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv ==>
  val_footprint tv v = type_memory_size tv
Proof
  cheat
QED
Theorem arg_fits_zero_memory_size:
  (!sty dty. !stv dtv.
    arg_type_fits sty dty /\
    evaluate_type tenv sty = SOME stv /\
    evaluate_type tenv dty = SOME dtv ==>
    (type_memory_size stv = 0 <=> type_memory_size dtv = 0)) /\
  (!stys dtys. !stvs dtvs.
    arg_types_fit stys dtys /\
    OPT_MMAP (evaluate_type tenv) stys = SOME stvs /\
    OPT_MMAP (evaluate_type tenv) dtys = SOME dtvs ==>
    (type_memory_size_list stvs = 0 <=> type_memory_size_list dtvs = 0))
Proof
  cheat
QED

Theorem widening_zero_memory_size:
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\
  evaluate_type tenv dty = SOME dtv ==>
  (type_memory_size stv = 0 <=> type_memory_size dtv = 0)
Proof
  cheat
QED


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

(* Materialization keeps the child's physical post layout, including widened
   internal-call buffers. *)
Theorem unwrap_value_materialise_physical_sim:
  !ctx func cenv cx e es sa sm sb s0 es' tv v vv op R.
    unwrap_value cenv vv sm = (op,sb) /\
    local_ptrs_reserved cenv sa /\ MAP FDOM es.scopes = MAP FDOM es'.scopes /\
    sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\
    read_result cx tv es' = (INL v,es') /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
    (!tvt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME tvt /\
           ~is_word_type (post_value_type cenv e) ==>
           type_memory_bytes cenv (post_value_type cenv e) = type_memory_size tvt /\
           type_memory_size tvt < 2 ** 64) ==>
    frag_exec ctx sm sb
      (\s. vv_post ctx func cenv cx e es sa sm s0 es' tv vv s)
      (\s. expr_post ctx func cenv cx e es sa sb s0 es' v op s) R
Proof
  cheat
QED

Theorem unwrap_value_materialise_sim:
  !ctx func cenv cx e es sa sm sb s0 es' tv v vv op R.
    post_value_type cenv e = expr_type e /\
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

Theorem vv_own_start_var[simp]:
  vv_own ce cx ty (sa with cs_next_var := n) sb es tv vv s <=>
  vv_own ce cx ty sa sb es tv vv s
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

Theorem unwrap_value_rebased_physical_sim:
  unwrap_value ce vv sm = (op,su) /\ local_ptrs_reserved ce sm /\
  sa.cs_next_id <= sm.cs_next_id /\
  read_result cx tv es' = (INL v,es') /\
  vv_post ctx func ce cx e es sa sm s0 es' tv vv r /\
  fn_has_code sm su func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
    (!tvt. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tvt /\
           ~is_word_type (post_value_type ce e) ==>
           type_memory_bytes ce (post_value_type ce e) = type_memory_size tvt /\
           type_memory_size tvt < 2 ** 64) ==>
  frag_exec ctx sm su (\s. s = r)
    (\s. expr_post ctx func ce cx e es'
      (sa with cs_next_var := sm.cs_next_var) su r es' v op s) R
Proof
  cheat
QED

Theorem unwrap_value_rebased_sim:
  post_value_type ce e = expr_type e /\
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

(* Restrict the expression's old-allocation frame before composing a store.
   The allocation identity remains explicit at this boundary. *)
Theorem expr_post_rebased_slice:
  expr_post ctx func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
    su r es' v op s /\
  FLOOKUP r.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
  (!n b k. local_region ce es'.scopes r n b k ==>
    off + sz <= b \/ b + k <= off) /\
  off <= a /\ a + len <= off + sz ==>
  mem_bytes_at a len s.vs_memory = mem_bytes_at a len r.vs_memory
Proof
  cheat
QED

Theorem expr_post_rebased_store_slice:
  expr_post ctx func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
    su r es' v op s /\
  FLOOKUP r.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
  (!n b k. local_region ce es'.scopes r n b k ==>
    off + sz <= b \/ b + k <= off) /\
  off <= a /\ a + len <= off + sz /\
  (!a len. a + len <= dst \/ dst + n <= a ==>
    mem_bytes_at a len q.vs_memory = mem_bytes_at a len s.vs_memory) /\
  (a + len <= dst \/ dst + n <= a) ==>
  mem_bytes_at a len q.vs_memory = mem_bytes_at a len r.vs_memory
Proof
  cheat
QED

(* Store the just-unwrapped value.  Both reference-state frames are composed
   here, so consumers need not inspect the rebased expr_post. *)
Theorem aggregate_store_rebased_slice_run:
  post_value_type ce e = expr_type e /\
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
  post_value_type ce e = expr_type e /\
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
  post_value_type ce e = expr_type e /\
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
  post_value_type ce e = expr_type e /\
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

(* Interface probe: disjoint allocations give full-layout source safety. *)
Theorem aggregate_allocated_source_bounds:
  stmt_state_rel ctx func ce cx es s /\
  FLOOKUP s.vs_allocas aid = SOME (a,n) /\
  FLOOKUP s.vs_allocas did = SOME (b,k) /\ aid <> did /\
  a <= src /\ src + len <= a+n /\
  b <= dst /\ dst + dlen <= b+k ==>
  src + len < dimword (:256) /\
  (src + len <= dst \/ dst + dlen <= src)
Proof
  cheat
QED

Theorem aggregate_physical_source_bounds:
  expr_val_at ce cx ty sa sb es v op s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  val_footprint tv v = type_memory_size tv /\ 0 < type_memory_size tv /\
  eval_operand op s = SOME sw /\ stmt_state_rel ctx func ce cx es s /\
  FLOOKUP s.vs_allocas did = SOME (b,k) /\ did < sa.cs_next_id /\
  b <= dst /\ dst + dlen <= b+k /\
  (!name a n. local_region ce es.scopes s name a n ==>
    a+n <= dst \/ dst+dlen <= a) ==>
  w2n sw + type_memory_size tv < dimword (:256) /\
  (w2n sw + type_memory_size tv <= dst \/ dst+dlen <= w2n sw)
Proof
  cheat
QED

Theorem aggregate_physical_source_slot_bounds:
  expr_val_at ce cx sty sa sb es v op s /\
  evaluate_type (get_tenv cx) sty = SOME tv /\ ~is_word_type sty /\
  ~is_bytestring_type sty /\
  type_widens_to (get_tenv cx) sty dty /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  eval_operand op s = SOME sw /\ stmt_state_rel ctx func ce cx es s /\
  FLOOKUP s.vs_allocas did = SOME (b,k) /\ did < sa.cs_next_id /\
  b <= w2n dw /\ w2n dw + type_memory_size dtv <= b+k /\
  (!name a n. local_region ce es.scopes s name a n ==>
    a+n <= w2n dw \/ w2n dw + type_memory_size dtv <= a) ==>
  w2n sw + type_memory_size tv < dimword (:256) /\
  (w2n sw + type_memory_size tv <= w2n dw \/
   w2n dw + type_memory_size dtv <= w2n sw)
Proof
  cheat
QED

Theorem aggregate_child_physical_encoding:
  expr_body_pre ce cx env e es /\
  (do res <- eval_expr cx e; read_result cx res od) es = (INL v,es') /\
  expr_post ctx func ce cx e ers sa sb r es' v op s /\
  ~is_word_type (post_value_type ce e) ==>
  ?stv sw.
    evaluate_type (get_tenv cx) (post_value_type ce e) = SOME stv /\
    value_has_type stv v /\ val_wf stv v /\
    eval_operand op s = SOME sw /\
    val_in_memory stv v (w2n sw) s.vs_memory /\
    type_widens_to (get_tenv cx) (post_value_type ce e) (expr_type e)
Proof
  cheat
QED

(* Typed copies may change the control location, but not the data-state
   invariants used by the aggregate store frame. *)
Theorem aggregate_store_control_frame:
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sa /\
  (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
            vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
            vs_inst_idx := s.vs_inst_idx|>) = s /\
  (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s) /\
  (!a k. a+k <= dst \/ dst+n <= a ==>
    mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory) /\
  (!name b sz. local_region ce es.scopes s name b sz ==>
    b+sz <= dst \/ dst+n <= b) /\
  LENGTH s.vs_memory <= LENGTH q.vs_memory /\
  (ce.ce_is_ctor ==> !name tv v off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    regions_disjoint off (type_memory_size tv) dst n) ==>
  stmt_state_rel ctx func ce cx es q
Proof
  cheat
QED


Theorem aggregate_store_rebased_control_frame:
  expr_post ctx func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
    su r es' v op s /\
  sm.cs_next_var <= su.cs_next_var /\
  local_ptrs_reserved ce sm /\ local_ptrs_reserved ce su /\
  (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
    vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
    vs_inst_idx := s.vs_inst_idx|>) = s /\
  (!z. not_fresh_at su z ==> lookup_var z q = lookup_var z s) /\
  (!a len. a+len <= dst \/ dst+n <= a ==>
    mem_bytes_at a len q.vs_memory = mem_bytes_at a len s.vs_memory) /\
  (!name b k. local_region ce es'.scopes s name b k ==>
    b+k <= dst \/ dst+n <= b) /\
  LENGTH s.vs_memory <= LENGTH q.vs_memory /\
  (ce.ce_is_ctor ==> !name tv v off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es'.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    regions_disjoint off (type_memory_size tv) dst n) ==>
  stmt_state_rel ctx func ce cx es' q /\
  (!z a. not_fresh_at sm z /\ lookup_var z r = SOME a ==>
    lookup_var z q = SOME a) /\
  (!aid b. FLOOKUP r.vs_allocas aid = SOME b ==>
    FLOOKUP q.vs_allocas aid = SOME b) /\
  (!aid off sz a len.
    FLOOKUP r.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
    (!name b k. local_region ce es'.scopes r name b k ==>
      off+sz <= b \/ b+k <= off) /\
    off <= a /\ a+len <= off+sz /\ (a+len <= dst \/ dst+n <= a) ==>
    mem_bytes_at a len q.vs_memory = mem_bytes_at a len r.vs_memory) /\
  locals_kept ce es' r q
Proof
  cheat
QED

Theorem aggregate_store_body_typed_run:
  compile_store_memory_typed ce (Var x) (expr_type e) op
    (post_value_type ce e) su = ((),sb) /\
  expr_body_pre ce cx env e es /\
  (do res <- eval_expr cx e; read_result cx res od) es = (INL v,es') /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  ~is_word_type (post_value_type ce e) /\
  ~is_bytestring_type (post_value_type ce e) /\
  expr_post ctx func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
    su r es' v op s /\
  not_fresh_at sm x /\ lookup_var x r = SOME w /\
  sm.cs_next_var <= su.cs_next_var /\
  (!z. op = Var z ==> not_fresh_at su z) /\
  local_ptrs_reserved ce sm /\ local_ptrs_reserved ce su /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  stmt_state_rel ctx func ce cx es' r /\
  FLOOKUP r.vs_allocas did = SOME (b,k) /\ did < sa.cs_next_id /\
  b <= w2n w /\ w2n w + type_memory_size tv <= b+k /\
  w2n w + type_memory_size tv < dimword (:256) /\
  (!name a len. local_region ce es'.scopes r name a len ==>
    a+len <= w2n w \/ w2n w + type_memory_size tv <= a) /\
  (ce.ce_is_ctor ==> !name itv iv off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es'.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) (w2n w) (type_memory_size tv)) /\
  fn_has_code su sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = su.cs_current_bb /\ s.vs_inst_idx = LENGTH su.cs_current_insts ==>
  ?q. val_in_memory tv v (w2n w) q.vs_memory /\
    stmt_state_rel ctx func ce cx es' q /\
    ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!z a. not_fresh_at sm z /\ lookup_var z r = SOME a ==> lookup_var z q = SOME a) /\
    (!aid a. FLOOKUP r.vs_allocas aid = SOME a ==> FLOOKUP q.vs_allocas aid = SOME a) /\
    (!aid off sz a len.
      FLOOKUP r.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
      (!name b k. local_region ce es'.scopes r name b k ==>
        off+sz <= b \/ b+k <= off) /\
      off <= a /\ a+len <= off+sz /\
      (a+len <= w2n w \/ w2n w+type_memory_size tv <= a) ==>
      mem_bytes_at a len q.vs_memory = mem_bytes_at a len r.vs_memory) /\
    locals_kept ce es' r q /\
    (!fuel rr. run_from fuel ctx fn q = rr /\ (!err. rr <> Error err) ==>
      ?fuel'. run_from fuel' ctx fn s = rr)
Proof
  cheat
QED

Theorem aggregate_store_body_typed_sim:
  compile_store_memory_typed ce (Var x) (expr_type e) op
    (post_value_type ce e) su = ((),sb) /\
  expr_body_pre ce cx env e es /\
  (do res <- eval_expr cx e; read_result cx res od) es = (INL v,es') /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  ~is_word_type (post_value_type ce e) /\
  ~is_bytestring_type (post_value_type ce e) /\
  not_fresh_at sm x /\ lookup_var x r = SOME w /\
  sm.cs_next_var <= su.cs_next_var /\
  (!z. op = Var z ==> not_fresh_at su z) /\
  local_ptrs_reserved ce sm /\ local_ptrs_reserved ce su /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  stmt_state_rel ctx func ce cx es' r /\
  FLOOKUP r.vs_allocas did = SOME (b,k) /\ did < sa.cs_next_id /\
  b <= w2n w /\ w2n w + type_memory_size tv <= b+k /\
  w2n w + type_memory_size tv < dimword (:256) /\
  (!name a len. local_region ce es'.scopes r name a len ==>
    a+len <= w2n w \/ w2n w + type_memory_size tv <= a) /\
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
      (!z a. not_fresh_at sm z /\ lookup_var z r = SOME a ==> lookup_var z q = SOME a) /\
      (!aid a. FLOOKUP r.vs_allocas aid = SOME a ==> FLOOKUP q.vs_allocas aid = SOME a) /\
      (!aid off sz a len.
        FLOOKUP r.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
        (!name b k. local_region ce es'.scopes r name b k ==>
          off+sz <= b \/ b+k <= off) /\
        off <= a /\ a+len <= off+sz /\
        (a+len <= w2n w \/ w2n w+type_memory_size tv <= a) ==>
        mem_bytes_at a len q.vs_memory = mem_bytes_at a len r.vs_memory) /\
      locals_kept ce es' r q) R
Proof
  cheat
QED

Theorem compile_store_memory_post_type:
  !ce e env src dst.
    well_typed_expr env e ==>
    compile_store_memory ce src dst (expr_type e) (lowered_value_type ce e) =
    compile_store_memory ce src dst (expr_type e) (post_value_type ce e)
Proof
  cheat
QED

Theorem aggregate_store_body_rebased_slice_sim:
  compile_store_memory ce op (Var x) (expr_type e) (lowered_value_type ce e)
    su = ((),sb) /\
  expr_body_pre ce cx env e es /\
  (do res <- eval_expr cx e; read_result cx res od) es = (INL v,es') /\
  (int_calls_expr e <> [] /\ lowered_value_type ce e <> expr_type e ==>
    acyclic_struct_metadata ce.ce_struct_fields) /\
  not_fresh_at sm x /\ lookup_var x r = SOME w /\
  sm.cs_next_var <= su.cs_next_var /\
  (!z. op = Var z ==> not_fresh_at su z) /\
  local_ptrs_reserved ce sm /\ local_ptrs_reserved ce su /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes ce (expr_type e) = type_memory_size tv /\
  type_memory_size tv < dimword (:256) /\
  stmt_state_rel ctx func ce cx es' r /\
  FLOOKUP r.vs_allocas did = SOME (b,k) /\ did < sa.cs_next_id /\
  b <= w2n w /\ w2n w + type_memory_size tv <= b+k /\
  w2n w + type_memory_size tv < dimword (:256) /\
  (!name a len. local_region ce es'.scopes r name a len ==>
    a+len <= w2n w \/ w2n w + type_memory_size tv <= a) /\
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
      (!z a. not_fresh_at sm z /\ lookup_var z r = SOME a ==> lookup_var z q = SOME a) /\
      (!aid a. FLOOKUP r.vs_allocas aid = SOME a ==> FLOOKUP q.vs_allocas aid = SOME a) /\
      (!aid off sz a len.
        FLOOKUP r.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
        (!name b k. local_region ce es'.scopes r name b k ==>
          off+sz <= b \/ b+k <= off) /\
        off <= a /\ a+len <= off+sz /\
        (a+len <= w2n w \/ w2n w+type_memory_size tv <= a) ==>
        mem_bytes_at a len q.vs_memory = mem_bytes_at a len r.vs_memory) /\
      locals_kept ce es' r q) R
Proof
  cheat
QED

(* Body-aware child continuation: unwrap at the physical post type, then
   re-layout into the destination slot. *)
Theorem aggregate_body_unwrap_store_slice_sim:
  unwrap_value ce vv sm = (op,su) /\
  compile_store_memory ce op (Var x) (expr_type e) (lowered_value_type ce e)
    su = ((),sb) /\
  expr_body_pre ce cx env e es /\
  (do res <- eval_expr cx e; read_result cx res od) es = (INL v,es') /\
  (int_calls_expr e <> [] /\ lowered_value_type ce e <> expr_type e ==>
    acyclic_struct_metadata ce.ce_struct_fields) /\
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
  (!tvt. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tvt /\
    ~is_word_type (post_value_type ce e) ==>
    type_memory_bytes ce (post_value_type ce e) = type_memory_size tvt /\
    type_memory_size tvt < 2 ** 64) /\
  fn_has_code sm su func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  stmt_state_rel ctx func ce cx es' r /\
  FLOOKUP r.vs_allocas did = SOME (b,k) /\ did < sa.cs_next_id /\
  b <= w2n w /\ w2n w + type_memory_size tv <= b+k /\
  w2n w + type_memory_size tv < dimword (:256) /\
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

Theorem aggregate_intcall_result_location:
  compile_call cfn ce rt ty (IntCall fid) args drv sa = (vv,sb) ==>
  !t p. vv = LocatedValue t p ==> p.ptr_location = LocMemory
Proof
  cheat
QED

Theorem aggregate_unequal_post_result_location:
  post_value_type ce e <> expr_type e /\
  compile_expr ce ty e si = (vv,sj) ==>
  !t p. vv = LocatedValue t p ==> p.ptr_location = LocMemory
Proof
  cheat
QED

Theorem unwrap_value_body_rebased_sim:
  compile_expr ce ty e si = (vv,sj) /\
  expr_body_pre ce cx env e es /\
  unwrap_value ce vv sm = (op,su) /\ local_ptrs_reserved ce sm /\
  sa.cs_next_id <= sm.cs_next_id /\
  read_result cx tv es' = (INL v,es') /\
  vv_post ctx func ce cx e es sa sm s0 es' tv vv r /\
  fn_has_code sm su func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) ==>
  frag_exec ctx sm su (\s. s = r)
    (\s. expr_post ctx func ce cx e es'
      (sa with cs_next_var := sm.cs_next_var) su r es' v op s) R
Proof
  cheat
QED

Theorem aggregate_body_child_store_slice_sim:
  compile_expr ce ty e si = (vv,sj) /\
  unwrap_value ce vv sm = (op,su) /\
  compile_store_memory ce op (Var x) (expr_type e) (lowered_value_type ce e)
    su = ((),sb) /\
  expr_body_pre ce cx env e es /\
  (do res <- eval_expr cx e; read_result cx res od) es = (INL v,es') /\
  (int_calls_expr e <> [] /\ lowered_value_type ce e <> expr_type e ==>
    acyclic_struct_metadata ce.ce_struct_fields) /\
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
  fn_has_code sm su func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  stmt_state_rel ctx func ce cx es' r /\
  FLOOKUP r.vs_allocas did = SOME (b,k) /\ did < sa.cs_next_id /\
  b <= w2n w /\ w2n w + type_memory_size tv <= b+k /\
  w2n w + type_memory_size tv < dimword (:256) /\
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
      locals_kept ce es' r q ==> Q q) ==>
  frag_exec ctx sm sb (\s. s = r) Q R
Proof
  cheat
QED

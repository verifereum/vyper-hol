(*
 * Expression simulation for the conditional expression (#636, part 3)
 *
 * x if c else y lowers to c's fragment, a JNZ on its operand, one block per
 * branch that lowers its expression and assigns its operand to a fresh
 * variable, and a JMP from each branch to a common exit block
 * (compile_expr_ifexp).  The source evaluates c and then the branch its
 * boolean picks (eval_expr_ifexp_cases).
 *
 * TOP-LEVEL:
 *   compile_ifexp_vv_sim      — expr_vv_sim of an IfExp from expr_sim of its
 *                               condition, expr_vv_sim of its arms and the
 *                               compile-state shape of their lowering
 *   compile_ifexp_word_vv_sim — its word-typed instance
 *
 * Helpers: compile_expr_ifexp, compile_expr_ifexp_states,
 * eval_expr_ifexp_cases, frag_exec_assign, ifexp_arm_outcome,
 * expr_post_ifexp, vv_post_of_expr_post.
 *)

Theory exprSimIfExp
Ancestors
  exprBopSimProps
  exprSimUnwrapProps exprSimMemorySource
  exprSimProps
  exprSimDefs exprSimVVFrame exprSimSource exprSimHypsDefs
  stmtSimProps gasContext gasOutcome gasSummary gasSummaryCompose gasExemptCert
  fragGasPath fragGasMode fragGasSeq vyperStatePreservation
  loweringPosts typedMemoryCopy exprSimTypedAlloc
  list rich_list finite_map marker exprSimHyps exprSimIfExpCompat exprSimLayoutTransport
  fragExec  exprSimOps exprSimUnwrap freshWrites exprBopLowering loweringSlice
  vyperEvalExprPreservesScopesDom exprLowering emitHelperProps
  exprLoweringProps compileEnv context vyperAST vyperInterpreter vyperState
  vyperValue valueEncoding venomExecSemantics venomExecProofs venomInst
  venomState exprSimLiteralBuffer words integer_word vfmConstants valueEncodingProps
  valueTypingMemoryProps copyFwdEquiv allocaRemapDefs valueEncodingProofs
Libs
  pairLib intLib

Theorem compile_ifexp_arm_unwrap[local]:
  !cenv rt at vv.
    is_word_type rt \/ same_memory_layout cenv at rt ==>
    compile_ifexp_arm cenv rt at vv = unwrap_value cenv vv
Proof
  cheat
QED

Theorem ifexp_layout_refl[local]:
  (!t. punnable cenv t t) /\
  (!ts. punnable_list cenv ts ts)
Proof
  cheat
QED

Theorem ifexp_copy_types[local]:
  !cenv rt at.
    (at = rt \/
     is_bytestring_type rt /\ is_bytestring_type at /\ arg_type_fits at rt \/
     same_memory_layout cenv at rt) /\
    ~is_word_type rt /\ ~same_memory_layout cenv at rt ==>
    is_bytestring_type rt /\ is_bytestring_type at
Proof
  cheat
QED

(* Low-level bytestring copy interface, kept below the operator layer. *)
Theorem ifexp_round_no_wrap[local]:
  !len. 32 + 32 * word_size len < dimword (:256) ==>
    len + 31 < dimword (:256)
Proof
  cheat
QED

Theorem ifexp_round_size[local]:
  !len. 32 + 32 * word_size len < dimword (:256) ==>
    ((((n2w len:bytes32) + 31w) && i2w (- &32)) + 32w =
     n2w (32 + 32 * word_size len))
Proof
  cheat
QED

Theorem ifexp_emit_mcopy_run[local]:
  !sa sb dst src sz d w n s.
    emit_void MCOPY [dst; src; sz] sa = ((),sb) /\
    eval_operand dst s = SOME d /\ eval_operand src s = SOME w /\
    eval_operand sz s = SOME n ==>
    run_inst_seq (emitted_insts sa sb) s =
      OK (mcopy (w2n d) (w2n w) (w2n n) s)
Proof
  cheat
QED

Theorem ifexp_copy_len_shape[local]:
  !src out sa sb.
    compile_bytestring_copy_len src sa = (out,sb) ==>
    same_blocks sa sb /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    sb.cs_next_var = sa.cs_next_var + 4 /\
    sb.cs_next_id = sa.cs_next_id + 4
Proof
  cheat
QED

Theorem ifexp_copy_len_run[local]:
  !src out sa sb s w len.
    compile_bytestring_copy_len src sa = (out,sb) /\
    eval_operand src s = SOME w /\ mload (w2n w) s = n2w len /\
    32 + 32 * word_size len < dimword (:256) ==>
    ?q. run_inst_seq (emitted_insts sa sb) s = OK q /\
      eval_operand out q = SOME (n2w (32 + 32 * word_size len)) /\
      (q with vs_vars := s.vs_vars) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s)
Proof
  cheat
QED

Theorem ifexp_store_bytestring_run[local]:
  !src dst sa sb s w d len.
    compile_store_bytestring src dst sa = ((),sb) /\
    eval_operand src s = SOME w /\ eval_operand dst s = SOME d /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
    mload (w2n w) s = n2w len /\
    32 + 32 * word_size len < dimword (:256) ==>
    ?q. run_inst_seq (emitted_insts sa sb) s = OK q /\
      q.vs_memory = (mcopy (w2n d) (w2n w) (32 + 32 * word_size len) s).vs_memory /\
      (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s)
Proof
  cheat
QED

Theorem ifexp_bytes_header[local]:
  !cap bs src s.
    val_in_memory (BaseTV (BytesT (Dynamic cap))) (BytesV bs) src s.vs_memory ==>
    mload src s = n2w (LENGTH bs)
Proof
  cheat
QED

Theorem ifexp_string_header[local]:
  !cap str src s.
    val_in_memory (BaseTV (StringT cap)) (StringV str) src s.vs_memory ==>
    mload src s = n2w (LENGTH str)
Proof
  cheat
QED

Theorem ifexp_typed_bytestring_header[local]:
  !tenv ty tv v p s.
    is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv /\
    value_has_type tv v /\ val_in_memory tv v p s.vs_memory ==>
    ?len. mload p s = n2w len /\
      val_store_size tv v = 32 + 32 * word_size len
Proof
  cheat
QED

Theorem ifexp_copy_source_bounds[local]:
  !cx ty tv v op s.
    is_bytestring_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
    value_has_type tv v /\ expr_val_rel cx ty v op s ==>
    ?w len. eval_operand op s = SOME w /\
      val_in_memory tv v (w2n w) s.vs_memory /\
      mload (w2n w) s = n2w len /\
      val_store_size tv v = 32 + 32 * word_size len /\
      32 + 32 * word_size len <= type_memory_size tv
Proof
  cheat
QED

Theorem ifexp_vv_at_alloc_frame[local]:
  vv_at cenv cx ty sa sb es raw vv s /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
               FLOOKUP q.vs_allocas aid = SOME entry) /\
  eval_operand (vv_operand vv) q = eval_operand (vv_operand vv) s /\
  (!n b sz. local_region cenv es.scopes q n b sz <=>
            local_region cenv es.scopes s n b sz) /\
  sb.cs_next_id <= sm.cs_next_id ==>
  vv_at cenv cx ty sa sm es raw vv q
Proof
  cheat
QED

Theorem ifexp_vv_own_alloc_frame[local]:
  vv_own cenv cx ty sa sb es raw vv s /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
               FLOOKUP q.vs_allocas aid = SOME entry) /\
  eval_operand (vv_operand vv) q = eval_operand (vv_operand vv) s /\
  (!n b sz. local_region cenv es.scopes q n b sz <=>
            local_region cenv es.scopes s n b sz) /\
  sb.cs_next_id <= sm.cs_next_id ==>
  vv_own cenv cx ty sa sm es raw vv q
Proof
  cheat
QED

Theorem ifexp_alloc_local_regions[local]:
  !ctx func cenv cx es sa s q.
    stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
    (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s) ==>
    !n b sz. local_region cenv es.scopes q n b sz <=>
             local_region cenv es.scopes s n b sz
Proof
  cheat
QED

Theorem ifexp_bytestring_adapter_parts[local]:
  !cenv t arm_ty vv sa op sb.
    ~is_word_type t /\ ~same_memory_layout cenv arm_ty t /\
    is_bytestring_type t /\ compile_ifexp_arm cenv t arm_ty vv sa = (op,sb) ==>
    ?buf sm src sn.
      compile_alloc_buffer (type_memory_bytes cenv t) sa = (buf,sm) /\
      unwrap_value cenv vv sm = (src,sn) /\
      compile_store_bytestring src buf.buf_operand sn = ((),sb) /\
      op = buf.buf_operand
Proof
  cheat
QED

(* Aggregate adapters copy from the physical arm layout into the annotation. *)
Theorem ifexp_zero_source_fits[local]:
  (!sty dty. arg_type_fits sty dty ==>
    !tenv tv. evaluate_type tenv sty = SOME tv /\
      type_memory_size tv = 0 ==> sty = dty) /\
  (!stys dtys. arg_types_fit stys dtys ==>
    !tenv tvs. OPT_MMAP (evaluate_type tenv) stys = SOME tvs /\
      type_memory_size_list tvs = 0 ==> stys = dtys)
Proof
  cheat
QED

Theorem ifexp_widened_source_positive[local]:
  type_widens_to tenv sty dty /\ sty <> dty /\
  evaluate_type tenv sty = SOME stv ==>
  0 < type_memory_size stv
Proof
  cheat
QED

Theorem ifexp_physical_source_positive[local]:
  expr_body_pre cenv cx env e es /\
  post_value_type cenv e <> expr_type e /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME stv ==>
  0 < type_memory_size stv
Proof
  cheat
QED

Theorem ifexp_aggregate_footprint[local]:
  !tenv t tv v.
    evaluate_type tenv t = SOME tv /\ ~is_bytestring_type t ==>
    val_footprint tv v = type_memory_size tv
Proof
  cheat
QED

Theorem ifexp_aggregate_source_region[local]:
  expr_val_at cenv cx ty origin sa es v src s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  ~is_word_type ty /\ ~is_bytestring_type ty /\
  eval_operand src s = SOME w ==>
  type_memory_size tv = 0 \/
  (?aid b sz. aid < sa.cs_next_id /\
    FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
    b <= w2n w /\ w2n w + type_memory_size tv <= b + sz) \/
  (?n b sz. local_region cenv es.scopes s n b sz /\
    b <= w2n w /\ w2n w + type_memory_size tv <= b + sz)
Proof
  cheat
QED

Theorem ifexp_typed_adapter_parts[local]:
  ~is_word_type t /\ ~same_memory_layout cenv arm_ty t /\
  ~is_bytestring_type t /\ arm_ty <> t /\
  compile_ifexp_arm cenv t arm_ty vv sa = (op,sb) ==>
  ?buf sm src sn.
    compile_alloc_buffer (type_memory_bytes cenv t) sa = (buf,sm) /\
    unwrap_value cenv vv sm = (src,sn) /\
    compile_store_memory_typed cenv buf.buf_operand t src arm_ty sn = ((),sb) /\
    op = buf.buf_operand
Proof
  cheat
QED

Theorem ifexp_typed_alloc_source[local]:
  compile_alloc_buffer (type_memory_bytes cenv dty) sa = (buf,sm) /\
  compile_store_memory_typed cenv buf.buf_operand dty src sty sm = ((),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  type_widens_to (get_tenv cx) sty dty /\ sty <> dty /\
  ~is_word_type sty /\ ~is_bytestring_type sty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  type_memory_size dtv < dimword (:256) /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf dtv v /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname, fty, sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  stmt_state_rel ctx func cenv cx es s /\
  expr_val_at cenv cx sty origin sa es v src s /\
  eval_operand src s = SOME sw /\
  val_in_memory stv v (w2n sw) s.vs_memory ==>
  frag_exec ctx sa sb (\z. z = s)
    (\u. ?w. stmt_state_rel ctx func cenv cx es u /\
      eval_operand buf.buf_operand u = SOME w /\
      w2n w + type_memory_size dtv < dimword (:256) /\
      val_in_memory dtv v (w2n w) u.vs_memory /\
      FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,type_memory_size dtv) /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
        FLOOKUP u.vs_allocas aid = SOME entry) /\
      (!off len. off + len <= w2n w \/ w2n w + type_memory_size dtv <= off ==>
        mem_bytes_at off len u.vs_memory = mem_bytes_at off len s.vs_memory) /\
      (!aid b len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
        regions_disjoint (w2n w) (type_memory_size dtv) b len) /\
      (!name b len. local_region cenv es.scopes s name b len ==>
        regions_disjoint (w2n w) (type_memory_size dtv) b len)) R
Proof
  cheat
QED

(* Restore the expression frame after a fresh typed normalization. *)
Theorem ifexp_typed_copy_post[local]:
  expr_post ctx func ce cx e es origin sa s0 es' v src r /\
  local_ptrs_reserved ce origin /\ local_ptrs_reserved ce sa /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  origin.cs_next_var <= sa.cs_next_var /\
  origin.cs_next_id <= sa.cs_next_id /\ sa.cs_next_id < sb.cs_next_id /\
  ~is_word_type dty /\ ~is_bytestring_type dty /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  value_has_type dtv v /\ val_wf dtv v /\
  stmt_state_rel ctx func ce cx es' u /\ eval_operand op u = SOME w /\
  val_in_memory dtv v (w2n w) u.vs_memory /\
  FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,type_memory_size dtv) /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x r) /\
  (!aid entry. FLOOKUP r.vs_allocas aid = SOME entry ==>
    FLOOKUP u.vs_allocas aid = SOME entry) /\
  (!off len. off + len <= w2n w \/ w2n w + type_memory_size dtv <= off ==>
    mem_bytes_at off len u.vs_memory = mem_bytes_at off len r.vs_memory) /\
  (!aid b len. aid < sa.cs_next_id /\ FLOOKUP r.vs_allocas aid = SOME (b,len) ==>
    regions_disjoint (w2n w) (type_memory_size dtv) b len) /\
  (!name b len. local_region ce es'.scopes r name b len ==>
    regions_disjoint (w2n w) (type_memory_size dtv) b len) ==>
  expr_post ctx func ce cx (IfExp dty c a b) es origin sb s0 es' v op u
Proof
  cheat
QED


Theorem ifexp_typed_normalize_post[local]:
  compile_alloc_buffer (type_memory_bytes ce dty) sa = (buf,sm) /\
  compile_store_memory_typed ce buf.buf_operand dty src sty sm = ((),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce origin /\ local_ptrs_reserved ce sa /\
  origin.cs_next_var <= sa.cs_next_var /\ origin.cs_next_id <= sa.cs_next_id /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  sty = post_value_type ce e /\
  type_widens_to (get_tenv cx) sty dty /\ sty <> dty /\
  ~is_word_type sty /\ ~is_bytestring_type sty /\
  ~is_word_type dty /\ ~is_bytestring_type dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  type_memory_bytes ce dty = type_memory_size dtv /\
  type_memory_size dtv < dimword (:256) /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf dtv v /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname, fty, sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) ==>
  frag_exec ctx sa sb
    (\r. expr_post ctx func ce cx e es origin sa s0 es' v src r)
    (\u. expr_post ctx func ce cx (IfExp dty c a b) es origin sb s0 es' v buf.buf_operand u) R
Proof
  cheat
QED

Theorem ifexp_mcopy_window[local]:
  !dst src n s k. k <= n ==>
    mem_bytes_at dst k (mcopy dst src n s).vs_memory =
    mem_bytes_at src k s.vs_memory
Proof
  cheat
QED

Theorem ifexp_mcopy_exterior[local]:
  !dst src n s a k. a + k <= dst \/ dst + n <= a ==>
    mem_bytes_at a k (mcopy dst src n s).vs_memory =
    mem_bytes_at a k s.vs_memory
Proof
  cheat
QED

Theorem ifexp_store_bytestring_encoding[local]:
  !src dst sa sb s w d len tv v.
    compile_store_bytestring src dst sa = ((),sb) /\
    eval_operand src s = SOME w /\ eval_operand dst s = SOME d /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
    mload (w2n w) s = n2w len /\
    val_in_memory tv v (w2n w) s.vs_memory /\ val_wf tv v /\
    val_store_size tv v = 32 + 32 * word_size len /\
    type_memory_size tv < dimword (:256) ==>
    ?q. run_inst_seq (emitted_insts sa sb) s = OK q /\
      val_in_memory tv v (w2n d) q.vs_memory /\
      LENGTH s.vs_memory <= LENGTH q.vs_memory /\
      (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s) /\
      (!a k. a + k <= w2n d \/ w2n d + type_memory_size tv <= a ==>
        mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory)
Proof
  cheat
QED

Theorem ifexp_immutable_destination_sep[local]:
  !ctx func cenv cx es s inst dst sz.
    stmt_state_rel ctx func cenv cx es s /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (dst,sz) ==>
    cenv.ce_is_ctor ==> !name tv v off.
      FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
      FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
        | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
      regions_disjoint off (type_memory_size tv) dst sz
Proof
  cheat
QED

Theorem ifexp_bytestring_store_state[local]:
  !ctx func cenv cx es src dst sa sb s w d len tv v inst.
    compile_store_bytestring src dst sa = ((),sb) /\
    eval_operand src s = SOME w /\ eval_operand dst s = SOME d /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
    mload (w2n w) s = n2w len /\
    val_in_memory tv v (w2n w) s.vs_memory /\ val_wf tv v /\
    val_store_size tv v = 32 + 32 * word_size len /\
    type_memory_size tv < dimword (:256) /\
    stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n d,type_memory_size tv) /\
    (!name b sz. local_region cenv es.scopes s name b sz ==>
      b + sz <= w2n d \/ w2n d + type_memory_size tv <= b) ==>
    ?q. run_inst_seq (emitted_insts sa sb) s = OK q /\
      stmt_state_rel ctx func cenv cx es q /\
      val_in_memory tv v (w2n d) q.vs_memory /\
      (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s) /\
      (!a k. a + k <= w2n d \/ w2n d + type_memory_size tv <= a ==>
        mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory)
Proof
  cheat
QED

Theorem ifexp_destination_at[local]:
  !cenv cx ty tv v sa sb es op s w aid.
    evaluate_type (get_tenv cx) ty = SOME tv /\ val_wf tv v /\
    eval_operand op s = SOME w /\
    FLOOKUP s.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\
    sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
    (!n b sz. local_region cenv es.scopes s n b sz ==>
      w2n w + type_memory_size tv <= b \/ b + sz <= w2n w) ==>
    expr_val_at cenv cx ty sa sb es v op s
Proof
  cheat
QED

Theorem ifexp_alloc_preserves_post[local]:
  !ctx func cenv cx e es origin sa sm buf sz s0 es' raw vv s.
    compile_alloc_buffer sz sa = (buf,sm) /\
    vv_post ctx func cenv cx e es origin sa s0 es' raw vv s /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    origin.cs_next_var <= sa.cs_next_var /\ sz < dimword (:256) /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) /\
    (!x. vv_operand vv = Var x ==> not_fresh_at sa x) ==>
    ?q w. run_inst_seq (emitted_insts sa sm) s = OK q /\
      vv_post ctx func cenv cx e es origin sm s0 es' raw vv q /\
      eval_operand buf.buf_operand q = SOME w /\
      FLOOKUP q.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
      q.vs_memory = s.vs_memory
Proof
  cheat
QED

(* Rebase variables without changing allocation ownership. *)
Theorem ifexp_expr_val_at_start_var[local,simp]:
  expr_val_at ce cx ty (sa with cs_next_var := n) sb es v op s <=>
  expr_val_at ce cx ty sa sb es v op s
Proof
  cheat
QED

Theorem ifexp_vv_at_start_var[local,simp]:
  vv_at ce cx ty (sa with cs_next_var := n) sb es tv vv s <=>
  vv_at ce cx ty sa sb es tv vv s
Proof
  cheat
QED

Theorem ifexp_vv_own_start_var[local,simp]:
  vv_own ce cx ty (sa with cs_next_var := n) sb es tv vv s <=>
  vv_own ce cx ty sa sb es tv vv s
Proof
  cheat
QED

Theorem ifexp_vv_post_rebase[local]:
  vv_post ctx func ce cx e es sa sm s0 es' tv vv r ==>
  vv_post ctx func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
    sm r es' tv vv r
Proof
  cheat
QED

Theorem ifexp_expr_post_rebased_operand[local]:
  expr_post ctx func ce cx e es (sa with cs_next_var := sm.cs_next_var)
    su r es' v op s /\ not_fresh_at sm x /\
  eval_operand (Var x) r = SOME w ==>
  eval_operand (Var x) s = SOME w
Proof
  cheat
QED

Theorem ifexp_rebased_store_run[local]:
  compile_store_bytestring src (Var x) sn = ((),sb) /\
  expr_post ctx func ce cx e es' (origin with cs_next_var := sm.cs_next_var)
    sn r es' v src s /\
  not_fresh_at sm x /\ eval_operand (Var x) r = SOME d /\
  sm.cs_next_var <= sn.cs_next_var /\
  (!z. src = Var z ==> not_fresh_at sn z) /\
  local_ptrs_reserved ce sm /\ local_ptrs_reserved ce sn /\
  is_bytestring_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\ type_memory_size tv < dimword (:256) /\
  stmt_state_rel ctx func ce cx es' r /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP r.vs_allocas inst.inst_id = SOME (w2n d,type_memory_size tv) /\
  (!n b k. local_region ce es'.scopes r n b k ==>
    b + k <= w2n d \/ w2n d + type_memory_size tv <= b) ==>
  ?q. run_inst_seq (emitted_insts sn sb) s = OK q /\
    val_in_memory tv v (w2n d) q.vs_memory /\
    stmt_state_rel ctx func ce cx es' q /\
    eval_operand (Var x) q = SOME d /\
    (!z a. not_fresh_at sm z /\ lookup_var z r = SOME a ==>
      lookup_var z q = SOME a) /\
    (!aid b. FLOOKUP r.vs_allocas aid = SOME b ==>
      FLOOKUP q.vs_allocas aid = SOME b) /\
    (!a k. a + k <= w2n d \/ w2n d + type_memory_size tv <= a ==>
      mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory) /\
    locals_kept ce es' r q
Proof
  cheat
QED

Theorem ifexp_rebased_old_memory[local]:
  vv_post ctx func ce cx e es origin sm s0 es' raw vv r /\
  expr_post ctx func ce cx e es' (origin with cs_next_var := sm.cs_next_var)
    sn r es' v src s /\
  stmt_state_rel ctx func ce cx es s0 /\ local_ptrs_reserved ce origin /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  FLOOKUP s.vs_allocas dest_id = SOME (dst,cap) /\
  origin.cs_next_id <= dest_id /\
  (!a k. a + k <= dst \/ dst + cap <= a ==>
    mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory) ==>
  !aid off sz.
    FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < origin.cs_next_id /\
    (!n b k. local_region ce es.scopes s0 n b k ==>
      off + sz <= b \/ b + k <= off) ==>
    mem_bytes_at off sz q.vs_memory = mem_bytes_at off sz s0.vs_memory
Proof
  cheat
QED

Theorem ifexp_rebased_store_post_run[local]:
  compile_store_bytestring src (Var x) sn = ((),sb) /\
  vv_post ctx func ce cx e es origin sm s0 es' raw vv r /\
  expr_post ctx func ce cx e es' (origin with cs_next_var := sm.cs_next_var)
    sn r es' v src s /\
  stmt_state_rel ctx func ce cx es s0 /\ local_ptrs_reserved ce origin /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  origin.cs_next_var <= sm.cs_next_var /\
  origin.cs_next_id <= inst.inst_id /\ inst.inst_id < sb.cs_next_id /\
  not_fresh_at sm x /\ eval_operand (Var x) r = SOME d /\
  sm.cs_next_var <= sn.cs_next_var /\
  (!z. src = Var z ==> not_fresh_at sn z) /\
  local_ptrs_reserved ce sm /\ local_ptrs_reserved ce sn /\
  is_bytestring_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\ type_memory_size tv < dimword (:256) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP r.vs_allocas inst.inst_id = SOME (w2n d,type_memory_size tv) /\
  (!n b k. local_region ce es'.scopes r n b k ==>
    b + k <= w2n d \/ w2n d + type_memory_size tv <= b) ==>
  ?q. run_inst_seq (emitted_insts sn sb) s = OK q /\
    expr_post ctx func ce cx e es origin sb s0 es' v (Var x) q
Proof
  cheat
QED

Theorem ifexp_expr_post_inst_idx[local,simp]:
  expr_post ctx func ce cx e es sa sb s0 es' v op (s with vs_inst_idx := n) <=>
  expr_post ctx func ce cx e es sa sb s0 es' v op s
Proof
  cheat
QED

Theorem ifexp_store_bytestring_straight[local]:
  compile_store_bytestring src dst sa = ((),sb) ==>
  sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
  isPREFIX sa.cs_current_insts sb.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)
Proof
  cheat
QED

Theorem ifexp_vv_post_inst_idx[local]:
  vv_post ctx func cenv cx e es sa sb s0 es' raw vv (s with vs_inst_idx := n) <=>
  vv_post ctx func cenv cx e es sa sb s0 es' raw vv s
Proof
  cheat
QED

Theorem ifexp_different_type_unwrap_pure[local]:
  !ce e ty sa vv sb.
    lowered_value_type ce e <> expr_type e /\
    ~is_word_type (expr_type e) /\
    ~is_word_type (lowered_value_type ce e) /\
    compile_expr ce ty e sa = (vv,sb) ==>
    ?op. unwrap_value ce vv = comp_return op
Proof
  cheat
QED


Theorem ifexp_post_annotated[local]:
  (!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
     type_memory_bytes ce ty = type_memory_size tv) /\
  (~is_word_type (expr_type e) ==>
    lowered_value_type ce e = expr_type e \/
    is_bytestring_type (expr_type e) /\ is_bytestring_type (lowered_value_type ce e) /\
      arg_type_fits (lowered_value_type ce e) (expr_type e) \/
    same_memory_layout ce (lowered_value_type ce e) (expr_type e) /\
      arg_type_fits (lowered_value_type ce e) (expr_type e) /\
      ?tvp. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tvp) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v /\
  expr_post ctx func ce cx e es sa sb s0 es' v op s ==>
  expr_post ctx func ce cx (IfExp (expr_type e) c a b) es sa sb s0 es' v op s
Proof
  cheat
QED

Theorem ifexp_aggregate_source_kind[local]:
  !sty dty. arg_type_fits sty dty /\
    ~is_word_type dty /\ ~is_bytestring_type dty ==>
    ~is_word_type sty /\ ~is_bytestring_type sty
Proof
  cheat
QED

(* What compile_expr emits for an IfExp. *)
Theorem compile_expr_ifexp:
  !cenv ty t c a b st vv st'.
    compile_expr cenv ty (IfExp t c a b) st = (vv, st') ==>
    ?cond_op s1 rv s2 tl s3 el s4 xl s5 s6 x6 s7 av s7a aop s8 s9 s10 x10 s11 bv s11a bop
     s12 s13 s14 x14.
      lower_value compile_expr cenv (BaseT BoolT) c st = (cond_op, s1) /\
      fresh_var s1 = (rv, s2) /\
      fresh_label "then" s2 = (tl, s3) /\ fresh_label "else" s3 = (el, s4) /\
      fresh_label "exit" s4 = (xl, s5) /\
      emit_inst JNZ [cond_op; Label tl; Label el] [] s5 = ((), s6) /\
      new_block tl s6 = (x6, s7) /\
      compile_expr cenv ty a s7 = (av, s7a) /\
      compile_ifexp_arm cenv t (lowered_value_type cenv a) av s7a = (aop, s8) /\
      emit_inst ASSIGN [aop] [rv] s8 = ((), s9) /\
      emit_inst JMP [Label xl] [] s9 = ((), s10) /\
      new_block el s10 = (x10, s11) /\
      compile_expr cenv ty b s11 = (bv, s11a) /\
      compile_ifexp_arm cenv t (lowered_value_type cenv b) bv s11a = (bop, s12) /\
      emit_inst ASSIGN [bop] [rv] s12 = ((), s13) /\
      emit_inst JMP [Label xl] [] s13 = ((), s14) /\
      new_block xl s14 = (x14, st') /\
      vv = if is_word_type t then StackValue t (Var rv)
           else LocatedValue t (mk_ptr (Var rv) LocMemory)
Proof
  cheat
QED

Theorem conditional_read_cases[local]:
  !cx raw st res st'.
    (do r <- conditional_result cx raw; read_result cx r od) st = (res,st') ==>
    read_result cx raw st = (res,st') \/
    ?m. conditional_result cx raw st = (INR (Error (TypeError m)),st') /\
        res = INR (Error (TypeError m))
Proof
  cheat
QED

Theorem eval_expr_ifexp_cases:
  !cx t c a b es res es'.
    (do result <- eval_expr cx (IfExp t c a b); read_result cx result od) es =
      (res, es') ==>
    (?exc. (do result <- eval_expr cx c; read_result cx result od) es =
             (INR exc, es') /\ res = INR exc) \/
    (?bv es1.
       (do result <- eval_expr cx c; read_result cx result od) es =
         (INL (BoolV bv), es1) /\
       (do result <- eval_expr cx (if bv then a else b);
           read_result cx result od) es1 = (res, es')) \/
    (?v es1 m.
       (do result <- eval_expr cx c; read_result cx result od) es = (INL v, es1) /\
       v <> BoolV T /\ v <> BoolV F /\
       res = INR (Error (TypeError m))) \/
    (?bv es1 raw es2 m.
       (do result <- eval_expr cx c; read_result cx result od) es =
         (INL (BoolV bv), es1) /\
       eval_expr cx (if bv then a else b) es1 = (INL raw, es2) /\
       conditional_result cx raw es2 = (INR (Error (TypeError m)), es') /\
       res = INR (Error (TypeError m)))
Proof
  cheat
QED

Theorem expr_post_ifexp:
  !func cenv cx t c a b e es es1 es' sa s1 sc sd sb s0 tt u cop aop
             rv v1 v lbl w k xl ctx.
    expr_post ctx func cenv cx c es sa s1 s0 es1 v1 cop tt /\
    expr_post ctx func cenv cx e es1 sc sd (jump_to lbl tt) es' v aop u /\
    post_value_type cenv e = expr_type e /\
    expr_type e = t /\ eval_operand aop u = SOME w /\
    (!x. not_fresh_at sa x ==> x <> rv) /\
    local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s0 /\
    MAP FDOM es.scopes = MAP FDOM es1.scopes /\
    sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= sc.cs_next_var /\
    sa.cs_next_id <= s1.cs_next_id /\ s1.cs_next_id <= sc.cs_next_id /\
    sd.cs_next_id <= sb.cs_next_id ==>
    expr_post ctx func cenv cx (IfExp t c a b) es sa sb s0 es' v (Var rv)
      (jump_to xl (update_var rv w u with vs_inst_idx := k))
Proof
  cheat
QED

(* An ASSIGN as a fragment. *)
Theorem frag_exec_assign:
  !ctx st st' src out P Q R.
    emit_inst ASSIGN [src] [out] st = ((), st') /\
    (!s. P s ==> ?w. eval_operand src s = SOME w /\
                     Q ((update_var out w s) with
                          vs_inst_idx := LENGTH st'.cs_current_insts)) ==>
    frag_exec ctx st st' P Q R
Proof
  cheat
QED

(* expr_post of an operand held by a variable, as vv_post of the value_vv
   compile_expr makes of the variable. *)
Theorem vv_post_of_expr_post:
  !func cenv cx e es sa sb s0 es' v rv s ctx.
    post_value_type cenv e = expr_type e /\
    expr_post ctx func cenv cx e es sa sb s0 es' v (Var rv) s ==>
    vv_post ctx func cenv cx e es sa sb s0 es' (Value v)
      (if is_word_type (expr_type e) then StackValue (expr_type e) (Var rv)
       else LocatedValue (expr_type e) (mk_ptr (Var rv) LocMemory)) s
Proof
  cheat
QED

Theorem ifexp_root_assign_zero_path[local]:
  emit_inst ASSIGN [op] [rv] sa = ((),sb) /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ eval_operand op s = SOME w ==>
  gas_path ctx func s 0
    (OK ((update_var rv w s) with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  cheat
QED

Theorem ifexp_root_eval_forced[local]:
  eval_expr cx (IfExp t c a b) =
  vyperState$bind (vyperState$bind (eval_expr cx c) (read_result cx))
    (\v. if v = BoolV T then vyperState$bind (eval_expr cx a) (conditional_result cx)
         else if v = BoolV F then vyperState$bind (eval_expr cx b) (conditional_result cx)
         else raise (Error (TypeError "not BoolV")))
Proof
  cheat
QED

Theorem ifexp_root_condition_admissible[local]:
  gas_admissible (eval_expr cx (IfExp t c a b)) expr_vv_res_ok es ==>
  gas_admissible (vyperState$bind (eval_expr cx c) (read_result cx)) expr_res_ok es
Proof
  cheat
QED

Theorem ifexp_root_branch_admissible[local]:
  gas_admissible (eval_expr cx (IfExp t c a b)) expr_vv_res_ok es /\
  (!tail. vyperState$bind (eval_expr cx c) (read_result cx)
    (es with gas_obs := xs ++ tail) = (INL (BoolV sel),mid with gas_obs := tail)) ==>
  gas_admissible
    (vyperState$bind (eval_expr cx (if sel then a else b)) (conditional_result cx))
    expr_vv_res_ok (mid with gas_obs := [])
Proof
  cheat
QED

Theorem ifexp_root_condition_bool[local]:
  gas_admissible (eval_expr cx (IfExp t c a b)) expr_vv_res_ok es /\
  vyperState$bind (eval_expr cx c) (read_result cx)
    (es with gas_obs := gs) = (INL v,mid) ==>
  ?sel. v = BoolV sel
Proof
  cheat
QED

Theorem ifexp_root_condition_cert[local]:
  gas_exempt_cert memory tops (ctx,func)
    (vyperState$ignore_bind
      (vyperState$bind (eval_expr cx c) (read_result cx)) (return ()))
    (es,s0) marks (err,ee) (leaf,finalst) ==>
  gas_exempt_cert memory tops (ctx,func)
    (vyperState$ignore_bind (eval_expr cx (IfExp t c a b)) (return ()))
    (es,s0) marks (err,ee) (leaf,finalst)
Proof
  cheat
QED

Theorem ifexp_root_vv_post_of_expr_post_read[local]:
  post_value_type cenv e = expr_type e /\
  expr_post ctx func cenv cx e es sa sb s0 es' v (Var rv) s /\
  read_result cx tv es' = (INL v, es') ==>
  vv_post ctx func cenv cx e es sa sb s0 es' tv
    (if is_word_type (expr_type e) then StackValue (expr_type e) (Var rv)
     else LocatedValue (expr_type e) (mk_ptr (Var rv) LocMemory)) s
Proof
  cheat
QED

(* compile_expr_ifexp with what the two arms of compile_ifexp_vv_sim need
   of its states, from the compile-state shape of the operands' lowering. *)
Theorem ifexp_new_block_fields[local]:
  !lbl sa old sb.
    new_block lbl sa = (old, sb) ==>
    sb.cs_current_bb = lbl /\ sb.cs_current_insts = [] /\
    sb.cs_next_var = sa.cs_next_var /\ sb.cs_next_id = sa.cs_next_id
Proof
  cheat
QED

Theorem compile_expr_ifexp_states:
  !cenv ty t c a b st vv st'.
    compile_expr cenv ty (IfExp t c a b) st = (vv, st') /\
    (!sa sb op. lower_value compile_expr cenv (BaseT BoolT) c sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       sa.cs_next_id <= sb.cs_next_id) /\
    (!e sa sb op. (e = a \/ e = b) /\
       lower_value compile_expr cenv ty e sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       sa.cs_next_id <= sb.cs_next_id) ==>
    ?cond_op s1 rv tl el xl s5 s6 x6 s7 av s7a aop s8 s9 s10 x10 s11 bv s11a bop s12 s13
     s14 x14.
      lower_value compile_expr cenv (BaseT BoolT) c st = (cond_op, s1) /\
      emit_inst JNZ [cond_op; Label tl; Label el] [] s5 = ((), s6) /\
      new_block tl s6 = (x6, s7) /\
      compile_expr cenv ty a s7 = (av, s7a) /\
      compile_ifexp_arm cenv t (lowered_value_type cenv a) av s7a = (aop, s8) /\
      emit_inst ASSIGN [aop] [rv] s8 = ((), s9) /\
      emit_inst JMP [Label xl] [] s9 = ((), s10) /\
      new_block el s10 = (x10, s11) /\
      compile_expr cenv ty b s11 = (bv, s11a) /\
      compile_ifexp_arm cenv t (lowered_value_type cenv b) bv s11a = (bop, s12) /\
      emit_inst ASSIGN [bop] [rv] s12 = ((), s13) /\
      emit_inst JMP [Label xl] [] s13 = ((), s14) /\
      new_block xl s14 = (x14, st') /\
      vv = (if is_word_type t then StackValue t (Var rv)
            else LocatedValue t (mk_ptr (Var rv) LocMemory)) /\
      s5.cs_current_bb = s1.cs_current_bb /\
      s5.cs_current_insts = s1.cs_current_insts /\
      s7.cs_current_bb = tl /\ s11.cs_current_bb = el /\
      st'.cs_current_bb = xl /\ s7.cs_current_insts = [] /\
      s11.cs_current_insts = [] /\ st'.cs_current_insts = [] /\
      cs_extends st s1 /\ cs_extends s1 s5 /\ cs_extends s7 s8 /\
      cs_extends s7 s11 /\ cs_extends s11 s12 /\ cs_extends s11 st' /\
      cs_extends s1 st' /\
      st.cs_next_var <= s1.cs_next_var /\ st.cs_next_id <= s1.cs_next_id /\
      s1.cs_next_var <= s7.cs_next_var /\ s1.cs_next_id <= s7.cs_next_id /\
      s1.cs_next_var <= s11.cs_next_var /\ s1.cs_next_id <= s11.cs_next_id /\
      s8.cs_next_id <= st'.cs_next_id /\ s12.cs_next_id <= st'.cs_next_id /\
      !x. not_fresh_at st x ==> x <> rv
Proof
  cheat
QED

Theorem ifexp_root_code_layout[local]:
  compile_expr cenv ty (IfExp t c a b) st = (vv,st') /\
  fn_has_code st st' func /\ local_ptrs_reserved cenv st /\
  (!sa sb op. lower_value compile_expr cenv (BaseT BoolT) c sa = (op,sb) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id) /\
  (!e sa sb op. (e = a \/ e = b) /\ lower_value compile_expr cenv ty e sa = (op,sb) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id) ==>
  ?cop sc sj sn tl el xl rv se av sea aop sx sy sz.
    lower_value compile_expr cenv (BaseT BoolT) c st = (cop,sc) /\
    emit_inst JNZ [cop; Label tl; Label el] [] sj = ((),sn) /\
    sj.cs_current_bb = sc.cs_current_bb /\ sj.cs_current_insts = sc.cs_current_insts /\
    compile_expr cenv ty (if sel then a else b) se = (av,sea) /\
    compile_ifexp_arm cenv t (lowered_value_type cenv (if sel then a else b)) av sea = (aop,sx) /\
    emit_inst ASSIGN [aop] [rv] sx = ((),sy) /\
    emit_inst JMP [Label xl] [] sy = ((),sz) /\
    se.cs_current_bb = (if sel then tl else el) /\ se.cs_current_insts = [] /\
    st'.cs_current_bb = xl /\ st'.cs_current_insts = [] /\
    vv = (if is_word_type t then StackValue t (Var rv)
          else LocatedValue t (mk_ptr (Var rv) LocMemory)) /\
    fn_has_code st sc func /\ fn_has_code sj sn func /\
    fn_has_code se sx func /\ fn_has_code sx sy func /\ fn_has_code sy sz func /\
    local_ptrs_reserved cenv se /\ cs_extends sc st' /\ cs_extends se sx /\
    st.cs_next_var <= sc.cs_next_var /\ st.cs_next_id <= sc.cs_next_id /\
    sc.cs_next_var <= se.cs_next_var /\ sc.cs_next_id <= se.cs_next_id /\
    sx.cs_next_id <= st'.cs_next_id /\ (!x. not_fresh_at st x ==> x <> rv)
Proof
  cheat
QED

(* Compatibility support is checked independently of the arm composition. *)
Theorem ifexp_abi_size_bound_source:
  evaluate_type env ty = SOME tv /\
  sfields_tenv_consistent (sf : (string, (string # type # num) list) fmap) env ==>
  abi_size_bound sf ty <= vyper_abi_size_bound env ty
Proof
  cheat
QED

Theorem ifexp_abi_tuple_size_bound_source:
  evaluate_types env tys [] = SOME tvs /\
  sfields_tenv_consistent (sf : (string, (string # type # num) list) fmap) env ==>
  abi_size_bound sf (TupleT tys) <= vyper_abi_size_bound env (TupleT tys)
Proof
  cheat
QED

Theorem ifexp_lowered_type_compatible:
  !ce e env.
  well_typed_expr env e /\
  (!id t. FLOOKUP env.var_types id = SOME t ==>
          well_formed_type env.type_defs t) /\
  sfields_tenv_consistent ce.ce_struct_fields env.type_defs /\
  (int_calls_expr e = [] \/ same_memory_layout ce (lowered_value_type ce e) (expr_type e)) ==>
  lowered_value_type ce e = expr_type e \/
  is_bytestring_type (expr_type e) /\ is_bytestring_type (lowered_value_type ce e) /\
    arg_type_fits (lowered_value_type ce e) (expr_type e) \/
  same_memory_layout ce (lowered_value_type ce e) (expr_type e)
Proof
  cheat
QED

Theorem ifexp_body_pre_lowered_type_compatible:
  expr_body_pre ce cx env e es /\
  (int_calls_expr e = [] \/ same_memory_layout ce (lowered_value_type ce e) (expr_type e)) ==>
  lowered_value_type ce e = expr_type e \/
  is_bytestring_type (expr_type e) /\ is_bytestring_type (lowered_value_type ce e) /\
    arg_type_fits (lowered_value_type ce e) (expr_type e) \/
  (same_memory_layout ce (lowered_value_type ce e) (expr_type e) /\
   arg_type_fits (lowered_value_type ce e) (expr_type e) /\
   (?tvp. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tvp))
Proof
  cheat
QED

Theorem ifexp_body_pre_read_typed:
  expr_body_pre ce cx env e es /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v, es') ==>
  ?tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\ value_has_type tvt v
Proof
  cheat
QED

(* ===== Counted simulation ===== *)

Theorem ifexp_arm_seq_path[local]:
  sb.cs_current_bb = sa.cs_current_bb /\
  isPREFIX sa.cs_current_insts sb.cs_current_insts /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> GAS) (emitted_insts sa sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  gas_path ctx func s 0 (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  cheat
QED

Theorem ifexp_arm_rebased_unwrap_path[local]:
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
         type_memory_size tvt < 2 ** 64) /\
  ~r.vs_halted /\ r.vs_current_bb = sm.cs_current_bb /\
  r.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u. gas_path ctx func r 0 (OK u) /\
      expr_post ctx func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
        su r es' v op u /\
      u.vs_current_bb = su.cs_current_bb /\
      u.vs_inst_idx = LENGTH su.cs_current_insts
Proof
  cheat
QED

Theorem ifexp_arm_store_path[local]:
  compile_store_bytestring src dst sa = ((),sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  gas_path ctx func s 0 (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  cheat
QED

Theorem ifexp_arm_unwrap_store_path[local]:
  unwrap_value ce vv sm = (src,sn) /\
  compile_store_bytestring src (Var x) sn = ((),sb) /\
  vv_post ctx func ce cx e es origin sm s0 es' raw vv r /\
  stmt_state_rel ctx func ce cx es s0 /\ local_ptrs_reserved ce origin /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  origin.cs_next_var <= sm.cs_next_var /\ origin.cs_next_id <= sm.cs_next_id /\
  origin.cs_next_id <= inst.inst_id /\ inst.inst_id < sm.cs_next_id /\
  not_fresh_at sm x /\ eval_operand (Var x) r = SOME d /\
  ci_mono sm sn /\ ci_mono sn sb /\
  (!z. vv_operand vv = Var z ==> not_fresh_at sm z) /\
  local_ptrs_reserved ce sm /\ local_ptrs_reserved ce sn /\
  read_result cx raw es' = (INL v,es') /\
  is_bytestring_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\ type_memory_bytes ce (expr_type e) = type_memory_size tv /\
  type_memory_size tv < 2 ** 64 /\
  fn_has_code sm sn func /\ fn_has_code sn sb func /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP r.vs_allocas inst.inst_id = SOME (w2n d,type_memory_size tv) /\
  (!n b k. local_region ce es'.scopes r n b k ==>
    b + k <= w2n d \/ w2n d + type_memory_size tv <= b) /\
  ~r.vs_halted /\ r.vs_current_bb = sm.cs_current_bb /\
  r.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?t. gas_path ctx func r 0 (OK t) /\
      expr_post ctx func ce cx e es origin sb s0 es' v (Var x) t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  cheat
QED

Theorem ifexp_arm_alloc_path[local]:
  compile_alloc_buffer sz sa = (buf,sm) /\
  vv_post ctx func ce cx e es origin sa s0 es' raw vv s /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  origin.cs_next_var <= sa.cs_next_var /\ sz < dimword (:256) /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sa x) /\
  fn_has_code sa sm func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?r d. gas_path ctx func s 0 (OK r) /\
    vv_post ctx func ce cx e es origin sm s0 es' raw vv r /\
    eval_operand buf.buf_operand r = SOME d /\
    FLOOKUP r.vs_allocas sa.cs_next_id = SOME (w2n d,sz) /\
    r.vs_current_bb = sm.cs_current_bb /\
    r.vs_inst_idx = LENGTH sm.cs_current_insts
Proof
  cheat
QED

Theorem ifexp_arm_alloc_separated[local]:
  vv_post ctx func ce cx e es origin sm s0 es' raw vv r /\
  local_ptrs_reserved ce sa /\ fn_inst_ids_distinct func /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
       [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) /\
  eval_operand (Var (STRING #"%" (toString sa.cs_next_var))) r = SOME d /\
  FLOOKUP r.vs_allocas sa.cs_next_id = SOME (w2n d,sz) ==>
  !n b k. local_region ce es'.scopes r n b k ==>
    b + k <= w2n d \/ w2n d + sz <= b
Proof
  cheat
QED

Theorem ifexp_arm_bytestring_path[local]:
  expr_type e = t /\ is_bytestring_type t /\
  ~is_word_type t /\ ~same_memory_layout ce arm_ty t /\
  compile_ifexp_arm ce t arm_ty vv sa = (op,sb) /\
  read_result cx raw es' = (INL v,es') /\
  evaluate_type (get_tenv cx) t = SOME tv /\ value_has_type tv v /\
  type_memory_bytes ce t = type_memory_size tv /\ type_memory_size tv < 2 ** 64 /\
  stmt_state_rel ctx func ce cx es s0 /\ local_ptrs_reserved ce origin /\
  origin.cs_next_var <= sa.cs_next_var /\ origin.cs_next_id <= sa.cs_next_id /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sa x) /\
  vv_post ctx func ce cx e es origin sa s0 es' raw vv s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?q. gas_path ctx func s 0 (OK q) /\
    expr_post ctx func ce cx e es origin sb s0 es' v op q /\
    q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  cheat
QED

Theorem ifexp_arm_raw_admissible[local]:
  gas_admissible (bind (eval_expr cx e) (conditional_result cx))
    expr_vv_res_ok es ==>
  gas_admissible (eval_expr cx e) expr_vv_res_ok es
Proof
  cheat
QED

Theorem ifexp_arm_conditional_read[local]:
  read_result cx raw ee = (INL v,ee) /\
  conditional_result cx raw ee = (res,ss) /\ expr_vv_res_ok res ==>
  ?tv. res = INL tv /\ ss = ee /\
       read_result cx tv ee = (INL v,ee)
Proof
  cheat
QED

Theorem ifexp_arm_conditional_gas_obs[local]:
  conditional_result cx raw ee = (INL tv,ee) ==>
  !tail. conditional_result cx raw (ee with gas_obs := tail) =
    (INL tv,ee with gas_obs := tail)
Proof
  cheat
QED

Theorem ifexp_arm_suffix_path[local]:
  post_value_type ce e = expr_type e /\
  compile_ifexp_arm ce (expr_type e) (lowered_value_type ce e) vv sm = (op,sb) /\
  (~is_word_type (expr_type e) ==>
    lowered_value_type ce e = expr_type e \/
    is_bytestring_type (expr_type e) /\ is_bytestring_type (lowered_value_type ce e) /\
      arg_type_fits (lowered_value_type ce e) (expr_type e) \/
    same_memory_layout ce (lowered_value_type ce e) (expr_type e)) /\
  (!tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
      ~is_word_type (expr_type e) ==>
      type_memory_bytes ce (expr_type e) = type_memory_size tv /\
      type_memory_size tv < 2 ** 64) /\
  (~is_word_type (expr_type e) ==>
    ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v) /\
  read_result cx raw ee = (INL v,ee) /\
  vv_post ctx func ce cx e es sa sm s0 ee raw vv s /\
  stmt_state_rel ctx func ce cx es s0 /\ local_ptrs_reserved ce sa /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?q. gas_path ctx func s 0 (OK q) /\
    expr_post ctx func ce cx e es sa sb s0 ee v op q /\
    q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  cheat
QED

Theorem ifexp_arm_marked_suffix[local]:
  post_value_type ce e = expr_type e /\
  gas_marked_exec F (ctx,func) (eval_expr cx e) (es,s0) marks (INL raw) ee (OK s) /\
  vv_post ctx func ce cx e es sa sm s0 (ee with gas_obs := []) raw vv s /\
  compile_ifexp_arm ce (expr_type e) (lowered_value_type ce e) vv sm = (op,sb) /\
  (~is_word_type (expr_type e) ==>
    lowered_value_type ce e = expr_type e \/
    is_bytestring_type (expr_type e) /\ is_bytestring_type (lowered_value_type ce e) /\
      arg_type_fits (lowered_value_type ce e) (expr_type e) \/
    same_memory_layout ce (lowered_value_type ce e) (expr_type e)) /\
  (!tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
      ~is_word_type (expr_type e) ==>
      type_memory_bytes ce (expr_type e) = type_memory_size tv /\
      type_memory_size tv < 2 ** 64) /\
  (!gs v es2. ~is_word_type (expr_type e) /\
    (do r <- eval_expr cx e; read_result cx r od) (es with gas_obs := gs) = (INL v,es2) ==>
    ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v) /\
  gas_admissible (bind (eval_expr cx e) (conditional_result cx)) expr_vv_res_ok es /\
  stmt_state_rel ctx func ce cx es s0 /\ local_ptrs_reserved ce sa /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?tv v q. gas_marked_exec F (ctx,func) (conditional_result cx raw)
      (ee with gas_obs := [],s) [] (INL tv) (ee with gas_obs := []) (OK q) /\
    read_result cx tv (ee with gas_obs := []) = (INL v,ee with gas_obs := []) /\
    expr_post ctx func ce cx e es sa sb s0 (ee with gas_obs := []) v op q /\
    q.vs_current_bb = sb.cs_current_bb /\ q.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  cheat
QED

Theorem ifexp_arm_ignore_bind_action[local]:
  ignore_bind (bind a (conditional_result cx)) (return ()) =
  bind a (\tv. ignore_bind (conditional_result cx tv) (return ()))
Proof
  cheat
QED

Theorem ifexp_arm_exempt_transport[local]:
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind a (return ())) (es,s0) marks (err,ee) (leaf,finstate) ==>
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (bind a (conditional_result cx)) (return ()))
    (es,s0) marks (err,ee) (leaf,finstate)
Proof
  cheat
QED

Theorem ifexp_arm_outcome[local]:
  !ctx func cenv cx ty e es1 sa sm sb vv op u.
    post_value_type cenv e = expr_type e /\
    expr_vv_sim ctx func cenv cx ty e es1 /\
    compile_expr cenv ty e sa = (vv, sm) /\
    compile_ifexp_arm cenv (expr_type e) (lowered_value_type cenv e) vv sm =
      (op, sb) /\
    (~is_word_type (expr_type e) ==>
      lowered_value_type cenv e = expr_type e \/
      is_bytestring_type (expr_type e) /\
      is_bytestring_type (lowered_value_type cenv e) /\
      arg_type_fits (lowered_value_type cenv e) (expr_type e) \/
      same_memory_layout cenv (lowered_value_type cenv e) (expr_type e)) /\
    (!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
       ~is_word_type (expr_type e) ==>
       type_memory_bytes cenv (expr_type e) = type_memory_size tvt /\
       type_memory_size tvt < 2 ** 64) /\
    (!gs v es2. ~is_word_type (expr_type e) /\
       (do r <- eval_expr cx e; read_result cx r od)
         (es1 with gas_obs := gs) = (INL v, es2) ==>
       ?tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
             value_has_type tvt v) /\
    gas_admissible (bind (eval_expr cx e) (conditional_result cx))
      expr_vv_res_ok es1 /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    stmt_state_rel ctx func cenv cx es1 u /\ ~u.vs_halted /\
    u.vs_current_bb = sa.cs_current_bb /\
    u.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome F (cx_tops cx) (ctx, func)
      (bind (eval_expr cx e) (conditional_result cx)) (es1, u)
      (\res ee t. ?tv v. res = INL tv /\ read_result cx tv ee = (INL v, ee) /\
         expr_post ctx func cenv cx e es1 sa sb u ee v op t /\
         t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts)
      (\res ee r. expr_exit res r)
Proof
  cheat
QED

Theorem ifexp_root_outcome_suffix[local]:
  gas_outcome F tops (ctx,func) source (es,s0) Q R /\
  (!res ee u. Q res ee u /\ ~u.vs_halted ==>
     ?v. gas_path ctx func u 0 (OK v) /\ Q' res ee v) ==>
  gas_outcome F tops (ctx,func) source (es,s0) Q' R
Proof
  cheat
QED

Theorem ifexp_root_suffix_path[local]:
  emit_inst ASSIGN [op] [rv] sx = ((),sy) /\
  emit_inst JMP [Label xl] [] sy = ((),sz) /\
  fn_has_code sx sy func /\ fn_has_code sy sz func /\
  ~u.vs_halted /\ u.vs_current_bb = sx.cs_current_bb /\
  u.vs_inst_idx = LENGTH sx.cs_current_insts /\ eval_operand op u = SOME w ==>
  gas_path ctx func u 0
    (OK (jump_to xl (update_var rv w u with vs_inst_idx := LENGTH sy.cs_current_insts)))
Proof
  cheat
QED

Theorem ifexp_root_finish_post[local]:
  post_value_type cenv e = expr_type e /\
  expr_post ctx func cenv cx c es sa s1 s0 es1 v1 cop tt /\
  expr_post ctx func cenv cx e es1 sc sd (jump_to lbl tt) ee v op u /\
  read_result cx tv ee = (INL v,ee) /\ expr_type e = t /\
  eval_operand op u = SOME w /\ (!x. not_fresh_at sa x ==> x <> rv) /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s0 /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= sc.cs_next_var /\
  sa.cs_next_id <= s1.cs_next_id /\ s1.cs_next_id <= sc.cs_next_id /\
  sd.cs_next_id <= sb.cs_next_id ==>
  vv_post ctx func cenv cx (IfExp t c a b) es sa sb s0 ee tv
    (if is_word_type t then StackValue t (Var rv)
     else LocatedValue t (mk_ptr (Var rv) LocMemory))
    (jump_to xl (update_var rv w u with vs_inst_idx := k))
Proof
  cheat
QED

Theorem ifexp_root_arm_finish[local]:
  post_value_type cenv e = expr_type e /\
  expr_post ctx func cenv cx c es sa s1 s0 es1 v1 cop tt /\
  expr_type e = t /\ (!x. not_fresh_at sa x ==> x <> rv) /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s0 /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= sc.cs_next_var /\
  sa.cs_next_id <= s1.cs_next_id /\ s1.cs_next_id <= sc.cs_next_id /\
  sd.cs_next_id <= sb.cs_next_id /\ sb.cs_current_bb = xl /\ sb.cs_current_insts = [] /\
  emit_inst ASSIGN [op] [rv] sd = ((),sy) /\
  emit_inst JMP [Label xl] [] sy = ((),sz) /\
  fn_has_code sd sy func /\ fn_has_code sy sz func /\
  gas_outcome F tops (ctx,func) source (es1,jump_to lbl tt)
    (\res ee u. ?tv v. res = INL tv /\ read_result cx tv ee = (INL v,ee) /\
      expr_post ctx func cenv cx e es1 sc sd (jump_to lbl tt) ee v op u /\
      u.vs_current_bb = sd.cs_current_bb /\ u.vs_inst_idx = LENGTH sd.cs_current_insts) R ==>
  gas_outcome F tops (ctx,func) source (es1,jump_to lbl tt)
    (\res ee u. ?tv. res = INL tv /\
      vv_post ctx func cenv cx (IfExp t c a b) es sa sb s0 ee tv
        (if is_word_type t then StackValue t (Var rv)
         else LocatedValue t (mk_ptr (Var rv) LocMemory)) u /\
      u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts) R
Proof
  cheat
QED

Theorem ifexp_root_condition_scopes[local]:
  vyperState$bind (eval_expr cx c) (read_result cx)
    (es with gas_obs := gs) = (INL v,mid) ==>
  MAP FDOM es.scopes = MAP FDOM mid.scopes
Proof
  cheat
QED

Theorem ifexp_root_marked_zero_suffix[local]:
  gas_marked_exec F (ctx,func) source (es,s0) marks res mid (OK u) /\
  gas_path ctx func u 0 (OK v) ==>
  gas_marked_exec F (ctx,func) source (es,s0) marks res mid (OK v)
Proof
  cheat
QED

Theorem ifexp_root_selected_outcome_prefix[local]:
  gas_marked_exec F (ctx,func)
    (vyperState$bind (eval_expr cx c) (read_result cx))
    (es,s0) marks (INL (BoolV sel)) mid (OK u) /\
  gas_path ctx func u 0 (OK v) /\
  gas_outcome F tops (ctx,func)
    (vyperState$bind (eval_expr cx (if sel then a else b)) (conditional_result cx))
    (mid with gas_obs := [],v) Q R ==>
  gas_outcome F tops (ctx,func) (eval_expr cx (IfExp t c a b)) (es,s0) Q R
Proof
  cheat
QED

Theorem ifexp_root_condition_exit[local]:
  gas_marked_exec F (ctx,func)
    (vyperState$bind (eval_expr cx c) (read_result cx))
    (es,s0) marks res mid r /\ expr_exit res r ==>
  gas_outcome F tops (ctx,func) (eval_expr cx (IfExp t c a b)) (es,s0) Q
    (\res ee r. expr_exit res r)
Proof
  cheat
QED

Theorem ifexp_root_jnz_path[local]:
  expr_post ctx func cenv cx c es sa sc s0 mid (BoolV sel) cop u /\
  expr_type c = BaseT BoolT /\
  emit_inst JNZ [cop; Label tl; Label el] [] sj = ((),sn) /\
  fn_has_code sj sn func /\ sj.cs_current_bb = sc.cs_current_bb /\
  sj.cs_current_insts = sc.cs_current_insts /\
  ~u.vs_halted /\ u.vs_current_bb = sc.cs_current_bb /\
  u.vs_inst_idx = LENGTH sc.cs_current_insts ==>
  gas_path ctx func u 0 (OK (jump_to (if sel then tl else el) u))
Proof
  cheat
QED

(* x if c else y, from expr_sim of c and expr_vv_sim of the arm that c's
   value picks: the condition's run, the JNZ into the arm's block, the arm
   (ifexp_arm_outcome), the ASSIGN to the result variable and the JMP to the
   exit block. *)
Theorem compile_ifexp_vv_sim:
  !ctx func cenv cx ty t c a b es.
    expr_type c = BaseT BoolT /\ expr_type a = t /\ expr_type b = t /\
    (~is_word_type t ==>
     !e. (e = a \/ e = b) ==>
         lowered_value_type cenv e = expr_type e \/
         is_bytestring_type (expr_type e) /\
         is_bytestring_type (lowered_value_type cenv e) /\
         arg_type_fits (lowered_value_type cenv e) (expr_type e) \/
         same_memory_layout cenv (lowered_value_type cenv e) (expr_type e)) /\
    (!e. (e = a \/ e = b) ==> post_value_type cenv e = expr_type e) /\
    (!tvt. evaluate_type (get_tenv cx) t = SOME tvt /\ ~is_word_type t ==>
       type_memory_bytes cenv t = type_memory_size tvt /\
       type_memory_size tvt < 2 ** 64) /\
    (!sa sb op. lower_value compile_expr cenv (BaseT BoolT) c sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       sa.cs_next_id <= sb.cs_next_id) /\
    (!e sa sb op. (e = a \/ e = b) /\
       lower_value compile_expr cenv ty e sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       sa.cs_next_id <= sb.cs_next_id) /\
    expr_sim ctx func cenv cx (BaseT BoolT) c es /\
    (!gs tv es1.
       (do result <- eval_expr cx c; read_result cx result od)
         (es with gas_obs := gs) = (INL tv, es1) ==>
       expr_sim ctx func cenv cx ty a es1 /\
       expr_sim ctx func cenv cx ty b es1 /\
       expr_vv_sim ctx func cenv cx ty a es1 /\
       expr_vv_sim ctx func cenv cx ty b es1 /\
       !e gs' v es2. ~is_word_type t /\ (e = a \/ e = b) /\
         (do r <- eval_expr cx e; read_result cx r od)
           (es1 with gas_obs := gs') = (INL v, es2) ==>
         ?tvt. evaluate_type (get_tenv cx) t = SOME tvt /\ value_has_type tvt v) ==>
    expr_vv_sim ctx func cenv cx ty (IfExp t c a b) es
Proof
  cheat
QED




Theorem compile_ifexp_word_vv_sim:
  !ctx func cenv cx ty t c a b es.
    expr_type c = BaseT BoolT /\ expr_type a = t /\ expr_type b = t /\
    is_word_type t /\
    (!sa sb op. lower_value compile_expr cenv (BaseT BoolT) c sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       sa.cs_next_id <= sb.cs_next_id) /\
    (!e sa sb op. (e = a \/ e = b) /\
       lower_value compile_expr cenv ty e sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       sa.cs_next_id <= sb.cs_next_id) /\
    expr_sim ctx func cenv cx (BaseT BoolT) c es /\
    (!gs tv es1.
       (do result <- eval_expr cx c; read_result cx result od)
         (es with gas_obs := gs) = (INL tv, es1) ==>
       expr_sim ctx func cenv cx ty a es1 /\
       expr_sim ctx func cenv cx ty b es1 /\
       expr_vv_sim ctx func cenv cx ty a es1 /\
       expr_vv_sim ctx func cenv cx ty b es1) ==>
    expr_vv_sim ctx func cenv cx ty (IfExp t c a b) es
Proof
  cheat
QED

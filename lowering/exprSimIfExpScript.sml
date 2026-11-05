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
 *   compile_ifexp_vv_sim   — expr_vv_sim of an IfExp, on results that are
 *                            values, from expr_sim of its three operands and
 *                            the compile-state shape of their lowering
 *   ifexp_branch_sim       — one arm of it, from the condition's fragment
 *                            through the arm's jump to the exit block
 *
 * Helpers: compile_expr_ifexp, compile_expr_ifexp_states,
 * eval_expr_ifexp_cases, frag_exec_assign, ifexp_arm_frag, ifexp_jnz_arm,
 * expr_post_ifexp, vv_post_of_expr_post.
 *)

Theory exprSimIfExp
Ancestors
  exprBopSimProps
  exprSimUnwrapProps
  exprSimProps
  exprSimDefs
  loweringPosts
  list rich_list finite_map marker exprSimHyps
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

Theorem ifexp_store_bytestring_shape[local]:
  !src dst sa sb.
    compile_store_bytestring src dst sa = ((),sb) ==>
    same_blocks sa sb /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    sb.cs_next_var = sa.cs_next_var + 4 /\
    sb.cs_next_id = sa.cs_next_id + 5
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

Theorem ifexp_alloc_preserves_holds[local]:
  !ctx func cenv cx es sa sm buf sz s et raw vv.
    compile_alloc_buffer sz sa = (buf,sm) /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ sz < dimword (:256) /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) /\
    (!x. vv_operand vv = Var x ==> not_fresh_at sa x) /\
    vv_holds cenv cx et raw vv es s ==>
    ?q w. run_inst_seq (emitted_insts sa sm) s = OK q /\
      stmt_state_rel ctx func cenv cx es q /\
      vv_holds cenv cx et raw vv es q /\
      eval_operand buf.buf_operand q = SOME w /\
      FLOOKUP q.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
      q.vs_memory = s.vs_memory
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

Theorem ifexp_alloc_local_regions[local]:
  !ctx func cenv cx es sa s q.
    stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
    (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s) ==>
    !n b sz. local_region cenv es.scopes q n b sz <=>
             local_region cenv es.scopes s n b sz
Proof
  cheat
QED

Theorem ifexp_alloc_preserves_at[local]:
  !ctx func cenv cx es origin sa sm buf sz s ty raw vv.
    compile_alloc_buffer sz sa = (buf,sm) /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ sz < dimword (:256) /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) /\
    (!x. vv_operand vv = Var x ==> not_fresh_at sa x) /\
    vv_at cenv cx ty origin sa es raw vv s ==>
    ?q. run_inst_seq (emitted_insts sa sm) s = OK q /\
        vv_at cenv cx ty origin sm es raw vv q
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

Theorem ifexp_vv_post_rebase[local]:
  vv_post ctx func ce cx e es sa sm s0 es' tv vv r ==>
  vv_post ctx func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
    sm r es' tv vv r
Proof
  cheat
QED

Theorem ifexp_unwrap_value_rebased_sim[local]:
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

Theorem ifexp_unwrap_store_sim[local]:
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
  fn_has_code sm sn func /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP r.vs_allocas inst.inst_id = SOME (w2n d,type_memory_size tv) /\
  (!n b k. local_region ce es'.scopes r n b k ==>
    b + k <= w2n d \/ w2n d + type_memory_size tv <= b) ==>
  frag_exec ctx sm sb (\s. s = r)
    (\s. expr_post ctx func ce cx e es origin sb s0 es' v (Var x) s) R
Proof
  cheat
QED

Theorem ifexp_vv_post_inst_idx[local]:
  vv_post ctx func cenv cx e es sa sb s0 es' raw vv (s with vs_inst_idx := n) <=>
  vv_post ctx func cenv cx e es sa sb s0 es' raw vv s
Proof
  cheat
QED

Theorem ifexp_bytestring_adapter_sim[local]:
  !ctx func cenv cx e t arm_ty vv sa op sb raw es' v tvt origin es s0 R.
    expr_type e = t /\ is_bytestring_type t /\
    ~is_word_type t /\ ~same_memory_layout cenv arm_ty t /\
    compile_ifexp_arm cenv t arm_ty vv sa = (op,sb) /\
    read_result cx raw es' = (INL v,es') /\
    evaluate_type (get_tenv cx) t = SOME tvt /\ value_has_type tvt v /\
    type_memory_bytes cenv t = type_memory_size tvt /\
    type_memory_size tvt < 2 ** 64 /\
    stmt_state_rel ctx func cenv cx es s0 /\
    local_ptrs_reserved cenv origin /\
    origin.cs_next_var <= sa.cs_next_var /\
    origin.cs_next_id <= sa.cs_next_id /\
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    (!x. vv_operand vv = Var x ==> not_fresh_at sa x) ==>
    frag_exec ctx sa sb
      (\s. vv_post ctx func cenv cx e es origin sa s0 es' raw vv s)
      (\s. expr_post ctx func cenv cx e es origin sb s0 es' v op s) R
Proof
  cheat
QED

Theorem ifexp_copy_arm_success[local]:
  expr_vv_sim ctx func ce cx ty e es /\
  compile_expr ce ty e sa = (vv,sm) /\
  compile_ifexp_arm ce (expr_type e) arm_ty vv sm = (op,sb) /\
  eval_expr cx e es = (INL raw,es') /\
  read_result cx raw es' = (INL v,es') /\
  is_bytestring_type (expr_type e) /\ ~is_word_type (expr_type e) /\
  ~same_memory_layout ce arm_ty (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\ value_has_type tvt v /\
  type_memory_bytes ce (expr_type e) = type_memory_size tvt /\
  type_memory_size tvt < 2 ** 64 /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ stmt_state_rel ctx func ce cx es s0 ==>
  frag_exec ctx sa sb (\s. s = s0)
    (\s. expr_post ctx func ce cx e es sa sb s0 es' v op s)
    (expr_exit (INL raw))
Proof
  cheat
QED

Theorem ifexp_different_type_unwrap[local]:
  !ce e ty sa vv sb.
    lowered_value_type ce e <> expr_type e /\
    ~is_word_type (expr_type e) /\
    ~is_word_type (lowered_value_type ce e) /\
    compile_expr ce ty e sa = (vv,sb) ==>
    ?op. unwrap_value ce vv sb = (op,sb) /\
         lower_value compile_expr ce ty e sa = (op,sb)
Proof
  cheat
QED


Theorem ifexp_actual_arm_sim[local]:
  expr_sim ctx func ce cx ty e es /\ expr_vv_sim ctx func ce cx ty e es /\
  compile_expr ce ty e sa = (vv,sm) /\
  compile_ifexp_arm ce (expr_type e) (lowered_value_type ce e) vv sm = (op,sb) /\
  (~is_word_type (expr_type e) ==>
    lowered_value_type ce e = expr_type e \/
    is_bytestring_type (expr_type e) /\ is_bytestring_type (lowered_value_type ce e) /\
    arg_type_fits (lowered_value_type ce e) (expr_type e) \/
    same_memory_layout ce (lowered_value_type ce e) (expr_type e)) /\
  (!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
     ~is_word_type (expr_type e) ==>
     type_memory_bytes ce (expr_type e) = type_memory_size tvt /\
     type_memory_size tvt < 2 ** 64) /\
  eval_expr cx e es = (eres,es') /\ expr_read_res_ok cx es' eres /\
  (do r <- eval_expr cx e; read_result cx r od) es = (res,es') /\
  (!raw v. eres = INL raw /\ read_result cx raw es' = (INL v,es') ==>
     ?tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\ value_has_type tvt v) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ stmt_state_rel ctx func ce cx es s0 ==>
  frag_exec ctx sa sb (\s. s = s0)
    (\s. ?v. res = INL v /\ expr_post ctx func ce cx e es sa sb s0 es' v op s)
    (expr_exit res)
Proof
  cheat
QED




Theorem ifexp_forced_arm_sim[local]:
  expr_sim ctx func ce cx ty e es /\ expr_vv_sim ctx func ce cx ty e es /\
  compile_expr ce ty e sa = (vv,sm) /\
  compile_ifexp_arm ce (expr_type e) (lowered_value_type ce e) vv sm = (op,sb) /\
  (~is_word_type (expr_type e) ==>
    lowered_value_type ce e = expr_type e \/
    is_bytestring_type (expr_type e) /\ is_bytestring_type (lowered_value_type ce e) /\
    arg_type_fits (lowered_value_type ce e) (expr_type e) \/
    same_memory_layout ce (lowered_value_type ce e) (expr_type e)) /\
  (!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
     ~is_word_type (expr_type e) ==>
     type_memory_bytes ce (expr_type e) = type_memory_size tvt /\
     type_memory_size tvt < 2 ** 64) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (res,es') /\
  expr_res_ok res /\
  (!v. res = INL v ==>
     ?tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\ value_has_type tvt v) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ stmt_state_rel ctx func ce cx es s0 ==>
  frag_exec ctx sa sb (\s. s = s0)
    (\s. ?v. res = INL v /\ expr_post ctx func ce cx e es sa sb s0 es' v op s)
    (expr_exit res)
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
    expr_post ctx func cenv cx e es sa sb s0 es' v (Var rv) s ==>
    vv_post ctx func cenv cx e es sa sb s0 es' (Value v)
      (if is_word_type (expr_type e) then StackValue (expr_type e) (Var rv)
       else LocatedValue (expr_type e) (mk_ptr (Var rv) LocMemory)) s
Proof
  cheat
QED

(* One arm of an IfExp, lowered to eop between bs and bm, then assigned to
   rv: from the jump into the arm's block, the arm's fragment and the
   ASSIGN run to bn with eop's word in rv. *)
Theorem ifexp_arm_frag:
  !ctx func cenv cx ty e es1 res es' bs bm bn eop rv tt lbl.
    (!u. stmt_state_rel ctx func cenv cx es1 u ==>
      frag_exec ctx bs bm (\s. s = u)
        (\s. ?v. res = INL v /\
          expr_post ctx func cenv cx e es1 bs bm u es' v eop s)
        (expr_exit res)) /\
    emit_inst ASSIGN [eop] [rv] bm = ((), bn) /\
    (do result <- eval_expr cx e; read_result cx result od) es1 = (res, es') /\ expr_res_ok res /\
    fn_has_code bs bm func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv bs /\ stmt_state_rel ctx func cenv cx es1 tt /\
    cs_extends bs bm ==>
    frag_exec ctx bs bn (\s. s = jump_to lbl tt)
      (\s. ?v u w. res = INL v /\
             expr_post ctx func cenv cx e es1 bs bm (jump_to lbl tt) es' v eop u /\
             eval_operand eop u = SOME w /\
             s = (update_var rv w u) with
                   vs_inst_idx := LENGTH bn.cs_current_insts)
      (expr_exit res)
Proof
  cheat
QED

(* The JNZ that ends c's code, from the state tt c's fragment ends in: it
   jumps to bl, the block bs starts, where the arm runs as ifexp_arm_frag
   says, and the arm's JMP reaches the exit block xl, which sb starts. *)
Theorem ifexp_jnz_arm:
  !ctx func cenv cx t c a b e bv es es1 es' res sa sb s0 s1 s5 s6 x6 s7
   bs bm bn bo bx bp tl el xl bl lbl rv cond_op eop tt.
    frag_exec ctx bs bn (\s. s = jump_to bl tt)
      (\s. ?v u w. res = INL v /\
             expr_post ctx func cenv cx e es1 bs bm (jump_to bl tt) es' v eop u /\
             eval_operand eop u = SOME w /\
             s = (update_var rv w u) with
                   vs_inst_idx := LENGTH bn.cs_current_insts)
      (expr_exit res) /\
    expr_post ctx func cenv cx c es sa s1 s0 es1 (BoolV bv) cond_op tt /\
    eval_operand cond_op tt = SOME (val_to_w256 (BoolV bv)) /\
    emit_inst JNZ [cond_op; Label tl; Label el] [] s5 = ((), s6) /\
    new_block tl s6 = (x6, s7) /\
    emit_inst JMP [Label xl] [] bn = ((), bo) /\
    new_block lbl bo = (bx, bp) /\
    (if bv then tl else el) = bl /\ bs.cs_current_bb = bl /\
    bs.cs_current_insts = [] /\
    s5.cs_current_bb = s1.cs_current_bb /\
    s5.cs_current_insts = s1.cs_current_insts /\
    sb.cs_current_bb = xl /\ sb.cs_current_insts = [] /\
    cs_extends s1 s6 /\ cs_extends s6 s7 /\ cs_extends s7 sb /\
    cs_extends s1 bs /\ cs_extends bs bn /\ cs_extends bs bp /\
    cs_extends bp sb /\
    sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= bs.cs_next_var /\
    sa.cs_next_id <= s1.cs_next_id /\ s1.cs_next_id <= bs.cs_next_id /\
    bm.cs_next_id <= sb.cs_next_id /\
    expr_type e = t /\ (!x. not_fresh_at sa x ==> x <> rv) /\
    local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s0 /\
    MAP FDOM es.scopes = MAP FDOM es1.scopes ==>
    frag_exec ctx s1 sb (\s. s = tt)
      (\s. ?v. res = INL v /\
                vv_post ctx func cenv cx (IfExp t c a b) es sa sb s0 es' (Value v)
                  (if is_word_type t then StackValue t (Var rv)
                   else LocatedValue t (mk_ptr (Var rv) LocMemory)) s)
      (expr_exit res)
Proof
  cheat
QED

(* An IfExp whose condition c evaluates to bv, lowered to cond_op between sa
   and s1: the JNZ on cond_op (emitted between s5 and s6) jumps to bl, the
   block bs starts, where the arm e that bv picks runs as ifexp_arm_frag
   says, and a JMP to the exit block xl, which sb starts, ends the arm
   (ifexp_jnz_arm).  Both arms of compile_ifexp_vv_sim are this lemma. *)
Theorem ifexp_branch_sim:
  !ctx func cenv cx ty t c a b e bv es es1 es' res sa sb s0 s1 s5 s6 x6 s7
   bs bm bn bo bx bp tl el xl bl lbl rv cond_op eop.
    expr_type c = BaseT BoolT /\ expr_sim ctx func cenv cx (BaseT BoolT) c es /\
    (!u. stmt_state_rel ctx func cenv cx es1 u ==>
      frag_exec ctx bs bm (\s. s = u)
        (\s. ?v. res = INL v /\
          expr_post ctx func cenv cx e es1 bs bm u es' v eop s)
        (expr_exit res)) /\
    (do result <- eval_expr cx c; read_result cx result od) es = (INL (BoolV bv), es1) /\
    (do result <- eval_expr cx e; read_result cx result od) es1 = (res, es') /\ expr_res_ok res /\ expr_type e = t /\
    lower_value compile_expr cenv (BaseT BoolT) c sa = (cond_op, s1) /\
    emit_inst JNZ [cond_op; Label tl; Label el] [] s5 = ((), s6) /\
    new_block tl s6 = (x6, s7) /\
    emit_inst ASSIGN [eop] [rv] bm = ((), bn) /\
    emit_inst JMP [Label xl] [] bn = ((), bo) /\
    new_block lbl bo = (bx, bp) /\
    (if bv then tl else el) = bl /\ bs.cs_current_bb = bl /\
    bs.cs_current_insts = [] /\
    s5.cs_current_bb = s1.cs_current_bb /\
    s5.cs_current_insts = s1.cs_current_insts /\
    sb.cs_current_bb = xl /\ sb.cs_current_insts = [] /\
    cs_extends sa s1 /\ cs_extends s1 s5 /\ cs_extends s7 bs /\
    cs_extends bs bm /\ cs_extends bp sb /\
    sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= bs.cs_next_var /\
    sa.cs_next_id <= s1.cs_next_id /\ s1.cs_next_id <= bs.cs_next_id /\
    bm.cs_next_id <= sb.cs_next_id /\
    (!x. not_fresh_at sa x ==> x <> rv) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s0 ==>
    frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
      (\s. ?v. res = INL v /\
                vv_post ctx func cenv cx (IfExp t c a b) es sa sb s0 es' (Value v)
                  (if is_word_type t then StackValue t (Var rv)
                   else LocatedValue t (mk_ptr (Var rv) LocMemory)) s)
      (expr_exit res)
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

Theorem readable_eval_frag_transport[local]:
  eval_expr cx e es = (raw,es') /\ expr_read_res_ok cx es' raw /\
  (!res. (do result <- eval_expr cx e; read_result cx result od) es = (res,es') /\
         expr_res_ok res ==>
         frag_exec ctx sa sb P
           (\s. ?v. res = INL v /\
                vv_post ctx func cenv cx e es sa sb s0 es' (Value v) vv s)
           (expr_exit res)) ==>
  frag_exec ctx sa sb P
    (\s. ?tv. raw = INL tv /\
         vv_post ctx func cenv cx e es sa sb s0 es' tv vv s)
    (expr_exit raw)
Proof
  cheat
QED

Theorem ifexp_word_forced_arm_sim[local]:
  expr_sim ctx func ce cx ty e es /\ is_word_type (expr_type e) /\
  compile_expr ce ty e sa = (vv,sm) /\
  compile_ifexp_arm ce (expr_type e) (lowered_value_type ce e) vv sm = (op,sb) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (res,es') /\
  expr_res_ok res /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ stmt_state_rel ctx func ce cx es s0 ==>
  frag_exec ctx sa sb (\s. s = s0)
    (\s. ?v. res = INL v /\ expr_post ctx func ce cx e es sa sb s0 es' v op s)
    (expr_exit res)
Proof
  cheat
QED

Theorem compile_ifexp_forced_frag[local]:
  !ctx func cenv cx ty t c a b es.
    expr_type c = BaseT BoolT /\ expr_type a = t /\ expr_type b = t /\
    (~is_word_type t ==>
     !e. (e = a \/ e = b) ==>
         lowered_value_type cenv e = expr_type e \/
         is_bytestring_type (expr_type e) /\
         is_bytestring_type (lowered_value_type cenv e) /\
         arg_type_fits (lowered_value_type cenv e) (expr_type e) \/
         same_memory_layout cenv (lowered_value_type cenv e) (expr_type e)) /\
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
    (!tv es1. (do result <- eval_expr cx c; read_result cx result od) es = (INL tv, es1) ==>
       expr_sim ctx func cenv cx ty a es1 /\
       expr_sim ctx func cenv cx ty b es1 /\
       expr_vv_sim ctx func cenv cx ty a es1 /\
       expr_vv_sim ctx func cenv cx ty b es1 /\
       !e v es2. (e = a \/ e = b) /\
         (do r <- eval_expr cx e; read_result cx r od) es1 = (INL v, es2) ==>
         ?tvt. evaluate_type (get_tenv cx) t = SOME tvt /\ value_has_type tvt v) ==>
    !sa sb vv res es' s0.
      compile_expr cenv ty (IfExp t c a b) sa = (vv, sb) /\
      (do result <- eval_expr cx (IfExp t c a b); read_result cx result od) es = (res, es') /\ expr_res_ok res /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa ==>
      frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
        (\s. ?v. res = INL v /\
                  vv_post ctx func cenv cx (IfExp t c a b) es sa sb s0 es' (Value v) vv s)
        (expr_exit res)
Proof
  cheat
QED



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
    (!tv es1. (do result <- eval_expr cx c; read_result cx result od) es = (INL tv, es1) ==>
       expr_sim ctx func cenv cx ty a es1 /\
       expr_sim ctx func cenv cx ty b es1 /\
       expr_vv_sim ctx func cenv cx ty a es1 /\
       expr_vv_sim ctx func cenv cx ty b es1 /\
       !e v es2. (e = a \/ e = b) /\
         (do r <- eval_expr cx e; read_result cx r od) es1 = (INL v, es2) ==>
         ?tvt. evaluate_type (get_tenv cx) t = SOME tvt /\ value_has_type tvt v) ==>
    !sa sb vv res es' s0.
      compile_expr cenv ty (IfExp t c a b) sa = (vv, sb) /\
      eval_expr cx (IfExp t c a b) es = (res, es') /\ expr_read_res_ok cx es' res /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa ==>
      frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
        (\s. ?tv. res = INL tv /\
                  vv_post ctx func cenv cx (IfExp t c a b) es sa sb s0 es' tv vv s)
        (expr_exit res)
Proof
  cheat
QED

Theorem ifexp_sfields_partial[local]:
  sfields_tenv_consistent sf env ==>
  !nsid args fields.
    FLOOKUP env nsid = SOME (StructArgs args) /\
    FLOOKUP sf (nsid_to_string nsid) = SOME fields ==>
    MAP (\(name,ty,sz). (name,ty)) fields = args
Proof
  cheat
QED

Theorem ifexp_sfields_partial_delete[local]:
  (!nsid args fields.
    FLOOKUP env nsid = SOME (StructArgs args) /\
    FLOOKUP sf (nsid_to_string nsid) = SOME fields ==>
    MAP (\(name,ty,sz). (name,ty)) fields = args) ==>
  !key nsid args fields.
    FLOOKUP (env \\ key) nsid = SOME (StructArgs args) /\
    FLOOKUP (sf \\ nsid_to_string key) (nsid_to_string nsid) = SOME fields ==>
    MAP (\(name,ty,sz). (name,ty)) fields = args
Proof
  cheat
QED

Theorem ifexp_sfields_partial_types[local]:
  (!nsid args fields.
    FLOOKUP env nsid = SOME (StructArgs args) /\
    FLOOKUP sf (nsid_to_string nsid) = SOME fields ==>
    MAP (\(name,ty,sz). (name,ty)) fields = args) /\
  FLOOKUP env nsid = SOME (StructArgs args) /\
  FLOOKUP sf (nsid_to_string nsid) = SOME fields ==>
  MAP (FST o SND) fields = MAP SND args
Proof
  cheat
QED

Theorem ifexp_abi_missing_struct[local]:
  FLOOKUP sf (nsid_to_string nsid) = NONE ==>
  ~is_abi_dynamic sf (StructT nsid) /\
  abi_size_bound sf (StructT nsid) = 0 /\
  abi_static_size sf (StructT nsid) = 0
Proof
  cheat
QED

Theorem ifexp_abi_members_dynamic[local]:
  !tys. EVERY (\ty. is_abi_dynamic sf ty ==> vyper_is_dynamic env ty) tys ==>
  EXISTS (is_abi_dynamic sf) tys ==> vyper_any_dynamic env tys
Proof
  cheat
QED

Theorem ifexp_abi_members_bound[local]:
  !tys. EVERY (\ty.
    (is_abi_dynamic sf ty ==> vyper_is_dynamic env ty) /\
    abi_size_bound sf ty <= vyper_abi_size_bound env ty /\
    (~is_abi_dynamic sf ty ==>
       abi_static_size sf ty <= vyper_abi_size_bound env ty)) tys ==>
  SUM (MAP (\t. (if is_abi_dynamic sf t then 32 else abi_static_size sf t) +
                 (if is_abi_dynamic sf t then abi_size_bound sf t else 0)) tys)
    <= vyper_abi_size_bound_list env tys
Proof
  cheat
QED

Theorem ifexp_abi_static_members_bound[local]:
  !tys. EVERY (\ty.
    (is_abi_dynamic sf ty ==> vyper_is_dynamic env ty) /\
    abi_size_bound sf ty <= vyper_abi_size_bound env ty /\
    (~is_abi_dynamic sf ty ==>
       abi_static_size sf ty <= vyper_abi_size_bound env ty)) tys /\
  ~EXISTS (is_abi_dynamic sf) tys ==>
  SUM (MAP (abi_static_size sf) tys) <= vyper_abi_size_bound_list env tys
Proof
  cheat
QED

Theorem ifexp_abi_bound_induction[local]:
  (!env ty. !tv (sf : (string, (string # type # num) list) fmap).
    evaluate_type env ty = SOME tv /\
    (!nsid args fields.
      FLOOKUP env nsid = SOME (StructArgs args) /\
      FLOOKUP sf (nsid_to_string nsid) = SOME fields ==>
      MAP (\(name,ty,sz). (name,ty)) fields = args) ==>
    (is_abi_dynamic sf ty ==> vyper_is_dynamic env ty) /\
    abi_size_bound sf ty <= vyper_abi_size_bound env ty /\
    (~is_abi_dynamic sf ty ==> abi_static_size sf ty <= vyper_abi_size_bound env ty)) /\
  (!env tys acc. !tvs (sf : (string, (string # type # num) list) fmap).
    evaluate_types env tys acc = SOME tvs /\
    (!nsid args fields.
      FLOOKUP env nsid = SOME (StructArgs args) /\
      FLOOKUP sf (nsid_to_string nsid) = SOME fields ==>
      MAP (\(name,ty,sz). (name,ty)) fields = args) ==>
    EVERY (\ty.
      (is_abi_dynamic sf ty ==> vyper_is_dynamic env ty) /\
      abi_size_bound sf ty <= vyper_abi_size_bound env ty /\
      (~is_abi_dynamic sf ty ==> abi_static_size sf ty <= vyper_abi_size_bound env ty)) tys)
Proof
  cheat
QED


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
  same_memory_layout ce (lowered_value_type ce e) (expr_type e)
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

Theorem compile_ifexp_word_forced_frag[local]:
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
    (!tv es1. (do result <- eval_expr cx c; read_result cx result od) es = (INL tv, es1) ==>
       expr_sim ctx func cenv cx ty a es1 /\
       expr_sim ctx func cenv cx ty b es1) ==>
    !sa sb vv res es' s0.
      compile_expr cenv ty (IfExp t c a b) sa = (vv, sb) /\
      (do result <- eval_expr cx (IfExp t c a b); read_result cx result od) es = (res, es') /\ expr_res_ok res /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa ==>
      frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
        (\s. ?v. res = INL v /\
                  vv_post ctx func cenv cx (IfExp t c a b) es sa sb s0 es' (Value v) vv s)
        (expr_exit res)
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
    (!tv es1. (do result <- eval_expr cx c; read_result cx result od) es = (INL tv, es1) ==>
       expr_sim ctx func cenv cx ty a es1 /\
       expr_sim ctx func cenv cx ty b es1) ==>
    !sa sb vv res es' s0.
      compile_expr cenv ty (IfExp t c a b) sa = (vv, sb) /\
      eval_expr cx (IfExp t c a b) es = (res, es') /\ expr_read_res_ok cx es' res /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa ==>
      frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
        (\s. ?tv. res = INL tv /\
                  vv_post ctx func cenv cx (IfExp t c a b) es sa sb s0 es' tv vv s)
        (expr_exit res)
Proof
  cheat
QED

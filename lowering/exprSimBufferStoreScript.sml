(*
 * Stores into expression buffers (#636)
 *
 * The lowering writes a child's value into its parent's buffer with
 * compile_store_memory: a word store, an MCOPY, or a bytestring store.
 * The code runs, val_in_memory holds at the destination, and only the
 * destination window changes; stmt_state_rel survives when that window is
 * clear of the locals.
 *
 * TOP-LEVEL:
 *   buffer_store_memory_shape — compile_store_memory only appends
 *     instructions
 *   buffer_store_memory_encoding — it runs and leaves the value at the
 *     destination, and other variables and memory alone
 *   buffer_store_state_frame — such a change keeps stmt_state_rel
 *
 * Helpers: buffer_round_*, the MCOPY and bytestring runs
 *   (buffer_copy_*, buffer_mcopy_*, buffer_store_bytestring_* lemmas),
 *   buffer_window_byte.
 *)
Theory exprSimBufferStore
Ancestors
  exprSimProps
  exprSimVVFrame
  exprSimProps
  loweringPosts
  exprSimBuffer exprSimLiteralBuffer words integer_word vfmConstants emitHelperProps
  exprLoweringProps context venomExecSemantics venomState compileEnv
  copyFwdEquiv allocaRemapDefs valueEncodingProofs list rich_list
  exprSimMemoryTransport valueEncodingProps entryDecodeProps entryDecodeStaticProps
  loweringSlice intCallResult valueCopy localPtrsProps fragExec
Libs
  wordsLib


Theorem buffer_round_no_wrap:
  !len. 32 + 32 * word_size len < dimword (:256) ==>
    len + 31 < dimword (:256)
Proof
  cheat
QED

Theorem buffer_round_size:
  !len. 32 + 32 * word_size len < dimword (:256) ==>
    ((((n2w len:bytes32) + 31w) && i2w (- &32)) + 32w =
     n2w (32 + 32 * word_size len))
Proof
  cheat
QED

Theorem buffer_emit_mcopy_run:
  !sa sb dst src sz d w n s.
    emit_void MCOPY [dst; src; sz] sa = ((),sb) /\
    eval_operand dst s = SOME d /\ eval_operand src s = SOME w /\
    eval_operand sz s = SOME n ==>
    run_inst_seq (emitted_insts sa sb) s =
      OK (mcopy (w2n d) (w2n w) (w2n n) s)
Proof
  cheat
QED

Theorem buffer_copy_memory_run:
  !dst src n sa sb s d w.
    compile_copy_memory dst src n sa = ((),sb) /\
    eval_operand dst s = SOME d /\ eval_operand src s = SOME w /\
    n < dimword (:256) ==>
    run_inst_seq (emitted_insts sa sb) s =
      OK (if n = 0 then s else mcopy (w2n d) (w2n w) n s)
Proof
  cheat
QED

Theorem buffer_copy_memory_shape:
  !dst src n sa sb.
    compile_copy_memory dst src n sa = ((),sb) ==>
    same_blocks sa sb /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    sb.cs_next_var = sa.cs_next_var /\
    sb.cs_next_id = sa.cs_next_id + (if n = 0 then 0 else 1)
Proof
  cheat
QED

Theorem buffer_copy_len_shape:
  !src out sa sb.
    compile_bytestring_copy_len src sa = (out,sb) ==>
    same_blocks sa sb /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    sb.cs_next_var = sa.cs_next_var + 4 /\
    sb.cs_next_id = sa.cs_next_id + 4
Proof
  cheat
QED


Theorem buffer_copy_len_run:
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

Theorem buffer_store_bytestring_shape:
  !src dst sa sb.
    compile_store_bytestring src dst sa = ((),sb) ==>
    same_blocks sa sb /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    sb.cs_next_var = sa.cs_next_var + 4 /\
    sb.cs_next_id = sa.cs_next_id + 5
Proof
  cheat
QED

Theorem buffer_store_bytestring_run:
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

Theorem buffer_window_byte:
  !off len mem i. i < len ==>
    EL i (mem_bytes_at off len mem) = mem_byte_at mem (off + i)
Proof
  cheat
QED

Theorem buffer_mcopy_window:
  !dst src n s off k. off + k <= n ==>
    mem_bytes_at (dst + off) k (mcopy dst src n s).vs_memory =
    mem_bytes_at (src + off) k s.vs_memory
Proof
  cheat
QED

Theorem buffer_mcopy_exterior:
  !dst src n s a k. a + k <= dst \/ dst + n <= a ==>
    mem_bytes_at a k (mcopy dst src n s).vs_memory =
    mem_bytes_at a k s.vs_memory
Proof
  cheat
QED

Theorem buffer_mcopy_restore:
  !dst src n s. (mcopy dst src n s with vs_memory := s.vs_memory) = s
Proof
  cheat
QED

Theorem buffer_mcopy_encoding:
  !tv v src dst n s.
    val_in_memory tv v src s.vs_memory /\ val_wf tv v /\
    val_footprint tv v <= n ==>
    val_in_memory tv v dst (mcopy dst src n s).vs_memory
Proof
  cheat
QED

Theorem buffer_bytes_header:
  !cap bs src s.
    val_in_memory (BaseTV (BytesT (Dynamic cap))) (BytesV bs) src s.vs_memory ==>
    mload src s = n2w (LENGTH bs)
Proof
  cheat
QED

Theorem buffer_string_header:
  !cap str src s.
    val_in_memory (BaseTV (StringT cap)) (StringV str) src s.vs_memory ==>
    mload src s = n2w (LENGTH str)
Proof
  cheat
QED

Theorem buffer_store_memory_shape:
  !cenv src dst ty sa sb.
    compile_store_memory cenv src dst ty ty sa = ((),sb) ==>
    same_blocks sa sb /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id
Proof
  cheat
QED

Theorem buffer_copy_memory_encoding:
  !dst src n sa sb s d w tv v.
    compile_copy_memory dst src n sa = ((),sb) /\
    eval_operand dst s = SOME d /\ eval_operand src s = SOME w /\
    n < dimword (:256) /\ val_in_memory tv v (w2n w) s.vs_memory /\
    val_wf tv v /\ val_footprint tv v <= n ==>
    ?q. run_inst_seq (emitted_insts sa sb) s = OK q /\
      val_in_memory tv v (w2n d) q.vs_memory /\
      (q with vs_memory := s.vs_memory) = s /\
      (!a k. a + k <= w2n d \/ w2n d + n <= a ==>
        mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory)
Proof
  cheat
QED

Theorem buffer_store_word_encoding:
  !src dst sa sb s d w tenv ty tv v.
    emit_void MSTORE [dst;src] sa = ((),sb) /\
    eval_operand dst s = SOME d /\ eval_operand src s = SOME w /\
    is_word_type ty /\ evaluate_type tenv ty = SOME tv /\
    value_has_type tv v /\ w = typed_val_to_w256 tv v ==>
    ?q. run_inst_seq (emitted_insts sa sb) s = OK q /\
      val_in_memory tv v (w2n d) q.vs_memory /\
      (q with vs_memory := s.vs_memory) = s /\
      (!a k. a + k <= w2n d \/ w2n d + type_memory_size tv <= a ==>
        mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory)
Proof
  cheat
QED

Theorem buffer_store_bytestring_encoding:
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
      (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s) /\
      (!a k. a + k <= w2n d \/ w2n d + type_memory_size tv <= a ==>
        mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory)
Proof
  cheat
QED

Theorem buffer_typed_bytestring_header:
  !tenv ty tv v p s.
    is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv /\
    value_has_type tv v /\ val_in_memory tv v p s.vs_memory ==>
    ?len. mload p s = n2w len /\
      val_store_size tv v = 32 + 32 * word_size len
Proof
  cheat
QED

Theorem buffer_store_memory_encoding:
  !cenv cx src dst ty sa sb tv v s d.
    compile_store_memory cenv src dst ty ty sa = ((),sb) /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
    val_wf tv v /\ expr_val_rel cx ty v src s /\
    type_memory_bytes cenv ty = type_memory_size tv /\
    type_memory_size tv < dimword (:256) /\ eval_operand dst s = SOME d /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) ==>
    ?q. run_inst_seq (emitted_insts sa sb) s = OK q /\
      val_in_memory tv v (w2n d) q.vs_memory /\
      (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s) /\
      (!a k. a + k <= w2n d \/ w2n d + type_memory_size tv <= a ==>
        mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory)
Proof
  cheat
QED

Theorem buffer_store_memory_capacity:
  !cenv cx src dst ty sa sb tv v s d q.
    compile_store_memory cenv src dst ty ty sa = ((),sb) /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
    val_wf tv v /\ expr_val_rel cx ty v src s /\
    type_memory_bytes cenv ty = type_memory_size tv /\
    type_memory_size tv < dimword (:256) /\ eval_operand dst s = SOME d /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
    run_inst_seq (emitted_insts sa sb) s = OK q ==>
    LENGTH s.vs_memory <= LENGTH q.vs_memory
Proof
  cheat
QED

Theorem buffer_store_state_frame:
  !func cenv cx es sa s q dst n ctx.
    stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
    (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s) /\
    (!a k. a+k <= dst \/ dst+n <= a ==>
      mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory) /\
    (!name b sz. local_region cenv es.scopes s name b sz ==>
      b+sz <= dst \/ dst+n <= b) /\
    LENGTH s.vs_memory <= LENGTH q.vs_memory /\
    (cenv.ce_is_ctor ==> !name tv v off.
      FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) =
        SOME (ImmutableLoc off) /\
      FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
        | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
      regions_disjoint off (type_memory_size tv) dst n) ==>
    stmt_state_rel ctx func cenv cx es q
Proof
  cheat
QED

(* A short copy into a non-live allocation preserves live local and immutable
   memory. The allocation can be larger than the copied prefix. *)
Theorem stmt_state_rel_mcopy_alloca:
  !func cenv cx es s inst p dst src sz alloc_sz ctx.
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
    not_local_ptr cenv es.scopes p /\ sz <= alloc_sz /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (dst, alloc_sz) ==>
    stmt_state_rel ctx func cenv cx es (mcopy dst src sz s)
Proof
  cheat
QED

Theorem mcopy_alloca_framed_frag:
  !ctx func cenv cx es sa sb s inst p dw sw src sz alloc_sz tv v.
    emit_void MCOPY [Var p; src; Lit (n2w sz)] sa = ((), sb) /\
    lookup_var p s = SOME dw /\ eval_operand src s = SOME sw /\
    sz < dimword (:256) /\ sz <= alloc_sz /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
    not_local_ptr cenv es.scopes p /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n dw, alloc_sz) /\
    val_in_memory tv v (w2n sw) s.vs_memory /\ val_wf tv v /\
    val_footprint tv v <= sz ==>
    frag_exec ctx sa sb (\t. t = s)
      (\t. stmt_state_rel ctx func cenv cx es t /\
           val_in_memory tv v (w2n dw) t.vs_memory /\
           (!q. lookup_var q t = lookup_var q s) /\
           t.vs_allocas = s.vs_allocas /\
           LENGTH s.vs_memory <= LENGTH t.vs_memory /\
           (!a k. a + k <= w2n dw \/ w2n dw + sz <= a ==>
                mem_bytes_at a k t.vs_memory = mem_bytes_at a k s.vs_memory)) (\r. F)
Proof
  cheat
QED

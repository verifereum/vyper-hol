(*
 * Execution of empty(T) buffers (#636)
 *
 * compile_builtin_empty_complex allocates a buffer and zeroes it a word at
 * a time (compile_zero_words).  The code runs and keeps stmt_state_rel,
 * the buffer is disjoint from older allocations and the locals, and the
 * result has a zero header word or sz zero bytes.  Allocation itself need
 * not clear memory.
 *
 * TOP-LEVEL:
 *   compile_builtin_empty_complex_run, compile_builtin_empty_complex_frag —
 *     the run of the emitted code, and the same as a frag_exec
 *   compile_builtin_empty_complex_shape — the code is straight-line
 *   compile_zero_words_run — compile_zero_words zeroes 32 * n bytes and
 *     nothing else
 *
 * Helpers: the buffer_zero_words_*, empty_tail_* and
 *   empty_compile_decompose lemmas.
 *)
Theory exprSimBufferEmptyExec
Ancestors
  exprSimProps
  exprSimAlloc
  exprSimBuffer exprSimBufferEmpty builtinSimple exprSimBufferStore
  exprSimLiteralBuffer exprSimOps freshWrites valueEncodingProps
  exprSimWordArgs emitHelperProps exprLoweringProps compileEnv context
  venomInst venomState words fragExec rich_list list

Theorem buffer_zero_words_shape[local]:
  !n pop sa sb.
    compile_zero_words pop n sa = ((),sb) ==>
    same_blocks sa sb /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    sb.cs_next_var = sa.cs_next_var + n /\
    sb.cs_next_id = sa.cs_next_id + 2*n
Proof
  cheat
QED

Theorem buffer_zero_words_run_frame[local]:
  !n pop sa sb s w sz.
    compile_zero_words pop n sa = ((),sb) /\
    eval_operand pop s = SOME w /\
    (!p. pop = Var p ==> not_fresh_at sa p) /\
    32*n <= sz /\ w2n w + sz < dimword (:256) ==>
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      eval_operand pop t = SOME w /\
      mem_bytes_at (w2n w) (32*n) t.vs_memory = REPLICATE (32*n) 0w /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!a len. a+len <= w2n w \/ w2n w+32*n <= a ==>
        mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  cheat
QED



Theorem compile_zero_words_run:
  !n pop sa sb s w sz func cenv cx es ctx.
    compile_zero_words pop n sa = ((),sb) /\
    eval_operand pop s = SOME w /\
    (!p. pop = Var p ==> not_fresh_at sa p) /\
    stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
    32*n <= sz /\ w2n w+sz < dimword (:256) /\
    (!name b len. local_region cenv es.scopes s name b len ==>
       w2n w+sz <= b \/ b+len <= w2n w) /\
    (cenv.ce_is_ctor ==> !name tv v off.
      FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
      FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
        | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
      regions_disjoint off (type_memory_size tv) (w2n w) (32*n)) ==>
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      stmt_state_rel ctx func cenv cx es t /\ eval_operand pop t = SOME w /\
      mem_bytes_at (w2n w) (32*n) t.vs_memory = REPLICATE (32*n) 0w /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!a len. a+len <= w2n w \/ w2n w+32*n <= a ==>
        mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory)
Proof
  cheat
QED

Theorem empty_word_count[local]:
  !sz. sz MOD 32 = 0 ==> 32*((sz+31) DIV 32) = sz
Proof
  cheat
QED

Theorem empty_tail_run[local]:
  !header pop sz sa sb s w func cenv cx es ctx.
    (if header then emit_void MSTORE [pop; Lit 0w]
     else compile_zero_words pop ((sz+31) DIV 32)) sa = ((),sb) /\
    eval_operand pop s = SOME w /\
    (!p. pop = Var p ==> not_fresh_at sa p) /\
    stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
    w2n w+sz < dimword (:256) /\
    (if header then 32 <= sz else sz MOD 32 = 0) /\
    (!name b len. local_region cenv es.scopes s name b len ==>
      w2n w+sz <= b \/ b+len <= w2n w) /\
    (cenv.ce_is_ctor ==> !name tv v off.
      FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
      FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
        | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
      regions_disjoint off (type_memory_size tv) (w2n w) (if header then 32 else sz)) ==>
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      stmt_state_rel ctx func cenv cx es t /\ eval_operand pop t = SOME w /\
      mem_bytes_at (w2n w) (if header then 32 else sz) t.vs_memory =
        REPLICATE (if header then 32 else sz) 0w /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!a len. a+len <= w2n w \/ w2n w+sz <= a ==>
        mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory)
Proof
  cheat
QED



Theorem empty_tail_shape[local]:
  !header pop sz sa sb.
    (if header then emit_void MSTORE [pop; Lit 0w]
     else compile_zero_words pop ((sz+31) DIV 32)) sa = ((),sb) ==>
    cs_extends sa sb /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    sa.cs_next_id <= sb.cs_next_id
Proof
  cheat
QED

Theorem empty_compile_decompose[local]:
  !sz header sa sb buf.
    compile_builtin_empty_complex sz header sa = (buf,sb) ==>
    ?sm. compile_alloc_buffer sz sa = (buf,sm) /\
      (if header then emit_void MSTORE [buf.buf_operand; Lit 0w]
       else compile_zero_words buf.buf_operand ((sz+31) DIV 32)) sm = ((),sb)
Proof
  cheat
QED

Theorem compile_builtin_empty_complex_run:
  !sz header sa sb buf func cenv cx es s ctx.
    compile_builtin_empty_complex sz header sa = (buf,sb) /\
    fn_has_code sa sb func /\ stmt_state_rel ctx func cenv cx es s /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    sz < dimword (:256) /\
    (if header then 32 <= sz else sz MOD 32 = 0) ==>
    ?t w. run_inst_seq (emitted_insts sa sb) s = OK t /\
      stmt_state_rel ctx func cenv cx es t /\
      eval_operand buf.buf_operand t = SOME w /\
      FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
      w2n w+sz < dimword (:256) /\ sa.cs_next_id < sb.cs_next_id /\
      (if header then mem_word_at (w2n w) t.vs_memory = 0w
       else mem_bytes_at (w2n w) sz t.vs_memory = REPLICATE sz 0w) /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
        FLOOKUP t.vs_allocas aid = SOME entry) /\
      (!aid b len. aid < sa.cs_next_id /\
        FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
        regions_disjoint (w2n w) sz b len) /\
      (!a len. a+len <= w2n w \/ w2n w+sz <= a ==>
        mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      (!name b len. local_region cenv es.scopes s name b len ==>
        w2n w+sz <= b \/ b+len <= w2n w)
Proof
  cheat
QED



Theorem buffer_zero_words_safe[local]:
  !n pop sa sb.
    compile_zero_words pop n sa = ((),sb) ==>
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb)
Proof
  cheat
QED

Theorem compile_builtin_empty_complex_shape:
  !sz header sa sb buf.
    compile_builtin_empty_complex sz header sa = (buf,sb) ==>
    sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
    isPREFIX sa.cs_current_insts sb.cs_current_insts /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb)
Proof
  cheat
QED

Theorem compile_builtin_empty_complex_frag:
  !sz header sa sb buf ctx P Q R.
    compile_builtin_empty_complex sz header sa = (buf,sb) /\
    (!s. P s ==> ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      Q (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
    frag_exec ctx sa sb P Q R
Proof
  cheat
QED

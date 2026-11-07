(*
 * Copying a value held in memory (#638)
 *
 * val_in_memory lays a value out relative to its address, so the bytes of
 * its footprint, copied anywhere, hold the value there.  The internal call
 * copies values this way: the caller stages a memory-passed argument in a
 * buffer of its own, and the callee copies a memory return into the
 * caller's buffer.
 *
 * TOP-LEVEL:
 *   val_in_memory_drop     — val_in_memory at k + off of mem is
 *                            val_in_memory at off of DROP k mem
 *   val_in_memory_relocate — a value's footprint bytes (val_footprint,
 *                            exprSim), copied to another address, hold the
 *                            value there
 *   mcopy_val_in_memory    — MCOPY of at least the footprint does that
 *   mem_bytes_at_mcopy_disjoint — and leaves the bytes outside its
 *                            destination alone
 *   compile_store_memory_run_size_bound — compile_store_memory at one type puts the
 *                            value at the destination and changes memory
 *                            only there
 *   stage_store_run        — and so does compile_stage_intcall_args's
 *                            store of a memory-passed argument
 *)

Theory valueCopy
Ancestors
  exprSimProps
  list rich_list arithmetic
  valueEncoding valueEncodingProps valueEncodingProofs  valueCopyBytes
  compileEnv context exprLoweringProps emitHelper emitHelperProps
  vyperValue vyperTyping vfmConstants immutableMemoryFrame
  venomInst venomState venomExecSemantics venomMemProps
Libs
  blastLib

Theorem mem_word_at_drop[local]:
  !k off mem. mem_word_at (k + off) mem = mem_word_at off (DROP k mem)
Proof
  cheat
QED

Theorem mem_bytes_at_drop[local]:
  !k off len mem.
    mem_bytes_at (k + off) len mem = mem_bytes_at off len (DROP k mem)
Proof
  cheat
QED

val drop_rws = [val_in_memory_def, LET_THM, GSYM mem_word_at_drop,
                GSYM mem_bytes_at_drop, AC ADD_ASSOC ADD_COMM];

Theorem val_in_memory_drop:
  (!ty v off mem k.
     val_in_memory ty v (k + off) mem <=>
     val_in_memory ty v off (DROP k mem)) /\
  (!fields field_tvs off mem k.
     fields_in_memory fields field_tvs (k + off) mem <=>
     fields_in_memory fields field_tvs off (DROP k mem)) /\
  (!vs off tv mem k.
     elems_in_memory vs (k + off) tv mem <=>
     elems_in_memory vs off tv (DROP k mem)) /\
  (!(kvs : (num # value) list) off tv mem k.
     kvs_in_memory kvs (k + off) tv mem <=>
     kvs_in_memory kvs off tv (DROP k mem)) /\
  (!vs tvs off mem k.
     tuple_in_memory vs tvs (k + off) mem <=>
     tuple_in_memory vs tvs off (DROP k mem))
Proof
  cheat
QED

(* The footprint bytes of a value, wherever they are copied, hold it. *)
Theorem val_in_memory_relocate:
  !tv v a b len mem mem'.
    val_in_memory tv v a mem /\ val_wf tv v /\ val_footprint tv v <= len /\
    mem_bytes_at b len mem' = mem_bytes_at a len mem ==>
    val_in_memory tv v b mem'
Proof
  cheat
QED

Theorem mcopy_val_in_memory:
  !tv v dst src n s.
    val_in_memory tv v src s.vs_memory /\ val_wf tv v /\
    val_footprint tv v <= n ==>
    val_in_memory tv v dst (mcopy dst src n s).vs_memory
Proof
  cheat
QED

Theorem mem_bytes_at_write_disjoint:
  !a len d bytes s.
    a + len <= d \/ d + LENGTH bytes <= a ==>
    mem_bytes_at a len (write_memory_with_expansion d bytes s).vs_memory =
    mem_bytes_at a len s.vs_memory
Proof
  cheat
QED

Theorem mem_bytes_at_mcopy_disjoint:
  !a len dst src n s.
    a + len <= dst \/ dst + n <= a ==>
    mem_bytes_at a len (mcopy dst src n s).vs_memory =
    mem_bytes_at a len s.vs_memory
Proof
  cheat
QED


(* ===== Storing a value into memory ===== *)

Theorem eval_operand_update_not_fresh[local]:
  !op sa n w s.
    (!x. op = Var x ==> not_fresh_at sa x) /\ sa.cs_next_var <= n ==>
    eval_operand op (update_var (STRING #"%" (toString n)) w s) =
    eval_operand op s
Proof
  cheat
QED

(* The copy length compile_bytestring_copy_len computes from the length
   word: the length word and the data rounded up to whole words. *)
Theorem bytestring_copy_len_word_exact:
  !L. 32 + 32 * word_size L < dimword (:256) ==>
      w2n (((n2w L + 31w) && i2w (-32)) + 32w : bytes32) =
      32 + 32 * word_size L
Proof
  cheat
QED

Theorem bytestring_copy_len_word[local]:
  !L. L + 64 < dimword (:256) ==>
      w2n (((n2w L + 31w) && i2w (-32)) + 32w : bytes32) =
      32 + 32 * word_size L
Proof
  cheat
QED

(* The steps of the copy, as rewrites: the operands' values are THE of
   their evaluation, so simp can chain them. *)
Theorem step_MLOAD_some[local]:
  !op1 id out ss.
    IS_SOME (eval_operand op1 ss) ==>
    step_inst_base (mk_inst id MLOAD [op1] [out]) ss =
      OK (update_var out (mload (w2n (THE (eval_operand op1 ss))) ss) ss)
Proof
  cheat
QED

Theorem step_ADD_some[local]:
  !op1 op2 id out ss.
    IS_SOME (eval_operand op1 ss) /\ IS_SOME (eval_operand op2 ss) ==>
    step_inst_base (mk_inst id ADD [op1; op2] [out]) ss =
      OK (update_var out
            (THE (eval_operand op1 ss) + THE (eval_operand op2 ss)) ss)
Proof
  cheat
QED

Theorem step_AND_some[local]:
  !op1 op2 id out ss.
    IS_SOME (eval_operand op1 ss) /\ IS_SOME (eval_operand op2 ss) ==>
    step_inst_base (mk_inst id AND [op1; op2] [out]) ss =
      OK (update_var out
            (word_and (THE (eval_operand op1 ss)) (THE (eval_operand op2 ss)))
            ss)
Proof
  cheat
QED

Theorem step_MCOPY_some[local]:
  !d a n id s.
    IS_SOME (eval_operand d s) /\ IS_SOME (eval_operand a s) /\
    IS_SOME (eval_operand n s) ==>
    step_inst_base (mk_inst id MCOPY [d; a; n] []) s =
      OK (mcopy (w2n (THE (eval_operand d s))) (w2n (THE (eval_operand a s)))
            (w2n (THE (eval_operand n s))) s)
Proof
  cheat
QED

Theorem store_bytestring_run_exact:
  !val_op dst_op sa sb s src dst L.
    compile_store_bytestring val_op dst_op sa = ((),sb) /\
    (!x. val_op = Var x ==> not_fresh_at sa x) /\
    (!x. dst_op = Var x ==> not_fresh_at sa x) /\
    eval_operand val_op s = SOME src /\ eval_operand dst_op s = SOME dst /\
    mem_word_at (w2n src) s.vs_memory = n2w L /\
    32 + 32 * word_size L < dimword (:256) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      t.vs_memory =
        (mcopy (w2n dst) (w2n src) (32 + 32 * word_size L) s).vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  cheat
QED

Theorem store_bytestring_run:
  !val_op dst_op sa sb s src dst L.
    compile_store_bytestring val_op dst_op sa = ((),sb) /\
    (!x. val_op = Var x ==> not_fresh_at sa x) /\
    (!x. dst_op = Var x ==> not_fresh_at sa x) /\
    eval_operand val_op s = SOME src /\ eval_operand dst_op s = SOME dst /\
    mem_word_at (w2n src) s.vs_memory = n2w L /\ L + 64 < dimword (:256) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      t.vs_memory =
        (mcopy (w2n dst) (w2n src) (32 + 32 * word_size L) s).vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  cheat
QED

Theorem emit_mstore_run:
  !sa sb dst src s d w.
    emit_void MSTORE [dst; src] sa = ((),sb) /\
    eval_operand dst s = SOME d /\ eval_operand src s = SOME w ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\
    run_inst_seq (emitted_insts sa sb) s = OK (mstore (w2n d) w s)
Proof
  cheat
QED

Theorem emit_mcopy_run:
  !sa sb dst src n s d a.
    emit_void MCOPY [dst; src; Lit (n2w n)] sa = ((),sb) /\
    eval_operand dst s = SOME d /\ eval_operand src s = SOME a /\
    n < dimword (:256) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\
    run_inst_seq (emitted_insts sa sb) s = OK (mcopy (w2n d) (w2n a) n s)
Proof
  cheat
QED

(* compile_store_memory at one type ty: a word type's value, held by src
   as its typed word, or any other type's value, held in memory at src,
   ends up in memory at dst, and memory changes only in the
   type_memory_size bytes from dst.  type_memory_bytes, the size the
   lowering copies, is the compile environment's account of that size
   (build_compile_env_type_memory_bytes). *)
Theorem compile_store_memory_run_size_bound_capacity[local]:
  !cenv src dst ty sa sb s tenv tv v sw dw.
    compile_store_memory cenv src dst ty ty sa = ((),sb) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
    evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
    type_memory_bytes cenv ty = type_memory_size tv /\
    (if is_word_type ty then sw = typed_val_to_w256 tv v
     else val_in_memory tv v (w2n sw) s.vs_memory) /\
    type_memory_size tv + 64 < dimword (:256) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      val_in_memory tv v (w2n dw) t.vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!a len. a + len <= w2n dw \/ w2n dw + type_memory_size tv <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  cheat
QED




Theorem compile_store_memory_run_size_bound_with_capacity:
  !cenv src dst ty sa sb s tenv tv v sw dw.
    compile_store_memory cenv src dst ty ty sa = ((),sb) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
    evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
    type_memory_bytes cenv ty = type_memory_size tv /\
    (if is_word_type ty then sw = typed_val_to_w256 tv v
     else val_in_memory tv v (w2n sw) s.vs_memory) /\
    type_memory_size tv + 64 < dimword (:256) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      val_in_memory tv v (w2n dw) t.vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!a len. a + len <= w2n dw \/ w2n dw + type_memory_size tv <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  cheat
QED

Theorem compile_store_memory_run_frame_with_capacity:
  !cenv src dst ty sa sb s tenv tv v sw dw bound.
    compile_store_memory cenv src dst ty ty sa = ((),sb) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
    evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
    type_memory_bytes cenv ty = type_memory_size tv /\
    (if is_word_type ty then sw = typed_val_to_w256 tv v
     else val_in_memory tv v (w2n sw) s.vs_memory) /\
    type_memory_size tv + 64 < dimword (:256) /\
    (if is_bytestring_type ty then val_store_size tv v <= bound
     else type_memory_size tv <= bound) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      val_in_memory tv v (w2n dw) t.vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!a len. a + len <= w2n dw \/ w2n dw + bound <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  cheat
QED




Theorem compile_store_memory_run_frame:
  !cenv src dst ty sa sb s tenv tv v sw dw bound.
    compile_store_memory cenv src dst ty ty sa = ((),sb) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
    evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
    type_memory_bytes cenv ty = type_memory_size tv /\
    (if is_word_type ty then sw = typed_val_to_w256 tv v
     else val_in_memory tv v (w2n sw) s.vs_memory) /\
    type_memory_size tv + 64 < dimword (:256) /\
    (if is_bytestring_type ty then val_store_size tv v <= bound
     else type_memory_size tv <= bound) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      val_in_memory tv v (w2n dw) t.vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!a len. a + len <= w2n dw \/ w2n dw + bound <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory)
Proof
  cheat
QED

Theorem compile_store_memory_run_size_bound:
  !cenv src dst ty sa sb s tenv tv v sw dw.
    compile_store_memory cenv src dst ty ty sa = ((),sb) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
    evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
    type_memory_bytes cenv ty = type_memory_size tv /\
    (if is_word_type ty then sw = typed_val_to_w256 tv v
     else val_in_memory tv v (w2n sw) s.vs_memory) /\
    type_memory_size tv + 64 < dimword (:256) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      val_in_memory tv v (w2n dw) t.vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!a len. a + len <= w2n dw \/ w2n dw + type_memory_size tv <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory)
Proof
  cheat
QED

Theorem compile_store_memory_run_capacity:
  !cenv src dst ty sa sb s tenv tv v sw dw.
    compile_store_memory cenv src dst ty ty sa = ((),sb) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
    evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
    type_memory_bytes cenv ty = type_memory_size tv /\
    (if is_word_type ty then sw = typed_val_to_w256 tv v
     else val_in_memory tv v (w2n sw) s.vs_memory) /\
    w2n dw + type_memory_size tv + 64 < dimword (:256) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      val_in_memory tv v (w2n dw) t.vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!a len. a + len <= w2n dw \/ w2n dw + type_memory_size tv <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  cheat
QED
Theorem compile_store_memory_run:
  !cenv src dst ty sa sb s tenv tv v sw dw.
    compile_store_memory cenv src dst ty ty sa = ((),sb) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
    evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
    type_memory_bytes cenv ty = type_memory_size tv /\
    (if is_word_type ty then sw = typed_val_to_w256 tv v
     else val_in_memory tv v (w2n sw) s.vs_memory) /\
    w2n dw + type_memory_size tv + 64 < dimword (:256) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      val_in_memory tv v (w2n dw) t.vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!a len. a + len <= w2n dw \/ w2n dw + type_memory_size tv <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory)
Proof
  cheat
QED

(* The store compile_stage_intcall_args emits for a memory-passed argument
   into its buffer dst: compile_store_memory at one type, except that it
   copies with MCOPY whatever type_memory_bytes is. *)
Theorem stage_store_run:
  !cenv src dst ty sa sb s tenv tv v sw dw.
    (if is_word_type ty then emit_void MSTORE [dst; src]
     else if is_bytestring_type ty then
       do compile_store_bytestring src dst; return () od
     else emit_void MCOPY [dst; src; Lit (n2w (type_memory_bytes cenv ty))])
      sa = ((),sb) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
    evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
    type_memory_bytes cenv ty = type_memory_size tv /\
    (if is_word_type ty then sw = typed_val_to_w256 tv v
     else val_in_memory tv v (w2n sw) s.vs_memory) /\
    w2n dw + type_memory_size tv + 64 < dimword (:256) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      val_in_memory tv v (w2n dw) t.vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!a len. a + len <= w2n dw \/ w2n dw + type_memory_size tv <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory)
Proof
  cheat
QED

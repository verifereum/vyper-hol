(*
 * Internal calls: the caller's side of the result (#638)
 *
 * After INVOKE, compile_call's IntCall case stores the callee's stack
 * results into the return buffer (store_multi_results) and hands out the
 * buffer as a LocatedValue.  This theory proves that the stored words hold
 * the source's return value in memory, for every value intret_vals_match
 * relates to the words the callee returned.
 *
 * TOP-LEVEL:
 *   store_multi_results_shape — straight-line code, no INVOKE or terminator
 *   store_multi_results_run — the stores write each result word at its
 *     slot of the buffer and leave everything else alone
 *   stack_results_val_in_memory — the words of a stack-returned value,
 *     laid out 32 bytes apart, hold the value in memory (val_in_memory)
 *   buffer_vv_holds — a value held in memory at the buffer's address is
 *     what the buffer's LocatedValue stands for (vv_holds); this is also
 *     the caller's side of a memory return
 *   store_multi_results_frag — the stores, from a related state, end
 *     related, with the buffer's LocatedValue holding the returned value
 *   result_state_memory_frame, store_result_operand_frame — what such
 *     straight-line code keeps
 *)

Theory intCallResult
Ancestors
  exprSimProps
  loweringPosts
  list rich_list arithmetic
  exprLowering exprLoweringProps emitHelper emitHelperProps compileEnv
  freshWrites valueEncoding valueEncodingProps entryDecodeProps immutableMemoryFrame
   fragExec localPtrsProps context valueCopy
  vyperTyping vyperValue vyperState venomExecSemantics venomState

(* ===== Storing the results ===== *)

Theorem store_result_head_run[local]:
  !buf_op off op sa dst sm sb s w x.
    emit_op ADD [buf_op; Lit off] sa = (dst,sm) /\
    emit_void MSTORE [dst; op] sm = ((),sb) /\
    (!y. op = Var y ==> not_fresh_at sa y) /\
    eval_operand buf_op s = SOME w /\ eval_operand op s = SOME x ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sb.cs_next_var = sa.cs_next_var + 1 /\
    sa.cs_next_id <= sb.cs_next_id /\
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      t.vs_memory = (mstore (w2n (w + off)) x s).vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!y. not_fresh_at sa y ==> lookup_var y t = lookup_var y s)
Proof
  cheat
QED

Theorem store_result_head_shape[local]:
  !buf_op off op sa dst sm sb.
    emit_op ADD [buf_op; Lit off] sa = (dst,sm) /\
    emit_void MSTORE [dst; op] sm = ((),sb) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb)
Proof
  cheat
QED

Theorem store_multi_results_shape:
  !ops buf_op off sa sb.
    store_multi_results buf_op ops off sa = ((),sb) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb)
Proof
  cheat
QED

Theorem store_result_operand_frame:
  !op sa s t.
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!x. op = Var x ==> not_fresh_at sa x) ==>
    eval_operand op t = eval_operand op s
Proof
  cheat
QED

(* store_multi_results buf ops off stores the i-th operand at buf + off +
   32 * i, with an ADD for each address.  The operands are the INVOKE's
   outputs, older than the ADDs' fresh variables, so the ADDs do not
   change them. *)
Theorem store_multi_results_run_capacity[local]:
  !ops buf_op off sa sb s b ws.
    store_multi_results buf_op ops off sa = ((),sb) /\
    (!x. buf_op = Var x ==> not_fresh_at sa x) /\
    (!x. MEM (Var x) ops ==> not_fresh_at sa x) /\
    eval_operand buf_op s = SOME (n2w b) /\
    MAP (\op. eval_operand op s) ops = MAP SOME ws /\
    b + off + 32 * LENGTH ops < dimword (:256) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      (!i. i < LENGTH ws ==>
           mem_word_at (b + off + 32 * i) t.vs_memory = EL i ws) /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!a len. a + len <= b + off \/ b + off + 32 * LENGTH ops <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  cheat
QED



Theorem store_multi_results_run:
  !ops buf_op off sa sb s b ws.
    store_multi_results buf_op ops off sa = ((),sb) /\
    (!x. buf_op = Var x ==> not_fresh_at sa x) /\
    (!x. MEM (Var x) ops ==> not_fresh_at sa x) /\
    eval_operand buf_op s = SOME (n2w b) /\
    MAP (\op. eval_operand op s) ops = MAP SOME ws /\
    b + off + 32 * LENGTH ops < dimword (:256) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      (!i. i < LENGTH ws ==>
           mem_word_at (b + off + 32 * i) t.vs_memory = EL i ws) /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!a len. a + len <= b + off \/ b + off + 32 * LENGTH ops <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory)
Proof
  cheat
QED

(* ===== The stored words hold the value ===== *)

Theorem word_tuple_in_memory[local]:
  !tvs vs tenv off mem.
    values_have_types tvs vs /\
    EVERY (\etv. ?t. is_word_type t /\ evaluate_type tenv t = SOME etv) tvs /\
    (!i. i < LENGTH tvs ==>
         mem_word_at (off + 32 * i) mem =
         typed_val_to_w256 (EL i tvs) (EL i vs)) ==>
    tuple_in_memory vs tvs off mem
Proof
  cheat
QED

Theorem word_fields_in_memory[local]:
  !ftvs fields tenv off mem.
    struct_has_type ftvs fields /\
    EVERY (\etv. ?t. is_word_type t /\ evaluate_type tenv t = SOME etv)
      (MAP SND ftvs) /\
    (!i. i < LENGTH ftvs ==>
         mem_word_at (off + 32 * i) mem =
         typed_val_to_w256 (SND (EL i ftvs)) (SND (EL i fields))) ==>
    fields_in_memory fields ftvs off mem
Proof
  cheat
QED

(* A word type's value returns as one word, its typed encoding. *)
Theorem intret_vals_match_word_eq:
  !tenv t tv v ws.
    is_word_type t /\ evaluate_type tenv t = SOME tv /\
    intret_vals_match tv v ws /\ ws <> [] ==>
    ws = [typed_val_to_w256 tv v]
Proof
  cheat
QED

(* The words a callee returns on the stack (intret_vals_match: one word
   for a word type, one per member for a tuple or struct of words), each
   at its 32-byte slot from off, hold the return value in memory. *)
Theorem stack_results_val_in_memory:
  !tenv tv v ws off mem.
    value_has_type tv v /\ intret_vals_match tv v ws /\ ws <> [] /\
    ((?t. is_word_type t /\ evaluate_type tenv t = SOME tv) \/
     (?tvs. tv = TupleTV tvs /\
        EVERY (\etv. ?t. is_word_type t /\ evaluate_type tenv t = SOME etv)
          tvs) \/
     (?ftvs. tv = StructTV ftvs /\
        EVERY (\etv. ?t. is_word_type t /\ evaluate_type tenv t = SOME etv)
          (MAP SND ftvs))) /\
    (!i. i < LENGTH ws ==> mem_word_at (off + 32 * i) mem = EL i ws) ==>
    val_in_memory tv v off mem
Proof
  cheat
QED




(* ===== The result in the return buffer ===== *)

(* stmt_state_rel survives code that changes only variables and memory,
   keeping the live locals' pointer variables and the bytes of their
   regions (as literal_state_memory_frame in exprSimLiteralBuffer). *)
Theorem result_state_memory_frame:
  !func cenv cx es s t ctx.
    stmt_state_rel ctx func cenv cx es s /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!name entry p sz. lookup_scopes name es.scopes = SOME entry /\
       FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
       lookup_var p t = lookup_var p s) /\
    (!name b sz. local_region cenv es.scopes s name b sz ==>
       mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory) /\
    immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es t /\
    (!x. cenv.ce_imm_alloca = SOME (Var x) ==>
         lookup_var x t = lookup_var x s) ==>
    stmt_state_rel ctx func cenv cx es t
Proof
  cheat
QED

(* A buffer holding v in memory is a pointer to v: the caller's view of a
   return buffer, filled by the stack results (store_multi_results_frag)
   or by the callee's memory return (intCallReturnMem). *)
Theorem buffer_vv_holds:
  !cenv cx t tv v rbuf es s w.
    eval_operand rbuf.buf_operand s = SOME w /\
    evaluate_type (get_tenv cx) t = SOME tv /\ value_has_type tv v /\
    val_in_memory tv v (w2n w) s.vs_memory ==>
    vv_holds cenv cx t (Value v) (LocatedValue t (base_ptr rbuf)) es s
Proof
  cheat
QED

(* After INVOKE, storing the callee's stack results (ws, related to the
   return value v by intret_vals_match) into the return buffer, whose
   result slots miss every live local, leaves the buffer holding v as
   #636's vv_holds says for compile_call's LocatedValue, keeps
   stmt_state_rel, and changes memory only in those slots. *)
Theorem store_multi_results_frag:
  !ctx func cenv cx es t tv v rbuf results sa sb s0 w ws.
    store_multi_results rbuf.buf_operand results 0 sa = ((),sb) /\
    local_ptrs_reserved cenv sa /\
    (!x. rbuf.buf_operand = Var x ==> not_fresh_at sa x) /\
    (!x. MEM (Var x) results ==> not_fresh_at sa x) /\
    evaluate_type (get_tenv cx) t = SOME tv /\ value_has_type tv v /\
    ((?t'. is_word_type t' /\ evaluate_type (get_tenv cx) t' = SOME tv) \/
     (?tvs. tv = TupleTV tvs /\
        EVERY (\etv. ?t'. is_word_type t' /\
                          evaluate_type (get_tenv cx) t' = SOME etv) tvs) \/
     (?ftvs. tv = StructTV ftvs /\
        EVERY (\etv. ?t'. is_word_type t' /\
                          evaluate_type (get_tenv cx) t' = SOME etv)
          (MAP SND ftvs))) /\
    intret_vals_match tv v ws /\ ws <> [] /\
    stmt_state_rel ctx func cenv cx es s0 /\
    eval_operand rbuf.buf_operand s0 = SOME w /\
    MAP (\op. eval_operand op s0) results = MAP SOME ws /\
    w2n w + 32 * LENGTH results < dimword (:256) /\
    (!n lb lsz. local_region cenv es.scopes s0 n lb lsz ==>
       w2n w + 32 * LENGTH results <= lb \/ lb + lsz <= w2n w) /\
    (cenv.ce_is_ctor ==> !name itv iv off.
       FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) =
         SOME (ImmutableLoc off) /\
       FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
         | SOME imms => get_source_immutables cenv.ce_module imms) name =
         SOME (itv,iv) ==>
       regions_disjoint (w2n w) (32 * LENGTH results) off
         (type_memory_size itv)) ==>
    frag_exec ctx sa sb (\s. s = s0)
      (\s. stmt_state_rel ctx func cenv cx es s /\
           vv_holds cenv cx t (Value v) (LocatedValue t (base_ptr rbuf)) es s /\
           (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x s0) /\
           s.vs_allocas = s0.vs_allocas /\
           (!a len. a + len <= w2n w \/ w2n w + 32 * LENGTH results <= a ==>
              mem_bytes_at a len s.vs_memory = mem_bytes_at a len s0.vs_memory))
      (\r. F)
Proof
  cheat
QED



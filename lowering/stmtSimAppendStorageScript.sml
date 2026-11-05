(* Source and machine boundaries for word storage/transient Append. *)
Theory stmtSimAppendStorage
Ancestors
  bodyAppendStorageFacts stmtSimAssignStorage vyperState vyperStorage
  vyperStorageBackend vyperValue valueEncoding valueEncodingProofs
  vyperTyping words exprLowering compileEnv emitHelper emitHelperProps
  exprLoweringProps venomExecSemantics venomInst venomState stateFrame

Theorem append_storage_full:
  cap <= w2n (lookup_storage slot (get_storage cx es tr)) ==>
  append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v es =
    (INR (Error (RuntimeError "append full storage array")), es)
Proof
  cheat
QED

Theorem append_storage_writes:
  w2n (lookup_storage slot (get_storage cx es tr)) < cap ==>
  append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v es =
  (ignore_bind
    (write_storage_slot cx tr
      (slot + n2w (1 + w2n (lookup_storage slot (get_storage cx es tr)) *
                       type_slot_size tv)) tv v)
    (write_storage_slot cx tr slot (BaseTV (UintT 256))
      (IntV &(w2n (lookup_storage slot (get_storage cx es tr)) + 1)))) es
Proof
  cheat
QED

Theorem append_storage_word_success:
  ~cx.txn.is_static /\
  len = w2n (lookup_storage slot (get_storage cx es tr)) /\
  len < cap /\ type_slot_size tv = 1 /\
  encode_value tv v = SOME [(0,w)] ==>
  append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v es =
  (INL (),
   set_storage cx
     (set_storage cx es tr
       (update_storage (slot + n2w (1 + len)) w (get_storage cx es tr))) tr
     (update_storage slot (n2w (len + 1))
       (update_storage (slot + n2w (1 + len)) w (get_storage cx es tr))))
Proof
  cheat
QED

(* All non-register state is unchanged by the guard and address arithmetic. *)
Theorem append_storage_step_frame[local]:
  MEM i.inst_opcode [SLOAD; TLOAD; LT; ADD; MUL; ASSERT] /\
  step_inst_base i s = OK t ==> state_frame t = state_frame s
Proof
  cheat
QED

Theorem append_storage_seq_frame:
  EVERY (\i. MEM i.inst_opcode [SLOAD; TLOAD; LT; ADD; MUL; ASSERT]) code /\
  run_inst_seq code s = OK t ==> state_frame t = state_frame s
Proof
  cheat
QED

Theorem append_storage_store_frame:
  state_frame s = state_frame t ==>
  state_frame (if tr then tstore p w s else sstore p w s) =
  state_frame (if tr then tstore p w t else sstore p w t)
Proof
  cheat
QED

Theorem append_storage_check_run:
  emit_op (if tr then TLOAD else SLOAD) [bop] st0 = (lop,st1) /\
  emit_op LT [lop; Lit (n2w cap)] st1 = (valid,st2) /\
  eval_operand bop ss = SOME slot /\ fresh_vars_wrt st0 ss /\
  cap < dimword (:256) ==>
  ?ss'. run_inst_seq (emitted_insts st0 st2) ss = OK ss' /\
    eval_operand valid ss' =
      SOME (bool_to_word (w2n (if tr then tload slot ss else sload slot ss) < cap)) /\
    eval_operand lop ss' = SOME (if tr then tload slot ss else sload slot ss) /\
    same_blocks st0 st2 /\ fresh_vars_wrt st2 ss' /\
    state_frame ss' = state_frame ss /\
    (!op w. eval_operand op ss = SOME w ==> eval_operand op ss' = SOME w)
Proof
  cheat
QED

Theorem append_storage_guard_run:
  emit_op (if tr then TLOAD else SLOAD) [bop] st0 = (lop,st1) /\
  emit_op LT [lop; Lit (n2w cap)] st1 = (valid,st2) /\
  emit_void ASSERT [valid] st2 = ((),st3) /\
  eval_operand bop ss = SOME slot /\ fresh_vars_wrt st0 ss /\
  cap < dimword (:256) ==>
  ?ss'.
    state_frame ss' = state_frame ss /\
    eval_operand lop ss' = SOME (if tr then tload slot ss else sload slot ss) /\
    (!op w. eval_operand op ss = SOME w ==> eval_operand op ss' = SOME w) /\
    (if w2n (if tr then tload slot ss else sload slot ss) < cap then
       run_inst_seq (emitted_insts st0 st3) ss = OK ss' /\
       same_blocks st0 st3 /\ fresh_vars_wrt st3 ss'
     else
       run_inst_seq (emitted_insts st0 st3) ss =
         Abort Revert_abort (revert_state (set_returndata [] ss')))
Proof
  cheat
QED

(* No allocation or copy-loop code is emitted in the primitive branch. *)
Theorem compile_dynarray_append_word_parts:
  compile_dynarray_append cenv bop vop 1 1 dt st cap T
    load_opc store_opc s0 = ((),s9) <=>
  ?lop valid dop off pop nop s1 s2 s3 s4 s5 s6 s7 s8.
    emit_op load_opc [bop] s0 = (lop,s1) /\
    emit_op LT [lop; Lit (n2w cap)] s1 = (valid,s2) /\
    emit_void ASSERT [valid] s2 = ((),s3) /\
    emit_op ADD [bop; Lit 1w] s3 = (dop,s4) /\
    emit_op MUL [lop; Lit 1w] s4 = (off,s5) /\
    emit_op ADD [dop; off] s5 = (pop,s6) /\
    emit_void store_opc [pop; vop] s6 = ((),s7) /\
    emit_op ADD [lop; Lit 1w] s7 = (nop,s8) /\
    emit_void store_opc [bop; nop] s8 = ((),s9)
Proof
  cheat
QED

Theorem append_storage_store_run:
  emit_void (if tr then TSTORE else SSTORE) [aop; vop] st = ((),st') /\
  eval_operand aop ss = SOME addr /\ eval_operand vop ss = SOME w /\
  fresh_vars_wrt st ss /\ ~ss.vs_call_ctx.cc_static ==>
  run_inst_seq (emitted_insts st st') ss =
    OK (if tr then tstore addr w ss else sstore addr w ss) /\
  same_blocks st st' /\
  fresh_vars_wrt st' (if tr then tstore addr w ss else sstore addr w ss) /\
  (!op x. eval_operand op ss = SOME x ==>
    eval_operand op (if tr then tstore addr w ss else sstore addr w ss) = SOME x)
Proof
  cheat
QED

Theorem append_storage_address_run:
  emit_op ADD [bop; Lit 1w] st3 = (dop,st4) /\
  emit_op MUL [lop; Lit 1w] st4 = (off,st5) /\
  emit_op ADD [dop; off] st5 = (pop,st6) /\
  eval_operand bop ss = SOME slot /\ eval_operand lop ss = SOME len /\
  fresh_vars_wrt st3 ss ==>
  ?t. run_inst_seq (emitted_insts st3 st6) ss = OK t /\
    eval_operand pop t = SOME (slot + 1w + len) /\
    same_blocks st3 st6 /\ fresh_vars_wrt st6 t /\
    state_frame t = state_frame ss /\
    (!op w. eval_operand op ss = SOME w ==> eval_operand op t = SOME w)
Proof
  cheat
QED

Theorem append_storage_suffix_run:
  emit_op ADD [bop; Lit 1w] st3 = (dop,st4) /\
  emit_op MUL [lop; Lit 1w] st4 = (off,st5) /\
  emit_op ADD [dop; off] st5 = (pop,st6) /\
  emit_void (if tr then TSTORE else SSTORE) [pop; vop] st6 = ((),st7) /\
  emit_op ADD [lop; Lit 1w] st7 = (nop,st8) /\
  emit_void (if tr then TSTORE else SSTORE) [bop; nop] st8 = ((),st9) /\
  eval_operand bop ss = SOME slot /\ eval_operand lop ss = SOME len /\
  eval_operand vop ss = SOME w /\ fresh_vars_wrt st3 ss /\
  ~ss.vs_call_ctx.cc_static ==>
  ?t. run_inst_seq (emitted_insts st3 st9) ss = OK t /\
    same_blocks st3 st9 /\ fresh_vars_wrt st9 t /\
    (!op x. eval_operand op ss = SOME x ==> eval_operand op t = SOME x) /\
    state_frame t = state_frame
      (if tr then tstore slot (len+1w) (tstore (slot+1w+len) w ss)
       else sstore slot (len+1w) (sstore (slot+1w+len) w ss))
Proof
  cheat
QED

Theorem compile_dynarray_append_word_run:
  compile_dynarray_append cenv bop vop 1 1 dt st cap T
    (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) s0 = ((),s9) /\
  eval_operand bop ss = SOME slot /\ eval_operand vop ss = SOME w /\
  fresh_vars_wrt s0 ss /\ cap < dimword (:256) /\
  len = w2n (if tr then tload slot ss else sload slot ss) /\ len < cap /\
  ~ss.vs_call_ctx.cc_static ==>
  ?t. run_inst_seq (emitted_insts s0 s9) ss = OK t /\
    same_blocks s0 s9 /\ fresh_vars_wrt s9 t /\
    (!op x. eval_operand op ss = SOME x ==> eval_operand op t = SOME x) /\
    state_frame t = state_frame
      (if tr then tstore slot (n2w len+1w) (tstore (slot+1w+n2w len) w ss)
       else sstore slot (n2w len+1w) (sstore (slot+1w+n2w len) w ss))
Proof
  cheat
QED

Theorem compile_dynarray_append_word_abort:
  compile_dynarray_append cenv bop vop 1 1 dt st cap T
    (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) s0 = ((),s9) /\
  eval_operand bop ss = SOME slot /\ fresh_vars_wrt s0 ss /\
  cap < dimword (:256) /\
  cap <= w2n (if tr then tload slot ss else sload slot ss) ==>
  ?g. state_frame g = state_frame ss /\
    (!op x. eval_operand op ss = SOME x ==> eval_operand op g = SOME x) /\
    run_inst_seq (emitted_insts s0 s9) ss =
      Abort Revert_abort (revert_state (set_returndata [] g))
Proof
  cheat
QED

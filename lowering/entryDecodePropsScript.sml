(*
 * Entry argument decoding: word arguments (#639)
 *
 * TOP-LEVEL:
 *   calldata_encodes_word_arg — calldata that encodes a call holds, at a
 *     word argument's head offset, typed_val_to_w256 of the argument
 *   word_arg_clamp_ok — that word passes the argument's ABI clamp
 *   compile_decode_word_arg_frag — the is_prim path of compile_decode_args
 *     (CALLDATALOAD, clamp, MSTORE) as a fragment: it stores the loaded word
 *     when the clamp accepts it and reverts otherwise
 *   compile_decode_word_arg_correct — for a well-typed source value at the
 *     argument's offset, the decode reaches its end with the value in
 *     memory at the destination (val_in_memory)
 *
 * Helpers: abi_clamp_ok, abi_head_size, enc_tuple_heads,
 *   enc_tuple_static_head, val_in_memory_word, vyper_to_abi_word_enc,
 *   bind_arguments_word_arg, abi_head_size_word_prefix,
 *   abi_embedded_static_size_word, vyper_to_abi_types_EL; and the decode
 *   lemmas (compile_abi_clamp_structure, decode_emit_update_frame,
 *   decode_clamp_frame, ...), which
 *   abiDecodeStaticProps and entryDecodeStaticProps reuse
 *
 * The decoder's head offset (compile_register_positional_args adds
 * abi_embedded_static_size for each argument) agrees with the ABI's
 * (abi_head_size) when the earlier arguments are words
 * (abi_head_size_word_prefix, abi_embedded_static_size_word).  For
 * earlier static or dynamic arguments of other types, the agreement needs
 * the compile env's struct metadata to match the type environment; that
 * belongs to the static/dynamic decoding items.
 *)
Theory entryDecodeProps
Ancestors
  arithmetic list rich_list words integer integer_word
  valueEncodingProofs valueEncodingProps loweringHalt exprSimConvert
  moduleLoweringProps abiEncoderProps entryDispatchProps
  moduleLowering abiEncoder compileEnv compileVyper exprLowering
  exprSimProps valueEncoding selectorDispatch fragExec emitHelper emitHelperProps
  venomExecSemantics venomState venomInst venomMemProps
  vyperABI vyperABIRoundtrip vyperTyping vyperValue vyperValueOperation
  vyperInterpreter exprSimArith contractABI byte vfmTypes vyperCall
Libs
  wordsLib intLib dep_rewrite

(* ===== What the clamp accepts ===== *)

(* The words compile_abi_clamp_basetype lets through, stated with the
   operations its code runs (SHR, SIGNEXTEND, SHL on literal shifts). *)
Definition abi_clamp_ok_def:
  abi_clamp_ok NoClamp (w : bytes32) = T /\
  abi_clamp_ok (IntClamp bits is_signed) w =
    (if is_signed then sign_extend (n2w (bits DIV 8 - 1)) w = w
     else word_lsr w (w2n (n2w bits : bytes32)) = 0w) /\
  abi_clamp_ok (BytesMClamp m) w =
    (word_lsl w (w2n (n2w (m * 8) : bytes32)) = 0w) /\
  abi_clamp_ok BoolClamp w = (word_lsr w 1 = 0w)
End

(* ===== Head offsets in a tuple encoding ===== *)

(* Bytes an element takes in the head of a tuple encoding: an offset word
   for a dynamic element, its encoding for a static one. *)
Definition abi_head_size_def:
  abi_head_size t v = if is_dynamic t then 32n else LENGTH (enc t v)
End

(* The heads of a tuple encoding come first, in order. *)
Theorem enc_tuple_heads:
  !ts vs hl tl rhds rtls.
    LENGTH ts = LENGTH vs ==>
    ?hs rest.
      enc_tuple hl tl ts vs rhds rtls = FLAT (REVERSE rhds) ++ FLAT hs ++ rest /\
      LENGTH hs = LENGTH ts /\
      !j. j < LENGTH ts ==>
          LENGTH (EL j hs) = abi_head_size (EL j ts) (EL j vs) /\
          (~is_dynamic (EL j ts) ==> EL j hs = enc (EL j ts) (EL j vs))
Proof
  cheat
QED

(* A static element's encoding sits at its head offset. *)
Theorem enc_tuple_static_head:
  !ts vs i.
    LENGTH ts = LENGTH vs /\ i < LENGTH ts /\ ~is_dynamic (EL i ts) ==>
    TAKE (LENGTH (enc (EL i ts) (EL i vs)))
      (DROP (SUM (MAP2 abi_head_size (TAKE i ts) (TAKE i vs)))
         (enc (Tuple ts) (ListV vs))) =
    enc (EL i ts) (EL i vs)
Proof
  cheat
QED

(* ===== Word values ===== *)

(* A word-typed value is in memory exactly when its word is. *)
(* A word-typed value's ABI encoding is its word. *)
Theorem vyper_to_abi_word_enc:
  !tenv ty tv v av.
    is_word_type ty /\ evaluate_type tenv ty = SOME tv /\
    value_has_type tv v /\ vyper_to_abi tenv ty v = SOME av ==>
    ~is_dynamic (vyper_to_abi_type tenv ty) /\
    enc (vyper_to_abi_type tenv ty) av = word_to_bytes (typed_val_to_w256 tv v) T
Proof
  cheat
QED

(* ===== The calldata word ===== *)

Theorem vyper_to_abi_types_EL:
  !tys i. i < LENGTH tys ==>
    LENGTH (vyper_to_abi_types tenv tys) = LENGTH tys /\
    EL i (vyper_to_abi_types tenv tys) = vyper_to_abi_type tenv (EL i tys)
Proof
  cheat
QED

(* Calldata that encodes a call holds a word argument's word at the
   argument's head offset, after the 4-byte selector. *)
Theorem calldata_encodes_word_arg:
  !tenv fname tys vals cd i tv.
    calldata_encodes tenv fname tys vals cd /\ LENGTH vals = LENGTH tys /\
    i < LENGTH tys /\ is_word_type (EL i tys) /\
    evaluate_type tenv (EL i tys) = SOME tv /\
    value_has_type tv (EL i vals) ==>
    ?avs. vyper_to_abi_list tenv tys vals = SOME avs /\
          mem_word_at
            (4 + SUM (MAP2 abi_head_size
                        (TAKE i (vyper_to_abi_types tenv tys)) (TAKE i avs)))
            cd =
          typed_val_to_w256 tv (EL i vals)
Proof
  cheat
QED

(* bind_arguments succeeding types each argument. *)
Theorem bind_arguments_word_arg:
  !tenv args vals env i.
    bind_arguments tenv args vals = SOME env /\ i < LENGTH args ==>
    LENGTH vals = LENGTH args /\
    ?tv. evaluate_type tenv (SND (EL i args)) = SOME tv /\
         value_has_type tv (EL i vals)
Proof
  cheat
QED

(* With only word arguments before i, the head offset is 32 bytes per
   argument, as the decoder steps through them. *)
Theorem abi_head_size_word_prefix:
  !tenv tys vals avs i.
    vyper_to_abi_list tenv tys vals = SOME avs /\ i <= LENGTH tys /\
    (!j. j < i ==> is_word_type (EL j tys) /\
                   ?tv. evaluate_type tenv (EL j tys) = SOME tv /\
                        value_has_type tv (EL j vals)) ==>
    SUM (MAP2 abi_head_size (TAKE i (vyper_to_abi_types tenv tys))
                            (TAKE i avs)) = 32 * i
Proof
  cheat
QED

Theorem abi_embedded_static_size_word:
  !sfields ty. is_word_type ty ==> abi_embedded_static_size sfields ty = 32
Proof
  cheat
QED

(* ===== The clamp accepts the word ===== *)

val dimindex_256 = fcpLib.INDEX_CONV ``dimindex(:256)``;

Theorem lsr_zero_of_lt[local]:
  !(w : 'a word) n. w2n w < 2 ** n ==> w >>> n = 0w
Proof
  cheat
QED

Theorem n2w_lsr_clamp_ok[local]:
  !m k. m <= 256 /\ k < 2 ** m ==>
        (n2w k : bytes32) >>> w2n (n2w m : bytes32) = 0w
Proof
  cheat
QED

Theorem signed_int_mod_within[local]:
  !m i. 0 < m /\ within_int_bound (Signed m) i ==> signed_int_mod m i = i
Proof
  cheat
QED

Theorem int_clamp_signed_ok[local]:
  !m i. 8 <= m /\ m < 256 /\ m MOD 8 = 0 /\ within_int_bound (Signed m) i ==>
        sign_extend (n2w (m DIV 8 - 1)) (i2w i : bytes32) = i2w i
Proof
  cheat
QED

Theorem address_clamp_ok[local]:
  !bs. LENGTH bs = 20 ==>
       (word_of_bytes_be (PAD_LEFT 0w 32 bs) : bytes32) >>>
         w2n (n2w 160 : bytes32) = 0w
Proof
  cheat
QED

Theorem bytesM_clamp_ok[local]:
  !bs. LENGTH bs < 32 ==>
       word_lsl (word_of_bytes_be (PAD_RIGHT 0w 32 bs) : bytes32)
                (w2n (n2w (LENGTH bs * 8) : bytes32)) = 0w
Proof
  cheat
QED

(* A well-typed word argument passes the clamp the compiler picks for its
   type.  The signed clamp sign-extends from byte bits DIV 8 - 1, which is
   right because evaluate_type only admits widths that are multiples of 8.
   One hypothesis ties the compiler's view to the source: a flag's member
   count in the compile env is the source's (the same clause exprSimHyps
   uses). *)
Theorem word_arg_clamp_ok:
  !tenv sfields cenv ty tv v.
    is_word_type ty /\ evaluate_type tenv ty = SOME tv /\
    value_has_type tv v /\
    (!nsid m. FLOOKUP tenv nsid = SOME (FlagArgs m) ==>
              cenv.ce_flag_n_members (nsid_to_string nsid) = m) ==>
    abi_clamp_ok
      (case type_to_abi_dec_info sfields cenv ty of
         DecPrimWord c => c
       | _ => NoClamp)
      (typed_val_to_w256 tv v)
Proof
  cheat
QED

(* Inverse primitives use the actual accepted word, not a source encoding. *)
Theorem unsigned_word_clamp_bound[local]:
  !n (w:bytes32).
    n <= 256 /\
    abi_clamp_ok (if n = 256 then NoClamp else IntClamp n F) w ==>
    w2n w < 2 ** n
Proof
  cheat
QED

Theorem unsigned_word_clamp_value[local]:
  !n (w:bytes32).
    n <= 256 /\
    abi_clamp_ok (if n = 256 then NoClamp else IntClamp n F) w ==>
    ?v. value_has_type (BaseTV (UintT n)) v /\
        typed_val_to_w256 (BaseTV (UintT n)) v = w
Proof
  cheat
QED

Theorem flag_word_clamp_value[local]:
  !m (w:bytes32).
    m <= 256 /\
    abi_clamp_ok (if m = 256 then NoClamp else IntClamp m F) w ==>
    ?v. value_has_type (FlagTV m) v /\ typed_val_to_w256 (FlagTV m) v = w
Proof
  cheat
QED

Theorem bool_word_clamp_value[local]:
  !(w:bytes32). abi_clamp_ok BoolClamp w ==>
    ?v. value_has_type (BaseTV BoolT) v /\
        typed_val_to_w256 (BaseTV BoolT) v = w
Proof
  cheat
QED

Theorem signed_int_mod_range[local]:
  !m i. 0 < m ==> within_int_bound (Signed m) (signed_int_mod m i)
Proof
  cheat
QED

Theorem signed_word_clamp_representation[local]:
  !n (w:bytes32).
    8 <= n /\ n <= 256 /\ n MOD 8 = 0 /\
    abi_clamp_ok (if n = 256 then NoClamp else IntClamp n T) w ==>
    (i2w (signed_int_mod n (&(w2n w))) : bytes32) = w
Proof
  cheat
QED

Theorem signed_word_clamp_value[local]:
  !n (w:bytes32).
    8 <= n /\ n <= 256 /\ n MOD 8 = 0 /\
    abi_clamp_ok (if n = 256 then NoClamp else IntClamp n T) w ==>
    ?v. value_has_type (BaseTV (IntT n)) v /\
        typed_val_to_w256 (BaseTV (IntT n)) v = w
Proof
  cheat
QED

Theorem decimal_word_clamp_value[local]:
  !(w:bytes32). abi_clamp_ok (IntClamp 168 T) w ==>
    ?v. value_has_type (BaseTV DecimalT) v /\
        typed_val_to_w256 (BaseTV DecimalT) v = w
Proof
  cheat
QED

Theorem address_word_clamp_value[local]:
  !(w:bytes32). abi_clamp_ok (IntClamp 160 F) w ==>
    ?v. value_has_type (BaseTV AddressT) v /\
        typed_val_to_w256 (BaseTV AddressT) v = w
Proof
  cheat
QED

Theorem fixed_bytes_word_clamp_value[local]:
  !m (w:bytes32).
    m <= 32 /\
    abi_clamp_ok (if m = 32 then NoClamp else BytesMClamp m) w ==>
    ?v. value_has_type (BaseTV (BytesT (Fixed m))) v /\
        typed_val_to_w256 (BaseTV (BytesT (Fixed m))) v = w
Proof
  cheat
QED

(* Every accepted primitive word has a source value with the same encoding. *)
Theorem word_arg_clamp_inverse:
  !tenv sfields cenv ty tv (w:bytes32).
    is_word_type ty /\ evaluate_type tenv ty = SOME tv /\
    (!nsid m. FLOOKUP tenv nsid = SOME (FlagArgs m) ==>
      cenv.ce_flag_n_members (nsid_to_string nsid) = m) /\
    abi_clamp_ok
      (case type_to_abi_dec_info sfields cenv ty of
         DecPrimWord c => c | _ => NoClamp) w ==>
    ?v. value_has_type tv v /\ typed_val_to_w256 tv v = w
Proof
  cheat
QED

(* Selected flags suffice: unrelated environment entries are immaterial. *)
Theorem word_arg_clamp_inverse_selected:
  !tenv sfields cenv ty tv (w:bytes32).
    is_word_type ty /\ evaluate_type tenv ty = SOME tv /\
    (!nsid. ty = FlagT nsid ==>
      ?m. FLOOKUP tenv nsid = SOME (FlagArgs m) /\
          cenv.ce_flag_n_members (nsid_to_string nsid) = m) /\
    abi_clamp_ok
      (case type_to_abi_dec_info sfields cenv ty of
         DecPrimWord c => c | _ => NoClamp) w ==>
    ?v. value_has_type tv v /\ typed_val_to_w256 tv v = w
Proof
  cheat
QED

(* ===== The decode code ===== *)

(* The is_prim path of compile_decode_args for one calldata argument:
   CALLDATALOAD at off, the clamp, MSTORE to the destination.  It either
   finishes with the loaded word stored at the destination, having passed
   the clamp, or reverts because the clamp rejects it. *)
Theorem compile_decode_word_arg_phases[local]:
  !cenv name is_dyn abi_size dec off hi st st' loc dst.
  compile_decode_args cenv [(name, T, is_dyn, abi_size, dec)] off
    CALLDATALOAD hi 4 st = ((), st') /\
  FLOOKUP cenv.ce_vars name = SOME loc /\
  var_location_decode_operand loc = SOME dst ==>
  ?src val_op st1 st2 st3.
    emit_op ADD [Lit 4w; Lit (n2w (off - 4))] st = (src, st1) /\
    emit_op CALLDATALOAD [src] st1 = (val_op, st2) /\
    compile_abi_clamp_basetype val_op
      (case dec of DecPrimWord c => c | _ => NoClamp) st2 = ((), st3) /\
    emit_void MSTORE [dst; val_op] st3 = ((), st')
Proof
  cheat
QED

Theorem compile_abi_clamp_structure:
  !cl op st st'.
  compile_abi_clamp_basetype op cl st = ((), st') ==>
  st'.cs_blocks = st.cs_blocks /\
  st'.cs_current_bb = st.cs_current_bb /\
  inst_extends st st' /\ st.cs_next_var <= st'.cs_next_var /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')
Proof
  cheat
QED

Theorem compile_decode_word_arg_structure[local]:
  !cenv name is_dyn abi_size dec off hi st st' loc dst.
  compile_decode_args cenv [(name, T, is_dyn, abi_size, dec)] off
    CALLDATALOAD hi 4 st = ((), st') /\
  FLOOKUP cenv.ce_vars name = SOME loc /\
  var_location_decode_operand loc = SOME dst ==>
  st'.cs_blocks = st.cs_blocks /\
  st'.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts st'.cs_current_insts /\
  st.cs_next_var <= st'.cs_next_var /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')
Proof
  cheat
QED

Theorem decode_emit_update_frame:
  !opc ops st v st' s w.
  emit_op opc ops st = (v, st') /\ fresh_vars_wrt st s /\
  step_inst_base (mk_inst st.cs_next_id opc ops
    [STRING #"%" (toString st.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString st.cs_next_var)) w s) ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
      eval_operand v t = SOME w /\ fresh_vars_wrt st' t /\
      vars_pc_only s t /\
      (!op a. eval_operand op s = SOME a ==> eval_operand op t = SOME a) /\
      (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s)
Proof
  cheat
QED

Theorem decode_calldataload_frame[local]:
  !op a st v st' s.
  emit_op CALLDATALOAD [op] st = (v, st') /\
  eval_operand op s = SOME a /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
      eval_operand v t = SOME (mem_word_at (w2n a) s.vs_call_ctx.cc_calldata) /\
      fresh_vars_wrt st' t /\ vars_pc_only s t /\
      (!op b. eval_operand op s = SOME b ==> eval_operand op t = SOME b) /\
      (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s)
Proof
  cheat
QED

Theorem decode_mstore_frame:
  !s t a w. vars_pc_only s t ==>
    vars_pc_only (mstore a w s) (mstore a w t)
Proof
  cheat
QED

Theorem decode_emit_mstore_frame:
  !op1 op2 p w st st' s.
  emit_void MSTORE [op1; op2] st = ((), st') /\
  eval_operand op1 s = SOME p /\ eval_operand op2 s = SOME w /\
  fresh_vars_wrt st s ==>
  run_inst_seq (emitted_insts st st') s = OK (mstore (w2n p) w s) /\
  fresh_vars_wrt st' (mstore (w2n p) w s) /\
  (!x. lookup_var x (mstore (w2n p) w s) = lookup_var x s)
Proof
  cheat
QED

Theorem decode_frame_compose:
  !st st1 s t u.
  st.cs_next_var <= st1.cs_next_var /\
  vars_pc_only s t /\ vars_pc_only t u /\
  (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
  (!x. not_fresh_at st1 x ==> lookup_var x u = lookup_var x t) ==>
  vars_pc_only s u /\
  (!x. not_fresh_at st x ==> lookup_var x u = lookup_var x s)
Proof
  cheat
QED

Theorem decode_two_tests_assert[local]:
  !opc ops test tops st a st1 b st2 st' s w z.
  emit_op opc ops st = (a, st1) /\
  emit_op test tops st1 = (b, st2) /\
  emit_void ASSERT [b] st2 = ((), st') /\ fresh_vars_wrt st s /\
  step_inst_base (mk_inst st.cs_next_id opc ops
    [STRING #"%" (toString st.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString st.cs_next_var)) w s) /\
  step_inst_base (mk_inst st1.cs_next_id test tops
    [STRING #"%" (toString st1.cs_next_var)])
    (update_var (STRING #"%" (toString st.cs_next_var)) w s) =
    OK (update_var (STRING #"%" (toString st1.cs_next_var)) z
      (update_var (STRING #"%" (toString st.cs_next_var)) w s)) ==>
  if z <> 0w then
    ?t. run_inst_seq (emitted_insts st st') s = OK t /\
        vars_pc_only s t /\ fresh_vars_wrt st' t /\
        (!op v. eval_operand op s = SOME v ==> eval_operand op t = SOME v) /\
        (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s)
  else ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  cheat
QED

Theorem decode_zero_test_assert[local]:
  !opc ops st a st1 b st2 st' s w.
  emit_op opc ops st = (a, st1) /\
  emit_op ISZERO [a] st1 = (b, st2) /\
  emit_void ASSERT [b] st2 = ((), st') /\ fresh_vars_wrt st s /\
  step_inst_base (mk_inst st.cs_next_id opc ops
    [STRING #"%" (toString st.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString st.cs_next_var)) w s) ==>
  if w = 0w then
    ?t. run_inst_seq (emitted_insts st st') s = OK t /\
        vars_pc_only s t /\ fresh_vars_wrt st' t /\
        (!op v. eval_operand op s = SOME v ==> eval_operand op t = SOME v) /\
        (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s)
  else ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  cheat
QED

Theorem decode_unsigned_clamp[local]:
  !op bits st st' s w.
  compile_abi_int_clamp op bits F st = ((), st') /\
  eval_operand op s = SOME w /\ fresh_vars_wrt st s ==>
  if word_lsr w (w2n (n2w bits : bytes32)) = 0w then
    ?t. run_inst_seq (emitted_insts st st') s = OK t /\
        vars_pc_only s t /\ fresh_vars_wrt st' t /\
        (!op v. eval_operand op s = SOME v ==> eval_operand op t = SOME v) /\
        (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s)
  else ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  cheat
QED

Theorem decode_bytes_clamp[local]:
  !op m st st' s w.
  compile_abi_bytes_clamp op m st = ((), st') /\
  eval_operand op s = SOME w /\ fresh_vars_wrt st s ==>
  if word_lsl w (w2n (n2w (m * 8) : bytes32)) = 0w then
    ?t. run_inst_seq (emitted_insts st st') s = OK t /\
        vars_pc_only s t /\ fresh_vars_wrt st' t /\
        (!op v. eval_operand op s = SOME v ==> eval_operand op t = SOME v) /\
        (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s)
  else ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  cheat
QED

Theorem decode_signed_clamp[local]:
  !op bits st st' s w.
  compile_abi_int_clamp op bits T st = ((), st') /\
  eval_operand op s = SOME w /\ fresh_vars_wrt st s ==>
  if sign_extend (n2w (bits DIV 8 - 1)) w = w then
    ?t. run_inst_seq (emitted_insts st st') s = OK t /\
        vars_pc_only s t /\ fresh_vars_wrt st' t /\
        (!op v. eval_operand op s = SOME v ==> eval_operand op t = SOME v) /\
        (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s)
  else ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  cheat
QED

Theorem decode_clamp_frame:
  !cl op st st' s w.
  compile_abi_clamp_basetype op cl st = ((), st') /\
  eval_operand op s = SOME w /\ fresh_vars_wrt st s ==>
  if abi_clamp_ok cl w then
    ?t. run_inst_seq (emitted_insts st st') s = OK t /\
        vars_pc_only s t /\ fresh_vars_wrt st' t /\
        (!op v. eval_operand op s = SOME v ==> eval_operand op t = SOME v) /\
        (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s)
  else ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  cheat
QED

Theorem decode_load_frame[local]:
  !off st src st1 val_op st2 s.
  emit_op ADD [Lit 4w; Lit (n2w (off - 4))] st = (src, st1) /\
  emit_op CALLDATALOAD [src] st1 = (val_op, st2) /\
  4 <= off /\ off < dimword (:256) /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st2) s = OK t /\
      eval_operand val_op t = SOME (mem_word_at off s.vs_call_ctx.cc_calldata) /\
      vars_pc_only s t /\ fresh_vars_wrt st2 t /\
      (!op v. eval_operand op s = SOME v ==> eval_operand op t = SOME v) /\
      (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s)
Proof
  cheat
QED

Theorem decode_word_arg_run[local]:
  !cenv name is_dyn abi_size dec off hi st st' loc dst s0 p.
    compile_decode_args cenv [(name, T, is_dyn, abi_size, dec)] off
      CALLDATALOAD hi 4 st = ((), st') /\
    FLOOKUP cenv.ce_vars name = SOME loc /\
    var_location_decode_operand loc = SOME dst /\
    4 <= off /\ off < dimword (:256) /\
    eval_operand dst s0 = SOME p /\ fresh_vars_wrt st s0 ==>
    (?t. run_inst_seq (emitted_insts st st') s0 = OK t /\
         vars_pc_only
           (mstore (w2n p) (mem_word_at off s0.vs_call_ctx.cc_calldata) s0) t /\
         fresh_vars_wrt st' t /\
         (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s0) /\
         abi_clamp_ok (case dec of DecPrimWord c => c | _ => NoClamp)
           (mem_word_at off s0.vs_call_ctx.cc_calldata)) \/
    (?t. run_inst_seq (emitted_insts st st') s0 = Abort Revert_abort t /\
         ~abi_clamp_ok (case dec of DecPrimWord c => c | _ => NoClamp)
           (mem_word_at off s0.vs_call_ctx.cc_calldata))
Proof
  cheat
QED

Theorem compile_decode_word_arg_frag:
  !cenv name is_dyn abi_size dec off hi st st' ctx loc dst s0 p.
    compile_decode_args cenv [(name, T, is_dyn, abi_size, dec)] off
      CALLDATALOAD hi 4 st = ((), st') /\
    FLOOKUP cenv.ce_vars name = SOME loc /\
    var_location_decode_operand loc = SOME dst /\
    4 <= off /\ off < dimword (:256) /\
    eval_operand dst s0 = SOME p /\ fresh_vars_wrt st s0 ==>
    frag_exec ctx st st' (\s. s = s0)
      (\t. vars_pc_only
             (mstore (w2n p) (mem_word_at off s0.vs_call_ctx.cc_calldata) s0) t /\
           fresh_vars_wrt st' t /\
           (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s0) /\
           abi_clamp_ok (case dec of DecPrimWord c => c | _ => NoClamp)
             (mem_word_at off s0.vs_call_ctx.cc_calldata))
      (\r. ?t. r = Abort Revert_abort t /\
               ~abi_clamp_ok (case dec of DecPrimWord c => c | _ => NoClamp)
                  (mem_word_at off s0.vs_call_ctx.cc_calldata))
Proof
  cheat
QED

(* A word argument whose source value sits at its offset in the calldata
   decodes without reverting, leaving the value in memory at the
   destination.  calldata_encodes_word_arg gives the calldata premise for
   calldata that encodes the call. *)
Theorem compile_decode_word_arg_correct:
  !cenv cenv0 sfields name is_dyn abi_size off hi st st' ctx loc dst s0 p
   tenv ty tv v.
    compile_decode_args cenv
      [(name, T, is_dyn, abi_size, type_to_abi_dec_info sfields cenv0 ty)] off
      CALLDATALOAD hi 4 st = ((), st') /\
    FLOOKUP cenv.ce_vars name = SOME loc /\
    var_location_decode_operand loc = SOME dst /\
    4 <= off /\ off < dimword (:256) /\
    eval_operand dst s0 = SOME p /\ fresh_vars_wrt st s0 /\
    is_word_type ty /\ evaluate_type tenv ty = SOME tv /\
    value_has_type tv v /\
    (!nsid m. FLOOKUP tenv nsid = SOME (FlagArgs m) ==>
              cenv0.ce_flag_n_members (nsid_to_string nsid) = m) /\
    mem_word_at off s0.vs_call_ctx.cc_calldata = typed_val_to_w256 tv v ==>
    frag_exec ctx st st' (\s. s = s0)
      (\t. vars_pc_only (mstore (w2n p) (typed_val_to_w256 tv v) s0) t /\
           fresh_vars_wrt st' t /\
           (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s0) /\
           val_in_memory tv v (w2n p) t.vs_memory)
      (\r. F)
Proof
  cheat
QED

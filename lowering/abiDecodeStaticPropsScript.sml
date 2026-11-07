(*
 * ABI decoding of static values from calldata (#639)
 *
 * TOP-LEVEL:
 *   compile_abi_decode_static_run — compile_abi_decode_static (load, clamp,
 *     MSTORE) with the clamp compile_abi_clamp_basetype emits: it stores
 *     the loaded word when the clamp accepts it and reverts otherwise
 *   compile_abi_decode_static_correct — a word value's word, loaded and
 *     stored by it, is the value in memory at the destination
 *     (val_in_memory)
 *   compile_abi_decode_static_buf_frag — compile_abi_decode_to_buf from
 *     calldata, for a static decode info (static_dec): it copies the
 *     calldata window to the destination when every clamp accepts its word
 *     (dec_ok) and reverts otherwise
 *
 * Also used by entryDecodeStaticProps: static_dec (the static decode
 *   infos), dec_ok (every clamp accepts), dec_frame (what the decode
 *   changes), dec_run (copy or revert), dec_straight (straight-line
 *   code) and their lemmas, and decode_static_buf_run (the induction
 *   behind compile_abi_decode_static_buf_frag).
 *
 * Helpers: the memory-window lemmas.
 *
 * The decode of a static value from calldata (hi_op = Lit 0w, the bound
 * pinned Vyper omits for calldata) runs straight-line code: a word is
 * loaded, clamped and stored, and a tuple, struct or static array
 * decodes its elements at their head offsets.  For a static value the ABI
 * layout and the memory layout coincide (static_dec: each element's ABI
 * size is its memory size), so the decode copies the calldata window
 * word by word, checking each word against its clamp.
 *)
Theory abiDecodeStaticProps
Ancestors
  exprSimProps arithmetic list rich_list words finite_map
  entryDecodeProps moduleLoweringProps
  abiEncoder compileEnv emitHelper emitHelperProps exprLoweringProps
  valueEncoding valueEncodingProps valueEncodingProofs fragExec
  venomState venomInst
Libs
  wordsLib

(* ===== Straight-line fragments ===== *)

(* Code from st to st' in the current block, with no terminator or call. *)
Definition dec_straight_def:
  dec_straight st st' <=>
    st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
    inst_extends st st' /\ st.cs_next_var <= st'.cs_next_var /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts st st')
End

Theorem dec_straight_trans:
  !st st1 st2.
    dec_straight st st1 /\ dec_straight st1 st2 ==> dec_straight st st2
Proof
  cheat
QED

Theorem dec_straight_emit_op:
  !opc ops st v st'.
    emit_op opc ops st = (v, st') /\ opc <> INVOKE /\ ~is_terminator opc ==>
    dec_straight st st'
Proof
  cheat
QED

Theorem dec_straight_emit_add:
  !ops st v st'. emit_op ADD ops st = (v, st') ==> dec_straight st st'
Proof
  cheat
QED

Theorem dec_straight_emit_void:
  !opc ops st st'.
    emit_void opc ops st = ((), st') /\ opc <> INVOKE /\ ~is_terminator opc ==>
    dec_straight st st'
Proof
  cheat
QED

Theorem dec_straight_clamp:
  !op cl st st'.
    compile_abi_clamp_basetype op cl st = ((), st') ==> dec_straight st st'
Proof
  cheat
QED

(* ===== Static word decode ===== *)

(* compile_abi_decode_static with the basetype clamp: the load gives w (any
   load opcode, as its step says), then the clamp checks w, then w is
   stored at the destination. *)
Theorem compile_abi_decode_static_run:
  !src_op dst_op load_opc cl st st' s p w.
    compile_abi_decode_static src_op dst_op load_opc
      (\val_op. compile_abi_clamp_basetype val_op cl) st = ((), st') /\
    (!id out. step_inst_base (mk_inst id load_opc [src_op] [out]) s =
              OK (update_var out w s)) /\
    eval_operand dst_op s = SOME p /\ fresh_vars_wrt st s ==>
    if abi_clamp_ok cl w then
      ?t. run_inst_seq (emitted_insts st st') s = OK t /\
          vars_pc_only (mstore (w2n p) w s) t /\ fresh_vars_wrt st' t /\
          (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s)
    else ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  cheat
QED

Theorem dec_straight_decode_static:
  !src_op dst_op load_opc cl st st'.
    compile_abi_decode_static src_op dst_op load_opc
      (\val_op. compile_abi_clamp_basetype val_op cl) st = ((), st') /\
    load_opc <> INVOKE /\ ~is_terminator load_opc ==>
    dec_straight st st'
Proof
  cheat
QED

(* A word value's word, loaded by compile_abi_decode_static and checked by
   the clamp type_to_abi_dec_info gives its type, ends as the value in
   memory at the destination.  The load step says which word is loaded:
   CALLDATALOAD at a gives mem_word_at (w2n a) of the calldata
   (step_CALLDATALOAD).  The flag premise is that of
   word_arg_clamp_ok. *)
Theorem compile_abi_decode_static_correct:
  !src_op dst_op load_opc sfields cenv st st' s p tenv ty tv v.
    compile_abi_decode_static src_op dst_op load_opc
      (\val_op. compile_abi_clamp_basetype val_op
         (case type_to_abi_dec_info sfields cenv ty of
            DecPrimWord c => c
          | _ => NoClamp)) st = ((), st') /\
    (!id out. step_inst_base (mk_inst id load_opc [src_op] [out]) s =
              OK (update_var out (typed_val_to_w256 tv v) s)) /\
    eval_operand dst_op s = SOME p /\ fresh_vars_wrt st s /\
    is_word_type ty /\ evaluate_type tenv ty = SOME tv /\
    value_has_type tv v /\
    (!nsid m. FLOOKUP tenv nsid = SOME (FlagArgs m) ==>
              cenv.ce_flag_n_members (nsid_to_string nsid) = m) ==>
    ?t. run_inst_seq (emitted_insts st st') s = OK t /\
        vars_pc_only (mstore (w2n p) (typed_val_to_w256 tv v) s) t /\
        fresh_vars_wrt st' t /\
        (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
        val_in_memory tv v (w2n p) t.vs_memory
Proof
  cheat
QED

(* ===== Static decode infos ===== *)

(* static_dec info n: info decodes a static value of n bytes whose ABI
   layout is its memory layout: a word, or a static tuple (struct, static
   array) whose elements each take as many bytes in the ABI head as in
   memory.  type_to_abi_dec_info builds DecComplex F for those. *)
Inductive static_dec:
[~prim:]
  static_dec (DecPrimWord c) 32
[~complex:]
  static_decs elems n ==> static_dec (DecComplex F elems) n
[~nil:]
  static_decs [] 0
[~cons:]
  static_dec ei m /\ static_decs elems n ==>
  static_decs ((ei, m, m)::elems) (m + n)
End

Theorem static_dec_shape:
  !ei m. static_dec ei m ==>
         (?c. ei = DecPrimWord c) \/ (?elems. ei = DecComplex F elems)
Proof
  cheat
QED

(* dec_ok info cd off: each clamp of info accepts its word of cd, for a
   value encoded at off. *)
Definition dec_ok_def:
  dec_ok (DecPrimWord c) cd off = abi_clamp_ok c (mem_word_at off cd) /\
  dec_ok (DecComplex d elems) cd off = decs_ok elems cd off /\
  dec_ok (DecBytestring _) cd off = F /\
  dec_ok (DecDynArray _ _ _ _ _) cd off = F /\
  decs_ok [] cd off = T /\
  decs_ok ((ei, asz, msz)::elems) cd off =
    (dec_ok ei cd off /\ decs_ok elems cd (off + asz))
Termination
  WF_REL_TAC `measure (\x. case x of
       INL (ei, cd, off) => abi_dec_info_size ei
     | INR (elems, cd, off) =>
         list_size (pair_size abi_dec_info_size
           (pair_size (\x. x) (\(x:num). x))) elems)`
End

(* ===== Frames ===== *)

(* What decoding code from st changes from s to t: the variables past st,
   the pc, and the memory in [q, q + n) only. *)
Definition dec_frame_def:
  dec_frame st q n s t <=>
    vars_pc_only (s with vs_memory := t.vs_memory) t /\
    (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
    (!i. i < q \/ q + n <= i ==>
         mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory)
End

(* Decoding n static bytes from calldata at b to memory at q: when ok
   (every clamp accepts), the window is copied and nothing else changes;
   otherwise a revert. *)
Definition dec_run_def:
  dec_run st st' s q b n ok <=>
    if ok then
      ?t. run_inst_seq (emitted_insts st st') s = OK t /\
          fresh_vars_wrt st' t /\ dec_frame st q n s t /\
          mem_bytes_at q n t.vs_memory =
            mem_bytes_at b n s.vs_call_ctx.cc_calldata
    else ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
End

Theorem dec_frame_call_ctx:
  !st q n s t. dec_frame st q n s t ==> t.vs_call_ctx = s.vs_call_ctx
Proof
  cheat
QED

Theorem dec_frame_eval:
  !st q n s t op w.
    dec_frame st q n s t /\ fresh_vars_wrt st s /\
    eval_operand op s = SOME w ==> eval_operand op t = SOME w
Proof
  cheat
QED

Theorem dec_frame_inst_idx:
  !st q n s t k. dec_frame st q n s t ==>
                 dec_frame st q n s (t with vs_inst_idx := k)
Proof
  cheat
QED

Theorem dec_frame_of_vars:
  !st q n s t.
    vars_pc_only s t /\
    (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) ==>
    dec_frame st q n s t
Proof
  cheat
QED

Theorem dec_frame_trans:
  !st q n s t st1 q1 n1 q2 n2 u.
    dec_frame st q1 n1 s t /\ dec_frame st1 q2 n2 t u /\
    st.cs_next_var <= st1.cs_next_var /\
    q <= q1 /\ q1 + n1 <= q + n /\ q <= q2 /\ q2 + n2 <= q + n ==>
    dec_frame st q n s u
Proof
  cheat
QED

(* ===== Memory windows ===== *)

Theorem mem_bytes_at_bytewise:
  !q n m1 m2.
    (!i. q <= i /\ i < q + n ==> mem_bytes_at i 1 m1 = mem_bytes_at i 1 m2) ==>
    mem_bytes_at q n m1 = mem_bytes_at q n m2
Proof
  cheat
QED

Theorem window_concat:
  !q b m n cd mem1 mem2.
    mem_bytes_at q m mem1 = mem_bytes_at b m cd /\
    mem_bytes_at (q + m) n mem2 = mem_bytes_at (b + m) n cd /\
    (!i. i < q + m ==> mem_bytes_at i 1 mem2 = mem_bytes_at i 1 mem1) ==>
    mem_bytes_at q (m + n) mem2 = mem_bytes_at b (m + n) cd
Proof
  cheat
QED

Theorem mem_bytes_at_mstore_outside:
  !i q w s. i < q \/ q + 32 <= i ==>
    mem_bytes_at i 1 (mstore q w s).vs_memory = mem_bytes_at i 1 s.vs_memory
Proof
  cheat
QED

Theorem w2n_add_n2w_lt:
  !(p : bytes32) k. w2n p + k < dimword (:256) ==> w2n (p + n2w k) = w2n p + k
Proof
  cheat
QED

(* ===== Decoding a static value from calldata ===== *)

Theorem mstore_with_memory:
  !q w s. mstore q w s = s with vs_memory := (mstore q w s).vs_memory
Proof
  cheat
QED

(* A word: compile_abi_decode_static with CALLDATALOAD. *)
Theorem decode_prim_buf_run:
  !dst src c st st' s p a.
    compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (DecPrimWord c) st =
      ((), st') /\
    eval_operand dst s = SOME p /\ eval_operand src s = SOME a /\
    fresh_vars_wrt st s ==>
    dec_straight st st' /\
    dec_run st st' s (w2n p) (w2n a) 32
      (dec_ok (DecPrimWord c) s.vs_call_ctx.cc_calldata (w2n a))
Proof
  cheat
QED

Theorem getelemptr_static_emit:
  !src k opc hi st es st1.
    compile_getelemptr_abi src F k opc hi st = (es, st1) ==>
    emit_op ADD [src; Lit (n2w k)] st = (es, st1)
Proof
  cheat
QED

(* The element pointers of a static element at head offset k. *)
Theorem decode_elem_ptrs:
  !src dst k st es st1 ed st2 s a p.
    compile_getelemptr_abi src F k CALLDATALOAD (Lit 0w) st = (es, st1) /\
    emit_op ADD [dst; Lit (n2w k)] st1 = (ed, st2) /\
    eval_operand src s = SOME a /\ eval_operand dst s = SOME p /\
    fresh_vars_wrt st s ==>
    ?t. run_inst_seq (emitted_insts st st2) s = OK t /\
        eval_operand es t = SOME (a + n2w k) /\
        eval_operand ed t = SOME (p + n2w k) /\
        fresh_vars_wrt st2 t /\ vars_pc_only s t /\
        (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
        (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
        dec_straight st st2
Proof
  cheat
QED

(* The instructions of a static element: its two pointers, its decode,
   then the remaining elements. *)
Theorem decode_elems_cons_phases:
  !ei m elems dst src k st st'.
    compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w)
      ((ei, m, m)::elems) k k st = ((), st') /\
    static_dec ei m ==>
    ?es st1 ed st2 st3.
      compile_getelemptr_abi src F k CALLDATALOAD (Lit 0w) st = (es, st1) /\
      emit_op ADD [dst; Lit (n2w k)] st1 = (ed, st2) /\
      compile_abi_decode_to_buf ed es CALLDATALOAD (Lit 0w) ei st2 =
        ((), st3) /\
      compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w)
        elems (k + m) (k + m) st3 = ((), st')
Proof
  cheat
QED

Theorem static_dec_straight:
  (!info n. static_dec info n ==>
     !dst src st st'.
       compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) info st =
         ((), st') ==> dec_straight st st') /\
  (!elems n. static_decs elems n ==>
     !dst src k st st'.
       compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w)
         elems k k st = ((), st') ==> dec_straight st st')
Proof
  cheat
QED

(* One static element at head offset k: its pointers and its decode. *)
Theorem decode_elem_step:
  !ei m es st1 ed st2 st3 src dst k st s p a.
    static_dec ei m /\
    compile_getelemptr_abi src F k CALLDATALOAD (Lit 0w) st = (es, st1) /\
    emit_op ADD [dst; Lit (n2w k)] st1 = (ed, st2) /\
    compile_abi_decode_to_buf ed es CALLDATALOAD (Lit 0w) ei st2 =
      ((), st3) /\
    (!dst src st st' s p a.
       compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) ei st =
         ((), st') /\
       eval_operand dst s = SOME p /\ eval_operand src s = SOME a /\
       fresh_vars_wrt st s /\
       w2n p + m < dimword (:256) /\ w2n a + m < dimword (:256) ==>
       dec_run st st' s (w2n p) (w2n a) m
         (dec_ok ei s.vs_call_ctx.cc_calldata (w2n a))) /\
    eval_operand dst s = SOME p /\ eval_operand src s = SOME a /\
    fresh_vars_wrt st s /\
    w2n p + k + m < dimword (:256) /\ w2n a + k + m < dimword (:256) ==>
    dec_straight st st3 /\
    dec_run st st3 s (w2n p + k) (w2n a + k) m
      (dec_ok ei s.vs_call_ctx.cc_calldata (w2n a + k))
Proof
  cheat
QED

(* A static element followed by the remaining ones. *)
Theorem decode_elems_cons_run:
  !ei m elems n dst src k st st' s p a.
    static_dec ei m /\ static_decs elems n /\
    compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w)
      ((ei, m, m)::elems) k k st = ((), st') /\
    (!dst src st st' s p a.
       compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) ei st =
         ((), st') /\
       eval_operand dst s = SOME p /\ eval_operand src s = SOME a /\
       fresh_vars_wrt st s /\
       w2n p + m < dimword (:256) /\ w2n a + m < dimword (:256) ==>
       dec_run st st' s (w2n p) (w2n a) m
         (dec_ok ei s.vs_call_ctx.cc_calldata (w2n a))) /\
    (!dst src k st st' s p a.
       compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w)
         elems k k st = ((), st') /\
       eval_operand dst s = SOME p /\ eval_operand src s = SOME a /\
       fresh_vars_wrt st s /\
       w2n p + k + n < dimword (:256) /\ w2n a + k + n < dimword (:256) ==>
       dec_run st st' s (w2n p + k) (w2n a + k) n
         (decs_ok elems s.vs_call_ctx.cc_calldata (w2n a + k))) /\
    eval_operand dst s = SOME p /\ eval_operand src s = SOME a /\
    fresh_vars_wrt st s /\
    w2n p + k + (m + n) < dimword (:256) /\
    w2n a + k + (m + n) < dimword (:256) ==>
    dec_run st st' s (w2n p + k) (w2n a + k) (m + n)
      (decs_ok ((ei, m, m)::elems) s.vs_call_ctx.cc_calldata (w2n a + k))
Proof
  cheat
QED

Theorem decode_static_buf_run:
  (!info n. static_dec info n ==>
     !dst src st st' s p a.
       compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) info st =
         ((), st') /\
       eval_operand dst s = SOME p /\ eval_operand src s = SOME a /\
       fresh_vars_wrt st s /\
       w2n p + n < dimword (:256) /\ w2n a + n < dimword (:256) ==>
       dec_run st st' s (w2n p) (w2n a) n
         (dec_ok info s.vs_call_ctx.cc_calldata (w2n a))) /\
  (!elems n. static_decs elems n ==>
     !dst src k st st' s p a.
       compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w)
         elems k k st = ((), st') /\
       eval_operand dst s = SOME p /\ eval_operand src s = SOME a /\
       fresh_vars_wrt st s /\
       w2n p + k + n < dimword (:256) /\ w2n a + k + n < dimword (:256) ==>
       dec_run st st' s (w2n p + k) (w2n a + k) n
         (decs_ok elems s.vs_call_ctx.cc_calldata (w2n a + k)))
Proof
  cheat
QED

(* A static value decoded from calldata at a to memory at p: the calldata
   window is copied when every clamp accepts its word, and the decode
   reverts otherwise. *)
Theorem compile_abi_decode_static_buf_frag:
  !info n dst src st st' ctx s0 p a.
    static_dec info n /\
    compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) info st =
      ((), st') /\
    eval_operand dst s0 = SOME p /\ eval_operand src s0 = SOME a /\
    fresh_vars_wrt st s0 /\
    w2n p + n < dimword (:256) /\ w2n a + n < dimword (:256) ==>
    frag_exec ctx st st' (\s. s = s0)
      (\t. dec_frame st (w2n p) n s0 t /\ fresh_vars_wrt st' t /\
           mem_bytes_at (w2n p) n t.vs_memory =
             mem_bytes_at (w2n a) n s0.vs_call_ctx.cc_calldata /\
           dec_ok info s0.vs_call_ctx.cc_calldata (w2n a))
      (\r. ?t. r = Abort Revert_abort t /\
               ~dec_ok info s0.vs_call_ctx.cc_calldata (w2n a))
Proof
  cheat
QED

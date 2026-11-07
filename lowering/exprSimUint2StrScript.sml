(*
 * uint2str(x) in the unit context (#636)
 *
 * compile_uint2str stores x's decimal digits right to left into a buffer
 * of 32 + 32 * word_size n bytes, puts the length word just below the
 * leading digit, and returns a pointer to that length word, inside the
 * buffer.
 *
 * TOP-LEVEL:
 *   compile_uint2str_typed_vv_sim — the lowered uint2str simulates the
 *     source builtin at its string type
 *   compile_uint2str_layout — the code compile_uint2str emits, as the
 *     u2s_* block templates
 *)
Theory exprSimUint2Str
Ancestors
  exprBopSimProps
  exprSimDefs exprSimProps exprSimStack loweringPosts
  arithmetic list ASCIInumbers numposrep logroot
  exprSimHyps allocLimits vyperTypeSystem compileEnv
  valueEncodingProps valueEncodingProofs venomExecSemantics byte words
  builtinStrings emitHelper fragExec exprSimLiteralBuffer immutableMemoryFrame
   exprSimWordArgs exprSimOps exprSimHash exprSimCalldataSlice exprSimAlloc
  exprSimHypsDefs gasOutcome gasSummary gasContext fragGasMode fragGasPath
  storageCopyGasPath
Libs
  monadsyntax

Theorem decimal_string_step:
  num_to_dec_string x =
    if x < 10 then [CHR (48 + x MOD 10)]
    else num_to_dec_string (x DIV 10) ++ [CHR (48 + x MOD 10)]
Proof
  cheat
QED

Theorem decimal_string_length_bound:
  x < 10 ** k /\ 0 < k ==> LENGTH (num_to_dec_string x) <= k
Proof
  cheat
QED

Theorem uint256_decimal_length:
  x < 2 ** 256 ==>
  1 <= LENGTH (num_to_dec_string x) /\
  LENGTH (num_to_dec_string x) <= 78
Proof
  cheat
QED

Theorem uint2str_builtin_types:
  well_typed_builtin_app ty (Uint2Str n) ts ==>
  ?k. ts = [BaseT (UintT k)] /\ ty = BaseT (StringT n) /\ 78 <= n
Proof
  cheat
QED

Theorem uint2str_body_capacity:
  expr_body_pre cenv cx env (Builtin (BaseT (StringT m)) (Uint2Str n) args) es ==>
  type_memory_bytes cenv (BaseT (StringT m)) < 2 ** 64
Proof
  cheat
QED

Theorem uint2str_expr_types:
  well_typed_expr env (Builtin ann (Uint2Str n) args) ==>
  ?e k. args = [e] /\ ann = BaseT (StringT n) /\
        expr_type e = BaseT (UintT k) /\ 78 <= n
Proof
  cheat
QED

Theorem mstore_string_header:
  mem_bytes_at (p + 32) (LENGTH str) s.vs_memory = MAP (n2w o ORD) str ==>
  val_in_memory ty (StringV str) p
    (mstore p (n2w (LENGTH str)) s).vs_memory
Proof
  cheat
QED

Theorem uint2str_dimindex_256[local,simp]:
  dimindex (:256) = 256
Proof
  cheat
QED

Theorem mstore_last_byte:
  mem_bytes_at (a + 31) 1 (mstore a (w:bytes32) s).vs_memory = [w2w w]
Proof
  cheat
QED

Theorem mstore_prepend_byte:
  mem_bytes_at (a + 32) (LENGTH bs) s.vs_memory = bs ==>
  mem_bytes_at (a + 31) (SUC (LENGTH bs))
    (mstore a (w:bytes32) s).vs_memory = w2w w :: bs
Proof
  cheat
QED

(* The post-allocation state is the descriptor for the finite compiler tail. *)
Definition u2s_var_def:
  u2s_var a k = FST (fresh_var (a with cs_next_var := a.cs_next_var + k))
End

Definition u2s_label_def:
  u2s_label a k =
    FST (fresh_label
      (EL k ["u2s_check"; "u2s_cond"; "u2s_body";
             "u2s_zero"; "u2s_final"; "u2s_exit"])
      (a with cs_next_label := a.cs_next_label + k))
End

Definition u2s_inst_def:
  u2s_inst a k opc ops outs = mk_inst (a.cs_next_id + k) opc ops outs
End

Definition u2s_setup_def:
  u2s_setup a op buf =
    [u2s_inst a 0 ASSIGN [op] [u2s_var a 0];
     u2s_inst a 1 ASSIGN [Lit 0w] [u2s_var a 1];
     u2s_inst a 2 ASSIGN [buf] [u2s_var a 2];
     u2s_inst a 3 JMP [Label (u2s_label a 0)] []]
End

Definition u2s_check_def:
  u2s_check a =
    [u2s_inst a 4 EQ [Var (u2s_var a 0); Lit 0w] [u2s_var a 3];
     u2s_inst a 5 JNZ
       [Var (u2s_var a 3); Label (u2s_label a 3); Label (u2s_label a 1)] []]
End

Definition u2s_cond_def:
  u2s_cond a =
    [u2s_inst a 6 EQ [Var (u2s_var a 0); Lit 0w] [u2s_var a 4];
     u2s_inst a 7 JNZ
       [Var (u2s_var a 4); Label (u2s_label a 4); Label (u2s_label a 2)] []]
End

Definition u2s_body_def:
  u2s_body a buf n =
    [u2s_inst a 8 Mod [Var (u2s_var a 0); Lit 10w] [u2s_var a 5];
     u2s_inst a 9 ADD [Lit 48w; Var (u2s_var a 5)] [u2s_var a 6];
     u2s_inst a 10 ADD [buf; Lit (n2w n)] [u2s_var a 7];
     u2s_inst a 11 SUB [Var (u2s_var a 7); Var (u2s_var a 1)] [u2s_var a 8];
     u2s_inst a 12 MSTORE [Var (u2s_var a 8); Var (u2s_var a 6)] [];
     u2s_inst a 13 Div [Var (u2s_var a 0); Lit 10w] [u2s_var a 9];
     u2s_inst a 14 ASSIGN [Var (u2s_var a 9)] [u2s_var a 0];
     u2s_inst a 15 ADD [Var (u2s_var a 1); Lit 1w] [u2s_var a 10];
     u2s_inst a 16 ASSIGN [Var (u2s_var a 10)] [u2s_var a 1];
     u2s_inst a 17 JMP [Label (u2s_label a 1)] []]
End

Definition u2s_zero_def:
  u2s_zero a buf n =
    [u2s_inst a 18 ADD [buf; Lit (n2w n)] [u2s_var a 11];
     u2s_inst a 19 MSTORE [Var (u2s_var a 11); Lit 48w] [];
     u2s_inst a 20 ADD [buf; Lit (n2w n)] [u2s_var a 12];
     u2s_inst a 21 SUB [Var (u2s_var a 12); Lit 1w] [u2s_var a 13];
     u2s_inst a 22 MSTORE [Var (u2s_var a 13); Lit 1w] [];
     u2s_inst a 23 ASSIGN [Var (u2s_var a 13)] [u2s_var a 2];
     u2s_inst a 24 JMP [Label (u2s_label a 5)] []]
End

Definition u2s_final_def:
  u2s_final a buf n =
    [u2s_inst a 25 ADD [buf; Lit (n2w n)] [u2s_var a 14];
     u2s_inst a 26 SUB [Var (u2s_var a 14); Var (u2s_var a 1)] [u2s_var a 15];
     u2s_inst a 27 MSTORE [Var (u2s_var a 15); Var (u2s_var a 1)] [];
     u2s_inst a 28 ASSIGN [Var (u2s_var a 15)] [u2s_var a 2];
     u2s_inst a 29 JMP [Label (u2s_label a 5)] []]
End

Definition u2s_blocks_def:
  u2s_blocks a op buf n =
    [<|bb_label := u2s_label a 4; bb_instructions := u2s_final a buf n|>;
     <|bb_label := u2s_label a 3; bb_instructions := u2s_zero a buf n|>;
     <|bb_label := u2s_label a 2; bb_instructions := u2s_body a buf n|>;
     <|bb_label := u2s_label a 1; bb_instructions := u2s_cond a|>;
     <|bb_label := u2s_label a 0; bb_instructions := u2s_check a|>;
     <|bb_label := a.cs_current_bb;
       bb_instructions := a.cs_current_insts ++ u2s_setup a op buf|>]
End

Definition u2s_end_def:
  u2s_end a op buf n = a with
    <|cs_blocks := u2s_blocks a op buf n ++ a.cs_blocks;
      cs_current_bb := u2s_label a 5; cs_current_insts := [];
      cs_next_var := a.cs_next_var + 16;
      cs_next_id := a.cs_next_id + 30;
      cs_next_label := a.cs_next_label + 6|>
End

Definition u2s_layout_def:
  u2s_layout a op buf n sb <=> sb = u2s_end a op buf n
End

Theorem u2s_template_lengths[simp]:
  LENGTH (u2s_setup a op buf) = 4 /\ LENGTH (u2s_check a) = 2 /\
  LENGTH (u2s_cond a) = 2 /\ LENGTH (u2s_body a buf n) = 10 /\
  LENGTH (u2s_zero a buf n) = 7 /\ LENGTH (u2s_final a buf n) = 5
Proof
  cheat
QED

Theorem u2s_var_injective[simp]:
  u2s_var a j = u2s_var a k <=> j = k
Proof
  cheat
QED

Theorem u2s_var_fresh:
  not_fresh_at a z ==> z <> u2s_var a k
Proof
  cheat
QED

Theorem u2s_setup_cont[local]:
  (do v <- fresh_var;
      emit_inst ASSIGN [op] [v];
      i <- fresh_var;
      emit_inst ASSIGN [Lit 0w] [i];
      r <- fresh_var;
      emit_inst ASSIGN [buf] [r];
      check <- fresh_label "u2s_check";
      cond <- fresh_label "u2s_cond";
      body <- fresh_label "u2s_body";
      zero <- fresh_label "u2s_zero";
      final <- fresh_label "u2s_final";
      exit <- fresh_label "u2s_exit";
      emit_inst JMP [Label check] [];
      kont v i r check cond body zero final exit
   od) a =
  kont (u2s_var a 0) (u2s_var a 1) (u2s_var a 2)
       (u2s_label a 0) (u2s_label a 1) (u2s_label a 2)
       (u2s_label a 3) (u2s_label a 4) (u2s_label a 5)
       (a with <|cs_next_var := a.cs_next_var + 3;
                 cs_next_id := a.cs_next_id + 4;
                 cs_next_label := a.cs_next_label + 6;
                 cs_current_insts := a.cs_current_insts ++ u2s_setup a op buf|>)
Proof
  cheat
QED

Theorem u2s_check_cont[local]:
  s.cs_next_var = a.cs_next_var + 3 /\
  s.cs_next_id = a.cs_next_id + 4 ==>
  (do z <- emit_op EQ [Var (u2s_var a 0); Lit 0w];
      emit_inst JNZ [z; Label (u2s_label a 3); Label (u2s_label a 1)] [];
      kont () od) s =
  kont () (s with <|cs_next_var := a.cs_next_var + 4;
                    cs_next_id := a.cs_next_id + 6;
                    cs_current_insts := s.cs_current_insts ++ u2s_check a|>)
Proof
  cheat
QED

Theorem u2s_cond_cont[local]:
  s.cs_next_var = a.cs_next_var + 4 /\
  s.cs_next_id = a.cs_next_id + 6 ==>
  (do z <- emit_op EQ [Var (u2s_var a 0); Lit 0w];
      emit_inst JNZ [z; Label (u2s_label a 4); Label (u2s_label a 2)] [];
      kont () od) s =
  kont () (s with <|cs_next_var := a.cs_next_var + 5;
                    cs_next_id := a.cs_next_id + 8;
                    cs_current_insts := s.cs_current_insts ++ u2s_cond a|>)
Proof
  cheat
QED

Theorem u2s_body_cont[local]:
  s.cs_next_var = a.cs_next_var + 5 /\
  s.cs_next_id = a.cs_next_id + 8 ==>
  (do digit <- emit_op Mod [Var (u2s_var a 0); Lit 10w];
      char <- emit_op ADD [Lit 48w; digit];
      base <- emit_op ADD [buf; Lit (n2w n)];
      pos <- emit_op SUB [base; Var (u2s_var a 1)];
      emit_void MSTORE [pos; char];
      val <- emit_op Div [Var (u2s_var a 0); Lit 10w];
      emit_inst ASSIGN [val] [u2s_var a 0];
      count <- emit_op ADD [Var (u2s_var a 1); Lit 1w];
      emit_inst ASSIGN [count] [u2s_var a 1];
      emit_inst JMP [Label (u2s_label a 1)] [];
      kont () od) s =
  kont () (s with <|cs_next_var := a.cs_next_var + 11;
                    cs_next_id := a.cs_next_id + 18;
                    cs_current_insts := s.cs_current_insts ++ u2s_body a buf n|>)
Proof
  cheat
QED

Theorem u2s_zero_cont[local]:
  s.cs_next_var = a.cs_next_var + 11 /\
  s.cs_next_id = a.cs_next_id + 18 ==>
  (do pos <- emit_op ADD [buf; Lit (n2w n)];
      emit_void MSTORE [pos; Lit 48w];
      base <- emit_op ADD [buf; Lit (n2w n)];
      ptr <- emit_op SUB [base; Lit 1w];
      emit_void MSTORE [ptr; Lit 1w];
      emit_inst ASSIGN [ptr] [u2s_var a 2];
      emit_inst JMP [Label (u2s_label a 5)] [];
      kont () od) s =
  kont () (s with <|cs_next_var := a.cs_next_var + 14;
                    cs_next_id := a.cs_next_id + 25;
                    cs_current_insts := s.cs_current_insts ++ u2s_zero a buf n|>)
Proof
  cheat
QED

Theorem u2s_final_cont[local]:
  s.cs_next_var = a.cs_next_var + 14 /\
  s.cs_next_id = a.cs_next_id + 25 ==>
  (do base <- emit_op ADD [buf; Lit (n2w n)];
      ptr <- emit_op SUB [base; Var (u2s_var a 1)];
      emit_void MSTORE [ptr; Var (u2s_var a 1)];
      emit_inst ASSIGN [ptr] [u2s_var a 2];
      emit_inst JMP [Label (u2s_label a 5)] [];
      kont () od) s =
  kont () (s with <|cs_next_var := a.cs_next_var + 16;
                    cs_next_id := a.cs_next_id + 30;
                    cs_current_insts := s.cs_current_insts ++ u2s_final a buf n|>)
Proof
  cheat
QED

Theorem u2s_new_block_cont[local]:
  (do new_block lbl; kont od) s =
  kont (s with <|cs_blocks :=
    <|bb_label := s.cs_current_bb; bb_instructions := s.cs_current_insts|> :: s.cs_blocks;
    cs_current_bb := lbl; cs_current_insts := []|>)
Proof
  cheat
QED

Theorem compile_uint2str_layout_eq:
  compile_alloc_buffer (sz + n) sa = (ba,a) ==>
  compile_uint2str op n sz sa =
    (Var (u2s_var a 2), u2s_end a op ba.buf_operand n)
Proof
  cheat
QED

Theorem compile_uint2str_layout:
  compile_uint2str op n sz sa = (out,sb) ==>
  ?ba a. compile_alloc_buffer (sz + n) sa = (ba,a) /\
         out = Var (u2s_var a 2) /\ u2s_layout a op ba.buf_operand n sb
Proof
  cheat
QED

Definition u2s_frame_def:
  u2s_frame a b sz s0 s <=>
    s with <|vs_vars := s0.vs_vars; vs_memory := s0.vs_memory;
             vs_prev_bb := s0.vs_prev_bb; vs_current_bb := s0.vs_current_bb;
             vs_inst_idx := s0.vs_inst_idx|> = s0 /\
    (!z. not_fresh_at a z ==> lookup_var z s = lookup_var z s0) /\
    (!off len. off + len <= b \/ b + sz <= off ==>
       mem_bytes_at off len s.vs_memory = mem_bytes_at off len s0.vs_memory) /\
    LENGTH s0.vs_memory <= LENGTH s.vs_memory
End

Theorem u2s_frame_refl:
  u2s_frame a b sz s s
Proof
  cheat
QED

Theorem u2s_frame_jump:
  u2s_frame a b sz s0 s ==> u2s_frame a b sz s0 (jump_to lbl s)
Proof
  cheat
QED

Theorem u2s_frame_index:
  u2s_frame a b sz s0 s ==>
  u2s_frame a b sz s0 (s with vs_inst_idx := idx)
Proof
  cheat
QED

Theorem u2s_frame_update:
  u2s_frame a b sz s0 s ==>
  u2s_frame a b sz s0 (update_var (u2s_var a k) w s)
Proof
  cheat
QED

Theorem u2s_frame_mstore:
  u2s_frame a b sz s0 s /\ b <= p /\ p + 32 <= b + sz ==>
  u2s_frame a b sz s0 (mstore p w s)
Proof
  cheat
QED

Definition u2s_safe_def:
  u2s_safe ctx fn cenv cx es a buf b sz inst s0 s <=>
    u2s_frame a b sz s0 s /\ stmt_state_rel ctx fn cenv cx es s /\
    eval_operand buf s = SOME (n2w b) /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
    (!name lb lsz. local_region cenv es.scopes s name lb lsz ==>
       b + sz <= lb \/ lb + lsz <= b)
End

Theorem u2s_safe_initial:
  stmt_state_rel ctx fn cenv cx es s /\
  eval_operand buf s = SOME (n2w b) /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
  (!name lb lsz. local_region cenv es.scopes s name lb lsz ==>
     b + sz <= lb \/ lb + lsz <= b) ==>
  u2s_safe ctx fn cenv cx es a buf b sz inst s s
Proof
  cheat
QED

Theorem u2s_safe_mstore:
  u2s_safe ctx fn cenv cx es a buf b sz inst s0 s /\
  (?p. buf = Var p) /\ b <= at /\ at + 32 <= b + sz /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA ==>
  u2s_safe ctx fn cenv cx es a buf b sz inst s0 (mstore at w s)
Proof
  cheat
QED

Theorem u2s_var_not_local:
  local_ptrs_reserved cenv a ==>
  not_local_ptr cenv scopes (u2s_var a k)
Proof
  cheat
QED

Theorem u2s_safe_update:
  u2s_safe ctx fn cenv cx es a buf b sz inst s0 s /\
  local_ptrs_reserved cenv a /\
  (?p. buf = Var p /\ not_fresh_at a p) ==>
  u2s_safe ctx fn cenv cx es a buf b sz inst s0
    (update_var (u2s_var a k) w s)
Proof
  cheat
QED

Theorem u2s_frame_wb_tail:
  wb_frame cenv es sa spre s0 /\ u2s_frame a b sz s0 s /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= a.cs_next_var /\
  (!name lb lsz. local_region cenv es.scopes s0 name lb lsz ==>
     b + sz <= lb \/ lb + lsz <= b) /\
  (!aid off len. aid < sa.cs_next_id /\
     FLOOKUP spre.vs_allocas aid = SOME (off,len) ==>
     off + len <= b \/ b + sz <= off) ==>
  wb_frame cenv es sa spre s
Proof
  cheat
QED

Definition u2s_digits_def:
  u2s_digits a b n X x str s <=>
    x < dimword (:256) /\ LENGTH str <= n /\
    lookup_var (u2s_var a 0) s = SOME (n2w x) /\
    lookup_var (u2s_var a 1) s = SOME (n2w (LENGTH str)) /\
    mem_bytes_at (b + n - LENGTH str + 32) (LENGTH str) s.vs_memory =
      MAP (n2w o ORD) str /\
    num_to_dec_string X =
      (if x = 0 then [] else num_to_dec_string x) ++ str
End

Theorem u2s_digits_initial:
  0 < X /\ X < dimword (:256) /\
  lookup_var (u2s_var a 0) s = SOME (n2w X) /\
  lookup_var (u2s_var a 1) s = SOME 0w ==>
  u2s_digits a b n X X [] s
Proof
  cheat
QED

Theorem u2s_step_assign:
  eval_operand op s = SOME w ==>
  step_inst_base (mk_inst id ASSIGN [op] [out]) s = OK (update_var out w s)
Proof
  cheat
QED

Theorem u2s_setup_run:
  eval_operand op s = SOME w /\ eval_operand buf s = SOME p /\
  (!z. buf = Var z ==> not_fresh_at a z) ==>
  run_inst_seq (TAKE 3 (u2s_setup a op buf)) s =
    OK (update_var (u2s_var a 2) p
         (update_var (u2s_var a 1) 0w (update_var (u2s_var a 0) w s)))
Proof
  cheat
QED

Theorem u2s_setup_safe:
  u2s_safe ctx fn cenv cx es a buf b sz inst s0 s /\
  local_ptrs_reserved cenv a /\
  (?p. buf = Var p /\ not_fresh_at a p) ==>
  u2s_safe ctx fn cenv cx es a buf b sz inst s0
    (update_var (u2s_var a 2) v
      (update_var (u2s_var a 1) 0w (update_var (u2s_var a 0) w s)))
Proof
  cheat
QED

Theorem u2s_setup_values:
  t = update_var (u2s_var a 2) p
        (update_var (u2s_var a 1) 0w (update_var (u2s_var a 0) w s)) ==>
  lookup_var (u2s_var a 0) t = SOME w /\
  lookup_var (u2s_var a 1) t = SOME 0w /\
  lookup_var (u2s_var a 2) t = SOME p /\
  t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = s.vs_inst_idx /\
  t.vs_halted = s.vs_halted
Proof
  cheat
QED

Theorem u2s_safe_jump:
  u2s_safe ctx fn cenv cx es a buf b sz inst s0 s ==>
  u2s_safe ctx fn cenv cx es a buf b sz inst s0 (jump_to lbl s)
Proof
  cheat
QED

Theorem u2s_digits_jump:
  u2s_digits a b n X x str (jump_to lbl s) <=> u2s_digits a b n X x str s
Proof
  cheat
QED

Theorem u2s_digits_update:
  k <> 0 /\ k <> 1 ==>
  (u2s_digits a b n X x str (update_var (u2s_var a k) w s) <=>
   u2s_digits a b n X x str s)
Proof
  cheat
QED

Theorem u2s_eq_run:
  lookup_var (u2s_var a 0) s = SOME (n2w x) /\ x < dimword (:256) ==>
  run_inst_seq [u2s_inst a id EQ [Var (u2s_var a 0); Lit 0w] [u2s_var a k]] s =
    OK (update_var (u2s_var a k) (bool_to_word (x = 0)) s)
Proof
  cheat
QED

Theorem u2s_jnz_step:
  lookup_var (u2s_var a k) s = SOME w ==>
  step_inst_base (u2s_inst a id JNZ
    [Var (u2s_var a k); Label yes; Label no] []) s =
    OK (jump_to (if w = 0w then no else yes) s)
Proof
  cheat
QED

Theorem u2s_check_run:
  lookup_var (u2s_var a 0) s = SOME (n2w x) /\ x < dimword (:256) /\
  t = update_var (u2s_var a 3) (bool_to_word (x = 0)) s ==>
  run_inst_seq (TAKE 1 (u2s_check a)) s = OK t /\
  step_inst_base (LAST (u2s_check a)) t =
    OK (jump_to (u2s_label a (if x = 0 then 3 else 1)) t)
Proof
  cheat
QED

Theorem u2s_cond_run:
  lookup_var (u2s_var a 0) s = SOME (n2w x) /\ x < dimword (:256) /\
  t = update_var (u2s_var a 4) (bool_to_word (x = 0)) s ==>
  run_inst_seq (TAKE 1 (u2s_cond a)) s = OK t /\
  step_inst_base (LAST (u2s_cond a)) t =
    OK (jump_to (u2s_label a (if x = 0 then 4 else 2)) t)
Proof
  cheat
QED

Theorem decimal_string_quotient_step:
  num_to_dec_string x =
    (if x DIV 10 = 0 then [] else num_to_dec_string (x DIV 10)) ++
    [CHR (48 + x MOD 10)]
Proof
  cheat
QED

Theorem decimal_suffix_step:
  0 < x /\ num_to_dec_string X = num_to_dec_string x ++ str ==>
  num_to_dec_string X =
    (if x DIV 10 = 0 then [] else num_to_dec_string (x DIV 10)) ++
    CHR (48 + x MOD 10)::str
Proof
  cheat
QED

Theorem u2s_digits_room:
  u2s_digits a b n X x str s /\ 0 < x /\
  X < dimword (:256) /\ 78 <= n ==> LENGTH str < n
Proof
  cheat
QED

Theorem u2s_store_digit:
  LENGTH str < n /\
  mem_bytes_at (b + n - LENGTH str + 32) (LENGTH str) s.vs_memory =
    MAP (n2w o ORD) str ==>
  mem_bytes_at (b + n - LENGTH (CHR (48 + x MOD 10)::str) + 32)
    (LENGTH (CHR (48 + x MOD 10)::str))
    (mstore (b + n - LENGTH str) (n2w (48 + x MOD 10)) s).vs_memory =
    MAP (n2w o ORD) (CHR (48 + x MOD 10)::str)
Proof
  cheat
QED

Theorem u2s_digits_step:
  u2s_digits a b n X x str s /\ 0 < x /\ LENGTH str < n ==>
  u2s_digits a b n X (x DIV 10) (CHR (48 + x MOD 10)::str)
    (update_var (u2s_var a 1) (n2w (SUC (LENGTH str)))
      (update_var (u2s_var a 0) (n2w (x DIV 10))
        (mstore (b + n - LENGTH str) (n2w (48 + x MOD 10)) s)))
Proof
  cheat
QED

Theorem u2s_body_address_run:
  eval_operand (Var (u2s_var a 0)) s = SOME xw /\
  eval_operand (Var (u2s_var a 1)) s = SOME iw /\
  eval_operand buf s = SOME bw /\
  (!z. buf = Var z ==> not_fresh_at a z) ==>
  run_inst_seq (TAKE 4 (u2s_body a buf n)) s =
    OK (update_var (u2s_var a 8) (bw + n2w n - iw)
      (update_var (u2s_var a 7) (bw + n2w n)
        (update_var (u2s_var a 6) (48w + safe_mod xw 10w)
          (update_var (u2s_var a 5) (safe_mod xw 10w) s))))
Proof
  cheat
QED

Theorem u2s_body_div_run:
  eval_operand (Var (u2s_var a 0)) s = SOME xw ==>
  run_inst_seq (TAKE 2 (DROP 5 (u2s_body a buf n))) s =
    OK (update_var (u2s_var a 0) (safe_div xw 10w)
      (update_var (u2s_var a 9) (safe_div xw 10w) s))
Proof
  cheat
QED

Theorem u2s_body_count_run:
  eval_operand (Var (u2s_var a 1)) s = SOME iw ==>
  run_inst_seq (TAKE 2 (DROP 7 (u2s_body a buf n))) s =
    OK (update_var (u2s_var a 1) (iw + 1w)
      (update_var (u2s_var a 10) (iw + 1w) s))
Proof
  cheat
QED

Theorem u2s_body_run:
  eval_operand (Var (u2s_var a 0)) s = SOME xw /\
  eval_operand (Var (u2s_var a 1)) s = SOME iw /\
  eval_operand buf s = SOME bw /\
  (!z. buf = Var z ==> not_fresh_at a z) /\
  s1 = update_var (u2s_var a 8) (bw + n2w n - iw)
        (update_var (u2s_var a 7) (bw + n2w n)
         (update_var (u2s_var a 6) (48w + safe_mod xw 10w)
          (update_var (u2s_var a 5) (safe_mod xw 10w) s))) /\
  s2 = mstore (w2n (bw + n2w n - iw)) (48w + safe_mod xw 10w) s1 /\
  s3 = update_var (u2s_var a 0) (safe_div xw 10w)
        (update_var (u2s_var a 9) (safe_div xw 10w) s2) /\
  t = update_var (u2s_var a 1) (iw + 1w)
        (update_var (u2s_var a 10) (iw + 1w) s3) ==>
  run_inst_seq (TAKE 9 (u2s_body a buf n)) s = OK t
Proof
  cheat
QED

Theorem u2s_word_arithmetic:
  x < dimword (:256) /\ i <= n ==>
  safe_mod (n2w x) 10w = n2w (x MOD 10) /\
  safe_div (n2w x) 10w = n2w (x DIV 10) /\
  48w + safe_mod (n2w x) 10w = n2w (48 + x MOD 10) /\
  (n2w b : bytes32) + n2w n - n2w i = n2w (b+n-i) /\
  (n2w i : bytes32) + 1w = n2w (SUC i)
Proof
  cheat
QED

Theorem u2s_body_digits:
  u2s_digits a b n X x str s /\ 0 < x /\ LENGTH str < n /\
  s1 = update_var (u2s_var a 8) v8
        (update_var (u2s_var a 7) v7
         (update_var (u2s_var a 6) v6
          (update_var (u2s_var a 5) v5 s))) /\
  s2 = mstore (b+n-LENGTH str) (n2w (48+x MOD 10)) s1 /\
  s3 = update_var (u2s_var a 0) (n2w (x DIV 10))
        (update_var (u2s_var a 9) (n2w (x DIV 10)) s2) /\
  t = update_var (u2s_var a 1) (n2w (SUC (LENGTH str)))
        (update_var (u2s_var a 10) (n2w (SUC (LENGTH str))) s3) ==>
  u2s_digits a b n X (x DIV 10) (CHR (48+x MOD 10)::str) t
Proof
  cheat
QED

Theorem u2s_body_safe:
  u2s_safe ctx fn cenv cx es a buf b sz inst s0 s /\
  local_ptrs_reserved cenv a /\ (?p. buf = Var p /\ not_fresh_at a p) /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  b <= at /\ at+32 <= b+sz /\
  s1 = update_var (u2s_var a 8) v8
        (update_var (u2s_var a 7) v7
         (update_var (u2s_var a 6) v6
          (update_var (u2s_var a 5) v5 s))) /\
  s2 = mstore at w s1 /\
  s3 = update_var (u2s_var a 0) q (update_var (u2s_var a 9) q s2) /\
  t = update_var (u2s_var a 1) i (update_var (u2s_var a 10) i s3) ==>
  u2s_safe ctx fn cenv cx es a buf b sz inst s0 t
Proof
  cheat
QED

Theorem u2s_update_control:
  (update_var z w s).vs_current_bb = s.vs_current_bb /\
  (update_var z w s).vs_inst_idx = s.vs_inst_idx /\
  (update_var z w s).vs_prev_bb = s.vs_prev_bb /\
  (update_var z w s).vs_halted = s.vs_halted
Proof
  cheat
QED

Theorem u2s_mstore_control:
  (mstore at w s).vs_current_bb = s.vs_current_bb /\
  (mstore at w s).vs_inst_idx = s.vs_inst_idx /\
  (mstore at w s).vs_prev_bb = s.vs_prev_bb /\
  (mstore at w s).vs_halted = s.vs_halted
Proof
  cheat
QED

Theorem u2s_body_iteration:
  u2s_safe ctx fn cenv cx es a buf b sz inst s0 s /\
  u2s_digits a b n X x str s /\ 0 < x /\ LENGTH str < n /\
  local_ptrs_reserved cenv a /\ (?p. buf = Var p /\ not_fresh_at a p) /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  n+32 <= sz /\ b+sz < dimword (:256) ==>
  ?t. run_inst_seq (TAKE 9 (u2s_body a buf n)) s = OK t /\
      u2s_safe ctx fn cenv cx es a buf b sz inst s0 t /\
      u2s_digits a b n X (x DIV 10) (CHR (48+x MOD 10)::str) t /\
      t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = s.vs_inst_idx /\
      t.vs_prev_bb = s.vs_prev_bb /\ t.vs_halted = s.vs_halted
Proof
  cheat
QED

Theorem u2s_final_run:
  eval_operand buf s = SOME bw /\
  eval_operand (Var (u2s_var a 1)) s = SOME iw /\
  s1 = update_var (u2s_var a 14) (bw + n2w n) s /\
  s2 = update_var (u2s_var a 15) (bw + n2w n - iw) s1 /\
  s3 = mstore (w2n (bw + n2w n - iw)) iw s2 /\
  t = update_var (u2s_var a 2) (bw + n2w n - iw) s3 ==>
  run_inst_seq (TAKE 4 (u2s_final a buf n)) s = OK t
Proof
  cheat
QED

Theorem u2s_final_encoding:
  u2s_digits a b n X 0 str s /\
  s1 = update_var (u2s_var a 14) v s /\
  s2 = update_var (u2s_var a 15) (n2w (b+n-LENGTH str)) s1 /\
  s3 = mstore (b+n-LENGTH str) (n2w (LENGTH str)) s2 /\
  t = update_var (u2s_var a 2) (n2w (b+n-LENGTH str)) s3 ==>
  val_in_memory ty (StringV str) (b+n-LENGTH str) t.vs_memory /\
  eval_operand (Var (u2s_var a 2)) t = SOME (n2w (b+n-LENGTH str))
Proof
  cheat
QED

Theorem u2s_final_safe:
  u2s_safe ctx fn cenv cx es a buf b sz inst s0 s /\
  local_ptrs_reserved cenv a /\ (?p. buf = Var p /\ not_fresh_at a p) /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  b <= at /\ at+32 <= b+sz /\
  s1 = update_var (u2s_var a 14) v s /\
  s2 = update_var (u2s_var a 15) (n2w at) s1 /\
  s3 = mstore at w s2 /\
  t = update_var (u2s_var a 2) (n2w at) s3 ==>
  u2s_safe ctx fn cenv cx es a buf b sz inst s0 t
Proof
  cheat
QED

Theorem u2s_final_result:
  u2s_safe ctx fn cenv cx es a buf b sz inst s0 s /\
  u2s_digits a b n X 0 str s /\ local_ptrs_reserved cenv a /\
  (?p. buf = Var p /\ not_fresh_at a p) /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  n+32 <= sz /\ b+sz < dimword (:256) ==>
  ?t. run_inst_seq (TAKE 4 (u2s_final a buf n)) s = OK t /\
      u2s_safe ctx fn cenv cx es a buf b sz inst s0 t /\
      eval_operand (Var (u2s_var a 2)) t = SOME (n2w (b+n-LENGTH str)) /\
      val_in_memory ty (StringV str) (b+n-LENGTH str) t.vs_memory /\
      b <= b+n-LENGTH str /\ b+n-LENGTH str+32+LENGTH str <= b+sz /\
      t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = s.vs_inst_idx /\
      t.vs_prev_bb = s.vs_prev_bb /\ t.vs_halted = s.vs_halted
Proof
  cheat
QED

Theorem u2s_zero_run:
  eval_operand buf s = SOME bw /\
  (?p. buf = Var p /\ not_fresh_at a p) /\
  s1 = update_var (u2s_var a 11) (bw+n2w n) s /\
  s2 = mstore (w2n (bw+n2w n)) 48w s1 /\
  s3 = update_var (u2s_var a 12) (bw+n2w n) s2 /\
  s4 = update_var (u2s_var a 13) (bw+n2w n-1w) s3 /\
  s5 = mstore (w2n (bw+n2w n-1w)) 1w s4 /\
  t = update_var (u2s_var a 2) (bw+n2w n-1w) s5 ==>
  run_inst_seq (TAKE 6 (u2s_zero a buf n)) s = OK t
Proof
  cheat
QED

Theorem u2s_zero_encoding:
  1 <= n /\
  s1 = update_var (u2s_var a 11) v s /\
  s2 = mstore (b+n) 48w s1 /\
  s3 = update_var (u2s_var a 12) v s2 /\
  s4 = update_var (u2s_var a 13) (n2w (b+n-1)) s3 /\
  s5 = mstore (b+n-1) 1w s4 /\
  t = update_var (u2s_var a 2) (n2w (b+n-1)) s5 ==>
  val_in_memory ty (StringV "0") (b+n-1) t.vs_memory /\
  eval_operand (Var (u2s_var a 2)) t = SOME (n2w (b+n-1))
Proof
  cheat
QED

Theorem u2s_zero_safe:
  u2s_safe ctx fn cenv cx es a buf b sz inst s0 s /\
  local_ptrs_reserved cenv a /\ (?p. buf = Var p /\ not_fresh_at a p) /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  1 <= n /\ n+32 <= sz /\
  s1 = update_var (u2s_var a 11) v s /\
  s2 = mstore (b+n) 48w s1 /\
  s3 = update_var (u2s_var a 12) v s2 /\
  s4 = update_var (u2s_var a 13) (n2w (b+n-1)) s3 /\
  s5 = mstore (b+n-1) 1w s4 /\
  t = update_var (u2s_var a 2) (n2w (b+n-1)) s5 ==>
  u2s_safe ctx fn cenv cx es a buf b sz inst s0 t
Proof
  cheat
QED

Theorem u2s_zero_result:
  u2s_safe ctx fn cenv cx es a buf b sz inst s0 s /\
  local_ptrs_reserved cenv a /\ (?p. buf = Var p /\ not_fresh_at a p) /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  1 <= n /\ n+32 <= sz /\ b+sz < dimword (:256) ==>
  ?t. run_inst_seq (TAKE 6 (u2s_zero a buf n)) s = OK t /\
      u2s_safe ctx fn cenv cx es a buf b sz inst s0 t /\
      eval_operand (Var (u2s_var a 2)) t = SOME (n2w (b+n-1)) /\
      val_in_memory ty (StringV "0") (b+n-1) t.vs_memory /\
      b <= b+n-1 /\ b+n-1+33 <= b+sz /\
      t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = s.vs_inst_idx /\
      t.vs_prev_bb = s.vs_prev_bb /\ t.vs_halted = s.vs_halted
Proof
  cheat
QED

(* Lift a straight-line prefix without exposing individual instruction steps. *)
Theorem u2s_run_from_prefix:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX is (DROP s.vs_inst_idx bb.bb_instructions) /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) is /\
  run_inst_seq is s = OK t ==>
  run_from fuel ctx fn s =
  run_from fuel ctx fn (t with vs_inst_idx := s.vs_inst_idx + LENGTH is)
Proof
  cheat
QED

Theorem u2s_run_from_block:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = is ++ [j] /\ s.vs_inst_idx = 0 /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) is /\
  run_inst_seq is s = OK t /\
  is_terminator j.inst_opcode /\ j.inst_opcode <> INVOKE /\
  step_inst_base j (t with vs_inst_idx := LENGTH is) = OK (jump_to lbl t) /\
  ~t.vs_halted /\
  run_from fuel ctx fn (jump_to lbl t) = r /\ (!e. r <> Error e) ==>
  run_from (SUC fuel) ctx fn s = r
Proof
  cheat
QED

Theorem u2s_final_continue:
  lookup_block (u2s_label a 4) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 4; bb_instructions := u2s_final a buf n|> /\
  s.vs_current_bb = u2s_label a 4 /\ s.vs_inst_idx = 0 /\
  run_inst_seq (TAKE 4 (u2s_final a buf n)) s = OK t /\ ~t.vs_halted /\
  run_from fuel ctx fn (jump_to (u2s_label a 5) t) = r /\ (!e. r <> Error e) ==>
  run_from (SUC fuel) ctx fn s = r
Proof
  cheat
QED

Theorem u2s_zero_continue:
  lookup_block (u2s_label a 3) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 3; bb_instructions := u2s_zero a buf n|> /\
  s.vs_current_bb = u2s_label a 3 /\ s.vs_inst_idx = 0 /\
  run_inst_seq (TAKE 6 (u2s_zero a buf n)) s = OK t /\ ~t.vs_halted /\
  run_from fuel ctx fn (jump_to (u2s_label a 5) t) = r /\ (!e. r <> Error e) ==>
  run_from (SUC fuel) ctx fn s = r
Proof
  cheat
QED

Theorem u2s_body_continue:
  lookup_block (u2s_label a 2) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 2; bb_instructions := u2s_body a buf n|> /\
  s.vs_current_bb = u2s_label a 2 /\ s.vs_inst_idx = 0 /\
  run_inst_seq (TAKE 9 (u2s_body a buf n)) s = OK t /\ ~t.vs_halted /\
  run_from fuel ctx fn (jump_to (u2s_label a 1) t) = r /\ (!e. r <> Error e) ==>
  run_from (SUC fuel) ctx fn s = r
Proof
  cheat
QED

Theorem u2s_cond_continue:
  lookup_block (u2s_label a 1) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 1; bb_instructions := u2s_cond a|> /\
  s.vs_current_bb = u2s_label a 1 /\ s.vs_inst_idx = 0 /\
  lookup_var (u2s_var a 0) s = SOME (n2w x) /\ x < dimword (:256) /\
  t = update_var (u2s_var a 4) (bool_to_word (x = 0)) s /\ ~t.vs_halted /\
  run_from fuel ctx fn (jump_to (u2s_label a (if x = 0 then 4 else 2)) t) = r /\
  (!e. r <> Error e) ==>
  run_from (SUC fuel) ctx fn s = r
Proof
  cheat
QED

Theorem u2s_check_continue:
  lookup_block (u2s_label a 0) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 0; bb_instructions := u2s_check a|> /\
  s.vs_current_bb = u2s_label a 0 /\ s.vs_inst_idx = 0 /\
  lookup_var (u2s_var a 0) s = SOME (n2w x) /\ x < dimword (:256) /\
  t = update_var (u2s_var a 3) (bool_to_word (x = 0)) s /\ ~t.vs_halted /\
  run_from fuel ctx fn (jump_to (u2s_label a (if x = 0 then 3 else 1)) t) = r /\
  (!e. r <> Error e) ==>
  run_from (SUC fuel) ctx fn s = r
Proof
  cheat
QED

Theorem u2s_setup_continue:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = pre ++ u2s_setup a op buf /\
  s.vs_inst_idx = LENGTH pre /\
  eval_operand op s = SOME w /\ eval_operand buf s = SOME p /\
  (!z. buf = Var z ==> not_fresh_at a z) /\ ~s.vs_halted /\
  t = update_var (u2s_var a 2) p
        (update_var (u2s_var a 1) 0w (update_var (u2s_var a 0) w s)) /\
  run_from fuel ctx fn (jump_to (u2s_label a 0) t) = r /\ (!e. r <> Error e) ==>
  run_from (SUC fuel) ctx fn s = r
Proof
  cheat
QED

Theorem u2s_alloc_safe:
  compile_alloc_buffer sz sa = (buf,a) /\
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\ sz < dimword (:256) /\
  inst = mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
    [STRING #"%" (toString sa.cs_next_var)] /\ MEM inst (fn_insts fn) ==>
  ?t (w:256 word). run_inst_seq (emitted_insts sa a) s = OK t /\
    u2s_safe ctx fn cenv cx es a buf.buf_operand (w2n w) sz inst t t /\
    w2n w + sz < dimword (:256) /\ sa.cs_next_id < a.cs_next_id /\
    wb_frame cenv es sa s t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid off len. aid < sa.cs_next_id /\
       FLOOKUP s.vs_allocas aid = SOME (off,len) ==>
       off + len <= w2n w \/ w2n w + sz <= off) /\
    (!name off len. local_region cenv es.scopes t name off len ==>
       w2n w + sz <= off \/ off + len <= w2n w) /\
    (?p. buf.buf_operand = Var p /\ not_fresh_at a p)
Proof
  cheat
QED

Theorem u2s_alloc_layout_code:
  compile_alloc_buffer sz sa = (ba,a) /\
  u2s_layout a op ba.buf_operand n sb /\ fn_has_code sa sb fn ==>
  (!bb. MEM bb (u2s_blocks a op ba.buf_operand n) ==>
        lookup_block bb.bb_label fn.fn_blocks = SOME bb) /\
  lookup_block a.cs_current_bb fn.fn_blocks =
    SOME <|bb_label := a.cs_current_bb;
           bb_instructions := a.cs_current_insts ++ u2s_setup a op ba.buf_operand|> /\
  fn_has_code sa a fn /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn)
Proof
  cheat
QED

Theorem u2s_alloc_step:
  compile_alloc_buffer sz sa = (ba,a) /\
  run_inst_seq (emitted_insts sa a) s = OK t ==>
  step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
      [STRING #"%" (toString sa.cs_next_var)]) s = OK t
Proof
  cheat
QED

Theorem u2s_alloc_continue:
  compile_alloc_buffer sz sa = (ba,a) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = a.cs_current_insts ++ tail /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa a) s = OK t ==>
  run_from fuel ctx fn s =
  run_from fuel ctx fn (t with vs_inst_idx := LENGTH a.cs_current_insts)
Proof
  cheat
QED

Theorem u2s_safe_index:
  u2s_safe ctx fn cenv cx es a buf b sz inst s0 s ==>
  u2s_safe ctx fn cenv cx es a buf b sz inst s0 (s with vs_inst_idx := idx)
Proof
  cheat
QED

Theorem u2s_alloc_control:
  compile_alloc_buffer sz sa = (ba,a) /\
  run_inst_seq (emitted_insts sa a) s = OK t ==>
  t.vs_current_bb = s.vs_current_bb /\ t.vs_halted = s.vs_halted
Proof
  cheat
QED

Theorem u2s_safe_wb_tail:
  wb_frame cenv es sa s s0 /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= a.cs_next_var /\ inst.inst_id = sa.cs_next_id /\
  (!name lb len. local_region cenv es.scopes s0 name lb len ==>
    b+sz <= lb \/ lb+len <= b) /\
  (!aid off len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (off,len) ==>
    off+len <= b \/ b+sz <= off) ==>
  !out. u2s_safe ctx fn cenv cx es a buf b sz inst s0 out ==>
    stmt_state_rel ctx fn cenv cx es out /\ wb_frame cenv es sa s out /\
    FLOOKUP out.vs_allocas sa.cs_next_id = SOME (b,sz)
Proof
  cheat
QED

(* The code carrier need not own the semantic allocation invariant. *)
Theorem u2s_cond_transition:
  lookup_block (u2s_label a 1) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 1; bb_instructions := u2s_cond a|> /\
  s.vs_current_bb = u2s_label a 1 /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  u2s_safe ctx func cenv cx es a buf b sz inst s0 s /\
  u2s_digits a b n X x str s /\ local_ptrs_reserved cenv a /\
  (?p. buf = Var p /\ not_fresh_at a p) ==>
  ?t. u2s_safe ctx func cenv cx es a buf b sz inst s0 t /\
      u2s_digits a b n X x str t /\
      t.vs_current_bb = u2s_label a (if x = 0 then 4 else 2) /\
      t.vs_inst_idx = 0 /\ ~t.vs_halted /\
      (!fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
                ?fuel'. run_from fuel' ctx fn s = r)
Proof
  cheat
QED

Theorem u2s_body_transition:
  lookup_block (u2s_label a 2) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 2; bb_instructions := u2s_body a buf n|> /\
  s.vs_current_bb = u2s_label a 2 /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  u2s_safe ctx func cenv cx es a buf b sz inst s0 s /\
  u2s_digits a b n X x str s /\ 0 < x /\ LENGTH str < n /\
  local_ptrs_reserved cenv a /\ (?p. buf = Var p /\ not_fresh_at a p) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  n+32 <= sz /\ b+sz < dimword (:256) ==>
  ?t. u2s_safe ctx func cenv cx es a buf b sz inst s0 t /\
      u2s_digits a b n X (x DIV 10) (CHR (48+x MOD 10)::str) t /\
      t.vs_current_bb = u2s_label a 1 /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
      (!fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
                ?fuel'. run_from fuel' ctx fn s = r)
Proof
  cheat
QED

Theorem u2s_final_exit:
  lookup_block (u2s_label a 4) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 4; bb_instructions := u2s_final a buf n|> /\
  s.vs_current_bb = u2s_label a 4 /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  u2s_safe ctx func cenv cx es a buf b sz inst s0 s /\
  u2s_digits a b n X 0 str s /\ local_ptrs_reserved cenv a /\
  (?p. buf = Var p /\ not_fresh_at a p) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  n+32 <= sz /\ b+sz < dimword (:256) ==>
  ?t. u2s_safe ctx func cenv cx es a buf b sz inst s0 t /\
      eval_operand (Var (u2s_var a 2)) t = SOME (n2w (b+n-LENGTH str)) /\
      val_in_memory ty (StringV str) (b+n-LENGTH str) t.vs_memory /\
      b <= b+n-LENGTH str /\ b+n-LENGTH str+32+LENGTH str <= b+sz /\
      t.vs_current_bb = u2s_label a 5 /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
      (!fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
                ?fuel'. run_from fuel' ctx fn s = r)
Proof
  cheat
QED

Theorem u2s_loop:
  !x s str.
  (!bb. MEM bb (u2s_blocks a op buf n) ==>
        lookup_block bb.bb_label fn.fn_blocks = SOME bb) /\
  s.vs_current_bb = u2s_label a 1 /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  u2s_safe ctx func cenv cx es a buf b sz inst s0 s /\
  u2s_digits a b n X x str s /\ local_ptrs_reserved cenv a /\
  (?p. buf = Var p /\ not_fresh_at a p) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  X < dimword (:256) /\ 78 <= n /\ n+32 <= sz /\ b+sz < dimword (:256) ==>
  ?t. u2s_safe ctx func cenv cx es a buf b sz inst s0 t /\
      eval_operand (Var (u2s_var a 2)) t = SOME (n2w (b+n-LENGTH (num_to_dec_string X))) /\
      val_in_memory ty (StringV (num_to_dec_string X))
        (b+n-LENGTH (num_to_dec_string X)) t.vs_memory /\
      b <= b+n-LENGTH (num_to_dec_string X) /\
      b+n-LENGTH (num_to_dec_string X)+32+LENGTH (num_to_dec_string X) <= b+sz /\
      t.vs_current_bb = u2s_label a 5 /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
      (!fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
                ?fuel'. run_from fuel' ctx fn s = r)
Proof
  cheat
QED




Theorem u2s_zero_exit:
  lookup_block (u2s_label a 3) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 3; bb_instructions := u2s_zero a buf n|> /\
  s.vs_current_bb = u2s_label a 3 /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  u2s_safe ctx func cenv cx es a buf b sz inst s0 s /\
  local_ptrs_reserved cenv a /\ (?p. buf = Var p /\ not_fresh_at a p) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  1 <= n /\ n+32 <= sz /\ b+sz < dimword (:256) ==>
  ?t. u2s_safe ctx func cenv cx es a buf b sz inst s0 t /\
      eval_operand (Var (u2s_var a 2)) t = SOME (n2w (b+n-1)) /\
      val_in_memory ty (StringV "0") (b+n-1) t.vs_memory /\
      b <= b+n-1 /\ b+n-1+33 <= b+sz /\
      t.vs_current_bb = u2s_label a 5 /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
      (!fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
                ?fuel'. run_from fuel' ctx fn s = r)
Proof
  cheat
QED

Theorem u2s_check_transition:
  lookup_block (u2s_label a 0) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 0; bb_instructions := u2s_check a|> /\
  s.vs_current_bb = u2s_label a 0 /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  u2s_safe ctx func cenv cx es a buf b sz inst s0 s /\
  u2s_digits a b n X x str s /\ local_ptrs_reserved cenv a /\
  (?p. buf = Var p /\ not_fresh_at a p) ==>
  ?t. u2s_safe ctx func cenv cx es a buf b sz inst s0 t /\
      u2s_digits a b n X x str t /\
      t.vs_current_bb = u2s_label a (if x = 0 then 3 else 1) /\
      t.vs_inst_idx = 0 /\ ~t.vs_halted /\
      (!fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
                ?fuel'. run_from fuel' ctx fn s = r)
Proof
  cheat
QED

Theorem u2s_check_zero_transition:
  lookup_block (u2s_label a 0) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 0; bb_instructions := u2s_check a|> /\
  s.vs_current_bb = u2s_label a 0 /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  u2s_safe ctx func cenv cx es a buf b sz inst s0 s /\
  lookup_var (u2s_var a 0) s = SOME 0w /\ local_ptrs_reserved cenv a /\
  (?p. buf = Var p /\ not_fresh_at a p) ==>
  ?t. u2s_safe ctx func cenv cx es a buf b sz inst s0 t /\
      t.vs_current_bb = u2s_label a 3 /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
      (!fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
                ?fuel'. run_from fuel' ctx fn s = r)
Proof
  cheat
QED

Theorem u2s_check_exit:
  (!bb. MEM bb (u2s_blocks a op buf n) ==>
        lookup_block bb.bb_label fn.fn_blocks = SOME bb) /\
  s.vs_current_bb = u2s_label a 0 /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  u2s_safe ctx func cenv cx es a buf b sz inst s0 s /\
  lookup_var (u2s_var a 0) s = SOME (n2w X) /\
  lookup_var (u2s_var a 1) s = SOME 0w /\ local_ptrs_reserved cenv a /\
  (?p. buf = Var p /\ not_fresh_at a p) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  X < dimword (:256) /\ 78 <= n /\ n+32 <= sz /\ b+sz < dimword (:256) ==>
  ?t. u2s_safe ctx func cenv cx es a buf b sz inst s0 t /\
      eval_operand (Var (u2s_var a 2)) t = SOME (n2w (b+n-LENGTH (num_to_dec_string X))) /\
      val_in_memory ty (StringV (num_to_dec_string X))
        (b+n-LENGTH (num_to_dec_string X)) t.vs_memory /\
      b <= b+n-LENGTH (num_to_dec_string X) /\
      b+n-LENGTH (num_to_dec_string X)+32+LENGTH (num_to_dec_string X) <= b+sz /\
      t.vs_current_bb = u2s_label a 5 /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
      (!fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
                ?fuel'. run_from fuel' ctx fn s = r)
Proof
  cheat
QED




Theorem u2s_setup_transition:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = pre ++ u2s_setup a op buf /\
  s.vs_inst_idx = LENGTH pre /\ ~s.vs_halted /\
  eval_operand op s = SOME (n2w X) /\
  u2s_safe ctx func cenv cx es a buf b sz inst s0 s /\
  local_ptrs_reserved cenv a /\ (?p. buf = Var p /\ not_fresh_at a p) ==>
  ?t. u2s_safe ctx func cenv cx es a buf b sz inst s0 t /\
      lookup_var (u2s_var a 0) t = SOME (n2w X) /\
      lookup_var (u2s_var a 1) t = SOME 0w /\
      t.vs_current_bb = u2s_label a 0 /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
      (!fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
                ?fuel'. run_from fuel' ctx fn s = r)
Proof
  cheat
QED

Theorem u2s_setup_exit:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = pre ++ u2s_setup a op buf /\
  s.vs_inst_idx = LENGTH pre /\ ~s.vs_halted /\
  (!bb. MEM bb (u2s_blocks a op buf n) ==>
        lookup_block bb.bb_label fn.fn_blocks = SOME bb) /\
  eval_operand op s = SOME (n2w X) /\
  u2s_safe ctx func cenv cx es a buf b sz inst s0 s /\
  local_ptrs_reserved cenv a /\ (?p. buf = Var p /\ not_fresh_at a p) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  X < dimword (:256) /\ 78 <= n /\ n+32 <= sz /\ b+sz < dimword (:256) ==>
  ?t. u2s_safe ctx func cenv cx es a buf b sz inst s0 t /\
      eval_operand (Var (u2s_var a 2)) t = SOME (n2w (b+n-LENGTH (num_to_dec_string X))) /\
      val_in_memory ty (StringV (num_to_dec_string X))
        (b+n-LENGTH (num_to_dec_string X)) t.vs_memory /\
      b <= b+n-LENGTH (num_to_dec_string X) /\
      b+n-LENGTH (num_to_dec_string X)+32+LENGTH (num_to_dec_string X) <= b+sz /\
      t.vs_current_bb = u2s_label a 5 /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
      (!fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
                ?fuel'. run_from fuel' ctx fn s = r)
Proof
  cheat
QED

Theorem u2s_setup_entry_exit:
  s.vs_current_bb = a.cs_current_bb /\
  lookup_block a.cs_current_bb fn.fn_blocks = SOME
    <|bb_label := a.cs_current_bb;
      bb_instructions := a.cs_current_insts ++ u2s_setup a op buf|> /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\ ~s.vs_halted /\
  (!bb. MEM bb (u2s_blocks a op buf n) ==>
        lookup_block bb.bb_label fn.fn_blocks = SOME bb) /\
  eval_operand op s = SOME (n2w X) /\
  u2s_safe ctx func cenv cx es a buf b sz inst s0 s /\
  local_ptrs_reserved cenv a /\ (?p. buf = Var p /\ not_fresh_at a p) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  X < dimword (:256) /\ 78 <= n /\ n+32 <= sz /\ b+sz < dimword (:256) ==>
  ?t. u2s_safe ctx func cenv cx es a buf b sz inst s0 t /\
      eval_operand (Var (u2s_var a 2)) t = SOME (n2w (b+n-LENGTH (num_to_dec_string X))) /\
      val_in_memory ty (StringV (num_to_dec_string X))
        (b+n-LENGTH (num_to_dec_string X)) t.vs_memory /\
      b <= b+n-LENGTH (num_to_dec_string X) /\
      b+n-LENGTH (num_to_dec_string X)+32+LENGTH (num_to_dec_string X) <= b+sz /\
      t.vs_current_bb = u2s_label a 5 /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
      (!fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
                ?fuel'. run_from fuel' ctx fn s = r)
Proof
  cheat
QED

(* ===== Counted target paths of the uint2str code =====

   The fragment is GAS-free, so each block from the setup jump to the exit
   label is a counted path with no readings. *)

Theorem u2s_path_then[local]:
  gas_marked_path F ctx fn s 0 (OK c) /\ gas_marked_path F ctx fn c 0 r ==>
  gas_marked_path F ctx fn s 0 r
Proof
  cheat
QED

(* A straight-line block body ending in a jump: the multi-block runs below
   are composed from these with gas_marked_path_then. *)
Theorem u2s_block_path[local]:
  !ctx fn s bb pre is j t lbl.
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = pre ++ is ++ [j] /\ s.vs_inst_idx = LENGTH pre /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) is /\
  EVERY (\i. i.inst_opcode <> GAS) is /\
  (j.inst_opcode = JMP \/ j.inst_opcode = JNZ) /\
  run_inst_seq is s = OK t /\ ~s.vs_halted /\ ~t.vs_halted /\
  step_inst_base j (t with vs_inst_idx := LENGTH pre + LENGTH is) =
    OK (jump_to lbl t) ==>
  gas_marked_path F ctx fn s 0 (OK (jump_to lbl t))
Proof
  cheat
QED

Theorem u2s_path_continue[local]:
  gas_marked_path F ctx fn s n (OK t) ==>
  !fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
           ?fuel'. run_from fuel' ctx fn s = r
Proof
  cheat
QED

Theorem u2s_cond_path:
  lookup_block (u2s_label a 1) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 1; bb_instructions := u2s_cond a|> /\
  s.vs_current_bb = u2s_label a 1 /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  u2s_safe ctx func cenv cx es a buf b sz inst s0 s /\
  u2s_digits a b n X x str s /\ local_ptrs_reserved cenv a /\
  (?p. buf = Var p /\ not_fresh_at a p) ==>
  ?t. gas_marked_path F ctx fn s 0 (OK t) /\
      u2s_safe ctx func cenv cx es a buf b sz inst s0 t /\
      u2s_digits a b n X x str t /\
      t.vs_current_bb = u2s_label a (if x = 0 then 4 else 2) /\
      t.vs_inst_idx = 0 /\ ~t.vs_halted
Proof
  cheat
QED

Theorem u2s_check_path:
  lookup_block (u2s_label a 0) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 0; bb_instructions := u2s_check a|> /\
  s.vs_current_bb = u2s_label a 0 /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  u2s_safe ctx func cenv cx es a buf b sz inst s0 s /\
  lookup_var (u2s_var a 0) s = SOME (n2w x) /\ x < dimword (:256) /\
  local_ptrs_reserved cenv a /\ (?p. buf = Var p /\ not_fresh_at a p) ==>
  ?t. gas_marked_path F ctx fn s 0 (OK t) /\
      u2s_safe ctx func cenv cx es a buf b sz inst s0 t /\
      (!y str. u2s_digits a b n X y str t <=> u2s_digits a b n X y str s) /\
      t.vs_current_bb = u2s_label a (if x = 0 then 3 else 1) /\
      t.vs_inst_idx = 0 /\ ~t.vs_halted
Proof
  cheat
QED

Theorem u2s_body_path:
  lookup_block (u2s_label a 2) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 2; bb_instructions := u2s_body a buf n|> /\
  s.vs_current_bb = u2s_label a 2 /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  u2s_safe ctx func cenv cx es a buf b sz inst s0 s /\
  u2s_digits a b n X x str s /\ 0 < x /\ LENGTH str < n /\
  local_ptrs_reserved cenv a /\ (?p. buf = Var p /\ not_fresh_at a p) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  n+32 <= sz /\ b+sz < dimword (:256) ==>
  ?t. gas_marked_path F ctx fn s 0 (OK t) /\
      u2s_safe ctx func cenv cx es a buf b sz inst s0 t /\
      u2s_digits a b n X (x DIV 10) (CHR (48+x MOD 10)::str) t /\
      t.vs_current_bb = u2s_label a 1 /\ t.vs_inst_idx = 0 /\ ~t.vs_halted
Proof
  cheat
QED

Theorem u2s_final_path:
  lookup_block (u2s_label a 4) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 4; bb_instructions := u2s_final a buf n|> /\
  s.vs_current_bb = u2s_label a 4 /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  u2s_safe ctx func cenv cx es a buf b sz inst s0 s /\
  u2s_digits a b n X 0 str s /\ local_ptrs_reserved cenv a /\
  (?p. buf = Var p /\ not_fresh_at a p) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  n+32 <= sz /\ b+sz < dimword (:256) ==>
  ?t. gas_marked_path F ctx fn s 0 (OK t) /\
      u2s_safe ctx func cenv cx es a buf b sz inst s0 t /\
      eval_operand (Var (u2s_var a 2)) t = SOME (n2w (b+n-LENGTH str)) /\
      val_in_memory ty (StringV str) (b+n-LENGTH str) t.vs_memory /\
      b <= b+n-LENGTH str /\ b+n-LENGTH str+32+LENGTH str <= b+sz /\
      t.vs_current_bb = u2s_label a 5 /\ t.vs_inst_idx = 0 /\ ~t.vs_halted
Proof
  cheat
QED

Theorem u2s_zero_path:
  lookup_block (u2s_label a 3) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 3; bb_instructions := u2s_zero a buf n|> /\
  s.vs_current_bb = u2s_label a 3 /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  u2s_safe ctx func cenv cx es a buf b sz inst s0 s /\
  local_ptrs_reserved cenv a /\ (?p. buf = Var p /\ not_fresh_at a p) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  1 <= n /\ n+32 <= sz /\ b+sz < dimword (:256) ==>
  ?t. gas_marked_path F ctx fn s 0 (OK t) /\
      u2s_safe ctx func cenv cx es a buf b sz inst s0 t /\
      eval_operand (Var (u2s_var a 2)) t = SOME (n2w (b+n-1)) /\
      val_in_memory ty (StringV "0") (b+n-1) t.vs_memory /\
      b <= b+n-1 /\ b+n-1+33 <= b+sz /\
      t.vs_current_bb = u2s_label a 5 /\ t.vs_inst_idx = 0 /\ ~t.vs_halted
Proof
  cheat
QED

Theorem u2s_loop_path:
  !x s str.
  (!bb. MEM bb (u2s_blocks a op buf n) ==>
        lookup_block bb.bb_label fn.fn_blocks = SOME bb) /\
  s.vs_current_bb = u2s_label a 1 /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  u2s_safe ctx func cenv cx es a buf b sz inst s0 s /\
  u2s_digits a b n X x str s /\ local_ptrs_reserved cenv a /\
  (?p. buf = Var p /\ not_fresh_at a p) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  X < dimword (:256) /\ 78 <= n /\ n+32 <= sz /\ b+sz < dimword (:256) ==>
  ?t. gas_marked_path F ctx fn s 0 (OK t) /\
      u2s_safe ctx func cenv cx es a buf b sz inst s0 t /\
      eval_operand (Var (u2s_var a 2)) t = SOME (n2w (b+n-LENGTH (num_to_dec_string X))) /\
      val_in_memory ty (StringV (num_to_dec_string X))
        (b+n-LENGTH (num_to_dec_string X)) t.vs_memory /\
      b <= b+n-LENGTH (num_to_dec_string X) /\
      b+n-LENGTH (num_to_dec_string X)+32+LENGTH (num_to_dec_string X) <= b+sz /\
      t.vs_current_bb = u2s_label a 5 /\ t.vs_inst_idx = 0 /\ ~t.vs_halted
Proof
  cheat
QED




Theorem u2s_check_exit_path:
  (!bb. MEM bb (u2s_blocks a op buf n) ==>
        lookup_block bb.bb_label fn.fn_blocks = SOME bb) /\
  s.vs_current_bb = u2s_label a 0 /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  u2s_safe ctx func cenv cx es a buf b sz inst s0 s /\
  lookup_var (u2s_var a 0) s = SOME (n2w X) /\
  lookup_var (u2s_var a 1) s = SOME 0w /\ local_ptrs_reserved cenv a /\
  (?p. buf = Var p /\ not_fresh_at a p) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  X < dimword (:256) /\ 78 <= n /\ n+32 <= sz /\ b+sz < dimword (:256) ==>
  ?t. gas_marked_path F ctx fn s 0 (OK t) /\
      u2s_safe ctx func cenv cx es a buf b sz inst s0 t /\
      eval_operand (Var (u2s_var a 2)) t = SOME (n2w (b+n-LENGTH (num_to_dec_string X))) /\
      val_in_memory ty (StringV (num_to_dec_string X))
        (b+n-LENGTH (num_to_dec_string X)) t.vs_memory /\
      b <= b+n-LENGTH (num_to_dec_string X) /\
      b+n-LENGTH (num_to_dec_string X)+32+LENGTH (num_to_dec_string X) <= b+sz /\
      t.vs_current_bb = u2s_label a 5 /\ t.vs_inst_idx = 0 /\ ~t.vs_halted
Proof
  cheat
QED

Theorem u2s_setup_entry_path:
  s.vs_current_bb = a.cs_current_bb /\
  lookup_block a.cs_current_bb fn.fn_blocks = SOME
    <|bb_label := a.cs_current_bb;
      bb_instructions := a.cs_current_insts ++ u2s_setup a op buf|> /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\ ~s.vs_halted /\
  (!bb. MEM bb (u2s_blocks a op buf n) ==>
        lookup_block bb.bb_label fn.fn_blocks = SOME bb) /\
  eval_operand op s = SOME (n2w X) /\
  u2s_safe ctx func cenv cx es a buf b sz inst s0 s /\
  local_ptrs_reserved cenv a /\ (?p. buf = Var p /\ not_fresh_at a p) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  X < dimword (:256) /\ 78 <= n /\ n+32 <= sz /\ b+sz < dimword (:256) ==>
  ?t. gas_marked_path F ctx fn s 0 (OK t) /\
      u2s_safe ctx func cenv cx es a buf b sz inst s0 t /\
      eval_operand (Var (u2s_var a 2)) t = SOME (n2w (b+n-LENGTH (num_to_dec_string X))) /\
      val_in_memory ty (StringV (num_to_dec_string X))
        (b+n-LENGTH (num_to_dec_string X)) t.vs_memory /\
      b <= b+n-LENGTH (num_to_dec_string X) /\
      b+n-LENGTH (num_to_dec_string X)+32+LENGTH (num_to_dec_string X) <= b+sz /\
      t.vs_current_bb = u2s_label a 5 /\ t.vs_inst_idx = 0 /\ ~t.vs_halted
Proof
  cheat
QED

Theorem u2s_alloc_path[local]:
  !sz sa ba a fn s bb tail t ctx.
  compile_alloc_buffer sz sa = (ba,a) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = a.cs_current_insts ++ tail /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  run_inst_seq (emitted_insts sa a) s = OK t ==>
  gas_marked_path F ctx fn s 0
    (OK (t with vs_inst_idx := LENGTH a.cs_current_insts))
Proof
  cheat
QED

Theorem u2s_alloc_ready_path:
  compile_alloc_buffer sz sa = (ba,a) /\
  u2s_layout a op ba.buf_operand n sb /\
  fn_has_code sa sb func /\ fn_has_code sa sb fn /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  (!z. op = Var z ==> not_fresh_at sa z) /\ (!l. op <> Label l) /\
  eval_operand op s = SOME (n2w X) /\ sz < dimword (:256) ==>
  ?b s0 ready inst.
    u2s_safe ctx func cenv cx es a ba.buf_operand b sz inst s0 ready /\
    ready.vs_current_bb = a.cs_current_bb /\
    ready.vs_inst_idx = LENGTH a.cs_current_insts /\ ~ready.vs_halted /\
    eval_operand op ready = SOME (n2w X) /\ local_ptrs_reserved cenv a /\
    (?p. ba.buf_operand = Var p /\ not_fresh_at a p) /\
    lookup_block a.cs_current_bb fn.fn_blocks = SOME
      <|bb_label := a.cs_current_bb;
        bb_instructions := a.cs_current_insts ++ u2s_setup a op ba.buf_operand|> /\
    (!bb. MEM bb (u2s_blocks a op ba.buf_operand n) ==>
      lookup_block bb.bb_label fn.fn_blocks = SOME bb) /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ b+sz < dimword (:256) /\
    (!fuel. run_from fuel ctx fn s = run_from fuel ctx fn ready) /\
    gas_marked_path F ctx fn s 0 (OK ready) /\
    (!out. u2s_safe ctx func cenv cx es a ba.buf_operand b sz inst s0 out ==>
      stmt_state_rel ctx func cenv cx es out /\ wb_frame cenv es sa s out /\
      FLOOKUP out.vs_allocas sa.cs_next_id = SOME (b,sz))
Proof
  cheat
QED

Theorem u2s_alloc_ready:
  compile_alloc_buffer sz sa = (ba,a) /\
  u2s_layout a op ba.buf_operand n sb /\
  fn_has_code sa sb func /\ fn_has_code sa sb fn /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  (!z. op = Var z ==> not_fresh_at sa z) /\ (!l. op <> Label l) /\
  eval_operand op s = SOME (n2w X) /\ sz < dimword (:256) ==>
  ?b s0 ready inst.
    u2s_safe ctx func cenv cx es a ba.buf_operand b sz inst s0 ready /\
    ready.vs_current_bb = a.cs_current_bb /\
    ready.vs_inst_idx = LENGTH a.cs_current_insts /\ ~ready.vs_halted /\
    eval_operand op ready = SOME (n2w X) /\ local_ptrs_reserved cenv a /\
    (?p. ba.buf_operand = Var p /\ not_fresh_at a p) /\
    lookup_block a.cs_current_bb fn.fn_blocks = SOME
      <|bb_label := a.cs_current_bb;
        bb_instructions := a.cs_current_insts ++ u2s_setup a op ba.buf_operand|> /\
    (!bb. MEM bb (u2s_blocks a op ba.buf_operand n) ==>
      lookup_block bb.bb_label fn.fn_blocks = SOME bb) /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ b+sz < dimword (:256) /\
    (!fuel. run_from fuel ctx fn s = run_from fuel ctx fn ready) /\
    (!out. u2s_safe ctx func cenv cx es a ba.buf_operand b sz inst s0 out ==>
      stmt_state_rel ctx func cenv cx es out /\ wb_frame cenv es sa s out /\
      FLOOKUP out.vs_allocas sa.cs_next_id = SOME (b,sz))
Proof
  cheat
QED

Theorem u2s_alloc_vv_path:
  post_value_type cenv e = expr_type e /\
  compile_uint2str op n sz sa = (out,sb) /\
  fn_has_code sa sb func /\ fn_has_code sa sb fn /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  (!z. op = Var z ==> not_fresh_at sa z) /\ (!l. op <> Label l) /\
  eval_operand op s = SOME (n2w X) /\
  X < dimword (:256) /\ 78 <= n /\ n+32 <= sz /\ sz + n < dimword (:256) /\
  ~is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  val_wf tv (StringV (num_to_dec_string X)) /\
  val_footprint tv (StringV (num_to_dec_string X)) <= 32+LENGTH (num_to_dec_string X) ==>
  ?t. gas_marked_path F ctx fn s 0 (OK t) /\
      vv_post ctx func cenv cx e es sa sb s es (Value (StringV (num_to_dec_string X)))
        (LocatedValue (expr_type e) <|ptr_operand := out; ptr_location := LocMemory|>) t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ~t.vs_halted
Proof
  cheat
QED

Theorem u2s_alloc_vv_exit:
  post_value_type cenv e = expr_type e /\
  compile_uint2str op n sz sa = (out,sb) /\
  fn_has_code sa sb func /\ fn_has_code sa sb fn /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  (!z. op = Var z ==> not_fresh_at sa z) /\ (!l. op <> Label l) /\
  eval_operand op s = SOME (n2w X) /\
  X < dimword (:256) /\ 78 <= n /\ n+32 <= sz /\ sz + n < dimword (:256) /\
  ~is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  val_wf tv (StringV (num_to_dec_string X)) /\
  val_footprint tv (StringV (num_to_dec_string X)) <= 32+LENGTH (num_to_dec_string X) ==>
  ?t. vv_post ctx func cenv cx e es sa sb s es (Value (StringV (num_to_dec_string X)))
        (LocatedValue (expr_type e) <|ptr_operand := out; ptr_location := LocMemory|>) t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ~t.vs_halted /\
      (!fuel r. run_from fuel ctx fn t = r /\ (!err. r <> Error err) ==>
                ?fuel'. run_from fuel' ctx fn s = r)
Proof
  cheat
QED

Theorem u2s_alloc_vv_frag:
  post_value_type cenv e = expr_type e /\
  compile_uint2str op n sz sa = (out,sb) /\ fn_has_code sa sb func /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  (!z. op = Var z ==> not_fresh_at sa z) /\ (!l. op <> Label l) /\
  eval_operand op s = SOME (n2w X) /\
  X < dimword (:256) /\ 78 <= n /\ n+32 <= sz /\ sz + n < dimword (:256) /\
  ~is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  val_wf tv (StringV (num_to_dec_string X)) /\
  val_footprint tv (StringV (num_to_dec_string X)) <= 32+LENGTH (num_to_dec_string X) ==>
  frag_exec ctx sa sb (\t. t = s)
    (\t. vv_post ctx func cenv cx e es sa sb s es (Value (StringV (num_to_dec_string X)))
        (LocatedValue (expr_type e) <|ptr_operand := out; ptr_location := LocMemory|>) t) R
Proof
  cheat
QED

Theorem compile_uint2str_singleton:
  compile_expr cenv ty (Builtin ann (Uint2Str n) [e]) sa =
    (let (v,sm) = lower_value compile_expr cenv ty e sa in
     as_ptr_val ann LocMemory (compile_uint2str v n (type_memory_bytes cenv ann) sm))
Proof
  cheat
QED

Theorem uint2str_suffix_appends:
  cs_appends (compile_uint2str op n sz)
Proof
  cheat
QED

Theorem uint2str_source_result:
  builtin_result cx acc ann (Uint2Str n) ts [IntV i] =
    INL (StringV (num_to_dec_string (Num i)))
Proof
  cheat
QED

(* The suffix is an actual counted target path from every operand endpoint,
   whose source reads may run under any replacement of the gas observations. *)
Theorem compile_typed_unary_builtin_vv_sim_with_initial_rel:
  expr_body_pre cenv cx env (Builtin ann bt [e]) es /\
  expr_sim ctx func cenv cx ty e es /\ expr_type e = BaseT bty /\
  ~precompile_builtin bt /\ bt <> Len /\ builtin_args_length_ok bt 1 /\
  (!sa sb vv. compile_expr cenv ty (Builtin ann bt [e]) sa = (vv,sb) ==>
    ?x sm. lower_value compile_expr cenv ty e sa = (x,sm) /\
      code x sm = (vv,sb)) /\
  (!x. cs_appends (code x)) /\
  (!sa sm sb x vv s0 v gs es' s.
    lower_value compile_expr cenv ty e sa = (x,sm) /\
    code x sm = (vv,sb) /\ fn_has_code sm sb func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    local_ptrs_reserved cenv sm /\
    bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
      (INL v,es') /\
    value_has_type (BaseTV bty) v /\ expr_sim_inv cenv cx env es' /\
    expr_res_ok (builtin_result cx es'.accounts ann bt [expr_type e] [v]) /\
    stmt_state_rel ctx func cenv cx es s0 /\
    expr_post ctx func cenv cx e es sa sm s0 es' v x s /\ ~s.vs_halted /\
    s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?n r. gas_marked_path F ctx func s n r /\
      ((?t rv. r = OK t /\
          builtin_result cx es'.accounts ann bt [expr_type e] [v] = INL rv /\
          vv_post ctx func cenv cx (Builtin ann bt [e]) es sa sb s0 es'
            (Value rv) vv t /\
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts) \/
       (exit_result r /\
        expr_exit (builtin_result cx es'.accounts ann bt [expr_type e] [v]) r))) ==>
  expr_vv_sim ctx func cenv cx ty (Builtin ann bt [e]) es
Proof
  cheat
QED

Theorem vv_post_prefix_frag:
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  wb_frame cenv es sa s0 t /\
  frag_exec ctx sm sb P
    (\u. vv_post ctx func cenv cx e es1 sm sb t es2 tv vv u) R ==>
  frag_exec ctx sm sb P
    (\u. vv_post ctx func cenv cx e es sa sb s0 es2 tv vv u) R
Proof
  cheat
QED

Theorem uint2str_result_memory_bounds:
  X < dimword (:256) /\ 78 <= n ==>
  val_wf (BaseTV (StringT n)) (StringV (num_to_dec_string X)) /\
  val_footprint (BaseTV (StringT n)) (StringV (num_to_dec_string X)) =
    32 + LENGTH (num_to_dec_string X) /\ n + 32 <= 32 + 32 * word_size n
Proof
  cheat
QED

Theorem vv_post_located_mk_ptr:
  vv_post ctx func cenv cx e es sa sb s0 es' tv (LocatedValue ty p) s <=>
  vv_post ctx func cenv cx e es sa sb s0 es' tv
    (LocatedValue ty (mk_ptr p.ptr_operand p.ptr_location)) s
Proof
  cheat
QED

Theorem uint2str_numeric_suffix:
  expr_body_pre cenv cx env e es /\ expr_type e = BaseT (UintT k) /\
  lower_value compile_expr cenv ty e sa = (x,sm) /\
  compile_uint2str x n sz sm = (out,sb) /\ fn_has_code sm sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  local_ptrs_reserved cenv sm /\ stmt_state_rel ctx func cenv cx es s0 /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  expr_post ctx func cenv cx e es sa sm s0 es' (IntV (&X)) x s /\
  X < dimword (:256) /\ 78 <= n /\ n+32 <= sz /\ sz + n < dimword (:256) ==>
  frag_exec ctx sm sb (\t. t = s)
    (\t. vv_post ctx func cenv cx (Builtin (BaseT (StringT n)) (Uint2Str n) [e])
      es sa sb s0 es' (Value (StringV (num_to_dec_string X)))
      (LocatedValue (BaseT (StringT n)) (mk_ptr out LocMemory)) t) R
Proof
  cheat
QED

Theorem uint2str_typed_suffix:
  expr_body_pre cenv cx env (Builtin (BaseT (StringT n)) (Uint2Str n) [e]) es /\
  expr_type e = BaseT (UintT k) /\ 78 <= n /\
  lower_value compile_expr cenv ty e sa = (x,sm) /\
  as_ptr_val (BaseT (StringT n)) LocMemory
    (compile_uint2str x n (type_memory_bytes cenv (BaseT (StringT n))) sm) = (vv,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  stmt_state_rel ctx func cenv cx es s0 /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,es') /\
  value_has_type (BaseTV (UintT k)) v /\
  expr_post ctx func cenv cx e es sa sm s0 es' v x s ==>
  frag_exec ctx sm sb (\t. t = s)
    (\t. ?r. builtin_result cx es'.accounts (BaseT (StringT n)) (Uint2Str n) [expr_type e] [v] = INL r /\
      vv_post ctx func cenv cx (Builtin (BaseT (StringT n)) (Uint2Str n) [e])
        es sa sb s0 es' (Value r) vv t)
    (expr_exit (builtin_result cx es'.accounts (BaseT (StringT n)) (Uint2Str n) [expr_type e] [v]))
Proof
  cheat
QED

Theorem uint2str_numeric_path:
  expr_body_pre cenv cx env e es /\ expr_type e = BaseT (UintT k) /\
  lower_value compile_expr cenv ty e sa = (x,sm) /\
  compile_uint2str x n sz sm = (out,sb) /\ fn_has_code sm sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  local_ptrs_reserved cenv sm /\ stmt_state_rel ctx func cenv cx es s0 /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  expr_post ctx func cenv cx e es sa sm s0 es' (IntV (&X)) x s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  X < dimword (:256) /\ 78 <= n /\ n+32 <= sz /\ sz + n < dimword (:256) ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      vv_post ctx func cenv cx (Builtin (BaseT (StringT n)) (Uint2Str n) [e])
        es sa sb s0 es' (Value (StringV (num_to_dec_string X)))
        (LocatedValue (BaseT (StringT n)) (mk_ptr out LocMemory)) t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  cheat
QED

Theorem uint2str_typed_path:
  expr_body_pre cenv cx env (Builtin (BaseT (StringT n)) (Uint2Str n) [e]) es /\
  expr_type e = BaseT (UintT k) /\ 78 <= n /\
  lower_value compile_expr cenv ty e sa = (x,sm) /\
  as_ptr_val (BaseT (StringT n)) LocMemory
    (compile_uint2str x n (type_memory_bytes cenv (BaseT (StringT n))) sm) = (vv,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  stmt_state_rel ctx func cenv cx es s0 /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,es') /\
  value_has_type (BaseTV (UintT k)) v /\
  expr_post ctx func cenv cx e es sa sm s0 es' v x s /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?m r. gas_marked_path F ctx func s m r /\
    ((?t rv. r = OK t /\
        builtin_result cx es'.accounts (BaseT (StringT n)) (Uint2Str n)
          [expr_type e] [v] = INL rv /\
        vv_post ctx func cenv cx (Builtin (BaseT (StringT n)) (Uint2Str n) [e])
          es sa sb s0 es' (Value rv) vv t /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts) \/
     (exit_result r /\
      expr_exit (builtin_result cx es'.accounts (BaseT (StringT n)) (Uint2Str n)
        [expr_type e] [v]) r))
Proof
  cheat
QED

Theorem compile_uint2str_typed_vv_sim:
  expr_body_pre cenv cx env (Builtin ann (Uint2Str n) [e]) es /\
  expr_sim ctx func cenv cx ty e es ==>
  expr_vv_sim ctx func cenv cx ty (Builtin ann (Uint2Str n) [e]) es
Proof
  cheat
QED

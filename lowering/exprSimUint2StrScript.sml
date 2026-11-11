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
  simp[num_to_dec_string_def, n2s_def, Once n2l_def] >>
  Cases_on `x < 10` >> simp[HEX, ADD_COMM]
QED

Theorem decimal_string_length_bound:
  x < 10 ** k /\ 0 < k ==> LENGTH (num_to_dec_string x) <= k
Proof
  strip_tac >> Cases_on `x = 0` >> simp[LENGTH_num_to_dec_string] >>
  `LOG 10 x < k` suffices_by simp[] >>
  spose_not_then assume_tac >>
  `10 ** k <= 10 ** LOG 10 x` by
    (irule EXP_BASE_LEQ_MONO_IMP >> simp[]) >>
  `10 ** LOG 10 x <= x` by
    (qspec_then `10` (qspec_then `x` mp_tac) LOG >> simp[]) >>
  decide_tac
QED

Theorem uint256_decimal_length:
  x < 2 ** 256 ==>
  1 <= LENGTH (num_to_dec_string x) /\
  LENGTH (num_to_dec_string x) <= 78
Proof
  strip_tac >> conj_tac
  >- (Cases_on `num_to_dec_string x` >> gvs[]) >>
  irule decimal_string_length_bound >>
  `x < 10 ** 78` by
    (`2 ** 256 < 10 ** 78` by EVAL_TAC >> decide_tac) >>
  simp[]
QED

Theorem uint2str_builtin_types:
  well_typed_builtin_app ty (Uint2Str n) ts ==>
  ?k. ts = [BaseT (UintT k)] /\ ty = BaseT (StringT n) /\ 78 <= n
Proof
  simp[well_typed_builtin_app_def] >>
  Cases_on `ts` >> simp[] >>
  rename1 `LENGTH rest = 0` >> Cases_on `rest` >> simp[] >>
  metis_tac[]
QED

Theorem uint2str_body_capacity:
  expr_body_pre cenv cx env (Builtin (BaseT (StringT m)) (Uint2Str n) args) es ==>
  type_memory_bytes cenv (BaseT (StringT m)) < 2 ** 64
Proof
  simp[expr_body_pre_def, alloc_limits_expr_def, type_alloc_ok_def,
       is_word_type_def]
QED

Theorem uint2str_expr_types:
  well_typed_expr env (Builtin ann (Uint2Str n) args) ==>
  ?e k. args = [e] /\ ann = BaseT (StringT n) /\
        expr_type e = BaseT (UintT k) /\ 78 <= n
Proof
  simp[well_typed_expr_def] >> strip_tac >>
  drule uint2str_builtin_types >> strip_tac >>
  Cases_on `args` >> gvs[] >>
  metis_tac[]
QED

Theorem mstore_string_header:
  mem_bytes_at (p + 32) (LENGTH str) s.vs_memory = MAP (n2w o ORD) str ==>
  val_in_memory ty (StringV str) p
    (mstore p (n2w (LENGTH str)) s).vs_memory
Proof
  strip_tac >> simp[valueEncodingTheory.val_in_memory_def,
    mstore_mem_word_at_same, mstore_mem_bytes_at_disjoint]
QED

Theorem uint2str_dimindex_256[local,simp]:
  dimindex (:256) = 256
Proof
  CONV_TAC fcpLib.INDEX_CONV
QED

Theorem mstore_last_byte:
  mem_bytes_at (a + 31) 1 (mstore a (w:bytes32) s).vs_memory = [w2w w]
Proof
  `dimword (:256) = 2 ** 256` by simp[dimword_def] >>
  irule LIST_EQ >> simp[valueEncodingPropsTheory.LENGTH_mem_bytes_at] >>
  rewrite_tac[GSYM EL] >>
  qspecl_then [`a`, `w`, `s`] mp_tac mem_bytes_at_mstore_same >>
  disch_then (mp_tac o AP_TERM ``EL 31 : word8 list -> word8``) >>
  simp[EL_mem_bytes_at, word_to_bytes_def, word_to_bytes_be_def,
       EL_word_to_bytes_aux, get_byte_def, byte_index_def,
       (* explicit dimension fact above avoids ambient simpset reliance *)
       MOD_LESS, SHIFT_ZERO]
QED

Theorem mstore_prepend_byte:
  mem_bytes_at (a + 32) (LENGTH bs) s.vs_memory = bs ==>
  mem_bytes_at (a + 31) (SUC (LENGTH bs))
    (mstore a (w:bytes32) s).vs_memory = w2w w :: bs
Proof
  strip_tac >>
  `SUC (LENGTH bs) = 1 + LENGTH bs` by decide_tac >>
  asm_rewrite_tac[] >>
  rewrite_tac[mem_bytes_at_split_padded, mstore_last_byte] >>
  `a + 31 + 1 = a + 32` by decide_tac >>
  `mem_bytes_at (a + 32) (LENGTH bs) (mstore a w s).vs_memory =
   mem_bytes_at (a + 32) (LENGTH bs) s.vs_memory` by
    (irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
  asm_rewrite_tac[APPEND]
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
  simp[u2s_setup_def, u2s_check_def, u2s_cond_def,
       u2s_body_def, u2s_zero_def, u2s_final_def]
QED

Theorem u2s_var_injective[simp]:
  u2s_var a j = u2s_var a k <=> j = k
Proof
  simp[u2s_var_def, fresh_var_def, toString_11]
QED

Theorem u2s_var_fresh:
  not_fresh_at a z ==> z <> u2s_var a k
Proof
  simp[not_fresh_at_def, u2s_var_def, fresh_var_def] >>
  strip_tac >> first_x_assum (qspec_then `a.cs_next_var + k` mp_tac) >> simp[]
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
  simp[u2s_setup_def, u2s_inst_def, u2s_var_def, u2s_label_def,
       fresh_var_def, fresh_label_def, emit_inst_def, fresh_id_def,
       emit_def, comp_bind_def, comp_ignore_bind_def, ADD_ASSOC,
       APPEND_ASSOC] >>
  rewrite_tac[GSYM APPEND_ASSOC, APPEND]
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
  strip_tac >>
  simp[u2s_check_def, u2s_inst_def, u2s_var_def, fresh_var_def,
       emit_op_def, emit_inst_def, fresh_id_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       ADD_ASSOC, APPEND_ASSOC] >>
  rewrite_tac[GSYM APPEND_ASSOC, APPEND]
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
  strip_tac >>
  simp[u2s_cond_def, u2s_inst_def, u2s_var_def, fresh_var_def,
       emit_op_def, emit_inst_def, fresh_id_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       ADD_ASSOC, APPEND_ASSOC] >>
  rewrite_tac[GSYM APPEND_ASSOC, APPEND]
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
  strip_tac >>
  simp[u2s_body_def, u2s_inst_def, u2s_var_def, fresh_var_def,
       emit_op_def, emit_void_def, emit_inst_def, fresh_id_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       ADD_ASSOC, APPEND_ASSOC] >>
  rewrite_tac[GSYM APPEND_ASSOC, APPEND]
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
  strip_tac >>
  simp[u2s_zero_def, u2s_inst_def, u2s_var_def, fresh_var_def,
       emit_op_def, emit_void_def, emit_inst_def, fresh_id_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       ADD_ASSOC, APPEND_ASSOC] >>
  rewrite_tac[GSYM APPEND_ASSOC, APPEND]
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
  strip_tac >>
  simp[u2s_final_def, u2s_inst_def, u2s_var_def, fresh_var_def,
       emit_op_def, emit_void_def, emit_inst_def, fresh_id_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       ADD_ASSOC, APPEND_ASSOC] >>
  rewrite_tac[GSYM APPEND_ASSOC, APPEND]
QED

Theorem u2s_new_block_cont[local]:
  (do new_block lbl; kont od) s =
  kont (s with <|cs_blocks :=
    <|bb_label := s.cs_current_bb; bb_instructions := s.cs_current_insts|> :: s.cs_blocks;
    cs_current_bb := lbl; cs_current_insts := []|>)
Proof
  simp[comp_ignore_bind_def, comp_bind_def, new_block_def]
QED

Theorem compile_uint2str_layout_eq:
  compile_alloc_buffer (sz + n) sa = (ba,a) ==>
  compile_uint2str op n sz sa =
    (Var (u2s_var a 2), u2s_end a op ba.buf_operand n)
Proof
  strip_tac >>
  once_rewrite_tac[compile_uint2str_def] >>
  simp[Once comp_bind_def] >> asm_rewrite_tac[] >>
  simp[Once comp_bind_def, comp_return_def] >>
  CONV_TAC (LAND_CONV (HO_REWR_CONV u2s_setup_cont)) >>
  rewrite_tac[u2s_new_block_cont] >> simp[] >>
  dep_rewrite.DEP_ONCE_REWRITE_TAC [u2s_check_cont] >> simp[] >>
  rewrite_tac[u2s_new_block_cont] >> simp[] >>
  dep_rewrite.DEP_ONCE_REWRITE_TAC [u2s_cond_cont] >> simp[] >>
  rewrite_tac[u2s_new_block_cont] >> simp[] >>
  dep_rewrite.DEP_ONCE_REWRITE_TAC [u2s_body_cont] >> simp[] >>
  rewrite_tac[u2s_new_block_cont] >> simp[] >>
  dep_rewrite.DEP_ONCE_REWRITE_TAC [u2s_zero_cont] >> simp[] >>
  rewrite_tac[u2s_new_block_cont] >> simp[] >>
  dep_rewrite.DEP_ONCE_REWRITE_TAC [u2s_final_cont] >> simp[] >>
  simp[u2s_new_block_cont, comp_return_def, u2s_end_def, u2s_blocks_def]
QED

Theorem compile_uint2str_layout:
  compile_uint2str op n sz sa = (out,sb) ==>
  ?ba a. compile_alloc_buffer (sz + n) sa = (ba,a) /\
         out = Var (u2s_var a 2) /\ u2s_layout a op ba.buf_operand n sb
Proof
  Cases_on `compile_alloc_buffer (sz + n) sa` >>
  drule compile_uint2str_layout_eq >> simp[u2s_layout_def] >>
  metis_tac[]
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
  simp[u2s_frame_def]
QED

Theorem u2s_frame_jump:
  u2s_frame a b sz s0 s ==> u2s_frame a b sz s0 (jump_to lbl s)
Proof
  strip_tac >> gvs[u2s_frame_def, venomStateTheory.jump_to_def,
       venomStateTheory.lookup_var_def] >> metis_tac[]
QED

Theorem u2s_frame_index:
  u2s_frame a b sz s0 s ==>
  u2s_frame a b sz s0 (s with vs_inst_idx := idx)
Proof
  strip_tac >> gvs[u2s_frame_def, venomStateTheory.lookup_var_def] >> metis_tac[]
QED

Theorem u2s_frame_update:
  u2s_frame a b sz s0 s ==>
  u2s_frame a b sz s0 (update_var (u2s_var a k) w s)
Proof
  simp[u2s_frame_def, venomStateTheory.update_var_def,
       venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  metis_tac[u2s_var_fresh]
QED

Theorem u2s_frame_mstore:
  u2s_frame a b sz s0 s /\ b <= p /\ p + 32 <= b + sz ==>
  u2s_frame a b sz s0 (mstore p w s)
Proof
  strip_tac >>
  `LENGTH s0.vs_memory <= LENGTH (mstore p w s).vs_memory` by
    (gvs[u2s_frame_def, immutable_mstore_capacity, MAX_DEF] >>
     IF_CASES_TAC >> decide_tac) >>
  gvs[u2s_frame_def, venomStateTheory.mstore_def,
      venomStateTheory.lookup_var_def] >>
  rpt strip_tac >>
  `mem_bytes_at off len (mstore p w s).vs_memory =
   mem_bytes_at off len s.vs_memory` by
    (irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
  gvs[venomStateTheory.mstore_def] >> metis_tac[]
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
  simp[u2s_safe_def, u2s_frame_refl] >> metis_tac[]
QED

Theorem u2s_safe_mstore:
  u2s_safe ctx fn cenv cx es a buf b sz inst s0 s /\
  (?p. buf = Var p) /\ b <= at /\ at + 32 <= b + sz /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA ==>
  u2s_safe ctx fn cenv cx es a buf b sz inst s0 (mstore at w s)
Proof
  strip_tac >>
  `u2s_frame a b sz s0 (mstore at w s)` by
    (irule u2s_frame_mstore >> gvs[u2s_safe_def]) >>
  `stmt_state_rel ctx fn cenv cx es (mstore at w s)` by
    (irule literal_mstore_state_rel >>
     gvs[u2s_safe_def] >> metis_tac[]) >>
  gvs[u2s_safe_def, venomStateTheory.eval_operand_def, venomStateTheory.mstore_def,
      venomStateTheory.lookup_var_def, compileEnvTheory.local_region_def] >>
  metis_tac[]
QED

Theorem u2s_var_not_local:
  local_ptrs_reserved cenv a ==>
  not_local_ptr cenv scopes (u2s_var a k)
Proof
  strip_tac >> simp[u2s_var_def, fresh_var_def] >>
  irule exprLoweringPropsTheory.local_ptrs_reserved_fresh >>
  qexists_tac `a` >> simp[]
QED

Theorem u2s_safe_update:
  u2s_safe ctx fn cenv cx es a buf b sz inst s0 s /\
  local_ptrs_reserved cenv a /\
  (?p. buf = Var p /\ not_fresh_at a p) ==>
  u2s_safe ctx fn cenv cx es a buf b sz inst s0
    (update_var (u2s_var a k) w s)
Proof
  strip_tac >>
  `not_local_ptr cenv es.scopes (u2s_var a k)` by
    (irule u2s_var_not_local >> simp[]) >>
  `stmt_state_rel ctx fn cenv cx es (update_var (u2s_var a k) w s)` by
    (irule exprLoweringPropsTheory.stmt_state_rel_update_var >>
     gvs[u2s_safe_def]) >>
  `u2s_frame a b sz s0 (update_var (u2s_var a k) w s)` by
    (irule u2s_frame_update >> gvs[u2s_safe_def]) >>
  gvs[u2s_safe_def, venomStateTheory.update_var_def,
      venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
      compileEnvTheory.local_region_def, compileEnvTheory.not_local_ptr_def,
      finite_mapTheory.FLOOKUP_UPDATE] >>
  metis_tac[u2s_var_fresh]
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
  strip_tac >>
  `s.vs_allocas = s0.vs_allocas` by
    fs[u2s_frame_def, venomStateTheory.venom_state_component_equality] >>
  `!name lb lsz. local_region cenv es.scopes spre name lb lsz ==>
     local_region cenv es.scopes s0 name lb lsz` by
    (rpt strip_tac >> irule local_region_frame_fwd >>
     qexistsl [`spre`, `sa`, `es.scopes`] >>
     simp[] >> metis_tac[wb_frame_vars]) >>
  `locals_kept cenv es spre s` by
    (irule exprSimPropsTheory.locals_kept_regions_tail >> qexists `s0` >>
     reverse conj_tac >- fs[wb_frame_def] >>
     rpt strip_tac >> fs[u2s_frame_def] >> metis_tac[ADD_COMM]) >>
  simp[wb_frame_def] >> conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at a x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
      fs[u2s_frame_def] >> metis_tac[wb_frame_vars]) >>
  conj_tac >- (fs[wb_frame_def] >> metis_tac[]) >>
  rpt strip_tac >> fs[wb_frame_def, u2s_frame_def] >>
  metis_tac[]
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
  simp[u2s_digits_def, valueEncodingTheory.mem_bytes_at_def]
QED

Theorem u2s_step_assign:
  eval_operand op s = SOME w ==>
  step_inst_base (mk_inst id ASSIGN [op] [out]) s = OK (update_var out w s)
Proof
  strip_tac >> simp[step_inst_base_def, venomInstTheory.mk_inst_def]
QED

Theorem u2s_setup_run:
  eval_operand op s = SOME w /\ eval_operand buf s = SOME p /\
  (!z. buf = Var z ==> not_fresh_at a z) ==>
  run_inst_seq (TAKE 3 (u2s_setup a op buf)) s =
    OK (update_var (u2s_var a 2) p
         (update_var (u2s_var a 1) 0w (update_var (u2s_var a 0) w s)))
Proof
  strip_tac >>
  `eval_operand buf (update_var (u2s_var a 1) 0w
     (update_var (u2s_var a 0) w s)) = SOME p` by
    (irule emitHelperPropsTheory.eval_operand_update_var_mstore >> conj_tac
     >- metis_tac[u2s_var_fresh] >>
     irule emitHelperPropsTheory.eval_operand_update_var_mstore >> simp[] >>
     metis_tac[u2s_var_fresh]) >>
  `step_inst_base (u2s_inst a 0 ASSIGN [op] [u2s_var a 0]) s =
      OK (update_var (u2s_var a 0) w s)` by
    (simp[u2s_inst_def] >> irule u2s_step_assign >> simp[]) >>
  `step_inst_base (u2s_inst a 1 ASSIGN [Lit 0w] [u2s_var a 1])
      (update_var (u2s_var a 0) w s) =
      OK (update_var (u2s_var a 1) 0w (update_var (u2s_var a 0) w s))` by
    (simp[u2s_inst_def] >> irule u2s_step_assign >>
     simp[emitHelperPropsTheory.eval_operand_lit]) >>
  `step_inst_base (u2s_inst a 2 ASSIGN [buf] [u2s_var a 2])
      (update_var (u2s_var a 1) 0w (update_var (u2s_var a 0) w s)) =
      OK (update_var (u2s_var a 2) p
        (update_var (u2s_var a 1) 0w (update_var (u2s_var a 0) w s)))` by
    (simp[u2s_inst_def] >> irule u2s_step_assign >> simp[]) >>
  simp[u2s_setup_def, exprLoweringPropsTheory.run_inst_seq_def]
QED

Theorem u2s_setup_safe:
  u2s_safe ctx fn cenv cx es a buf b sz inst s0 s /\
  local_ptrs_reserved cenv a /\
  (?p. buf = Var p /\ not_fresh_at a p) ==>
  u2s_safe ctx fn cenv cx es a buf b sz inst s0
    (update_var (u2s_var a 2) v
      (update_var (u2s_var a 1) 0w (update_var (u2s_var a 0) w s)))
Proof
  strip_tac >> irule u2s_safe_update >> simp[] >>
  irule u2s_safe_update >> simp[] >>
  irule u2s_safe_update >> gvs[]
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
  simp[venomStateTheory.update_var_def, venomStateTheory.lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE, u2s_var_injective]
QED

Theorem u2s_safe_jump:
  u2s_safe ctx fn cenv cx es a buf b sz inst s0 s ==>
  u2s_safe ctx fn cenv cx es a buf b sz inst s0 (jump_to lbl s)
Proof
  simp[u2s_safe_def, u2s_frame_jump,
       exprLoweringPropsTheory.stmt_state_rel_jump_to,
       venomStateTheory.jump_to_def, venomStateTheory.eval_operand_def,
       venomStateTheory.lookup_var_def, compileEnvTheory.local_region_def] >>
  metis_tac[]
QED

Theorem u2s_digits_jump:
  u2s_digits a b n X x str (jump_to lbl s) <=> u2s_digits a b n X x str s
Proof
  simp[u2s_digits_def, venomStateTheory.jump_to_def, venomStateTheory.lookup_var_def]
QED

Theorem u2s_digits_update:
  k <> 0 /\ k <> 1 ==>
  (u2s_digits a b n X x str (update_var (u2s_var a k) w s) <=>
   u2s_digits a b n X x str s)
Proof
  simp[u2s_digits_def, venomStateTheory.update_var_def,
       venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem u2s_eq_run:
  lookup_var (u2s_var a 0) s = SOME (n2w x) /\ x < dimword (:256) ==>
  run_inst_seq [u2s_inst a id EQ [Var (u2s_var a 0); Lit 0w] [u2s_var a k]] s =
    OK (update_var (u2s_var a k) (bool_to_word (x = 0)) s)
Proof
  strip_tac >>
  simp[u2s_inst_def, venomInstTheory.mk_inst_def] >>
  simp[exprLoweringPropsTheory.run_inst_seq_def, step_inst_base_def,
       exec_pure2_def, venomStateTheory.eval_operand_def, n2w_11]
QED

Theorem u2s_jnz_step:
  lookup_var (u2s_var a k) s = SOME w ==>
  step_inst_base (u2s_inst a id JNZ
    [Var (u2s_var a k); Label yes; Label no] []) s =
    OK (jump_to (if w = 0w then no else yes) s)
Proof
  strip_tac >>
  simp_tac (srw_ss()) [u2s_inst_def, venomInstTheory.mk_inst_def] >>
  simp_tac (srw_ss()) [step_inst_base_def] >>
  Cases_on `w = 0w` >> gvs[venomStateTheory.eval_operand_def]
QED

Theorem u2s_check_run:
  lookup_var (u2s_var a 0) s = SOME (n2w x) /\ x < dimword (:256) /\
  t = update_var (u2s_var a 3) (bool_to_word (x = 0)) s ==>
  run_inst_seq (TAKE 1 (u2s_check a)) s = OK t /\
  step_inst_base (LAST (u2s_check a)) t =
    OK (jump_to (u2s_label a (if x = 0 then 3 else 1)) t)
Proof
  strip_tac >> conj_tac
  >- (gvs[u2s_check_def] >> irule u2s_eq_run >> simp[]) >>
  `lookup_var (u2s_var a 3) t = SOME (bool_to_word (x = 0))` by
    gvs[venomStateTheory.update_var_def, venomStateTheory.lookup_var_def,
        finite_mapTheory.FLOOKUP_UPDATE] >>
  qpat_x_assum `t = _` kall_tac >>
  Cases_on `x = 0` >> gvs[u2s_check_def] >>
  drule u2s_jnz_step >> simp[] >> metis_tac[]
QED

Theorem u2s_cond_run:
  lookup_var (u2s_var a 0) s = SOME (n2w x) /\ x < dimword (:256) /\
  t = update_var (u2s_var a 4) (bool_to_word (x = 0)) s ==>
  run_inst_seq (TAKE 1 (u2s_cond a)) s = OK t /\
  step_inst_base (LAST (u2s_cond a)) t =
    OK (jump_to (u2s_label a (if x = 0 then 4 else 2)) t)
Proof
  strip_tac >> conj_tac
  >- (gvs[u2s_cond_def] >> irule u2s_eq_run >> simp[]) >>
  `lookup_var (u2s_var a 4) t = SOME (bool_to_word (x = 0))` by
    gvs[venomStateTheory.update_var_def, venomStateTheory.lookup_var_def,
        finite_mapTheory.FLOOKUP_UPDATE] >>
  qpat_x_assum `t = _` kall_tac >>
  Cases_on `x = 0` >> gvs[u2s_cond_def] >>
  drule u2s_jnz_step >> simp[] >> metis_tac[]
QED

Theorem decimal_string_quotient_step:
  num_to_dec_string x =
    (if x DIV 10 = 0 then [] else num_to_dec_string (x DIV 10)) ++
    [CHR (48 + x MOD 10)]
Proof
  Cases_on `x < 10`
  >- (`x DIV 10 = 0` by simp[DIV_EQ_0] >>
      simp[Once decimal_string_step]) >>
  `x DIV 10 <> 0` by simp[DIV_EQ_0] >>
  simp[Once decimal_string_step]
QED

Theorem decimal_suffix_step:
  0 < x /\ num_to_dec_string X = num_to_dec_string x ++ str ==>
  num_to_dec_string X =
    (if x DIV 10 = 0 then [] else num_to_dec_string (x DIV 10)) ++
    CHR (48 + x MOD 10)::str
Proof
  strip_tac >> qpat_x_assum `num_to_dec_string X = _` SUBST1_TAC >>
  CONV_TAC (LAND_CONV (LAND_CONV (REWR_CONV decimal_string_quotient_step))) >>
  simp[APPEND_ASSOC]
QED

Theorem u2s_digits_room:
  u2s_digits a b n X x str s /\ 0 < x /\
  X < dimword (:256) /\ 78 <= n ==> LENGTH str < n
Proof
  simp[u2s_digits_def] >> strip_tac >>
  `1 <= LENGTH (num_to_dec_string x)` by
    (irule (cj 1 uint256_decimal_length) >> gvs[dimword_def]) >>
  `LENGTH (num_to_dec_string X) <= 78` by
    (irule (cj 2 uint256_decimal_length) >> gvs[dimword_def]) >>
  qpat_x_assum `num_to_dec_string X = _` (mp_tac o AP_TERM ``LENGTH : string -> num``) >>
  simp[]
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
  strip_tac >>
  `48 + x MOD 10 < 256` by
    (`x MOD 10 < 10` by simp[] >> decide_tac) >>
  `b + n - SUC (LENGTH str) + 32 = b + n - LENGTH str + 31` by decide_tac >>
  `mem_bytes_at (b + n - LENGTH str + 32)
     (LENGTH (MAP (n2w o ORD) str : word8 list)) s.vs_memory =
     MAP (n2w o ORD) str` by asm_rewrite_tac[LENGTH_MAP] >>
  drule mstore_prepend_byte >>
  disch_then (qspec_then `n2w (48 + x MOD 10)` mp_tac) >>
  `dimindex (:8) = 8` by CONV_TAC fcpLib.INDEX_CONV >>
  simp_tac bool_ss [LENGTH_MAP, LENGTH, MAP, combinTheory.o_THM, w2w_n2w,
                    stringTheory.ORD_CHR_RWT] >>
  simp[]
QED

Theorem u2s_digits_step:
  u2s_digits a b n X x str s /\ 0 < x /\ LENGTH str < n ==>
  u2s_digits a b n X (x DIV 10) (CHR (48 + x MOD 10)::str)
    (update_var (u2s_var a 1) (n2w (SUC (LENGTH str)))
      (update_var (u2s_var a 0) (n2w (x DIV 10))
        (mstore (b + n - LENGTH str) (n2w (48 + x MOD 10)) s)))
Proof
  strip_tac >>
  `x DIV 10 < dimword (:256)` by
    (fs[u2s_digits_def] >>
     `x DIV 10 <= x` by simp[DIV_LESS_EQ] >> decide_tac) >>
  `num_to_dec_string X =
     (if x DIV 10 = 0 then [] else num_to_dec_string (x DIV 10)) ++
       CHR (48 + x MOD 10)::str` by
    (irule decimal_suffix_step >> fs[u2s_digits_def]) >>
  `mem_bytes_at (b + n - LENGTH (CHR (48 + x MOD 10)::str) + 32)
     (LENGTH (CHR (48 + x MOD 10)::str))
     (mstore (b + n - LENGTH str) (n2w (48 + x MOD 10)) s).vs_memory =
       MAP (n2w o ORD) (CHR (48 + x MOD 10)::str)` by
    (irule u2s_store_digit >> fs[u2s_digits_def]) >>
  gvs[u2s_digits_def, venomStateTheory.update_var_def,
      venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]
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
  strip_tac >>
  `eval_operand buf (update_var (u2s_var a 6) (48w + safe_mod xw 10w)
     (update_var (u2s_var a 5) (safe_mod xw 10w) s)) = SOME bw` by
    (irule emitHelperPropsTheory.eval_operand_update_var_mstore >> conj_tac
     >- metis_tac[u2s_var_fresh] >>
     irule emitHelperPropsTheory.eval_operand_update_var_mstore >> simp[] >>
     metis_tac[u2s_var_fresh]) >>
  `step_inst_base (u2s_inst a 8 Mod
      [Var (u2s_var a 0); Lit 10w] [u2s_var a 5]) s =
     OK (update_var (u2s_var a 5) (safe_mod xw 10w) s)` by
    (simp[u2s_inst_def] >> irule emitHelperPropsTheory.step_Mod >>
     simp[emitHelperPropsTheory.eval_operand_lit]) >>
  `step_inst_base (u2s_inst a 9 ADD
      [Lit 48w; Var (u2s_var a 5)] [u2s_var a 6])
      (update_var (u2s_var a 5) (safe_mod xw 10w) s) =
     OK (update_var (u2s_var a 6) (48w + safe_mod xw 10w)
       (update_var (u2s_var a 5) (safe_mod xw 10w) s))` by
    (simp[u2s_inst_def] >> irule emitHelperPropsTheory.step_ADD >>
     simp[emitHelperPropsTheory.eval_operand_lit,
          emitHelperPropsTheory.eval_operand_update_var]) >>
  `step_inst_base (u2s_inst a 10 ADD [buf; Lit (n2w n)] [u2s_var a 7])
      (update_var (u2s_var a 6) (48w + safe_mod xw 10w)
       (update_var (u2s_var a 5) (safe_mod xw 10w) s)) =
     OK (update_var (u2s_var a 7) (bw + n2w n)
       (update_var (u2s_var a 6) (48w + safe_mod xw 10w)
        (update_var (u2s_var a 5) (safe_mod xw 10w) s)))` by
    (simp[u2s_inst_def] >> irule emitHelperPropsTheory.step_ADD >>
     simp[emitHelperPropsTheory.eval_operand_lit]) >>
  `step_inst_base (u2s_inst a 11 SUB
      [Var (u2s_var a 7); Var (u2s_var a 1)] [u2s_var a 8])
      (update_var (u2s_var a 7) (bw + n2w n)
       (update_var (u2s_var a 6) (48w + safe_mod xw 10w)
        (update_var (u2s_var a 5) (safe_mod xw 10w) s))) =
     OK (update_var (u2s_var a 8) (bw + n2w n - iw)
       (update_var (u2s_var a 7) (bw + n2w n)
        (update_var (u2s_var a 6) (48w + safe_mod xw 10w)
         (update_var (u2s_var a 5) (safe_mod xw 10w) s))))` by
    (simp[u2s_inst_def] >> irule emitHelperPropsTheory.step_SUB >>
     simp[emitHelperPropsTheory.eval_operand_update_var,
          emitHelperPropsTheory.eval_operand_update_other]) >>
  simp[u2s_body_def, exprLoweringPropsTheory.run_inst_seq_def]
QED

Theorem u2s_body_div_run:
  eval_operand (Var (u2s_var a 0)) s = SOME xw ==>
  run_inst_seq (TAKE 2 (DROP 5 (u2s_body a buf n))) s =
    OK (update_var (u2s_var a 0) (safe_div xw 10w)
      (update_var (u2s_var a 9) (safe_div xw 10w) s))
Proof
  strip_tac >>
  `step_inst_base (u2s_inst a 13 Div
      [Var (u2s_var a 0); Lit 10w] [u2s_var a 9]) s =
      OK (update_var (u2s_var a 9) (safe_div xw 10w) s)` by
    (simp[u2s_inst_def] >> irule emitHelperPropsTheory.step_Div >>
     simp[emitHelperPropsTheory.eval_operand_lit]) >>
  simp[u2s_body_def, exprLoweringPropsTheory.run_inst_seq_def] >>
  simp_tac (srw_ss()) [u2s_inst_def, venomInstTheory.mk_inst_def] >>
  simp_tac (srw_ss()) [Once step_inst_base_def] >>
  simp[emitHelperPropsTheory.eval_operand_update_var]
QED

Theorem u2s_body_count_run:
  eval_operand (Var (u2s_var a 1)) s = SOME iw ==>
  run_inst_seq (TAKE 2 (DROP 7 (u2s_body a buf n))) s =
    OK (update_var (u2s_var a 1) (iw + 1w)
      (update_var (u2s_var a 10) (iw + 1w) s))
Proof
  strip_tac >>
  `step_inst_base (u2s_inst a 15 ADD
      [Var (u2s_var a 1); Lit 1w] [u2s_var a 10]) s =
      OK (update_var (u2s_var a 10) (iw + 1w) s)` by
    (simp[u2s_inst_def] >> irule emitHelperPropsTheory.step_ADD >>
     simp[emitHelperPropsTheory.eval_operand_lit]) >>
  simp[u2s_body_def, exprLoweringPropsTheory.run_inst_seq_def] >>
  simp[u2s_inst_def, step_inst_base_def, venomInstTheory.mk_inst_def,
       emitHelperPropsTheory.eval_operand_update_var]
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
  strip_tac >>
  `run_inst_seq (TAKE 4 (u2s_body a buf n)) s = OK s1` by
    (gvs[] >> irule u2s_body_address_run >> simp[]) >>
  `step_inst_base (u2s_inst a 12 MSTORE
      [Var (u2s_var a 8); Var (u2s_var a 6)] []) s1 = OK s2` by
    (gvs[] >> simp[u2s_inst_def] >> irule emitHelperPropsTheory.step_MSTORE >>
     simp[emitHelperPropsTheory.eval_operand_update_var,
          emitHelperPropsTheory.eval_operand_update_other]) >>
  `eval_operand (Var (u2s_var a 0)) s2 = SOME xw /\
   eval_operand (Var (u2s_var a 1)) s3 = SOME iw` by
    (gvs[] >> simp[emitHelperPropsTheory.eval_operand_mstore,
       emitHelperPropsTheory.eval_operand_update_other]) >>
  `run_inst_seq (TAKE 2 (DROP 5 (u2s_body a buf n))) s2 = OK s3` by
    (qpat_x_assum `s3 = _` SUBST1_TAC >> irule u2s_body_div_run >> simp[]) >>
  `run_inst_seq (TAKE 2 (DROP 7 (u2s_body a buf n))) s3 = OK t` by
    (qpat_x_assum `t = _` SUBST1_TAC >> irule u2s_body_count_run >> simp[]) >>
  `TAKE 9 (u2s_body a buf n) = TAKE 4 (u2s_body a buf n) ++
     [u2s_inst a 12 MSTORE [Var (u2s_var a 8); Var (u2s_var a 6)] []] ++
     (TAKE 2 (DROP 5 (u2s_body a buf n)) ++
      TAKE 2 (DROP 7 (u2s_body a buf n)))` by simp[u2s_body_def] >>
  map_every (fn q => qpat_x_assum q kall_tac)
    [`s1 = _`, `s2 = _`, `s3 = _`, `t = _`] >>
  qpat_x_assum `TAKE 9 _ = _` (fn th => pure_rewrite_tac[th]) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  qpat_assum `run_inst_seq (TAKE 4 _) s = _`
    (fn th => rewrite_tac[MATCH_MP exprLoweringPropsTheory.run_inst_seq_append th]) >>
  simp[APPEND, exprLoweringPropsTheory.run_inst_seq_def] >>
  qpat_assum `run_inst_seq (TAKE 2 (DROP 5 _)) s2 = _`
    (fn th => rewrite_tac[MATCH_MP exprLoweringPropsTheory.run_inst_seq_append th]) >>
  asm_rewrite_tac[]
QED

Theorem u2s_word_arithmetic:
  x < dimword (:256) /\ i <= n ==>
  safe_mod (n2w x) 10w = n2w (x MOD 10) /\
  safe_div (n2w x) 10w = n2w (x DIV 10) /\
  48w + safe_mod (n2w x) 10w = n2w (48 + x MOD 10) /\
  (n2w b : bytes32) + n2w n - n2w i = n2w (b+n-i) /\
  (n2w i : bytes32) + 1w = n2w (SUC i)
Proof
  strip_tac >>
  simp[safe_mod_def, safe_div_def, word_mod_def, word_div_def,
       word_add_n2w, GSYM n2w_sub, ADD1] >>
  simp[dimword_def, word_add_n2w, ADD_COMM]
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
  strip_tac >>
  `u2s_digits a b n X x str s1` by gvs[u2s_digits_update] >>
  drule_all u2s_digits_step >>
  gvs[u2s_digits_def, venomStateTheory.update_var_def,
      venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]
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
  strip_tac >> qpat_x_assum `buf = Var p` SUBST_ALL_TAC >>
  `u2s_safe ctx fn cenv cx es a (Var p) b sz inst s0 s1` by
    (qpat_x_assum `s1 = _` SUBST1_TAC >>
     rpt (irule u2s_safe_update >> simp[])) >>
  qpat_x_assum `s1 = _` kall_tac >>
  `u2s_safe ctx fn cenv cx es a (Var p) b sz inst s0 s2` by
    (qpat_x_assum `s2 = _` SUBST1_TAC >> irule u2s_safe_mstore >>
     simp[] >> metis_tac[]) >>
  qpat_x_assum `s2 = _` kall_tac >>
  `u2s_safe ctx fn cenv cx es a (Var p) b sz inst s0 s3` by
    (qpat_x_assum `s3 = _` SUBST1_TAC >>
     rpt (irule u2s_safe_update >> simp[])) >>
  qpat_x_assum `s3 = _` kall_tac >>
  qpat_x_assum `t = _` SUBST1_TAC >>
  rpt (irule u2s_safe_update >> simp[])
QED

Theorem u2s_update_control:
  (update_var z w s).vs_current_bb = s.vs_current_bb /\
  (update_var z w s).vs_inst_idx = s.vs_inst_idx /\
  (update_var z w s).vs_prev_bb = s.vs_prev_bb /\
  (update_var z w s).vs_halted = s.vs_halted
Proof
  simp[venomStateTheory.update_var_def]
QED

Theorem u2s_mstore_control:
  (mstore at w s).vs_current_bb = s.vs_current_bb /\
  (mstore at w s).vs_inst_idx = s.vs_inst_idx /\
  (mstore at w s).vs_prev_bb = s.vs_prev_bb /\
  (mstore at w s).vs_halted = s.vs_halted
Proof
  simp[venomStateTheory.mstore_def]
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
  strip_tac >>
  `safe_mod (n2w x) 10w = n2w (x MOD 10) /\
   safe_div (n2w x) 10w = n2w (x DIV 10) /\
   48w + safe_mod (n2w x) 10w = n2w (48+x MOD 10) /\
   (n2w b : bytes32) + n2w n - n2w (LENGTH str) = n2w (b+n-LENGTH str) /\
   (n2w (LENGTH str) : bytes32) + 1w = n2w (SUC (LENGTH str))` by
    (irule u2s_word_arithmetic >> fs[u2s_digits_def]) >>
  qabbrev_tac `s1 = update_var (u2s_var a 8) (n2w (b+n-LENGTH str))
    (update_var (u2s_var a 7) (n2w b + n2w n)
     (update_var (u2s_var a 6) (n2w (48+x MOD 10))
      (update_var (u2s_var a 5) (n2w (x MOD 10)) s)))` >>
  qabbrev_tac `s2 = mstore (b+n-LENGTH str) (n2w (48+x MOD 10)) s1` >>
  qabbrev_tac `s3 = update_var (u2s_var a 0) (n2w (x DIV 10))
    (update_var (u2s_var a 9) (n2w (x DIV 10)) s2)` >>
  qabbrev_tac `t = update_var (u2s_var a 1) (n2w (SUC (LENGTH str)))
    (update_var (u2s_var a 10) (n2w (SUC (LENGTH str))) s3)` >>
  qexists_tac `t` >> conj_tac
  >- (irule u2s_body_run >> conj_tac >- simp[] >>
      qexistsl_tac [`n2w b`, `n2w (LENGTH str)`, `s1`, `s2`, `s3`, `n2w x`] >>
      `b+n-LENGTH str < dimword (:256)` by decide_tac >>
      simp[Abbr `s1`, Abbr `s2`, Abbr `s3`, Abbr `t`,
           u2s_safe_def, u2s_digits_def, venomStateTheory.eval_operand_def] >>
      gvs[u2s_safe_def, u2s_digits_def, venomStateTheory.eval_operand_def]) >>
  `b <= b+n-LENGTH str /\ b+n-LENGTH str+32 <= b+sz` by decide_tac >>
  `?p. buf = Var p /\ not_fresh_at a p` by metis_tac[] >>
  rule_assum_tac (REWRITE_RULE [markerTheory.Abbrev_def]) >>
  `u2s_safe ctx fn cenv cx es a buf b sz inst s0 t` by
    (metis_tac[u2s_body_safe]) >>
  `u2s_digits a b n X (x DIV 10) (CHR (48+x MOD 10)::str) t` by
    (drule_all u2s_body_digits >> simp[]) >>
  simp[] >>
  simp_tac (srw_ss()) [u2s_update_control, u2s_mstore_control]
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
  strip_tac >>
  `step_inst_base (u2s_inst a 25 ADD [buf; Lit (n2w n)] [u2s_var a 14]) s =
     OK s1` by
    (qpat_x_assum `s1 = _` SUBST1_TAC >> simp[u2s_inst_def] >>
     irule emitHelperPropsTheory.step_ADD >> simp[emitHelperPropsTheory.eval_operand_lit]) >>
  `step_inst_base (u2s_inst a 26 SUB
     [Var (u2s_var a 14); Var (u2s_var a 1)] [u2s_var a 15]) s1 = OK s2` by
    (qpat_x_assum `s2 = _` SUBST1_TAC >> simp[u2s_inst_def] >>
     irule emitHelperPropsTheory.step_SUB >>
     gvs[emitHelperPropsTheory.eval_operand_update_var,
         emitHelperPropsTheory.eval_operand_update_other]) >>
  `step_inst_base (u2s_inst a 27 MSTORE
     [Var (u2s_var a 15); Var (u2s_var a 1)] []) s2 = OK s3` by
    (qpat_x_assum `s3 = _` SUBST1_TAC >> simp[u2s_inst_def] >>
     irule emitHelperPropsTheory.step_MSTORE >>
     gvs[emitHelperPropsTheory.eval_operand_update_var,
         emitHelperPropsTheory.eval_operand_update_other]) >>
  `step_inst_base (u2s_inst a 28 ASSIGN [Var (u2s_var a 15)] [u2s_var a 2]) s3 =
     OK t` by
    (qpat_x_assum `t = _` SUBST1_TAC >> simp[u2s_inst_def] >>
     irule u2s_step_assign >>
     gvs[emitHelperPropsTheory.eval_operand_mstore,
         emitHelperPropsTheory.eval_operand_update_var]) >>
  map_every (fn q => qpat_x_assum q kall_tac)
    [`s1 = _`, `s2 = _`, `s3 = _`, `t = _`] >>
  simp[u2s_final_def, exprLoweringPropsTheory.run_inst_seq_def]
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
  strip_tac >>
  `mem_bytes_at (b+n-LENGTH str+32) (LENGTH str) s2.vs_memory =
     MAP (n2w o ORD) str` by
    gvs[u2s_digits_def, venomStateTheory.update_var_def] >>
  drule mstore_string_header >> disch_then (qspec_then `ty` assume_tac) >>
  gvs[venomStateTheory.update_var_def, venomStateTheory.eval_operand_def,
      venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]
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
  strip_tac >> qpat_x_assum `buf = Var p` SUBST_ALL_TAC >>
  `u2s_safe ctx fn cenv cx es a (Var p) b sz inst s0 s1` by
    (qpat_x_assum `s1 = _` SUBST1_TAC >> irule u2s_safe_update >> simp[]) >>
  qpat_x_assum `s1 = _` kall_tac >>
  `u2s_safe ctx fn cenv cx es a (Var p) b sz inst s0 s2` by
    (qpat_x_assum `s2 = _` SUBST1_TAC >> irule u2s_safe_update >> simp[]) >>
  qpat_x_assum `s2 = _` kall_tac >>
  `u2s_safe ctx fn cenv cx es a (Var p) b sz inst s0 s3` by
    (qpat_x_assum `s3 = _` SUBST1_TAC >> irule u2s_safe_mstore >> simp[]) >>
  qpat_x_assum `s3 = _` kall_tac >>
  qpat_x_assum `t = _` SUBST1_TAC >> irule u2s_safe_update >> simp[]
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
  strip_tac >>
  `LENGTH str <= n` by fs[u2s_digits_def] >>
  `b <= b+n-LENGTH str /\ b+n-LENGTH str+32 <= b+sz /\
   b+n-LENGTH str+32+LENGTH str <= b+sz /\
   b+n-LENGTH str < dimword (:256)` by decide_tac >>
  `(n2w b : bytes32)+n2w n-n2w (LENGTH str) = n2w (b+n-LENGTH str)` by
    simp[word_add_n2w, GSYM n2w_sub] >>
  qabbrev_tac `s1 = update_var (u2s_var a 14) (n2w b+n2w n) s` >>
  qabbrev_tac `s2 = update_var (u2s_var a 15) (n2w (b+n-LENGTH str)) s1` >>
  qabbrev_tac `s3 = mstore (b+n-LENGTH str) (n2w (LENGTH str)) s2` >>
  qabbrev_tac `t = update_var (u2s_var a 2) (n2w (b+n-LENGTH str)) s3` >>
  qexists_tac `t` >> conj_tac
  >- (irule u2s_final_run >>
      qexistsl_tac [`n2w b`, `n2w (LENGTH str)`, `s1`, `s2`, `s3`] >>
      simp[Abbr `s1`, Abbr `s2`, Abbr `s3`, Abbr `t`] >>
      gvs[u2s_safe_def, u2s_digits_def, venomStateTheory.eval_operand_def]) >>
  rule_assum_tac (REWRITE_RULE [markerTheory.Abbrev_def]) >>
  `u2s_safe ctx fn cenv cx es a buf b sz inst s0 t` by
    metis_tac[u2s_final_safe] >>
  `val_in_memory ty (StringV str) (b+n-LENGTH str) t.vs_memory /\
   eval_operand (Var (u2s_var a 2)) t = SOME (n2w (b+n-LENGTH str))` by
    (drule_all u2s_final_encoding >> simp[]) >>
  simp[] >> simp_tac (srw_ss()) [u2s_update_control, u2s_mstore_control]
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
  strip_tac >> qpat_x_assum `buf = Var p` SUBST_ALL_TAC >>
  `step_inst_base (u2s_inst a 18 ADD [Var p; Lit (n2w n)] [u2s_var a 11]) s = OK s1` by
    (qpat_x_assum `s1 = _` SUBST1_TAC >> simp[u2s_inst_def] >>
     irule emitHelperPropsTheory.step_ADD >> simp[emitHelperPropsTheory.eval_operand_lit]) >>
  `step_inst_base (u2s_inst a 19 MSTORE [Var (u2s_var a 11); Lit 48w] []) s1 = OK s2` by
    (qpat_x_assum `s2 = _` SUBST1_TAC >> simp[u2s_inst_def] >>
     irule emitHelperPropsTheory.step_MSTORE >>
     gvs[emitHelperPropsTheory.eval_operand_update_var, emitHelperPropsTheory.eval_operand_lit]) >>
  `step_inst_base (u2s_inst a 20 ADD [Var p; Lit (n2w n)] [u2s_var a 12]) s2 = OK s3` by
    (qpat_x_assum `s3 = _` SUBST1_TAC >> simp[u2s_inst_def] >>
     irule emitHelperPropsTheory.step_ADD >>
     gvs[emitHelperPropsTheory.eval_operand_mstore, emitHelperPropsTheory.eval_operand_update_other,
         emitHelperPropsTheory.eval_operand_lit, u2s_var_fresh]) >>
  `step_inst_base (u2s_inst a 21 SUB [Var (u2s_var a 12); Lit 1w] [u2s_var a 13]) s3 = OK s4` by
    (qpat_x_assum `s4 = _` SUBST1_TAC >> simp[u2s_inst_def] >>
     irule emitHelperPropsTheory.step_SUB >>
     gvs[emitHelperPropsTheory.eval_operand_update_var, emitHelperPropsTheory.eval_operand_lit]) >>
  `step_inst_base (u2s_inst a 22 MSTORE [Var (u2s_var a 13); Lit 1w] []) s4 = OK s5` by
    (qpat_x_assum `s5 = _` SUBST1_TAC >> simp[u2s_inst_def] >>
     irule emitHelperPropsTheory.step_MSTORE >>
     gvs[emitHelperPropsTheory.eval_operand_update_var, emitHelperPropsTheory.eval_operand_lit]) >>
  `step_inst_base (u2s_inst a 23 ASSIGN [Var (u2s_var a 13)] [u2s_var a 2]) s5 = OK t` by
    (qpat_x_assum `t = _` SUBST1_TAC >> simp[u2s_inst_def] >> irule u2s_step_assign >>
     gvs[emitHelperPropsTheory.eval_operand_mstore, emitHelperPropsTheory.eval_operand_update_var]) >>
  map_every (fn q => qpat_x_assum q kall_tac)
    [`s1 = _`, `s2 = _`, `s3 = _`, `s4 = _`, `s5 = _`, `t = _`] >>
  simp[u2s_zero_def, exprLoweringPropsTheory.run_inst_seq_def]
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
  strip_tac >>
  `b+n-1+32 = b+n+31` by decide_tac >>
  `mem_bytes_at ((b+n)+31) 1 (mstore (b+n) 48w s1).vs_memory = [48w]` by
    (rewrite_tac[mstore_last_byte, w2w_n2w] >> CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> simp[]) >>
  `mem_bytes_at (b+n-1+32) (LENGTH "0") s4.vs_memory =
     MAP (n2w o ORD) "0"` by
    gvs[venomStateTheory.update_var_def] >>
  drule mstore_string_header >> disch_then (qspec_then `ty` assume_tac) >>
  gvs[venomStateTheory.update_var_def, venomStateTheory.eval_operand_def,
      venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]
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
  strip_tac >> qpat_x_assum `buf = Var p` SUBST_ALL_TAC >>
  `u2s_safe ctx fn cenv cx es a (Var p) b sz inst s0 s1` by
    (qpat_x_assum `s1 = _` SUBST1_TAC >> irule u2s_safe_update >> simp[]) >>
  qpat_x_assum `s1 = _` kall_tac >>
  `u2s_safe ctx fn cenv cx es a (Var p) b sz inst s0 s2` by
    (qpat_x_assum `s2 = _` SUBST1_TAC >> irule u2s_safe_mstore >> simp[]) >>
  qpat_x_assum `s2 = _` kall_tac >>
  `u2s_safe ctx fn cenv cx es a (Var p) b sz inst s0 s3` by
    (qpat_x_assum `s3 = _` SUBST1_TAC >> irule u2s_safe_update >> simp[]) >>
  qpat_x_assum `s3 = _` kall_tac >>
  `u2s_safe ctx fn cenv cx es a (Var p) b sz inst s0 s4` by
    (qpat_x_assum `s4 = _` SUBST1_TAC >> irule u2s_safe_update >> simp[]) >>
  qpat_x_assum `s4 = _` kall_tac >>
  `u2s_safe ctx fn cenv cx es a (Var p) b sz inst s0 s5` by
    (qpat_x_assum `s5 = _` SUBST1_TAC >> irule u2s_safe_mstore >> simp[] >> decide_tac) >>
  qpat_x_assum `s5 = _` kall_tac >>
  qpat_x_assum `t = _` SUBST1_TAC >> irule u2s_safe_update >> simp[]
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
  strip_tac >>
  `b <= b+n-1 /\ b+n-1+33 <= b+sz /\
   b+n < dimword (:256) /\ b+n-1 < dimword (:256)` by decide_tac >>
  `(n2w b : bytes32)+n2w n = n2w (b+n)` by simp[word_add_n2w] >>
  `(n2w (b+n) : bytes32)-1w = n2w (b+n-1)` by simp[GSYM n2w_sub] >>
  qabbrev_tac `s1 = update_var (u2s_var a 11) (n2w (b+n)) s` >>
  qabbrev_tac `s2 = mstore (b+n) 48w s1` >>
  qabbrev_tac `s3 = update_var (u2s_var a 12) (n2w (b+n)) s2` >>
  qabbrev_tac `s4 = update_var (u2s_var a 13) (n2w (b+n-1)) s3` >>
  qabbrev_tac `s5 = mstore (b+n-1) 1w s4` >>
  qabbrev_tac `t = update_var (u2s_var a 2) (n2w (b+n-1)) s5` >>
  qexists_tac `t` >> conj_tac
  >- (irule u2s_zero_run >> conj_tac >- metis_tac[] >>
      qexistsl_tac [`n2w b`, `s1`, `s2`, `s3`, `s4`, `s5`] >>
      simp[Abbr `s1`, Abbr `s2`, Abbr `s3`, Abbr `s4`, Abbr `s5`, Abbr `t`] >>
      gvs[u2s_safe_def]) >>
  rule_assum_tac (REWRITE_RULE [markerTheory.Abbrev_def]) >>
  `u2s_safe ctx fn cenv cx es a buf b sz inst s0 t` by
    metis_tac[u2s_zero_safe] >>
  `val_in_memory ty (StringV "0") (b+n-1) t.vs_memory /\
   eval_operand (Var (u2s_var a 2)) t = SOME (n2w (b+n-1))` by
    (drule_all u2s_zero_encoding >> simp[]) >>
  simp[] >> simp_tac (srw_ss()) [u2s_update_control, u2s_mstore_control]
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
  strip_tac >> drule_all exec_block_run_inst_seq >>
  disch_then (qspecl_then [`fuel`, `ctx`] mp_tac) >>
  disch_then (qspec_then `t` mp_tac o CONJUNCT1) >> simp[] >> strip_tac >>
  simp[run_from_def]
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
  strip_tac >>
  `!k. run_from k ctx fn s =
       run_from k ctx fn (t with vs_inst_idx := LENGTH is)` by
    (`isPREFIX is (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >>
     drule_all u2s_run_from_prefix >> simp[]) >>
  simp[] >> irule run_from_jump_result >> simp[] >>
  qexistsl_tac [`bb`, `j`, `lbl`] >>
  `t.vs_current_bb = s.vs_current_bb` by
    (`isPREFIX is (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >>
     drule_all exec_block_run_inst_seq >>
     disch_then (qspecl_then [`fuel`, `ctx`] mp_tac) >>
     disch_then (qspec_then `t` mp_tac o CONJUNCT1) >> simp[]) >>
  gvs[venomInstTheory.get_instruction_def, EL_APPEND_EQN,
      venomStateTheory.jump_to_def]
QED

Theorem u2s_final_continue:
  lookup_block (u2s_label a 4) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 4; bb_instructions := u2s_final a buf n|> /\
  s.vs_current_bb = u2s_label a 4 /\ s.vs_inst_idx = 0 /\
  run_inst_seq (TAKE 4 (u2s_final a buf n)) s = OK t /\ ~t.vs_halted /\
  run_from fuel ctx fn (jump_to (u2s_label a 5) t) = r /\ (!e. r <> Error e) ==>
  run_from (SUC fuel) ctx fn s = r
Proof
  strip_tac >> irule u2s_run_from_block >> simp[] >>
  qexistsl_tac [`TAKE 4 (u2s_final a buf n)`, `LAST (u2s_final a buf n)`,
                `u2s_label a 5`, `t`] >>
  simp[] >>
  simp[u2s_final_def, u2s_inst_def, venomInstTheory.mk_inst_def,
       venomInstTheory.is_terminator_def, step_inst_base_def, venomStateTheory.jump_to_def]
QED

Theorem u2s_zero_continue:
  lookup_block (u2s_label a 3) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 3; bb_instructions := u2s_zero a buf n|> /\
  s.vs_current_bb = u2s_label a 3 /\ s.vs_inst_idx = 0 /\
  run_inst_seq (TAKE 6 (u2s_zero a buf n)) s = OK t /\ ~t.vs_halted /\
  run_from fuel ctx fn (jump_to (u2s_label a 5) t) = r /\ (!e. r <> Error e) ==>
  run_from (SUC fuel) ctx fn s = r
Proof
  strip_tac >> irule u2s_run_from_block >> simp[] >>
  qexistsl_tac [`TAKE 6 (u2s_zero a buf n)`, `LAST (u2s_zero a buf n)`,
                `u2s_label a 5`, `t`] >>
  simp[] >>
  simp[u2s_zero_def, u2s_inst_def, venomInstTheory.mk_inst_def,
       venomInstTheory.is_terminator_def, step_inst_base_def, venomStateTheory.jump_to_def]
QED

Theorem u2s_body_continue:
  lookup_block (u2s_label a 2) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 2; bb_instructions := u2s_body a buf n|> /\
  s.vs_current_bb = u2s_label a 2 /\ s.vs_inst_idx = 0 /\
  run_inst_seq (TAKE 9 (u2s_body a buf n)) s = OK t /\ ~t.vs_halted /\
  run_from fuel ctx fn (jump_to (u2s_label a 1) t) = r /\ (!e. r <> Error e) ==>
  run_from (SUC fuel) ctx fn s = r
Proof
  strip_tac >> irule u2s_run_from_block >> simp[] >>
  qexistsl_tac [`TAKE 9 (u2s_body a buf n)`, `LAST (u2s_body a buf n)`,
                `u2s_label a 1`, `t`] >> simp[] >>
  simp[u2s_body_def, u2s_inst_def, venomInstTheory.mk_inst_def,
       venomInstTheory.is_terminator_def, step_inst_base_def, venomStateTheory.jump_to_def]
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
  strip_tac >>
  `run_inst_seq (TAKE 1 (u2s_cond a)) s = OK t` by
    (drule_all u2s_cond_run >> simp[]) >>
  irule u2s_run_from_block >> simp[] >>
  qexistsl_tac [`TAKE 1 (u2s_cond a)`, `LAST (u2s_cond a)`,
                `u2s_label a (if x = 0 then 4 else 2)`, `t`] >> simp[] >>
  `lookup_var (u2s_var a 4) (t with vs_inst_idx := 1) = SOME (bool_to_word (x = 0))` by
    gvs[venomStateTheory.update_var_def, venomStateTheory.lookup_var_def,
        finite_mapTheory.FLOOKUP_UPDATE] >>
  Cases_on `x = 0` >>
  gvs[] >>
  simp_tac (srw_ss()) [u2s_cond_def, LAST_DEF] >>
  drule_then assume_tac u2s_jnz_step >>
  simp[venomStateTheory.jump_to_def] >>
  simp_tac (srw_ss()) [u2s_inst_def, venomInstTheory.mk_inst_def,
      venomInstTheory.is_terminator_def]
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
  strip_tac >>
  `run_inst_seq (TAKE 1 (u2s_check a)) s = OK t` by
    (drule_all u2s_check_run >> simp[]) >>
  irule u2s_run_from_block >> simp[] >>
  qexistsl_tac [`TAKE 1 (u2s_check a)`, `LAST (u2s_check a)`,
                `u2s_label a (if x = 0 then 3 else 1)`, `t`] >> simp[] >>
  `lookup_var (u2s_var a 3) (t with vs_inst_idx := 1) = SOME (bool_to_word (x = 0))` by
    gvs[venomStateTheory.update_var_def, venomStateTheory.lookup_var_def,
        finite_mapTheory.FLOOKUP_UPDATE] >>
  Cases_on `x = 0` >>
  gvs[] >>
  simp_tac (srw_ss()) [u2s_check_def, LAST_DEF] >>
  drule_then assume_tac u2s_jnz_step >>
  simp[venomStateTheory.jump_to_def] >>
  simp_tac (srw_ss()) [u2s_inst_def, venomInstTheory.mk_inst_def,
      venomInstTheory.is_terminator_def]
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
  strip_tac >>
  `run_inst_seq (TAKE 3 (u2s_setup a op buf)) s = OK t` by
    (gvs[] >> irule u2s_setup_run >> simp[]) >>
  `!k. run_from k ctx fn s =
       run_from k ctx fn (t with vs_inst_idx := LENGTH pre + 3)` by
    (`isPREFIX (TAKE 3 (u2s_setup a op buf))
        (DROP s.vs_inst_idx bb.bb_instructions)` by
       simp[u2s_setup_def, rich_listTheory.DROP_LENGTH_APPEND] >>
     `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
        (TAKE 3 (u2s_setup a op buf))` by
       simp[u2s_setup_def, venomInstTheory.is_terminator_def,
            u2s_inst_def, venomInstTheory.mk_inst_def] >>
     drule_all u2s_run_from_prefix >> simp[]) >>
  simp[] >> irule run_from_jump_result >> simp[u2s_update_control] >>
  qexistsl_tac [`LAST (u2s_setup a op buf)`, `u2s_label a 0`] >>
  `t.vs_current_bb = s.vs_current_bb /\ ~t.vs_halted` by
    (drule u2s_setup_values >> simp[]) >>
  simp[venomInstTheory.get_instruction_def, EL_APPEND_EQN,
       u2s_setup_def, u2s_inst_def, venomInstTheory.mk_inst_def,
       venomInstTheory.is_terminator_def] >>
  rewrite_tac[step_inst_base_def] >>
  gvs[venomStateTheory.jump_to_def]
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
  strip_tac >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
     [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn)` by metis_tac[] >>
  drule_all alloc_buffer_frame_run >> strip_tac >>
  `!name off len. local_region cenv es.scopes t name off len ==>
     w2n w + sz <= off \/ off + len <= w2n w` by
    (rpt strip_tac >> first_x_assum drule >>
     simp[compileEnvTheory.regions_disjoint_def] >> decide_tac) >>
  `u2s_safe ctx fn cenv cx es a buf.buf_operand (w2n w) sz inst t t` by
    (irule u2s_safe_initial >> gvs[venomInstTheory.mk_inst_def] >>
     metis_tac[ADD_COMM]) >>
  qexistsl_tac [`t`, `w`] >> simp[] >>
  rpt strip_tac >> first_x_assum drule >> simp[compileEnvTheory.regions_disjoint_def] >>
  decide_tac
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
  strip_tac >> drule loweringHaltTheory.compile_alloc_buffer_insts >> strip_tac >>
  `emitted_blocks sa sb = u2s_blocks a op ba.buf_operand n` by
    (qpat_x_assum `u2s_layout _ _ _ _ _` mp_tac >>
     simp[u2s_layout_def] >> strip_tac >>
     simp[u2s_end_def, emitted_blocks_def, rich_listTheory.TAKE_LENGTH_APPEND]) >>
  `!bb. MEM bb (u2s_blocks a op ba.buf_operand n) ==>
        lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    metis_tac[fn_has_code_def] >>
  `lookup_block a.cs_current_bb fn.fn_blocks =
    SOME <|bb_label := a.cs_current_bb;
           bb_instructions := a.cs_current_insts ++ u2s_setup a op ba.buf_operand|>` by
    (first_x_assum (qspec_then
      `<|bb_label := a.cs_current_bb;
         bb_instructions := a.cs_current_insts ++ u2s_setup a op ba.buf_operand|>` mp_tac) >>
     simp[u2s_blocks_def]) >>
  simp[] >> conj_tac
  >- (simp[fn_has_code_def, emitted_blocks_def] >>
      qexists_tac `<|bb_label := a.cs_current_bb;
        bb_instructions := a.cs_current_insts ++ u2s_setup a op ba.buf_operand|>` >>
      simp[rich_listTheory.IS_PREFIX_APPEND] >> metis_tac[]) >>
  irule lookup_block_fn_insts >>
  qexistsl_tac [`<|bb_label := a.cs_current_bb;
    bb_instructions := a.cs_current_insts ++ u2s_setup a op ba.buf_operand|>`,
    `a.cs_current_bb`] >> simp[]
QED

Theorem u2s_alloc_step:
  compile_alloc_buffer sz sa = (ba,a) /\
  run_inst_seq (emitted_insts sa a) s = OK t ==>
  step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
      [STRING #"%" (toString sa.cs_next_var)]) s = OK t
Proof
  strip_tac >> drule loweringHaltTheory.compile_alloc_buffer_insts >> strip_tac >>
  gvs[exprLoweringPropsTheory.emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND,
      exprLoweringPropsTheory.run_inst_seq_def, venomInstTheory.mk_inst_def,
      venomInstTheory.is_terminator_def, AllCaseEqs()]
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
  strip_tac >> drule loweringHaltTheory.compile_alloc_buffer_insts >> strip_tac >>
  `step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
      [STRING #"%" (toString sa.cs_next_var)]) s = OK t` by
    (drule_all u2s_alloc_step >> simp[]) >>
  `LENGTH a.cs_current_insts = SUC s.vs_inst_idx` by simp[] >>
  qpat_x_assum `LENGTH a.cs_current_insts = _` (fn th => pure_once_rewrite_tac[th]) >>
  irule run_from_step >> qexists_tac `bb` >>
  qexists_tac `mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
      [STRING #"%" (toString sa.cs_next_var)]` >>
  simp[venomInstTheory.get_instruction_def, EL_APPEND_EQN,
       venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def, APPEND_ASSOC]
QED

Theorem u2s_safe_index:
  u2s_safe ctx fn cenv cx es a buf b sz inst s0 s ==>
  u2s_safe ctx fn cenv cx es a buf b sz inst s0 (s with vs_inst_idx := idx)
Proof
  strip_tac >> Cases_on `buf` >>
  gvs[u2s_safe_def, u2s_frame_index, exprLoweringPropsTheory.stmt_state_rel_inst_idx,
       venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
       compileEnvTheory.local_region_def] >> metis_tac[]
QED

Theorem u2s_alloc_control:
  compile_alloc_buffer sz sa = (ba,a) /\
  run_inst_seq (emitted_insts sa a) s = OK t ==>
  t.vs_current_bb = s.vs_current_bb /\ t.vs_halted = s.vs_halted
Proof
  strip_tac >> drule_all u2s_alloc_step >> strip_tac >>
  `step_inst 0 ctx (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
    [STRING #"%" (toString sa.cs_next_var)]) s = OK t` by
    simp[step_inst_non_invoke, venomInstTheory.mk_inst_def] >>
  drule venomInstPropsTheory.step_preserves_control_flow >>
  simp[venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def] >> strip_tac >>
  drule venomInstPropsTheory.step_preserves_halted >>
  simp[venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def]
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
  rpt strip_tac >> gvs[u2s_safe_def] >>
  irule u2s_frame_wb_tail >> simp[] >> qexistsl_tac [`a`, `b`, `s0`, `sz`] >> simp[] >> metis_tac[]
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
  strip_tac >>
  qabbrev_tac `t = update_var (u2s_var a 4) (bool_to_word (x = 0)) s` >>
  `u2s_safe ctx func cenv cx es a buf b sz inst s0 t` by
    (simp[Abbr `t`] >> irule u2s_safe_update >> gvs[]) >>
  `u2s_digits a b n X x str t` by simp[Abbr `t`, u2s_digits_update] >>
  `~t.vs_halted` by simp[Abbr `t`, u2s_update_control] >>
  qexists_tac `jump_to (u2s_label a (if x = 0 then 4 else 2)) t` >>
  simp[u2s_safe_jump, u2s_digits_jump, venomStateTheory.jump_to_def] >>
  rpt strip_tac >> qexists_tac `SUC fuel` >>
  irule u2s_cond_continue >> simp[] >>
  qexistsl_tac [`a`, `x`] >>
  gvs[Abbr `t`, u2s_digits_def, venomStateTheory.jump_to_def]
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
  strip_tac >>
  drule u2s_body_iteration >> simp[] >>
  disch_then (qspecl_then [`x`, `str`, `n`, `X`] mp_tac) >>
  simp[] >> strip_tac >>
  qexists_tac `jump_to (u2s_label a 1) t` >>
  simp[u2s_safe_jump, u2s_digits_jump, venomStateTheory.jump_to_def] >>
  rpt strip_tac >> qexists_tac `SUC fuel` >>
  irule u2s_body_continue >> simp[] >>
  qexistsl_tac [`a`, `Var p`, `n`, `t`] >>
  gvs[venomStateTheory.jump_to_def]
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
  strip_tac >>
  drule u2s_final_result >> simp[] >>
  disch_then (qspec_then `ty` mp_tac) >>
  disch_then (qspecl_then [`str`, `n`, `X`] mp_tac) >> simp[] >> strip_tac >>
  qexists_tac `jump_to (u2s_label a 5) t` >>
  fs[venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def] >>
  simp[u2s_safe_jump, venomStateTheory.jump_to_def,
       venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def] >>
  rpt strip_tac >> qexists_tac `SUC fuel` >>
  irule u2s_final_continue >> simp[] >> qexistsl_tac [`a`, `Var p`, `n`, `t`] >>
  gvs[venomStateTheory.jump_to_def]
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
  completeInduct_on `x` >> rpt gen_tac >> strip_tac >>
  `?c. u2s_safe ctx func cenv cx es a buf b sz inst s0 c /\
       u2s_digits a b n X x str c /\
       c.vs_current_bb = u2s_label a (if x = 0 then 4 else 2) /\
       c.vs_inst_idx = 0 /\ ~c.vs_halted /\
       (!fuel r. run_from fuel ctx fn c = r /\ (!e. r <> Error e) ==>
                 ?fuel'. run_from fuel' ctx fn s = r)` by
    (irule u2s_cond_transition >> simp[] >>
     first_x_assum (qspec_then
       `<|bb_label := u2s_label a 1; bb_instructions := u2s_cond a|>` mp_tac) >>
     simp[u2s_blocks_def]) >>
  Cases_on `x = 0`
  >- suspend "zero_quotient"
  >> suspend "positive_quotient"
QED

Resume u2s_loop[zero_quotient]:
  gvs[] >>
  `str = num_to_dec_string X` by gvs[u2s_digits_def] >>
  `?t. u2s_safe ctx func cenv cx es a (Var p) b sz inst s0 t /\
      eval_operand (Var (u2s_var a 2)) t = SOME (n2w (b+n-LENGTH str)) /\
      val_in_memory ty (StringV str) (b+n-LENGTH str) t.vs_memory /\
      b <= b+n-LENGTH str /\ b+n-LENGTH str+32+LENGTH str <= b+sz /\
      t.vs_current_bb = u2s_label a 5 /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
      (!fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
                ?fuel'. run_from fuel' ctx fn c = r)` by
    (irule u2s_final_exit >> simp[] >> conj_tac
     >- (first_x_assum (qspec_then
       `<|bb_label := u2s_label a 4; bb_instructions := u2s_final a (Var p) n|>` mp_tac) >>
         simp[u2s_blocks_def]) >>
     qexists_tac `X` >> gvs[]) >>
  qexists_tac `t` >> simp[] >> metis_tac[]
QED

Resume u2s_loop[positive_quotient]:
  gvs[] >>
  `0 < x /\ x DIV 10 < x` by simp[DIV_LESS] >>
  `LENGTH str < n` by (irule u2s_digits_room >> metis_tac[]) >>
  `?d. u2s_safe ctx func cenv cx es a (Var p) b sz inst s0 d /\
       u2s_digits a b n X (x DIV 10) (CHR (48+x MOD 10)::str) d /\
       d.vs_current_bb = u2s_label a 1 /\ d.vs_inst_idx = 0 /\ ~d.vs_halted /\
       (!fuel r. run_from fuel ctx fn d = r /\ (!e. r <> Error e) ==>
                 ?fuel'. run_from fuel' ctx fn c = r)` by
    (irule u2s_body_transition >> simp[] >>
     first_x_assum (qspec_then
       `<|bb_label := u2s_label a 2; bb_instructions := u2s_body a (Var p) n|>` mp_tac) >>
     simp[u2s_blocks_def]) >>
  qpat_x_assum `!m. m < x ==> _` (qspec_then `x DIV 10` mp_tac) >> simp[] >>
  disch_then (qspecl_then [`d`, `CHR (48+x MOD 10)::str`] mp_tac) >>
  simp[] >> strip_tac >>
  qexists_tac `t` >> simp[] >> metis_tac[]
QED

Finalise u2s_loop

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
  strip_tac >> drule u2s_zero_result >> simp[] >>
  disch_then (qspecl_then [`ty`, `n`] mp_tac) >> simp[] >> strip_tac >>
  qexists_tac `jump_to (u2s_label a 5) t` >>
  fs[venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def] >>
  simp[u2s_safe_jump, venomStateTheory.jump_to_def,
       venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def] >>
  rpt strip_tac >> qexists_tac `SUC fuel` >>
  irule u2s_zero_continue >> simp[] >> qexistsl_tac [`a`, `Var p`, `n`, `t`] >>
  gvs[venomStateTheory.jump_to_def]
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
  strip_tac >>
  qabbrev_tac `t = update_var (u2s_var a 3) (bool_to_word (x = 0)) s` >>
  `u2s_safe ctx func cenv cx es a buf b sz inst s0 t` by
    (simp[Abbr `t`] >> irule u2s_safe_update >> gvs[]) >>
  `u2s_digits a b n X x str t` by simp[Abbr `t`, u2s_digits_update] >>
  `~t.vs_halted` by simp[Abbr `t`, u2s_update_control] >>
  qexists_tac `jump_to (u2s_label a (if x = 0 then 3 else 1)) t` >>
  simp[u2s_safe_jump, u2s_digits_jump, venomStateTheory.jump_to_def] >>
  rpt strip_tac >> qexists_tac `SUC fuel` >>
  irule u2s_check_continue >> simp[] >> qexistsl_tac [`a`, `x`] >>
  gvs[Abbr `t`, u2s_digits_def, venomStateTheory.jump_to_def]
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
  strip_tac >>
  qabbrev_tac `t = update_var (u2s_var a 3) 1w s` >>
  `u2s_safe ctx func cenv cx es a buf b sz inst s0 t` by
    (simp[Abbr `t`] >> irule u2s_safe_update >> gvs[]) >>
  `~t.vs_halted` by simp[Abbr `t`, u2s_update_control] >>
  qexists_tac `jump_to (u2s_label a 3) t` >>
  simp[u2s_safe_jump, venomStateTheory.jump_to_def] >>
  rpt strip_tac >> qexists_tac `SUC fuel` >>
  irule u2s_check_continue >> simp[] >> qexistsl_tac [`a`, `0`] >>
  gvs[Abbr `t`, venomStateTheory.jump_to_def]
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
  strip_tac >> Cases_on `X = 0`
  >- suspend "zero_input" >>
  `u2s_digits a b n X X [] s` by (irule u2s_digits_initial >> simp[]) >>
  `?c. u2s_safe ctx func cenv cx es a buf b sz inst s0 c /\
       u2s_digits a b n X X [] c /\
       c.vs_current_bb = u2s_label a (if X = 0 then 3 else 1) /\
       c.vs_inst_idx = 0 /\ ~c.vs_halted /\
       (!fuel r. run_from fuel ctx fn c = r /\ (!e. r <> Error e) ==>
                 ?fuel'. run_from fuel' ctx fn s = r)` by
    (irule u2s_check_transition >> simp[] >>
     first_x_assum (qspec_then
       `<|bb_label := u2s_label a 0; bb_instructions := u2s_check a|>` mp_tac) >>
     simp[u2s_blocks_def]) >>
  suspend "positive_input"
QED

Resume u2s_check_exit[positive_input]:
  gvs[] >>
  `?t. u2s_safe ctx func cenv cx es a (Var p) b sz inst s0 t /\
      eval_operand (Var (u2s_var a 2)) t = SOME (n2w (b+n-LENGTH (num_to_dec_string X))) /\
      val_in_memory ty (StringV (num_to_dec_string X))
        (b+n-LENGTH (num_to_dec_string X)) t.vs_memory /\
      b <= b+n-LENGTH (num_to_dec_string X) /\
      b+n-LENGTH (num_to_dec_string X)+32+LENGTH (num_to_dec_string X) <= b+sz /\
      t.vs_current_bb = u2s_label a 5 /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
      (!fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
                ?fuel'. run_from fuel' ctx fn c = r)` by
    (irule u2s_loop >> simp[] >> conj_tac
     >- (qexists_tac `op` >> simp[]) >>
     qexistsl_tac [`[]`, `X`] >> simp[]) >>
  qexists_tac `t` >> simp[] >> metis_tac[]
QED

Resume u2s_check_exit[zero_input]:
  gvs[] >>
  `?c. u2s_safe ctx func cenv cx es a (Var p) b sz inst s0 c /\
       c.vs_current_bb = u2s_label a 3 /\ c.vs_inst_idx = 0 /\ ~c.vs_halted /\
       (!fuel r. run_from fuel ctx fn c = r /\ (!e. r <> Error e) ==>
                 ?fuel'. run_from fuel' ctx fn s = r)` by
    (irule u2s_check_zero_transition >> simp[] >>
     first_x_assum (qspec_then
       `<|bb_label := u2s_label a 0; bb_instructions := u2s_check a|>` mp_tac) >>
     simp[u2s_blocks_def]) >>
  `?t. u2s_safe ctx func cenv cx es a (Var p) b sz inst s0 t /\
      eval_operand (Var (u2s_var a 2)) t = SOME (n2w (b+n-1)) /\
      val_in_memory ty (StringV "0") (b+n-1) t.vs_memory /\
      b <= b+n-1 /\ b+n-1+33 <= b+sz /\
      t.vs_current_bb = u2s_label a 5 /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
      (!fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
                ?fuel'. run_from fuel' ctx fn c = r)` by
    (irule u2s_zero_exit >> simp[] >>
     first_x_assum (qspec_then
       `<|bb_label := u2s_label a 3; bb_instructions := u2s_zero a (Var p) n|>` mp_tac) >>
     simp[u2s_blocks_def]) >>
  `num_to_dec_string 0 = "0"` by EVAL_TAC >>
  qexists_tac `t` >> simp[] >> metis_tac[]
QED

Finalise u2s_check_exit

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
  strip_tac >>
  qabbrev_tac `t = update_var (u2s_var a 2) (n2w b)
    (update_var (u2s_var a 1) 0w (update_var (u2s_var a 0) (n2w X) s))` >>
  `u2s_safe ctx func cenv cx es a buf b sz inst s0 t` by
    (simp[Abbr `t`] >> irule u2s_setup_safe >> gvs[]) >>
  `lookup_var (u2s_var a 0) t = SOME (n2w X) /\
   lookup_var (u2s_var a 1) t = SOME 0w /\ ~t.vs_halted` by
    (simp[Abbr `t`, u2s_update_control, venomStateTheory.lookup_var_def,
          venomStateTheory.update_var_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
  qexists_tac `jump_to (u2s_label a 0) t` >>
  simp[u2s_safe_jump, venomStateTheory.jump_to_def, venomStateTheory.lookup_var_def] >>
  fs[venomStateTheory.lookup_var_def] >>
  rpt strip_tac >> qexists_tac `SUC fuel` >>
  irule u2s_setup_continue >> simp[] >>
  qexistsl_tac [`a`, `buf`, `op`, `n2w b`, `pre`, `n2w X`] >>
  gvs[Abbr `t`, u2s_safe_def, venomStateTheory.jump_to_def]
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
  strip_tac >>
  drule_at (Pat `u2s_safe _ _ _ _ _ _ _ _ _ _ _ _`) u2s_setup_transition >>
  disch_then (qspecl_then [`pre`, `op`, `fn`, `bb`, `X`] mp_tac) >> simp[] >> strip_tac >>
  drule_at (Pat `u2s_safe _ _ _ _ _ _ _ _ _ _ _ _`) u2s_check_exit >>
  disch_then (qspecl_then [`ty`, `op`, `n`, `fn`, `X`] mp_tac) >> gvs[] >> strip_tac >>
  rename1 `val_in_memory ty _ _ out.vs_memory` >>
  qexists_tac `out` >> simp[] >> metis_tac[]
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
  strip_tac >> irule u2s_setup_exit >> simp[] >>
  qexistsl_tac [`op`, `a.cs_current_insts`] >> simp[]
QED

(* ===== Counted target paths of the uint2str code =====

   The fragment is GAS-free, so each block from the setup jump to the exit
   label is a counted path with no readings. *)

Theorem u2s_path_then[local]:
  gas_marked_path F ctx fn s 0 (OK c) /\ gas_marked_path F ctx fn c 0 r ==>
  gas_marked_path F ctx fn s 0 r
Proof
  metis_tac[gas_marked_path_then, arithmeticTheory.ADD_0]
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
  rpt strip_tac >>
  `isPREFIX is (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[DROP_APPEND, rich_listTheory.DROP_LENGTH_APPEND,
         rich_listTheory.IS_PREFIX_APPEND] >>
  `t.vs_current_bb = s.vs_current_bb` by
    (drule_all exec_block_run_inst_seq >>
     disch_then (qspecl_then [`0`, `ctx`] mp_tac) >>
     disch_then (qspec_then `t` mp_tac o CONJUNCT1) >> simp[]) >>
  `gas_marked_path F ctx fn s 0
     (OK (t with vs_inst_idx := LENGTH pre + LENGTH is))` by
    (qspecl_then [`is`, `s`, `t`, `F`, `ctx`, `fn`, `bb`] mp_tac
       storage_copy_seq_path >> simp[]) >>
  `get_instruction bb (LENGTH pre + LENGTH is) = SOME j` by
    simp[venomInstTheory.get_instruction_def, EL_APPEND_EQN] >>
  `jump_to lbl (t with vs_inst_idx := LENGTH pre + LENGTH is) = jump_to lbl t` by
    simp[venomStateTheory.jump_to_def] >>
  `gas_marked_path F ctx fn (t with vs_inst_idx := LENGTH pre + LENGTH is) 0
     (OK (jump_to lbl t))` by
    (qpat_assum `jump_to _ _ = jump_to _ _` (SUBST1_TAC o SYM) >>
     irule storage_copy_jump_path >> simp[] >>
     qexists_tac `j` >> gvs[arithmeticTheory.ADD_COMM]) >>
  irule u2s_path_then >>
  qexists_tac `t with vs_inst_idx := LENGTH pre + LENGTH is` >> simp[]
QED

Theorem u2s_path_continue[local]:
  gas_marked_path F ctx fn s n (OK t) ==>
  !fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
           ?fuel'. run_from fuel' ctx fn s = r
Proof
  metis_tac[gas_marked_path_exec, gas_path_normal]
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
  strip_tac >>
  `lookup_var (u2s_var a 0) s = SOME (n2w x) /\ x < dimword (:256)` by
    fs[u2s_digits_def] >>
  qabbrev_tac `t = update_var (u2s_var a 4) (bool_to_word (x = 0)) s` >>
  `u2s_safe ctx func cenv cx es a buf b sz inst s0 t` by
    (simp[Abbr `t`] >> irule u2s_safe_update >> gvs[]) >>
  `u2s_digits a b n X x str t` by simp[Abbr `t`, u2s_digits_update] >>
  `~t.vs_halted` by simp[Abbr `t`, u2s_update_control] >>
  `run_inst_seq (TAKE 1 (u2s_cond a)) s = OK t` by
    (mp_tac (Q.INST [`t` |-> `update_var (u2s_var a 4) (bool_to_word (x = 0)) s`]
       u2s_cond_run) >> simp[Abbr `t`]) >>
  `lookup_var (u2s_var a 4) (t with vs_inst_idx := 1) = SOME (bool_to_word (x = 0))` by
    simp[Abbr `t`, venomStateTheory.update_var_def, venomStateTheory.lookup_var_def,
         finite_mapTheory.FLOOKUP_UPDATE] >>
  `LENGTH (TAKE 1 (u2s_cond a)) = 1 /\
   step_inst_base (LAST (u2s_cond a)) (t with vs_inst_idx := 1) =
     OK (jump_to (u2s_label a (if x = 0 then 4 else 2)) t)` by
    (simp_tac (srw_ss()) [u2s_cond_def, LAST_DEF] >>
     drule u2s_jnz_step >>
     disch_then (qspecl_then [`u2s_label a 4`, `u2s_label a 2`, `7`] mp_tac) >>
     Cases_on `x = 0` >> simp[venomStateTheory.jump_to_def]) >>
  `gas_marked_path F ctx fn s 0
     (OK (jump_to (u2s_label a (if x = 0 then 4 else 2)) t))` by
    (qspecl_then [`ctx`, `fn`, `s`,
       `<|bb_label := u2s_label a 1; bb_instructions := u2s_cond a|>`, `[]`,
       `TAKE 1 (u2s_cond a)`, `LAST (u2s_cond a)`, `t`,
       `u2s_label a (if x = 0 then 4 else 2)`] mp_tac u2s_block_path >>
     impl_tac >- (simp[] >>
       simp[u2s_cond_def, u2s_inst_def, venomInstTheory.mk_inst_def,
            venomInstTheory.is_terminator_def]) >>
     simp[]) >>
  qexists_tac `jump_to (u2s_label a (if x = 0 then 4 else 2)) t` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  simp[u2s_safe_jump, u2s_digits_jump, venomStateTheory.jump_to_def]
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
  strip_tac >>
  qabbrev_tac `t = update_var (u2s_var a 3) (bool_to_word (x = 0)) s` >>
  `u2s_safe ctx func cenv cx es a buf b sz inst s0 t` by
    (simp[Abbr `t`] >> irule u2s_safe_update >> gvs[]) >>
  `!y str. u2s_digits a b n X y str t <=> u2s_digits a b n X y str s` by
    simp[Abbr `t`, u2s_digits_update] >>
  `~t.vs_halted` by simp[Abbr `t`, u2s_update_control] >>
  `run_inst_seq (TAKE 1 (u2s_check a)) s = OK t` by
    (mp_tac (Q.INST [`t` |-> `update_var (u2s_var a 3) (bool_to_word (x = 0)) s`]
       u2s_check_run) >> simp[Abbr `t`]) >>
  `lookup_var (u2s_var a 3) (t with vs_inst_idx := 1) = SOME (bool_to_word (x = 0))` by
    simp[Abbr `t`, venomStateTheory.update_var_def, venomStateTheory.lookup_var_def,
         finite_mapTheory.FLOOKUP_UPDATE] >>
  `LENGTH (TAKE 1 (u2s_check a)) = 1 /\
   step_inst_base (LAST (u2s_check a)) (t with vs_inst_idx := 1) =
     OK (jump_to (u2s_label a (if x = 0 then 3 else 1)) t)` by
    (simp_tac (srw_ss()) [u2s_check_def, LAST_DEF] >>
     drule u2s_jnz_step >>
     disch_then (qspecl_then [`u2s_label a 3`, `u2s_label a 1`, `5`] mp_tac) >>
     Cases_on `x = 0` >> simp[venomStateTheory.jump_to_def]) >>
  `gas_marked_path F ctx fn s 0
     (OK (jump_to (u2s_label a (if x = 0 then 3 else 1)) t))` by
    (qspecl_then [`ctx`, `fn`, `s`,
       `<|bb_label := u2s_label a 0; bb_instructions := u2s_check a|>`, `[]`,
       `TAKE 1 (u2s_check a)`, `LAST (u2s_check a)`, `t`,
       `u2s_label a (if x = 0 then 3 else 1)`] mp_tac u2s_block_path >>
     impl_tac >- (simp[] >>
       simp[u2s_check_def, u2s_inst_def, venomInstTheory.mk_inst_def,
            venomInstTheory.is_terminator_def]) >>
     simp[]) >>
  qexists_tac `jump_to (u2s_label a (if x = 0 then 3 else 1)) t` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  simp[u2s_safe_jump, u2s_digits_jump, venomStateTheory.jump_to_def]
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
  strip_tac >>
  drule u2s_body_iteration >> simp[] >>
  disch_then (qspecl_then [`x`, `str`, `n`, `X`] mp_tac) >>
  simp[] >> strip_tac >>
  `gas_marked_path F ctx fn s 0 (OK (jump_to (u2s_label a 1) t))` by
    (qspecl_then [`ctx`, `fn`, `s`,
       `<|bb_label := u2s_label a 2; bb_instructions := u2s_body a (Var p) n|>`, `[]`,
       `TAKE 9 (u2s_body a (Var p) n)`, `LAST (u2s_body a (Var p) n)`, `t`,
       `u2s_label a 1`] mp_tac u2s_block_path >>
     impl_tac >- (simp[] >>
       simp[u2s_body_def, u2s_inst_def, venomInstTheory.mk_inst_def,
            venomInstTheory.is_terminator_def, step_inst_base_def,
            venomStateTheory.jump_to_def]) >>
     simp[]) >>
  qexists_tac `jump_to (u2s_label a 1) t` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  simp[u2s_safe_jump, u2s_digits_jump, venomStateTheory.jump_to_def]
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
  strip_tac >>
  drule u2s_final_result >> simp[] >>
  disch_then (qspec_then `ty` mp_tac) >>
  disch_then (qspecl_then [`str`, `n`, `X`] mp_tac) >> simp[] >> strip_tac >>
  `gas_marked_path F ctx fn s 0 (OK (jump_to (u2s_label a 5) t))` by
    (qspecl_then [`ctx`, `fn`, `s`,
       `<|bb_label := u2s_label a 4; bb_instructions := u2s_final a (Var p) n|>`, `[]`,
       `TAKE 4 (u2s_final a (Var p) n)`, `LAST (u2s_final a (Var p) n)`, `t`,
       `u2s_label a 5`] mp_tac u2s_block_path >>
     impl_tac >- (simp[] >>
       simp[u2s_final_def, u2s_inst_def, venomInstTheory.mk_inst_def,
            venomInstTheory.is_terminator_def, step_inst_base_def,
            venomStateTheory.jump_to_def]) >>
     simp[]) >>
  qexists_tac `jump_to (u2s_label a 5) t` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  fs[venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def] >>
  simp[u2s_safe_jump, venomStateTheory.jump_to_def,
       venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def]
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
  strip_tac >> drule u2s_zero_result >> simp[] >>
  disch_then (qspecl_then [`ty`, `n`] mp_tac) >> simp[] >> strip_tac >>
  `gas_marked_path F ctx fn s 0 (OK (jump_to (u2s_label a 5) t))` by
    (qspecl_then [`ctx`, `fn`, `s`,
       `<|bb_label := u2s_label a 3; bb_instructions := u2s_zero a (Var p) n|>`, `[]`,
       `TAKE 6 (u2s_zero a (Var p) n)`, `LAST (u2s_zero a (Var p) n)`, `t`,
       `u2s_label a 5`] mp_tac u2s_block_path >>
     impl_tac >- (simp[] >>
       simp[u2s_zero_def, u2s_inst_def, venomInstTheory.mk_inst_def,
            venomInstTheory.is_terminator_def, step_inst_base_def,
            venomStateTheory.jump_to_def]) >>
     simp[]) >>
  qexists_tac `jump_to (u2s_label a 5) t` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  fs[venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def] >>
  simp[u2s_safe_jump, venomStateTheory.jump_to_def,
       venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def]
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
  completeInduct_on `x` >> rpt gen_tac >> strip_tac >>
  `?c. gas_marked_path F ctx fn s 0 (OK c) /\
       u2s_safe ctx func cenv cx es a buf b sz inst s0 c /\
       u2s_digits a b n X x str c /\
       c.vs_current_bb = u2s_label a (if x = 0 then 4 else 2) /\
       c.vs_inst_idx = 0 /\ ~c.vs_halted` by
    (irule u2s_cond_path >> simp[] >>
     first_x_assum (qspec_then
       `<|bb_label := u2s_label a 1; bb_instructions := u2s_cond a|>` mp_tac) >>
     simp[u2s_blocks_def]) >>
  Cases_on `x = 0`
  >- suspend "zero_quotient"
  >> suspend "positive_quotient"
QED

Resume u2s_loop_path[zero_quotient]:
  gvs[] >>
  `str = num_to_dec_string X` by gvs[u2s_digits_def] >>
  `?t. gas_marked_path F ctx fn c 0 (OK t) /\
      u2s_safe ctx func cenv cx es a (Var p) b sz inst s0 t /\
      eval_operand (Var (u2s_var a 2)) t = SOME (n2w (b+n-LENGTH str)) /\
      val_in_memory ty (StringV str) (b+n-LENGTH str) t.vs_memory /\
      b <= b+n-LENGTH str /\ b+n-LENGTH str+32+LENGTH str <= b+sz /\
      t.vs_current_bb = u2s_label a 5 /\ t.vs_inst_idx = 0 /\ ~t.vs_halted` by
    (irule u2s_final_path >> simp[] >> conj_tac
     >- (first_x_assum (qspec_then
       `<|bb_label := u2s_label a 4; bb_instructions := u2s_final a (Var p) n|>` mp_tac) >>
         simp[u2s_blocks_def]) >>
     qexists_tac `X` >> gvs[]) >>
  qexists_tac `t` >> gvs[] >>
  irule u2s_path_then >> qexists_tac `c` >> simp[]
QED

Resume u2s_loop_path[positive_quotient]:
  gvs[] >>
  `0 < x /\ x DIV 10 < x` by simp[DIV_LESS] >>
  `LENGTH str < n` by (irule u2s_digits_room >> metis_tac[]) >>
  `?d. gas_marked_path F ctx fn c 0 (OK d) /\
       u2s_safe ctx func cenv cx es a (Var p) b sz inst s0 d /\
       u2s_digits a b n X (x DIV 10) (CHR (48+x MOD 10)::str) d /\
       d.vs_current_bb = u2s_label a 1 /\ d.vs_inst_idx = 0 /\ ~d.vs_halted` by
    (irule u2s_body_path >> simp[] >>
     first_x_assum (qspec_then
       `<|bb_label := u2s_label a 2; bb_instructions := u2s_body a (Var p) n|>` mp_tac) >>
     simp[u2s_blocks_def]) >>
  qpat_x_assum `!m. m < x ==> _` (qspec_then `x DIV 10` mp_tac) >> simp[] >>
  disch_then (qspecl_then [`d`, `CHR (48+x MOD 10)::str`] mp_tac) >>
  simp[] >> strip_tac >>
  qexists_tac `t` >> simp[] >>
  irule u2s_path_then >> qexists_tac `d` >> simp[] >>
  irule u2s_path_then >> qexists_tac `c` >> simp[]
QED

Finalise u2s_loop_path

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
  strip_tac >>
  `?c. gas_marked_path F ctx fn s 0 (OK c) /\
       u2s_safe ctx func cenv cx es a buf b sz inst s0 c /\
       (!y str. u2s_digits a b n X y str c <=> u2s_digits a b n X y str s) /\
       c.vs_current_bb = u2s_label a (if X = 0 then 3 else 1) /\
       c.vs_inst_idx = 0 /\ ~c.vs_halted` by
    (irule u2s_check_path >> simp[] >>
     first_x_assum (qspec_then
       `<|bb_label := u2s_label a 0; bb_instructions := u2s_check a|>` mp_tac) >>
     simp[u2s_blocks_def]) >>
  `?t. gas_marked_path F ctx fn c 0 (OK t) /\
      u2s_safe ctx func cenv cx es a buf b sz inst s0 t /\
      eval_operand (Var (u2s_var a 2)) t = SOME (n2w (b+n-LENGTH (num_to_dec_string X))) /\
      val_in_memory ty (StringV (num_to_dec_string X))
        (b+n-LENGTH (num_to_dec_string X)) t.vs_memory /\
      b <= b+n-LENGTH (num_to_dec_string X) /\
      b+n-LENGTH (num_to_dec_string X)+32+LENGTH (num_to_dec_string X) <= b+sz /\
      t.vs_current_bb = u2s_label a 5 /\ t.vs_inst_idx = 0 /\ ~t.vs_halted` by
    (Cases_on `X = 0` >> fs[]
     >- (`num_to_dec_string 0 = "0"` by EVAL_TAC >>
         mp_tac (Q.INST [`s` |-> `c`] u2s_zero_path) >>
         impl_tac >- (fs[] >> first_x_assum (qspec_then
           `<|bb_label := u2s_label a 3; bb_instructions := u2s_zero a buf n|>` mp_tac) >>
           simp[u2s_blocks_def]) >>
         strip_tac >> qexists_tac `t` >> gvs[]) >>
     qspecl_then [`X`, `c`, `[]`] mp_tac u2s_loop_path >>
     impl_tac >- (simp[] >> irule u2s_digits_initial >> simp[]) >>
     strip_tac >> qexists_tac `t` >> gvs[]) >>
  qexists_tac `t` >> simp[] >>
  irule u2s_path_then >> qexists_tac `c` >> simp[]
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
  strip_tac >>
  `eval_operand buf s = SOME (n2w b)` by gvs[u2s_safe_def] >>
  qabbrev_tac `t = update_var (u2s_var a 2) (n2w b)
    (update_var (u2s_var a 1) 0w (update_var (u2s_var a 0) (n2w X) s))` >>
  `u2s_safe ctx func cenv cx es a buf b sz inst s0 t` by
    (simp[Abbr `t`] >> irule u2s_setup_safe >> gvs[]) >>
  `lookup_var (u2s_var a 0) t = SOME (n2w X) /\
   lookup_var (u2s_var a 1) t = SOME 0w /\ ~t.vs_halted` by
    simp[Abbr `t`, u2s_update_control, venomStateTheory.lookup_var_def,
         venomStateTheory.update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  `run_inst_seq (TAKE 3 (u2s_setup a op buf)) s = OK t` by
    (simp[Abbr `t`] >> irule u2s_setup_run >> gvs[]) >>
  `gas_marked_path F ctx fn s 0 (OK (jump_to (u2s_label a 0) t))` by
    (qspecl_then [`ctx`, `fn`, `s`,
       `<|bb_label := a.cs_current_bb;
          bb_instructions := a.cs_current_insts ++ u2s_setup a op buf|>`,
       `a.cs_current_insts`, `TAKE 3 (u2s_setup a op buf)`,
       `LAST (u2s_setup a op buf)`, `t`, `u2s_label a 0`] mp_tac u2s_block_path >>
     impl_tac >- (simp[] >>
       simp[u2s_setup_def, u2s_inst_def, venomInstTheory.mk_inst_def,
            venomInstTheory.is_terminator_def, step_inst_base_def,
            venomStateTheory.jump_to_def]) >>
     simp[]) >>
  `?u. gas_marked_path F ctx fn (jump_to (u2s_label a 0) t) 0 (OK u) /\
      u2s_safe ctx func cenv cx es a buf b sz inst s0 u /\
      eval_operand (Var (u2s_var a 2)) u = SOME (n2w (b+n-LENGTH (num_to_dec_string X))) /\
      val_in_memory ty (StringV (num_to_dec_string X))
        (b+n-LENGTH (num_to_dec_string X)) u.vs_memory /\
      b <= b+n-LENGTH (num_to_dec_string X) /\
      b+n-LENGTH (num_to_dec_string X)+32+LENGTH (num_to_dec_string X) <= b+sz /\
      u.vs_current_bb = u2s_label a 5 /\ u.vs_inst_idx = 0 /\ ~u.vs_halted` by
    (mp_tac (Q.INST [`s` |-> `jump_to (u2s_label a 0) t`] u2s_check_exit_path) >>
     impl_tac >- (simp[u2s_safe_jump] >>
       fs[venomStateTheory.jump_to_def, venomStateTheory.lookup_var_def] >>
       metis_tac[]) >>
     strip_tac >> rename1 `gas_marked_path F ctx fn _ 0 (OK result)` >>
     qexists_tac `result` >> simp[]) >>
  qexists_tac `u` >> simp[] >>
  irule u2s_path_then >> qexists_tac `jump_to (u2s_label a 0) t` >> simp[]
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
  rpt strip_tac >> drule loweringHaltTheory.compile_alloc_buffer_insts >> strip_tac >>
  qspecl_then [`emitted_insts sa a`, `s`, `t`, `F`, `ctx`, `fn`, `bb`] mp_tac
    storage_copy_seq_path >>
  gvs[exprLoweringPropsTheory.emitted_insts_def, DROP_APPEND,
      rich_listTheory.DROP_LENGTH_APPEND,
      venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def]
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
  strip_tac >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)` by
    (irule (cj 4 u2s_alloc_layout_code) >>
     qexistsl_tac [`a`, `ba`, `n`, `op`, `sb`] >> simp[]) >>
  drule_all u2s_alloc_layout_code >> strip_tac >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
    [STRING #"%" (toString sa.cs_next_var)]` >>
  `MEM inst (fn_insts func)` by simp[Abbr `inst`] >>
  `inst = mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
    [STRING #"%" (toString sa.cs_next_var)]` by simp[Abbr `inst`] >>
  drule_all u2s_alloc_safe >> strip_tac >>
  `sa.cs_next_var <= a.cs_next_var` by
    (mp_tac (Q.SPECL [`sz`, `sa`] exprLoweringPropsTheory.ci_mono_compile_alloc_buffer) >>
     simp[exprLoweringPropsTheory.ci_mono_def]) >>
  `local_ptrs_reserved cenv a` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `eval_operand op t = SOME (n2w X)` by
    (irule eval_operand_frame >> simp[] >> qexistsl_tac [`sa`, `s`] >> simp[]) >>
  drule_all u2s_alloc_control >> strip_tac >>
  drule loweringHaltTheory.compile_alloc_buffer_insts >> strip_tac >>
  `!out. u2s_safe ctx func cenv cx es a ba.buf_operand (w2n w) sz inst t out ==>
      stmt_state_rel ctx func cenv cx es out /\ wb_frame cenv es sa s out /\
      FLOOKUP out.vs_allocas sa.cs_next_id = SOME (w2n w,sz)` by
    (match_mp_tac u2s_safe_wb_tail >> simp[Abbr `inst`, venomInstTheory.mk_inst_def] >>
     metis_tac[ADD_COMM]) >>
  `!fuel. run_from fuel ctx fn s =
      run_from fuel ctx fn (t with vs_inst_idx := LENGTH a.cs_current_insts)` by
    (gen_tac >> irule u2s_alloc_continue >>
     conj_tac >-
       (qexistsl_tac [`<|bb_label := a.cs_current_bb;
          bb_instructions := a.cs_current_insts ++ u2s_setup a op ba.buf_operand|>`,
          `u2s_setup a op ba.buf_operand`] >>
        simp_tac (srw_ss()) [] >> metis_tac[]) >>
     qexistsl_tac [`ba`, `sa`, `sz`] >> metis_tac[]) >>
  `gas_marked_path F ctx fn s 0
     (OK (t with vs_inst_idx := LENGTH a.cs_current_insts))` by
    (qspecl_then [`sz`, `sa`, `ba`, `a`, `fn`, `s`,
       `<|bb_label := a.cs_current_bb;
          bb_instructions := a.cs_current_insts ++ u2s_setup a op ba.buf_operand|>`,
       `u2s_setup a op ba.buf_operand`, `t`, `ctx`] mp_tac u2s_alloc_path >>
     impl_tac >- (simp_tac (srw_ss()) [] >> metis_tac[]) >> simp[]) >>
  qexistsl_tac [`w2n w`, `t`, `t with vs_inst_idx := LENGTH a.cs_current_insts`, `inst`] >>
  simp_tac (srw_ss()) [u2s_safe_index] >>
  conj_tac >- metis_tac[u2s_safe_index] >>
  `eval_operand op (t with vs_inst_idx := LENGTH a.cs_current_insts) = SOME (n2w X)` by
    (qpat_x_assum `eval_operand op t = _` mp_tac >>
     Cases_on `op` >>
     simp_tac (srw_ss()) [venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def]) >>
  `inst.inst_opcode = ALLOCA` by
    simp_tac (srw_ss()) [Abbr `inst`, venomInstTheory.mk_inst_def] >>
  metis_tac[]
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
  strip_tac >> drule_all u2s_alloc_ready_path >> metis_tac[]
QED

Theorem u2s_alloc_vv_path:
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
  strip_tac >> drule compile_uint2str_layout >> strip_tac >>
  drule_all u2s_alloc_ready_path >> strip_tac >>
  mp_tac (Q.INST [`s` |-> `ready`, `buf` |-> `ba.buf_operand`, `ty` |-> `tv`,
                  `sz` |-> `sz + n`]
    u2s_setup_entry_path) >>
  impl_tac >- (simp[] >> metis_tac[]) >> strip_tac >>
  rename1 `val_in_memory tv _ _ t.vs_memory` >>
  `stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es sa s t /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (b,sz + n)` by metis_tac[] >>
  `w2n (n2w (b+n-LENGTH (num_to_dec_string X)):bytes32) =
    b+n-LENGTH (num_to_dec_string X)` by
    (simp[wordsTheory.w2n_n2w] >> irule LESS_MOD >> decide_tac) >>
  `sa.cs_next_id < sb.cs_next_id` by
    (mp_tac (Q.SPECL [`sz + n`, `sa`] exprLoweringPropsTheory.ci_mono_compile_alloc_buffer) >>
     simp[exprLoweringPropsTheory.ci_mono_def] >> strip_tac >>
     gvs[u2s_layout_def, u2s_end_def]) >>
  qexists_tac `t` >>
  conj_tac >- (irule u2s_path_then >> qexists_tac `ready` >> simp[]) >>
  reverse conj_tac >- gvs[u2s_layout_def, u2s_end_def] >>
  irule vv_post_allocated_memory_intro >> simp[] >>
  qexistsl_tac [`sa.cs_next_id`, `b`, `sz + n`] >> simp[] >>
  qpat_x_assum `u2s_safe _ _ _ _ _ _ _ _ _ _ _ t` mp_tac >>
  simp_tac (srw_ss()) [u2s_safe_def] >> rpt strip_tac >>
  first_x_assum drule >> decide_tac
QED

Theorem u2s_alloc_vv_exit:
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
  strip_tac >> mp_tac u2s_alloc_vv_path >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >> qexists_tac `t` >> simp[] >> metis_tac[u2s_path_continue]
QED

Theorem u2s_alloc_vv_frag:
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
  strip_tac >> simp[frag_exec_def] >> rpt strip_tac >>
  drule_all u2s_alloc_vv_exit >> metis_tac[]
QED

Theorem compile_uint2str_singleton:
  compile_expr cenv ty (Builtin ann (Uint2Str n) [e]) sa =
    (let (v,sm) = lower_value compile_expr cenv ty e sa in
     as_ptr_val ann LocMemory (compile_uint2str v n (type_memory_bytes cenv ann) sm))
Proof
  `~names_builtin (Uint2Str n) [e]` by
    (Cases_on `e` >> simp[names_builtin_def]) >>
  simp[exprSimHypsDefsTheory.compile_expr_builtin_dispatch] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 exprLoweringTheory.compile_expr_raw_def)),
       exprLoweringTheory.compile_builtin_dispatch_body_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp[exprBopLoweringTheory.lower_value_child_call,
       vyperASTTheory.expr_size_def, list_size_def, basicSizeTheory.option_size_def]
QED

Theorem uint2str_suffix_appends:
  cs_appends (compile_uint2str op n sz)
Proof
  `!n. cs_appends (compile_alloc_buffer n)` by
    (rw[contextTheory.compile_alloc_buffer_def] >>
     irule cs_appends_bind >> simp[cs_appends_emit_helpers, cs_appends_return]) >>
  rw[compile_uint2str_def] >>
  rpt (FIRST [irule cs_appends_bind, irule cs_appends_ignore_bind] >>
       rw[cs_appends_prims, cs_appends_emit_helpers, cs_appends_return])
QED

Theorem uint2str_source_result:
  builtin_result cx acc ann (Uint2Str n) ts [IntV i] =
    INL (StringV (num_to_dec_string (Num i)))
Proof
  simp[builtin_result_def, vyperContextTheory.evaluate_builtin_def]
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
  strip_tac >> rewrite_tac[expr_vv_sim_def] >> rpt strip_tac >>
  `!k. bt <> Slice k` by
    (strip_tac >> strip_tac >> gvs[vyperContextTheory.builtin_args_length_ok_def]) >>
  `expr_body_pre cenv cx env e es` by
    (drule exprSimSourceTheory.expr_body_pre_builtin_arg >>
     disch_then irule >> gvs[expr_body_pre_def]) >>
  qpat_x_assum `!sa sb vv. _` drule >> strip_tac >>
  `cs_appends (code x)` by simp[] >>
  drule_all hash_unary_suffix_cut >> strip_tac >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[exprSimSourceTheory.expr_body_pre_gas_admissible] >>
  `eval_expr cx (Builtin ann bt [e]) =
   bind (bind (eval_expr cx e) (read_result cx))
     (\v es. ((case builtin_result cx es.accounts ann bt [expr_type e] [v] of
                 INL w => INL (Value w) | INR exc => INR exc), es))` by
    (irule eval_expr_unary_builtin_action >> simp[]) >>
  qpat_x_assum `gas_admissible (eval_expr _ _) _ _`
    (mp_tac o REWRITE_RULE [gas_admissible_def]) >>
  asm_rewrite_tac[] >> strip_tac >>
  irule expr_sim_suffix >>
  first_assum (irule_at (Pat `expr_sim _ _ _ _ _ _ _`)) >>
  first_assum (irule_at (Pat `lower_value _ _ _ _ _ = _`)) >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> Cases_on `exc` >> Cases_on `r` >> gvs[expr_exit_def] >>
      rename1 `Error err` >> Cases_on `err` >> gvs[expr_exit_def]) >>
  rpt strip_tac >>
  drule_at (Pat `bind _ _ _ = _`)
    (CONV_RULE (DEPTH_CONV ETA_CONV) expr_body_pre_base_result) >>
  disch_then (qspecl_then [`env`, `cenv`] mp_tac) >>
  simp[] >> strip_tac >>
  `expr_res_ok (builtin_result cx ee.accounts ann bt [expr_type e] [v])` by
    (qpat_x_assum `!gs res ee. _` (qspec_then `gs` mp_tac) >> simp[vyperStateTheory.bind_def] >>
     Cases_on `builtin_result cx ee.accounts ann bt [expr_type e] [v]` >>
     gvs[expr_vv_res_ok_def, expr_res_ok_def]) >>
  qpat_x_assum `!sa sm sb x vv s0 v gs es' s. _` drule_all >> strip_tac >>
  `ee with gas_obs := [] = ee` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  qexists_tac `REPLICATE n F` >>
  rewrite_tac[gas_summary_at_def, gas_marked_exec_def] >>
  qexistsl_tac [`case builtin_result cx ee.accounts ann bt [expr_type e] [v] of
                   INL w => INL (Value w) | INR exc => INR exc`, `ee`, `r`] >>
  simp[expr_exit_success_map] >>
  Cases_on `builtin_result cx ee.accounts ann bt [expr_type e] [v]` >> gvs[]
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
  strip_tac >> irule frag_exec_conseq >> goal_assum (drule_at Any) >>
  simp[] >> rpt strip_tac >> metis_tac[vv_post_prefix_frame]
QED

Theorem uint2str_result_memory_bounds:
  X < dimword (:256) /\ 78 <= n ==>
  val_wf (BaseTV (StringT n)) (StringV (num_to_dec_string X)) /\
  val_footprint (BaseTV (StringT n)) (StringV (num_to_dec_string X)) =
    32 + LENGTH (num_to_dec_string X) /\ n + 32 <= 32 + 32 * word_size n
Proof
  strip_tac >>
  `LENGTH (num_to_dec_string X) <= 78` by
    (irule (cj 2 uint256_decimal_length) >> gvs[wordsTheory.dimword_def]) >>
  qspec_then `n` assume_tac le_word_size_mul >>
  simp[valueEncodingTheory.val_wf_def, valueEncodingTheory.type_memory_size_def,
       val_footprint_def] >> decide_tac
QED

Theorem vv_post_located_mk_ptr:
  vv_post ctx func cenv cx e es sa sb s0 es' tv (LocatedValue ty p) s <=>
  vv_post ctx func cenv cx e es sa sb s0 es' tv
    (LocatedValue ty (mk_ptr p.ptr_operand p.ptr_location)) s
Proof
  simp[vv_post_def, vv_holds_def, vv_at_def, contextTheory.mk_ptr_def]
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
  strip_tac >>
  `is_word_type (expr_type e)` by simp[is_word_type_def] >>
  drule_all exprSimSourceTheory.expr_body_pre_lower_value_word_shape >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es' s` by metis_tac[expr_post_state] >>
  `IS_SOME (evaluate_type (get_tenv cx) (expr_type e))` by
    metis_tac[expr_body_pre_type_evaluates] >>
  `eval_operand x s = SOME (n2w X)` by
    (drule expr_post_word_operand >>
     simp[vyperValueTheory.evaluate_type_def, is_word_type_def,
          loweringSliceTheory.word_value_def, valueEncodingTheory.val_to_w256_def,
          integer_wordTheory.i2w_pos]) >>
  mp_tac (Q.INST [`X` |-> `X`, `n` |-> `n`] uint2str_result_memory_bounds) >>
  simp[] >> strip_tac >>
  irule vv_post_prefix_frag >> simp[] >>
  qexistsl_tac [`es'`, `s`] >> simp[] >>
  conj_tac >- metis_tac[expr_post_frame] >>
  irule (u2s_alloc_vv_frag |> Q.INST
    [`e` |-> `Builtin (BaseT (StringT n)) (Uint2Str n) [e]`]
    |> ONCE_REWRITE_RULE [vv_post_located_mk_ptr]
    |> SRULE [vyperASTTheory.expr_type_def]) >>
  simp[vyperASTTheory.expr_type_def, is_word_type_def,
       vyperValueTheory.evaluate_type_def] >>
  conj_tac
  >- (qexistsl_tac [`x`, `sz`] >> simp[]) >>
  `word_size n <= n` by (irule vyperArithTheory.word_size_le >> decide_tac) >>
  simp[vyperValueTheory.type_slot_size_def] >> decide_tac
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
  strip_tac >>
  `expr_body_pre cenv cx env e es` by
    (drule exprSimSourceTheory.expr_body_pre_builtin_arg >> disch_then irule >> gvs[expr_body_pre_def]) >>
  `IS_SOME (evaluate_type (get_tenv cx) (expr_type e))` by
    metis_tac[expr_body_pre_type_evaluates] >>
  `k <= 256` by gvs[vyperValueTheory.evaluate_type_def] >>
  drule_all exprSimWordBuiltinsTheory.uint_value_word_rep >> strip_tac >>
  qpat_x_assum `v = _` SUBST_ALL_TAC >>
  qmatch_goalsub_abbrev_tac `IntV (&X)` >>
  `X < dimword (:256)` by simp[Abbr `X`, wordsTheory.w2n_lt] >>
  gvs[uint2str_source_result] >>
  Cases_on `compile_uint2str x n (type_memory_bytes cenv (BaseT (StringT n))) sm` >>
  gvs[exprLoweringTheory.as_ptr_val_def, contextTheory.mk_ptr_def] >>
  irule (SRULE [contextTheory.mk_ptr_def] uint2str_numeric_suffix) >>
  goal_assum (drule_at Any) >> simp[] >>
  `type_memory_bytes cenv (BaseT (StringT n)) < 2 ** 64` by
    metis_tac[uint2str_body_capacity] >>
  `n <= 32 * word_size n` by simp[le_word_size_mul] >>
  simp[type_memory_bytes_def, vfmConstantsTheory.word_size_def, wordsTheory.dimword_def] >>
  conj_tac >- metis_tac[forced_eval_expr_preserves_scopes_dom] >>
  gvs[type_memory_bytes_def, vfmConstantsTheory.word_size_def] >>
  conj_tac >- metis_tac[] >>
  qexists_tac `32 * ((n + 31) DIV 32) + 32` >> simp[] >> metis_tac[]
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
  strip_tac >>
  `is_word_type (expr_type e)` by simp[is_word_type_def] >>
  drule_all exprSimSourceTheory.expr_body_pre_lower_value_word_shape >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es' s` by metis_tac[expr_post_state] >>
  `IS_SOME (evaluate_type (get_tenv cx) (expr_type e))` by
    metis_tac[expr_body_pre_type_evaluates] >>
  `eval_operand x s = SOME (n2w X)` by
    (drule expr_post_word_operand >>
     simp[vyperValueTheory.evaluate_type_def, is_word_type_def,
          loweringSliceTheory.word_value_def, valueEncodingTheory.val_to_w256_def,
          integer_wordTheory.i2w_pos]) >>
  mp_tac (Q.INST [`X` |-> `X`, `n` |-> `n`] uint2str_result_memory_bounds) >>
  simp[] >> strip_tac >>
  `word_size n <= n` by (irule vyperArithTheory.word_size_le >> decide_tac) >>
  mp_tac (u2s_alloc_vv_path |> Q.INST
    [`e` |-> `Builtin (BaseT (StringT n)) (Uint2Str n) [e]`, `op` |-> `x`,
     `sa` |-> `sm`, `fn` |-> `func`, `es` |-> `es'`, `tv` |-> `BaseTV (StringT n)`]
    |> ONCE_REWRITE_RULE [vv_post_located_mk_ptr]
    |> SRULE [vyperASTTheory.expr_type_def]) >>
  impl_tac
  >- (simp[is_word_type_def, vyperValueTheory.evaluate_type_def,
           vyperValueTheory.type_slot_size_def] >> decide_tac) >>
  strip_tac >> qexists_tac `t` >> simp[] >>
  irule vv_post_prefix_frame >>
  first_assum (irule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> metis_tac[expr_post_frame]
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
  strip_tac >>
  `expr_body_pre cenv cx env e es` by
    (drule exprSimSourceTheory.expr_body_pre_builtin_arg >> disch_then irule >> gvs[expr_body_pre_def]) >>
  `MAP FDOM es.scopes = MAP FDOM es'.scopes` by
    (drule (CONV_RULE (DEPTH_CONV ETA_CONV) forced_eval_expr_preserves_scopes_dom) >>
     simp[]) >>
  `IS_SOME (evaluate_type (get_tenv cx) (expr_type e))` by
    metis_tac[expr_body_pre_type_evaluates] >>
  `k <= 256` by gvs[vyperValueTheory.evaluate_type_def] >>
  drule_all exprSimWordBuiltinsTheory.uint_value_word_rep >> strip_tac >>
  qpat_x_assum `v = _` SUBST_ALL_TAC >>
  qmatch_goalsub_abbrev_tac `IntV (&X)` >>
  `X < dimword (:256)` by simp[Abbr `X`, wordsTheory.w2n_lt] >>
  `?out. compile_uint2str x n (type_memory_bytes cenv (BaseT (StringT n))) sm =
           (out,sb) /\
         vv = LocatedValue (BaseT (StringT n)) (mk_ptr out LocMemory)` by
    (Cases_on `compile_uint2str x n (type_memory_bytes cenv (BaseT (StringT n))) sm` >>
     gvs[exprLoweringTheory.as_ptr_val_def]) >>
  `type_memory_bytes cenv (BaseT (StringT n)) < 2 ** 64` by
    metis_tac[uint2str_body_capacity] >>
  `n <= 32 * word_size n` by simp[le_word_size_mul] >>
  mp_tac (Q.INST [`sz` |-> `type_memory_bytes cenv (BaseT (StringT n))`]
    uint2str_numeric_path) >>
  impl_tac
  >- (gvs[type_memory_bytes_def, vfmConstantsTheory.word_size_def,
          wordsTheory.dimword_def]) >>
  strip_tac >> qexistsl_tac [`0`, `OK t`] >>
  gvs[uint2str_source_result]
QED

Theorem compile_uint2str_typed_vv_sim:
  expr_body_pre cenv cx env (Builtin ann (Uint2Str n) [e]) es /\
  expr_sim ctx func cenv cx ty e es ==>
  expr_vv_sim ctx func cenv cx ty (Builtin ann (Uint2Str n) [e]) es
Proof
  strip_tac >>
  `well_typed_expr env (Builtin ann (Uint2Str n) [e])` by
    gvs[expr_body_pre_def] >>
  drule uint2str_expr_types >> strip_tac >> gvs[] >>
  irule compile_typed_unary_builtin_vv_sim_with_initial_rel >>
  simp[vyperContextTheory.builtin_args_length_ok_def] >>
  qexistsl_tac [`\x sm. as_ptr_val (BaseT (StringT n)) LocMemory
      (compile_uint2str x n (type_memory_bytes cenv (BaseT (StringT n))) sm)`, `env`] >>
  simp[vyperContextTheory.builtin_args_length_ok_def] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_assum `expr_type e = _`
        (fn th => irule (REWRITE_RULE [th] uint2str_typed_path)) >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      gvs[compile_uint2str_singleton] >> pairarg_tac >> gvs[] >> metis_tac[]) >>
  rpt strip_tac >> simp[cs_appends_def] >> rpt strip_tac >>
  Cases_on `compile_uint2str x n (type_memory_bytes cenv (BaseT (StringT n))) sm` >>
  gvs[exprLoweringTheory.as_ptr_val_def] >>
  irule (SRULE [cs_appends_def] uint2str_suffix_appends) >>
  goal_assum (drule_at Any)
QED

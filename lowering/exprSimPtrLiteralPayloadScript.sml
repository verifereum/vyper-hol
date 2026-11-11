(* Functional memory boundary for the same literal payload execution. *)
Theory exprSimPtrLiteralPayload
Ancestors
  exprSimPtrLiteralChunks exprSimPtrLiteralOps exprSimLiteralBuffer
  exprLowering exprLoweringProps fragExec venomExecSemantics venomInst
  venomState valueEncoding valueEncodingDefs valueEncodingProofs valueEncodingProps
  venomMemProps immutableMemoryFrame compileEnv emitHelper freshWrites
  words list rich_list finite_map vfmConstants

Theorem literal_payload_padded_length[local]:
  !bs:word8 list. bs <> [] ==>
    LENGTH (TAKE 32 (bs ++ REPLICATE 31 0w)) = 32
Proof
  rpt strip_tac >> simp[LENGTH_TAKE_EQ] >> Cases_on `bs` >> gvs[]
QED

Theorem literal_payload_padded_store[local]:
  !bs off s. bs <> [] ==>
    mem_bytes_at off 32
      (mstore off (word_of_bytes T (0w:bytes32)
        (TAKE 32 (bs ++ REPLICATE 31 0w))) s).vs_memory =
    TAKE 32 (bs ++ REPLICATE 31 0w)
Proof
  rpt strip_tac >> rewrite_tac[mem_bytes_at_mstore_same] >>
  irule word_bytes_roundtrip_256 >> irule literal_payload_padded_length >> simp[]
QED

Theorem literal_payload_chunk_prefix[local]:
  !bs off s. bs <> [] ==>
    mem_bytes_at off (MIN 32 (LENGTH bs))
      (mstore off (word_of_bytes T (0w:bytes32)
        (TAKE 32 (bs ++ REPLICATE 31 0w))) s).vs_memory = TAKE 32 bs
Proof
  rpt strip_tac >> drule literal_payload_padded_store >>
  disch_then (qspecl_then [`off`, `s`] mp_tac) >>
  strip_tac >> irule LIST_EQ >> simp[LENGTH_TAKE_EQ, arithmeticTheory.MIN_DEF] >>
  qx_gen_tac `i` >> strip_tac >>
  `EL i (mem_bytes_at off 32
      (mstore off (word_of_bytes T (0w:bytes32)
        (TAKE 32 (bs ++ REPLICATE 31 0w))) s).vs_memory) =
    EL i (TAKE 32 (bs ++ REPLICATE 31 0w))` by simp[] >>
  gvs[EL_mem_bytes_at, EL_TAKE, EL_APPEND1]
QED

Theorem literal_payload_assemble[local]:
  !a bs m.
    mem_bytes_at a (MIN 32 (LENGTH bs)) m = TAKE 32 bs /\
    mem_bytes_at (a+32) (LENGTH (DROP 32 bs)) m = DROP 32 bs ==>
    mem_bytes_at a (LENGTH bs) m = bs
Proof
  rpt strip_tac >> Cases_on `LENGTH bs < 32`
  >- gvs[arithmeticTheory.MIN_DEF, TAKE_LENGTH_TOO_LONG] >>
  `MIN 32 (LENGTH bs) = 32` by
    (simp[arithmeticTheory.MIN_DEF] >> decide_tac) >>
  `32 + (LENGTH bs - 32) = LENGTH bs` by decide_tac >>
  qspec_then `a` mp_tac mem_bytes_at_split_padded >>
  disch_then (qspecl_then [`32`, `LENGTH bs - 32`, `m`] mp_tac) >>
  gvs[LENGTH_DROP] >> simp[TAKE_DROP]
QED

Theorem literal_payload_head_functional:
  emit_op ADD [Var p; Lit (n2w off)] sa = (dst,sm) /\
  emit_void MSTORE [dst; Lit value] sm = ((),sb) /\
  lookup_var p s = SOME (n2w b) /\ b+off < dimword (:256) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\ sb.cs_next_var = sa.cs_next_var + 1 /\
  sa.cs_next_id <= sb.cs_next_id /\
  t.vs_memory = (mstore (b+off) value s).vs_memory /\
  LENGTH s.vs_memory <= LENGTH t.vs_memory /\
  (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >> drule_all literal_chunk_head_shape >> strip_tac >>
  drule literal_chunk_pair_run >>
  disch_then (qspecl_then [`value`, `off`, `sa.cs_next_id`, `x`] mp_tac) >>
  simp[] >> strip_tac >>
  gvs[w2n_n2w, arithmeticTheory.LESS_MOD] >>
  simp[mstore_def, update_var_def, immutable_mstore_capacity,
       arithmeticTheory.MAX_DEF, lookup_var_def, FLOOKUP_UPDATE] >>
  metis_tac[]
QED

Theorem literal_payload_chunks_shape:
  !ptr bs off sa sb.
    compile_store_byte_chunks ptr bs off sa = ((),sb) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb
Proof
  recInduct compile_store_byte_chunks_ind >> rpt gen_tac >> strip_tac
  >- gvs[compile_store_byte_chunks_def, comp_return_def,
         emitted_insts_def, same_blocks_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  rename1 `compile_store_byte_chunks data_ptr (hd::tl) offset sa = ((),sb)` >>
  qpat_x_assum `compile_store_byte_chunks _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [Once compile_store_byte_chunks_def, LET_THM,
                   comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >> strip_tac >>
  rename1 `emit_void MSTORE _ mid = (u,post)` >> Cases_on `u` >>
  first_x_assum (qspecl_then
    [`TAKE 32 (hd::tl ++ REPLICATE 31 0w)`,
     `word_of_bytes T 0w (TAKE 32 (hd::tl ++ REPLICATE 31 0w))`] mp_tac) >>
  simp_tac bool_ss [] >> disch_then drule >> strip_tac >>
  drule_all literal_chunk_head_shape >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa post ++ emitted_insts post sb` by
    (irule emitted_insts_append >> simp[]) >>
  simp[] >> metis_tac[same_blocks_trans, APPEND_ASSOC]
QED

Theorem literal_chunks_functional:
  !ptr bs off sa sb p s b t.
    compile_store_byte_chunks ptr bs off sa = ((),sb) /\ ptr = Var p /\
    not_fresh_at sa p /\ lookup_var p s = SOME (n2w b) /\
    b+off+32*word_size (LENGTH bs) < dimword (:256) /\
    run_inst_seq (emitted_insts sa sb) s = OK t ==>
    mem_bytes_at (b+off) (LENGTH bs) t.vs_memory = bs /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!a len. a+len <= b+off \/ b+off+32*word_size (LENGTH bs) <= a ==>
      mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory)
Proof
  recInduct compile_store_byte_chunks_ind >> rpt gen_tac >> strip_tac
  >- gvs[compile_store_byte_chunks_def, comp_return_def,
         emitted_insts_def, run_inst_seq_def, mem_bytes_at_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  rename1 `compile_store_byte_chunks data_ptr (hd::tl) offset sa = ((),sb)` >>
  qpat_x_assum `compile_store_byte_chunks _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [Once compile_store_byte_chunks_def, LET_THM,
                   comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >> strip_tac >>
  rename1 `emit_void MSTORE _ mid = (u,post)` >> Cases_on `u` >>
  drule_all literal_chunk_head_shape >> strip_tac >>
  first_x_assum (qspecl_then
    [`TAKE 32 (hd::tl ++ REPLICATE 31 0w)`,
     `word_of_bytes T 0w (TAKE 32 (hd::tl ++ REPLICATE 31 0w))`] mp_tac) >>
  simp_tac bool_ss [] >> disch_tac >> gvs[] >>
  `32 + 32*word_size (LENGTH (DROP 32 (hd::tl))) =
   32*word_size (LENGTH (hd::tl))` by
    (rewrite_tac[LENGTH_DROP] >> irule literal_chunk_span >> simp[]) >>
  qpat_x_assum `32 + _ = _` (assume_tac o SIMP_RULE (srw_ss()) []) >>
  `b+offset+32 < dimword (:256)` by decide_tac >>
  qmatch_asmsub_abbrev_tac `word_of_bytes T 0w chunk` >>
  qabbrev_tac `value:bytes32 = word_of_bytes T 0w chunk` >>
  qabbrev_tac `head = mstore (w2n (n2w (b+offset):bytes32)) value
    (update_var x (n2w (b+offset)) s)` >>
  `run_inst_seq (emitted_insts sa post) s = OK head` by
    (drule literal_chunk_pair_run >>
     disch_then (qspecl_then [`value`, `offset`, `sa.cs_next_id`, `x`] mp_tac) >>
     simp[Abbr `head`, Abbr `value`, w2n_n2w, arithmeticTheory.LESS_MOD]) >>
  `b+offset < dimword (:256)` by decide_tac >>
  drule_all literal_payload_head_functional >> strip_tac >>
  drule literal_payload_chunks_shape >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa post ++ emitted_insts post sb` by
    (irule emitted_insts_append >> simp[]) >>
  `run_inst_seq (emitted_insts post sb) head = OK t` by
    (drule run_inst_seq_append >>
     disch_then (qspec_then `emitted_insts post sb` assume_tac) >> gvs[]) >>
  `not_fresh_at post p` by
    (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `lookup_var p head = SOME (n2w b)` by metis_tac[] >>
  `b+(offset+32)+32*word_size (LENGTH (DROP 32 (hd::tl))) < dimword (:256)` by
    (simp[LENGTH_DROP] >> decide_tac) >>
  `b + (offset + (32*word_size (SUC (LENGTH tl)-32)+32)) < dimword (:256)` by
    decide_tac >>
  qpat_x_assum `!sa' sb' s' b' t'. _` drule_all >> strip_tac >>
  suspend "compose"
QED

Resume literal_chunks_functional[compose]:
  `mem_bytes_at (b+offset) (MIN 32 (LENGTH (hd::tl))) t.vs_memory = TAKE 32 (hd::tl)` by
    (`mem_bytes_at (b+offset) (MIN 32 (LENGTH (hd::tl))) t.vs_memory =
      mem_bytes_at (b+offset) (MIN 32 (LENGTH (hd::tl))) head.vs_memory` by
      (qpat_x_assum `!a len. _ ==> mem_bytes_at _ _ t.vs_memory = _` irule >>
       disj1_tac >> simp[arithmeticTheory.MIN_DEF]) >>
     asm_simp_tac bool_ss [] >>
     qpat_x_assum `head.vs_memory = _` SUBST1_TAC >>
     qspec_then `hd::tl` mp_tac literal_payload_chunk_prefix >>
     disch_then (qspecl_then [`b+offset`, `s`] mp_tac) >>
     simp[Abbr `value`, Abbr `chunk`]) >>
  conj_tac
  >- (qspec_then `b+offset` mp_tac literal_payload_assemble >>
      disch_then (qspecl_then [`hd::tl`, `t.vs_memory`] mp_tac) >>
      asm_simp_tac bool_ss [GSYM arithmeticTheory.ADD_ASSOC, LENGTH, DROP, LENGTH_DROP] >> simp[]) >>
  conj_tac >- decide_tac >>
  conj_tac
  >- (qpat_x_assum `t with <|vs_memory := _; vs_vars := _|> = head`
       (mp_tac o AP_TERM ``\z. z with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>``) >>
      simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at post x'` by
        (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
      metis_tac[]) >>
  rpt gen_tac >> disch_tac >>
  `mem_bytes_at a len t.vs_memory = mem_bytes_at a len head.vs_memory` by
    (qpat_x_assum `!a len. _ ==> mem_bytes_at _ _ t.vs_memory = _` irule >>
     decide_tac) >>
  asm_simp_tac bool_ss [] >>
  qpat_x_assum `head.vs_memory = _` SUBST1_TAC >>
  irule mstore_mem_bytes_at_disjoint >> decide_tac
QED

Finalise literal_chunks_functional


Theorem literal_header_chunks_functional:
  compile_store_byte_chunks (Var p) bs 32 sh = ((),sb) /\
  not_fresh_at sh p /\ lookup_var p s = SOME (n2w b) /\
  b+32+32*word_size (LENGTH bs) < dimword (:256) /\
  run_inst_seq (mk_inst id MSTORE [Var p; Lit (n2w (LENGTH bs))] [] ::
    emitted_insts sh sb) s = OK t ==>
  mem_word_at b t.vs_memory = n2w (LENGTH bs) /\
  mem_bytes_at (b+32) (LENGTH bs) t.vs_memory = bs /\
  LENGTH s.vs_memory <= LENGTH t.vs_memory /\
  (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
  (!x. not_fresh_at sh x ==> lookup_var x t = lookup_var x s) /\
  (!a len. a+len <= b \/ b+32+32*word_size (LENGTH bs) <= a ==>
    mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory)
Proof
  strip_tac >>
  `b < dimword (:256)` by decide_tac >>
  `step_inst_base (mk_inst id MSTORE [Var p; Lit (n2w (LENGTH bs))] []) s =
     OK (mstore b (n2w (LENGTH bs)) s)` by
    (simp[step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def, eval_operand_def, w2n_n2w]) >>
  qpat_x_assum `run_inst_seq (_::_) _ = _` mp_tac >>
  simp[run_inst_seq_def, mk_inst_def, is_terminator_def] >> strip_tac >>
  `lookup_var p (mstore b (n2w (LENGTH bs)) s) = SOME (n2w b)` by
    simp[mstore_def, lookup_var_def] >>
  drule literal_chunks_functional >>
  disch_then (qspecl_then [`p`, `mstore b (n2w (LENGTH bs)) s`, `b`, `t`] mp_tac) >>
  simp[] >> strip_tac >>
  conj_tac
  >- (`mem_bytes_at b 32 t.vs_memory =
        mem_bytes_at b 32 (mstore b (n2w (LENGTH bs)) s).vs_memory` by
        (first_x_assum irule >> simp[]) >>
      `mem_word_at b t.vs_memory =
        mem_word_at b (mstore b (n2w (LENGTH bs)) s).vs_memory` by
        gvs[mem_word_at_def, mem_bytes_at_def] >>
      simp[mstore_mem_word_at_same]) >>
  conj_tac
  >- (`LENGTH s.vs_memory <= LENGTH (mstore b (n2w (LENGTH bs)) s).vs_memory` by
        simp[immutable_mstore_capacity, arithmeticTheory.MAX_DEF] >> decide_tac) >>
  conj_tac
  >- (qpat_x_assum `t with <|vs_memory := _; vs_vars := _|> = _`
        (mp_tac o AP_TERM ``\z. z with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>``) >>
      simp[mstore_def]) >>
  rpt gen_tac >> disch_tac >>
  `mem_bytes_at a len t.vs_memory =
    mem_bytes_at a len (mstore b (n2w (LENGTH bs)) s).vs_memory` by
    (qpat_x_assum `!a len. _` irule >> decide_tac) >>
  asm_simp_tac bool_ss [] >>
  irule mstore_mem_bytes_at_disjoint >> decide_tac
QED

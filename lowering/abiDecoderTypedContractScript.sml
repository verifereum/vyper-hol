(* Candidate recursive boundary: pure metadata and observations, never execution.
   Interface checkpoint C6.6.4.1, not a general decoder correctness theorem:
   - metadata is root agreement; descendants still need compatibility closure;
   - reservation constrains existing ALLOCA mappings and the initial frontier,
     not the total budget of future fresh sites or repeated loop executions;
   - canonical word/load agreement is derived below for Uint256;
   - singleton Bytes restrictions validate one consumer, not general member
     head/tail closure. Allocation separation at lower_abi_decode and recursive
     capacity accounting remain downstream proof obligations. *)
Theory abiDecoderTypedContract
Ancestors
  abiDecoderFrame abiDecodeRanges abiWrappedDecodeProps abiStaticLayoutProps
  abiCanonicalLoad vyperABI contractABI byte
  abiDecoderContract fragExec exprLoweringProps vyperTyping context
  abiEncoder emitHelper valueEncoding abiBoundaryChecks compileEnv
  emitHelperProps valueEncodingProps venomExecSemantics venomExecProofs venomInst

Theorem abi_decoder_dimindex[simp,local]: dimindex (:256) = 256
Proof
  CONV_TAC fcpLib.INDEX_CONV
QED

Definition abi_decoder_metadata_def:
  abi_decoder_metadata ce env ty tv di av v <=>
    evaluate_type env ty = SOME tv /\ value_has_type tv v /\
    di = type_to_abi_dec_info ce.ce_struct_fields ce ty /\
    has_type (vyper_to_abi_type env ty) av /\
    abi_to_vyper env ty av = SOME v /\
    type_memory_size tv = type_memory_bytes ce ty
End

(* These are actual ALLOCA instruction ids, not SSA names. A reserved entry
   may be reused by exec_alloca. New allocations start at vs_alloca_next;
   closing the total capacity budget under recursion is a later obligation. *)
Definition abi_decoder_reservation_def:
  abi_decoder_reservation first last b cap s <=>
    b + cap < dimword (:256) /\
    b <= s.vs_alloca_next /\ s.vs_alloca_next <= b + cap /\
    (!id off sz. first <= id /\ id < last /\
       FLOOKUP s.vs_allocas id = SOME (off,sz) ==>
       b <= off /\ off + sz <= b + cap)
End

Definition abi_decoder_ranges_def:
  abi_decoder_ranges opc hi src dst sb len d outsz b cap s <=>
    abi_decode_source_opcode opc /\
    eval_operand src s = SOME (n2w sb) /\
    eval_operand dst s = SOME (n2w d) /\
    sb + len < dimword (:256) /\ d + outsz < dimword (:256) /\
    (hi = Lit 0w \/ ?h. eval_operand hi s = SOME (n2w h) /\
                           sb + len <= h /\ h < dimword (:256)) /\
    (d + outsz <= b \/ b + cap <= d) /\
    (opc = MLOAD ==>
       abi_footprint_disjoint sb len [(d,outsz);(b,cap)])
End

Definition abi_decoder_pre_def:
  abi_decoder_pre ce env ty tv di av v st last src dst opc hi sb d b cap s <=>
    abi_decoder_metadata ce env ty tv di av v /\
    fresh_vars_wrt st s /\
    abi_decoder_reservation st.cs_next_id last b cap s /\
    abi_decoder_ranges opc hi src dst sb
      (LENGTH (enc (vyper_to_abi_type env ty) av)) d
      (type_memory_bytes ce ty) b cap s /\
    mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) av))
      (abi_decode_source opc s) = enc (vyper_to_abi_type env ty) av
End

Definition abi_decoder_post_def:
  abi_decoder_post tv v st' d outsz b cap s0 s <=>
    val_in_memory tv v d s.vs_memory /\ fresh_vars_wrt st' s /\
    (!op w. eval_operand op s0 = SOME w ==> eval_operand op s = SOME w) /\
    abi_decode_footprint_frame [(d,outsz);(b,cap)] s0 s
End

Theorem abi_decoder_frame_from_output:
  abi_decode_frame d n s t ==>
  abi_decode_footprint_frame [(d,n);(b,cap)] s t
Proof
  rw[abi_decode_frame_def, abi_decode_footprint_frame_def,
     abi_footprint_disjoint_def] >> metis_tac[]
QED

(* ABI-to-Vyper conversion followed by encoding is the valid inverse direction;
   it identifies the canonical word without assuming a source-value roundtrip. *)
Theorem abi_decoder_uint256_canonical_load:
  abi_decoder_pre ce env (BaseT (UintT 256)) (BaseTV (UintT 256))
    (DecPrimWord NoClamp) av (IntV (&w2n w)) st last src dst opc hi sb d b cap s ==>
  abi_decode_load opc (n2w sb : bytes32) s = w
Proof
  pure_rewrite_tac[abi_decoder_pre_def, abi_decoder_metadata_def,
                   abi_decoder_ranges_def] >> rpt strip_tac >>
  `av = NumV (w2n w)` by
    (drule_all (cj 1 abi_to_vyper_vyper_to_abi) >>
     simp[vyper_to_abi_def, vyper_to_abi_base_def]) >>
  gvs[vyper_to_abi_type_def, enc_def, enc_number_def] >>
  `sb < dimword (:256)` by decide_tac >>
  asm_simp_tac bool_ss [abi_decode_load_bytes] >>
  asm_rewrite_tac[] >> irule word_of_bytes_word_to_bytes >>
  simp[dividesTheory.divides_def]
QED

Theorem abi_decoder_typed_word_sequence:
  compile_abi_decode_to_buf dst src opc hi (DecPrimWord NoClamp) st = ((),st') /\
  abi_decoder_pre ce env (BaseT (UintT 256)) (BaseTV (UintT 256))
    (DecPrimWord NoClamp) av (IntV (&w2n (w:bytes32))) st last src dst opc hi sb d b cap s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
      abi_decoder_post (BaseTV (UintT 256)) (IntV (&w2n w)) st'
        d 32 b cap s t
Proof
  strip_tac >>
  `abi_decode_load opc (n2w sb : bytes32) s = w` by
    (drule_all abi_decoder_uint256_canonical_load >> simp[]) >>
  qhdtm_x_assum `abi_decoder_pre` mp_tac >>
  pure_rewrite_tac[abi_decoder_pre_def, abi_decoder_ranges_def] >> rpt strip_tac >>
  `d < dimword (:256)` by decide_tac >>
  drule_all abi_decode_word_sequence >> strip_tac >>
  qexists_tac `s'` >>
  gvs[abi_decoder_post_def] >>
  irule abi_decoder_frame_from_output >> simp[]
QED

Theorem abi_decoder_word_shape:
  compile_abi_decode_to_buf dst src opc hi (DecPrimWord NoClamp) st = ((),st') /\
  abi_decode_source_opcode opc ==>
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts st'.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')
Proof
  strip_tac >> gvs[] >>
  gvs[compile_abi_decode_to_buf_def, compile_abi_decode_static_def,
      compile_abi_clamp_basetype_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
      fresh_id_def, emit_def, emitted_insts_def,
      rich_listTheory.DROP_LENGTH_APPEND, is_terminator_def,
      rich_listTheory.IS_PREFIX_APPEND] >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
  gvs[rich_listTheory.DROP_LENGTH_APPEND, is_terminator_def,
      abi_decode_source_opcode_def, mk_inst_def]
QED

Theorem abi_decoder_typed_word_fragment:
  compile_abi_decode_to_buf dst src opc hi (DecPrimWord NoClamp) st = ((),st') ==>
  frag_exec ctx st st'
    (\s. abi_decoder_pre ce env (BaseT (UintT 256)) (BaseTV (UintT 256))
       (DecPrimWord NoClamp) av (IntV (&w2n (w:bytes32))) st last src dst opc hi sb d b cap s)
    (\t. ?s. abi_decoder_pre ce env (BaseT (UintT 256)) (BaseTV (UintT 256))
       (DecPrimWord NoClamp) av (IntV (&w2n w)) st last src dst opc hi sb d b cap s /\
       abi_decode_load opc (n2w sb : bytes32) s = w /\
       abi_decoder_post (BaseTV (UintT 256)) (IntV (&w2n w)) st' d 32 b cap s t)
    (K F)
Proof
  reverse (Cases_on `abi_decode_source_opcode opc`)
  >- simp[frag_exec_def, abi_decoder_pre_def, abi_decoder_ranges_def] >>
  strip_tac >> drule_all abi_decoder_word_shape >> strip_tac >>
  irule frag_exec_run_inst_seq >> simp[] >> rpt strip_tac >>
  drule_all abi_decoder_typed_word_sequence >> strip_tac >>
  `abi_decode_load opc (n2w sb : bytes32) s = w` by
    (drule_all abi_decoder_uint256_canonical_load >> simp[]) >>
  qexists_tac `t` >> simp[] >> qexists_tac `s` >>
  gvs[abi_decoder_post_def, fresh_vars_wrt_def,
      venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
      abi_decode_footprint_frame_def] >>
  rpt gen_tac >> strip_tac >>
  `eval_operand op (t with vs_inst_idx := LENGTH st'.cs_current_insts) =
   eval_operand op t` by
    (Cases_on `op` >> simp[venomStateTheory.eval_operand_def,
                           venomStateTheory.lookup_var_def]) >>
  metis_tac[]
QED

Theorem abi_decoder_typed_empty_fragment:
  compile_abi_decode_to_buf dst src opc (Lit 0w) (DecComplex F []) st = ((),st') ==>
  frag_exec ctx st st'
    (abi_decoder_pre ce env (TupleT []) (TupleTV []) (DecComplex F [])
       (ListV []) (ArrayV (TupleV [])) st last src dst opc (Lit 0w) sb d b cap)
    (\t. ?s. abi_decoder_pre ce env (TupleT []) (TupleTV []) (DecComplex F [])
       (ListV []) (ArrayV (TupleV [])) st last src dst opc (Lit 0w) sb d b cap s /\
       abi_decoder_post (TupleTV []) (ArrayV (TupleV [])) st' d 0 b cap s t)
    (K F)
Proof
  simp[compile_abi_decode_to_buf_def, comp_return_def] >> strip_tac >> gvs[] >>
  irule frag_exec_refl >> rpt strip_tac >> BETA_TAC >> qexists_tac `s` >>
  gvs[abi_decoder_pre_def, abi_decoder_post_def, val_in_memory_def,
      abi_decode_footprint_frame_refl]
QED

(* Single-element memory projection is offset zero even for dynamic Bytes.
   This is not a claim that the ABI source payload begins at offset zero. *)
Theorem abi_decoder_wrapped_bytes_post:
  abi_decoder_post (TupleTV [BaseTV (BytesT (Dynamic n))])
    (ArrayV (TupleV [BytesV bs])) st' d outsz b cap s0 s ==>
  abi_decoder_post (BaseTV (BytesT (Dynamic n))) (BytesV bs)
    st' d outsz b cap s0 s
Proof
  simp[abi_decoder_post_def, val_in_memory_singleton_tuple]
QED

Theorem abi_decoder_singleton_metadata_child:
  abi_decoder_metadata ce env (TupleT [ty]) (TupleTV [tv]) di
    (ListV [av]) (ArrayV (TupleV [v])) ==>
  abi_decoder_metadata ce env ty tv
    (type_to_abi_dec_info ce.ce_struct_fields ce ty) av v
Proof
  simp[abi_decoder_metadata_def, vyperValueTheory.evaluate_type_def,
       value_has_type_def, abi_to_vyper_singleton_tuple,
       vyperABITheory.vyper_to_abi_type_def, contractABITheory.has_type_def,
       type_memory_size_def, type_memory_bytes_def, AllCaseEqs()]
QED

Theorem abi_decoder_child_ranges:
  abi_decoder_ranges opc hi src dst sb len d outsz b cap s /\
  delta + childlen <= len /\
  eval_operand childsrc s = SOME (n2w (sb + delta)) ==>
  abi_decoder_ranges opc hi childsrc dst (sb + delta) childlen d outsz b cap s
Proof
  rw[abi_decoder_ranges_def] >>
  gvs[abi_footprint_disjoint_def, DISJ_IMP_THM, FORALL_AND_THM] >>
  TRY (first_assum ACCEPT_TAC) >>
  TRY (disj2_tac >> qexists_tac `h` >> simp[] >> decide_tac) >>
  TRY (rpt gen_tac >> strip_tac >> first_x_assum drule >> strip_tac >> decide_tac) >>
  decide_tac
QED

(* The source restriction uses canonical runtime bytes only. It imposes no
   observation on padding beyond the encoded payload. *)
Theorem abi_decoder_source_subwindow:
  !sb prefix payload suffix mem.
  mem_bytes_at sb (LENGTH (prefix ++ payload ++ suffix)) mem =
    prefix ++ payload ++ suffix ==>
  mem_bytes_at (sb + LENGTH prefix) (LENGTH payload) mem = payload
Proof
  rpt gen_tac >> strip_tac >>
  `mem_bytes_at 0 (LENGTH (prefix ++ payload ++ suffix))
      (prefix ++ payload ++ suffix) = prefix ++ payload ++ suffix` by
    simp[mem_bytes_at_def, rich_listTheory.TAKE_APPEND1] >>
  `mem_bytes_at (sb + LENGTH prefix) (LENGTH payload) mem =
   mem_bytes_at (0 + LENGTH prefix) (LENGTH payload)
     (prefix ++ payload ++ suffix)` by
    (irule mem_bytes_at_translated_window >>
     qexists_tac `LENGTH (prefix ++ payload ++ suffix)` >> simp[]) >>
  gvs[mem_bytes_at_def, listTheory.DROP_APPEND,
    rich_listTheory.TAKE_APPEND1]
QED

Theorem abi_decoder_source_prefix:
  mem_bytes_at sb (LENGTH (prefix ++ payload)) mem = prefix ++ payload ==>
  mem_bytes_at (sb + LENGTH prefix) (LENGTH payload) mem = payload
Proof
  strip_tac >>
  irule abi_decoder_source_subwindow >> qexists_tac `[]` >> simp[]
QED

(* Actual allocator probe: its returned capacity is the requested capacity,
   not the runtime Bytes length. The instruction id, not buf_operand, selects
   a reused allocation. This exposes a necessary budget for fresh allocation. *)
Theorem abi_decoder_buffer_reservation_probe:
  compile_alloc_buffer n st = (buf,st') /\
  FLOOKUP s.vs_allocas st.cs_next_id = NONE /\
  s.vs_alloca_next = b /\ b + n <= b + cap /\ n < dimword (:256) ==>
  buf.buf_size = n /\
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand buf.buf_operand t = SOME (n2w b) /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (b,n) /\
    t.vs_alloca_next = b + n /\
    t.vs_memory = s.vs_memory
Proof
  simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  drule emitted_insts_emit_op >> strip_tac >>
  simp[run_inst_seq_def, step_inst_base_def, exec_alloca_def,
       venomInstTheory.mk_inst_def, venomStateTheory.update_var_def,
       venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE, wordsTheory.w2n_n2w]
QED

Theorem abi_decoder_singleton_bytes_encoding:
  enc (Tuple [Bytes NONE]) (ListV [contractABI$BytesV bs]) =
    word_to_bytes (n2w 32 : bytes32) T ++ enc (Bytes NONE) (contractABI$BytesV bs)
Proof
  simp[contractABITheory.enc_def, contractABITheory.is_dynamic_def,
       contractABITheory.head_lengths_def, contractABITheory.enc_number_def,
       listTheory.REV_REVERSE_LEM]
QED

Theorem abi_decoder_singleton_bytes_source:
  mem_bytes_at sb (LENGTH (enc (Tuple [Bytes NONE])
      (ListV [contractABI$BytesV bs]))) mem =
    enc (Tuple [Bytes NONE]) (ListV [contractABI$BytesV bs]) ==>
  mem_bytes_at (sb + 32) (LENGTH (enc (Bytes NONE) (contractABI$BytesV bs))) mem =
    enc (Bytes NONE) (contractABI$BytesV bs)
Proof
  rewrite_tac[abi_decoder_singleton_bytes_encoding] >> strip_tac >>
  drule abi_decoder_source_prefix >> simp[byteTheory.LENGTH_word_to_bytes]
QED

(* Pure child restriction at the mandatory memory-source wrapped Bytes use
   site. childsrc is the result of the head load/add; its execution remains
   to be justified by the recursive decoder proof. *)
Theorem abi_decoder_wrapped_bytes_pre_child:
  abi_decoder_pre ce env (TupleT [BaseT (BytesT (Dynamic n))])
    (TupleTV [BaseTV (BytesT (Dynamic n))]) di
    (ListV [contractABI$BytesV bs]) (ArrayV (TupleV [BytesV bs]))
    st last src dst MLOAD hi sb d b cap s /\
  eval_operand childsrc s = SOME (n2w (sb + 32)) ==>
  abi_decoder_pre ce env (BaseT (BytesT (Dynamic n)))
    (BaseTV (BytesT (Dynamic n)))
    (type_to_abi_dec_info ce.ce_struct_fields ce (BaseT (BytesT (Dynamic n))))
    (contractABI$BytesV bs) (BytesV bs)
    st last childsrc dst MLOAD hi (sb + 32) d b cap s
Proof
  pure_rewrite_tac[abi_decoder_pre_def] >> strip_tac >>
  drule abi_decoder_singleton_metadata_child >> strip_tac >>
  asm_rewrite_tac[vyperABITheory.vyper_to_abi_type_def,
      vyperABITheory.vyper_base_to_abi_type_def] >>
  conj_tac
  >- (irule abi_decoder_child_ranges >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`LENGTH (enc (Tuple [Bytes NONE])
                      (ListV [contractABI$BytesV bs]))`, `src`] >>
      gvs[vyperABITheory.vyper_to_abi_type_def,
          vyperABITheory.vyper_base_to_abi_type_def,
          type_memory_bytes_def, abi_decoder_singleton_bytes_encoding,
          byteTheory.LENGTH_word_to_bytes]) >>
  irule abi_decoder_singleton_bytes_source >>
  qpat_x_assum `mem_bytes_at sb _ _ = _` mp_tac >>
  rewrite_tac[vyperABITheory.vyper_base_to_abi_type_def,
      vyperABITheory.vyper_to_abi_type_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_TYPED_CONTRACT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI decoder typed contract not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderTypedContract");

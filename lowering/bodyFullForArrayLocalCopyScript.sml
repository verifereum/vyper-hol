(* The raw copy endpoint is shared by all dead masks and allocation floors. *)
Theory bodyFullForArrayLocalCopy
Ancestors
  instSeqPtrLo abiDecodePtrBytesRuntimeFrame freshWrites
  forPtrCopyInterface forPtrBytes forPtrBulk forPtrWord forPtrElementFrame
  typedCopyPtr typedCopyAgreement exprLoweringProps exprSimProps
  emitHelper emitHelperProps rich_list list venomInst venomState ptrDiscipline
  valueEncoding valueEncodingProps loweringPosts finite_map compileEnv bodyPtrDefs

Theorem for_array_local_copy_memory_code[local]:
  compile_iter_elem_copy cenv src dst stride LocMemory F ty ty sa = ((),sb) ==>
  EVERY (\i. (fresh_write_op i.inst_opcode \/
    MEM i.inst_opcode [MLOAD; MSTORE; MCOPY]) /\
    i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
    ~is_terminator i.inst_opcode) (emitted_insts sa sb)
Proof
  rewrite_tac[for_memory_element_copy_dispatch] >>
  Cases_on `is_word_type ty`
  >- (simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
        comp_return_def, fresh_id_def, fresh_var_def, emit_def] >> strip_tac >>
      gvs[emitted_insts_def] >>
      pure_rewrite_tac[GSYM APPEND_ASSOC] >>
      simp[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def]) >>
  Cases_on `is_bytestring_type ty` >> simp[] >> strip_tac
  >- (drule for_bytes_copy_code >> strip_tac >>
      simp[mk_inst_def, fresh_write_op_def, is_terminator_def]) >>
  drule for_compile_bulk_copy_code >> simp[] >>
  Cases_on `type_memory_bytes cenv ty = 0` >> simp[mk_inst_def, is_terminator_def]
QED

Theorem for_array_local_copy_checked_full:
  compile_iter_elem_copy cenv (Var src) (Var dst) stride LocMemory F ty ty
    sa = ((),sb) /\
  not_fresh_at sa src /\ not_fresh_at sa dst /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes cenv ty = type_memory_size tv /\
  type_memory_size tv < dimword (:256) /\
  ptr_covers G tn src s (type_memory_size tv) /\
  ptr_covers G tn dst s (type_memory_size tv) /\
  ~ctx_has_dalloca ctx /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory tv v (w2n a) m) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next ==>
  ?gf tf sf.
    (!D. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s gf tf) /\
    run_inst_seq (emitted_insts sa sb) s = OK sf /\
    mem_agree_outside {i | w2n b <= i /\ i < w2n b + type_memory_size tv}
      sf.vs_memory s.vs_memory /\
    (!i. i < w2n b \/ w2n b + type_memory_size tv <= i ==>
      (i IN tf.t_mem <=> i IN tn.t_mem)) /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    sf.vs_call_ctx = s.vs_call_ctx /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP gf p = FLOOKUP G p /\
      op_taint tf (Var p) = op_taint tn (Var p)) /\
    (!m. mem_agree_outside tf.t_mem sf.vs_memory m ==>
      val_in_memory tv v (w2n b) m) /\
    (sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
      ~is_terminator i.inst_opcode) (emitted_insts sa sb)
Proof
  strip_tac >>
  drule for_array_local_copy_memory_code >> strip_tac >>
  `EVERY (\i. fresh_write_op i.inst_opcode \/
      MEM i.inst_opcode [MLOAD; MSTORE; MCOPY]) (emitted_insts sa sb) /\
   EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
      ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  Cases_on `is_word_type ty` >- suspend "word" >>
  Cases_on `is_bytestring_type ty` >- suspend "bytes" >>
  suspend "bulk"
QED

Resume for_array_local_copy_checked_full[word]:
  drule_all word_tv_memory_size >> strip_tac >>
  `compile_store_memory_typed cenv (Var dst) ty (Var src) ty sa = ((),sb)` by
    gvs[compile_store_memory_typed_word, for_memory_element_copy_dispatch] >>
  fs[] >> drule_all for_compile_word_copy_checked >>
  disch_then (qspecl_then
    [`func`, `PG`, `<| d_stor := K (K {}); d_trans := K (K {});
                    d_imm := K {}; d_ret := K {} |>`] strip_assume_tac) >>
  `emitted_insts sa sb =
    [mk_inst id MLOAD [Var src] [tmp];
     mk_inst (id+1) MSTORE [Var dst; Var tmp] []]` by
    simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
  drule_all word_copy_endpoint_frames >> strip_tac >>
  `run_inst_seq (emitted_insts sa sb) s = OK sf` by simp[] >>
  ` (sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s` by
    (irule (cj 1 abi_decode_memory_run_frame) >>
     goal_assum (drule_at (Pat `run_inst_seq _ _ = OK _`)) >> simp[]) >>
  qexistsl [`Gf`, `tnf`, `sf`] >> conj_tac
  >- (gen_tac >> irule inst_seq_ptr_zero_to_lo >> simp[] >>
      qexists_tac `<| d_stor := K (K {}); d_trans := K (K {});
                     d_imm := K {}; d_ret := K {} |>` >> simp[]) >>
  simp[] >> fs[venom_state_component_equality]
QED

Resume for_array_local_copy_checked_full[bytes]:
  drule_all for_iter_bytes_copy_checked >>
  disch_then (qspecl_then
    [`func`, `PG`, `<| d_stor := K (K {}); d_trans := K (K {});
                    d_imm := K {}; d_ret := K {} |>`] strip_assume_tac) >>
  `inst_seq_ptr <| d_stor := K (K {}); d_trans := K (K {});
                  d_imm := K {}; d_ret := K {} |>
     0 ctx func PG G tn (emitted_insts sa sb) s gf tf` by
    (qpat_x_assum `!k. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
      (qspec_then `s.vs_inst_idx` mp_tac) >> simp[]) >>
  `compile_store_bytestring (Var src) (Var dst) sa = ((),sb)` by
    gvs[for_memory_element_copy_dispatch] >>
  drule_all for_bytes_typed_layout >> strip_tac >>
  `mload (w2n a) s = n2w len /\
   (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem)` by
    (irule for_bytes_copy_header >> metis_tac[]) >>
  `32 + 32 * word_size cap < dimword (:256)` by metis_tac[] >>
  drule_all for_bytes_runtime_extent >> strip_tac >>
  `ptr_covers G tn src s 32` by
    (gvs[ptr_covers_def] >> goal_assum (drule_at Any) >> decide_tac) >>
  `w2n (((mload (w2n a) s + 31w) && ~31w) + 32w) <=
    type_memory_size tv` by metis_tac[] >>
  drule_all compile_bytes_copy_endpoint_frames >> strip_tac >>
  ` (sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s` by
    (irule (cj 1 abi_decode_memory_run_frame) >>
     goal_assum (drule_at (Pat `run_inst_seq _ _ = OK _`)) >> simp[]) >>
  (qexistsl [`gf`, `tf`, `sf`] >> conj_tac
   >- (gen_tac >> irule inst_seq_ptr_zero_to_lo >> simp[] >>
       qexists_tac `<| d_stor := K (K {}); d_trans := K (K {});
                      d_imm := K {}; d_ret := K {} |>` >> simp[]) >>
   gvs[] >> first_assum ACCEPT_TAC)
QED

Resume for_array_local_copy_checked_full[bulk]:
  `val_footprint tv v <= type_memory_size tv` by metis_tac[val_footprint_le] >>
  drule_all for_iter_bulk_copy_checked >>
  disch_then (qspecl_then
    [`func`, `PG`, `<| d_stor := K (K {}); d_trans := K (K {});
                    d_imm := K {}; d_ret := K {} |>`] strip_assume_tac) >>
  `compile_copy_memory (Var dst) (Var src) (type_memory_size tv) sa = ((),sb)` by
    gvs[for_memory_element_copy_dispatch] >>
  drule_all compile_bulk_copy_endpoint_frames >> strip_tac >>
  ` (sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s` by
    (irule (cj 1 abi_decode_memory_run_frame) >>
     goal_assum (drule_at (Pat `run_inst_seq _ _ = OK _`)) >> simp[]) >>
  qexistsl [`G`, `tf`, `sf`] >> conj_tac
  >- (gen_tac >> irule inst_seq_ptr_zero_to_lo >> simp[] >>
      qexists_tac `<| d_stor := K (K {}); d_trans := K (K {});
                     d_imm := K {}; d_ret := K {} |>` >> simp[]) >>
  simp[] >>
  qpat_x_assum `!i. i < _ \/ _ <= i ==> _` mp_tac >>
  simp[arithmeticTheory.ADD_COMM]
QED

Finalise for_array_local_copy_checked_full

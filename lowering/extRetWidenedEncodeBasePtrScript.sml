Theory extRetWidenedEncodeBasePtr
Ancestors
  bodyPtrTypeBuiltinsUintCounted
  logAbiEncodePtr logAbiStaticPtr logInstSeqPtr wordLoadStorePtr forPtrWord
  abiDecodePtrBytesRuntimeFrame abiEncoderObserverCode abiEncoderBytesCode
  abiEncoder abiEncoderMemory abiDecoderContract freshWrites
  fragGasSeqPtr fragGasPathPtr fragExec emitHelper emitHelperProps
  exprLoweringProps compileEnv bodyPtrDefs ptrDiscipline ptrCoverage loweringStateRelDefs
  venomExecSemantics venomInstProofs venomInst venomState venomMemProofs
  finite_map words list rich_list arithmetic pred_set

Definition widened_encode_endpoint_def:
  widened_encode_endpoint D ctx fn PG sa sb out b n G tn s <=>
    ?Gf tnf sf.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
      sf.vs_current_bb = sb.cs_current_bb /\
      sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
      eval_operand out sf = SOME (n2w n) /\ op_taint tnf out = {} /\
      (!i. i < n ==> b+i NOTIN tnf.t_mem) /\
      (!p. not_fresh_at sa p ==>
        lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
        op_taint tnf (Var p) = op_taint tn (Var p)) /\
      (!i. ~(b <= i /\ i < b+n) ==>
        mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory /\
        (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
      tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
      tnf.t_imm = tn.t_imm /\
      (sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
        vs_current_bb := s.vs_current_bb; vs_prev_bb := s.vs_prev_bb;
        vs_inst_idx := s.vs_inst_idx|>) = s
End

Theorem widened_encode_leaf_code[local]:
  compile_abi_encode_to_buf dst src info sa = (out,sb) /\
  (info = AbiPrimWord \/ (?m. info = AbiBytestring m) \/
   (?k. info = AbiCopy k) \/ info = AbiComplex []) ==>
  sb.cs_current_bb = sa.cs_current_bb /\ inst_extends sa sb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
    ~is_terminator i.inst_opcode /\
    (fresh_write_op i.inst_opcode \/ MEM i.inst_opcode [MLOAD;MSTORE;MCOPY]))
    (emitted_insts sa sb)
Proof
  strip_tac >> gvs[] >>
  qpat_x_assum `compile_abi_encode_to_buf _ _ _ _ = _` mp_tac >>
  simp[Once compile_abi_encode_child_def, compile_abi_encode_static_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def,
    emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  CONV_TAC (DEPTH_CONV (REWR_CONV (GSYM APPEND_ASSOC))) >>
  simp[emitted_insts_def, inst_extends_def] >>
  CONV_TAC (DEPTH_CONV (REWR_CONV (GSYM APPEND_ASSOC))) >>
  simp[DROP_LENGTH_APPEND, fresh_write_op_def, mk_inst_def, is_terminator_def]
QED

Theorem widened_encode_sequence_endpoint[local]:
  compile_abi_encode_to_buf (Var dst) (Var src) info sa = (out,sb) /\
  (info = AbiPrimWord \/ (?m. info = AbiBytestring m) \/
   (?k. info = AbiCopy k) \/ info = AbiComplex []) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H tm /\
  eval_operand out t = SOME (n2w n) /\ op_taint tm out = {} /\
  (!i. b <= i /\ i < b+n ==> i NOTIN tm.t_mem) /\
  (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
    FLOOKUP H p = FLOOKUP G p /\ op_taint tm (Var p) = op_taint tn (Var p)) /\
  mem_agree_outside {i | b <= i /\ i < b+n} t.vs_memory s.vs_memory /\
  (!i. ~(b <= i /\ i < b+n) ==> (i IN tm.t_mem <=> i IN tn.t_mem)) /\
  tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm ==>
  widened_encode_endpoint D ctx fn PG sa sb out b n G tn s
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all widened_encode_leaf_code >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
   EVERY (\i. fresh_write_op i.inst_opcode \/ MEM i.inst_opcode [MLOAD;MSTORE;MCOPY])
    (emitted_insts sa sb)` by (gvs[EVERY_MEM] >> metis_tac[]) >>
  drule_all abi_decode_memory_run_frame >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (irule fn_code_emitted_prefix >> metis_tac[]) >>
  drule_all run_inst_seq_gas_path_ptr >> strip_tac >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (simp[FILTER_EQ_NIL, EVERY_MEM] >> gvs[EVERY_MEM] >> metis_tac[]) >>
  `s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts` by
    metis_tac[LENGTH_APPEND] >>
  simp[widened_encode_endpoint_def] >>
  qexistsl_tac [`H`, `tm`, `t with vs_inst_idx := LENGTH sb.cs_current_insts`] >>
  gvs[mem_agree_outside_def, venom_state_component_equality, eval_operand_def,
    lookup_var_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac
QED

Theorem widened_encode_bytes_certificate[local]:
  compile_abi_encode_to_buf (Var dst) (Var src) (AbiBytestring maxlen) sa = (out,sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  n = 32+contractABI$ceil32 cnt /\
  (?Gf tnf sf.
    run_inst_seq (emitted_insts sa sb) s = OK sf /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gf tnf /\
    eval_operand out sf = SOME (n2w (32+contractABI$ceil32 cnt)) /\
    op_taint tnf out = {} /\ op_prov Gf out = NONE /\
    (!i. b <= i /\ i < b+32+contractABI$ceil32 cnt ==> i NOTIN tnf.t_mem) /\
    (!i. ~(b <= i /\ i < b+32+contractABI$ceil32 cnt) ==>
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    mem_agree_outside {i | b <= i /\ i < b+32+contractABI$ceil32 cnt}
      sf.vs_memory s.vs_memory /\
    (!p. not_fresh_at sa p ==> lookup_var p sf = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p))) ==>
  widened_encode_endpoint D ctx fn PG sa sb out b n G tn s
Proof
  strip_tac >> gvs[] >> irule widened_encode_sequence_endpoint >>
  goal_assum (drule_at Any) >> simp[] >>
  conj_tac >- (goal_assum (drule_at Any) >> simp[]) >>
  qexistsl_tac [`Gf`, `tnf`] >>
  pure_asm_rewrite_tac [GSYM ADD_ASSOC] >> simp[ADD_COMM] >>
  `b+32+contractABI$ceil32 cnt = b+(contractABI$ceil32 cnt+32)` by decide_tac >>
  qpat_x_assum `mem_agree_outside _ _ _` mp_tac >> pure_asm_rewrite_tac [] >> simp[]
QED

Theorem widened_encode_leaf_counted_ptr:
  compile_abi_encode_to_buf (Var dst) (Var src) info sa = (out,sb) /\
  fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa src /\ not_fresh_at sa dst /\
  (case info of
     AbiPrimWord =>
       n = 32 /\ lookup_var src s = SOME (n2w a) /\
       lookup_var dst s = SOME (n2w b) /\
       ptr_covers G tn src s 32 /\ ptr_covers G tn dst s 32 /\
       a+32 < dimword(:256) /\ b+32 < dimword(:256) /\
       (!i. a <= i /\ i < a+32 ==> i NOTIN tn.t_mem)
   | AbiBytestring maxlen =>
       n = 32+contractABI$ceil32 cnt /\ cnt <= maxlen /\
       lookup_var src s = SOME (n2w a) /\ lookup_var dst s = SOME (n2w b) /\
       mload a s = n2w cnt /\ ptr_covers G tn src s (32+cnt) /\
       ptr_covers G tn dst s n /\
       a+32+cnt < dimword(:256) /\ b+n < dimword(:256) /\
       32+cnt < dimword(:256) /\ (a+32+cnt <= b \/ b+n <= a) /\
       (!i. a <= i /\ i < a+32+cnt ==> i NOTIN tn.t_mem)
   | AbiCopy k =>
       n = k /\ lookup_var src s = SOME (n2w a) /\
       lookup_var dst s = SOME (n2w b) /\
       ptr_covers G tn src s n /\ ptr_covers G tn dst s n /\
       a+n < dimword(:256) /\ b+n < dimword(:256) /\
       (!i. a <= i /\ i < a+n ==> i NOTIN tn.t_mem)
   | AbiComplex elems => elems = [] /\ n = 0
   | _ => F) ==>
  widened_encode_endpoint D ctx fn PG sa sb out b n G tn s
Proof
  strip_tac >> Cases_on `info`
  >~ [`compile_abi_encode_to_buf _ _ AbiPrimWord _ = _`] >-
    (gvs[] >>
     `?tmp. out = Lit 32w /\
       emitted_insts sa sb =
         [mk_inst sa.cs_next_id MLOAD [Var src] [tmp];
          mk_inst (sa.cs_next_id+1) MSTORE [Var dst; Var tmp] []] /\
       (!p. not_fresh_at sa p ==> p <> tmp)` by
       (qpat_x_assum `compile_abi_encode_to_buf _ _ _ _ = _` mp_tac >>
        simp[Once compile_abi_encode_child_def, compile_abi_encode_static_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def,
          emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
        rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
        CONV_TAC (DEPTH_CONV (REWR_CONV (GSYM APPEND_ASSOC))) >>
        simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
        qexists_tac `STRING #"%" (toString sa.cs_next_var)` >>
        simp[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >>
     `tmp <> dst /\ a < dimword(:256) /\ b < dimword(:256)` by metis_tac[DECIDE ``x+32 < z ==> x < z``] >>
     `!i. w2n ((n2w a):256 word) <= i /\
       i < w2n ((n2w a):256 word)+32 ==> i NOTIN tn.t_mem` by simp[w2n_n2w] >>
     drule_all for_word_copy_checked_seq >>
     disch_then (qspecl_then [`sa.cs_next_id`, `fn`, `PG`, `D`] strip_assume_tac) >>
     `run_inst_seq (emitted_insts sa sb) s =
       OK (mstore b (mload a s) (update_var tmp (mload a s) s))` by
       (asm_rewrite_tac [] >>
        simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
          exec_read1_def, exec_write2_def, eval_operand_def, update_var_def,
          lookup_var_def, FLOOKUP_UPDATE] >> gvs[lookup_var_def] >> simp[w2n_n2w]) >>
     qabbrev_tac `u = update_var tmp (mload (w2n ((n2w a):256 word)) s) s` >>
     qabbrev_tac `tm = step_taint (mk_inst sa.cs_next_id MLOAD [Var src] [tmp]) s u tn` >>
     `tnf.t_mem = tn.t_mem DIFF {i | b <= i /\ i < b+32} /\
       tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans` by
       (drule_all for_word_copy_taint_frame >> simp[w2n_n2w]) >>
     FAIL_TAC "primitive frames")
  >~ [`compile_abi_encode_to_buf _ _ (AbiBytestring _) _ = _`] >-
    (irule widened_encode_bytes_certificate >>
     asm_rewrite_tac [] >> conj_tac
     >- (qexists_tac `cnt` >> reverse conj_tac
         >- (pop_assum mp_tac >> simp[]) >>
         irule compile_abi_bytes_seq_ptr >>
         pop_assum mp_tac >> simp[] >> strip_tac >>
         asm_rewrite_tac [] >>
         qexistsl_tac [`dst`, `n'`, `src`, `a`] >>
         gvs[] >> rpt conj_tac >> decide_tac) >>
     goal_assum (drule_at Any))
  >~ [`compile_abi_encode_to_buf _ _ (AbiCopy _) _ = _`] >-
    (gvs[] >> drule_all compile_abi_copy_seq_ptr >>
     disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
     irule widened_encode_sequence_endpoint >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[])
  >~ [`compile_abi_encode_to_buf _ _ (AbiComplex _) _ = _`] >-
    (gvs[Once compile_abi_encode_child_def, comp_return_def] >>
     simp[widened_encode_endpoint_def] >>
     qexistsl_tac [`G`, `tn`, `s`] >>
     simp[eval_operand_def, op_taint_def, venom_state_component_equality] >>
     irule (cj 1 gas_path_ptr_rules) >> simp[])
  >> gvs[]
QED

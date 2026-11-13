(* Exact instruction layout of the mapping-slot hash. *)
Theory bodyPtrSubscriptSeamMapSuffix
Ancestors
  bodyPtrSubscriptSeamMapKey bodyPtrSubscriptScratchTransfer
  bodyPtrHashBuiltinsAllocFrame bodyPtrHashBuiltinsKeccak
  exprLowering exprLoweringProps context compileEnv loweringStateRelDefs emitHelper emitHelperProps
  venomInst ASCIInumbers rich_list arithmetic list
  exprSimPtrTopLevelImmutableCopy typedCopyPtr ptrDiscipline
  bodyPtrDefs bodyPtrSubscriptScratchStore bodyPtrHashBuiltinsKeccakBytesRun
  venomExecSemantics venomState finite_map pred_set words fragGasSeqPtr exprSimHash
  fragExecPtr instIdxIndep exprSimMapKey exprSimAlloc loweringHalt allocationPtr

Theorem mapping_slot_hash_emission:
  !slot key sa op sb.
    compile_mapping_subscript slot key sa = (op,sb) ==>
    emitted_insts sa sb =
      [mk_inst sa.cs_next_id ALLOCA [Lit 64w]
         [STRING #"%" (toString sa.cs_next_var)];
       mk_inst (sa.cs_next_id+1) MSTORE
         [Var (STRING #"%" (toString sa.cs_next_var));slot] [];
       mk_inst (sa.cs_next_id+2) ADD
         [Var (STRING #"%" (toString sa.cs_next_var));Lit 32w]
         [STRING #"%" (toString (sa.cs_next_var+1))];
       mk_inst (sa.cs_next_id+3) MSTORE
         [Var (STRING #"%" (toString (sa.cs_next_var+1)));key] [];
       mk_inst (sa.cs_next_id+4) SHA3
         [Var (STRING #"%" (toString sa.cs_next_var));Lit 64w]
         [STRING #"%" (toString (sa.cs_next_var+2))]] /\
    op = Var (STRING #"%" (toString (sa.cs_next_var+2)))
Proof
  rpt gen_tac >>
  simp[compile_mapping_subscript_def, compile_alloc_buffer_def,
    emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, fresh_id_def, fresh_var_def, emit_def,
    emitted_insts_def, DROP_LENGTH_APPEND, ADD_ASSOC] >>
  strip_tac >> gvs[APPEND_ASSOC, DROP_LENGTH_APPEND]
QED

Theorem mapping_slot_hash_shape:
  !slot key sa op sb.
    compile_mapping_subscript slot key sa = (op,sb) ==>
    ?ia is ip ik ih p q h.
      emitted_insts sa sb =
        [mk_inst ia ALLOCA [Lit 64w] [p];
         mk_inst is MSTORE [Var p;slot] [];
         mk_inst ip ADD [Var p;Lit 32w] [q];
         mk_inst ik MSTORE [Var q;key] [];
         mk_inst ih SHA3 [Var p;Lit 64w] [h]] /\
      op = Var h /\ ALL_DISTINCT [p;q;h] /\
      (!z. not_fresh_at sa z ==> z <> p /\ z <> q /\ z <> h)
Proof
  rpt gen_tac >> strip_tac >> drule mapping_slot_hash_emission >> strip_tac >>
  qexistsl [`sa.cs_next_id`, `sa.cs_next_id+1`, `sa.cs_next_id+2`,
    `sa.cs_next_id+3`, `sa.cs_next_id+4`,
    `STRING #"%" (toString sa.cs_next_var)`,
    `STRING #"%" (toString (sa.cs_next_var+1))`,
    `STRING #"%" (toString (sa.cs_next_var+2))`] >>
  simp[toString_inj] >>
  rpt strip_tac >> gvs[not_fresh_at_def, toString_inj]
QED

Theorem mapping_slot_hash_tail:
  !D ctx fn PG G tn s is ip ik ih p q h slot key w0 w1 b root cap.
    ALL_DISTINCT [p;q;h] /\
    (!z. slot = Var z \/ key = Var z ==> z <> p /\ z <> q /\ z <> h) /\
    eval_operand (Var p) s = SOME (n2w b) /\
    FLOOKUP G p = SOME (root,cap) /\ root <= b /\ b+64 <= root+cap /\
    b+64 < dimword (:256) /\
    eval_operand slot s = SOME w0 /\ eval_operand key s = SOME w1 /\
    op_taint tn (Var p) = {} /\ op_taint tn slot = {} /\ op_taint tn key = {} /\
    ~ctx_has_dalloca ctx ==>
    ?G' tn'. inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst is MSTORE [Var p;slot] [];
       mk_inst ip ADD [Var p;Lit 32w] [q];
       mk_inst ik MSTORE [Var q;key] [];
       mk_inst ih SHA3 [Var p;Lit 64w] [h]] s G' tn' /\
      G' = DRESTRICT (G |+ (q,(root,cap))) (COMPL {h}) /\
      tn' = tn with <|t_var := tn.t_var |+ (q,{}) |+ (h,{});
        t_mem := tn.t_mem DIFF {i | b <= i /\ i < b+64}|>
Proof
  rpt gen_tac >> strip_tac >>
  `b < dimword (:256) /\ b+32 < dimword (:256)` by decide_tac >>
  `lookup_var p s = SOME (n2w b)` by gvs[eval_operand_def] >>
  `ptr_covers G tn p s 32` by
    (simp[ptr_covers_def] >> qexists `n2w b` >> simp[] >> decide_tac) >>
  `step_inst_base (mk_inst is MSTORE [Var p;slot] []) s =
    OK (mstore b w0 s)` by
    (simp[step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def, eval_operand_def]) >>
  simp[Once inst_seq_ptr_def] >>
  conj_tac >- (irule ptr_inst_ok_mstore_taint_transparent >> simp[]) >>
  `step_prov PG G (mk_inst is MSTORE [Var p;slot] []) (mstore b w0 s) = G /\
   step_taint (mk_inst is MSTORE [Var p;slot] []) s (mstore b w0 s) tn =
     tn with t_mem := tn.t_mem DIFF {i | b <= i /\ i < b+32}` by
    (qpat_x_assum `eval_operand key s = _` kall_tac >>
     drule_all toplevel_immutable_mstore_ghost_frame >>
     disch_then (qspecl_then [`is`, `PG`, `G`] mp_tac) >> simp[]) >>
  gvs[] >>
  qabbrev_tac `s1 = mstore b w0 s with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `tn1 = tn with t_mem := tn.t_mem DIFF {i | b <= i /\ i < b+32}` >>
  suspend "add"
QED

Resume mapping_slot_hash_tail[add]:
  `eval_operand (Var p) s1 = SOME (n2w b) /\ op_taint tn1 (Var p) = {}` by
    gvs[Abbr `s1`, Abbr `tn1`, eval_operand_def, lookup_var_def, mstore_def,
        op_taint_def] >>
  `step_inst_base (mk_inst ip ADD [Var p;Lit 32w] [q]) s1 =
     OK (update_var q (n2w b+32w) s1)` by
    (simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def, eval_operand_def]) >>
  simp[Once inst_seq_ptr_def] >>
  conj_tac >- (irule ptr_inst_ok_copy_len_binop >> simp[op_taint_def]) >>
  simp[hash_add_ghost] >>
  qabbrev_tac `s2 = update_var q (n2w b+32w) s1 with vs_inst_idx := SUC s1.vs_inst_idx` >>
  qabbrev_tac `G2 = G |+ (q,(root,cap))` >>
  qabbrev_tac `tn2 = tn1 with t_var := tn1.t_var |+ (q,{})` >>
  suspend "store"
QED

Resume mapping_slot_hash_tail[store]:
  `step_prov PG G (mk_inst ip ADD [Var p;Lit 32w] [q])
     (update_var q (n2w b+32w) s1) = G2` by
    (simp[Abbr `G2`] >> irule (cj 1 hash_add_ghost) >> simp[]) >>
  asm_rewrite_tac[] >>
  `lookup_var q s2 = SOME (n2w (b+32)) /\
   FLOOKUP G2 q = SOME (root,cap) /\ op_taint tn2 (Var q) = {} /\
   eval_operand key s2 = SOME w1 /\ op_taint tn2 key = {}` by
    (Cases_on `key` >>
     gvs[Abbr `s2`, Abbr `s1`, Abbr `G2`, Abbr `tn2`, Abbr `tn1`,
       eval_operand_def, lookup_var_def, update_var_def, mstore_def,
       op_taint_def, FLOOKUP_UPDATE, word_add_n2w]) >>
  `ptr_covers G2 tn2 q s2 32` by
    (simp[ptr_covers_def] >> qexists `n2w (b+32)` >> simp[] >> decide_tac) >>
  `step_inst_base (mk_inst ik MSTORE [Var q;key] []) s2 =
     OK (mstore (b+32) w1 s2)` by
    (simp[step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def, eval_operand_def]) >>
  simp[Once inst_seq_ptr_def] >>
  conj_tac >- (irule ptr_inst_ok_mstore_taint_transparent >> simp[]) >>
  `step_prov PG G2 (mk_inst ik MSTORE [Var q;key] []) (mstore (b+32) w1 s2) = G2 /\
   step_taint (mk_inst ik MSTORE [Var q;key] []) s2 (mstore (b+32) w1 s2) tn2 =
     tn2 with t_mem := tn2.t_mem DIFF {i | b+32 <= i /\ i < b+64}` by
    (qpat_x_assum `lookup_var p s = _` kall_tac >>
     drule_all toplevel_immutable_mstore_ghost_frame >>
     disch_then (qspecl_then [`ik`, `PG`, `G2`] mp_tac) >> simp[ADD_ASSOC]) >>
  asm_rewrite_tac[] >>
  qabbrev_tac `s3 = mstore (b+32) w1 s2 with vs_inst_idx := SUC s2.vs_inst_idx` >>
  qabbrev_tac `tn3 = tn2 with t_mem := tn2.t_mem DIFF {i | b+32 <= i /\ i < b+64}` >>
  suspend "hash"
QED

Resume mapping_slot_hash_tail[hash]:
  `eval_operand (Var p) s3 = SOME (n2w b) /\
   FLOOKUP G2 p = SOME (root,cap) /\ op_taint tn3 (Var p) = {}` by
    (simp[Abbr `s3`, Abbr `s2`, Abbr `s1`, Abbr `G2`, Abbr `tn3`, Abbr `tn2`,
      Abbr `tn1`, eval_operand_def, lookup_var_def, update_var_def, mstore_def,
      op_taint_def, FLOOKUP_UPDATE] >> gvs[op_taint_def, lookup_var_def]) >>
  `tn3.t_mem = tn.t_mem DIFF {i | b <= i /\ i < b+64}` by
    (simp[Abbr `tn3`, Abbr `tn2`, Abbr `tn1`, EXTENSION] >>
     gen_tac >> Cases_on `x IN tn.t_mem` >> simp[] >> decide_tac) >>
  `!i. b <= i /\ i < b+64 ==> i NOTIN tn3.t_mem` by simp[] >>
  `step_inst_base (mk_inst ih SHA3 [Var p;Lit 64w] [h]) s3 =
     OK (update_var h (word_of_bytes T (0w:bytes32)
       (Keccak_256_w64 (mem_bytes_at b 64 s3.vs_memory))) s3)` by
    (irule step_SHA3_bytes >> simp[eval_operand_def]) >>
  simp[Once inst_seq_ptr_def] >>
  conj_tac >- (irule hash_sha3_inst_ok >> simp[eval_operand_def, op_taint_def]) >>
  simp[inst_seq_ptr_def, hash_sha3_ghost, Abbr `G2`, Abbr `tn3`, Abbr `tn2`,
       Abbr `tn1`, finite_mapTheory.FUPDATE_COMMUTES] >>
  simp[taint_component_equality, EXTENSION] >> gen_tac >> Cases_on `x IN tn.t_mem` >> simp[] >> decide_tac
QED

Finalise mapping_slot_hash_tail

Theorem mapping_slot_hash_allocated:
  !D ctx fn PG G tn s ia is ip ik ih p q h slot key w0 w1 u G1 tn1 a.
    ALL_DISTINCT [p;q;h] /\
    (!z. slot = Var z \/ key = Var z ==> z <> p /\ z <> q /\ z <> h) /\
    step_inst_base (mk_inst ia ALLOCA [Lit 64w] [p]) s = OK u /\
    G1 = step_prov PG G (mk_inst ia ALLOCA [Lit 64w] [p]) u /\
    tn1 = step_taint (mk_inst ia ALLOCA [Lit 64w] [p]) s u tn /\
    ptr_covers G1 tn1 p u 64 /\ lookup_var p u = SOME a /\
    w2n a+64 < dimword (:256) /\
    eval_operand slot u = SOME w0 /\ eval_operand key u = SOME w1 /\
    op_taint tn1 slot = {} /\ op_taint tn1 key = {} /\ ~ctx_has_dalloca ctx ==>
    ?G' tn'. inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst ia ALLOCA [Lit 64w] [p];
       mk_inst is MSTORE [Var p;slot] [];
       mk_inst ip ADD [Var p;Lit 32w] [q];
       mk_inst ik MSTORE [Var q;key] [];
       mk_inst ih SHA3 [Var p;Lit 64w] [h]] s G' tn' /\
      op_taint tn' (Var h) = {} /\ op_prov G' (Var h) = NONE /\
      tn'.t_mem = tn1.t_mem DIFF {i | w2n a <= i /\ i < w2n a+64} /\
      tn'.t_stor = tn1.t_stor /\ tn'.t_trans = tn1.t_trans /\ tn'.t_imm = tn1.t_imm /\
      (!z. z <> q /\ z <> h ==> FLOOKUP G' z = FLOOKUP G1 z /\
        op_taint tn' (Var z) = op_taint tn1 (Var z))
Proof
  rpt gen_tac >> strip_tac >>
  `?root cap. FLOOKUP G1 p = SOME (root,cap) /\ root <= w2n a /\
    w2n a+64 <= root+cap /\ op_taint tn1 (Var p) = {}` by
    gvs[ptr_covers_def] >>
  `eval_operand (Var p) (u with vs_inst_idx := SUC s.vs_inst_idx) = SOME (n2w (w2n a)) /\
   eval_operand slot (u with vs_inst_idx := SUC s.vs_inst_idx) = SOME w0 /\
   eval_operand key (u with vs_inst_idx := SUC s.vs_inst_idx) = SOME w1` by
    gvs[eval_operand_def, lookup_var_def] >>
  drule_all mapping_slot_hash_tail >>
  disch_then (qspecl_then [`D`, `fn`, `PG`, `is`, `ip`, `ik`, `ih`] strip_assume_tac) >>
  qexistsl [`G'`, `tn'`] >>
  conj_tac >- (simp[Once inst_seq_ptr_def] >>
    conj_tac >- (irule ptr_inst_ok_alloca >> simp[]) >> gvs[]) >>
  gvs[op_taint_def, op_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, ALL_DISTINCT]
QED

Theorem mapping_slot_hash_inst_seq:
  !D ctx fn PG G tn s slot key sa op sb w0 w1 cenv cx es.
    compile_mapping_subscript slot key sa = (op,sb) /\
    (!z. slot = Var z \/ key = Var z ==> not_fresh_at sa z) /\
    eval_operand slot s = SOME w0 /\ eval_operand key s = SOME w1 /\
    op_taint tn slot = {} /\ op_taint tn key = {} /\
    stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
    local_ptrs_reserved cenv sa /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit 64w]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn) /\
    ~ctx_has_dalloca ctx ==>
    ?G' tn'. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s G' tn' /\
      op_taint tn' op = {} /\ op_prov G' op = NONE /\
      tn'.t_mem SUBSET tn.t_mem /\
      tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
      (!z. not_fresh_at sa z ==> FLOOKUP G' z = FLOOKUP G z /\
        op_taint tn' (Var z) = op_taint tn (Var z))
Proof
  rpt gen_tac >> strip_tac >>
  drule compile_mapping_subscript_parts >> strip_tac >>
  `64 < dimword (:256)` by simp[dimword_def] >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sm) s = OK u` >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `emitted_insts sa sm = [mk_inst sa.cs_next_id ALLOCA [Lit 64w]
    [STRING #"%" (toString sa.cs_next_var)]]` by
    (drule compile_alloc_buffer_emission >> strip_tac >>
     drule emitted_insts_emit_inst >> simp[emitted_insts_def] >> strip_tac >> gvs[]) >>
  `step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit 64w]
    [STRING #"%" (toString sa.cs_next_var)]) s = OK u` by
    gvs[run_inst_seq_def, AllCaseEqs()] >>
  gvs[] >>
  qabbrev_tac `p = STRING #"%" (toString sa.cs_next_var)` >>
  qabbrev_tac `q = STRING #"%" (toString (sa.cs_next_var+1))` >>
  qabbrev_tac `h = STRING #"%" (toString (sa.cs_next_var+2))` >>
  qabbrev_tac `G1 = step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit 64w] [p]) u` >>
  qabbrev_tac `tn1 = step_taint (mk_inst sa.cs_next_id ALLOCA [Lit 64w] [p]) s u tn` >>
  `ALL_DISTINCT [p;q;h] /\
   (!z. not_fresh_at sa z ==> z <> p /\ z <> q /\ z <> h)` by
    (simp[Abbr `p`, Abbr `q`, Abbr `h`, toString_inj] >>
     rpt strip_tac >> gvs[not_fresh_at_def, toString_inj]) >>
  suspend "operands"
QED

Resume mapping_slot_hash_inst_seq[operands]:
  `!z. slot = Var z \/ key = Var z ==> z <> p /\ z <> q /\ z <> h` by metis_tac[] >>
  `eval_operand slot u = SOME w0 /\ op_taint tn1 slot = {}` by
    (simp[Abbr `tn1`] >> irule hash_alloca_old_operand >>
     simp[] >> metis_tac[]) >>
  `eval_operand key u = SOME w1 /\ op_taint tn1 key = {}` by
    (simp[Abbr `tn1`] >> irule hash_alloca_old_operand >>
     simp[] >> metis_tac[]) >>
  `ptr_covers G1 tn1 p u 64` by
    (simp[Abbr `G1`, Abbr `tn1`] >> irule alloca_step_ptr_covers >>
     simp[] >> metis_tac[]) >>
  `lookup_var p u = SOME w` by gvs[eval_operand_def] >>
  `G1 = step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit 64w] [p]) u /\
   tn1 = step_taint (mk_inst sa.cs_next_id ALLOCA [Lit 64w] [p]) s u tn` by
    simp[Abbr `G1`, Abbr `tn1`] >>
  drule_all mapping_slot_hash_allocated >>
  disch_then (qspecl_then [`D`, `fn`, `sa.cs_next_id+1`, `sa.cs_next_id+2`,
    `sa.cs_next_id+3`, `sa.cs_next_id+4`] strip_assume_tac) >>
  suspend "post"
QED

Resume mapping_slot_hash_inst_seq[post]:
  `64 < dimword (:256)` by simp[dimword_def] >>
  `(!z. z <> p ==> FLOOKUP G1 z = FLOOKUP G z /\
      op_taint tn1 (Var z) = op_taint tn (Var z)) /\
   tn1.t_mem SUBSET tn.t_mem UNION {i | w2n w <= i /\ i < w2n w+64}` by
    (simp[Abbr `G1`, Abbr `tn1`] >>
     drule_all hash_alloca_exterior_effects >>
     disch_then (qspecl_then [`PG`, `G`, `tn`] mp_tac) >> simp[]) >>
  `tn1.t_stor = tn.t_stor /\ tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm` by
    simp[Abbr `tn1`, step_taint_def, mk_inst_def, store_taint_def,
         adopt_reset_def, imm_taint_def] >>
  drule mapping_slot_hash_emission >> strip_tac >>
  qexistsl [`G'`, `tn'`] >>
  conj_tac >- (qpat_x_assum `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
    simp[Abbr `p`, Abbr `q`, Abbr `h`]) >>
  conj_tac >- (qpat_x_assum `op_taint tn' (Var h) = _` mp_tac >> simp[Abbr `h`]) >>
  conj_tac >- (qpat_x_assum `op_prov G' (Var h) = _` mp_tac >> simp[Abbr `h`]) >>
  conj_tac >- (qpat_x_assum `tn'.t_mem = _` mp_tac >>
    qpat_x_assum `tn1.t_mem SUBSET _` mp_tac >>
    POP_ASSUM_LIST (K all_tac) >> simp[SUBSET_DEF] >> metis_tac[]) >>
  simp[] >> rpt strip_tac >> metis_tac[]
QED

Finalise mapping_slot_hash_inst_seq

Theorem mapping_slot_hash_counted:
  !D ctx fn PG G tn s t bb slot key sa op sb w0 w1 cenv cx es.
    compile_mapping_subscript slot key sa = (op,sb) /\
    (!z. slot = Var z \/ key = Var z ==> not_fresh_at sa z) /\
    eval_operand slot s = SOME w0 /\ eval_operand key s = SOME w1 /\
    op_taint tn slot = {} /\ op_taint tn key = {} /\
    stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
    local_ptrs_reserved cenv sa /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit 64w]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn) /\
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
    run_inst_seq (emitted_insts sa sb) s = OK t ==>
    ?G' tn'. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
        (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))) /\
      op_taint tn' op = {} /\ op_prov G' op = NONE /\
      tn'.t_mem SUBSET tn.t_mem /\
      tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
      (!z. not_fresh_at sa z ==> FLOOKUP G' z = FLOOKUP G z /\
        op_taint tn' (Var z) = op_taint tn (Var z))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all mapping_slot_hash_inst_seq >>
  disch_then (qspecl_then [`D`, `PG`, `G`] strip_assume_tac) >>
  qexistsl [`G'`, `tn'`] >> simp[] >>
  drule mapping_slot_hash_shape >> strip_tac >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb)) = 0 /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb)` by simp[mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_path_ptr >> simp[]
QED


(* Checked mapping-key hashing in the compiler's ADD/MLOAD/SHA3 order. *)
Theory bodyPtrPopTargetSimMapKeyRun
Ancestors bodyPtrHashBuiltinsKeccakBytesRun exprSimMapKey exprLowering
  emitHelper emitHelperProps compileEnv loweringStateRelDefs ASCIInumbers rich_list codegenRel exprLoweringProps
  typedCopyPtr typedCopyLoopHeaderPtr bodyPtrDefs fragGasSeqPtr wordLoadStorePtr
  ghostPcTransportPtr instIdxIndep ptrDiscipline venomState venomInst
  venomExecSemantics words finite_map pred_set contextCodegenRel valueEncodingProps
  bodyPtrHashBuiltinsKeccak exprSimHash

Theorem map_key_emission:
  !x sa op sb.
    compile_keccak256_key x F sa = (op,sb) ==>
    emitted_insts sa sb =
      [mk_inst sa.cs_next_id ADD [x;Lit 32w]
         [STRING #"%" (toString sa.cs_next_var)];
       mk_inst (sa.cs_next_id+1) MLOAD [x]
         [STRING #"%" (toString (sa.cs_next_var+1))];
       mk_inst (sa.cs_next_id+2) SHA3
         [Var (STRING #"%" (toString sa.cs_next_var));
          Var (STRING #"%" (toString (sa.cs_next_var+1)))]
         [STRING #"%" (toString (sa.cs_next_var+2))]] /\
    op = Var (STRING #"%" (toString (sa.cs_next_var+2)))
Proof
  rpt gen_tac >>
  simp[compile_keccak256_key_def,
    emit_op_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, fresh_id_def, fresh_var_def, emit_def,
    emitted_insts_def, DROP_LENGTH_APPEND, arithmeticTheory.ADD_ASSOC] >>
  strip_tac >> gvs[listTheory.APPEND_ASSOC, DROP_LENGTH_APPEND]
QED

Theorem map_key_shape:
  !x sa op sb.
    compile_keccak256_key x F sa = (op,sb) ==>
    ?ia il ih p l h.
      emitted_insts sa sb =
        [mk_inst ia ADD [x;Lit 32w] [p]; mk_inst il MLOAD [x] [l];
         mk_inst ih SHA3 [Var p;Var l] [h]] /\
      op = Var h /\ ALL_DISTINCT [p;l;h] /\
      (!z. not_fresh_at sa z ==> z <> p /\ z <> l /\ z <> h)
Proof
  rpt gen_tac >> strip_tac >> drule map_key_emission >> strip_tac >>
  qexistsl_tac [`sa.cs_next_id`, `sa.cs_next_id+1`, `sa.cs_next_id+2`,
    `STRING #"%" (toString sa.cs_next_var)`,
    `STRING #"%" (toString (sa.cs_next_var+1))`,
    `STRING #"%" (toString (sa.cs_next_var+2))`] >>
  simp[toString_inj] >>
  rpt strip_tac >> gvs[not_fresh_at_def, toString_inj]
QED

Theorem map_key_triple:
  !D ctx fn PG G tn s ia il ih x p l h b base cap n.
    ALL_DISTINCT [x;p;l;h] /\
    eval_operand (Var x) s = SOME (n2w b) /\
    FLOOKUP G x = SOME (base,cap) /\ base <= b /\ b+32+n <= base+cap /\
    b+32 < dimword (:256) /\ n < dimword (:256) /\
    op_taint tn (Var x) = {} /\
    (!i. b <= i /\ i < b+32+n ==> i NOTIN tn.t_mem) /\
    mem_word_at b s.vs_memory = n2w n /\ ~ctx_has_dalloca ctx ==>
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst ia ADD [Var x;Lit 32w] [p];
       mk_inst il MLOAD [Var x] [l];
       mk_inst ih SHA3 [Var p;Var l] [h]] s
      (DRESTRICT (DRESTRICT (G |+ (p,(base,cap))) (COMPL {l})) (COMPL {h}))
      (tn with t_var := tn.t_var |+ (p,{}) |+ (l,{}) |+ (h,{}))
Proof
  rpt gen_tac >> strip_tac >>
  `b < dimword (:256)` by decide_tac >>
  `step_inst_base (mk_inst ia ADD [Var x;Lit 32w] [p]) s =
    OK (update_var p (n2w b+32w) s)` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def, eval_operand_def] >>
  simp[Once inst_seq_ptr_def] >>
  conj_tac >- (irule ptr_inst_ok_copy_len_binop >> simp[op_taint_def]) >>
  rename1 `FLOOKUP G x = SOME (rootbase,cap)` >>
  `step_prov PG G (mk_inst ia ADD [Var x;Lit 32w] [p])
     (update_var p (n2w b+32w) s) = G |+ (p,(rootbase,cap))` by
    (irule (cj 1 hash_add_ghost) >> simp[]) >>
  simp[hash_add_ghost] >>
  qabbrev_tac `s1 = update_var p (n2w b+32w) s with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `G1 = G |+ (p,(rootbase,cap))` >>
  qabbrev_tac `tn1 = tn with t_var := tn.t_var |+ (p,{})` >>
  suspend "load"
QED

Resume map_key_triple[load]:
  rename1 `FLOOKUP G x = SOME (rootbase,cap)` >>
  `eval_operand (Var x) s1 = SOME (n2w b) /\
   FLOOKUP G1 x = SOME (rootbase,cap) /\ op_taint tn1 (Var x) = {} /\
   mem_word_at b s1.vs_memory = n2w n` by
    gvs[Abbr `s1`, Abbr `G1`, Abbr `tn1`, listTheory.ALL_DISTINCT,
      eval_operand_def, lookup_var_def, update_var_def, op_taint_def, FLOOKUP_UPDATE] >>
  `ptr_covers G1 tn1 x s1 32` by
    (simp[ptr_covers_def] >> qexists_tac `n2w b` >>
     fs[eval_operand_def] >> decide_tac) >>
  `!i. b <= i /\ i < b+32 ==> i NOTIN tn1.t_mem` by
    (simp[Abbr `tn1`] >> rpt gen_tac >> strip_tac >>
     qpat_x_assum `!i. _ ==> i NOTIN tn.t_mem` irule >> decide_tac) >>
  `mload b s1 = n2w n` by fs[mem_word_at_eq_mload] >>
  `step_inst_base (mk_inst il MLOAD [Var x] [l]) s1 =
    OK (update_var l (n2w n) s1)` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def] >>
  simp[Once inst_seq_ptr_def] >>
  conj_tac >- (irule ptr_inst_ok_mload >> simp[]) >>
  `step_prov PG G1 (mk_inst il MLOAD [Var x] [l])
    (update_var l (n2w n) s1) = DRESTRICT G1 (COMPL {l})` by
    simp[step_prov_def, set_prov_def, out_prov_def, mk_inst_def] >>
  simp[hash_mload_ghost] >>
  qabbrev_tac `s2 = update_var l (n2w n) s1 with vs_inst_idx := SUC s1.vs_inst_idx` >>
  qabbrev_tac `G2 = DRESTRICT G1 (COMPL {l})` >>
  qabbrev_tac `tn2 = tn1 with t_var := tn1.t_var |+ (l,{})` >>
  suspend "sha"
QED

Resume map_key_triple[sha]:
  `eval_operand (Var p) s2 = SOME (n2w (b+32)) /\
   eval_operand (Var l) s2 = SOME (n2w n) /\
   FLOOKUP G2 p = SOME (rootbase,cap) /\
   op_taint tn2 (Var p) = {} /\ op_taint tn2 (Var l) = {}` by
    gvs[Abbr `s2`, Abbr `s1`, Abbr `G2`, Abbr `G1`, Abbr `tn2`, Abbr `tn1`,
      listTheory.ALL_DISTINCT, eval_operand_def, lookup_var_def,
      update_var_def, op_taint_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, word_add_n2w] >>
  `!i. b+32 <= i /\ i < b+32+n ==> i NOTIN tn2.t_mem` by
    (simp[Abbr `tn2`, Abbr `tn1`] >> rpt gen_tac >> strip_tac >>
     qpat_x_assum `!i. b <= i /\ i < b+32+n ==> _` irule >> decide_tac) >>
  `step_inst_base (mk_inst ih SHA3 [Var p;Var l] [h]) s2 =
    OK (update_var h (word_of_bytes T (0w:bytes32)
      (Keccak_256_w64 (mem_bytes_at (b+32) n s2.vs_memory))) s2)` by
    (irule step_SHA3_bytes >> simp[]) >>
  simp[Once inst_seq_ptr_def] >>
  conj_tac >- (irule hash_sha3_inst_ok >> simp[] >>
    qexistsl_tac [`rootbase`, `cap`] >> simp[] >> decide_tac) >>
  simp[inst_seq_ptr_def, hash_sha3_ghost,
    Abbr `G2`, Abbr `G1`, Abbr `tn2`, Abbr `tn1`]
QED

Finalise map_key_triple

Theorem map_key_inst_seq:
  !D ctx fn PG G tn s x sa op sb b base cap n.
    compile_keccak256_key (Var x) F sa = (op,sb) /\ not_fresh_at sa x /\
    eval_operand (Var x) s = SOME (n2w b) /\
    FLOOKUP G x = SOME (base,cap) /\ base <= b /\ b+32+n <= base+cap /\
    b+32 < dimword (:256) /\ n < dimword (:256) /\
    op_taint tn (Var x) = {} /\
    (!i. b <= i /\ i < b+32+n ==> i NOTIN tn.t_mem) /\
    mem_word_at b s.vs_memory = n2w n /\ ~ctx_has_dalloca ctx ==>
    ?G' tn'. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s G' tn' /\
      op_taint tn' op = {} /\ op_prov G' op = NONE /\
      tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
      tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
      (!z. not_fresh_at sa z ==>
        FLOOKUP G' z = FLOOKUP G z /\
        op_taint tn' (Var z) = op_taint tn (Var z))
Proof
  rpt gen_tac >> strip_tac >> drule map_key_shape >> strip_tac >>
  `ALL_DISTINCT [x;p;l;h]` by
    (fs[listTheory.ALL_DISTINCT] >> metis_tac[]) >>
  rename1 `FLOOKUP G x = SOME (rootbase,cap)` >>
  qexistsl_tac [`DRESTRICT (DRESTRICT (G |+ (p,(rootbase,cap))) (COMPL {l})) (COMPL {h})`,
    `tn with t_var := tn.t_var |+ (p,{}) |+ (l,{}) |+ (h,{})`] >>
  conj_tac >-
    (qpat_x_assum `emitted_insts sa sb = _` (fn th => rewrite_tac[th]) >>
     irule map_key_triple >> simp[] >>
     qexistsl_tac [`b`, `n`] >> simp[] >> decide_tac) >>
  gvs[op_taint_def, op_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> res_tac >> simp[FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]
QED

Theorem map_key_counted:
  !D ctx fn PG G tn s t bb x sa op sb b base cap n.
    compile_keccak256_key (Var x) F sa = (op,sb) /\ not_fresh_at sa x /\
    eval_operand (Var x) s = SOME (n2w b) /\
    FLOOKUP G x = SOME (base,cap) /\ base <= b /\ b+32+n <= base+cap /\
    b+32 < dimword (:256) /\ n < dimword (:256) /\
    op_taint tn (Var x) = {} /\
    (!i. b <= i /\ i < b+32+n ==> i NOTIN tn.t_mem) /\
    mem_word_at b s.vs_memory = n2w n /\ ~ctx_has_dalloca ctx /\
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
    run_inst_seq (emitted_insts sa sb) s = OK t ==>
    ?G' tn'. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
        (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))) /\
      op_taint tn' op = {} /\ op_prov G' op = NONE /\
      tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
      tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
      (!z. not_fresh_at sa z ==>
        FLOOKUP G' z = FLOOKUP G z /\
        op_taint tn' (Var z) = op_taint tn (Var z))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all map_key_inst_seq >>
  disch_then (qspecl_then [`D`, `fn`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`G'`, `tn'`] >> simp[] >>
  drule map_key_shape >> strip_tac >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb)) = 0 /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb)` by simp[mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_path_ptr >> simp[]
QED

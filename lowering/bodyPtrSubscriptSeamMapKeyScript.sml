(* Mapping-key hashes emit ADD before MLOAD, unlike builtin byte hashes.
   Keep that instruction order explicit at the pointer boundary. *)
Theory bodyPtrSubscriptSeamMapKey
Ancestors
  wordLoadStorePtr
  bodyPtrHashBuiltinsKeccakBytesRun exprSimMapKey fragGasSeqPtr
  typedCopyPtr typedCopyLoopHeaderPtr ptrDiscipline venomExecSemantics
  venomState venomInst finite_map words pred_set list arithmetic
  bodyPtrDefs valueEncodingProps bodyPtrHashBuiltinsKeccak exprSimHash
  exprLowering emitHelper emitHelperProps compileEnv loweringStateRelDefs exprLoweringProps
  ASCIInumbers rich_list bodyPtrHashBuiltinsGhostFrame exprSimVVFrame
  bodyPtrHashBuiltinsCases vyperValue vyperTyping vyperStorage byte
  bodyPtrSubscriptSeamMapInterface

Theorem mapping_key_hash_triple:
  !D ctx fn PG G tn s ia il ih x p l h b root cap n.
    ALL_DISTINCT [x;p;l;h] /\
    eval_operand (Var x) s = SOME (n2w b) /\
    FLOOKUP G x = SOME (root,cap) /\ root <= b /\ b+32+n <= root+cap /\
    b+32 < dimword (:256) /\ n < dimword (:256) /\
    op_taint tn (Var x) = {} /\
    (!i. b <= i /\ i < b+32+n ==> i NOTIN tn.t_mem) /\
    mem_word_at b s.vs_memory = n2w n /\ ~ctx_has_dalloca ctx ==>
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst ia ADD [Var x;Lit 32w] [p];
       mk_inst il MLOAD [Var x] [l];
       mk_inst ih SHA3 [Var p;Var l] [h]] s
      (DRESTRICT (DRESTRICT (G |+ (p,(root,cap))) (COMPL {l})) (COMPL {h}))
      (tn with t_var := tn.t_var |+ (p,{}) |+ (l,{}) |+ (h,{}))
Proof
  rpt gen_tac >> strip_tac >>
  `b < dimword (:256)` by decide_tac >>
  `step_inst_base (mk_inst ia ADD [Var x;Lit 32w] [p]) s =
    OK (update_var p (n2w b+32w) s)` by
    (simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def, eval_operand_def]) >>
  simp[Once inst_seq_ptr_def] >>
  conj_tac >- (irule ptr_inst_ok_copy_len_binop >> simp[op_taint_def]) >>
  simp[hash_add_ghost] >>
  qabbrev_tac `s1 = update_var p (n2w b+32w) s with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `G1 = G |+ (p,(root,cap))` >>
  qabbrev_tac `tn1 = tn with t_var := tn.t_var |+ (p,{})` >>
  suspend "load"
QED

Resume mapping_key_hash_triple[load]:
  `step_prov PG G (mk_inst ia ADD [Var x;Lit 32w] [p])
     (update_var p (n2w b+32w) s) = G1` by
    (simp[Abbr `G1`] >> irule (cj 1 hash_add_ghost) >> simp[]) >>
  asm_rewrite_tac[] >>
  `eval_operand (Var x) s1 = SOME (n2w b) /\
   FLOOKUP G1 x = SOME (root,cap) /\ op_taint tn1 (Var x) = {}` by
    gvs[Abbr `s1`, Abbr `G1`, Abbr `tn1`, ALL_DISTINCT,
        eval_operand_def, lookup_var_def, update_var_def, op_taint_def,
        FLOOKUP_UPDATE] >>
  `!i. b <= i /\ i < b+32 ==> i NOTIN tn1.t_mem` by
    (simp[Abbr `tn1`] >> rpt strip_tac >>
     qpat_x_assum `!i. _ ==> i NOTIN tn.t_mem` irule >> decide_tac) >>
  `ptr_covers G1 tn1 x s1 32` by
    (simp[ptr_covers_def] >> qexists `n2w b` >>
     fs[eval_operand_def] >> decide_tac) >>
  `mload b s1 = n2w n` by
    gvs[Abbr `s1`, update_var_def, GSYM mem_word_at_eq_mload] >>
  `step_inst_base (mk_inst il MLOAD [Var x] [l]) s1 =
    OK (update_var l (n2w n) s1)` by
    (simp[step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def]) >>
  simp[Once inst_seq_ptr_def] >>
  conj_tac >- (irule ptr_inst_ok_mload >> simp[]) >>
  simp[hash_mload_ghost] >>
  qabbrev_tac `s2 = update_var l (n2w n) s1 with vs_inst_idx := SUC s1.vs_inst_idx` >>
  qabbrev_tac `G2 = DRESTRICT G1 (COMPL {l})` >>
  qabbrev_tac `tn2 = tn1 with t_var := tn1.t_var |+ (l,{})` >>
  suspend "hash"
QED

Resume mapping_key_hash_triple[hash]:
  `step_prov PG G1 (mk_inst il MLOAD [Var x] [l])
     (update_var l (n2w n) s1) = G2` by
    simp[Abbr `G2`, step_prov_def, set_prov_def, out_prov_def, mk_inst_def] >>
  asm_rewrite_tac[] >>
  `eval_operand (Var p) s2 = SOME (n2w (b+32)) /\
   eval_operand (Var l) s2 = SOME (n2w n) /\
   FLOOKUP G2 p = SOME (root,cap) /\
   op_taint tn2 (Var p) = {} /\ op_taint tn2 (Var l) = {}` by
    gvs[Abbr `s2`, Abbr `s1`, Abbr `G2`, Abbr `G1`,
        Abbr `tn2`, Abbr `tn1`, ALL_DISTINCT, eval_operand_def,
        lookup_var_def, update_var_def, op_taint_def, FLOOKUP_UPDATE,
        FLOOKUP_DRESTRICT, word_add_n2w] >>
  `!i. b+32 <= i /\ i < b+32+n ==> i NOTIN tn2.t_mem` by
    (simp[Abbr `tn2`, Abbr `tn1`] >> rpt strip_tac >>
     qpat_x_assum `!i. b <= i /\ i < b+32+n ==> _` irule >> decide_tac) >>
  `step_inst_base (mk_inst ih SHA3 [Var p;Var l] [h]) s2 =
    OK (update_var h (word_of_bytes T (0w:bytes32)
      (Keccak_256_w64 (mem_bytes_at (b+32) n s2.vs_memory))) s2)` by
    (irule step_SHA3_bytes >> simp[]) >>
  simp[Once inst_seq_ptr_def] >>
  conj_tac
  >- (irule hash_sha3_inst_ok >> simp[] >> qexistsl [`root`, `cap`] >> decide_tac) >>
  simp[inst_seq_ptr_def, hash_sha3_ghost, Abbr `G2`, Abbr `G1`,
       Abbr `tn2`, Abbr `tn1`, ALL_DISTINCT] >>
  simp[hash_add_ghost, hash_mload_ghost] >>
  gvs[ALL_DISTINCT] >>
  simp[step_prov_def, set_prov_def, out_prov_def, first_prov_def,
       op_prov_def, mk_inst_def, FLOOKUP_DRESTRICT]
QED

Finalise mapping_key_hash_triple

Theorem mapping_key_hash_emission:
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
    emitted_insts_def, DROP_LENGTH_APPEND, ADD_ASSOC] >>
  strip_tac >> gvs[APPEND_ASSOC, DROP_LENGTH_APPEND]
QED

Theorem mapping_key_hash_shape:
  !x sa op sb.
    compile_keccak256_key x F sa = (op,sb) ==>
    ?ia il ih p l h.
      emitted_insts sa sb =
        [mk_inst ia ADD [x;Lit 32w] [p]; mk_inst il MLOAD [x] [l];
         mk_inst ih SHA3 [Var p;Var l] [h]] /\
      op = Var h /\ ALL_DISTINCT [p;l;h] /\
      (!z. not_fresh_at sa z ==> z <> p /\ z <> l /\ z <> h)
Proof
  rpt gen_tac >> strip_tac >> drule mapping_key_hash_emission >> strip_tac >>
  qexistsl [`sa.cs_next_id`, `sa.cs_next_id+1`, `sa.cs_next_id+2`,
    `STRING #"%" (toString sa.cs_next_var)`,
    `STRING #"%" (toString (sa.cs_next_var+1))`,
    `STRING #"%" (toString (sa.cs_next_var+2))`] >>
  simp[toString_inj] >>
  rpt strip_tac >> gvs[not_fresh_at_def, toString_inj]
QED

Theorem mapping_key_hash_inst_seq:
  !D ctx fn PG G tn s x sa op sb b root cap n.
    compile_keccak256_key (Var x) F sa = (op,sb) /\ not_fresh_at sa x /\
    eval_operand (Var x) s = SOME (n2w b) /\
    FLOOKUP G x = SOME (root,cap) /\ root <= b /\ b+32+n <= root+cap /\
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
  rpt gen_tac >> strip_tac >> drule mapping_key_hash_shape >> strip_tac >>
  `ALL_DISTINCT [x;p;l;h]` by
    (fs[ALL_DISTINCT] >> metis_tac[]) >>
  qexistsl [`DRESTRICT (DRESTRICT (G |+ (p,(root,cap))) (COMPL {l})) (COMPL {h})`,
    `tn with t_var := tn.t_var |+ (p,{}) |+ (l,{}) |+ (h,{})`] >>
  conj_tac
  >- (qpat_x_assum `emitted_insts sa sb = _` (fn th => rewrite_tac[th]) >>
      irule mapping_key_hash_triple >> simp[] >>
      qexistsl [`b`, `n`] >> simp[] >> decide_tac) >>
  gvs[op_taint_def, op_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> res_tac >> simp[FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]
QED

Theorem mapping_key_hash_counted:
  !D ctx fn PG G tn s t bb x sa op sb b root cap n.
    compile_keccak256_key (Var x) F sa = (op,sb) /\ not_fresh_at sa x /\
    eval_operand (Var x) s = SOME (n2w b) /\
    FLOOKUP G x = SOME (root,cap) /\ root <= b /\ b+32+n <= root+cap /\
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
  drule_all mapping_key_hash_inst_seq >>
  disch_then (qspecl_then [`D`, `fn`, `PG`] strip_assume_tac) >>
  qexistsl [`G'`, `tn'`] >> simp[] >>
  drule mapping_key_hash_shape >> strip_tac >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb)) = 0 /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb)` by simp[mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_path_ptr >> simp[]
QED

Theorem mapping_key_hash_ptr_frame:
  !D ctx fn PG G tn s bb x sa op sb b root cap bs cenv cx es d.
    compile_keccak256_key (Var x) F sa = (op,sb) /\ not_fresh_at sa x /\
    eval_operand (Var x) s = SOME (n2w b) /\
    FLOOKUP G x = SOME (root,cap) /\ root <= b /\
    b+32+LENGTH bs <= root+cap /\
    b+32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
    op_taint tn (Var x) = {} /\
    (!i. b <= i /\ i < b+32+LENGTH bs ==> i NOTIN tn.t_mem) /\
    mem_word_at b s.vs_memory = n2w (LENGTH bs) /\
    mem_bytes_at (b+32) (LENGTH bs) s.vs_memory = bs /\
    stmt_state_rel ctx fn cenv cx es s /\ local_ptrs_reserved cenv sa /\
    ghost_inv d cenv cx es G tn s /\
    (!p k. cenv.ce_return_buf = SOME (PtrVar (Var p) k) ==> not_fresh_at sa p) /\
    (!p k. cenv.ce_return_pc = SOME (PtrVar (Var p) k) ==> not_fresh_at sa p) /\
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
    ?t G' tn'. run_inst_seq (emitted_insts sa sb) s = OK t /\
      t.vs_current_bb = s.vs_current_bb /\
      gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
        (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))) /\
      eval_operand op t = SOME (word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)) /\
      stmt_state_rel ctx fn cenv cx es t /\
      ghost_inv d cenv cx es G' tn' t /\
      ghost_kept cenv es sa G tn s G' tn' /\ op_taint tn' op = {} /\
      op_prov G' op = NONE /\
      ghost_inv d cenv cx es G' tn'
        (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)) /\
      (t with vs_vars := s.vs_vars) = s /\
      (!z. not_fresh_at sa z ==> lookup_var z t = lookup_var z s)
Proof
  rpt gen_tac >> strip_tac >>
  `!z. Var x = Var z ==> not_fresh_at sa z` by simp[] >>
  drule_all compile_keccak256_key_run >> strip_tac >>
  `stmt_state_rel ctx fn cenv cx es t` by
    (irule hash_readonly_state_rel >> goal_assum (drule_at Any) >> simp[]) >>
  `t.vs_current_bb = s.vs_current_bb` by
    (qpat_x_assum `t with vs_vars := _ = _` mp_tac >>
     simp[venom_state_component_equality]) >>
  drule_all mapping_key_hash_counted >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  `ghost_inv d cenv cx es G' tn' t` by
    (irule hash_readonly_ghost_inv >> qexistsl [`G`, `s`, `sa`, `tn`] >>
     simp[] >> metis_tac[]) >>
  `ghost_kept cenv es sa G tn s G' tn'` by
    (irule hash_ghost_kept_frame >> simp[]) >>
  qexistsl [`t`, `G'`, `tn'`] >> simp[hash_ghost_inv_inst_idx]
QED

Theorem mapping_key_bytestring_input:
  expr_post ctx fn cenv cx e es sa sm s0 ee kv op s /\
  is_bytestring_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv kv /\
  ptr_val_ok cx (expr_type e) kv op G tn s ==>
  ?b bs p root cap.
    op = Var p /\ eval_operand op s = SOME (n2w b) /\
    FLOOKUP G p = SOME (root,cap) /\ root <= b /\
    b+32+LENGTH bs <= root+cap /\
    (!i. b <= i /\ i < b+32+LENGTH bs ==> i NOTIN tn.t_mem) /\
    mem_word_at b s.vs_memory = n2w (LENGTH bs) /\
    mem_bytes_at (b+32) (LENGTH bs) s.vs_memory = bs /\
    b+32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
    encode_hashmap_key (expr_type e) kv = word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)
Proof
  strip_tac >> Cases_on `expr_type e` >> gvs[is_bytestring_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  gvs[is_bytestring_type_def, evaluate_type_def]
  >- (Cases_on `kv` >> gvs[value_has_type_def] >>
      `evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (StringT n))` by
        simp[evaluate_type_def] >>
      drule_all hash_string_post_view >> strip_tac >>
      drule hash_string_operand >> simp[is_word_type_def, evaluate_type_def] >> strip_tac >>
      gvs[ptr_covers_def, eval_operand_def] >>
      qexistsl [`b`, `MAP (n2w o ORD) s'`] >>
      simp[encode_hashmap_key_def, word_of_bytes_be_def, LENGTH_MAP,
           vyperMiscTheory.n2w_o_ORD_eq]) >>
  rename1 `BytesT bound` >> Cases_on `bound` >>
  gvs[is_bytestring_type_def, evaluate_type_def] >>
  Cases_on `kv` >> gvs[value_has_type_def] >>
  rename1 `BytesV bs` >> rename1 `Dynamic cap` >>
  `evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (BytesT (Dynamic cap)))` by
    simp[evaluate_type_def] >>
  drule_all hash_dynamic_post_view >> strip_tac >>
  drule hash_dynamic_bytes_operand >> simp[is_word_type_def, evaluate_type_def] >> strip_tac >>
  gvs[ptr_covers_def, eval_operand_def] >>
  qexistsl [`b`, `bs`] >>
  simp[encode_hashmap_key_def, word_of_bytes_be_def]
QED

(* Instruction and counted-run boundary for covered clean byte strings. *)
Theory bodyPtrHashBuiltinsKeccakBytesRun
Ancestors wordLoadStorePtr bodyPtrHashBuiltinsKeccakShape bodyPtrHashBuiltinsKeccak
  typedCopyPtr typedCopyLoopHeaderPtr bodyPtrDefs fragGasSeqPtr
  ghostPcTransportPtr instIdxIndep ptrDiscipline venomState venomInst
  venomExecSemantics words finite_map pred_set contextCodegenRel codegenRel valueEncodingProps exprSimHash

Theorem hash_mload_ghost:
  !PG G tn s id src out a v.
    eval_operand src s = SOME a /\
    (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem) ==>
    step_prov PG G (mk_inst id MLOAD [src] [out]) (update_var out v s) =
      DRESTRICT G (COMPL {out}) /\
    step_taint (mk_inst id MLOAD [src] [out]) s (update_var out v s) tn =
      tn with t_var := tn.t_var |+ (out,{})
Proof
  rpt gen_tac >> strip_tac >>
  `mem_word_taint tn.t_mem (w2n a) = {}` by
    (simp[mem_word_taint_def, EXTENSION] >> rpt strip_tac >>
     Cases_on `x < 32` >> simp[] >> metis_tac[arithmeticTheory.LESS_EQ_ADD]) >>
  `new_site_bytes s (update_var out v s) = {}` by
    simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF, EXTENSION, SF CONJ_ss] >>
  simp[step_prov_def, set_prov_def, out_prov_def, step_taint_def,
    mk_inst_def, set_var_taint_def, out_taint_def, op_taint_def,
    store_taint_def, adopt_reset_def, mem_taint_def, step_writes_def,
    source_memory_write_ranges_def, written_taint_def, range_bytes_def,
    imm_taint_def, taint_component_equality]
QED

Theorem hash_add_ghost:
  !PG G tn s id src out off v base cap.
    (FLOOKUP G src = SOME (base,cap) ==>
     step_prov PG G (mk_inst id ADD [Var src;Lit off] [out]) (update_var out v s) =
       G |+ (out,(base,cap))) /\
    step_taint (mk_inst id ADD [Var src;Lit off] [out]) s (update_var out v s) tn =
      tn with t_var := tn.t_var |+ (out,{})
Proof
  rpt gen_tac >>
  `new_site_bytes s (update_var out v s) = {}` by
    simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF, EXTENSION, SF CONJ_ss] >>
  Cases_on `eval_operand (Var src) s` >>
  simp[step_prov_def, set_prov_def, out_prov_def, first_prov_def,
    op_prov_def, step_taint_def, mk_inst_def, set_var_taint_def,
    out_taint_def, store_taint_def, adopt_reset_def, mem_taint_def,
    step_writes_def, source_memory_write_ranges_def, written_taint_def,
    range_bytes_def, imm_taint_def, taint_component_equality]
QED

Theorem hash_keccak_bytes_triple:
  !D ctx fn PG G tn s il ia ih x l p h b base cap n.
    ALL_DISTINCT [x;l;p;h] /\
    eval_operand (Var x) s = SOME (n2w b) /\
    FLOOKUP G x = SOME (base,cap) /\ base <= b /\ b+32+n <= base+cap /\
    b+32 < dimword (:256) /\ n < dimword (:256) /\
    op_taint tn (Var x) = {} /\
    (!i. b <= i /\ i < b+32+n ==> i NOTIN tn.t_mem) /\
    mem_word_at b s.vs_memory = n2w n /\ ~ctx_has_dalloca ctx ==>
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst il MLOAD [Var x] [l];
       mk_inst ia ADD [Var x;Lit 32w] [p];
       mk_inst ih SHA3 [Var p;Var l] [h]] s
      (DRESTRICT (DRESTRICT G (COMPL {l}) |+ (p,(base,cap))) (COMPL {h}))
      (tn with t_var := tn.t_var |+ (l,{}) |+ (p,{}) |+ (h,{}))
Proof
  rpt gen_tac >> strip_tac >>
  `b < dimword (:256)` by decide_tac >>
  `w2n (n2w b:bytes32) = b` by simp[] >>
  `ptr_covers G tn x s 32` by
    (simp[ptr_covers_def] >> qexists_tac `n2w b` >>
     fs[eval_operand_def] >> decide_tac) >>
  `!i. b <= i /\ i < b+32 ==> i NOTIN tn.t_mem` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `!i. _ ==> i NOTIN tn.t_mem` irule >> decide_tac) >>
  `mload b s = n2w n` by fs[mem_word_at_eq_mload] >>
  `step_inst_base (mk_inst il MLOAD [Var x] [l]) s = OK (update_var l (n2w n) s)` by
    (pure_once_rewrite_tac[step_inst_base_def] >>
     simp[mk_inst_def, exec_read1_def]) >>
  simp[Once inst_seq_ptr_def] >>
  conj_tac >- (irule ptr_inst_ok_mload >> simp[]) >>
  simp[hash_mload_ghost] >>
  qabbrev_tac `s1 = update_var l (n2w n) s with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `G1 = DRESTRICT G (COMPL {l})` >>
  qabbrev_tac `tn1 = tn with t_var := tn.t_var |+ (l,{})` >>
  suspend "add"
QED

Resume hash_keccak_bytes_triple[add]:
  `step_prov PG G (mk_inst il MLOAD [Var x] [l]) (update_var l (n2w n) s) = G1` by
    simp[Abbr `G1`, step_prov_def, set_prov_def, out_prov_def, mk_inst_def] >>
  rename1 `FLOOKUP G x = SOME (rootbase,cap)` >>
  `eval_operand (Var x) s1 = SOME (n2w b) /\
   eval_operand (Var l) s1 = SOME (n2w n) /\
   FLOOKUP G1 x = SOME (rootbase,cap) /\ op_taint tn1 (Var x) = {}` by
    gvs[Abbr `s1`, Abbr `G1`, Abbr `tn1`, listTheory.ALL_DISTINCT,
      eval_operand_def, lookup_var_def, update_var_def, op_taint_def,
      FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  `step_inst_base (mk_inst ia ADD [Var x;Lit 32w] [p]) s1 =
    OK (update_var p (n2w b + 32w) s1)` by
    (pure_once_rewrite_tac[step_inst_base_def] >> simp[mk_inst_def, exec_pure2_def, eval_operand_def]) >>
  simp[Once inst_seq_ptr_def] >>
  conj_tac >- (irule ptr_inst_ok_copy_len_binop >> simp[op_taint_def]) >>
  suspend "sha"
QED

Resume hash_keccak_bytes_triple[sha]:
  simp[hash_add_ghost] >>
  qabbrev_tac `s2 = update_var p (n2w b+32w) s1 with vs_inst_idx := SUC s1.vs_inst_idx` >>
  qabbrev_tac `G2 = G1 |+ (p,(rootbase,cap))` >>
  qabbrev_tac `tn2 = tn1 with t_var := tn1.t_var |+ (p,{})` >>
  `eval_operand (Var p) s2 = SOME (n2w (b+32)) /\
   eval_operand (Var l) s2 = SOME (n2w n) /\
   FLOOKUP G2 p = SOME (rootbase,cap) /\
   op_taint tn2 (Var p) = {} /\ op_taint tn2 (Var l) = {}` by
    gvs[Abbr `s2`, Abbr `G2`, Abbr `tn2`, Abbr `tn1`,
      listTheory.ALL_DISTINCT, eval_operand_def, lookup_var_def,
      update_var_def, op_taint_def, FLOOKUP_UPDATE, word_add_n2w] >>
  `!i. b+32 <= i /\ i < b+32+n ==> i NOTIN tn2.t_mem` by
    (simp[Abbr `tn2`, Abbr `tn1`] >> rpt gen_tac >> strip_tac >>
     qpat_x_assum `!i. b <= i /\ i < b+32+n ==> _` irule >> decide_tac) >>
  `step_inst_base (mk_inst ih SHA3 [Var p;Var l] [h]) s2 =
    OK (update_var h (word_of_bytes T (0w:bytes32)
      (Keccak_256_w64 (mem_bytes_at (b+32) n s2.vs_memory))) s2)` by
    (irule step_SHA3_bytes >> simp[]) >>
  simp[Once inst_seq_ptr_def] >>
  conj_tac >- suspend "check" >>
  simp[inst_seq_ptr_def, hash_sha3_ghost,
    Abbr `G2`, Abbr `G1`, Abbr `tn2`, Abbr `tn1`, listTheory.ALL_DISTINCT] >>
  simp[hash_add_ghost, FLOOKUP_DRESTRICT] >>
  gvs[listTheory.ALL_DISTINCT] >>
  simp[step_prov_def, set_prov_def, out_prov_def, first_prov_def,
    op_prov_def, mk_inst_def, FLOOKUP_DRESTRICT]
QED

Resume hash_keccak_bytes_triple[check]:
  irule hash_sha3_inst_ok >> simp[] >>
  qexistsl_tac [`rootbase`, `cap`] >>
  simp[step_prov_def, set_prov_def, out_prov_def, first_prov_def,
    op_prov_def, mk_inst_def] >> decide_tac
QED

Finalise hash_keccak_bytes_triple

Theorem hash_keccak_bytes_inst_seq:
  !D ctx fn PG G tn s x sa op sb b base cap n.
    compile_keccak256_bytes (Var x) sa = (op,sb) /\ not_fresh_at sa x /\
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
  rpt gen_tac >> strip_tac >> drule hash_keccak_bytes_shape >> strip_tac >>
  `ALL_DISTINCT [x;l;p;h]` by
    (fs[listTheory.ALL_DISTINCT] >> metis_tac[]) >>
  rename1 `FLOOKUP G x = SOME (rootbase,cap)` >>
  qexistsl_tac [`DRESTRICT (DRESTRICT G (COMPL {l}) |+ (p,(rootbase,cap))) (COMPL {h})`,
    `tn with t_var := tn.t_var |+ (l,{}) |+ (p,{}) |+ (h,{})`] >>
  conj_tac >-
    (qpat_x_assum `emitted_insts sa sb = _` (fn th => rewrite_tac[th]) >>
     irule hash_keccak_bytes_triple >> simp[] >>
     qexistsl_tac [`b`, `n`] >> simp[] >> decide_tac) >>
  gvs[op_taint_def, op_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> res_tac >> simp[FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]
QED

Theorem hash_keccak_bytes_counted:
  !D ctx fn PG G tn s t bb x sa op sb b base cap n.
    compile_keccak256_bytes (Var x) sa = (op,sb) /\ not_fresh_at sa x /\
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
  drule_all hash_keccak_bytes_inst_seq >>
  disch_then (qspecl_then [`D`, `fn`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`G'`, `tn'`] >> simp[] >>
  drule hash_keccak_bytes_shape >> strip_tac >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb)) = 0 /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb)` by simp[mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_path_ptr >> simp[]
QED

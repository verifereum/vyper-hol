(* Direct readonly Keccak certificates at an arbitrary allocation bound. *)
Theory bodyFullHashKeccakBytes
Ancestors
  bodyPtrHashBuiltinsKeccakBytesRun bodyPtrHashBuiltinsCursor
  bodyPtrHashBuiltinsKeccakShape
  bodyFullGhostFrame instSeqPtrLo fragGasSeqPtr ptrSafetyTransport ghostPcTransportPtr
  exprSimHash exprLoweringProps allocaHistoryFragment bodyPtrDefs
  loweringStateRelDefs venomState venomInst
  ptrDiscipline words list finite_map
  exprPtrCtorImmStore exprPtrUnwrapScalarEdges
  venomExecSemantics
  bodyPtrHashBuiltinsKeccak bodyPtrHashBuiltinsBoundary ptrSafeRun valueEncodingProps

Theorem bytes_triple_checked[local]:
  !D ctx fn PG G tn s il ia ih x l p h b base cap n.
    ALL_DISTINCT [x;l;p;h] /\
    eval_operand (Var x) s = SOME (n2w b) /\
    FLOOKUP G x = SOME (base,cap) /\ base <= b /\ b+32+n <= base+cap /\
    b+32 < dimword (:256) /\ n < dimword (:256) /\
    op_taint tn (Var x) = {} /\
    (!i. b <= i /\ i < b+32+n ==> i NOTIN tn.t_mem) /\
    mem_word_at b s.vs_memory = n2w n /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
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
    (pure_once_rewrite_tac[step_inst_base_def] >> simp[mk_inst_def, exec_read1_def]) >>
  simp[Once inst_seq_ptr_def] >>
  conj_tac >- (irule ptr_inst_ok_mload_lo >> simp[allocas_from_def]) >>
  simp[hash_mload_ghost] >>
  qabbrev_tac `s1 = update_var l (n2w n) s with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `G1 = DRESTRICT G (COMPL {l})` >>
  qabbrev_tac `tn1 = tn with t_var := tn.t_var |+ (l,{})` >>
  suspend "add"
QED

Resume bytes_triple_checked[add]:
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
  conj_tac >- (irule ptr_inst_ok_copy_arith >>
    simp[op_taint_def, allocas_from_def, Abbr `s1`, update_var_def, allocas_below_fmp_def]) >>
  suspend "sha"
QED

Resume bytes_triple_checked[sha]:
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

Resume bytes_triple_checked[check]:
  `access_ok 0 G2 fn (mk_inst ih SHA3 [Var p;Var l] [h]) s2` by
    (irule hash_sha3_access >> simp[] >>
     qexistsl_tac [`rootbase`, `cap`] >> decide_tac) >>
  `taint_ok fn tn2 (mk_inst ih SHA3 [Var p;Var l] [h]) s2` by
    (irule hash_sha3_taint >> simp[]) >>
  gvs[Abbr `G2`, Abbr `G1`, step_prov_def, set_prov_def,
    out_prov_def, first_prov_def, op_prov_def, mk_inst_def,
    FLOOKUP_DRESTRICT] >>
  simp[ptr_inst_ok_def, allocas_from_def, mk_inst_def, step_inst_non_invoke] >>
  simp[Abbr `s2`, Abbr `s1`, update_var_def, allocas_below_fmp_def] >>
  rpt strip_tac >> gvs[update_var_def]
QED

Finalise bytes_triple_checked

Theorem bytes_sequence_checked[local]:
  !D ctx fn PG G tn s x sa op sb b base cap n.
    compile_keccak256_bytes (Var x) sa = (op,sb) /\ not_fresh_at sa x /\
    eval_operand (Var x) s = SOME (n2w b) /\
    FLOOKUP G x = SOME (base,cap) /\ base <= b /\ b+32+n <= base+cap /\
    b+32 < dimword (:256) /\ n < dimword (:256) /\
    op_taint tn (Var x) = {} /\
    (!i. b <= i /\ i < b+32+n ==> i NOTIN tn.t_mem) /\
    mem_word_at b s.vs_memory = n2w n /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
    ?G' tn'. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s G' tn' /\
      op_taint tn' op = {} /\ op_prov G' op = NONE /\
      tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
      tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
      (!z. not_fresh_at sa z ==>
        FLOOKUP G' z = FLOOKUP G z /\ op_taint tn' (Var z) = op_taint tn (Var z))
Proof
  rpt gen_tac >> strip_tac >> drule hash_keccak_bytes_shape >> strip_tac >>
  `ALL_DISTINCT [x;l;p;h]` by
    (fs[listTheory.ALL_DISTINCT] >> metis_tac[]) >>
  rename1 `FLOOKUP G x = SOME (rootbase,cap)` >>
  qexistsl_tac [`DRESTRICT (DRESTRICT G (COMPL {l}) |+ (p,(rootbase,cap))) (COMPL {h})`,
    `tn with t_var := tn.t_var |+ (l,{}) |+ (p,{}) |+ (h,{})`] >>
  conj_tac >-
    (qpat_x_assum `emitted_insts sa sb = _` (fn th => rewrite_tac[th]) >>
     irule bytes_triple_checked >> simp[] >>
     qexistsl_tac [`b`, `n`] >> simp[] >> decide_tac) >>
  gvs[op_taint_def, op_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> res_tac >> simp[FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]
QED

Theorem bytes_origin_frame[local]:
  !x sa op sb s b G base cap bs ctx fn tn bb lo t explicit PG.
  compile_keccak256_bytes (Var x) sa = (op,sb) /\ not_fresh_at sa x /\
  eval_operand (Var x) s = SOME (n2w b) /\
  FLOOKUP G x = SOME (base:num,cap:num) /\ base <= b /\
  b+32+LENGTH bs <= base+cap /\
  b+32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
  op_taint tn (Var x) = {} /\
  (!i. b <= i /\ i < b+32+LENGTH bs ==> i NOTIN tn.t_mem) /\
  mem_word_at b s.vs_memory = n2w (LENGTH bs) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  run_inst_seq_mem_ok (emitted_insts sa sb) s /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)),Gf,tnf)) /\
    op_taint tnf op = {} /\ op_prov Gf op = NONE /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!z. not_fresh_at sa z ==> FLOOKUP Gf z = FLOOKUP G z /\
      op_taint tnf (Var z) = op_taint tn (Var z))
Proof
  rpt gen_tac >> strip_tac >> drule_all bytes_sequence_checked >>
  disch_then (qspecl_then [`ARB`, `fn`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`G'`, `tn'`] >> simp[] >> gen_tac >>
  `inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s G' tn'` by
    (drule_all bytes_sequence_checked >>
     disch_then (qspecl_then [`D`, `fn`, `PG`] strip_assume_tac) >>
     `G' = G'' /\ tn' = tn''` by metis_tac[inst_seq_ptr_ghost_unique] >>
     gvs[] >> irule inst_seq_ptr_zero_to_lo >> simp[] >>
     qexists_tac `D` >> simp[]) >>
  drule hash_keccak_bytes_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb) /\
   FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_origin_ptr_path >> simp[]
QED

Theorem hash_bytes_keccak_joint_run:
  !ctx fn PG G tn s bb x sa op sb b base cap bs cenv cx es d lo explicit.
    compile_keccak256_bytes (Var x) sa = (op,sb) /\ not_fresh_at sa x /\
    eval_operand (Var x) s = SOME (n2w b) /\
    FLOOKUP G x = SOME (base,cap) /\ base <= b /\
    b+32+LENGTH bs <= base+cap /\
    b+32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
    op_taint tn (Var x) = {} /\
    (!i. b <= i /\ i < b+32+LENGTH bs ==> i NOTIN tn.t_mem) /\
    mem_word_at b s.vs_memory = n2w (LENGTH bs) /\
    mem_bytes_at (b+32) (LENGTH bs) s.vs_memory = bs /\
    local_ptrs_reserved cenv sa /\
    (!p k. cenv.ce_return_buf = SOME (PtrVar (Var p) k) ==> not_fresh_at sa p) /\
    (!p k. cenv.ce_return_pc = SOME (PtrVar (Var p) k) ==> not_fresh_at sa p) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
    allocas_from lo s /\ lo <= s.vs_alloca_next /\
    run_inst_seq_mem_ok (emitted_insts sa sb) s ==>
    ?t Gf tnf.
      run_inst_seq (emitted_insts sa sb) s = OK t /\
      t.vs_current_bb = s.vs_current_bb /\
      eval_operand op t = SOME (word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)) /\
      op_taint tnf op = {} /\ op_prov Gf op = NONE /\
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
        (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)),Gf,tnf)) /\
      (!z. not_fresh_at sa z ==> lookup_var z t = lookup_var z s) /\
      t.vs_alloca_next = s.vs_alloca_next /\
      (!H D. stmt_state_rel (H:(bool # 256 word # type_value) list # num list) ctx fn cenv cx es s /\
        ghost_inv_at D lo d cenv cx es G tn s ==>
        stmt_state_rel H ctx fn cenv cx es t /\
        ghost_inv_at D lo d cenv cx es Gf tnf t /\
        ghost_kept_at lo cenv es sa G tn s Gf tnf) /\
      eval_operand op (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)) =
        SOME (word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)) /\
      (!H D. stmt_state_rel (H:(bool # 256 word # type_value) list # num list) ctx fn cenv cx es s /\
        ghost_inv_at D lo d cenv cx es G tn s ==>
        stmt_state_rel H ctx fn cenv cx es
          (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)) /\
        ghost_inv_at D lo d cenv cx es Gf tnf
          (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))) /\
      (fn_inst_ids_distinct fn /\ alloca_history fn s /\ alloca_inv s ==>
        alloca_history fn
          (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)))
Proof
  rpt gen_tac >> strip_tac >>
  `!z. Var x = Var z ==> not_fresh_at sa z` by simp[] >>
  drule_all compile_keccak256_bytes_run >> strip_tac >>
  drule_all bytes_origin_frame >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`t`, `Gf`, `tnf`] >> simp[] >>
  `t.vs_current_bb = s.vs_current_bb /\
   t.vs_alloca_next = s.vs_alloca_next /\
   t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
   t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
   t.vs_transient = s.vs_transient /\ t.vs_immutables = s.vs_immutables` by
    (qpat_x_assum `(t with vs_vars := s.vs_vars) = s` mp_tac >>
     simp[venom_state_component_equality] >> metis_tac[]) >>
  simp[] >> conj_asm1_tac
  >- (rpt gen_tac >> strip_tac >> conj_tac
      >- (drule_all compile_keccak256_bytes_frame >> strip_tac >> gvs[]) >>
      conj_tac
      >- (irule ghost_inv_at_exterior_frame >> simp[] >>
          qexistsl_tac [`G`, `es`, `s`, `sa`, `tn`] >> simp[]) >>
      simp[ghost_kept_at_def]) >>
  conj_tac
  >- (simp[stmt_state_rel_inst_idx, ghost_inv_at_inst_idx] >>
      rpt gen_tac >> strip_tac >>
      qpat_x_assum `!H D. _` (qspecl_then [`H`, `D`] mp_tac) >> simp[]) >>
  strip_tac >> drule hash_keccak_bytes_shape >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    simp[mk_inst_def, is_terminator_def] >>
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  irule alloca_history_run_inst_seq >> goal_assum (drule_at Any) >>
  simp[] >> gvs[rich_listTheory.IS_PREFIX_APPEND] >> metis_tac[]
QED

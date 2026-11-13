Theory abiBytesEncoderJointGhost
Ancestors
  abiBytestringCode abiEncoderRounding abiEncoderWindowBytes
  abiBytesEncoderPrefixGhost abiBytesEncoderCopyGhost abiBytesEncoderSuffixGhost
  instSeqComposePtr ghostPcTransportPtr exprLoweringProps loweringStateRelDefs
  fragGasSeqPtr bodyPtrDefs ptrCoverage ptrSafetyTransport
  ptrSafeRun ptrDiscipline venomInstProofs venomExecSemantics
  venomMemDefs venomState venomInst words list arithmetic finite_map

Theorem bytes_encoder_joint_ghosts:
  compile_abi_encode_to_buf (Var dst) (Var src) (AbiBytestring maxlen) st =
    (out,en) /\
  fn_has_code st en func /\ not_fresh_at st dst /\ not_fresh_at st src /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  eval_operand (Var src) s = SOME p /\
  eval_operand (Var dst) s = SOME q /\
  mload (w2n p) s = n2w (LENGTH bs) /\
  read_memory (w2n p + 32) (LENGTH bs) s = bs /\
  w2n p + 32 + LENGTH bs <= s.vs_alloca_next /\
  w2n p + 32 + LENGTH bs < dimword (:256) /\
  w2n q + 32 + contractABI$ceil32 (LENGTH bs) <= s.vs_alloca_next /\
  w2n q + 32 + contractABI$ceil32 (LENGTH bs) < dimword (:256) /\
  venomMemDefs$regions_disjoint (w2n p,32 + LENGTH bs)
    (w2n q,32 + contractABI$ceil32 (LENGTH bs)) /\
  ptr_covers G tn src s (32 + LENGTH bs) /\
  ptr_covers G tn dst s (32 + contractABI$ceil32 (LENGTH bs)) /\
  (!i. w2n p <= i /\ i < w2n p + 32 + LENGTH bs ==>
       i NOTIN tn.t_mem) /\
  run_inst_seq (emitted_insts st en) s = OK raw ==>
  ?G' tn'.
    op_taint tn' out = {} /\
    ptr_covers G' tn' dst raw (32 + contractABI$ceil32 (LENGTH bs)) /\
    (!i. w2n q <= i /\ i < w2n q + 32 + contractABI$ceil32 (LENGTH bs) ==>
         i NOTIN tn'.t_mem) /\
    (!i. i < w2n q \/ w2n q + 32 + contractABI$ceil32 (LENGTH bs) <= i ==>
         (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
    (!x. not_fresh_at st x ==>
         FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    !D. inst_seq_ptr D lo ctx func PG G tn (emitted_insts st en) s G' tn'
Proof
  rpt strip_tac >>
  drule compile_abi_bytestring_code >> strip_tac >>
  qabbrev_tac `N = compiler_var_names st.cs_next_var 9` >>
  qabbrev_tac `ins = bytestring_encoder_insts st.cs_next_id N (Var dst) (Var src)` >>
  `LENGTH N = 9 /\ ALL_DISTINCT N` by
    simp[Abbr `N`, compiler_var_names_distinct] >>
  `!x. not_fresh_at st x ==> x NOTIN set N` by
    (simp[Abbr `N`, compiler_var_names_def, MEM_GENLIST, not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LE_ADD]) >>
  `src NOTIN set N /\ dst NOTIN set N` by metis_tac[] >>
  `ins = TAKE 4 ins ++ TAKE 3 (DROP 4 ins) ++ DROP 7 ins` by
    simp[Abbr `ins`, bytestring_encoder_insts_def] >>
  `run_inst_seq ins s = OK raw` by gvs[Abbr `ins`, Abbr `N`] >>
  `?a. run_inst_seq (TAKE 4 ins) s = OK a` by
    (spose_not_then assume_tac >>
     drule run_inst_seq_append_err >>
     disch_then (qspec_then `TAKE 3 (DROP 4 ins) ++ DROP 7 ins` mp_tac) >>
     metis_tac[APPEND_ASSOC]) >>
  `run_inst_seq (TAKE 3 (DROP 4 ins) ++ DROP 7 ins) a = OK raw` by
    (qpat_assum `run_inst_seq (TAKE 4 ins) s = OK a`
       (mp_then Any mp_tac run_inst_seq_append) >>
     disch_then (qspec_then `TAKE 3 (DROP 4 ins) ++ DROP 7 ins` mp_tac) >>
     metis_tac[APPEND_ASSOC]) >>
  `?b. run_inst_seq (TAKE 3 (DROP 4 ins)) a = OK b` by
    (spose_not_then assume_tac >> drule run_inst_seq_append_err >>
     disch_then (qspec_then `DROP 7 ins` mp_tac) >> metis_tac[]) >>
  `run_inst_seq (DROP 7 ins) b = OK raw` by metis_tac[run_inst_seq_append] >>
  `?H tm.
    (!D. inst_seq_ptr D lo ctx func PG G tn (TAKE 4 ins) s H tm) /\
    eval_operand (Var (EL 0 N)) a = SOME (n2w (LENGTH bs)) /\
    op_taint tm (Var (EL 0 N)) = {} /\
    eval_operand (Var (EL 3 N)) a = SOME (n2w (w2n q + contractABI$ceil32 (LENGTH bs))) /\
    ptr_covers H tm (EL 3 N) a 32 /\
    eval_operand (Var src) a = SOME p /\ eval_operand (Var dst) a = SOME q /\
    ptr_covers H tm src a (32+LENGTH bs) /\
    ptr_covers H tm dst a (32+contractABI$ceil32 (LENGTH bs)) /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    a.vs_allocas = s.vs_allocas /\ a.vs_alloca_next = s.vs_alloca_next /\
    (!x. x NOTIN set (TAKE 4 N) ==>
      lookup_var x a = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x))` by
    (unabbrev_all_tac >> irule bytes_encoder_prefix_ghosts >>
     goal_assum (drule_at Any) >> simp[]) >>
  `allocas_from lo a` by metis_tac[allocas_from_def] >>
  qunabbrev_tac `ins` >>
  `w2n p + 32 + LENGTH bs <= a.vs_alloca_next /\
   w2n q + 32 + contractABI$ceil32 (LENGTH bs) <= a.vs_alloca_next` by simp[] >>
  `!i. w2n p <= i /\ i < w2n p + 32 + LENGTH bs ==> i NOTIN tm.t_mem` by simp[] >>
  drule_all bytes_encoder_copy_ghosts >>
  disch_then (qspecl_then [`func`, `PG`] strip_assume_tac) >>
  rename1 `ptr_covers H2 tm2 dst b _` >>
  `allocas_from lo b` by metis_tac[allocas_from_def] >>
  `LENGTH bs + 32 < dimword (:256)` by decide_tac >>
  drule_all bytes_encoder_suffix_ghosts >>
  disch_then (qspecl_then [`func`, `PG`, `H2`] strip_assume_tac) >>
  rename1 `op_taint tm3 (Var (EL 8 N)) = {}` >>
  rename1 `!D k. inst_seq_ptr D lo ctx func PG H2 tm2 _ (b with vs_inst_idx := k) H3 tm3` >>
  `!x. x NOTIN set N ==>
    lookup_var x raw = lookup_var x s /\ FLOOKUP H3 x = FLOOKUP G x /\
    op_taint tm3 (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >>
     `x NOTIN set (TAKE 4 N) /\ x <> EL 4 N /\ x NOTIN set (DROP 5 N)` by
       (conj_tac >- metis_tac[TAKE_DROP, MEM_APPEND] >>
        conj_tac >- (strip_tac >> `4 < LENGTH N` by simp[] >> metis_tac[MEM_EL]) >>
        metis_tac[TAKE_DROP, MEM_APPEND]) >>
     metis_tac[]) >>
  qexistsl [`H3`, `tm3`] >>
  simp[] >>
  conj_tac >- (gvs[ptr_covers_def] >> metis_tac[]) >>
  conj_tac >- gvs[] >>
  `EVERY (\i. ~is_terminator i.inst_opcode)
    (TAKE 4 (bytestring_encoder_insts st.cs_next_id N (Var dst) (Var src)) ++
     TAKE 3 (DROP 4 (bytestring_encoder_insts st.cs_next_id N (Var dst) (Var src))))` by
    simp[bytestring_encoder_insts_def, mk_inst_def, is_terminator_def] >>
  `run_inst_seq
    (TAKE 4 (bytestring_encoder_insts st.cs_next_id N (Var dst) (Var src)) ++
     TAKE 3 (DROP 4 (bytestring_encoder_insts st.cs_next_id N (Var dst) (Var src)))) s = OK b` by
    metis_tac[run_inst_seq_append] >>
  gen_tac >>
  `inst_seq_ptr D lo ctx func PG G tn
    (TAKE 4 (bytestring_encoder_insts st.cs_next_id N (Var dst) (Var src)) ++
     TAKE 3 (DROP 4 (bytestring_encoder_insts st.cs_next_id N (Var dst) (Var src)))) s H2 tm2` by
    (irule inst_seq_ptr_append >> conj_tac >- metis_tac[EVERY_APPEND] >>
     qexistsl [`H`, `a`, `tm`] >> simp[]) >>
  metis_tac[inst_seq_ptr_append, APPEND_ASSOC]
QED

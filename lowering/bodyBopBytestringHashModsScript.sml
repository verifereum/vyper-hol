(* Read-only hash suffix after a reached linked bytestring child. *)
Theory bodyBopBytestringHashMods
Ancestors
  bodyForRangeScalarFrameMods bodyFullUnwrapRun bodyFullPostsMods
  bodyFullHashKeccakFixed bodyPtrBopHashSuffix bodyMemBopHeldHash
  bytestringHashProps abiEncodeOwnership bodyPtrBopHashSemantic
  bodyPtrBopHashFootprint bodyPtrBopHashCompile bodyPtrBopHashRun
  fragGasSeqPtr fragGasCopySeqLiftProps fragGasOriginPtr
  exprSimWordArgs loweringPosts bodyPtrDefs vyperStorageTrace venomState
  compileEnv venomInst words list finite_map pred_set
  bodyPtrIfExpBytesFrame ptrDiscipline exprSimConvertBytes
  exprSimHashBoundary exprLoweringProps exprLowering exprOperandVar exprSimProps
  bodyFullShadowBodyInv bodyPtrBopHashCoverage exprSimLiteralWord
  gasOutcomeFullPostMods gasOutcomeFullBindMods vyperValueOperation vyperTyping
  valueEncodingDefs loweringStateRelDefs freshWrites fragExec keccak vyperValue

Theorem bytestring_hash_no_dalloca[local]:
  EVERY (\i. i.inst_opcode <> DALLOCA) (pre ++ i::post) ==>
    unitTransformDefs$dalloca_no_wrap i u
Proof
  simp[EVERY_APPEND] >> strip_tac >>
  irule memSafeRunTheory.dalloca_no_wrap_non_dalloca >> simp[]
QED

Theorem bytestring_hash_run_mods[local]:
  compile_bytestring_hash (Var p) cb = (h,sz) /\ not_fresh_at cb p /\
  fn_has_code cb sz func /\ ~t.vs_halted /\
  t.vs_current_bb = cb.cs_current_bb /\ t.vs_inst_idx = LENGTH cb.cs_current_insts /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ allocas_from lo t /\
  lookup_var p t = SOME (n2w b) /\
  mem_word_at b t.vs_memory = n2w (LENGTH contents) /\
  mem_bytes_at (b + 32) (LENGTH contents) t.vs_memory = contents /\
  b + 32 < dimword(:256) /\ LENGTH contents < dimword(:256) /\
  b + 32 + LENGTH contents <= t.vs_alloca_next /\
  ptr_covers G tn p t 32 /\ FLOOKUP G p = SOME (root,len) /\
  (0 < LENGTH contents ==> root <= b + 32 /\
    b + 32 + LENGTH contents <= root + len) /\
  (!i. b <= i /\ i < b + 32 ==> i NOTIN tn.t_mem) /\
  (!i. b + 32 <= i /\ i < b + 32 + LENGTH contents ==> i NOTIN tn.t_mem) ==>
  ?raw G' tn'.
    run_inst_seq (emitted_insts cb sz) t = OK raw /\
    eval_operand h raw = SOME (word_of_bytes_be (Keccak_256_w64 contents)) /\
    (raw with vs_vars := t.vs_vars) = t /\
    (!x. not_fresh_at cb x ==> lookup_var x raw = lookup_var x t /\
         FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    op_prov G' h = NONE /\ op_taint tn' h = {} /\
    (!z. h = Var z ==> not_fresh_at sz z) /\ (!l. h <> Label l) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G,tn) []
       (OK (raw with vs_inst_idx := LENGTH sz.cs_current_insts),G',tn'))
Proof
  strip_tac >>
  `eval_operand (Var p) t = SOME (n2w b)` by simp[eval_operand_def] >>
  drule (Q.INST [`x` |-> `Var p`] compile_bytestring_hash_run_nofresh) >>
  disch_then (qspecl_then [`t`, `contents`, `b`] mp_tac) >>
  simp[] >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts cb sz) t` by
    (irule held_hash_mem_ok >> goal_assum (drule_at Any) >>
     qexistsl [`LENGTH contents`,`h`] >> simp[] >> decide_tac) >>
  drule_all bop_hash_compile_placement >> strip_tac >>
  drule bop_hash_compile_layout >> strip_tac >>
  drule compile_bytestring_hash_shape >> strip_tac >>
  drule_all bop_hash_compile_emission >> strip_tac >>
  `w2n (n2w b + 32w:bytes32) = b + 32` by simp[word_add_n2w] >>
  `mem_word_at (w2n (n2w b:bytes32)) t.vs_memory = n2w (LENGTH contents)` by simp[] >>
  `(0 < LENGTH contents ==> root <= w2n (n2w b + 32w:bytes32) /\
    w2n (n2w b + 32w:bytes32) + LENGTH contents <= root + len)` by simp[] >>
  `!i. w2n (n2w b:bytes32) <= i /\ i < w2n (n2w b:bytes32) + 32 ==>
       i NOTIN tn.t_mem` by simp[] >>
  `!i. w2n (n2w b + 32w:bytes32) <= i /\
       i < w2n (n2w b + 32w:bytes32) + LENGTH contents ==> i NOTIN tn.t_mem` by simp[] >>
  qpat_assum `emitted_insts cb sz = _` (fn th =>
    rule_assum_tac (PURE_REWRITE_RULE [th]) >> assume_tac th) >>
  drule_all (GEN_ALL (SIMP_RULE bool_ss [REFL_CLAUSE, AND_CLAUSES]
    (Q.INST [`h` |-> `h'`,
             `iA` |-> `mk_inst aId ADD [Var p; Lit 32w] [q]`,
             `iL` |-> `mk_inst lId MLOAD [Var p] [l]`,
             `iH` |-> `mk_inst hId SHA3 [Var q; Var l] [h']`]
      (SPEC_ALL bop_hash_run_checked)))) >>
  disch_then (fn th => assume_tac th >>
    qspecl_then [`func`, `PG`, `D0`] strip_assume_tac th) >>
  rename1 `inst_seq_ptr D0 0 ctx func PG G tn _ t Gf tnf` >>
  rename1 `run_inst_seq _ t = OK raw` >>
  `tnf.t_imm = tn.t_imm` by
    (qpat_assum `inst_seq_ptr D0 _ _ _ _ _ _ _ _ _ _`
       (mp_then Any mp_tac inst_seq_ptr_immutable_frame) >>
     simp[mk_inst_def]) >>
  qexistsl [`raw`, `Gf`, `tnf`] >> simp[] >>
  conj_tac >- simp[op_taint_def] >>
  gen_tac >>
  qpat_x_assum `!fn PG D. _` (qspecl_then [`func`, `PG`, `D`] strip_assume_tac) >>
  `G' = Gf /\ tn' = tnf` by metis_tac[inst_seq_ptr_ghost_unique] >>
  qpat_x_assum `G' = Gf` SUBST_ALL_TAC >>
  qpat_x_assum `tn' = tnf` SUBST_ALL_TAC >>
  `inst_seq_ptr D lo ctx func PG G tn (emitted_insts cb sz) t Gf tnf` by
    (irule inst_seq_ptr_lower_bound_transport >>
     conj_tac >- simp[mk_inst_def] >> simp[] >> qexists_tac `0` >> simp[]) >>
  `ctx_has_dalloca ctx ==> !pre i post u. emitted_insts cb sz = pre ++ i::post /\
     run_inst_seq pre t = OK u ==> unitTransformDefs$dalloca_no_wrap i u` by
    (rpt strip_tac >>
     rename1 `emitted_insts cb sz = pre ++ i::post` >>
     `EVERY (\j. j.inst_opcode <> DALLOCA) (pre ++ i::post)` by
       (qpat_assum `emitted_insts cb sz = pre ++ i::post`
          (fn th => pure_once_rewrite_tac[GSYM th]) >>
        qpat_assum `emitted_insts cb sz = [_;_;_]` (fn th =>
          pure_once_rewrite_tac[th]) >> simp[mk_inst_def]) >>
     irule memSafeRunTheory.dalloca_no_wrap_non_dalloca >> fs[EVERY_APPEND]) >>
  qpat_assum `inst_seq_ptr D lo _ _ _ _ _ _ _ _ _`
    (mp_then (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`) mp_tac
      run_inst_seq_gas_origin_ptr_path) >>
  disch_then (qspecl_then [`explicit`, `raw`] mp_tac) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts cb sz)` by simp[mk_inst_def, is_terminator_def] >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts cb sz) = []` by simp[mk_inst_def] >>
  `run_inst_seq (emitted_insts cb sz) t = OK raw` by simp[] >>
  `run_inst_seq_mem_ok (emitted_insts cb sz) t` by simp[] >>
  `isPREFIX (emitted_insts cb sz) (DROP t.vs_inst_idx bb.bb_instructions)` by
    (qpat_assum `emitted_insts cb sz = [_;_;_]` (fn th => pure_once_rewrite_tac[th]) >>
     first_assum ACCEPT_TAC) >>
  `t.vs_inst_idx + LENGTH (emitted_insts cb sz) = LENGTH sz.cs_current_insts` by simp[] >>
  disch_then (qspec_then `bb` mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]
QED


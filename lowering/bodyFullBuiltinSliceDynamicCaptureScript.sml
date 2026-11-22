(* Slice's read-only length/data capture, on a common full endpoint. *)
Theory bodyFullBuiltinSliceDynamicCapture
Ancestors
  bodyFullUnwrapRun bodyPtrSignedConvertSourceFixed
  exprSimSliceMemory exprSimSliceCaptureControl builtinBytesMemory
  instSeqPtrLo fragGasSeqPtr bodyPtrDefs exprSimSliceOrdinaryFrame
  venomState venomExecSemantics exprLoweringProps list
  wordArgsPtr bodyPtrBopOperandRetention bodyPtrPrecompileBuiltinsGhost
  stmtSimLogArgs loweringPosts exprSimWordArgs
  logTopicFramePtr stmtSimLogTopics abiEncodeOwnership exprSimHashBoundary
  exprSimConvertBytes bodyPtrBytestringBuiltinsCalldataReserved
  valueEncodingProofs valueEncodingDefs compileEnv vyperValue
  supportedTypes vyperTypeSystem vyperTyping ptrDiscipline
  bodyPtrBytestringBuiltinsWindowGhost loweringStateRelDefs
  bodyPtrBytestringBuiltinsAllocation

Theorem slice_dynamic_capture_full_run:
  compile_bytestring_src (Var src) sa = ((len,data),sb) /\
  fn_has_code sa sb func /\ not_fresh_at sa src /\
  lookup_var src s = SOME p /\ ptr_covers G tn src s capacity /\
  32 <= capacity /\ w2n p + 32 < dimword (:256) /\
  mload (w2n p) s = n2w (LENGTH bs) /\
  mem_bytes_at (w2n p + 32) (LENGTH bs) s.vs_memory = bs /\
  (!i. w2n p <= i /\ i < w2n p + 32 + LENGTH bs ==> i NOTIN tn.t_mem) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  w2n p + 32 <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u G' tn'.
    run_inst_seq (emitted_insts sa sb) s = OK u /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
       (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),G',tn')) /\
    eval_operand len u = SOME (n2w (LENGTH bs)) /\
    eval_operand data u = SOME (p+32w) /\
    op_taint tn' len = {} /\ op_prov G' len = NONE /\
    mem_bytes_at (w2n p + 32) (LENGTH bs) u.vs_memory = bs /\
    (!i. w2n p <= i /\ i < w2n p + 32 + LENGTH bs ==> i NOTIN tn'.t_mem) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    u = s with vs_vars := u.vs_vars /\
    (!x. not_fresh_at sa x ==>
       lookup_var x u = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!n. 32+n <= capacity ==>
       ?dp. data = Var dp /\ ptr_covers G' tn' dp u n) /\
    (?lp dp. len = Var lp /\ data = Var dp /\
       not_fresh_at sb lp /\ not_fresh_at sb dp)
Proof
  strip_tac >>
  `?u. run_inst_seq (emitted_insts sa sb) s = OK u /\
       eval_operand len u = SOME (mload (w2n p) s) /\
       eval_operand data u = SOME (p+32w) /\
       u = s with vs_vars := u.vs_vars /\
       (!x. not_fresh_at sa x ==> FLOOKUP u.vs_vars x = FLOOKUP s.vs_vars x)` by
    (irule slice_bytestring_src_run >> qexists_tac `Var src` >>
     simp[eval_operand_def]) >>
  `!i. w2n p <= i /\ i < w2n p + 32 ==> i NOTIN tn.t_mem` by
    (rpt strip_tac >> gvs[]) >>
  drule_all compile_bytestring_src_fixed_frame >>
  disch_then (qspecl_then [`ARB`,`func`,`PG`]
    (qx_choose_then `lp` (qx_choose_then `dp`
      (qx_choose_then `H` (qx_choose_then `th` strip_assume_tac))))) >>
  `emitted_insts sa sb =
     [mk_inst sa.cs_next_id MLOAD [Var src] [lp];
      mk_inst (sa.cs_next_id+1) ADD [Var src;Lit 32w] [dp]]` by
    (drule slice_bytestring_src_shape >> simp[]) >>
  `run_inst_seq
     [mk_inst sa.cs_next_id MLOAD [Var src] [lp];
      mk_inst (sa.cs_next_id+1) ADD [Var src;Lit 32w] [dp]] s = OK u` by
    metis_tac[] >>
  mp_tac (Q.SPECL [`ARB`,`ctx`,`func`,`PG`,`G`,`tn`,`s`,`src`,`lp`,`dp`,
    `sa.cs_next_id`,`sa.cs_next_id+1`,`p`,`capacity`,`u`]
    bytestring_source_uniform_checks) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `HG` (qx_choose_then `tm` strip_assume_tac)) >>
  `HG = H /\ tm = th` by
    (qpat_assum `!k. inst_seq_ptr ARB _ _ _ _ _ _ _ _ H th`
       (qspec_then `s.vs_inst_idx` mp_tac) >>
     qpat_assum `!k. inst_seq_ptr ARB _ _ _ _ _ _ _ _ HG tm`
       (qspec_then `s.vs_inst_idx` mp_tac) >>
     qpat_assum `emitted_insts sa sb = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[] >>
     metis_tac[inst_seq_ptr_ghost_unique]) >>
  qpat_assum `HG = H` SUBST_ALL_TAC >>
  qpat_assum `tm = th` SUBST_ALL_TAC >>
  `u = update_var dp (p+32w) (update_var lp (mload (w2n p) s) s)` by
    (irule bytestring_source_run_endpoint >>
     qexistsl_tac [`sa.cs_next_id`,`sa.cs_next_id+1`,`src`] >> simp[] >> fs[]) >>
  `ptr_covers
     (step_prov PG G (mk_inst sa.cs_next_id MLOAD [Var src] [lp])
       (update_var lp (mload (w2n p) s) s))
     (step_taint (mk_inst sa.cs_next_id MLOAD [Var src] [lp]) s
       (update_var lp (mload (w2n p) s) s) tn)
     src (update_var lp (mload (w2n p) s) s) capacity` by
    (irule wordLoadStorePtrTheory.mload_preserves_ptr_covers >> fs[]) >>
  `lookup_var src (update_var lp (mload (w2n p) s) s) = SOME p` by
    fs[lookup_var_def,update_var_def,finite_mapTheory.FLOOKUP_UPDATE] >>
  `!n. 32+n <= capacity ==> ptr_covers H th dp u n` by
    (gen_tac >> disch_tac >>
     qpat_assum `H = step_prov _ _ _ _` (fn eq => once_rewrite_tac[eq]) >>
     qpat_assum `th = step_taint _ _ _ _` (fn eq => once_rewrite_tac[eq]) >>
     qpat_assum `u = update_var dp _ _` (fn eq => rewrite_tac[eq]) >>
     qspecl_then [`PG`,
       `step_prov PG G (mk_inst sa.cs_next_id MLOAD [Var src] [lp])
          (update_var lp (mload (w2n p) s) s)`,
       `step_taint (mk_inst sa.cs_next_id MLOAD [Var src] [lp]) s
          (update_var lp (mload (w2n p) s) s) tn`,
       `update_var lp (mload (w2n p) s) s`,`sa.cs_next_id+1`,`src`,`dp`,
       `p`,`32`,`capacity`,`n`,`Lit 32w`]
       mp_tac pointer_offset_covers >>
     (impl_tac >- simp[eval_operand_def,op_taint_def]) >> simp[]) >>
  `!D. inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s H th` by
    (gen_tac >>
     drule_all compile_bytestring_src_fixed_frame >>
     disch_then (qspecl_then [`D`,`func`,`PG`] strip_assume_tac) >>
     qpat_x_assum `!k. inst_seq_ptr D _ _ _ _ _ _ _ _ _ _`
       (qspec_then `s.vs_inst_idx` mp_tac) >>
     qpat_assum `!k. inst_seq_ptr ARB _ _ _ _ _ _ (emitted_insts sa sb) _ H th`
       (qspec_then `s.vs_inst_idx` mp_tac) >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[] >>
     metis_tac[inst_seq_ptr_ghost_unique]) >>
  qpat_x_assum `H = step_prov _ _ _ _` kall_tac >>
  qpat_x_assum `th = step_taint _ _ _ _` kall_tac >>
  qpat_x_assum `u = update_var dp _ _` kall_tac >>
  qexistsl_tac [`u`,`H`,`th`] >> simp[] >>
  gen_tac >> irule emitted_origin_ptr_path >> simp[] >>
      qexistsl_tac [`emitted_insts sa sb`,`sa`] >> simp[] >>
      drule slice_bytestring_src_control >> strip_tac >>
      simp[venomInstTheory.is_terminator_def] >>
      conj_tac >-
        (rpt strip_tac >> irule memSafeRunTheory.dalloca_no_wrap_non_dalloca >>
         qpat_assum `[mk_inst _ MLOAD _ _; mk_inst _ ADD _ _] = _ ++ _`
           (mp_tac o Q.AP_TERM `\code. EVERY (\j. j.inst_opcode <> DALLOCA) code`) >>
         simp[EVERY_APPEND,venomInstTheory.mk_inst_def]) >>
      conj_tac >- (drule compile_bytestring_src_mem_ok >> simp[eval_operand_def]) >>
      irule inst_seq_ptr_zero_to_lo >> simp[] >> qexists_tac `D` >>
      qpat_assum `!D. inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s H th`
        (qspec_then `D` mp_tac) >>
      qpat_assum `emitted_insts sa sb = _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> simp[]
QED

(* Constructor bytestring assignment through a computed destination operand. *)
Theory immutableBytestringPath
Ancestors
  bodyFullImmutablePathStore immutableBytestringFootprint immutableAssignStore
  immutableDeployMeaningfulTransfer calldataTypedRobustPtr fragGasOriginPtrDead
  exprSimMemoryTransport exprSimProps valueTypingMemoryProps
  placeStoreStorage valueEncodingProps immutableDeployAssignTransfer
  vyperValue vyperContext vyperTypeSystem loweringPosts reasonCopySourcePtr
  bytestringCopyExecution immutableCopyExecution
  bodyFullUnwrapRun bodyPtrIfExpAssignFrame exprPtrCtorImmStore
  exprPtrCtorCodeLoad exprPtrUnwrapOffsetSegment exprPtrUnwrapScalarEdges
  exprPtrUnwrapScalarSegments fragGasCopyLoop fragGasCopySeqLiftProps fragGasOriginPtrLoop
  instSeqComposePtr logInstSeqPtr[qualified,ignore_grammar]
  abiEncoderWindowLookup[qualified,ignore_grammar] decoderSetupStepPtr
  bodyPtrDefs decoderGhostFramePtr ghostPcTransportPtr
  exprSimCopy representationCleanPtr typedCopyOriginPtrBase
  fragExecMem fragGasOriginPtr fragGasSeqAbort fragGasSeqPtr memSafeRun
  ptrSafeRun ptrDiscipline instIdxIndep instMemFrontier unitTransformDefs
  loweringStateRelDefs valueCopyBytes valueEncodingDefs vyperTyping
  context compileEnv emitHelper emitHelperProps exprLoweringProps fragExec
  codegenRel contextCodegenRel ssaOperandFrame venomExecSemantics venomInst venomState
  ASCIInumbers arithmetic finite_map list option pred_set rich_list words

val _ = Parse.hide "body";

Theorem body_assign_bytes_header_shr_check[local]:
  eval_operand value s = SOME w /\ op_taint tn value = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ptr_inst_ok D lo fuel ctx fn G tn (mk_inst id SHR [Lit 5w;value] [out]) s
Proof
  strip_tac >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def,
       op_taint_def] >>
  simp[GSYM mk_inst_def, step_inst_non_invoke] >>
  simp[mk_inst_def, step_inst_base_opcode_eqs, exec_pure2_def,
       eval_operand_def, update_var_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem body_assign_immutable_bytes_header_joint_fresh:
  compile_bytestring_word_count (Var src) sa = (cnt,sm) /\
  fn_has_code sa sm func /\ not_fresh_at sa src /\
  eval_operand (Var src) s = SOME a /\ mload (w2n a) s = n2w len /\
  len + 63 < dimword (:256) /\ ptr_covers G tn src s 32 /\
  w2n a + 32 <= s.vs_alloca_next /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?r Gf tnf out.
    cnt = Var out /\ not_fresh_at sm out /\ ~not_fresh_at sa out /\
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK r,Gf,tnf) /\
    eval_operand cnt r = SOME (n2w (1 + word_size len)) /\
    op_taint tnf cnt = {} /\ op_prov Gf cnt = NONE /\
    (r with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x r = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tnf (Var x) = op_taint tn (Var x)) /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!x C. not_fresh_at sa x /\ ptr_covers G tn x s C ==>
      ptr_covers Gf tnf x r C) /\
    ~r.vs_halted /\ r.vs_current_bb = sm.cs_current_bb /\
    r.vs_inst_idx = LENGTH sm.cs_current_insts /\
    (fresh_vars_wrt sa s ==> fresh_vars_wrt sm r)
Proof
  strip_tac >> drule_all bytestring_word_count_run >> strip_tac >>
  drule bytestring_word_count_shape >> strip_tac >>
  `?Gf tnf.
    inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sm) s Gf tnf /\
    op_taint tnf cnt = {} /\ op_prov Gf cnt = NONE /\
    (!x. not_fresh_at sa x ==> FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tnf (Var x) = op_taint tn (Var x)) /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm` by
    suspend "ghosts" >>
  `run_inst_seq_mem_ok (emitted_insts sa sm) s` by suspend "memory" >>
  suspend "join"
QED

Resume body_assign_immutable_bytes_header_joint_fresh[ghosts]:
  gvs[compile_bytestring_word_count_def, emit_op_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_id_def, fresh_var_def, emit_def] >>
  simp[emitted_insts_def, DROP_APPEND, SUB_PLUS] >>
  qpat_x_assum `fn_has_code _ _ _` kall_tac >>
  qpat_x_assum `run_inst_seq _ _ = _` kall_tac >>
  qpat_x_assum `same_blocks _ _` kall_tac >>
  qpat_x_assum `EVERY _ _` kall_tac >>
  qpat_x_assum `_ = emitted_insts _ _` kall_tac >>
  qabbrev_tac `v0 = STRING #"%" (toString sa.cs_next_var)` >>
  qabbrev_tac `v1 = STRING #"%" (toString (sa.cs_next_var + 1))` >>
  qabbrev_tac `v2 = STRING #"%" (toString (sa.cs_next_var + 2))` >>
  qmatch_goalsub_abbrev_tac `inst_seq_ptr _ _ _ _ _ _ _ [i0;i1;i2] _ _ _` >>
  qabbrev_tac `u0 = update_var v0 (n2w len) s` >>
  qabbrev_tac `q0 = u0 with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `G0 = step_prov PG G i0 u0` >>
  qabbrev_tac `tn0 = step_taint i0 s u0 tn` >>
  `step_inst_base i0 s = OK u0` by
    (qpat_assum `eval_operand (Var src) s = _`
       (mp_then Any mp_tac step_MLOAD) >> simp[Abbr `i0`, Abbr `u0`]) >>
  `ptr_inst_ok D lo 0 ctx func G tn i0 s` by
    (simp[Abbr `i0`] >> irule exprPtrCtorImmStoreTheory.ptr_inst_ok_mload_lo >> simp[]) >>
  `lookup_var src s = SOME a` by gvs[eval_operand_def] >>
  `op_taint tn0 (Var v0) = {} /\ op_prov G0 (Var v0) = NONE /\
   tn0.t_mem = tn.t_mem /\ tn0.t_stor = tn.t_stor /\
   tn0.t_trans = tn.t_trans /\ tn0.t_imm = tn.t_imm /\
   (!x. x <> v0 ==> FLOOKUP G0 x = FLOOKUP G x /\
     op_taint tn0 (Var x) = op_taint tn (Var x))` by
    (simp[Abbr `G0`, Abbr `tn0`, Abbr `i0`, Abbr `u0`] >>
     metis_tac[setup_mload_ghost]) >>
  qabbrev_tac `u1 = update_var v1 ((n2w len:bytes32) + 63w) q0` >>
  qabbrev_tac `q1 = u1 with vs_inst_idx := SUC q0.vs_inst_idx` >>
  qabbrev_tac `G1 = step_prov PG G0 i1 u1` >>
  qabbrev_tac `tn1 = step_taint i1 q0 u1 tn0` >>
  `eval_operand (Var v0) q0 = SOME (n2w len)` by
    simp[Abbr `q0`, Abbr `u0`, eval_operand_def, lookup_var_def,
         update_var_def, FLOOKUP_UPDATE] >>
  `step_inst_base i1 q0 = OK u1` by
    (simp[Abbr `i1`, Abbr `u1`] >> irule step_ADD >> simp[eval_operand_def]) >>
  `ptr_inst_ok D lo 0 ctx func G0 tn0 i1 q0` by
    (simp[Abbr `i1`] >> irule (cj 1 typed_copy_origin_ptr_binop_checks) >>
     conj_tac >- (qexists_tac `(n2w len:bytes32) + 63w` >> gvs[Abbr `u1`]) >>
     gvs[Abbr `q0`, Abbr `u0`, update_var_def, op_taint_def,
       allocas_from_def, allocas_below_fmp_def] >> metis_tac[]) >>
  `op_taint tn1 (Var v1) = {} /\ op_prov G1 (Var v1) = NONE /\
   tn1.t_mem = tn0.t_mem /\ tn1.t_stor = tn0.t_stor /\
   tn1.t_trans = tn0.t_trans /\ tn1.t_imm = tn0.t_imm /\
   (!x. x <> v1 ==> FLOOKUP G1 x = FLOOKUP G0 x /\
     op_taint tn1 (Var x) = op_taint tn0 (Var x))` by
    (simp[Abbr `G1`, Abbr `tn1`, Abbr `i1`, Abbr `u1`,
       step_prov_def, step_taint_def, out_prov_def, first_prov_def,
       set_prov_def, mk_inst_def, op_prov_def, set_var_taint_def,
       out_taint_def, op_taint_def, mem_taint_def, new_site_bytes_def,
       step_writes_def, written_taint_def, store_taint_def, imm_taint_def,
       adopt_reset_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE,
       source_memory_write_ranges_def, range_bytes_def, update_var_def,
       lookup_var_def, SF CONJ_ss] >>
     gvs[op_taint_def, op_prov_def, eval_operand_def, lookup_var_def,
         EXTENSION, FLOOKUP_DEF] >> metis_tac[]) >>
  qabbrev_tac `u2 = update_var v2 ((n2w len + 63w:bytes32) >>> 5) q1` >>
  qabbrev_tac `G2 = step_prov PG G1 i2 u2` >>
  qabbrev_tac `tn2 = step_taint i2 q1 u2 tn1` >>
  `eval_operand (Var v1) q1 = SOME ((n2w len:bytes32) + 63w)` by
    simp[Abbr `q1`, Abbr `u1`, eval_operand_def, lookup_var_def,
         update_var_def, FLOOKUP_UPDATE] >>
  `step_inst_base i2 q1 = OK u2` by
    simp[Abbr `i2`, Abbr `u2`, mk_inst_def, step_inst_base_opcode_eqs,
         exec_pure2_def, eval_operand_def] >>
  `ptr_inst_ok D lo 0 ctx func G1 tn1 i2 q1` by
    (simp[Abbr `i2`] >> irule body_assign_bytes_header_shr_check >>
     simp[] >> gvs[Abbr `q1`, Abbr `u1`, Abbr `q0`, Abbr `u0`,
       update_var_def, allocas_from_def, allocas_below_fmp_def] >> metis_tac[]) >>
  `op_taint tn2 (Var v2) = {} /\ op_prov G2 (Var v2) = NONE /\
   tn2.t_mem = tn1.t_mem /\ tn2.t_stor = tn1.t_stor /\
   tn2.t_trans = tn1.t_trans /\ tn2.t_imm = tn1.t_imm /\
   (!x. x <> v2 ==> FLOOKUP G2 x = FLOOKUP G1 x /\
     op_taint tn2 (Var x) = op_taint tn1 (Var x))` by
    (simp[Abbr `G2`, Abbr `tn2`, Abbr `i2`, Abbr `u2`,
       step_prov_def, step_taint_def, out_prov_def, first_prov_def,
       set_prov_def, mk_inst_def, op_prov_def, set_var_taint_def,
       out_taint_def, op_taint_def, mem_taint_def, new_site_bytes_def,
       step_writes_def, written_taint_def, store_taint_def, imm_taint_def,
       adopt_reset_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE,
       source_memory_write_ranges_def, range_bytes_def, update_var_def,
       lookup_var_def, SF CONJ_ss] >>
     gvs[op_taint_def, op_prov_def, eval_operand_def, lookup_var_def,
         shift_taint_def, EXTENSION, FLOOKUP_DEF] >> metis_tac[]) >>
  qexistsl_tac [`G2`,`tn2`] >>
  conj_tac >-
    (gvs[Abbr `q0`, Abbr `q1`, Abbr `G0`, Abbr `tn0`,
         Abbr `G1`, Abbr `tn1`, Abbr `G2`, Abbr `tn2`] >>
     simp[inst_seq_ptr_def]) >>
  simp[] >> rpt strip_tac >>
  `x <> v0 /\ x <> v1 /\ x <> v2` by
    (gvs[not_fresh_at_def, Abbr `v0`, Abbr `v1`, Abbr `v2`] >> metis_tac[LESS_EQ_REFL, DECIDE ``n <= n + 1 /\ n <= n + 2``]) >>
  metis_tac[]
QED

Resume body_assign_immutable_bytes_header_joint_fresh[memory]:
  gvs[compile_bytestring_word_count_def, emit_op_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_id_def, fresh_var_def, emit_def] >>
  simp[emitted_insts_def, DROP_APPEND, SUB_PLUS,
       run_inst_seq_mem_ok_def, inst_mem_below_frontier_def,
       inst_dload_in_section_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def, mk_inst_def] >>
  gvs[eval_operand_def, lookup_var_def] >>
  rpt CASE_TAC >> simp[]
QED

Resume body_assign_immutable_bytes_header_joint_fresh[join]:
  `EVERY (\i. i.inst_opcode <> DALLOCA) (emitted_insts sa sm)` by
    (gvs[compile_bytestring_word_count_def, emit_op_def,
         comp_bind_def, comp_ignore_bind_def, comp_return_def,
         fresh_id_def, fresh_var_def, emit_def] >>
     simp[emitted_insts_def, DROP_APPEND, SUB_PLUS, mk_inst_def]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (t with vs_inst_idx := LENGTH sm.cs_current_insts),Gf,tnf)` by
    (irule bodyFullUnwrapRunTheory.emitted_origin_ptr_path >>
     conj_tac >-
       (strip_tac >> rpt gen_tac >> strip_tac >>
        irule dalloca_no_wrap_non_dalloca >>
        qpat_x_assum `EVERY (\i. i.inst_opcode <> DALLOCA) _` mp_tac >>
        simp[EVERY_MEM]) >>
     qexistsl_tac [`emitted_insts sa sm`,`sa`] >>
     gvs[same_blocks_def, EVERY_MEM]) >>
  `fresh_vars_wrt sa s ==>
   fresh_vars_wrt sm (t with vs_inst_idx := LENGTH sm.cs_current_insts)` by
    (strip_tac >>
     `fresh_vars_wrt sm s` by (irule fresh_vars_wrt_mono >> qexists_tac `sa` >> simp[]) >>
     `EVERY (\i. i.inst_opcode <> INVOKE /\
                 EVERY (not_fresh_at sm) i.inst_outputs) (emitted_insts sa sm)` by
       (gvs[compile_bytestring_word_count_def, emit_op_def,
            comp_bind_def, comp_ignore_bind_def, comp_return_def,
            fresh_id_def, fresh_var_def, emit_def] >>
        simp[emitted_insts_def, DROP_APPEND, SUB_PLUS, mk_inst_def,
             not_fresh_at_def, ASCIInumbersTheory.toString_11]) >>
     irule abiEncoderWindowLookupTheory.abi_window_seq_fresh_idx >>
     goal_assum (drule_at Any) >> qexists_tac `s` >> simp[]) >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH sm.cs_current_insts`,`Gf`,`tnf`] >>
  simp[eval_operand_def, lookup_var_def] >>
  `?out. cnt = Var out /\ not_fresh_at sm out /\ ~not_fresh_at sa out` by
    (gvs[compile_bytestring_word_count_def, emit_op_def,
         comp_bind_def, comp_ignore_bind_def, comp_return_def,
         fresh_id_def, fresh_var_def, emit_def] >>
     simp[not_fresh_at_def, ASCIInumbersTheory.toString_11]) >>
  qexists_tac `out` >> simp[] >>
  conj_tac >-
    (qpat_x_assum `t with vs_vars := _ = s` mp_tac >>
     gvs[venom_state_component_equality]) >>
  conj_tac >- gvs[lookup_var_def] >>
  conj_tac >-
    (rpt strip_tac >> gvs[ptr_covers_def] >> metis_tac[]) >>
  gvs[venom_state_component_equality, same_blocks_def]
QED

Finalise body_assign_immutable_bytes_header_joint_fresh

Theorem body_assign_immutable_bytes_source_live_clean:
  evaluate_type tenv sty = SOME stv /\ is_bytestring_type sty /\
  value_has_type stv v /\
  (!mem. mem_agree_outside M s.vs_memory mem ==>
         val_in_memory stv v a mem) ==>
  ?len.
    ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
     (?str. v = StringV str /\ len = LENGTH str)) /\
    mload a s = n2w len /\
    (!i. a <= i /\ i < a + 32 + len ==> i NOTIN M)
Proof
  strip_tac >>
  `val_in_memory stv v a s.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  drule_all bytestring_type_value >> strip_tac >>
  Cases_on `v` >> gvs[value_has_type_def]
  >- (drule robust_val_in_memory_bytes_clean >> simp[] >> strip_tac >>
      conj_tac
      >- gvs[val_in_memory_def, mload_def, mem_word_at_def] >>
      rpt strip_tac >> Cases_on `i < a + 32` >> gvs[])
  >> drule robust_val_in_memory_string_clean >> strip_tac >>
  conj_tac
  >- gvs[val_in_memory_def, mload_def, mem_word_at_def] >>
  rpt strip_tac >> Cases_on `i < a + 32` >> gvs[]
QED

val _ = Parse.hide "count";

Theorem body_assign_immutable_bytes_loop_header_actual[local]:
  !sm src dst count imm a b n lo ctx cv s0 G0 tn0 D explicit func PG
   hdr loop_body exit ie ih ib test sx sp value dx dp ip nc bbE bbH bbB.
  copy_old_operand sm src /\ copy_old_operand sm dst /\
  copy_old_operand sm count /\
  (case imm of NONE => T | SOME region => copy_old_operand sm region) /\
  eval_operand src s0 = SOME a /\ op_taint tn0 src = {} /\
  (0 < n ==> ?p. src = Var p /\ ptr_covers G0 tn0 p s0 (32*n)) /\
  eval_operand dst s0 = SOME b /\ op_taint tn0 dst = {} /\ op_prov G0 dst = NONE /\
  eval_operand count s0 = SOME (n2w n) /\
  op_taint tn0 count = {} /\ op_prov G0 count = NONE /\
  (case imm of NONE => T | SOME region =>
    eval_operand region s0 = SOME (0w:bytes32) /\
    op_taint tn0 region = {} /\ op_prov G0 region = NONE) /\
  n < dimword(:256) /\ lo <= w2n a /\
  w2n a + 32*n < dimword(:256) /\ w2n b + 32*n <= lo /\
  allocas_from lo s0 /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  ALL_DISTINCT [hdr;loop_body;exit] /\
  ALL_DISTINCT ([cv;test;sx;sp;value;dx;dp;nc] ++
    (case imm of NONE => [] | SOME region => [ip])) /\
  (!x. MEM x ([cv;test;sx;sp;value;dx;dp;nc] ++
    (case imm of NONE => [] | SOME region => [ip])) ==> ~not_fresh_at sm x) /\
  lookup_block sm.cs_current_bb func.fn_blocks = SOME bbE /\
  isPREFIX [mk_inst ie ASSIGN [Lit 0w] [cv]; mk_inst (ie+1) JMP [Label hdr] []]
    (DROP (LENGTH sm.cs_current_insts) bbE.bb_instructions) /\
  lookup_block hdr func.fn_blocks = SOME bbH /\
  isPREFIX [mk_inst ih EQ [Var cv;count] [test];
    mk_inst (ih+1) JNZ [Var test;Label exit;Label loop_body] []] bbH.bb_instructions /\
  lookup_block loop_body func.fn_blocks = SOME bbB /\
  isPREFIX ([mk_inst ib MUL [Var cv;Lit 32w] [sx];
    mk_inst (ib+1) ADD [src;Var sx] [sp];
    mk_inst (ib+2) MLOAD [Var sp] [value];
    mk_inst (ib+3) MUL [Var cv;Lit 32w] [dx];
    mk_inst (ib+4) ADD [dst;Var dx] [dp]] ++
    (case imm of NONE =>
      [mk_inst (ib+5) ISTORE [Var dp;Var value] [];
       mk_inst (ib+6) ADD [Var cv;Lit 1w] [nc];
       mk_inst (ib+7) ASSIGN [Var nc] [cv]; mk_inst (ib+8) JMP [Label hdr] []]
     | SOME region =>
      [mk_inst (ib+5) ADD [region;Var dp] [ip];
       mk_inst (ib+6) ISTORE [Var ip;Var value] [];
       mk_inst (ib+7) ADD [Var cv;Lit 1w] [nc];
       mk_inst (ib+8) ASSIGN [Var nc] [cv]; mk_inst (ib+9) JMP [Label hdr] []]))
    bbB.bb_instructions ==>
  !j G tn q. j <= n /\
    (q with <|vs_vars := s0.vs_vars; vs_current_bb := s0.vs_current_bb;
       vs_prev_bb := s0.vs_prev_bb; vs_inst_idx := s0.vs_inst_idx|>) =
      immutable_transfers T T a b j 0 s0 /\
    lookup_var cv q = SOME (n2w j) /\
    FLOOKUP G cv = NONE /\ op_taint tn (Var cv) = {} /\
    (!x. not_fresh_at sm x ==>
      lookup_var x q = lookup_var x s0 /\ FLOOKUP G x = FLOOKUP G0 x /\
      op_taint tn (Var x) = op_taint tn0 (Var x)) /\
    eval_operand src q = SOME a /\ op_taint tn src = {} /\
    (0 < n ==> ?p. src = Var p /\ ptr_covers G tn p q (32*n)) /\
    eval_operand dst q = SOME b /\ op_taint tn dst = {} /\ op_prov G dst = NONE /\
    eval_operand count q = SOME (n2w n) /\
    op_taint tn count = {} /\ op_prov G count = NONE /\
    (case imm of NONE => T | SOME region =>
      eval_operand region q = SOME (0w:bytes32) /\
      op_taint tn region = {} /\ op_prov G region = NONE) /\
    q.vs_allocas = s0.vs_allocas /\ q.vs_alloca_next = s0.vs_alloca_next /\
    q.vs_fmp = s0.vs_fmp /\ q.vs_initial_fmp = s0.vs_initial_fmp /\
    allocas_from lo q /\ (ctx_has_dalloca ctx ==> allocas_below_fmp q) /\
    (!k. k < 32*j ==> (w2n b+k IN tn.t_mem <=> w2n a+k IN tn0.t_mem)) /\
    (!i. ~(w2n b <= i /\ i < w2n b+32*j) ==> (i IN tn.t_mem <=> i IN tn0.t_mem)) /\
    tn.t_stor = tn0.t_stor /\ tn.t_trans = tn0.t_trans /\
    ~q.vs_halted /\ q.vs_current_bb = hdr /\ q.vs_inst_idx = 0 ==>
  ?r G1 tn1.
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (q,G,tn) [] (OK r,G1,tn1) /\
    j <= n /\
    (r with <|vs_vars := s0.vs_vars; vs_current_bb := s0.vs_current_bb;
       vs_prev_bb := s0.vs_prev_bb; vs_inst_idx := s0.vs_inst_idx|>) =
      immutable_transfers T T a b j 0 s0 /\
    lookup_var cv r = SOME (n2w j) /\
    FLOOKUP G1 cv = NONE /\ op_taint tn1 (Var cv) = {} /\
    (!x. not_fresh_at sm x ==>
      lookup_var x r = lookup_var x s0 /\ FLOOKUP G1 x = FLOOKUP G0 x /\
      op_taint tn1 (Var x) = op_taint tn0 (Var x)) /\
    eval_operand src r = SOME a /\ op_taint tn1 src = {} /\
    (0 < n ==> ?p. src = Var p /\ ptr_covers G1 tn1 p r (32*n)) /\
    eval_operand dst r = SOME b /\ op_taint tn1 dst = {} /\ op_prov G1 dst = NONE /\
    eval_operand count r = SOME (n2w n) /\
    op_taint tn1 count = {} /\ op_prov G1 count = NONE /\
    (case imm of NONE => T | SOME region =>
      eval_operand region r = SOME (0w:bytes32) /\
      op_taint tn1 region = {} /\ op_prov G1 region = NONE) /\
    r.vs_allocas = s0.vs_allocas /\ r.vs_alloca_next = s0.vs_alloca_next /\
    r.vs_fmp = s0.vs_fmp /\ r.vs_initial_fmp = s0.vs_initial_fmp /\
    allocas_from lo r /\ (ctx_has_dalloca ctx ==> allocas_below_fmp r) /\
    (!k. k < 32*j ==> (w2n b+k IN tn1.t_mem <=> w2n a+k IN tn0.t_mem)) /\
    (!i. ~(w2n b <= i /\ i < w2n b+32*j) ==> (i IN tn1.t_mem <=> i IN tn0.t_mem)) /\
    tn1.t_stor = tn0.t_stor /\ tn1.t_trans = tn0.t_trans /\
    ~r.vs_halted /\ r.vs_inst_idx = 0 /\
    r.vs_current_bb = (if j=n then exit else loop_body)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `j < dimword(:256)` by decide_tac >>
  `((n2w j):bytes32 = n2w n) <=> (j = n)` by simp[n2w_11, LESS_MOD] >>
  `eval_operand (Var cv) q = SOME (n2w j)` by simp[eval_operand_def] >>
  qabbrev_tac `i0 = mk_inst ih EQ [Var cv;count] [test]` >>
  qabbrev_tac `u0 = update_var test (bool_to_word (j=n)) q` >>
  `step_inst_base i0 q = OK u0` by
    (simp[Abbr `i0`, Abbr `u0`] >>
     qpat_assum `(n2w j = n2w n) <=> (j = n)`
       (fn th => once_rewrite_tac [GSYM th]) >> irule step_EQ >> simp[]) >>
  `ptr_inst_ok D 0 0 ctx func G tn i0 q` by
    (simp[Abbr `i0`, ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
          mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke, Abbr `u0`, update_var_def] >>
     conj_tac >- (rpt strip_tac >> gvs[op_prov_def, flookup_thm]) >>
     rpt strip_tac >> Cases_on `op = Var cv` >> Cases_on `op = count` >> gvs[]) >>
  `run_inst_seq_mem_ok [i0] q` by
    (simp[Abbr `i0`, run_inst_seq_mem_ok_last, inst_dload_in_section_def, mk_inst_def] >>
     irule below_frontier_no_ranges >> simp[]) >>
  `isPREFIX [i0] (DROP q.vs_inst_idx bbH.bb_instructions)` by
    (qpat_assum `isPREFIX [i0; _] _`
       (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >> simp[]) >>
  qabbrev_tac `G1 = step_prov PG G i0 u0` >>
  qabbrev_tac `tn1 = step_taint i0 q u0 tn` >>
  `inst_seq_ptr D 0 ctx func PG G tn [i0] q G1 tn1` by
    simp[inst_seq_ptr_def, Abbr `G1`, Abbr `tn1`] >>
  `run_inst_seq [i0] q = OK u0` by simp[run_inst_seq_def] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
      i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) [i0]` by
    simp[Abbr `i0`, mk_inst_def, is_terminator_def] >>
  `lookup_block q.vs_current_bb func.fn_blocks = SOME bbH` by simp[] >>
  `(ptrDiscipline$ctx_has_dalloca ctx ==>
    !pre i post u. [i0] = pre ++ i::post /\ run_inst_seq pre q = OK u ==>
      unitTransformDefs$dalloca_no_wrap i u)` by
    (rpt strip_tac >>
     `MEM i [i0]` by
       (qpat_assum `[i0] = _` (fn th => pure_once_rewrite_tac [th]) >> simp[]) >>
     gvs[Abbr `i0`, mk_inst_def]) >>
  drule_all_then (qspec_then `explicit` strip_assume_tac) run_inst_seq_origin_ptr_lift >>
  qabbrev_tac `t0 = u0 with vs_inst_idx := q.vs_inst_idx + LENGTH [i0]` >>
  qabbrev_tac `lbl = if j=n then exit else loop_body` >>
  `G1 = DRESTRICT G (COMPL {test}) /\ tn1 = tn with t_var := tn.t_var |+ (test,{})` by
    simp[Abbr `G1`, Abbr `tn1`, Abbr `i0`, Abbr `u0`,
      step_prov_def, set_prov_def, out_prov_def, first_prov_def, op_prov_def,
      step_taint_def, mem_taint_def, new_site_bytes_def, step_writes_def,
      written_taint_def, out_taint_def, op_taint_def, set_var_taint_def,
      adopt_reset_def, store_taint_def, imm_taint_def, mk_inst_def,
      source_memory_write_ranges_def, eval_operand_def, update_var_def,
      range_bytes_def, flookup_thm, SF CONJ_ss, taint_component_equality, EXTENSION] >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t0,G1,tn1) []
     (OK (jump_to lbl t0),G1,tn1)` by suspend "jump" >>
  qexistsl_tac [`jump_to lbl t0`, `G1`, `tn1`] >>
  conj_tac >- metis_tac[gas_origin_ptr_path_append, APPEND_NIL] >>
  suspend "frame"
QED

Resume body_assign_immutable_bytes_loop_header_actual[jump]:
  `isPREFIX [i0; mk_inst (ih+1) JNZ [Var test;Label exit;Label loop_body] []]
      (DROP 0 bbH.bb_instructions)` by (rewrite_tac[DROP_0] >> first_assum ACCEPT_TAC) >>
  `get_instruction bbH t0.vs_inst_idx =
     SOME (mk_inst (ih+1) JNZ [Var test;Label exit;Label loop_body] [])` by
    ((qpat_x_assum `isPREFIX [i0; _] (DROP 0 _)`
       (mp_then Any strip_assume_tac instruction_prefix_cursor) >>
     qpat_assum `isPREFIX [mk_inst _ JNZ _ _] (DROP _ _)`
       (mp_then Any strip_assume_tac instruction_prefix_cursor) >>
     simp[Abbr `t0`] >> (gvs[]))) >>
  `lookup_var test t0 = SOME (bool_to_word (j=n))` by
    simp[Abbr `t0`, Abbr `u0`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  `step_inst_base (mk_inst (ih+1) JNZ [Var test;Label exit;Label loop_body] []) t0 =
     OK (jump_to lbl t0)` by
    (Cases_on `j=n` >>
     simp[Abbr `lbl`, step_inst_base_opcode_eqs, mk_inst_def,
          eval_operand_def, bool_to_word_def]) >>
  `ptr_inst_ok D 0 0 ctx func G1 tn1
    (mk_inst (ih+1) JNZ [Var test;Label exit;Label loop_body] []) t0` by
    (simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
          mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def] >>
     pure_rewrite_tac[GSYM mk_inst_def] >>
     `step_inst 0 ctx (mk_inst (ih+1) JNZ [Var test;Label exit;Label loop_body] []) t0 =
        OK (jump_to lbl t0)` by simp[step_inst_non_invoke, mk_inst_def, GSYM mk_inst_def] >>
     simp[jump_to_def, op_taint_def, FLOOKUP_UPDATE] >>
     conj_tac >-
       (gen_tac >> Cases_on `op = Var test` >> Cases_on `op = Label exit` >>
        Cases_on `op = Label loop_body` >> simp[]) >>
     simp[Abbr `t0`, Abbr `u0`, update_var_def, allocas_below_fmp_def]) >>
  irule copy_jump_origin_ptr >>
  reverse (rpt (conj_tac >- simp[Abbr `t0`, Abbr `u0`, update_var_def, allocas_from_def])) >>
  qexistsl_tac [`bbH`, `mk_inst (ih+1) JNZ [Var test;Label exit;Label loop_body] []`] >>
  simp[] >> simp[Abbr `t0`, Abbr `u0`, update_var_def, mk_inst_def, allocas_from_def]
QED

Resume body_assign_immutable_bytes_loop_header_actual[frame]:
  `cv <> test` by ((qpat_assum `ALL_DISTINCT ((cv::test::_) ++ _)` mp_tac >> simp[] >> (gvs[]))) >>
  `!x. not_fresh_at sm x ==> x <> test` by
    (qpat_assum `!x. MEM x (_ ++ _) ==> _` (qspec_then `test` mp_tac) >> simp[]) >>
  `!x. x <> test ==>
    lookup_var x (jump_to lbl t0) = lookup_var x q /\
    FLOOKUP G1 x = FLOOKUP G x /\ op_taint tn1 (Var x) = op_taint tn (Var x)` by
    simp[Abbr `t0`, Abbr `u0`, jump_to_def, update_var_def, lookup_var_def,
         FLOOKUP_DRESTRICT, FLOOKUP_UPDATE, op_taint_def] >>
  `!op. copy_old_operand sm op ==>
    eval_operand op (jump_to lbl t0) = eval_operand op q /\
    op_taint tn1 op = op_taint tn op /\ op_prov G1 op = op_prov G op` by
    (gen_tac >> Cases_on `op` >>
     simp[copy_old_operand_def, eval_operand_def, op_taint_def, op_prov_def]
     >~ [`FLOOKUP (jump_to lbl t0).vs_labels _ = _`]
     >- simp[Abbr `t0`, Abbr `u0`, jump_to_def, update_var_def] >>
     rename1 `not_fresh_at sm x ==> _` >> strip_tac >>
     `x <> test` by simp[] >>
     qpat_assum `!x. x <> test ==> lookup_var x _ = _ /\ _ /\ _`
       (qspec_then `x` mp_tac) >> simp[op_taint_def]) >>
  `(0 < n ==> ?p. src = Var p /\ ptr_covers G1 tn1 p (jump_to lbl t0) (32*n))` by
    (strip_tac >> qpat_assum `0 < n ==> ?p. src = Var p /\ ptr_covers G tn p q _`
       drule >> strip_tac >>
     `p <> test` by metis_tac[copy_old_operand_def] >>
     qexists_tac `p` >> simp[] >> irule ptr_covers_frame >>
     qexistsl_tac [`G`, `q`, `tn`] >>
     simp[op_taint_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]) >>
  `(case imm of NONE => T | SOME region =>
    eval_operand region (jump_to lbl t0) = SOME (0w:bytes32) /\
    op_taint tn1 region = {} /\ op_prov G1 region = NONE)` by
    (Cases_on `imm` >> gvs[] >> metis_tac[]) >>
  `(jump_to lbl t0 with <|vs_vars := s0.vs_vars; vs_current_bb := s0.vs_current_bb;
       vs_prev_bb := s0.vs_prev_bb; vs_inst_idx := s0.vs_inst_idx|>) =
    (q with <|vs_vars := s0.vs_vars; vs_current_bb := s0.vs_current_bb;
       vs_prev_bb := s0.vs_prev_bb; vs_inst_idx := s0.vs_inst_idx|>)` by
    simp[Abbr `t0`, Abbr `u0`, jump_to_def, update_var_def,
         venom_state_component_equality] >>
  simp[] >>
  simp[Abbr `t0`, Abbr `u0`, jump_to_def, update_var_def,
       allocas_from_def, allocas_below_fmp_def] >>
  gvs[allocas_from_def, allocas_below_fmp_def] >> metis_tac[]
QED

Finalise body_assign_immutable_bytes_loop_header_actual[local]

Theorem body_assign_immutable_bytes_loop_shape[local]:
  compile_word_copy_loop_base src dst count LocMemory LocCode T imm sm = (u,sb) /\
  fn_has_code sm sb func ==>
  ?hdr loop_body exit ie ih ib cv test sx sp value dx dp ip nc bbE bbH bbB.
    ALL_DISTINCT [hdr;loop_body;exit] /\
    ALL_DISTINCT ([cv;test;sx;sp;value;dx;dp;nc] ++
      (case imm of NONE => [] | SOME region => [ip])) /\
    (!x. MEM x ([cv;test;sx;sp;value;dx;dp;nc] ++
      (case imm of NONE => [] | SOME region => [ip])) ==> ~not_fresh_at sm x) /\
    lookup_block sm.cs_current_bb func.fn_blocks = SOME bbE /\
    isPREFIX [mk_inst ie ASSIGN [Lit 0w] [cv];
      mk_inst (ie+1) JMP [Label hdr] []]
      (DROP (LENGTH sm.cs_current_insts) bbE.bb_instructions) /\
    lookup_block hdr func.fn_blocks = SOME bbH /\
    isPREFIX [mk_inst ih EQ [Var cv;count] [test];
      mk_inst (ih+1) JNZ [Var test;Label exit;Label loop_body] []]
      bbH.bb_instructions /\
    lookup_block loop_body func.fn_blocks = SOME bbB /\
    isPREFIX ([mk_inst ib MUL [Var cv;Lit 32w] [sx];
      mk_inst (ib+1) ADD [src;Var sx] [sp];
      mk_inst (ib+2) MLOAD [Var sp] [value];
      mk_inst (ib+3) MUL [Var cv;Lit 32w] [dx];
      mk_inst (ib+4) ADD [dst;Var dx] [dp]] ++
      (case imm of NONE =>
        [mk_inst (ib+5) ISTORE [Var dp;Var value] [];
         mk_inst (ib+6) ADD [Var cv;Lit 1w] [nc];
         mk_inst (ib+7) ASSIGN [Var nc] [cv];
         mk_inst (ib+8) JMP [Label hdr] []]
       | SOME region =>
        [mk_inst (ib+5) ADD [region;Var dp] [ip];
         mk_inst (ib+6) ISTORE [Var ip;Var value] [];
         mk_inst (ib+7) ADD [Var cv;Lit 1w] [nc];
         mk_inst (ib+8) ASSIGN [Var nc] [cv];
         mk_inst (ib+9) JMP [Label hdr] []])) bbB.bb_instructions /\
    sb.cs_current_bb = exit /\ sb.cs_current_insts = [] /\
    ie = sm.cs_next_id /\ ih = ie+2 /\ ib = ie+4 /\
    cv = STRING #"%" (toString sm.cs_next_var) /\
    test = STRING #"%" (toString (sm.cs_next_var+1)) /\
    sx = STRING #"%" (toString (sm.cs_next_var+2)) /\
    sp = STRING #"%" (toString (sm.cs_next_var+3)) /\
    value = STRING #"%" (toString (sm.cs_next_var+4)) /\
    dx = STRING #"%" (toString (sm.cs_next_var+5)) /\
    dp = STRING #"%" (toString (sm.cs_next_var+6)) /\
    (case imm of NONE => nc = STRING #"%" (toString (sm.cs_next_var+7)) /\
                         sb.cs_next_var = sm.cs_next_var+8
     | SOME region => ip = STRING #"%" (toString (sm.cs_next_var+7)) /\
                      nc = STRING #"%" (toString (sm.cs_next_var+8)) /\
                      sb.cs_next_var = sm.cs_next_var+9)
Proof
  Cases_on `imm` >> strip_tac >>
  qpat_x_assum `compile_word_copy_loop_base _ _ _ _ _ _ _ _ = _` mp_tac
  >>> SPLIT_LT 1 (ALLGOALS (simp[compile_word_copy_loop_base_def, word_scale_def,
       compile_ptr_load_def, compile_ptr_store_def, compile_imm_store_word_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_label_def, fresh_var_def, emit_inst_def, emit_op_def,
       emit_void_def, fresh_id_def, emit_def, new_block_def, Excl "isPREFIX"]), ALL_LT)
  >>> SPLIT_LT 1 (ALL_LT, ALLGOALS (simp[compile_word_copy_loop_base_def, word_scale_def,
       compile_ptr_load_def, compile_ptr_store_def, compile_imm_store_word_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_label_def, fresh_var_def, emit_inst_def, emit_op_def,
       emit_void_def, fresh_id_def, emit_def, new_block_def, Excl "isPREFIX"])) >>
  strip_tac >> gvs[Excl "isPREFIX"] >>
  qpat_x_assum `fn_has_code _ _ _` mp_tac >>
  simp[fn_has_code_def, emitted_blocks_def, Excl "isPREFIX"] >>
  strip_tac >> gvs[not_fresh_at_def, Excl "isPREFIX"] >>
  gvs[DISJ_IMP_THM, FORALL_AND_THM, ADD1, Excl "isPREFIX"] >>
  qexistsl_tac [`fresh_label_output "wcopy_cond" sm.cs_next_label`,
    `fresh_label_output "wcopy_body" (sm.cs_next_label+1)`] >>
  rpt (goal_assum (drule_at Any)) >>
  once_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, Excl "isPREFIX", fresh_label_output_def]
QED

Theorem body_assign_immutable_bytes_loop_init_actual[local]:
  !sm src dst count imm a b n lo ctx cv s0 G0 tn0 D explicit func PG
   hdr loop_body exit ie ih ib test sx sp value dx dp ip nc bbE bbH bbB.
  copy_old_operand sm src /\ copy_old_operand sm dst /\
  copy_old_operand sm count /\
  (case imm of NONE => T | SOME region => copy_old_operand sm region) /\
  eval_operand src s0 = SOME a /\ op_taint tn0 src = {} /\
  (0 < n ==> ?p. src = Var p /\ ptr_covers G0 tn0 p s0 (32*n)) /\
  eval_operand dst s0 = SOME b /\ op_taint tn0 dst = {} /\ op_prov G0 dst = NONE /\
  eval_operand count s0 = SOME (n2w n) /\
  op_taint tn0 count = {} /\ op_prov G0 count = NONE /\
  (case imm of NONE => T | SOME region =>
    eval_operand region s0 = SOME (0w:bytes32) /\
    op_taint tn0 region = {} /\ op_prov G0 region = NONE) /\
  n < dimword(:256) /\ lo <= w2n a /\
  w2n a + 32*n < dimword(:256) /\ w2n b + 32*n <= lo /\
  allocas_from lo s0 /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  ALL_DISTINCT [hdr;loop_body;exit] /\
  ALL_DISTINCT ([cv;test;sx;sp;value;dx;dp;nc] ++
    (case imm of NONE => [] | SOME region => [ip])) /\
  (!x. MEM x ([cv;test;sx;sp;value;dx;dp;nc] ++
    (case imm of NONE => [] | SOME region => [ip])) ==> ~not_fresh_at sm x) /\
  lookup_block sm.cs_current_bb func.fn_blocks = SOME bbE /\
  isPREFIX [mk_inst ie ASSIGN [Lit 0w] [cv]; mk_inst (ie+1) JMP [Label hdr] []]
    (DROP (LENGTH sm.cs_current_insts) bbE.bb_instructions) /\
  lookup_block hdr func.fn_blocks = SOME bbH /\
  isPREFIX [mk_inst ih EQ [Var cv;count] [test];
    mk_inst (ih+1) JNZ [Var test;Label exit;Label loop_body] []] bbH.bb_instructions /\
  lookup_block loop_body func.fn_blocks = SOME bbB /\
  isPREFIX ([mk_inst ib MUL [Var cv;Lit 32w] [sx];
    mk_inst (ib+1) ADD [src;Var sx] [sp];
    mk_inst (ib+2) MLOAD [Var sp] [value];
    mk_inst (ib+3) MUL [Var cv;Lit 32w] [dx];
    mk_inst (ib+4) ADD [dst;Var dx] [dp]] ++
    (case imm of NONE =>
      [mk_inst (ib+5) ISTORE [Var dp;Var value] [];
       mk_inst (ib+6) ADD [Var cv;Lit 1w] [nc];
       mk_inst (ib+7) ASSIGN [Var nc] [cv]; mk_inst (ib+8) JMP [Label hdr] []]
     | SOME region =>
      [mk_inst (ib+5) ADD [region;Var dp] [ip];
       mk_inst (ib+6) ISTORE [Var ip;Var value] [];
       mk_inst (ib+7) ADD [Var cv;Lit 1w] [nc];
       mk_inst (ib+8) ASSIGN [Var nc] [cv]; mk_inst (ib+9) JMP [Label hdr] []]))
    bbB.bb_instructions /\
  ~s0.vs_halted /\ s0.vs_current_bb = sm.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?r G1 tn1.
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s0,G0,tn0) [] (OK r,G1,tn1) /\
    0 <= n /\
    (r with <|vs_vars := s0.vs_vars; vs_current_bb := s0.vs_current_bb;
       vs_prev_bb := s0.vs_prev_bb; vs_inst_idx := s0.vs_inst_idx|>) =
      immutable_transfers T T a b 0 0 s0 /\
    lookup_var cv r = SOME (n2w 0) /\
    FLOOKUP G1 cv = NONE /\ op_taint tn1 (Var cv) = {} /\
    (!x. not_fresh_at sm x ==>
      lookup_var x r = lookup_var x s0 /\ FLOOKUP G1 x = FLOOKUP G0 x /\
      op_taint tn1 (Var x) = op_taint tn0 (Var x)) /\
    eval_operand src r = SOME a /\ op_taint tn1 src = {} /\
    (0 < n ==> ?p. src = Var p /\ ptr_covers G1 tn1 p r (32*n)) /\
    eval_operand dst r = SOME b /\ op_taint tn1 dst = {} /\ op_prov G1 dst = NONE /\
    eval_operand count r = SOME (n2w n) /\
    op_taint tn1 count = {} /\ op_prov G1 count = NONE /\
    (case imm of NONE => T | SOME region =>
      eval_operand region r = SOME (0w:bytes32) /\
      op_taint tn1 region = {} /\ op_prov G1 region = NONE) /\
    r.vs_allocas = s0.vs_allocas /\ r.vs_alloca_next = s0.vs_alloca_next /\
    r.vs_fmp = s0.vs_fmp /\ r.vs_initial_fmp = s0.vs_initial_fmp /\
    allocas_from lo r /\ (ctx_has_dalloca ctx ==> allocas_below_fmp r) /\
    (!k. k < 32*0 ==> (w2n b+k IN tn1.t_mem <=> w2n a+k IN tn0.t_mem)) /\
    (!i. ~(w2n b <= i /\ i < w2n b+32*0) ==> (i IN tn1.t_mem <=> i IN tn0.t_mem)) /\
    tn1.t_stor = tn0.t_stor /\ tn1.t_trans = tn0.t_trans /\
    ~r.vs_halted /\ r.vs_current_bb = hdr /\ r.vs_inst_idx = 0
Proof
  rpt gen_tac >> strip_tac >>
  `!x. not_fresh_at sm x ==> x <> cv` by
    ((rpt strip_tac >> first_x_assum (qspec_then `cv` mp_tac) >> simp[] >> (gvs[]))) >>
  `isPREFIX [mk_inst ie ASSIGN [Lit 0w] [cv]]
     (DROP s0.vs_inst_idx bbE.bb_instructions)` by
    (qpat_assum `isPREFIX [mk_inst _ ASSIGN _ _; _] _`
       (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >> simp[]) >>
  `step_inst_base (mk_inst ie ASSIGN [Lit 0w] [cv]) s0 =
    OK (update_var cv 0w s0)` by
    simp[step_inst_base_def, mk_inst_def, eval_operands_def, eval_operand_def] >>
  `ptr_inst_ok D 0 0 ctx func G0 tn0 (mk_inst ie ASSIGN [Lit 0w] [cv]) s0` by
    (simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
      mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke, update_var_def]) >>
  `run_inst_seq_mem_ok [mk_inst ie ASSIGN [Lit 0w] [cv]] s0` by
    (simp[run_inst_seq_mem_ok_last, inst_dload_in_section_def, mk_inst_def] >>
     irule below_frontier_no_ranges >> simp[]) >>
  qabbrev_tac `i0 = mk_inst ie ASSIGN [Lit 0w] [cv]` >>
  qabbrev_tac `u0 = update_var cv 0w s0` >>
  qabbrev_tac `G1 = step_prov PG G0 i0 u0` >>
  qabbrev_tac `tn1 = step_taint i0 s0 u0 tn0` >>
  `inst_seq_ptr D 0 ctx func PG G0 tn0 [i0] s0 G1 tn1` by
    simp[inst_seq_ptr_def, Abbr `G1`, Abbr `tn1`] >>
  `run_inst_seq [i0] s0 = OK u0` by simp[run_inst_seq_def] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
      i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) [i0]` by
    simp[Abbr `i0`, mk_inst_def, is_terminator_def] >>
  `lookup_block s0.vs_current_bb func.fn_blocks = SOME bbE` by simp[] >>
  `(ptrDiscipline$ctx_has_dalloca ctx ==>
    !pre i post u. [i0] = pre ++ i::post /\ run_inst_seq pre s0 = OK u ==>
      unitTransformDefs$dalloca_no_wrap i u)` by
    (rpt strip_tac >>
     `MEM i [i0]` by
       (qpat_assum `[i0] = _` (fn th => pure_once_rewrite_tac [th]) >> simp[]) >>
     gvs[Abbr `i0`, mk_inst_def]) >>
  drule_all_then (qspec_then `explicit` strip_assume_tac) run_inst_seq_origin_ptr_lift >>
  qabbrev_tac `t0 = u0 with vs_inst_idx := s0.vs_inst_idx + LENGTH [i0]` >>
  `get_instruction bbE (s0.vs_inst_idx+1) =
     SOME (mk_inst (ie+1) JMP [Label hdr] [])` by
    (qpat_assum `isPREFIX [i0; _] _`
      (mp_then Any strip_assume_tac instruction_prefix_cursor) >>
     drule instruction_prefix_cursor >> simp[ADD1]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t0,G1,tn1) []
     (OK (jump_to hdr t0),G1,tn1)` by
    (irule jmp_origin_ptr_path >>
     simp[Abbr `t0`, Abbr `u0`, update_var_def] >>
     gvs[allocas_from_def, allocas_below_fmp_def, update_var_def] >> metis_tac[]) >>
  qexistsl_tac [`jump_to hdr t0`, `G1`, `tn1`] >>
  conj_tac >- metis_tac[gas_origin_ptr_path_append, APPEND_NIL] >>
  `G1 = DRESTRICT G0 (COMPL {cv}) /\ tn1 = tn0 with t_var := tn0.t_var |+ (cv,{})` by
    (simp[Abbr `G1`, Abbr `tn1`, Abbr `i0`, Abbr `u0`,
      step_prov_def, set_prov_def, out_prov_def, first_prov_def, op_prov_def,
      step_taint_def, mem_taint_def, new_site_bytes_def, step_writes_def,
      written_taint_def, out_taint_def, op_taint_def, set_var_taint_def,
      adopt_reset_def, store_taint_def, imm_taint_def, mk_inst_def,
      source_memory_write_ranges_def, eval_operand_def, update_var_def,
      range_bytes_def, flookup_thm, SF CONJ_ss, taint_component_equality, EXTENSION]) >>
  `!op. copy_old_operand sm op ==>
    eval_operand op (jump_to hdr t0) = eval_operand op s0 /\
    op_taint tn1 op = op_taint tn0 op /\ op_prov G1 op = op_prov G0 op` by
    (gen_tac >> Cases_on `op` >>
     simp[copy_old_operand_def, Abbr `t0`, Abbr `u0`, jump_to_def,
       update_var_def, eval_operand_def, lookup_var_def, op_taint_def,
       op_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
     rpt strip_tac >> gvs[] >> metis_tac[]) >>
  `(0 < n ==> ?p. src = Var p /\ ptr_covers G1 tn1 p (jump_to hdr t0) (32*n))` by
    (strip_tac >> qpat_x_assum `0 < n ==> ?p. _` drule >> strip_tac >>
     `p <> cv` by metis_tac[copy_old_operand_def] >>
     qexists_tac `p` >> simp[] >> irule ptr_covers_frame >>
     qexistsl_tac [`G0`, `s0`, `tn0`] >>
     simp[Abbr `t0`, Abbr `u0`, jump_to_def,
       update_var_def, lookup_var_def, op_taint_def, FLOOKUP_DRESTRICT,
       FLOOKUP_UPDATE]) >>
  `(case imm of NONE => T | SOME region =>
      eval_operand region (jump_to hdr t0) = SOME (0w:bytes32) /\
      op_taint tn1 region = {} /\ op_prov G1 region = NONE)` by
    (Cases_on `imm` >> gvs[] >> metis_tac[]) >>
  simp[] >>
  simp[Abbr `t0`, Abbr `u0`, immutable_transfers_def, jump_to_def,
    update_var_def, lookup_var_def, op_taint_def, FLOOKUP_UPDATE,
    FLOOKUP_DRESTRICT, venom_state_component_equality] >>
  gvs[allocas_from_def, allocas_below_fmp_def]
  >> (metis_tac[])
QED

Theorem body_assign_immutable_loop_mul_segment[local]:
  eval_operand arg s = SOME a /\ op_taint tn arg = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?Gf tnf t.
    run_inst_seq [mk_inst id MUL [arg;Lit 32w] [out]] s = OK t /\
    (!k. inst_seq_ptr D lo ctx fn PG G tn
      [mk_inst id MUL [arg;Lit 32w] [out]]
      (s with vs_inst_idx := k) Gf tnf) /\
    t = update_var out (a * 32w) s /\
    op_taint tnf (Var out) = {} /\ op_prov Gf (Var out) = NONE /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. p <> out ==> FLOOKUP Gf p = FLOOKUP G p /\
       op_taint tnf (Var p) = op_taint tn (Var p)) /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!p n. p <> out /\ ptr_covers G tn p s n ==> ptr_covers Gf tnf p t n)
Proof
  strip_tac >>
  qexistsl [`step_prov PG G (mk_inst id MUL [arg;Lit 32w] [out])
      (update_var out (a*32w) s)`,
    `step_taint (mk_inst id MUL [arg;Lit 32w] [out]) s
      (update_var out (a*32w) s) tn`, `update_var out (a*32w) s`] >>
  `step_inst_base (mk_inst id MUL [arg;Lit 32w] [out]) s =
    OK (update_var out (a*32w) s)` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
         eval_operand_def] >>
  simp[run_inst_seq_def, copy_mul_ghost_frame] >>
  conj_tac
  >- (gen_tac >> simp[inst_seq_ptr_def] >> conj_tac
      >- ((irule ptr_inst_ok_copy_arith >>
          fs[eval_op_inst_idx, allocas_from_def, allocas_below_fmp_def,
             op_taint_def] >> (metis_tac[eval_op_inst_idx, allocas_from_def, allocas_below_fmp_def, op_taint_def, ptr_inst_ok_copy_arith]))) >>
      simp[step_inst_inst_idx_indep, exec_result_map_def,
           mk_inst_def, is_terminator_def]) >>
  conj_tac
  >- (simp[step_taint_def, out_taint_def, mk_inst_def, set_var_taint_def,
          op_taint_def, FLOOKUP_UPDATE, eval_operand_def] >> (gvs[step_taint_def, out_taint_def, mk_inst_def, set_var_taint_def, op_taint_def, FLOOKUP_UPDATE, eval_operand_def])) >>
  conj_tac
  >- (irule step_prov_out_none >> simp[mk_inst_def] >>
      irule out_prov_other_none >> simp[mk_inst_def]) >>
  simp[allocas_from_def, allocas_below_fmp_def, update_var_def] >>
  rpt strip_tac >> irule ptr_covers_step_frame >>
  simp[mk_inst_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem body_assign_immutable_loop_load_segment[local]:
  lookup_var root s = SOME a /\ eval_operand offset s = SOME (n2w off) /\
  ptr_covers G tn root s capacity /\ op_taint tn offset = {} /\
  off < capacity /\ off+32 <= capacity /\ w2n a+off < dimword(:256) /\
  root <> addr /\ addr <> value /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?Gf tnf t.
    run_inst_seq [mk_inst id ADD [Var root;offset] [addr];
      mk_inst (id+1) MLOAD [Var addr] [value]] s = OK t /\
    inst_seq_ptr D lo ctx fn PG G tn
      [mk_inst id ADD [Var root;offset] [addr];
       mk_inst (id+1) MLOAD [Var addr] [value]] s Gf tnf /\
    t = update_var value (mload (w2n (a+n2w off)) s)
      (update_var addr (a+n2w off) s) /\
    op_taint tnf (Var value) = mem_word_taint tn.t_mem (w2n (a+n2w off)) /\
    op_prov Gf (Var value) = NONE /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. p <> addr /\ p <> value ==>
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p)) /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!p c. p <> addr /\ p <> value /\ ptr_covers G tn p s c ==>
      ptr_covers Gf tnf p t c)
Proof
  strip_tac >>
  `?G1 tn1 u.
     run_inst_seq [mk_inst id ADD [Var root;offset] [addr]] s = OK u /\
     inst_seq_ptr D lo ctx fn PG G tn
       [mk_inst id ADD [Var root;offset] [addr]] s G1 tn1 /\
     u = update_var addr (a+n2w off) s /\ ptr_covers G1 tn1 addr u 32 /\
     tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
     tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
     (!p. p <> addr ==> FLOOKUP G1 p = FLOOKUP G p /\
       op_taint tn1 (Var p) = op_taint tn (Var p)) /\
     allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
     (!p c. p <> addr /\ ptr_covers G tn p s c ==> ptr_covers G1 tn1 p u c)` by
    (irule copy_offset_segment >> metis_tac[]) >>
  qmatch_asmsub_abbrev_tac `u = update_var addr w s` >>
  qabbrev_tac `t = update_var value (mload (w2n w) u) u` >>
  `lookup_var addr u = SOME w /\
   run_inst_seq [mk_inst (id+1) MLOAD [Var addr] [value]] u = OK t` by
    (simp[Abbr `t`, run_inst_seq_def, step_inst_base_opcode_eqs,
      exec_read1_def, mk_inst_def, eval_operand_def] >>
     gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `?Gf tnf.
     (!k. inst_seq_ptr D lo ctx fn PG G1 tn1
       [mk_inst (id+1) MLOAD [Var addr] [value]]
       (u with vs_inst_idx := k) Gf tnf) /\
     op_taint tnf (Var value) = mem_word_taint tn1.t_mem (w2n w) /\
     op_prov Gf (Var value) = NONE /\
     tnf.t_mem = tn1.t_mem /\ tnf.t_stor = tn1.t_stor /\
     tnf.t_trans = tn1.t_trans /\ tnf.t_imm = tn1.t_imm /\
     (!p. p <> value ==> FLOOKUP Gf p = FLOOKUP G1 p /\
       op_taint tnf (Var p) = op_taint tn1 (Var p)) /\
     allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
     (!p c. p <> value /\ ptr_covers G1 tn1 p u c ==> ptr_covers Gf tnf p t c)` by
    (irule (BETA_RULE (Q.INST [`P` |-> `\p:string. p <> value`]
       ctor_mload_segment)) >> simp[]) >>
  qexistsl [`Gf`, `tnf`, `t`] >>
  `[mk_inst id ADD [Var root;offset] [addr];
    mk_inst (id+1) MLOAD [Var addr] [value]] =
   [mk_inst id ADD [Var root;offset] [addr]] ++
   [mk_inst (id+1) MLOAD [Var addr] [value]]` by simp[] >>
  pop_assum SUBST1_TAC >>
  conj_tac >- metis_tac[run_inst_seq_append] >>
  conj_tac
  >- (irule inst_seq_ptr_append >>
      conj_tac >- simp[mk_inst_def, is_terminator_def] >>
      qexistsl [`G1`, `u`, `tn1`] >> simp[]) >>
  simp[Abbr `t`, Abbr `w`, mload_update_var] >>
  metis_tac[]
QED

Theorem body_assign_immutable_loop_old_operand[local]:
  t.vs_labels = s.vs_labels /\
  (!x. not_fresh_at sm x ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
    op_taint tm (Var x) = op_taint tn (Var x)) /\ copy_old_operand sm arg ==>
  eval_operand arg t = eval_operand arg s /\ op_taint tm arg = op_taint tn arg /\
  op_prov H arg = op_prov G arg
Proof
  strip_tac >> Cases_on `arg` >>
  gvs[copy_old_operand_def, eval_operand_def, op_taint_def, op_prov_def] >>
  metis_tac[]
QED

Theorem body_assign_immutable_loop_store_segment[local]:
  eval_operand dst s = SOME a /\ op_taint tn dst = {} /\ op_prov G dst = NONE /\
  w2n a + 32 <= lo /\ eval_operand (Var v) s = SOME value /\
  (case imm of NONE => T | SOME region =>
    eval_operand region s = SOME 0w /\ op_taint tn region = {} /\ op_prov G region = NONE /\ v <> tmp) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?Gf tnf t.
    run_inst_seq (case imm of NONE => [mk_inst id ISTORE [dst;Var v] []]
      | SOME region => [mk_inst id ADD [region;dst] [tmp];
                        mk_inst (id+1) ISTORE [Var tmp;Var v] []]) s = OK t /\
    (!k. inst_seq_ptr D lo ctx fn PG G tn
      (case imm of NONE => [mk_inst id ISTORE [dst;Var v] []]
       | SOME region => [mk_inst id ADD [region;dst] [tmp];
                         mk_inst (id+1) ISTORE [Var tmp;Var v] []])
      (s with vs_inst_idx := k) Gf tnf) /\
    t = istore (w2n a) value
      (case imm of NONE => s | SOME region => update_var tmp a s) /\
    tnf.t_mem = (tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a+32}) UNION
      {w2n a+k | k IN op_taint tn (Var v)} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. (imm = NONE \/ p <> tmp) ==> FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!p n. (imm = NONE \/ p <> tmp) /\ ptr_covers G tn p s n ==> ptr_covers Gf tnf p t n)
Proof
  strip_tac >> Cases_on `imm` >> fs[]
  >- (drule_all ctor_istore_segment >>
      disch_then (qspecl_then [`id`, `fn`, `PG`, `D`] strip_assume_tac) >>
      qexistsl [`Gf`, `tnf`] >> gvs[ADD_COMM])
  >> `!p:string. p <> tmp ==> p <> tmp` by simp[] >>
  `!x. Var v = Var x ==> x <> tmp` by simp[] >>
  drule_all (BETA_RULE (Q.INST [`P` |-> `\p:string. p <> tmp`] ctor_word_store_seq)) >>
  disch_then (qspecl_then [`id`, `fn`, `PG`, `D`] strip_assume_tac) >>
  qexistsl [`Gf`, `tnf`] >> gvs[ADD_COMM]
QED

Theorem body_assign_immutable_bytes_loop_step_actual[local]:
  !sm src dst count imm a b n lo ctx cv s0 G0 tn0
    D explicit func PG hdr loop_body exit ie ih ib test sx sp value dx dp ip nc bbE bbH bbB.
  copy_old_operand sm src /\ copy_old_operand sm dst /\
  copy_old_operand sm count /\
  (case imm of NONE => T | SOME region => copy_old_operand sm region) /\
  eval_operand src s0 = SOME a /\ op_taint tn0 src = {} /\
  (0 < n ==> ?p. src = Var p /\ ptr_covers G0 tn0 p s0 (32*n)) /\
  eval_operand dst s0 = SOME b /\
  op_taint tn0 dst = {} /\ op_prov G0 dst = NONE /\
  eval_operand count s0 = SOME (n2w n) /\
  op_taint tn0 count = {} /\ op_prov G0 count = NONE /\
  (case imm of NONE => T | SOME region =>
    eval_operand region s0 = SOME (0w:bytes32) /\
    op_taint tn0 region = {} /\ op_prov G0 region = NONE) /\
  n < dimword(:256) /\ lo <= w2n a /\
  w2n a + 32*n < dimword(:256) /\ w2n b + 32*n <= lo /\
  allocas_from lo s0 /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (0 < n ==> w2n a + 32*n <= s0.vs_alloca_next) /\
  ALL_DISTINCT [hdr;loop_body;exit] /\
  ALL_DISTINCT ([cv;test;sx;sp;value;dx;dp;nc] ++
    (case imm of NONE => [] | SOME region => [ip])) /\
  (!x. MEM x ([cv;test;sx;sp;value;dx;dp;nc] ++
    (case imm of NONE => [] | SOME region => [ip])) ==> ~not_fresh_at sm x) /\
  lookup_block sm.cs_current_bb func.fn_blocks = SOME bbE /\
  isPREFIX [mk_inst ie ASSIGN [Lit 0w] [cv];
            mk_inst (ie+1) JMP [Label hdr] []]
    (DROP (LENGTH sm.cs_current_insts) bbE.bb_instructions) /\
  lookup_block hdr func.fn_blocks = SOME bbH /\
  isPREFIX [mk_inst ih EQ [Var cv; count] [test];
            mk_inst (ih+1) JNZ [Var test; Label exit; Label loop_body] []]
    bbH.bb_instructions /\
  lookup_block loop_body func.fn_blocks = SOME bbB /\
  isPREFIX
    ([mk_inst ib MUL [Var cv; Lit 32w] [sx];
      mk_inst (ib+1) ADD [src; Var sx] [sp];
      mk_inst (ib+2) MLOAD [Var sp] [value];
      mk_inst (ib+3) MUL [Var cv; Lit 32w] [dx];
      mk_inst (ib+4) ADD [dst; Var dx] [dp]] ++
     (case imm of
       NONE =>
         [mk_inst (ib+5) ISTORE [Var dp; Var value] [];
          mk_inst (ib+6) ADD [Var cv; Lit 1w] [nc];
          mk_inst (ib+7) ASSIGN [Var nc] [cv];
          mk_inst (ib+8) JMP [Label hdr] []]
     | SOME region =>
         [mk_inst (ib+5) ADD [region; Var dp] [ip];
          mk_inst (ib+6) ISTORE [Var ip; Var value] [];
          mk_inst (ib+7) ADD [Var cv; Lit 1w] [nc];
          mk_inst (ib+8) ASSIGN [Var nc] [cv];
          mk_inst (ib+9) JMP [Label hdr] []])) bbB.bb_instructions ==>
  !j G tn q.
    j<n /\
    (j <= n /\
     (q with <|vs_vars := s0.vs_vars;
               vs_current_bb := s0.vs_current_bb;
               vs_prev_bb := s0.vs_prev_bb;
               vs_inst_idx := s0.vs_inst_idx|>) =
       immutable_transfers T T a b j 0 s0 /\
     lookup_var cv q = SOME (n2w j) /\
     FLOOKUP G cv = NONE /\ op_taint tn (Var cv) = {} /\
     (!x. not_fresh_at sm x ==>
       lookup_var x q = lookup_var x s0 /\
       FLOOKUP G x = FLOOKUP G0 x /\
       op_taint tn (Var x) = op_taint tn0 (Var x)) /\
     eval_operand src q = SOME a /\ op_taint tn src = {} /\
     (0 < n ==> ?p. src = Var p /\ ptr_covers G tn p q (32*n)) /\
     eval_operand dst q = SOME b /\ op_taint tn dst = {} /\ op_prov G dst = NONE /\
     eval_operand count q = SOME (n2w n) /\
     op_taint tn count = {} /\ op_prov G count = NONE /\
     (case imm of NONE => T | SOME region =>
       eval_operand region q = SOME (0w:bytes32) /\
       op_taint tn region = {} /\ op_prov G region = NONE) /\
     q.vs_allocas = s0.vs_allocas /\ q.vs_alloca_next = s0.vs_alloca_next /\
     q.vs_fmp = s0.vs_fmp /\ q.vs_initial_fmp = s0.vs_initial_fmp /\
     allocas_from lo q /\ (ctx_has_dalloca ctx ==> allocas_below_fmp q) /\
     (!k. k < 32*j ==>
       (w2n b + k IN tn.t_mem <=> w2n a + k IN tn0.t_mem)) /\
     (!i. ~(w2n b <= i /\ i < w2n b + 32*j) ==>
       (i IN tn.t_mem <=> i IN tn0.t_mem)) /\
     tn.t_stor = tn0.t_stor /\ tn.t_trans = tn0.t_trans) /\
    ~q.vs_halted /\ q.vs_current_bb=loop_body /\ q.vs_inst_idx=0 ==>
    ?r G1 tn1.
      gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (q,G,tn) [] (OK r,G1,tn1) /\
      ((j+1) <= n /\
       (r with <|vs_vars := s0.vs_vars;
                 vs_current_bb := s0.vs_current_bb;
                 vs_prev_bb := s0.vs_prev_bb;
                 vs_inst_idx := s0.vs_inst_idx|>) =
         immutable_transfers T T a b (j+1) 0 s0 /\
       lookup_var cv r = SOME (n2w (j+1)) /\
       FLOOKUP G1 cv = NONE /\ op_taint tn1 (Var cv) = {} /\
       (!x. not_fresh_at sm x ==>
         lookup_var x r = lookup_var x s0 /\
         FLOOKUP G1 x = FLOOKUP G0 x /\
         op_taint tn1 (Var x) = op_taint tn0 (Var x)) /\
       eval_operand src r = SOME a /\ op_taint tn1 src = {} /\
       (0 < n ==> ?p. src = Var p /\ ptr_covers G1 tn1 p r (32*n)) /\
       eval_operand dst r = SOME b /\ op_taint tn1 dst = {} /\ op_prov G1 dst = NONE /\
       eval_operand count r = SOME (n2w n) /\
       op_taint tn1 count = {} /\ op_prov G1 count = NONE /\
       (case imm of NONE => T | SOME region =>
         eval_operand region r = SOME (0w:bytes32) /\
         op_taint tn1 region = {} /\ op_prov G1 region = NONE) /\
       r.vs_allocas = s0.vs_allocas /\ r.vs_alloca_next = s0.vs_alloca_next /\
       r.vs_fmp = s0.vs_fmp /\ r.vs_initial_fmp = s0.vs_initial_fmp /\
       allocas_from lo r /\ (ctx_has_dalloca ctx ==> allocas_below_fmp r) /\
       (!k. k < 32*(j+1) ==>
         (w2n b + k IN tn1.t_mem <=> w2n a + k IN tn0.t_mem)) /\
       (!i. ~(w2n b <= i /\ i < w2n b + 32*(j+1)) ==>
         (i IN tn1.t_mem <=> i IN tn0.t_mem)) /\
       tn1.t_stor = tn0.t_stor /\ tn1.t_trans = tn0.t_trans) /\
      ~r.vs_halted /\ r.vs_current_bb=hdr /\ r.vs_inst_idx=0
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `0 < n` by decide_tac >>
  `?root. src = Var root /\ ptr_covers G tn root q (32*n)` by metis_tac[] >>
  `root <> sx /\ root <> sp /\ root <> value` by
    (fs[copy_old_operand_def] >> metis_tac[MEM, MEM_APPEND]) >>
  `ALL_DISTINCT [cv;test;sx;sp;value;dx;dp;nc]` by
    fs[ALL_DISTINCT_APPEND] >>
  `?Ga ta qa.
     run_inst_seq [mk_inst ib MUL [Var cv;Lit 32w] [sx]] q = OK qa /\
     (!k. inst_seq_ptr D lo ctx func PG G tn
       [mk_inst ib MUL [Var cv;Lit 32w] [sx]]
       (q with vs_inst_idx := k) Ga ta) /\
     qa = update_var sx ((n2w j)*32w) q /\
     op_taint ta (Var sx) = {} /\ op_prov Ga (Var sx) = NONE /\
     ta.t_mem = tn.t_mem /\ ta.t_stor = tn.t_stor /\
     ta.t_trans = tn.t_trans /\ ta.t_imm = tn.t_imm /\
     (!p. p <> sx ==> FLOOKUP Ga p = FLOOKUP G p /\
       op_taint ta (Var p) = op_taint tn (Var p)) /\
     allocas_from lo qa /\ (ctx_has_dalloca ctx ==> allocas_below_fmp qa) /\
     (!p c. p <> sx /\ ptr_covers G tn p q c ==> ptr_covers Ga ta p qa c)` by
    (irule body_assign_immutable_loop_mul_segment >> simp[eval_operand_def]) >>
  `n2w j * 32w : bytes32 = n2w (32*j)` by
    (rewrite_tac[GSYM word_mul_n2w] >> simp[WORD_MULT_COMM]) >>
  `lookup_var root q = SOME a` by metis_tac[eval_operand_def] >>
  `lookup_var root qa = SOME a /\
   eval_operand (Var sx) qa = SOME (n2w (32*j)) /\
   ptr_covers Ga ta root qa (32*n)` by
    (conj_tac >- asm_rewrite_tac[lookup_var_update_var] >>
     conj_tac >- asm_rewrite_tac[eval_operand_def, lookup_var_update_var] >>
     metis_tac[]) >>
  qabbrev_tac `qa1 = qa with vs_inst_idx := 1` >>
  `?Gb tb qb.
     run_inst_seq [mk_inst (ib+1) ADD [Var root;Var sx] [sp];
       mk_inst ((ib+1)+1) MLOAD [Var sp] [value]] qa1 = OK qb /\
     inst_seq_ptr D lo ctx func PG Ga ta
       [mk_inst (ib+1) ADD [Var root;Var sx] [sp];
        mk_inst ((ib+1)+1) MLOAD [Var sp] [value]] qa1 Gb tb /\
     qb = update_var value (mload (w2n (a+n2w (32*j))) qa1)
       (update_var sp (a+n2w (32*j)) qa1) /\
     op_taint tb (Var value) = mem_word_taint ta.t_mem (w2n (a+n2w (32*j))) /\
     op_prov Gb (Var value) = NONE /\
     tb.t_mem = ta.t_mem /\ tb.t_stor = ta.t_stor /\
     tb.t_trans = ta.t_trans /\ tb.t_imm = ta.t_imm /\
     (!p. p <> sp /\ p <> value ==>
       FLOOKUP Gb p = FLOOKUP Ga p /\ op_taint tb (Var p) = op_taint ta (Var p)) /\
     allocas_from lo qb /\ (ctx_has_dalloca ctx ==> allocas_below_fmp qb) /\
     (!p c. p <> sp /\ p <> value /\ ptr_covers Ga ta p qa1 c ==>
       ptr_covers Gb tb p qb c)` by
    (irule body_assign_immutable_loop_load_segment >>
     simp[Abbr `qa1`, eval_op_inst_idx,
          ptr_covers_inst_idx, allocas_from_def, allocas_below_fmp_def] >>
     conj_tac >- fs[ALL_DISTINCT] >>
     conj_tac >- fs[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     qexists_tac `32*n` >> gvs[] >> decide_tac) >>
  `lookup_var cv qb = SOME (n2w j) /\ op_taint tb (Var cv) = {}` by
    (fs[ALL_DISTINCT, Abbr `qa1`, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `?Gc tc qc.
     run_inst_seq [mk_inst (ib+3) MUL [Var cv;Lit 32w] [dx]] qb = OK qc /\
     (!k. inst_seq_ptr D lo ctx func PG Gb tb
       [mk_inst (ib+3) MUL [Var cv;Lit 32w] [dx]]
       (qb with vs_inst_idx := k) Gc tc) /\
     qc = update_var dx ((n2w j)*32w) qb /\
     op_taint tc (Var dx) = {} /\ op_prov Gc (Var dx) = NONE /\
     tc.t_mem = tb.t_mem /\ tc.t_stor = tb.t_stor /\
     tc.t_trans = tb.t_trans /\ tc.t_imm = tb.t_imm /\
     (!p. p <> dx ==> FLOOKUP Gc p = FLOOKUP Gb p /\
       op_taint tc (Var p) = op_taint tb (Var p)) /\
     allocas_from lo qc /\ (ctx_has_dalloca ctx ==> allocas_below_fmp qc) /\
     (!p c. p <> dx /\ ptr_covers Gb tb p qb c ==> ptr_covers Gc tc p qc c)` by
    (irule body_assign_immutable_loop_mul_segment >> simp[eval_operand_def]) >>
  `!x. not_fresh_at sm x ==>
     x <> sx /\ x <> sp /\ x <> value /\ x <> dx /\ x <> dp /\ x <> nc /\ x <> cv` by
    (rpt strip_tac >> metis_tac[MEM, MEM_APPEND]) >>
  `!x. not_fresh_at sm x ==>
     lookup_var x qc = lookup_var x q /\ FLOOKUP Gc x = FLOOKUP G x /\
     op_taint tc (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >>
     `x <> sx /\ x <> sp /\ x <> value /\ x <> dx` by metis_tac[] >>
     fs[Abbr `qa1`, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `qc.vs_labels = q.vs_labels` by
    simp[Abbr `qa1`, update_var_def] >>
  `eval_operand dst qc = eval_operand dst q /\ op_taint tc dst = op_taint tn dst /\
   op_prov Gc dst = op_prov G dst` by
    (irule body_assign_immutable_loop_old_operand >>
     conj_tac >- first_assum ACCEPT_TAC >> qexists_tac `sm` >>
     conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC) >>
  `eval_operand (Var dx) qc = SOME (n2w (32*j))` by
    simp[eval_operand_def, lookup_var_update_var] >>
  qabbrev_tac `qd = update_var dp (b+n2w (32*j)) qc` >>
  `run_inst_seq [mk_inst (ib+4) ADD [dst;Var dx] [dp]] qc = OK qd` by
    (qpat_x_assum `qc = update_var _ _ _` kall_tac >>
     (simp[Abbr `qd`, run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def])) >>
  `eval_operand dst qc = SOME b /\ op_taint tc dst = {} /\ op_prov Gc dst = NONE` by simp[] >>
  drule_at (Pat `run_inst_seq _ _ = _`)
    (BETA_RULE (Q.INST [`out` |-> `dp`, `P` |-> `\p:string. p <> dp`]
      ctor_base_add_segment)) >>
  disch_then (drule_at (Pat `op_prov _ dst = NONE`)) >>
  disch_then (drule_at (Pat `op_taint _ dst = {}`)) >>
  disch_then (drule_at (Pat `eval_operand dst qc = _`)) >>
  disch_then (drule_at (Pat `eval_operand (Var dx) qc = _`)) >>
  disch_then (drule_at (Pat `allocas_from _ qc`)) >>
  disch_then (drule_at (Pat `ctx_has_dalloca _ ==> allocas_below_fmp qc`)) >>
  disch_then (qspecl_then [`func`, `PG`, `D`] mp_tac) >>
  impl_tac >- simp[] >>
  disch_then (qx_choose_then `Gd` (qx_choose_then `td` strip_assume_tac)) >>
  `w2n b + 32*j < dimword(:256) /\ w2n b + 32*j + 32 <= lo` by decide_tac >>
  `w2n (b+n2w (32*j)) = w2n b + 32*j` by
    (`32*j < dimword(:256)` by decide_tac >>
     simp[w2n_add_2]) >>
  `eval_operand (Var dp) qd = SOME (b+n2w (32*j)) /\
   eval_operand (Var value) qd = SOME (mload (w2n (a+n2w (32*j))) q)` by
    (fs[ALL_DISTINCT, Abbr `qd`, Abbr `qa1`,
        eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE, mload_def]) >>
  `!x. not_fresh_at sm x ==>
     lookup_var x qd = lookup_var x q /\ FLOOKUP Gd x = FLOOKUP G x /\
     op_taint td (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> `x <> dp` by metis_tac[] >>
     fs[Abbr `qd`, lookup_var_update_var]) >>
  `(case imm of NONE => T | SOME region =>
     eval_operand region qd = SOME 0w /\ op_taint td region = {} /\
     op_prov Gd region = NONE /\ value <> ip)` by
    (Cases_on `imm` >> fs[] >>
     `qd.vs_labels = q.vs_labels` by simp[Abbr `qd`, update_var_def] >>
     rename1 `copy_old_operand sm region` >>
     `eval_operand region qd = eval_operand region q /\
      op_taint td region = op_taint tn region /\ op_prov Gd region = op_prov G region` by
       (irule body_assign_immutable_loop_old_operand >>
        conj_tac >- first_assum ACCEPT_TAC >> qexists_tac `sm` >>
        conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC) >> simp[]) >>
  qpat_assum `eval_operand (Var dp) qd = _`
    (mp_then Any mp_tac body_assign_immutable_loop_store_segment) >>
  disch_then (drule_at (Pat `op_prov _ (Var dp) = NONE`) o SPEC_ALL) >>
  disch_then (drule_at (Pat `op_taint _ (Var dp) = {}`) o SPEC_ALL) >>
  disch_then (drule_at (Pat `eval_operand (Var value) qd = _`) o SPEC_ALL) >>
  disch_then (qspecl_then [`ip`, `lo`, `imm`, `ib+5`, `func`, `ctx`, `PG`, `D`] mp_tac) >>
  impl_tac >- simp[] >>
  disch_then (qx_choose_then `Ge` (qx_choose_then `te` (qx_choose_then `qe` strip_assume_tac))) >>
  Q_TAC (fn tm => SUBGOAL_THEN tm ASSUME_TAC)
    `((imm:operand option) = NONE) \/ ((cv:string) <> (ip:string))`
  >- (qpat_assum `ALL_DISTINCT (_ ++ _)` mp_tac >>
      Cases_on `imm` >> simp[NoAsms, ALL_DISTINCT]) >>
  `lookup_var cv qe = SOME (n2w j) /\ FLOOKUP Ge cv = NONE /\
   op_taint te (Var cv) = {}` by
    (`cv <> sx /\ cv <> sp /\ cv <> value /\ cv <> dx /\ cv <> dp` by fs[ALL_DISTINCT] >>
     conj_tac
     >- (qpat_assum `lookup_var cv q = _` (mp_tac o REWRITE_RULE [lookup_var_def]) >>
         Cases_on `imm`
         >- simp[Abbr `qd`, Abbr `qa1`, istore_def, lookup_var_def,
                 update_var_def, FLOOKUP_UPDATE] >>
         qpat_assum `SOME _ = NONE \/ cv <> ip`
           (mp_tac o REWRITE_RULE [optionTheory.NOT_SOME_NONE, OR_CLAUSES]) >>
         disch_tac >> `ip <> cv` by (qpat_assum `cv <> ip` mp_tac >> simp[NoAsms, EQ_SYM_EQ]) >>
         simp[Abbr `qd`, Abbr `qa1`, istore_def, lookup_var_def,
              update_var_def, FLOOKUP_UPDATE]) >>
     qpat_assum `!p. imm = NONE \/ p <> ip ==> _` (qspec_then `cv` mp_tac) >>
     qpat_assum `!p. p <> dp ==> _` (qspec_then `cv` mp_tac) >>
     qpat_assum `!p. p <> dx ==> _` (qspec_then `cv` mp_tac) >>
     qpat_assum `!p. p <> sp /\ p <> value ==> _` (qspec_then `cv` mp_tac) >>
     qpat_assum `!p. p <> sx ==> _` (qspec_then `cv` mp_tac) >> simp[]) >>
  qabbrev_tac `ci = if imm = NONE then ib+6 else ib+7` >>
  qabbrev_tac `qf = update_var nc (n2w (j+1)) qe` >>
  `run_inst_seq [mk_inst ci ADD [Var cv;Lit 1w] [nc]] qe = OK qf` by
    (qpat_x_assum `qe = istore _ _ _` kall_tac >>
     simp[Abbr `qf`, run_inst_seq_def, step_inst_base_opcode_eqs,
          mk_inst_def, exec_pure2_def, eval_operand_def, word_add_n2w]) >>
  `?Gf tf.
     (!k. inst_seq_ptr D lo ctx func PG Ge te
       [mk_inst ci ADD [Var cv;Lit 1w] [nc]]
       (qe with vs_inst_idx := k) Gf tf) /\
     op_taint tf (Var nc) = {} /\ op_prov Gf (Var nc) = NONE /\
     tf.t_mem = te.t_mem /\ tf.t_stor = te.t_stor /\
     tf.t_trans = te.t_trans /\ tf.t_imm = te.t_imm /\
     (!p. p <> nc ==> FLOOKUP Gf p = FLOOKUP Ge p /\
       op_taint tf (Var p) = op_taint te (Var p)) /\
     allocas_from lo qf /\ (ctx_has_dalloca ctx ==> allocas_below_fmp qf) /\
     (!p c. p <> nc /\ ptr_covers Ge te p qe c ==> ptr_covers Gf tf p qf c)` by
    (irule (BETA_RULE (Q.INST [`P` |-> `\p:string. p <> nc`] ctor_base_add_segment)) >>
     simp[eval_operand_def, op_taint_def, op_prov_def]) >>
  qabbrev_tac `qf1 = qf with vs_inst_idx := ci - ib + 1` >>
  `eval_operand (Var nc) qf1 = SOME (n2w (j+1))` by
    simp[Abbr `qf1`, Abbr `qf`, eval_operand_def, lookup_var_def,
         update_var_def, FLOOKUP_UPDATE] >>
  `?Gg tg qg.
     run_inst_seq [mk_inst (ci+1) ASSIGN [Var nc] [cv]] qf1 = OK qg /\
     inst_seq_ptr D lo ctx func PG Gf tf
       [mk_inst (ci+1) ASSIGN [Var nc] [cv]] qf1 Gg tg /\
     qg = update_var cv (n2w (j+1)) qf1 /\ op_taint tg (Var cv) = {} /\
     tg.t_mem = tf.t_mem /\ tg.t_stor = tf.t_stor /\
     tg.t_trans = tf.t_trans /\ tg.t_imm = tf.t_imm /\
     (!p. p <> cv ==> FLOOKUP Gg p = FLOOKUP Gf p /\
       op_taint tg (Var p) = op_taint tf (Var p)) /\
     allocas_from lo qg /\ (ctx_has_dalloca ctx ==> allocas_below_fmp qg) /\
     (!p c. p <> cv /\ ptr_covers Gf tf p qf1 c ==> ptr_covers Gg tg p qg c)` by
    (irule copy_assign_segment >>
     simp[Abbr `qf1`, allocas_from_def, allocas_below_fmp_def] >>
     qpat_assum `allocas_from lo qf` mp_tac >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp qf` mp_tac >>
     simp[allocas_from_def, allocas_below_fmp_def]) >>
  `step_inst_base (mk_inst (ci+1) ASSIGN [Var nc] [cv]) qf1 = OK qg` by
    simp[step_inst_base_opcode_eqs, mk_inst_def] >>
  `Gg = step_prov PG Gf (mk_inst (ci+1) ASSIGN [Var nc] [cv]) qg` by
    (qpat_x_assum `qg = update_var _ _ _` kall_tac >>
     qpat_x_assum `inst_seq_ptr D lo ctx func PG Gf tf _ qf1 Gg tg` mp_tac >>
     simp[inst_seq_ptr_def]) >>
  `op_prov Gg (Var cv) = NONE` by
    simp[bodyPtrIfExpAssignFrameTheory.assign_result_prov] >>
  `FLOOKUP Gg cv = NONE` by
    (qpat_assum `op_prov Gg (Var cv) = NONE` mp_tac >> simp[NoAsms, op_prov_def]) >>
  `w2n (a+n2w (32*j):bytes32) = w2n a + 32*j` by
    (`32*j < dimword(:256) /\ w2n a + 32*j < dimword(:256)` by decide_tac >>
     simp[w2n_add_2]) >>
  `w2n a + 32*n <= q.vs_alloca_next` by simp[] >>
  `w2n a + 32*j + 32 <= q.vs_alloca_next /\ lo <= q.vs_alloca_next` by decide_tac >>
  `qa1.vs_alloca_next = q.vs_alloca_next /\ qd.vs_alloca_next = q.vs_alloca_next` by
    simp[Abbr `qa1`, Abbr `qd`, update_var_def] >>
  `eval_operand (Var root) qa1 = SOME a /\
   eval_operand (Var sx) qa1 = SOME (n2w (32*j))` by
    (qunabbrev_tac `qa1` >> pure_rewrite_tac [eval_op_inst_idx] >>
     conj_tac >- (pure_rewrite_tac [eval_operand_def] >> first_assum ACCEPT_TAC) >>
     first_assum ACCEPT_TAC) >>
  `step_inst_base (mk_inst (ib+1) ADD [Var root;Var sx] [sp]) qa1 =
   OK (update_var sp (a+n2w (32*j)) qa1)` by
    (qpat_x_assum `qa = update_var _ _ _` kall_tac >>
     qpat_assum `eval_operand (Var root) qa1 = SOME a`
       (assume_tac o REWRITE_RULE [eval_operand_def, lookup_var_def]) >>
     qpat_assum `eval_operand (Var sx) qa1 = SOME (n2w (32*j))`
       (assume_tac o REWRITE_RULE [eval_operand_def, lookup_var_def]) >>
     simp[step_inst_base_opcode_eqs, exec_pure2_def, mk_inst_def,
          eval_operand_def, lookup_var_def]) >>
  `run_inst_seq_mem_ok [mk_inst (ib+1) ADD [Var root;Var sx] [sp];
      mk_inst ((ib+1)+1) MLOAD [Var sp] [value]] qa1` by
    (simp[fragExecMemTheory.run_inst_seq_mem_ok_cons, fragExecMemTheory.run_inst_seq_mem_ok_last,
          instMemFrontierTheory.below_frontier_MLOAD, instMemFrontierTheory.below_frontier_no_ranges,
          memSafeRunTheory.inst_dload_in_section_def, mk_inst_def] >>
     simp[eval_operand_def, lookup_var_update_var, update_var_def]) >>
  `w2n (b+n2w (32*j):bytes32) + 32 <= qd.vs_alloca_next` by decide_tac >>
  qabbrev_tac `stores = case imm of
       NONE => [mk_inst (ib+5) ISTORE [Var dp;Var value] []]
     | SOME region => [mk_inst (ib+5) ADD [region;Var dp] [ip];
                        mk_inst (ib+5+1) ISTORE [Var ip;Var value] []]` >>
  `run_inst_seq_mem_ok stores qd` by
    (Cases_on `imm`
     >- (simp[Abbr `stores`, fragExecMemTheory.run_inst_seq_mem_ok_last,
              instMemFrontierTheory.below_frontier_ISTORE] >>
         simp[memSafeRunTheory.inst_dload_in_section_def, mk_inst_def]) >>
     rename1 `(case SOME region of NONE => T | SOME opn => copy_old_operand sm opn)` >>
     `eval_operand region qd = SOME 0w` by fs[] >>
     `step_inst_base (mk_inst (ib+5) ADD [region;Var dp] [ip]) qd =
       OK (update_var ip (b+n2w (32*j)) qd)` by
       simp[step_inst_base_opcode_eqs, exec_pure2_def, mk_inst_def, WORD_ADD_0] >>
     simp[Abbr `stores`, fragExecMemTheory.run_inst_seq_mem_ok_cons,
          fragExecMemTheory.run_inst_seq_mem_ok_last,
          instMemFrontierTheory.below_frontier_ISTORE] >>
     simp[instMemFrontierTheory.below_frontier_no_ranges,
          memSafeRunTheory.inst_dload_in_section_def, mk_inst_def,
          eval_operand_def, lookup_var_update_var, update_var_def]) >>
  qabbrev_tac `m1 = [mk_inst ib MUL [Var cv;Lit 32w] [sx]]` >>
  qabbrev_tac `ld = [mk_inst (ib+1) ADD [Var root;Var sx] [sp];
                      mk_inst (ib+1+1) MLOAD [Var sp] [value]]` >>
  qabbrev_tac `m2 = [mk_inst (ib+3) MUL [Var cv;Lit 32w] [dx]]` >>
  qabbrev_tac `ad = [mk_inst (ib+4) ADD [dst;Var dx] [dp]]` >>
  `inst_seq_ptr D lo ctx func PG G tn m1 q Ga ta` by
    (`q with vs_inst_idx := q.vs_inst_idx = q` by
       simp[venom_state_component_equality] >>
     pop_assum (fn eq =>
       qpat_assum `!k. inst_seq_ptr _ _ _ _ _ G tn m1 _ Ga ta`
         (qspec_then `q.vs_inst_idx` (ACCEPT_TAC o REWRITE_RULE [eq])))) >>
  `qa.vs_inst_idx = 0` by simp[update_var_def] >>
  `(qa with vs_inst_idx := q.vs_inst_idx + LENGTH m1) = qa1` by
    simp[Abbr `qa1`, Abbr `m1`] >>
  `run_inst_seq (m1 ++ ld) q = OK (qb with vs_inst_idx := 0)` by
    (qpat_assum `run_inst_seq m1 q = _`
       (mp_then (Pat `run_inst_seq _ _ = _`) mp_tac
          logInstSeqPtrTheory.run_inst_seq_append_advanced) >>
     disch_then (qspecl_then [`ld`, `qb`] mp_tac) >>
     impl_tac
     >- (conj_tac >- simp[Abbr `ld`, mk_inst_def, is_terminator_def] >>
         qpat_assum `(qa with vs_inst_idx := q.vs_inst_idx + LENGTH m1) = qa1`
           SUBST1_TAC >>
         qpat_assum `run_inst_seq ld qa1 = OK qb` ACCEPT_TAC) >>
     simp[]) >>
  `inst_seq_ptr D lo ctx func PG G tn (m1 ++ ld) q Gb tb` by
    (irule inst_seq_ptr_append_ok >>
     conj_tac >- simp[Abbr `m1`, mk_inst_def, is_terminator_def] >>
     qexistsl [`Ga`,`qa`,`ta`] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `(qa with vs_inst_idx := q.vs_inst_idx + LENGTH m1) = qa1`
       SUBST1_TAC >>
     qpat_assum `inst_seq_ptr _ _ _ _ _ Ga ta ld qa1 _ _` ACCEPT_TAC) >>
  qabbrev_tac `p3 = m1 ++ ld` >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) p3 /\
   EVERY (\i. ~is_terminator i.inst_opcode) m2` by
    simp[Abbr `p3`, Abbr `m1`, Abbr `ld`, Abbr `m2`, mk_inst_def, is_terminator_def] >>
  `run_inst_seq m2 ((qb with vs_inst_idx := 0) with
       vs_inst_idx := q.vs_inst_idx + LENGTH p3) = OK (qc with vs_inst_idx := 3) /\
   inst_seq_ptr D lo ctx func PG Gb tb m2 ((qb with vs_inst_idx := 0) with
       vs_inst_idx := q.vs_inst_idx + LENGTH p3) Gc tc` by
    (`q.vs_inst_idx + LENGTH p3 = 3` by simp[Abbr `p3`, Abbr `m1`, Abbr `ld`] >>
     qpat_assum `q.vs_inst_idx + LENGTH p3 = 3` SUBST1_TAC >>
     conj_tac
     >- simp[run_inst_seq_inst_idx, exec_result_map_def] >>
     qpat_assum `!k. inst_seq_ptr _ _ _ _ _ Gb tb m2 _ Gc tc`
       (qspec_then `3` mp_tac) >> simp[NoAsms]) >>
  `run_inst_seq (p3 ++ m2) q = OK (qc with vs_inst_idx := 0) /\
   inst_seq_ptr D lo ctx func PG G tn (p3 ++ m2) q Gc tc` by
    ((qpat_assum `run_inst_seq p3 q = _`
       (mp_then (Pat `run_inst_seq xs s = OK t`) mp_tac logInstSeqPtrTheory.successful_seq_ptr_append) >>
     disch_then (drule_at (Pat `run_inst_seq ys _ = OK u`) o SPEC_ALL) >>
     disch_then (drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ p3 _ _ _`) o SPEC_ALL) >>
     simp[] >> (metis_tac[logInstSeqPtrTheory.successful_seq_ptr_append]))) >>
  (* Join the checked segments, advancing only the instruction cursor at each cut. *)
  `!xs ys u v H tm K tk.
      EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) xs /\
      EVERY (\i. ~is_terminator i.inst_opcode) ys /\
      run_inst_seq xs q = OK (u with vs_inst_idx := q.vs_inst_idx) /\
      inst_seq_ptr D lo ctx func PG G tn xs q H tm /\
      run_inst_seq ys u = OK v /\
      inst_seq_ptr D lo ctx func PG H tm ys
        (u with vs_inst_idx := q.vs_inst_idx + LENGTH xs) K tk ==>
      run_inst_seq (xs ++ ys) q = OK (v with vs_inst_idx := q.vs_inst_idx) /\
      inst_seq_ptr D lo ctx func PG G tn (xs ++ ys) q K tk` by
    ((POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac
     >- (`run_inst_seq ys ((u with vs_inst_idx := q.vs_inst_idx) with
               vs_inst_idx := q.vs_inst_idx + LENGTH xs) =
             OK (v with vs_inst_idx := q.vs_inst_idx + LENGTH xs)` by
           simp[run_inst_seq_inst_idx, exec_result_map_def] >>
         drule_all logInstSeqPtrTheory.run_inst_seq_append_advanced >> simp[]) >>
     irule inst_seq_ptr_append_ok >>
     conj_tac >- fs[EVERY_MEM] >>
     qexistsl [`H`,`u with vs_inst_idx := q.vs_inst_idx`,`tm`] >> simp[] >> (gvs[run_inst_seq_inst_idx, exec_result_map_def, EVERY_MEM, logInstSeqPtrTheory.run_inst_seq_append_advanced, inst_seq_ptr_append_ok]))) >>
  qabbrev_tac `p4 = p3 ++ m2` >>
  `q.vs_inst_idx + LENGTH p4 = 4` by simp[Abbr `p4`, Abbr `p3`, Abbr `m1`, Abbr `ld`, Abbr `m2`] >>
  `inst_seq_ptr D lo ctx func PG Gc tc ad
      (qc with vs_inst_idx := q.vs_inst_idx + LENGTH p4) Gd td` by
    (qpat_assum `q.vs_inst_idx + LENGTH p4 = 4` SUBST1_TAC >>
     qpat_assum `!k. inst_seq_ptr _ _ _ _ _ Gc tc ad _ Gd td`
       (qspec_then `4` ACCEPT_TAC)) >>
  `run_inst_seq (p4 ++ ad) q = OK (qd with vs_inst_idx := 0) /\
   inst_seq_ptr D lo ctx func PG G tn (p4 ++ ad) q Gd td` by
    (qpat_assum `!xs ys u v H tm K tk. _ ==> _` (qspecl_then [`p4`,`ad`,`qc`,`qd`] mp_tac) >>
     disch_then (drule_at (Pat `inst_seq_ptr _ _ _ _ _ G tn p4 _ _ _`) o SPEC_ALL) >>
     disch_then (drule_at (Pat `inst_seq_ptr _ _ _ _ _ Gc tc ad _ _ _`) o SPEC_ALL) >>
     simp[] >>
     simp[Abbr `p4`, Abbr `p3`, Abbr `m1`, Abbr `ld`, Abbr `m2`, Abbr `ad`, mk_inst_def, is_terminator_def]) >>
  qabbrev_tac `p5 = p4 ++ ad` >>
  `q.vs_inst_idx + LENGTH p5 = 5` by
    simp[Abbr `p5`, Abbr `p4`, Abbr `p3`, Abbr `m1`, Abbr `ld`, Abbr `m2`, Abbr `ad`] >>
  `inst_seq_ptr D lo ctx func PG Gd td stores
     (qd with vs_inst_idx := q.vs_inst_idx + LENGTH p5) Ge te` by
    (qpat_assum `q.vs_inst_idx + LENGTH p5 = 5` SUBST1_TAC >>
     qpat_assum `!k. inst_seq_ptr _ _ _ _ _ Gd td stores _ Ge te`
       (qspec_then `5` ACCEPT_TAC)) >>
  `run_inst_seq (p5 ++ stores) q = OK (qe with vs_inst_idx := 0) /\
   inst_seq_ptr D lo ctx func PG G tn (p5 ++ stores) q Ge te` by
    (qpat_assum `!xs ys u v H tm K tk. _ ==> _` (qspecl_then [`p5`,`stores`,`qd`,`qe`] mp_tac) >>
     disch_then (drule_at (Pat `inst_seq_ptr _ _ _ _ _ G tn p5 _ _ _`) o SPEC_ALL) >>
     disch_then (drule_at (Pat `inst_seq_ptr _ _ _ _ _ Gd td stores _ _ _`) o SPEC_ALL) >>
     simp[] >>
     Cases_on `imm` >>
     simp[Abbr `p5`, Abbr `p4`, Abbr `p3`, Abbr `m1`, Abbr `ld`, Abbr `m2`,
          Abbr `ad`, Abbr `stores`, mk_inst_def, is_terminator_def]) >>
  qabbrev_tac `pS = p5 ++ stores` >>
  qabbrev_tac `inc = [mk_inst ci ADD [Var cv;Lit 1w] [nc]]` >>
  qabbrev_tac `setc = [mk_inst (ci+1) ASSIGN [Var nc] [cv]]` >>
  `q.vs_inst_idx + LENGTH pS = ci - ib` by
    (Cases_on `imm` >>
     simp[Abbr `pS`, Abbr `p5`, Abbr `p4`, Abbr `p3`, Abbr `m1`, Abbr `ld`,
          Abbr `m2`, Abbr `ad`, Abbr `stores`, Abbr `ci`]) >>
  `inst_seq_ptr D lo ctx func PG Ge te inc
     (qe with vs_inst_idx := q.vs_inst_idx + LENGTH pS) Gf tf` by
    (qpat_assum `!k. inst_seq_ptr _ _ _ _ _ Ge te inc _ Gf tf`
       (qspec_then `q.vs_inst_idx + LENGTH pS` ACCEPT_TAC)) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) pS` by
    (Cases_on `imm` >>
     simp[NoAsms, Abbr `pS`, Abbr `p5`, Abbr `p4`, Abbr `p3`, Abbr `m1`, Abbr `ld`,
          Abbr `m2`, Abbr `ad`, Abbr `stores`, mk_inst_def, is_terminator_def]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) inc` by
    simp[NoAsms, Abbr `inc`, mk_inst_def, is_terminator_def] >>
  `run_inst_seq (pS ++ inc) q = OK (qf with vs_inst_idx := 0) /\
   inst_seq_ptr D lo ctx func PG G tn (pS ++ inc) q Gf tf` by
    (qpat_assum `!xs ys u v H tm K tk. _ ==> _` (qspecl_then [`pS`,`inc`,`qe`,`qf`] mp_tac) >>
     disch_then (drule_at (Pat `inst_seq_ptr _ _ _ _ _ G tn pS _ _ _`) o SPEC_ALL) >>
     disch_then (drule_at (Pat `inst_seq_ptr _ _ _ _ _ Ge te inc _ _ _`) o SPEC_ALL) >>
     simp[]) >>
  qabbrev_tac `pI = pS ++ inc` >>
  `((qf with vs_inst_idx := 0) with vs_inst_idx := q.vs_inst_idx + LENGTH pI) = qf1` by
    (Cases_on `imm` >>
     simp[Abbr `pI`, Abbr `pS`, Abbr `p5`, Abbr `p4`, Abbr `p3`, Abbr `m1`, Abbr `ld`,
          Abbr `m2`, Abbr `ad`, Abbr `stores`, Abbr `inc`, Abbr `ci`, Abbr `qf1`]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) pI /\
   EVERY (\i. ~is_terminator i.inst_opcode) setc` by
    simp[Abbr `pI`, EVERY_APPEND, Abbr `inc`, Abbr `setc`, mk_inst_def, is_terminator_def] >>
  `run_inst_seq (pI ++ setc) q = OK (qg with vs_inst_idx := 0) /\
   inst_seq_ptr D lo ctx func PG G tn (pI ++ setc) q Gg tg` by
    (conj_tac
     >- (qpat_assum `run_inst_seq pI q = _`
          (mp_then (Pat `run_inst_seq _ _ = _`) mp_tac
             logInstSeqPtrTheory.run_inst_seq_append_advanced) >>
         disch_then (qspecl_then [`setc`, `qg`] mp_tac) >>
         impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >>
                      qpat_assum `(_ with vs_inst_idx := _) = qf1` SUBST1_TAC >> simp[]) >>
         simp[]) >>
     irule inst_seq_ptr_append_ok >>
     conj_tac >- (qpat_assum `EVERY _ pI` mp_tac >> simp[NoAsms, EVERY_MEM]) >>
     qexistsl [`Gf`, `qf with vs_inst_idx := 0`, `tf`] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `(_ with vs_inst_idx := _) = qf1` SUBST1_TAC >>
     first_assum ACCEPT_TAC) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) ld /\
   EVERY (\i. ~is_terminator i.inst_opcode) stores` by
    (Cases_on `imm` >> simp[Abbr `ld`, Abbr `stores`, mk_inst_def, is_terminator_def]) >>
  `run_inst_seq_mem_ok p3 q` by
    ((simp[Abbr `p3`] >> MATCH_MP_TAC fragExecMemTheory.run_inst_seq_mem_ok_append >>
     conj_tac
     >- simp[Abbr `m1`, fragExecMemTheory.run_inst_seq_mem_ok_last,
            instMemFrontierTheory.below_frontier_no_ranges,
            memSafeRunTheory.inst_dload_in_section_def, mk_inst_def] >>
     qpat_assum `run_inst_seq_mem_ok ld qa1` mp_tac >>
     simp[Abbr `qa1`, fragExecMemTheory.run_inst_seq_mem_ok_inst_idx] >> (metis_tac[Abbr `p3`, Abbr `m1`, fragExecMemTheory.run_inst_seq_mem_ok_last, instMemFrontierTheory.below_frontier_no_ranges, memSafeRunTheory.inst_dload_in_section_def, mk_inst_def, Abbr `qa1`, fragExecMemTheory.run_inst_seq_mem_ok_inst_idx, fragExecMemTheory.run_inst_seq_mem_ok_append]))) >>
  `!s. run_inst_seq_mem_ok m2 s /\ run_inst_seq_mem_ok ad s /\
        run_inst_seq_mem_ok inc s /\ run_inst_seq_mem_ok setc s` by
    simp[Abbr `m2`, Abbr `ad`, Abbr `inc`, Abbr `setc`,
         fragExecMemTheory.run_inst_seq_mem_ok_last,
         instMemFrontierTheory.below_frontier_no_ranges,
         memSafeRunTheory.inst_dload_in_section_def, mk_inst_def] >>
  `!xs ys. run_inst_seq_mem_ok xs q /\ (!s. run_inst_seq_mem_ok ys s) ==>
           run_inst_seq_mem_ok (xs ++ ys) q` by
    (rpt strip_tac >> MATCH_MP_TAC fragExecMemTheory.run_inst_seq_mem_ok_append >>
     simp[]) >>
  `run_inst_seq_mem_ok p4 q` by
    (simp[Abbr `p4`] >> first_assum match_mp_tac >> simp[]) >>
  `run_inst_seq_mem_ok p5 q` by
    (simp[Abbr `p5`] >> first_assum match_mp_tac >> simp[]) >>
  `run_inst_seq_mem_ok pS q` by
    (simp[Abbr `pS`] >> MATCH_MP_TAC fragExecMemTheory.run_inst_seq_mem_ok_append >>
     simp[fragExecMemTheory.run_inst_seq_mem_ok_inst_idx]) >>
  `run_inst_seq_mem_ok pI q` by
    (simp[Abbr `pI`] >> first_assum match_mp_tac >> simp[]) >>
  `run_inst_seq_mem_ok (pI ++ setc) q` by
    (first_assum match_mp_tac >> simp[]) >>
  qabbrev_tac `code = pI ++ setc` >>
  `isPREFIX (code ++ [mk_inst (ci+2) JMP [Label hdr] []]) bbB.bb_instructions` by
    (qpat_assum `isPREFIX (_ ++ (case imm of NONE => _ | SOME _ => _)) _` mp_tac >>
     Cases_on `imm` >>
     simp[Abbr `code`, Abbr `pI`, Abbr `pS`, Abbr `p5`, Abbr `p4`, Abbr `p3`,
          Abbr `m1`, Abbr `ld`, Abbr `m2`, Abbr `ad`, Abbr `stores`, Abbr `inc`,
          Abbr `setc`, Abbr `ci`, GSYM ADD_ASSOC] >> gvs[]) >>
  `isPREFIX code bbB.bb_instructions /\
   get_instruction bbB (LENGTH code) = SOME (mk_inst (ci+2) JMP [Label hdr] [])` by
    (qpat_assum `isPREFIX (code ++ _) _`
       (strip_assume_tac o REWRITE_RULE [rich_listTheory.IS_PREFIX_APPEND, GSYM APPEND_ASSOC, APPEND]) >>
     simp[rich_listTheory.IS_PREFIX_APPEND, get_instruction_def, EL_APPEND_EQN]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
   EVERY (\i. i.inst_opcode <> DALLOCA) code /\
   FILTER (\i. i.inst_opcode = GAS) code = []` by
    (Cases_on `imm` >>
     simp[Abbr `code`, Abbr `pI`, Abbr `pS`, Abbr `p5`, Abbr `p4`, Abbr `p3`,
          Abbr `m1`, Abbr `ld`, Abbr `m2`, Abbr `ad`, Abbr `stores`, Abbr `inc`,
          Abbr `setc`, mk_inst_def, is_terminator_def]) >>
  qabbrev_tac `endp = qg with vs_inst_idx := LENGTH code` >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (q,G,tn) [] (OK endp,Gg,tg)` by
    (qpat_assum `run_inst_seq code q = _`
       (mp_then (Pat `run_inst_seq _ _ = _`) mp_tac fragGasSeqPtrTheory.run_inst_seq_gas_origin_ptr_path) >>
     disch_then (drule_at (Pat `inst_seq_ptr _ _ _ _ _ G tn code q _ _`) o SPEC_ALL) >>
     disch_then (qspecl_then [`explicit`,`bbB`] mp_tac) >>
     simp[Abbr `endp`] >>
     (impl_tac >-
       (strip_tac >> rpt gen_tac >> strip_tac >>
        irule dalloca_no_wrap_non_dalloca >>
        qpat_x_assum `EVERY (\i. i.inst_opcode <> DALLOCA) code` mp_tac >>
        simp[EVERY_MEM])) >>
     simp[]) >>
  `qe.vs_current_bb = loop_body /\ ~qe.vs_halted /\
   qe.vs_allocas = q.vs_allocas /\ qe.vs_alloca_next = q.vs_alloca_next /\
   qe.vs_fmp = q.vs_fmp /\ qe.vs_initial_fmp = q.vs_initial_fmp /\
   qe.vs_labels = q.vs_labels` by
    (qpat_x_assum `qe = istore _ _ _` mp_tac >> Cases_on `imm` >>
     simp[NoAsms] >> disch_then SUBST1_TAC >>
     qunabbrev_tac `qd` >> qunabbrev_tac `qa1` >>
     qpat_assum `qc = update_var _ _ _` SUBST1_TAC >>
     qpat_assum `qb = update_var _ _ _` SUBST1_TAC >>
     qpat_assum `qa = update_var _ _ _` SUBST1_TAC >>
     simp[NoAsms, update_var_def, istore_def, mstore_def] >>
     simp[]) >>
  `endp.vs_current_bb = loop_body /\ ~endp.vs_halted` by
    simp[IgnAsm `qe = istore _ _ _`, Abbr `endp`, Abbr `qf1`, Abbr `qf`, update_var_def] >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (endp,Gg,tg) []
     (OK (jump_to hdr endp),Gg,tg)` by
    (irule fragGasOriginPtrLoopTheory.jmp_origin_ptr_path >>
     `endp.vs_inst_idx = LENGTH code` by simp[Abbr `endp`] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (qexistsl [`bbB`,`ci+2`] >> simp[]) >>
     qpat_assum `allocas_from lo qg` mp_tac >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp qg` mp_tac >>
     simp[Abbr `endp`, allocas_from_def, allocas_below_fmp_def]) >>
  qabbrev_tac `r = jump_to hdr endp` >>
  qexistsl [`r`,`Gg`,`tg`] >>
  conj_tac >- (irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
               qexistsl [`Gg`,`endp`,`tg`] >> simp[]) >>
  `(r with <|vs_vars := s0.vs_vars; vs_current_bb := s0.vs_current_bb;
             vs_prev_bb := s0.vs_prev_bb; vs_inst_idx := s0.vs_inst_idx|>) =
   immutable_transfers T T a b (j+1) 0 s0` by
    (`(r with <|vs_vars := s0.vs_vars; vs_current_bb := s0.vs_current_bb;
                vs_prev_bb := s0.vs_prev_bb; vs_inst_idx := s0.vs_inst_idx|>) =
       qe with <|vs_vars := s0.vs_vars; vs_current_bb := s0.vs_current_bb;
                 vs_prev_bb := s0.vs_prev_bb; vs_inst_idx := s0.vs_inst_idx|>` by
       simp[IgnAsm `qe = istore _ _ _`, Abbr `r`, Abbr `endp`, Abbr `qf1`,
            Abbr `qf`, jump_to_def, update_var_def] >>
     pop_assum SUBST1_TAC >>
     qpat_x_assum `_ = immutable_transfers T T a b j 0 s0` (fn th =>
       rewrite_tac[GSYM ADD1, immutable_transfers_snoc, GSYM th,
                   immutable_word_transfer_def, immutable_copy_read_def]) >>
     qpat_x_assum `qe = istore _ _ _` mp_tac >> Cases_on `imm` >>
     simp[NoAsms] >> disch_then SUBST1_TAC >>
     qunabbrev_tac `qd` >> qunabbrev_tac `qa1` >>
     qpat_assum `qc = update_var _ _ _` SUBST1_TAC >>
     qpat_assum `qb = update_var _ _ _` SUBST1_TAC >>
     qpat_assum `qa = update_var _ _ _` SUBST1_TAC >>
     simp[NoAsms, update_var_def, istore_def, mstore_def, mload_def]) >>
  `r.vs_vars = qg.vs_vars /\ r.vs_labels = qg.vs_labels /\
   r.vs_allocas = qg.vs_allocas /\ r.vs_alloca_next = qg.vs_alloca_next /\
   r.vs_fmp = qg.vs_fmp /\ r.vs_initial_fmp = qg.vs_initial_fmp /\
   r.vs_halted = qg.vs_halted /\ r.vs_current_bb = hdr /\
   r.vs_inst_idx = 0` by
    simp[NoAsms, Abbr `r`, Abbr `endp`, jump_to_def] >>
  `r.vs_labels = q.vs_labels /\ r.vs_allocas = q.vs_allocas /\
   r.vs_alloca_next = q.vs_alloca_next /\ r.vs_fmp = q.vs_fmp /\
   r.vs_initial_fmp = q.vs_initial_fmp /\ ~r.vs_halted` by
    simp[IgnAsm `qe = istore _ _ _`, Abbr `qf1`, Abbr `qf`, update_var_def] >>
  `allocas_from lo r /\ (ctx_has_dalloca ctx ==> allocas_below_fmp r)` by
    (qpat_assum `r.vs_allocas = qg.vs_allocas` (fn alloc =>
     qpat_assum `r.vs_fmp = qg.vs_fmp` (fn fmp =>
     qpat_assum `r.vs_initial_fmp = qg.vs_initial_fmp` (fn init =>
       pure_rewrite_tac [allocas_from_def, allocas_below_fmp_def,
                         alloc, fmp, init]))) >>
     conj_tac
     >- qpat_assum `allocas_from lo qg`
          (ACCEPT_TAC o REWRITE_RULE [allocas_from_def]) >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp qg`
       (ACCEPT_TAC o REWRITE_RULE [allocas_below_fmp_def])) >>
  `lookup_var cv r = SOME (n2w (j+1))` by
    simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `!x. not_fresh_at sm x ==> imm = NONE \/ x <> ip` by
    (gen_tac >> disch_tac >> Cases_on `imm` >- simp[] >>
     `~not_fresh_at sm ip` by
       (qpat_assum `!x. MEM x (_ ++ _) ==> ~not_fresh_at sm x`
          (qspec_then `ip` mp_tac) >> simp[MEM_APPEND]) >>
     simp[] >>
     qpat_assum `not_fresh_at sm x` mp_tac >>
     qpat_assum `~not_fresh_at sm ip` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `!x. not_fresh_at sm x ==>
     lookup_var x r = lookup_var x q /\ FLOOKUP Gg x = FLOOKUP G x /\
     op_taint tg (Var x) = op_taint tn (Var x)` by
    (gen_tac >> disch_tac >>
     `x <> dp /\ x <> nc /\ x <> cv` by metis_tac[] >>
     qpat_assum `!x. not_fresh_at sm x ==> lookup_var x qd = _ /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!x. not_fresh_at sm x ==> imm = NONE \/ x <> ip`
       (qspec_then `x` (fn guard =>
         qpat_assum `not_fresh_at sm x` (fn old =>
           qpat_assum `!p. imm = NONE \/ p <> ip ==> _`
             (qspec_then `x` (fn frame =>
               map_every assume_tac (CONJUNCTS (MP frame (MP guard old)))))))) >>
     qpat_assum `!p. p <> nc ==> FLOOKUP Gf p = _ /\ _`
       (qspec_then `x` (fn frame =>
         qpat_assum `x <> nc` (map_every assume_tac o CONJUNCTS o MP frame))) >>
     qpat_assum `!p. p <> cv ==> FLOOKUP Gg p = _ /\ _`
       (qspec_then `x` (fn frame =>
         qpat_assum `x <> cv` (map_every assume_tac o CONJUNCTS o MP frame))) >>
     `lookup_var x qg = lookup_var x qe` by
       simp[IgnAsm `qe = istore _ _ _`, Abbr `qf1`, Abbr `qf`,
            lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     `lookup_var x qe = lookup_var x qd` by
       (Cases_on `imm`
        >- (qpat_assum `qe = istore _ _ _` mp_tac >> simp[NoAsms] >>
            disch_then SUBST1_TAC >>
            simp[NoAsms, lookup_var_def, istore_def, mstore_def]) >>
        `ip <> x` by
          (qpat_assum `!x. not_fresh_at sm x ==> _ \/ x <> ip`
             (qspec_then `x` (fn guard =>
               qpat_assum `not_fresh_at sm x` (mp_tac o MP guard))) >>
           POP_ASSUM_LIST (K ALL_TAC) >>
           simp[optionTheory.NOT_SOME_NONE, EQ_SYM_EQ]) >>
        qpat_assum `qe = istore _ _ _` mp_tac >> simp[NoAsms] >>
        disch_then SUBST1_TAC >>
        qpat_assum `ip <> x` (fn distinct =>
          simp[NoAsms, lookup_var_def, istore_def, mstore_def, update_var_def,
               FLOOKUP_UPDATE, distinct])) >>
     `lookup_var x r = lookup_var x qg` by
       qpat_assum `r.vs_vars = qg.vs_vars` (fn vars =>
         simp[NoAsms, lookup_var_def, vars]) >>
     simp[]) >>
  `!arg. copy_old_operand sm arg ==>
      eval_operand arg r = eval_operand arg q /\
      op_taint tg arg = op_taint tn arg /\ op_prov Gg arg = op_prov G arg` by
    (gen_tac >> disch_tac >> irule body_assign_immutable_loop_old_operand >>
     conj_tac >- first_assum ACCEPT_TAC >> qexists_tac `sm` >>
     conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC) >>
  `copy_old_operand sm (Var root)` by
    qpat_assum `src = Var root` (fn src_eq =>
      qpat_assum `copy_old_operand sm src`
        (ACCEPT_TAC o REWRITE_RULE [src_eq])) >>
  `ptr_covers Gg tg root r (32*n)` by
    (qpat_assum `ptr_covers G tn root q (32*n)`
       (strip_assume_tac o REWRITE_RULE[ptr_covers_def]) >>
     `not_fresh_at sm root` by fs[copy_old_operand_def] >>
     qpat_assum `!x. not_fresh_at sm x ==> lookup_var x r = _ /\ _`
       (drule_then strip_assume_tac) >>
     simp[ptr_covers_def] >> metis_tac[]) >>
  `!x. not_fresh_at sm x ==>
      lookup_var x r = lookup_var x s0 /\ FLOOKUP Gg x = FLOOKUP G0 x /\
      op_taint tg (Var x) = op_taint tn0 (Var x)` by
    (rpt strip_tac >>
     qpat_assum `!x. not_fresh_at sm x ==> lookup_var x r = _ /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!x. not_fresh_at sm x ==> lookup_var x q = _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `op_taint td (Var value) = mem_word_taint tn.t_mem (w2n a + 32*j)` by
    (`value <> dx /\ value <> dp` by fs[ALL_DISTINCT] >>
     qpat_assum `!p. p <> dp ==> FLOOKUP Gd p = _ /\ _`
       (qspec_then `value` mp_tac) >>
     qpat_assum `!p. p <> dx ==> FLOOKUP Gc p = _ /\ _`
       (qspec_then `value` mp_tac) >> simp[]) >>
  `mem_word_taint tn.t_mem (w2n a + 32*j) =
     mem_word_taint tn0.t_mem (w2n a + 32*j)` by
    (simp[mem_word_taint_def, pred_setTheory.EXTENSION] >> gen_tac >> strip_tac >>
     qpat_assum `!i. ~(w2n b <= i /\ i < w2n b + 32*j) ==> _` irule >>
     decide_tac) >>
  qabbrev_tac `start = w2n b + 32*j` >>
  qabbrev_tac `src_at = w2n a + 32*j` >>
  `tg.t_mem = (tn.t_mem DIFF {i | start <= i /\ i < start+32}) UNION
               {start+k | k IN mem_word_taint tn0.t_mem src_at}` by
    simp[Abbr `start`, Abbr `src_at`] >>
  `!i. i IN tg.t_mem <=>
      if start <= i /\ i < start+32 then src_at + (i-start) IN tn0.t_mem
      else i IN tn.t_mem` by
    (gen_tac >>
     qpat_assum `tg.t_mem = (tn.t_mem DIFF _) UNION _` SUBST1_TAC >>
     Cases_on `start <= i /\ i < start+32`
     >- (simp[mem_word_taint_def] >> eq_tac >> strip_tac
         >- (rename1 `i = k + start` >>
             `i + src_at - start = k + src_at` by decide_tac >> simp[]) >>
         qexists_tac `i-start` >> simp[] >> decide_tac) >>
     simp[mem_word_taint_def] >> eq_tac
     >- (strip_tac >> decide_tac) >>
     simp[]) >>
  `!k. k < 32*(j+1) ==>
       (w2n b + k IN tg.t_mem <=> w2n a + k IN tn0.t_mem)` by
    (rpt strip_tac >>
     qpat_assum `!i. i IN tg.t_mem <=> _` (qspec_then `w2n b+k` SUBST1_TAC) >>
     Cases_on `k < 32*j`
     >- (`~(start <= w2n b+k)` by (simp[Abbr `start`] >> decide_tac) >>
         simp[]) >>
     `start <= w2n b+k /\ w2n b+k < start+32` by
       (simp[Abbr `start`] >> decide_tac) >>
     `src_at + (w2n b+k-start) = w2n a+k` by
       (simp[Abbr `start`, Abbr `src_at`] >> decide_tac) >> simp[]) >>
  `!i. ~(w2n b <= i /\ i < w2n b+32*(j+1)) ==>
      (i IN tg.t_mem <=> i IN tn0.t_mem)` by
    (gen_tac >> disch_tac >>
     `~(start <= i /\ i < start+32) /\ ~(w2n b <= i /\ i < start)` by
       (simp[Abbr `start`] >> decide_tac) >>
     qpat_assum `!i. i IN tg.t_mem <=> _` (qspec_then `i` SUBST1_TAC) >>
     qpat_assum `~(start <= i /\ i < start+32)` (fn outside =>
       simp[NoAsms, outside]) >>
     qpat_assum `!k. ~(w2n b <= k /\ k < start) ==> _`
       (qspec_then `i` (fn frame =>
         qpat_assum `~(w2n b <= i /\ i < start)` (ACCEPT_TAC o MP frame)))) >>
  `j+1 <= n` by decide_tac >>
  qpat_x_assum `Gg = step_prov _ _ _ _` kall_tac >>
  Cases_on `imm` >> simp[] >>
  rename1 `eval_operand region r = SOME 0w /\ _` >>
  qpat_assum `case SOME region of NONE => T | SOME arg => copy_old_operand sm arg`
    (assume_tac o SIMP_RULE (srw_ss()) []) >>
  qpat_assum `!arg. copy_old_operand sm arg ==> _`
    (qspec_then `region` (fn frame =>
      qpat_assum `copy_old_operand sm region` (strip_assume_tac o MP frame))) >>
  qpat_assum `case SOME region of NONE => T | SOME arg => eval_operand arg q = SOME 0w /\ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
  simp[]
QED

(* All three transitions take this same concrete loop and entry context. *)
fun immutable_bytes_loop_transition th =
  qspecl_then [`sm`,`src`,`dst`,`cnt`,`imm`,`a`,`b`,`n`,`lo`,`ctx`,
    `cv`,`s0`,`G0`,`tn0`,`D`,`explicit`,`func`,`PG`,`hdr`,`loop_body`,
    `exit`,`ie`,`ih`,`ib`,`test`,`sx`,`sp`,`value`,`dx`,`dp`,`ip`,`nc`,
    `bbE`,`bbH`,`bbB`] mp_tac th >>
  (impl_tac >- asm_rewrite_tac[]);

Theorem body_assign_immutable_bytes_loop_actual:
  !sm src dst cnt imm a b n lo ctx s0 G0 tn0 D explicit func PG u sb.
  compile_word_copy_loop_base src dst cnt LocMemory LocCode T imm sm = (u,sb) /\
  fn_has_code sm sb func /\
  copy_old_operand sm src /\ copy_old_operand sm dst /\
  copy_old_operand sm cnt /\
  (case imm of NONE => T | SOME region => copy_old_operand sm region) /\
  eval_operand src s0 = SOME a /\ op_taint tn0 src = {} /\
  (0 < n ==> ?p. src = Var p /\ ptr_covers G0 tn0 p s0 (32*n)) /\
  eval_operand dst s0 = SOME b /\ op_taint tn0 dst = {} /\ op_prov G0 dst = NONE /\
  eval_operand cnt s0 = SOME (n2w n) /\
  op_taint tn0 cnt = {} /\ op_prov G0 cnt = NONE /\
  (case imm of NONE => T | SOME region =>
    eval_operand region s0 = SOME (0w:bytes32) /\
    op_taint tn0 region = {} /\ op_prov G0 region = NONE) /\
  n < dimword(:256) /\ lo <= w2n a /\
  w2n a + 32*n < dimword(:256) /\ w2n b + 32*n <= lo /\
  allocas_from lo s0 /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (0 < n ==> w2n a + 32*n <= s0.vs_alloca_next) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sm.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?t Gf tnf.
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s0,G0,tn0) [] (OK t,Gf,tnf) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (t with <|vs_vars := s0.vs_vars; vs_current_bb := s0.vs_current_bb;
       vs_prev_bb := s0.vs_prev_bb; vs_inst_idx := s0.vs_inst_idx|>) =
      immutable_transfers T T a b n 0 s0 /\
    (!x. not_fresh_at sm x ==>
      lookup_var x t = lookup_var x s0 /\ FLOOKUP Gf x = FLOOKUP G0 x /\
      op_taint tnf (Var x) = op_taint tn0 (Var x)) /\
    eval_operand src t = SOME a /\ op_taint tnf src = {} /\
    (0 < n ==> ?p. src = Var p /\ ptr_covers Gf tnf p t (32*n)) /\
    eval_operand dst t = SOME b /\ op_taint tnf dst = {} /\ op_prov Gf dst = NONE /\
    eval_operand cnt t = SOME (n2w n) /\
    op_taint tnf cnt = {} /\ op_prov Gf cnt = NONE /\
    (case imm of NONE => T | SOME region =>
      eval_operand region t = SOME (0w:bytes32) /\
      op_taint tnf region = {} /\ op_prov Gf region = NONE) /\
    t.vs_allocas = s0.vs_allocas /\ t.vs_alloca_next = s0.vs_alloca_next /\
    t.vs_fmp = s0.vs_fmp /\ t.vs_initial_fmp = s0.vs_initial_fmp /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!k. k < 32*n ==> (w2n b + k IN tnf.t_mem <=> w2n a + k IN tn0.t_mem)) /\
    (!i. ~(w2n b <= i /\ i < w2n b + 32*n) ==> (i IN tnf.t_mem <=> i IN tn0.t_mem)) /\
    tnf.t_stor = tn0.t_stor /\ tnf.t_trans = tn0.t_trans
Proof
  rpt gen_tac >> strip_tac >>
  drule_all body_assign_immutable_bytes_loop_shape >>
  disch_then (qx_choosel_then
    [`hdr`,`loop_body`,`exit`,`ie`,`ih`,`ib`,`cv`,`test`,`sx`,`sp`,`value`,
     `dx`,`dp`,`ip`,`nc`,`bbE`,`bbH`,`bbB`] strip_assume_tac) >>
  qabbrev_tac `Inv = \(j:num) (G:(string,num # num) fmap) (tn:taint) (q:venom_state).
    j <= n /\
    (q with <|vs_vars := s0.vs_vars; vs_current_bb := s0.vs_current_bb;
       vs_prev_bb := s0.vs_prev_bb; vs_inst_idx := s0.vs_inst_idx|>) =
      immutable_transfers T T a b j 0 s0 /\
    lookup_var cv q = SOME (n2w j) /\
    FLOOKUP G cv = NONE /\ op_taint tn (Var cv) = {} /\
    (!x. not_fresh_at sm x ==>
      lookup_var x q = lookup_var x s0 /\ FLOOKUP G x = FLOOKUP G0 x /\
      op_taint tn (Var x) = op_taint tn0 (Var x)) /\
    eval_operand src q = SOME a /\ op_taint tn src = {} /\
    (0 < n ==> ?p. src = Var p /\ ptr_covers G tn p q (32*n)) /\
    eval_operand dst q = SOME b /\ op_taint tn dst = {} /\ op_prov G dst = NONE /\
    eval_operand cnt q = SOME (n2w n) /\
    op_taint tn cnt = {} /\ op_prov G cnt = NONE /\
    (case imm of NONE => T | SOME region =>
      eval_operand region q = SOME (0w:bytes32) /\
      op_taint tn region = {} /\ op_prov G region = NONE) /\
    q.vs_allocas = s0.vs_allocas /\ q.vs_alloca_next = s0.vs_alloca_next /\
    q.vs_fmp = s0.vs_fmp /\ q.vs_initial_fmp = s0.vs_initial_fmp /\
    allocas_from lo q /\ (ctx_has_dalloca ctx ==> allocas_below_fmp q) /\
    (!k. k < 32*j ==> (w2n b + k IN tn.t_mem <=> w2n a + k IN tn0.t_mem)) /\
    (!i. ~(w2n b <= i /\ i < w2n b + 32*j) ==> (i IN tn.t_mem <=> i IN tn0.t_mem)) /\
    tn.t_stor = tn0.t_stor /\ tn.t_trans = tn0.t_trans` >>
  `?r G1 tn1.
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s0,G0,tn0) [] (OK r,G1,tn1) /\
    Inv 0 G1 tn1 r /\ ~r.vs_halted /\ r.vs_current_bb = hdr /\ r.vs_inst_idx = 0` by
    (immutable_bytes_loop_transition body_assign_immutable_bytes_loop_init_actual >>
     simp[Abbr `Inv`, GSYM CONJ_ASSOC]) >>
  qspecl_then [`Inv`,`(D,lo,explicit,ctx,func,PG)`,`n`,`hdr`,`loop_body`,`exit`,
    `n`,`0`,`G1`,`tn1`,`r`] mp_tac fragGasCopyLoopTheory.copy_loop_iterate_origin_ptr >>
  (impl_tac >-
    (conj_tac >-
       (immutable_bytes_loop_transition body_assign_immutable_bytes_loop_header_actual >>
        simp[Abbr `Inv`, GSYM CONJ_ASSOC, SF CONJ_ss]) >>
     conj_tac >-
       (immutable_bytes_loop_transition body_assign_immutable_bytes_loop_step_actual >>
        simp[Abbr `Inv`]) >>
     simp[])) >>
  disch_then (qx_choosel_then [`t`,`Gf`,`tnf`] strip_assume_tac) >>
  qpat_x_assum `Inv n Gf tnf t` mp_tac >>
  simp[Abbr `Inv`] >> strip_tac >>
  qexistsl_tac [`t`,`Gf`,`tnf`] >> simp[] >>
  conj_tac >-
    (irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     goal_assum (drule_at Any) >> simp[]) >>
  first_assum ACCEPT_TAC
QED

(* Copy the live bytestring prefix, rounded to whole words. *)
Theorem body_assign_immutable_bytes_path_copy:
  compile_store_immutable_bytestring imm (Var src) dst sa = ((),sb) /\
  fn_has_code sa sb func /\
  not_fresh_at sa src /\ copy_old_operand sa dst /\
  eval_operand dst s = SOME (n2w off) /\
  op_taint tn dst = {} /\ op_prov G dst = NONE /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  is_bytestring_type sty /\ is_bytestring_type dty /\
  type_widens_to (get_tenv cx) sty dty /\ value_has_type stv v /\
  off + type_memory_size dtv <= lo /\ lo < dimword(:256) /\
  eval_operand (Var src) s = SOME (n2w a) /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory stv v a mem) /\
  ptr_covers G tn src s (type_memory_size stv) /\
  lo <= a /\ a + type_memory_size stv < dimword(:256) /\
  (type_memory_size stv = 0 \/ a + type_memory_size stv <= s.vs_alloca_next) /\
  (!region. imm = SOME region ==>
    eval_operand region s = SOME 0w /\ op_taint tn region = {} /\
    op_prov G region = NONE) /\
  (!x. imm = SOME (Var x) ==> not_fresh_at sa x) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?len t Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tnf)) /\
    value_has_type dtv v /\
    val_footprint stv v = 32 + len /\ val_footprint dtv v = 32 + len /\
    32 + len <= 32 * (1 + word_size len) /\
    32 * (1 + word_size len) <= type_memory_size dtv /\
    (t with <|vs_vars := s.vs_vars; vs_current_bb := s.vs_current_bb;
       vs_prev_bb := s.vs_prev_bb; vs_inst_idx := s.vs_inst_idx|>) =
      immutable_transfers T T (n2w a) (n2w off) (1 + word_size len) 0 s /\
    (!k. k < 32 * (1 + word_size len) ==>
      (off + k IN tnf.t_mem <=> a + k IN tn.t_mem)) /\
    (!i. ~(off <= i /\ i < off + 32 * (1 + word_size len)) ==>
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!i. a <= i /\ i < a + 32 + len ==> i NOTIN tn.t_mem) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tnf (Var x) = op_taint tn (Var x))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `compile_bytestring_word_count (Var src) sa` >>
  rename1 `compile_bytestring_word_count (Var src) sa = (cnt,sm)` >>
  Cases_on `compile_word_copy_loop_base (Var src) (dst) cnt LocMemory LocCode T imm sm` >>
  rename1 `compile_word_copy_loop_base _ _ cnt LocMemory LocCode T _ sm = (u,sn)` >>
  `sn = sb` by
    (qpat_assum `compile_bytestring_word_count _ _ = _` (fn h =>
     qpat_assum `compile_word_copy_loop_base _ _ _ _ _ _ _ _ = _` (fn h' =>
     qpat_x_assum `compile_store_immutable_bytestring _ _ _ _ = _` mp_tac >>
     simp[NoAsms, compile_store_immutable_bytestring_def, comp_bind_def,
          comp_ignore_bind_def, comp_return_def, pairTheory.UNCURRY, h, h']))) >>
  qpat_x_assum `sn = sb` SUBST_ALL_TAC >>
  drule bytestring_word_count_shape >> strip_tac >>
  `cs_extends sa sm` by (irule cs_extends_same_block >> fs[same_blocks_def]) >>
  `ci_mono sm sb` by
    (qspecl_then [`Var src`,`dst`,`cnt`,`LocMemory`,`LocCode`,
                  `T`,`imm`,`sm`] mp_tac ci_mono_word_copy >> simp[]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (irule fn_has_code_split >> fs[ci_mono_def]) >>
  `val_in_memory stv v a s.vs_memory` by
    (qpat_assum `!mem. mem_agree_outside _ _ mem ==> _` irule >>
     simp[mem_agree_outside_def]) >>
  drule_all body_assign_immutable_bytes_source_live_clean >>
  disch_then (qx_choose_then `len` (map_every assume_tac o CONJUNCTS)) >>
  `value_has_type dtv v` by
    (drule_all place_store_bytestring_representation >>
     strip_tac >> gvs[value_has_type_def]) >>
  `32 * (1 + word_size len) <= type_memory_size stv /\
   32 * (1 + word_size len) <= type_memory_size dtv` by
    (drule_all immutable_bytestring_runtime_extent >> strip_tac >>
     `val_footprint stv v = 32 + len` suffices_by
       (strip_tac >> `len' = len` by decide_tac >> gvs[]) >>
     drule_all bytestring_type_value >> strip_tac >>
     qpat_x_assum `(?bs. _) \/ (?str. _)` strip_assume_tac >>
     gvs[val_footprint_def, value_has_type_def]) >>
  qabbrev_tac `n = 1 + word_size len` >>
  `0 < n /\ 32 + len <= 32*n` by
    (qspec_then `len` assume_tac exprSimPropsTheory.le_word_size_mul >>
     simp[Abbr `n`, arithmeticTheory.LEFT_ADD_DISTRIB] >> decide_tac) >>
  `a + 32*n <= s.vs_alloca_next /\ a + 32*n < dimword(:256) /\
   off + 32*n <= lo /\ a < dimword(:256) /\ off < dimword(:256)` by decide_tac >>
  `len + 63 < dimword(:256)` by
    (irule bytestring_word_count_no_wrap >>
     qpat_assum `a + 32*n < dimword(:256)` mp_tac >>
     qpat_assum `Abbrev (n = _)` (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     simp[IgnAsm `(?bs. _) \/ (?str. _)`, arithmeticTheory.LEFT_ADD_DISTRIB] >> decide_tac) >>
  `ptr_covers G tn src s (32*n) /\ ptr_covers G tn src s 32` by
    (conj_tac >> irule ptr_covers_mono >> qexists `type_memory_size stv` >>
     simp[] >> decide_tac) >>
  `w2n (n2w a:bytes32) = a /\ w2n (n2w off:bytes32) = off` by
    simp[w2n_n2w, arithmeticTheory.LESS_MOD] >>
  `a + 32 <= s.vs_alloca_next` by decide_tac >>
  `!i. a <= i /\ i < a + 32 ==> i NOTIN tn.t_mem` by
    (rpt strip_tac >> qpat_assum `!i. a <= i /\ i < a + 32 + len ==> _`
       (qspec_then `i` mp_tac) >> simp[] >> decide_tac) >>
  rename1 `eval_operand (Var src) s = SOME (n2w src_addr)` >>
  qabbrev_tac `emptyD = <| d_stor := K (K {}); d_trans := K (K {});
                          d_imm := K {}; d_ret := K {} |>` >>
  mp_tac (Q.INST [`a` |-> `n2w (src_addr:num)`, `D` |-> `emptyD`]
    body_assign_immutable_bytes_header_joint_fresh) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choosel_then [`r`,`Gr`,`tr`,`out`] (map_every assume_tac o CONJUNCTS)) >>
  `r.vs_alloca_next = s.vs_alloca_next /\ r.vs_allocas = s.vs_allocas /\
   r.vs_fmp = s.vs_fmp /\ r.vs_initial_fmp = s.vs_initial_fmp /\
   r.vs_labels = s.vs_labels` by
    (qpat_assum `(r with <|vs_vars := _; vs_inst_idx := _|>) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    (simp[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS,
      DECIDE ``m:num <= m + 3``]) >>
  `eval_operand (Var src) r = SOME (n2w src_addr) /\
   op_taint tr (Var src) = {} /\ ptr_covers Gr tr src r (32*n)` by
    (conj_tac >- fs[eval_operand_def] >>
     `ptr_covers Gr tr src r (32*n)` by metis_tac[] >> fs[ptr_covers_def]) >>
  `case imm of NONE => T | SOME region =>
     copy_old_operand sm region /\ eval_operand region r = SOME (0w:bytes32) /\
     op_taint tr region = {} /\ op_prov Gr region = NONE` by
    (Cases_on `imm` >> simp[] >> rename1 `copy_old_operand sm opnd` >>
     Cases_on `opnd` >> fs[copy_old_operand_def, eval_operand_def, op_taint_def, op_prov_def]) >>
  `copy_old_operand sm dst /\ eval_operand dst r = SOME (n2w off) /\
    op_taint tr dst = {} /\ op_prov Gr dst = NONE` by
    (Cases_on `dst` >> fs[copy_old_operand_def,eval_operand_def,op_taint_def,op_prov_def]) >>
  `n < dimword(:256)` by decide_tac >>
  `allocas_from lo r /\ (ctx_has_dalloca ctx ==> allocas_below_fmp r)` by
    (fs[allocas_from_def, allocas_below_fmp_def] >> (metis_tac[allocas_from_def, allocas_below_fmp_def])) >>
  mp_tac (Q.SPECL [`sm`,`Var src`,`dst`,`cnt`,`imm`,
    `n2w src_addr`,`n2w off`,`n`,`lo`,`ctx`,`r`,`Gr`,`tr`,`emptyD`,
    `explicit`,`func`,`PG`,`u`,`sb`] body_assign_immutable_bytes_loop_actual) >>
  (impl_tac >-
    (`eval_operand cnt r = SOME (n2w n)` by fs[Abbr `n`] >>
     Cases_on `imm` >>
     qpat_x_assum `case _ of NONE => T | SOME _ => _` mp_tac >>
     simp[eval_operand_def, op_taint_def, op_prov_def, copy_old_operand_def,
          IgnAsm `32 + len <= 32 * n`] >> decide_tac)) >>
  disch_then strip_assume_tac >>
  rename1 `t_exit.vs_inst_idx = LENGTH sb.cs_current_insts` >>
  rename1 `gas_origin_ptr_path _ (_,_,_) [] (OK t_exit,G_exit,tn_exit)` >>
  `gas_origin_ptr_path (emptyD,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t_exit,G_exit,tn_exit)` by
    (irule gas_origin_ptr_path_trans >> metis_tac[]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t_exit,G_exit,tn_exit)` by
    (gen_tac >> irule fragGasOriginPtrDeadTheory.gas_origin_ptr_path_from_no_dead >>
     qpat_assum `gas_origin_ptr_path (emptyD,_,_,_,_,_) (s,G,tn) [] (OK t_exit,_,_)`
       mp_tac >> simp[Abbr `emptyD`]) >>
  `(t_exit with <|vs_vars := s.vs_vars; vs_current_bb := s.vs_current_bb;
     vs_prev_bb := s.vs_prev_bb; vs_inst_idx := s.vs_inst_idx|>) =
     immutable_transfers T T (n2w src_addr) (n2w off) n 0 s` by
    (qabbrev_tac `ur = immutable_transfers T T (n2w src_addr) (n2w off) n 0 r` >>
     qabbrev_tac `us = immutable_transfers T T (n2w src_addr) (n2w off) n 0 s` >>
     `ur.vs_memory = us.vs_memory /\ ur.vs_immutables = us.vs_immutables` by
       (simp[Abbr `ur`, Abbr `us`, NoAsms] >>
        irule immutableCopyExecutionTheory.immutable_transfers_cong >>
        qpat_assum `(r with <|vs_vars := _; vs_inst_idx := _|>) = s` mp_tac >>
        POP_ASSUM_LIST kall_tac >> simp[venom_state_component_equality] >>
        strip_tac >> simp[]) >>
     `(ur with <|vs_memory := r.vs_memory; vs_immutables := r.vs_immutables|>) = r` by
       simp[Abbr `ur`, NoAsms, immutableAssignStoreTheory.immutable_transfers_record_restore] >>
     `(us with <|vs_memory := s.vs_memory; vs_immutables := s.vs_immutables|>) = s` by
       simp[Abbr `us`, NoAsms, immutableAssignStoreTheory.immutable_transfers_record_restore] >>
     qpat_assum `(t_exit with <|vs_vars := _; vs_current_bb := _;
       vs_prev_bb := _; vs_inst_idx := _|>) = ur` mp_tac >>
     qpat_assum `(r with <|vs_vars := _; vs_inst_idx := _|>) = s` mp_tac >>
     map_every (fn q => qpat_assum q mp_tac)
       [`ur.vs_memory = us.vs_memory`, `ur.vs_immutables = us.vs_immutables`,
        `(ur with <|vs_memory := _; vs_immutables := _|>) = r`,
        `(us with <|vs_memory := _; vs_immutables := _|>) = s`] >>
     POP_ASSUM_LIST kall_tac >> simp[venom_state_component_equality] >>
     rpt strip_tac >> metis_tac[]) >>
  `sa.cs_next_var <= sb.cs_next_var` by
    (qpat_assum `ci_mono sm sb` (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
     decide_tac) >>
  `!x. not_fresh_at sa x ==> lookup_var x t_exit = lookup_var x s /\
     FLOOKUP G_exit x = FLOOKUP G x /\ op_taint tn_exit (Var x) = op_taint tn (Var x)` by
    (gen_tac >> strip_tac >> `not_fresh_at sm x` by simp[] >> simp[]) >>
  `val_footprint stv v = 32 + len /\ val_footprint dtv v = 32 + len` by
    (drule_all place_store_bytestring_representation >> strip_tac >>
     drule_all bytestring_type_value >> strip_tac >>
     qpat_x_assum `(?bs. _) \/ (?str. _)` strip_assume_tac >>
     gvs[val_footprint_def, value_has_type_def]) >>
  `!k. k < 32*n ==> (off + k IN tn_exit.t_mem <=> src_addr + k IN tn.t_mem)` by
    (qpat_assum `!k. _ ==> (w2n (n2w off) + k IN tn_exit.t_mem <=> _)` mp_tac >>
     qpat_assum `w2n (n2w off:bytes32) = off` (fn hb =>
       qpat_assum `w2n (n2w src_addr:bytes32) = src_addr` (fn ha =>
         qpat_assum `tr.t_mem = tn.t_mem` (fn hm => pure_rewrite_tac[ha,hb,hm]))) >>
     disch_then ACCEPT_TAC) >>
  `!j. ~(off <= j /\ j < off+32*n) ==> (j IN tn_exit.t_mem <=> j IN tn.t_mem)` by
    (qpat_assum `!j. _ ==> (j IN tn_exit.t_mem <=> j IN tr.t_mem)` mp_tac >>
     qpat_assum `w2n (n2w off:bytes32) = off` (fn hb =>
       qpat_assum `tr.t_mem = tn.t_mem` (fn hm => pure_rewrite_tac[hb,hm])) >>
     disch_then ACCEPT_TAC) >>
  `tn_exit.t_stor = tn.t_stor /\ tn_exit.t_trans = tn.t_trans` by simp[] >>
  qexistsl [`len`,`t_exit`,`G_exit`,`tn_exit`] >>
  qpat_assum `Abbrev (n = _)`
    (fn th => pure_once_rewrite_tac[GSYM (REWRITE_RULE[markerTheory.Abbrev_def] th)]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (qpat_assum `v = _` (fn th => simp[NoAsms,th]) >> NO_TAC) >>
  simp[]
QED

Theorem body_assign_immutable_bytes_path_store:
  compile_store_immutable_bytestring imm (Var src) dst sa = ((),sb) /\
  fn_has_code sa sb func /\
  not_fresh_at sa src /\ copy_old_operand sa dst /\
  eval_operand dst s = SOME (n2w off) /\
  op_taint tn dst = {} /\ op_prov G dst = NONE /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  is_bytestring_type sty /\ is_bytestring_type dty /\
  type_widens_to (get_tenv cx) sty dty /\ value_has_type stv v /\
  off + type_memory_size dtv <= lo /\ lo < dimword(:256) /\
  eval_operand (Var src) s = SOME (n2w a) /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory stv v a mem) /\
  ptr_covers G tn src s (type_memory_size stv) /\
  lo <= a /\ a + type_memory_size stv < dimword(:256) /\
  (type_memory_size stv = 0 \/ a + type_memory_size stv <= s.vs_alloca_next) /\
  (!region. imm = SOME region ==>
    eval_operand region s = SOME 0w /\ op_taint tn region = {} /\
    op_prov G region = NONE) /\
  (!x. imm = SOME (Var x) ==> not_fresh_at sa x) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?q Gf tf. immutable_path_store_post (lo,explicit,ctx,func,PG) off dtv v
    sa sb (s,G,tn) (q,Gf,tf)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`explicit` |-> `explicit`,`PG` |-> `PG`]
    body_assign_immutable_bytes_path_copy) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`len`,`q`,`Gf`,`tf`] (map_every assume_tac o CONJUNCTS)) >>
  qabbrev_tac `n = 1 + word_size len` >>
  `q.vs_memory = (immutable_transfers T T (n2w a) (n2w off) n 0 s).vs_memory` by
    (qpat_assum `(q with <|vs_vars := _; vs_current_bb := _;
       vs_prev_bb := _; vs_inst_idx := _|>) = _` mp_tac >>
     simp[venom_state_component_equality,Abbr `n`]) >>
  `a+32+len < dimword (:256) /\ off+32*n < dimword (:256) /\
   off+32*n <= a /\ 32+len <= 32*n` by
    (`val_footprint stv v <= type_memory_size stv` by simp[val_footprint_le,valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
     fs[Abbr `n`] >> decide_tac) >>
  `mem_bytes_at off (32+len) q.vs_memory = mem_bytes_at a (32+len) s.vs_memory` by
    (simp[] >> irule immutable_transfers_memory_prefix >> simp[]) >>
  `val_in_memory stv v a s.vs_memory` by fs[mem_agree_outside_def] >>
  `val_in_memory stv v off q.vs_memory` by
    (qspecl_then [`stv`,`v`,`a`,`off`,`s.vs_memory`,`q.vs_memory`]
       match_mp_tac exprSimMemoryTransportTheory.val_in_memory_relocate_footprint >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- simp[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
     qpat_assum `val_footprint stv v = _` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `mem_bytes_at off (32+len) q.vs_memory = _` (ACCEPT_TAC o SYM)) >>
  `val_in_memory dtv v off q.vs_memory` by
    (qspecl_then [`get_tenv cx`,`sty`,`dty`,`stv`,`dtv`,`v`,`off`,`q.vs_memory`]
       match_mp_tac valueCopyBytesTheory.bytestring_val_in_memory_transfer >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!j. off <= j /\ j < off + val_footprint dtv v ==> j NOTIN tf.t_mem` by
    (rpt strip_tac >>
     `off+(j-off) = j /\ j-off < 32*n /\
       a <= a+(j-off) /\ a+(j-off) < a+32+len` by decide_tac >>
     `a+(j-off) NOTIN tn.t_mem` by
       (qpat_assum `!i. _ ==> i NOTIN tn.t_mem`
          (qspec_then `a+(j-off)` match_mp_tac) >>
        conj_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `!k. k < 32*n ==> _` (qspec_then `j-off` (drule_then mp_tac)) >>
     qpat_assum `off+(j-off) = j` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `a+(j-off) NOTIN tn.t_mem` (fn th => simp[NoAsms,th]) >>
     first_assum ACCEPT_TAC) >>
  `!mem. mem_agree_outside tf.t_mem q.vs_memory mem ==> val_in_memory dtv v off mem` by
    (qspecl_then [`dtv`,`v`,`off`,`q.vs_memory`,`tf.t_mem`] match_mp_tac
       calldataTypedRobustPtrTheory.clean_footprint_val_in_memory_robust >>
     simp[valueTypingMemoryPropsTheory.value_has_type_memory_wf]) >>
  qexistsl [`q`,`Gf`,`tf`] >> simp[immutable_path_store_post_def] >>
  `((immutable_transfers T T (n2w a) (n2w off) n 0 s) with
      <|vs_memory := s.vs_memory; vs_immutables := s.vs_immutables|>) = s` by
    simp[immutable_transfers_record_restore] >>
  conj_tac >-
    (qpat_assum `(q with <|vs_vars := _; vs_current_bb := _;
         vs_prev_bb := _; vs_inst_idx := _|>) = _`
       (mp_tac o AP_TERM ``\t:venom_state.
         t with <|vs_memory := s.vs_memory; vs_immutables := s.vs_immutables|>``) >>
     BETA_TAC >>
     qpat_assum `(_ with <|vs_memory := s.vs_memory; vs_immutables := s.vs_immutables|>) = s`
       (fn th =>
         qpat_assum `s.vs_current_bb = sa.cs_current_bb` (fn bb =>
           qpat_assum `s.vs_inst_idx = LENGTH sa.cs_current_insts` (fn idx =>
             simp[NoAsms,th,bb,idx]))) >>
     disch_then ACCEPT_TAC) >>
  simp[immutable_transfers_memory_nondecreasing] >>
  conj_tac >-
    (rpt strip_tac >> simp[] >> irule immutable_transfers_memory_frame >>
     fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  rpt strip_tac >>
  qpat_assum `!i. _ ==> (i IN tf.t_mem <=> i IN tn.t_mem)` (qspec_then `i` mp_tac) >>
  (impl_tac >- (fs[Abbr `n`] >> decide_tac)) >> simp[]
QED

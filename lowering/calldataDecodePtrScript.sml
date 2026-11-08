(* Pointer and taint boundaries for calldata decoding writes. *)
Theory calldataDecodePtr
Ancestors bodyPtrDefs ptrDiscipline venomInst venomState venomExecSemantics
  codegenRel contextCodegenRel memLocDefs pred_set abiEncoder compileEnv emitHelper
  entryDispatchPtr ptrSafeRun list finite_map abiDecoderGuards exprLoweringProps
  fragExec words abiDecoderContract ghostPcTransportPtr decoderGhostFramePtr

Theorem calldatacopy_access_ok:
  eval_operand n s = SOME nw /\ ptr_covers G tn p s (w2n nw) ==>
  access_ok lo G fn (mk_inst id CALLDATACOPY [Var p;src;n] []) s
Proof
  rw[ptr_covers_def, access_ok_def, mk_inst_def,
     source_memory_write_ranges_def, sized_source_write_range_def,
     source_memory_read_ranges_def, mem_write_ops_def, eval_operand_def] >>
  Cases_on `eval_operand src s` >> gvs[]
QED

Theorem calldatacopy_taint_ok:
  op_taint tn (Var p) = {} /\ op_taint tn src = {} /\ op_taint tn n = {} ==>
  taint_ok fn tn (mk_inst id CALLDATACOPY [Var p;src;n] []) s
Proof
  simp[taint_ok_def, mk_inst_def, source_memory_read_ranges_def] >>
  metis_tac[]
QED

Theorem calldatacopy_written_range_clean:
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  eval_operand n s = SOME nw /\ w2n dw <= i /\ i < w2n dw + w2n nw ==>
  i NOTIN (step_taint (mk_inst id CALLDATACOPY [dst;src;n] []) s s' tn).t_mem
Proof
  simp[step_taint_def, mem_taint_def, step_writes_def, written_taint_def,
       mk_inst_def, source_memory_write_ranges_def, sized_source_write_range_def,
       range_bytes_def] >> metis_tac[]
QED

Theorem calldatacopy_nonmemory_taint:
  (step_taint (mk_inst id CALLDATACOPY [dst;src;n] []) s s' tn).t_stor = tn.t_stor /\
  (step_taint (mk_inst id CALLDATACOPY [dst;src;n] []) s s' tn).t_trans = tn.t_trans /\
  (step_taint (mk_inst id CALLDATACOPY [dst;src;n] []) s s' tn).t_imm = tn.t_imm
Proof
  simp[step_taint_def, mk_inst_def, adopt_reset_def, store_taint_def, imm_taint_def]
QED

Theorem calldata_bytestring_decoder_instructions:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (DecBytestring m) sa =
    ((),sb) ==>
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++
    [mk_inst sa.cs_next_id CALLDATALOAD [src]
       ["%" ++ toString sa.cs_next_var];
     mk_inst (sa.cs_next_id + 1) GT
       [Var ("%" ++ toString sa.cs_next_var); Lit (n2w m)]
       ["%" ++ toString (sa.cs_next_var + 1)];
     mk_inst (sa.cs_next_id + 2) ISZERO
       [Var ("%" ++ toString (sa.cs_next_var + 1))]
       ["%" ++ toString (sa.cs_next_var + 2)];
     mk_inst (sa.cs_next_id + 3) ASSERT
       [Var ("%" ++ toString (sa.cs_next_var + 2))] [];
     mk_inst (sa.cs_next_id + 4) CALLDATACOPY
       [dst;src;Lit (n2w (32 + 32 * ((m + 31) DIV 32)))] []] /\
  sb.cs_next_var = sa.cs_next_var + 3 /\
  sb.cs_next_id = sa.cs_next_id + 5
Proof
  simp[Once compile_abi_decode_to_buf_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, emit_inst_def,
       fresh_var_def, fresh_id_def, emit_def, listTheory.APPEND_ASSOC] >>
  disch_then (SUBST1_TAC o SYM) >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >> simp[]
QED

Theorem ptr_safe_decoder_check_step:
  MEM opc [GT; ASSERT] /\
  EVERY (\op. op_taint tn op = {}) ops /\
  (!u v. ops <> [Var u; Var v]) /\
  step_inst fuel ctx (mk_inst id opc ops outs) s = OK t /\
  t.vs_requests = s.vs_requests /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ptr_safe_step D lo fuel ctx fn PG G tn (mk_inst id opc ops outs) s
Proof
  strip_tac >> fs[MEM] >>
  gvs[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
      mk_inst_def, source_memory_write_ranges_def,
      source_memory_read_ranges_def, EVERY_MEM] >>
  metis_tac[]
QED

Theorem decoder_gt_literal_output_clean:
  op_taint tn op = {} ==>
  op_taint (step_taint (mk_inst id GT [op; Lit bound] [out]) s t tn)
    (Var out) = {}
Proof
  simp[op_taint_def, step_taint_def, mk_inst_def, set_var_taint_def,
       FLOOKUP_UPDATE, out_taint_def] >>
  Cases_on `eval_operand op s` >> simp[]
QED

Theorem calldatacopy_safe_continuation:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id CALLDATACOPY [Var p;src;n] []) /\
  eval_operand (Var p) s = SOME dw /\ eval_operand src s = SOME sw /\
  eval_operand n s = SOME nw /\ ptr_covers G tn p s (w2n nw) /\
  op_taint tn (Var p) = {} /\ op_taint tn src = {} /\ op_taint tn n = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  t = write_memory_with_expansion (w2n dw)
    (TAKE (w2n nw)
      (DROP (w2n sw) s.vs_call_ctx.cc_calldata ++ REPLICATE (w2n nw) 0w)) s /\
  (!fuel. ptr_safe_run D lo fuel ctx fn PG
    (step_prov PG G (mk_inst id CALLDATACOPY [Var p;src;n] []) t)
    (step_taint (mk_inst id CALLDATACOPY [Var p;src;n] []) s t tn)
    (t with vs_inst_idx := SUC s.vs_inst_idx)) ==>
  !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s
Proof
  strip_tac >> gen_tac >>
  irule ptr_safe_run_scalar_continuation >>
  qexistsl_tac [`bb`, `mk_inst id CALLDATACOPY [Var p;src;n] []`, `t`] >>
  simp[mk_inst_def, is_terminator_def] >>
  conj_tac
  >- simp[step_inst_non_invoke, step_inst_base_def] >>
  conj_tac
  >- simp[write_memory_with_expansion_def, write_memory_def, expand_memory_def] >>
  `access_ok lo G fn (mk_inst id CALLDATACOPY [Var p;src;n] []) s` by
    (irule calldatacopy_access_ok >> metis_tac[]) >>
  `taint_ok fn tn (mk_inst id CALLDATACOPY [Var p;src;n] []) s` by
    (irule calldatacopy_taint_ok >> simp[]) >>
  gvs[ptr_safe_step_def, ptr_inst_ok_def, mk_inst_def,
      step_inst_non_invoke, step_inst_base_def,
      write_memory_with_expansion_def, write_memory_def, expand_memory_def]
QED

Theorem decoder_step_taint_memory_no_new_site[local]:
  t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp /\
  written_taint tn inst s = {} ==>
  (step_taint inst s t tn).t_mem SUBSET tn.t_mem
Proof
  strip_tac >>
  `new_site_bytes s t = {}` by
    (simp[new_site_bytes_def, EXTENSION, FLOOKUP_DEF] >> metis_tac[]) >>
  mp_tac (Q.INST [`R` |-> `{}:num set`] step_taint_memory_bound) >> simp[]
QED

Theorem calldata_bytestring_overwrite_endpoint_core[local]:
  compile_abi_decode_to_buf (Var p) src CALLDATALOAD (Lit 0w)
    (DecBytestring m) sa = ((),sb) /\
  C = 32 + 32 * ((m + 31) DIV 32) /\ C < dimword (:256) /\
  m < dimword (:256) /\
  eval_operand (Var p) s = SOME dw /\ eval_operand src s = SOME sw /\
  abi_decode_load CALLDATALOAD sw s = n2w len /\ len <= m /\
  not_fresh_at sa p /\ (!q. src = Var q ==> not_fresh_at sa q) /\
  run_inst_seq (emitted_insts sa sb) s = OK actual /\ ptr_covers G tn p s C /\
  op_taint tn src = {} /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?s' G' tn'.
    run_inst_seq (emitted_insts sa sb) s =
      OK (s' with vs_inst_idx := s.vs_inst_idx) /\
    ~s'.vs_halted /\ s'.vs_current_bb = sb.cs_current_bb /\
    s'.vs_inst_idx = LENGTH sb.cs_current_insts /\
    eval_operand (Var p) s' = SOME dw /\ eval_operand src s' = SOME sw /\
    s'.vs_allocas = s.vs_allocas /\ s'.vs_alloca_next = s.vs_alloca_next /\
    ptr_covers G' tn' p s' C /\
    (!i. w2n dw <= i /\ i < w2n dw + C ==> i NOTIN tn'.t_mem) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem SUBSET tn.t_mem /\
    ((!fuel. ptr_safe_run D lo fuel ctx fn PG G' tn' s') ==>
     !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >>
  drule calldata_bytestring_decoder_instructions >> strip_tac >>

  qabbrev_tac `v0 = "%" ++ toString sa.cs_next_var` >>
  qabbrev_tac `v1 = "%" ++ toString (sa.cs_next_var + 1)` >>
  qabbrev_tac `v2 = "%" ++ toString (sa.cs_next_var + 2)` >>
  qabbrev_tac `i0 = mk_inst sa.cs_next_id CALLDATALOAD [src] [v0]` >>
  qabbrev_tac `i1 = mk_inst (sa.cs_next_id + 1) GT [Var v0; Lit (n2w m)] [v1]` >>
  qabbrev_tac `i2 = mk_inst (sa.cs_next_id + 2) ISZERO [Var v1] [v2]` >>
  qabbrev_tac `i3 = mk_inst (sa.cs_next_id + 3) ASSERT [Var v2] []` >>
  `?guarded. run_inst_seq [i0;i1;i2;i3] s = OK guarded` by
    (spose_not_then assume_tac >>
     qspecl_then [`[i0;i1;i2;i3]`,
       `[mk_inst (sa.cs_next_id + 4) CALLDATACOPY [Var p;src;Lit (n2w C)] []]`, `s`]
       mp_tac run_inst_seq_append_err >>
     gvs[emitted_insts_def, DROP_PREFIX, Abbr `i0`, Abbr `i1`, Abbr `i2`,
       Abbr `i3`, Abbr `v0`, Abbr `v1`, Abbr `v2`]) >>
  qpat_x_assum `run_inst_seq _ s = OK actual` kall_tac >>
  qpat_x_assum `run_inst_seq _ s = OK guarded` mp_tac >>
  simp[run_inst_seq_def] >> simp[AllCaseEqs()] >> strip_tac >>
  rename1 `step_inst_base i0 s = OK s1` >>
  rename1 `step_inst_base i1 s1 = OK s2` >>
  rename1 `step_inst_base i2 s2 = OK s3` >>
  `p <> v0 /\ src <> Var v0` by
    (gvs[not_fresh_at_def, Abbr `v0`] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `ptr_covers (step_prov PG G i0 s1) (step_taint i0 s s1 tn) p s1 C /\
   op_taint (step_taint i0 s s1 tn) src = {}` by
    (qpat_x_assum `step_inst_base i0 s = OK s1` mp_tac >>
     simp[Abbr `i0`, step_inst_base_def, exec_read1_def] >>
     strip_tac >> gvs[] >> conj_tac
     >- (irule ptr_covers_step_frame >>
         simp[mk_inst_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
     simp[step_taint_single_output_preserves_other_operand]) >>
  qabbrev_tac `G1 = step_prov PG G i0 s1` >>
  qabbrev_tac `tn1 = step_taint i0 s s1 tn` >>
  qabbrev_tac `G2 = step_prov PG G1 i1 s2` >>
  qabbrev_tac `tn2 = step_taint i1 s1 s2 tn1` >>
  `!k. p <> "%" ++ toString (sa.cs_next_var + k) /\
       src <> Var ("%" ++ toString (sa.cs_next_var + k))` by
    (fs[not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_ADD, arithmeticTheory.ADD_COMM]) >>
  `p <> v1 /\ src <> Var v1` by
    (first_x_assum (qspec_then `1` mp_tac) >> simp[Abbr `v1`]) >>
  `ptr_covers G2 tn2 p s2 C /\ op_taint tn2 src = {}` by
    (qpat_x_assum `step_inst_base i1 s1 = OK s2` mp_tac >>
     simp[Abbr `i1`, step_inst_base_def, exec_pure2_def, AllCaseEqs()] >>
     strip_tac >> gvs[] >>
     simp[Abbr `G2`, Abbr `tn2`] >> conj_tac
     >- (irule ptr_covers_step_frame >>
         simp[mk_inst_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
     simp[step_taint_single_output_preserves_other_operand]) >>
  qabbrev_tac `G3 = step_prov PG G2 i2 s3` >>
  qabbrev_tac `tn3 = step_taint i2 s2 s3 tn2` >>
  `p <> v2 /\ src <> Var v2` by
    (first_x_assum (qspec_then `2` mp_tac) >> simp[Abbr `v2`]) >>
  `ptr_covers G3 tn3 p s3 C /\ op_taint tn3 src = {}` by
    (qpat_x_assum `step_inst_base i2 s2 = OK s3` mp_tac >>
     simp[Abbr `i2`, step_inst_base_def, exec_pure1_def, AllCaseEqs()] >>
     strip_tac >> gvs[] >>
     simp[Abbr `G3`, Abbr `tn3`] >> conj_tac
     >- (irule ptr_covers_step_frame >>
         simp[mk_inst_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
     simp[step_taint_single_output_preserves_other_operand]) >>
  `guarded = s3` by
    (qpat_x_assum `step_inst_base i3 s3 = OK guarded` mp_tac >>
     simp[Abbr `i3`, step_inst_base_def, mk_inst_def, AllCaseEqs()] >>
     metis_tac[]) >>
  qabbrev_tac `G4 = step_prov PG G3 i3 guarded` >>
  qabbrev_tac `tn4 = step_taint i3 s3 guarded tn3` >>
  `ptr_covers G4 tn4 p guarded C /\ op_taint tn4 src = {}` by
    (gvs[Abbr `G4`, Abbr `tn4`] >> conj_tac
     >- (irule ptr_covers_step_frame >> simp[Abbr `i3`, mk_inst_def]) >>
     Cases_on `src` >>
     gvs[Abbr `i3`, op_taint_def, step_taint_def, set_var_taint_def,
          mk_inst_def, FLOOKUP_DRESTRICT]) >>
  `eval_operand (Var p) guarded = SOME dw /\
   eval_operand src guarded = SOME sw` by
    (map_every (fn q => qpat_x_assum q mp_tac)
       [`step_inst_base i0 s = OK s1`,
        `step_inst_base i1 s1 = OK s2`,
        `step_inst_base i2 s2 = OK s3`] >>
     simp[Abbr `i0`, Abbr `i1`, Abbr `i2`, mk_inst_def] >>
     simp[Once step_inst_base_def] >>
     simp[Once step_inst_base_def] >>
     simp[Once step_inst_base_def] >>
     simp[exec_read1_def, exec_pure1_def, exec_pure2_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[] >> Cases_on `src` >>
     gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  qabbrev_tac `i4 = mk_inst (sa.cs_next_id + 4) CALLDATACOPY
    [Var p;src;Lit (n2w C)] []` >>
  qabbrev_tac `copied = write_memory_with_expansion (w2n dw)
    (TAKE C (DROP (w2n sw) guarded.vs_call_ctx.cc_calldata ++
      REPLICATE C 0w)) guarded` >>
  qabbrev_tac `G5 = step_prov PG G4 i4 copied` >>
  qabbrev_tac `tn5 = step_taint i4 guarded copied tn4` >>
  `ptr_covers G5 tn5 p copied C` by
    (gvs[Abbr `G5`, Abbr `tn5`, Abbr `i4`, Abbr `copied`,
      ptr_covers_def, step_prov_def, step_taint_def, set_prov_def,
      set_var_taint_def, mk_inst_def, op_taint_def, FLOOKUP_DRESTRICT,
      write_memory_with_expansion_def, write_memory_def, expand_memory_def]) >>
  `!i. w2n dw <= i /\ i < w2n dw + C ==> i NOTIN tn5.t_mem` by
    (gen_tac >> disch_tac >> simp[Abbr `tn5`, Abbr `i4`] >>
     irule calldatacopy_written_range_clean >>
     conj_tac
     >- (qexistsl_tac [`dw`, `n2w C`] >> gvs[eval_operand_def]) >>
     qexists_tac `sw` >> gvs[]) >>
  `s1.vs_inst_idx = s.vs_inst_idx /\ s2.vs_inst_idx = s.vs_inst_idx /\
   guarded.vs_inst_idx = s.vs_inst_idx /\
   guarded.vs_current_bb = s.vs_current_bb /\
   guarded.vs_halted = s.vs_halted /\
   guarded.vs_allocas = s.vs_allocas /\
   guarded.vs_alloca_next = s.vs_alloca_next` by
    (map_every (fn q => qpat_x_assum q mp_tac)
       [`step_inst_base i0 s = OK s1`,
        `step_inst_base i1 s1 = OK s2`,
        `step_inst_base i2 s2 = OK s3`] >>
     qunabbrev_tac `i0` >> qunabbrev_tac `i1` >> qunabbrev_tac `i2` >>
     qpat_x_assum `guarded = s3` (SUBST_ALL_TAC) >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     rpt disch_tac >>
     fs[mk_inst_def] >>
     fs[Once step_inst_base_def] >>
     fs[exec_read1_def, exec_pure1_def, exec_pure2_def, AllCaseEqs()] >>
     gvs[update_var_def]) >>
  qpat_x_assum `guarded = s3` SUBST_ALL_TAC >>
  `run_inst_seq (emitted_insts sa sb) s = OK copied` by
    (simp[emitted_insts_def, DROP_PREFIX, Abbr `i4`] >>
     simp[run_inst_seq_def] >>
     simp[step_inst_base_def, mk_inst_def, eval_operand_def] >>
     gvs[eval_operand_def, Abbr `copied`]) >>
  `tn5.t_stor = tn.t_stor /\ tn5.t_trans = tn.t_trans /\
   tn5.t_imm = tn.t_imm` by
    (simp[Abbr `tn5`, Abbr `i4`, calldatacopy_nonmemory_taint] >>
     simp[Abbr `tn4`, Abbr `i3`, step_taint_def, mk_inst_def,
       adopt_reset_def, store_taint_def, imm_taint_def] >>
     simp[Abbr `tn3`, Abbr `i2`, step_taint_def, mk_inst_def,
       adopt_reset_def, store_taint_def, imm_taint_def] >>
     simp[Abbr `tn2`, Abbr `i1`, step_taint_def, mk_inst_def,
       adopt_reset_def, store_taint_def, imm_taint_def] >>
     simp[Abbr `tn1`, Abbr `i0`, step_taint_def, mk_inst_def,
       adopt_reset_def, store_taint_def, imm_taint_def]) >>
  `copied.vs_inst_idx = s.vs_inst_idx /\
   copied.vs_current_bb = s.vs_current_bb /\
   copied.vs_halted = s.vs_halted /\
   copied.vs_allocas = s.vs_allocas /\
   copied.vs_alloca_next = s.vs_alloca_next /\
   eval_operand (Var p) copied = SOME dw /\
   eval_operand src copied = SOME sw` by
    (fs[eval_operand_def] >>
     simp[Abbr `copied`, write_memory_with_expansion_def,
          write_memory_def, expand_memory_def, eval_operand_def] >>
     Cases_on `src` >> gvs[eval_operand_def]) >>
  `!x. not_fresh_at sa x ==>
     FLOOKUP G5 x = FLOOKUP G x /\
     op_taint tn5 (Var x) = op_taint tn (Var x)` by
    (gen_tac >> strip_tac >>
     `x <> v0 /\ x <> v1 /\ x <> v2` by
       (gvs[not_fresh_at_def, Abbr `v0`, Abbr `v1`, Abbr `v2`]) >>
     simp[Abbr `G5`, Abbr `tn5`, step_prov_other_output,
          step_taint_other_output, Abbr `i4`, mk_inst_def] >>
     simp[Abbr `G4`, Abbr `tn4`, step_prov_other_output,
          step_taint_other_output, Abbr `i3`, mk_inst_def] >>
     simp[Abbr `G3`, Abbr `tn3`, step_prov_other_output,
          step_taint_other_output, Abbr `i2`, mk_inst_def] >>
     simp[Abbr `G2`, Abbr `tn2`, step_prov_other_output,
          step_taint_other_output, Abbr `i1`, mk_inst_def] >>
     simp[Abbr `G1`, Abbr `tn1`, step_prov_other_output,
          step_taint_other_output, Abbr `i0`, mk_inst_def]) >>
  `s1.vs_allocas = s.vs_allocas /\ s2.vs_allocas = s.vs_allocas /\
   s1.vs_fmp = s.vs_fmp /\ s2.vs_fmp = s.vs_fmp /\
   s3.vs_fmp = s.vs_fmp` by
    (map_every (fn q => qpat_x_assum q mp_tac)
       [`step_inst_base i0 s = OK s1`,
        `step_inst_base i1 s1 = OK s2`,
        `step_inst_base i2 s2 = OK s3`] >>
     qunabbrev_tac `i0` >> qunabbrev_tac `i1` >> qunabbrev_tac `i2` >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >> fs[mk_inst_def] >>
     fs[Once step_inst_base_def] >>
     fs[exec_read1_def, exec_pure1_def, exec_pure2_def, AllCaseEqs()] >>
     gvs[update_var_def]) >>
  `copied.vs_fmp = s3.vs_fmp` by
    simp[Abbr `copied`, write_memory_with_expansion_def,
         write_memory_def, expand_memory_def] >>
  `tn1.t_mem SUBSET tn.t_mem` by
    (simp[Abbr `tn1`] >> irule decoder_step_taint_memory_no_new_site >>
     simp[Abbr `i0`, written_taint_def, mk_inst_def]) >>
  `tn2.t_mem SUBSET tn1.t_mem` by
    (simp[Abbr `tn2`] >> irule decoder_step_taint_memory_no_new_site >>
     simp[Abbr `i1`, written_taint_def, mk_inst_def]) >>
  `tn3.t_mem SUBSET tn2.t_mem` by
    (simp[Abbr `tn3`] >> irule decoder_step_taint_memory_no_new_site >>
     simp[Abbr `i2`, written_taint_def, mk_inst_def]) >>
  `tn4.t_mem SUBSET tn3.t_mem` by
    (simp[Abbr `tn4`] >> irule decoder_step_taint_memory_no_new_site >>
     simp[Abbr `i3`, written_taint_def, mk_inst_def]) >>
  `tn5.t_mem SUBSET tn4.t_mem` by
    (simp[Abbr `tn5`] >> irule decoder_step_taint_memory_no_new_site >>
     simp[Abbr `i4`, written_taint_def, mk_inst_def]) >>
  `tn5.t_mem SUBSET tn.t_mem` by metis_tac[SUBSET_TRANS] >>
  qexistsl_tac [`copied with vs_inst_idx := LENGTH sb.cs_current_insts`, `G5`, `tn5`] >>
  `copied with vs_inst_idx := LENGTH sa.cs_current_insts = copied` by
    simp[venom_state_component_equality] >>
  `ptr_covers G5 tn5 p
     (copied with vs_inst_idx := LENGTH sb.cs_current_insts) C` by
    (fs[ptr_covers_def, lookup_var_def] >> metis_tac[]) >>
  fs[eval_operand_def, lookup_var_def] >>
  simp[lookup_var_def] >>
  conj_tac
  >- metis_tac[] >>
  disch_tac >>
  `?bb. lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
     !k. k < LENGTH [i0;i1;i2;i3;i4] ==> get_instruction bb (LENGTH sa.cs_current_insts + k) =
       SOME (EL k [i0;i1;i2;i3;i4])` by
    (irule fn_has_code_same_block >> qexists_tac `sb` >>
     simp[Abbr `i4`]) >>
  `!fuel. ptr_safe_run D lo fuel ctx fn PG G4 tn4
      (s3 with vs_inst_idx := LENGTH sa.cs_current_insts + 4)` by
    (`allocas_from lo (s3 with vs_inst_idx := LENGTH sa.cs_current_insts + 4)` by
       (fs[allocas_from_def] >> first_assum MATCH_ACCEPT_TAC) >>
     irule calldatacopy_safe_continuation >> simp[] >>
     qexistsl_tac [`dw`, `sa.cs_next_id + 4`, `Lit (n2w C)`,
       `n2w C`, `p`, `src`, `sw`] >>
     simp[Abbr `i4`, eval_operand_def, op_taint_def] >>
     conj_tac
     >- (qpat_x_assum `!fuel. ptr_safe_run _ _ _ _ _ _ G5 tn5 _` mp_tac >>
         simp[Abbr `G5`, Abbr `tn5`, Abbr `copied`, arithmeticTheory.ADD1]) >>
     qpat_x_assum `ptr_covers G4 tn4 p s3 C` mp_tac >>
     simp[ptr_covers_def, lookup_var_def, op_taint_def]) >>
  `op_taint tn1 (Var v0) = {}` by
    (simp[Abbr `tn1`, Abbr `i0`] >>
     irule dispatch_scalar_output_clean >> simp[]) >>
  `op_taint tn2 (Var v1) = {}` by
    (simp[Abbr `tn2`, Abbr `i1`] >>
     irule decoder_gt_literal_output_clean >> simp[]) >>
  `op_taint tn3 (Var v2) = {}` by
    (simp[Abbr `tn3`, Abbr `i2`] >>
     irule dispatch_scalar_output_clean >> simp[]) >>
  `!fuel. ptr_safe_run D lo fuel ctx fn PG G3 tn3
      (s3 with vs_inst_idx := LENGTH sa.cs_current_insts + 3)` by
    (gen_tac >> irule ptr_safe_run_scalar_continuation >>
     qexistsl_tac [`bb`, `i3`,
       `s3 with vs_inst_idx := LENGTH sa.cs_current_insts + 3`] >>
     simp[Abbr `i3`, mk_inst_def, is_terminator_def] >>
     `step_inst fuel ctx (mk_inst (sa.cs_next_id + 3) ASSERT [Var v2] [])
        (s3 with vs_inst_idx := LENGTH sa.cs_current_insts + 3) =
        OK (s3 with vs_inst_idx := LENGTH sa.cs_current_insts + 3)` by
       (qpat_x_assum `step_inst_base _ s3 = OK s3` mp_tac >>
        simp[step_inst_non_invoke, step_inst_base_def, mk_inst_def,
             eval_operand_def, AllCaseEqs()] >> metis_tac[]) >>
     fs[mk_inst_def] >> conj_tac
     >- (qpat_x_assum `!fuel. ptr_safe_run _ _ _ _ _ _ G4 tn4 _` mp_tac >>
         simp[Abbr `G4`, Abbr `tn4`, arithmeticTheory.ADD1]) >>
     simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
          source_memory_read_ranges_def, source_memory_write_ranges_def] >>
     fs[allocas_from_def] >> first_assum MATCH_ACCEPT_TAC) >>
  `s1.vs_current_bb = s.vs_current_bb /\
   s2.vs_current_bb = s.vs_current_bb /\
   s1.vs_requests = s.vs_requests /\
   s2.vs_requests = s.vs_requests /\
   s3.vs_requests = s.vs_requests /\
   s1.vs_allocas = s.vs_allocas /\ s2.vs_allocas = s.vs_allocas` by
    (map_every (fn q => qpat_x_assum q mp_tac)
       [`step_inst_base i0 s = OK s1`,
        `step_inst_base i1 s1 = OK s2`,
        `step_inst_base i2 s2 = OK s3`] >>
     qunabbrev_tac `i0` >> qunabbrev_tac `i1` >> qunabbrev_tac `i2` >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >> fs[mk_inst_def] >>
     fs[Once step_inst_base_def] >>
     fs[exec_read1_def, exec_pure1_def, exec_pure2_def, AllCaseEqs()] >>
     gvs[update_var_def]) >>
  `!fuel. ptr_safe_run D lo fuel ctx fn PG G2 tn2
      (s2 with vs_inst_idx := LENGTH sa.cs_current_insts + 2)` by
    (gen_tac >>
     `step_inst fuel ctx i2 (s2 with vs_inst_idx := LENGTH sa.cs_current_insts + 2) =
        OK (s3 with vs_inst_idx := LENGTH sa.cs_current_insts + 2)` by
       (qpat_x_assum `step_inst_base i2 s2 = OK s3` mp_tac >>
        simp[Abbr `i2`, step_inst_non_invoke, step_inst_base_def,
             exec_pure1_def, eval_operand_def, AllCaseEqs()] >>
        strip_tac >> gvs[update_var_def]) >>
     irule ptr_safe_run_scalar_continuation >>
     qexistsl_tac [`bb`, `i2`, `s3 with vs_inst_idx := LENGTH sa.cs_current_insts + 2`] >>
     simp[Abbr `i2`, mk_inst_def, is_terminator_def] >>
     conj_tac
     >- (qpat_x_assum `!fuel. ptr_safe_run _ _ _ _ _ _ G3 tn3 _` mp_tac >>
         simp[Abbr `G3`, Abbr `tn3`, arithmeticTheory.ADD1]) >>
     fs[mk_inst_def] >>
     simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
          source_memory_read_ranges_def, source_memory_write_ranges_def] >>
     fs[allocas_from_def] >> first_assum MATCH_ACCEPT_TAC) >>
  `!fuel. ptr_safe_run D lo fuel ctx fn PG G1 tn1
      (s1 with vs_inst_idx := LENGTH sa.cs_current_insts + 1)` by
    (gen_tac >>
     `step_inst fuel ctx i1 (s1 with vs_inst_idx := LENGTH sa.cs_current_insts + 1) =
        OK (s2 with vs_inst_idx := LENGTH sa.cs_current_insts + 1)` by
       (qpat_x_assum `step_inst_base i1 s1 = OK s2` mp_tac >>
        simp[Abbr `i1`, step_inst_non_invoke, step_inst_base_def,
             exec_pure2_def, eval_operand_def, AllCaseEqs()] >>
        strip_tac >> gvs[update_var_def]) >>
     irule ptr_safe_run_scalar_continuation >>
     qexistsl_tac [`bb`, `i1`, `s2 with vs_inst_idx := LENGTH sa.cs_current_insts + 1`] >>
     simp[Abbr `i1`, mk_inst_def, is_terminator_def] >>
     conj_tac
     >- (qpat_x_assum `!fuel. ptr_safe_run _ _ _ _ _ _ G2 tn2 _` mp_tac >>
         simp[Abbr `G2`, Abbr `tn2`, arithmeticTheory.ADD1]) >>
     fs[mk_inst_def] >>
     simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
          source_memory_read_ranges_def, source_memory_write_ranges_def,
          op_taint_def] >>
     fs[allocas_from_def, op_taint_def] >> conj_tac
     >- (gen_tac >> Cases_on `op = Var v0` >> gvs[op_taint_def] >>
         Cases_on `op = Lit (n2w m)` >> gvs[op_taint_def]) >>
     first_assum MATCH_ACCEPT_TAC) >>
  gen_tac >> irule ptr_safe_run_scalar_continuation >>
  qexistsl_tac [`bb`, `i0`, `s1`] >>
  simp[Abbr `i0`, mk_inst_def, is_terminator_def, step_inst_non_invoke] >>
  conj_tac
  >- (qpat_x_assum `!k. k < LENGTH _ ==> _` (qspec_then `0` mp_tac) >>
      simp[mk_inst_def]) >>
  conj_tac
  >- simp[arithmeticTheory.ADD1] >>
  fs[mk_inst_def] >>
  simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def,
       step_inst_non_invoke] >>
  fs[allocas_from_def] >> first_assum MATCH_ACCEPT_TAC
QED

Theorem calldata_bytestring_overwrite_prefix:
  compile_abi_decode_to_buf (Var p) src CALLDATALOAD (Lit 0w)
    (DecBytestring m) sa = ((),sb) /\
  C = 32 + 32 * ((m + 31) DIV 32) /\ C < dimword (:256) /\
  m < dimword (:256) /\
  eval_operand (Var p) s = SOME dw /\ eval_operand src s = SOME sw /\
  abi_decode_load CALLDATALOAD sw s = n2w len /\ len <= m /\
  not_fresh_at sa p /\ (!q. src = Var q ==> not_fresh_at sa q) /\
  run_inst_seq (emitted_insts sa sb) s = OK actual /\ ptr_covers G tn p s C /\
  op_taint tn src = {} /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?G' tn'.
    ~(actual with vs_inst_idx := LENGTH sb.cs_current_insts).vs_halted /\
    (actual with vs_inst_idx := LENGTH sb.cs_current_insts).vs_current_bb = sb.cs_current_bb /\
    (actual with vs_inst_idx := LENGTH sb.cs_current_insts).vs_inst_idx = LENGTH sb.cs_current_insts /\
    eval_operand (Var p) (actual with vs_inst_idx := LENGTH sb.cs_current_insts) = SOME dw /\
    eval_operand src (actual with vs_inst_idx := LENGTH sb.cs_current_insts) = SOME sw /\
    (actual with vs_inst_idx := LENGTH sb.cs_current_insts).vs_allocas = s.vs_allocas /\
    (actual with vs_inst_idx := LENGTH sb.cs_current_insts).vs_alloca_next = s.vs_alloca_next /\
    ptr_covers G' tn' p (actual with vs_inst_idx := LENGTH sb.cs_current_insts) C /\
    (!i. w2n dw <= i /\ i < w2n dw + C ==> i NOTIN tn'.t_mem) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem SUBSET tn.t_mem /\
    ((!fuel. ptr_safe_run D lo fuel ctx fn PG G' tn'
        (actual with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
     !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >> drule_all calldata_bytestring_overwrite_endpoint_core >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `s' = actual with vs_inst_idx := LENGTH sb.cs_current_insts` by
    (gvs[] >> simp[venom_state_component_equality]) >>
  qexistsl_tac [`G'`, `tn'`] >> gvs[]
QED

Theorem calldata_bytestring_decoder_prefix_framed:
  compile_abi_decode_to_buf (Var p) src CALLDATALOAD (Lit 0w)
    (DecBytestring m) sa = ((),sb) /\
  C = 32 + 32 * ((m + 31) DIV 32) /\ C < dimword (:256) /\
  m < dimword (:256) /\
  eval_operand (Var p) s = SOME dw /\ eval_operand src s = SOME sw /\
  abi_decode_load CALLDATALOAD sw s = n2w len /\ len <= m /\
  fresh_vars_wrt sa s /\ ptr_covers G tn p s C /\
  op_taint tn src = {} /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?s' G' tn'.
    run_inst_seq (emitted_insts sa sb) s =
      OK (s' with vs_inst_idx := s.vs_inst_idx) /\
    ~s'.vs_halted /\ s'.vs_current_bb = sb.cs_current_bb /\
    s'.vs_inst_idx = LENGTH sb.cs_current_insts /\
    eval_operand (Var p) s' = SOME dw /\ eval_operand src s' = SOME sw /\
    s'.vs_allocas = s.vs_allocas /\ s'.vs_alloca_next = s.vs_alloca_next /\
    ptr_covers G' tn' p s' C /\
    (!i. w2n dw <= i /\ i < w2n dw + C ==> i NOTIN tn'.t_mem) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem SUBSET tn.t_mem /\
    ((!fuel. ptr_safe_run D lo fuel ctx fn PG G' tn' s') ==>
     !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >>
  `not_fresh_at sa p /\ (!q. src = Var q ==> not_fresh_at sa q)` by
    (Cases_on `src` >>
     gvs[not_fresh_at_def, fresh_vars_wrt_def, eval_operand_def, lookup_var_def,
       arithmeticTheory.GREATER_EQ] >>
     metis_tac[FLOOKUP_DEF, optionTheory.NOT_SOME_NONE]) >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  Cases_on `abi_decode_count_guard CALLDATALOAD src m sa` >>
  rename1 `abi_decode_count_guard CALLDATALOAD src m sa = (count_op,sg)` >>
  drule_all abi_decode_count_guard_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sg) s = OK guarded` >>
  `eval_operand (Var p) guarded = SOME dw /\ eval_operand src guarded = SOME sw` by metis_tac[] >>
  `?actual. run_inst_seq (emitted_insts sa sb) s = OK actual` by
    (drule calldata_bytestring_decoder_instructions >> strip_tac >>
     drule abi_decode_count_guard_shape >> strip_tac >>
     `emitted_insts sa sb = emitted_insts sa sg ++
       [mk_inst (sa.cs_next_id + 4) CALLDATACOPY [Var p;src;Lit (n2w C)] []]` by
       (qpat_x_assum `abi_decode_count_guard _ _ _ _ = _` mp_tac >>
        simp[abi_decode_count_guard_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def, emit_op_def, emit_void_def, emit_inst_def,
          fresh_var_def, fresh_id_def, emit_def, APPEND_ASSOC] >>
        strip_tac >> gvs[emitted_insts_def, DROP_PREFIX, APPEND_ASSOC]) >>
     qpat_assum `run_inst_seq (emitted_insts sa sg) s = _`
       (mp_then Any mp_tac run_inst_seq_append) >>
     disch_then (qspec_then
       `[mk_inst (sa.cs_next_id + 4) CALLDATACOPY [Var p;src;Lit (n2w C)] []]` mp_tac) >>
     simp[run_inst_seq_def, step_inst_base_def, mk_inst_def, eval_operand_def] >>
     metis_tac[]) >>
  irule calldata_bytestring_overwrite_endpoint_core >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`len`,`m`] >> simp[] >>
  `len < dimword(:256)` by decide_tac >> simp[]
QED

Theorem calldata_bytestring_decoder_prefix:
  compile_abi_decode_to_buf (Var p) src CALLDATALOAD (Lit 0w)
    (DecBytestring m) sa = ((),sb) /\
  C = 32 + 32 * ((m + 31) DIV 32) /\ C < dimword (:256) /\
  m < dimword (:256) /\
  eval_operand (Var p) s = SOME dw /\ eval_operand src s = SOME sw /\
  abi_decode_load CALLDATALOAD sw s = n2w len /\ len <= m /\
  fresh_vars_wrt sa s /\ ptr_covers G tn p s C /\
  op_taint tn src = {} /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?s' G' tn'.
    run_inst_seq (emitted_insts sa sb) s =
      OK (s' with vs_inst_idx := s.vs_inst_idx) /\
    ~s'.vs_halted /\ s'.vs_current_bb = sb.cs_current_bb /\
    s'.vs_inst_idx = LENGTH sb.cs_current_insts /\
    eval_operand (Var p) s' = SOME dw /\ eval_operand src s' = SOME sw /\
    s'.vs_allocas = s.vs_allocas /\ s'.vs_alloca_next = s.vs_alloca_next /\
    ptr_covers G' tn' p s' C /\
    (!i. w2n dw <= i /\ i < w2n dw + C ==> i NOTIN tn'.t_mem) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    tn'.t_imm = tn.t_imm /\
    ((!fuel. ptr_safe_run D lo fuel ctx fn PG G' tn' s') ==>
     !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >> drule_all calldata_bytestring_decoder_prefix_framed >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`s'`, `G'`, `tn'`] >> simp[]
QED

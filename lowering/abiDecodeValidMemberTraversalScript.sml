(* Actual-run setup for allocated decoder member traversal. *)
Theory abiDecodeValidMemberTraversal
Ancestors
  abiDecoderComplexGuard abiDecoderComplexHead abiEncoder
  bodyPtrBopScalarSeq bodyPtrBopScalarOutcome entryDecoderHistoryFrame
  fragGasCopyLoop fragGasSeqPtr fragExecMem instMemFrontier memSafeRun ptrDiscipline allocasBelowFmpUpdatesProps
  fragGasCopySeqLiftProps
  emitHelper emitHelperProps exprLoweringProps compileEnv loweringStateRelDefs
  abiDecodePtrMemberFrame abiValidAllocatedMembers abiValidAllocatedContract abiValidMembers
  abiDecoderMemberInfos abiDecoderContract abiMalformedRecursiveInterface
  abiDecoderTypedCompose abiDecoderLoop abiMalformedSiteFrame
  fragGasOriginPtr bodyPtrDefs allocaHistory
  vyperABI valueEncoding valueEncodingDefs abiDecoderEmpty
  venomState venomInst finite_map pred_set list rich_list arithmetic
  abiDecoderMemberSetup exprSimAbiDecodeCompositePrefix bodyPtrBopHashSuffix
  abiDecodeStaticProps decoderNavigationPtr fragExec venomExecSemantics words
  stateRelProj allocaSiteResource decoderMemberPrefixPtr ghostPcTransportPtr
  exprSimConvertBytes instIdxIndep abiValidAllocatedNavigate
  abiValidAllocatedSource abiDecoderMemberCode abiDecoderSequenceReach
  abiDecoderMemberCons abiDecoderCoherence abiDecodeRanges
  abiValidAllocatedMemberJoin abiValidAllocatedMemberEntry abiDecoderReentry
  decoderGhostFramePtr valueEncodingTyping valueEncodingProofs
  robustCopyTransportPtr exprSimProps vyperTypeABI bodyFullHashKeccakFixed
  abiDecoderComplexExecute abiMalformedMemberSetup abiMalformedConstructorContract
  abiDecoderDynamicLoopSetup freshWrites abiValidAllocatedComplex
  abiDecoderMembers contractABI abiDecoderStruct abiDecoderFixedMemory
  abiValidAggregateHeads vyperABIValid exprSimAggregateEncoding vyperValue

Theorem member_guard_scalar_code[local]:
  abi_decode_complex_head_guard pos hi n sa = ((),sb) ==>
  ?B. bop_scalar_seq {x | not_fresh_at sa x} ({pos;hi} UNION IMAGE Lit UNIV)
        (emitted_insts sa sb) B
Proof
  Cases_on `hi = Lit 0w`
  >- simp[abi_decode_complex_head_guard_def, comp_return_def,
          emitted_insts_def] >>
  simp[abi_decode_complex_head_guard_def, compile_abi_decode_range_check_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def,
       emit_void_def, fresh_var_def, fresh_id_def, emit_def, emitted_insts_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND] >>
  rpt (CHANGED_TAC (simp[Once bop_scalar_seq_def, mk_inst_def, IN_IMAGE,
    not_fresh_at_def, ASCIInumbersTheory.toString_inj]))
QED

Theorem member_scalar_actual_run[local]:
  bop_scalar_seq {x | not_fresh_at sa x} A (emitted_insts sa sb) B /\
  sb.cs_current_bb = sa.cs_current_bb /\ isPREFIX sa.cs_current_insts sb.cs_current_insts /\
  fn_has_code sa sb func /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  (!op. op IN A ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
  allocas_from lo s /\ run_inst_seq (emitted_insts sa sb) s = OK u ==>
  ?G' tn'.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s with vs_inst_idx := LENGTH sa.cs_current_insts,G,tn) []
      (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),G',tn')) /\
    (!op. op IN B ==> op_prov G' op = NONE /\ op_taint tn' op = {}) /\
    u = s with vs_vars := u.vs_vars /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\ allocas_from lo u
Proof
  strip_tac >>
  drule_all entry_straight_line_code_slice >> strip_tac >>
  drule_all bop_scalar_seq_runtime_frame >> strip_tac >>
  qabbrev_tac `sn = s with vs_inst_idx := LENGTH sa.cs_current_insts` >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp sn` by
    (simp[Abbr `sn`, allocas_below_fmp_def] >>
     fs[allocas_below_fmp_def]) >>
  qabbrev_tac `un = u with vs_inst_idx := LENGTH sa.cs_current_insts` >>
  `isPREFIX (emitted_insts sa sb) (DROP sn.vs_inst_idx bb.bb_instructions)` by
    simp[Abbr `sn`, IS_PREFIX_APPEND] >>
  `sn.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts` by
    (fs[Abbr `sn`, IS_PREFIX_APPEND, emitted_insts_def] >> simp[DROP_LENGTH_APPEND]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    (drule bop_scalar_seq_opcodes >> simp[EVERY_MEM]) >>
  `run_inst_seq (emitted_insts sa sb) sn = OK un` by
    simp[Abbr `sn`, Abbr `un`, run_inst_seq_inst_idx, exec_result_map_def] >>
  `~sn.vs_halted /\ sn.vs_current_bb = sa.cs_current_bb /\ allocas_from lo sn` by
    (fs[Abbr `sn`, allocas_from_def] >> (metis_tac[Abbr `sn`, allocas_from_def])) >>
  qpat_x_assum `run_inst_seq (emitted_insts sa sb) s = OK u` kall_tac >>
  drule_all bop_scalar_seq_run >>
  disch_then (fn th => assume_tac th >>
    qspecl_then [`func`, `PG`, `ARB`] strip_assume_tac th) >>
  rename1 `inst_seq_ptr _ 0 ctx func PG G tn _ sn Gf tnf` >>
  `!D. inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) sn Gf tnf` by
    (gen_tac >>
     qpat_assum `!fn PG D. _` (qspecl_then [`func`, `PG`, `D`] strip_assume_tac) >>
     metis_tac[inst_seq_ptr_ghost_unique]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
               i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) (emitted_insts sa sb)` by
    (drule bop_scalar_seq_opcodes >>
     simp[EVERY_MEM] >> strip_tac >> gen_tac >> strip_tac >>
     drule_all bop_scalar_seq_outputs >> strip_tac >> gvs[]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) sn` by
    (irule run_inst_seq_mem_ok_every >> simp[EVERY_MEM] >>
     rpt gen_tac >> strip_tac >> gen_tac >>
     drule_all bop_scalar_seq_outputs >> strip_tac >>
     conj_tac >- (irule below_frontier_no_ranges >> gvs[]) >>
     irule inst_dload_in_section_other >> gvs[]) >>
  `lookup_block sn.vs_current_bb func.fn_blocks = SOME bb` by simp[Abbr `sn`] >>
  `(ctx_has_dalloca ctx ==> !pre i post v.
      emitted_insts sa sb = pre ++ i::post /\ run_inst_seq pre sn = OK v ==>
      unitTransformDefs$dalloca_no_wrap i v)` by
    (rpt strip_tac >> irule dalloca_no_wrap_non_dalloca >>
     `MEM i (emitted_insts sa sb)` by fs[MEM_APPEND] >>
     drule_all bop_scalar_seq_outputs >> strip_tac >> gvs[]) >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (sn,G,tn) []
      (OK (un with vs_inst_idx := sn.vs_inst_idx + LENGTH (emitted_insts sa sb)),Gf,tnf) /\
      allocas_from lo un` by
    (rpt gen_tac >>
     match_mp_tac (Q.INST [`code` |-> `emitted_insts sa sb`, `bb` |-> `bb`]
       run_inst_seq_origin_ptr_lift) >>
     asm_rewrite_tac[]) >>
  qexistsl_tac [`Gf`, `tnf`] >>
  fs[Abbr `sn`, Abbr `un`, FORALL_AND_THM, lookup_var_def, op_taint_def, allocas_from_def] >>
  metis_tac[]
QED

Theorem member_scalar_guard_actual_run[local]:
  abi_decode_complex_head_guard pos hi n sa = ((),sb) /\
  fn_has_code sa sb func /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  op_prov G pos = NONE /\ op_prov G hi = NONE /\
  op_taint tn pos = {} /\ op_taint tn hi = {} /\
  allocas_from lo s /\ run_inst_seq (emitted_insts sa sb) s = OK u ==>
  ?G' tn'.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),G',tn')) /\
    u = s with vs_vars := u.vs_vars /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\ allocas_from lo u
Proof
  strip_tac >> drule member_guard_scalar_code >> strip_tac >>
  drule abi_decoder_complex_guard_code >> strip_tac >>
  `!op. op IN {pos;hi} UNION IMAGE Lit UNIV ==>
        op_prov G op = NONE /\ op_taint tn op = {}` by
    (simp[IN_UNION, IN_IMAGE] >> rpt strip_tac >>
     gvs[op_prov_def, op_taint_def]) >>
  drule_all member_scalar_actual_run >>
  disch_then (qspec_then `PG` (qx_choose_then `H` (qx_choose_then `z` strip_assume_tac))) >>
  `s with vs_inst_idx := LENGTH sa.cs_current_insts = s` by
    (qpat_assum `s.vs_inst_idx = _` (once_rewrite_tac o single o SYM) >> simp[]) >>
  qexistsl_tac [`H`,`z`] >> fs[]
QED

(* Conditional child contract, generalized over its actual entry. *)
val decode_child_run = ``\ty tv.
 !v ctx func cenv cx es st en source hi pos output B L xs p d dstid live ceiling s H0.
 abi_valid_allocated_entry H0 ce env sf ty tv v ctx func cenv cx es
   st en (Var source) hi pos (Var output) B L xs p d dstid live ceiling s ==>
 !G tn PG lo.
 abi_decode_ptr_window G tn s source (n2w B) L /\
 ptr_covers G tn output s (type_memory_bytes ce ty) /\
 op_prov G pos = NONE /\ op_prov G hi = NONE /\
 op_taint tn pos = {} /\ op_taint tn hi = {} /\
 allocas_from lo s /\ lo <= s.vs_alloca_next /\ alloca_history func s ==>
 ?u G' tn'.
 abi_valid_allocated_post tv v ctx func cenv cx es st en ceiling dstid
   d (type_memory_bytes ce ty) s u /\
 u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
 u.vs_call_ctx = s.vs_call_ctx /\ u.vs_immutables = s.vs_immutables /\
 (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
   (s,G,tn) [] (OK u,G',tn')) /\
 ptr_covers G' tn' output u (type_memory_bytes ce ty) /\
 abi_decode_ptr_window G' tn' u source (n2w B) L /\
 (!mem. mem_agree_outside tn'.t_mem u.vs_memory mem ==> val_in_memory tv v d mem) /\
 (!x. abi_decoder_operand_live st.cs_next_var (Var x) ==>
   FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
 tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
 (!a. ~(d <= a /\ a < d+type_memory_bytes ce ty) /\
   ~abi_malformed_site_range (abi_malformed_scratch_sites st en func) s u a 1 ==>
   (a IN tn'.t_mem <=> a IN tn.t_mem)) /\
 alloca_history func u /\ allocas_from lo u /\ lo <= u.vs_alloca_next``;

(* The induction keeps the whole destination allocation and the source
   window live, even when the completed member interval is empty. *)
val decode_members_run = ``\tys tvs.
 !vs ctx func cenv cx es st en source hi pos output B L xs p d outsz ao vo dstid live ceiling s H0.
 abi_valid_allocated_members_entry H0 ce env sf tys tvs vs ctx func cenv cx es
   st en (Var source) hi pos (Var output) B L xs p d outsz ao vo dstid live ceiling s ==>
 !G tn PG lo.
 abi_decode_ptr_window G tn s source (n2w B) L /\
 ptr_covers G tn output s outsz /\
 op_prov G pos = NONE /\ op_prov G hi = NONE /\
 op_taint tn pos = {} /\ op_taint tn hi = {} /\
 allocas_from lo s /\ lo <= s.vs_alloca_next /\ alloca_history func s ==>
 ?u G' tn'.
 abi_valid_allocated_members_post tvs vs ctx func cenv cx es st en ceiling dstid
   (d+vo) (type_memory_size_list tvs) s u /\
 u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
 u.vs_call_ctx = s.vs_call_ctx /\ u.vs_immutables = s.vs_immutables /\
 (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
   (s,G,tn) [] (OK u,G',tn')) /\
 ptr_covers G' tn' output u outsz /\
 abi_decode_ptr_window G' tn' u source (n2w B) L /\
 (!mem. mem_agree_outside tn'.t_mem u.vs_memory mem ==>
   tuple_in_memory vs tvs (d+vo) mem) /\
 (!x. abi_decoder_operand_live st.cs_next_var (Var x) ==>
   FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
 tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
 (!a. ~(d+vo <= a /\ a < d+vo+type_memory_size_list tvs) /\
   ~abi_malformed_site_range (abi_malformed_scratch_sites st en func) s u a 1 ==>
   (a IN tn'.t_mem <=> a IN tn.t_mem)) /\
 alloca_history func u /\ allocas_from lo u /\ lo <= u.vs_alloca_next``;

Theorem decoder_joint_members_nil[local]:
  (^decode_members_run) [] []
Proof
  BETA_TAC >>
  simp_tac bool_ss [abi_valid_allocated_members_entry_def,
    abi_decoder_member_infos_def, Once compile_abi_decode_to_buf_def,
    comp_return_def, abi_decode_members_def, Once abi_to_vyper_def,
    MAP, SUM, LIST_REL_EL_EQN] >>
  rpt gen_tac >> strip_tac >> gvs[] >> rpt gen_tac >> strip_tac >>
  qexistsl_tac [`s`, `G`, `tn`] >>
  simp[abi_valid_allocated_members_post_def, val_in_memory_def,
    abi_decode_sim_refl, abi_valid_allocated_frame_refl,
    gas_origin_ptr_path_rules] >>
  fs[abi_malformed_entry_def] >> irule abi_malformed_resource_refl >>
  metis_tac[]
QED

Theorem allocated_member_setup_split[local]:
  abi_decode_member_setup dst src MLOAD base_op hi dyn ao vo st = (ops,ready) /\
  run_inst_seq (emitted_insts st ready) s = OK t ==>
  ?mid r. compile_getelemptr_abi src dyn ao MLOAD base_op hi st = (FST ops,mid) /\
    emit_op ADD [dst;Lit (n2w vo)] mid = (SND ops,ready) /\
    mid.cs_blocks = st.cs_blocks /\ mid.cs_current_bb = st.cs_current_bb /\
    inst_extends st mid /\ inst_extends mid ready /\
    run_inst_seq (emitted_insts st mid) s = OK r /\
    run_inst_seq (emitted_insts mid ready) r = OK t
Proof
  strip_tac >>
  qpat_x_assum `abi_decode_member_setup _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [abi_decode_member_setup_def, comp_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `compile_getelemptr_abi _ _ _ _ _ _ st = (_,mid)` >>
  rename1 `emit_op ADD _ mid = (_,ready)` >>
  drule abi_decode_member_pointer_prefix_shape >> strip_tac >>
  `inst_extends mid ready` by metis_tac[inst_extends_emit_op] >>
  `emitted_insts st ready = emitted_insts st mid ++ emitted_insts mid ready` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  fs[bop_run_inst_seq_append_ok] >> metis_tac[]
QED

Theorem allocated_member_head_add_origin[local]:
  emit_op ADD [pos;Lit (n2w ao)] sa = (out,sb) /\
  fn_has_code sa sb func /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand pos s = SOME (n2w p) /\ op_taint tn pos = {} /\
  op_prov G pos = NONE /\ allocas_from lo s /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?G' tn'. (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),G',tn')) /\
    eval_operand out t = SOME (n2w (p+ao)) /\
    op_taint tn' out = {} /\ op_prov G' out = NONE /\
    t = s with vs_vars := t.vs_vars /\ allocas_from lo t /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!q. not_fresh_at sa q ==> lookup_var q t = lookup_var q s /\
      FLOOKUP G' q = FLOOKUP G q /\ op_taint tn' (Var q) = op_taint tn (Var q))
Proof
  strip_tac >>
  `eval_operand (Lit (n2w ao)) s = SOME (n2w ao) /\
   op_taint tn (Lit (n2w ao)) = {} /\ op_prov G (Lit (n2w ao)) = NONE` by
    simp[eval_operand_def, op_taint_def, op_prov_def] >>
  drule_all (SRULE [] (Q.SPEC `ADD` emit_scalar_binop_endpoint_ptr_origin_core)) >>
  disch_then (qspecl_then [`ARB`,`ARB`,`ctx`,`PG`,`ARB`]
    (qx_choose_then `H` (qx_choose_then `u` strip_assume_tac))) >>
  `t = update_var (STRING #"%" (toString sa.cs_next_var)) (n2w (p+ao)) s` by
    (drule_all buffer_emit_add_run >> simp[word_add_n2w]) >>
  qexistsl_tac [`H`,`u`] >>
  `eval_operand out t = SOME (n2w (p+ao))` by
    (drule emitted_insts_emit_op >>
     simp[eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  fs[update_var_def, allocas_from_def] >>
  metis_tac[]
QED

Theorem allocated_member_head_read_bound[local]:
  abi_malformed_entry H ctx func cenv cx es st sites dstid live
    (Var source) hi pos dst B L xs p d n s /\
  abi_decode_ptr_window G tn s source (n2w B) L /\
  p + ao + 32 <= L ==>
  B + (p + ao) < dimword (:256) /\
  B + (p + ao) + 32 <= s.vs_alloca_next /\
  (!i. B + (p + ao) <= i /\ i < B + (p + ao) + 32 ==> i NOTIN tn.t_mem)
Proof
  strip_tac >>
  fs[abi_malformed_entry_def, abi_malformed_allocated_window_def,
     abi_decode_ptr_window_def] >>
  drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
  drule_all alloca_site_registered_below >> strip_tac >>
  `w2n (n2w B : bytes32) = B` by (simp[w2n_n2w, LESS_MOD] >> decide_tac) >>
  fs[] >> rpt strip_tac >> TRY decide_tac >>
  first_x_assum irule >> decide_tac
QED

(* The guard code follows the offset load; its success is not inferred
   from the source value. Split the supplied OK run to get every cut. *)
Theorem allocated_dynamic_source_split[local]:
  compile_getelemptr_abi pos T ao MLOAD (Var source) hi sa = (out,sb) /\
  hi <> Lit 0w /\ run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?head c1 addr c2 off c3 under c4 test c5 c6 r1 r2 r3.
    emit_op ADD [pos; Lit (n2w ao)] sa = (head,c1) /\
    emit_op ADD [Var source;head] c1 = (addr,c2) /\
    emit_op MLOAD [addr] c2 = (off,c3) /\
    emit_op ADD [pos;off] c3 = (out,c4) /\
    emit_op LT [out;pos] c4 = (under,c5) /\
    emit_op ISZERO [under] c5 = (test,c6) /\
    emit_void ASSERT [test] c6 = ((),sb) /\
    inst_extends sa c1 /\ inst_extends c1 c2 /\ inst_extends c2 c3 /\
    inst_extends c3 sb /\
    run_inst_seq (emitted_insts sa c1) s = OK r1 /\
    run_inst_seq (emitted_insts c1 c2) r1 = OK r2 /\
    run_inst_seq (emitted_insts c2 c3) r2 = OK r3 /\
    run_inst_seq (emitted_insts c3 sb) r3 = OK t
Proof
  strip_tac >>
  qpat_x_assum `compile_getelemptr_abi _ _ _ _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [compile_getelemptr_abi_def, compile_abi_dec_addr_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM,
    TypeBase.distinct_of ``:operand``] >>
  rpt (pairarg_tac >> fs[]) >> strip_tac >> gvs[] >>
  qpat_x_assum `comp_bind _ _ _ = _` mp_tac >>
  simp_tac bool_ss [comp_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> fs[]) >> strip_tac >> gvs[] >>
  rename1 `emit_op ADD [pos; Lit (n2w ao)] sa = (_,c1)` >>
  rename1 `emit_op ADD [Var source;_] c1 = (_,c2)` >>
  rename1 `emit_op MLOAD [_] c2 = (_,c3)` >>
  rename1 `emit_op ADD [pos;_] c3 = (_,c4)` >>
  rename1 `emit_op LT _ c4 = (_,c5)` >>
  rename1 `emit_op ISZERO _ c5 = (_,c6)` >>
  rename1 `emit_void ASSERT _ c6 = ((),sb)` >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `inst_extends c3 sb` by metis_tac[inst_extends_trans] >>
  `emitted_insts sa sb = emitted_insts sa c1 ++
    (emitted_insts c1 c2 ++ (emitted_insts c2 c3 ++ emitted_insts c3 sb))` by
    (`emitted_insts sa sb = emitted_insts sa c1 ++ emitted_insts c1 sb /\
      emitted_insts c1 sb = emitted_insts c1 c2 ++ emitted_insts c2 sb /\
      emitted_insts c2 sb = emitted_insts c2 c3 ++ emitted_insts c3 sb` suffices_by simp[] >>
     rpt conj_tac >> irule emitted_insts_append >>
     metis_tac[inst_extends_def, inst_extends_trans]) >>
  fs[bop_run_inst_seq_append_ok] >> metis_tac[]
QED

(* MLOAD is lifted from the physical cut; the cursor update does not
   alter the address, the clean footprint, or the allocation frontier. *)
Theorem allocated_member_read_origin[local]:
  emit_op MLOAD [Var q] sa = (out,sb) /\
  lookup_var q s = SOME a /\ ptr_covers G tn q s 32 /\
  w2n a + 32 <= s.vs_alloca_next /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  fn_has_code sa sb func /\ allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb ==>
  ?H u. op_taint u out = {} /\ op_prov H out = NONE /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s with vs_inst_idx := LENGTH sa.cs_current_insts,G,tn) []
       (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),H,u)) /\
    t = s with vs_vars := t.vs_vars /\ allocas_from lo t /\
    tn.t_mem = u.t_mem /\ tn.t_stor = u.t_stor /\
    tn.t_trans = u.t_trans /\ tn.t_imm = u.t_imm /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
       FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `eval_operand (Var q) s = SOME a` by simp[eval_operand_def] >>
  `t = s with vs_vars := t.vs_vars` by
    (drule_all convert_mload_run >> fs[update_var_def]) >>
  qabbrev_tac `sn = s with vs_inst_idx := LENGTH sa.cs_current_insts` >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp sn` by
    (strip_tac >>
     qpat_assum `ctx_has_dalloca ctx` (fn mode =>
       qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s`
         (fn bound => mp_tac (MP bound mode))) >>
     simp[Abbr `sn`, allocas_below_fmp_def]) >>
  qabbrev_tac `tnr = t with vs_inst_idx := LENGTH sa.cs_current_insts` >>
  `run_inst_seq (emitted_insts sa sb) sn = OK tnr` by
    (drule emit_op_run_pc >> simp[is_terminator_def] >>
     disch_then (qspecl_then [`s`,`LENGTH sa.cs_current_insts`] mp_tac) >>
     simp[exec_result_map_def, Abbr `sn`, Abbr `tnr`]) >>
  `lookup_var q sn = SOME a /\ ptr_covers G tn q sn 32 /\
   allocas_from lo sn /\ ~sn.vs_halted /\ sn.vs_current_bb = sa.cs_current_bb /\
   sn.vs_inst_idx = LENGTH sa.cs_current_insts /\ w2n a + 32 <= sn.vs_alloca_next` by
    (simp[Abbr `sn`, lookup_var_def, allocas_from_def] >> (metis_tac[Abbr `sn`, lookup_var_def, allocas_from_def])) >>
  qpat_x_assum `run_inst_seq (emitted_insts sa sb) s = OK t` kall_tac >>
  drule_all emit_mload_clean_endpoint_ptr_origin_core >>
  disch_then (qspecl_then [`ARB`,`ARB`,`ctx`,`PG`,`ARB`]
    (qx_choose_then `H` (qx_choose_then `u` strip_assume_tac))) >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (sn,G,tn) []
     (OK (tnr with vs_inst_idx := LENGTH sb.cs_current_insts),H,u)` by
    (rpt gen_tac >> first_x_assum irule >> simp[]) >>
  qexistsl_tac [`H`,`u`] >>
  fs[Abbr `sn`, Abbr `tnr`, lookup_var_def, allocas_from_def] >> metis_tac[]
QED

Theorem allocated_member_address_read_origin[local]:
  emit_op ADD [Var source;head] c1 = (addr,c2) /\
  emit_op MLOAD [addr] c2 = (off,c3) /\
  run_inst_seq (emitted_insts c1 c2) r1 = OK r2 /\
  run_inst_seq (emitted_insts c2 c3) r2 = OK r3 /\
  fn_has_code c1 c2 func /\ fn_has_code c2 c3 func /\
  allocas_from lo r1 /\ (ctx_has_dalloca ctx ==> allocas_below_fmp r1) /\ ~r1.vs_halted /\
  r1.vs_current_bb = c1.cs_current_bb /\
  lookup_var source r1 = SOME (n2w B) /\ ptr_covers G tn source r1 L /\
  eval_operand head r1 = SOME (n2w h) /\ op_taint tn head = {} /\ op_prov G head = NONE /\
  h + 32 <= L /\ B + h < dimword (:256) /\ B + h + 32 <= r1.vs_alloca_next /\
  (!i. B + h <= i /\ i < B + h + 32 ==> i NOTIN tn.t_mem) ==>
  ?H u. op_taint u off = {} /\ op_prov H off = NONE /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (r1 with vs_inst_idx := LENGTH c1.cs_current_insts,G,tn) []
      (OK (r3 with vs_inst_idx := LENGTH c3.cs_current_insts),H,u)) /\
    r3 = r1 with vs_vars := r3.vs_vars /\ allocas_from lo r3 /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. not_fresh_at c1 x ==> lookup_var x r3 = lookup_var x r1 /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `w2n (n2w B : bytes32) = B /\ w2n (n2w (B+h) : bytes32) = B+h` by
    (simp[w2n_n2w, LESS_MOD] >> decide_tac) >>
  `w2n (n2w B : bytes32) + h < dimword (:256)` by simp[] >>
  drule_all member_navigation_emit_pointer_pc_uniform_origin >>
  disch_then (qspec_then `PG` (qx_choose_then `q`
    (qx_choose_then `G2` (qx_choose_then `tn2` strip_assume_tac)))) >>
  `r2 = r1 with vs_vars := r2.vs_vars` by
    (qpat_assum `emit_op ADD _ c1 = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     gvs[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
         exec_pure2_def, eval_operand_def, update_var_def, emitted_insts_emit_op]) >>
  `allocas_from lo r2 /\ ~r2.vs_halted /\ r2.vs_current_bb = c2.cs_current_bb /\
   w2n (n2w (B+h) : bytes32) + 32 <= r2.vs_alloca_next` by
    ((qpat_assum `emit_op ADD _ c1 = _` (mp_then Any mp_tac emit_op_same_blocks) >>
     simp[same_blocks_def] >> strip_tac >>
     qpat_assum `r2 = r1 with vs_vars := r2.vs_vars` (fn th => once_rewrite_tac [th]) >>
     fs[allocas_from_def] >> (gvs[same_blocks_def, allocas_from_def, emit_op_same_blocks]))) >>
  `B MOD dimword (:256) = B` by (irule LESS_MOD >> decide_tac) >>
  `!i. w2n (n2w (B+h) : bytes32) <= i /\ i < w2n (n2w (B+h) : bytes32) + 32 ==>
     i NOTIN tn2.t_mem` by simp[] >>
  `!x. not_fresh_at c1 x ==> not_fresh_at c2 x` by
    (qpat_assum `emit_op ADD _ c1 = _` (mp_then Any mp_tac emitted_insts_emit_op) >>
     simp[not_fresh_at_def] >> metis_tac[DECIDE ``a+1 <= n ==> a <= n``]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp r2` by
    (qpat_assum `r2 = r1 with vs_vars := r2.vs_vars` (fn th => once_rewrite_tac [th]) >>
     rewrite_tac[allocas_below_fmp_updates] >> first_assum ACCEPT_TAC) >>
  gvs[] >>
  qpat_assum `ptr_covers G2 tn2 q r2 32`
    (mp_then Any mp_tac allocated_member_read_origin) >>
  disch_then drule >>
  disch_then (drule_at (Pat `lookup_var q r2 = SOME _`)) >>
  disch_then (qpat_assum `run_inst_seq (emitted_insts c2 c3) r2 = OK r3` o
    mp_then Any mp_tac) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `allocas_from _ _`)) >>
  disch_then (drule_at (Pat `ctx_has_dalloca ctx ==> allocas_below_fmp r2`)) >>
  disch_then (qspec_then `PG` mp_tac) >>
  (impl_tac >- (simp[w2n_n2w, LESS_MOD] >> metis_tac[])) >>
  disch_then (qx_choose_then `H` (qx_choose_then `u` strip_assume_tac)) >>
  qexistsl_tac [`H`,`u`] >> simp[] >>
  conj_tac
  >- (rpt gen_tac >>
      qpat_assum `!D explicit. gas_origin_ptr_path _ (_,G,tn) _ _`
        (qspecl_then [`D`,`explicit`] mp_tac) >>
      qpat_assum `!D explicit. gas_origin_ptr_path _ (_,G2,tn2) _ _`
        (qspecl_then [`D`,`explicit`] mp_tac) >>
      POP_ASSUM_LIST (K all_tac) >> metis_tac[gas_origin_ptr_path_append, APPEND_NIL]) >>
  reverse conj_tac >- metis_tac[] >>
  qpat_assum `r3 = r2 with vs_vars := r3.vs_vars`
    (fn th => once_rewrite_tac [th]) >>
  qpat_assum `r2 = r1 with vs_vars := r2.vs_vars`
    (fn th => once_rewrite_tac [th]) >> simp[]
QED

Theorem allocated_dynamic_suffix_scalar[local]:
  emit_op ADD [pos;off] c3 = (out,c4) /\
  emit_op LT [out;pos] c4 = (under,c5) /\
  emit_op ISZERO [under] c5 = (test,c6) /\
  emit_void ASSERT [test] c6 = ((),sb) ==>
  sb.cs_current_bb = c3.cs_current_bb /\
  isPREFIX c3.cs_current_insts sb.cs_current_insts /\
  bop_scalar_seq {x | not_fresh_at c3 x} {pos;off}
    (emitted_insts c3 sb) {test;under;out;pos;off}
Proof
  strip_tac >>
  conj_tac >- (imp_res_tac emit_op_same_blocks >> imp_res_tac emit_void_same_blocks >>
    fs[same_blocks_def]) >>
  conj_tac >- (imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
    `inst_extends c3 sb` by metis_tac[inst_extends_trans] >>
    fs[inst_extends_def, IS_PREFIX_APPEND]) >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac emitted_insts_emit_void >>
  `emitted_insts c3 sb = emitted_insts c3 c4 ++
    (emitted_insts c4 c5 ++ (emitted_insts c5 c6 ++ emitted_insts c6 sb))` by
    (`emitted_insts c3 sb = emitted_insts c3 c4 ++ emitted_insts c4 sb /\
      emitted_insts c4 sb = emitted_insts c4 c5 ++ emitted_insts c5 sb /\
      emitted_insts c5 sb = emitted_insts c5 c6 ++ emitted_insts c6 sb` suffices_by simp[] >>
     imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
     rpt conj_tac >> irule emitted_insts_append >>
     metis_tac[inst_extends_def, inst_extends_trans]) >>
  fs[] >>
  rpt (CHANGED_TAC (simp[Once bop_scalar_seq_def, mk_inst_def,
    not_fresh_at_def, ASCIInumbersTheory.toString_inj]))
QED

Theorem allocated_dynamic_suffix_origin[local]:
  emit_op ADD [pos;off] c3 = (out,c4) /\
  emit_op LT [out;pos] c4 = (under,c5) /\
  emit_op ISZERO [under] c5 = (test,c6) /\
  emit_void ASSERT [test] c6 = ((),sb) /\
  run_inst_seq (emitted_insts c3 sb) r3 = OK t /\
  fn_has_code c3 sb func /\ (ctx_has_dalloca ctx ==> allocas_below_fmp r3) /\ ~r3.vs_halted /\
  r3.vs_current_bb = c3.cs_current_bb /\ allocas_from lo r3 /\
  op_taint tn pos = {} /\ op_prov G pos = NONE /\
  op_taint tn off = {} /\ op_prov G off = NONE ==>
  ?H u. op_taint u out = {} /\ op_prov H out = NONE /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (r3 with vs_inst_idx := LENGTH c3.cs_current_insts,G,tn) []
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),H,u)) /\
    t = r3 with vs_vars := t.vs_vars /\ allocas_from lo t /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. not_fresh_at c3 x ==> lookup_var x t = lookup_var x r3 /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all allocated_dynamic_suffix_scalar >> strip_tac >>
  `!op. op IN {pos;off} ==> op_prov G op = NONE /\ op_taint tn op = {}` by
    (simp[] >> metis_tac[]) >>
  drule_all member_scalar_actual_run >>
  disch_then (qspec_then `PG` (qx_choose_then `H` (qx_choose_then `u` strip_assume_tac))) >>
  qexistsl_tac [`H`,`u`] >> simp[] >>
  qpat_assum `!op. op IN _ ==> _` (qspec_then `out` mp_tac) >> simp[]
QED

(* Lift dynamic member navigation without replaying its offset load. *)
Theorem allocated_dynamic_source_origin[local]:
  compile_getelemptr_abi pos T ao MLOAD (Var source) hi sa = (out,sb) /\
  hi <> Lit 0w /\ run_inst_seq (emitted_insts sa sb) s = OK t /\
  fn_has_code sa sb func /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  allocas_from lo s /\ abi_decode_ptr_window G tn s source (n2w B) L /\
  not_fresh_at sa source /\ (!x. pos = Var x ==> not_fresh_at sa x) /\
  eval_operand pos s = SOME (n2w p) /\ op_taint tn pos = {} /\ op_prov G pos = NONE /\
  p + ao + 32 <= L /\ B + (p+ao) < dimword (:256) /\
  B + (p+ao) + 32 <= s.vs_alloca_next ==>
  ?H u. op_taint u out = {} /\ op_prov H out = NONE /\
    sa.cs_next_var <= sb.cs_next_var /\ abi_decoder_operand_live sb.cs_next_var out /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),H,u)) /\
    t = s with vs_vars := t.vs_vars /\ allocas_from lo t /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all allocated_dynamic_source_split >> strip_tac >>
  imp_res_tac (REWRITE_RULE [cs_appends_def] (cj 2 cs_appends_emit_helpers)) >>
  imp_res_tac (REWRITE_RULE [cs_appends_def] (cj 3 cs_appends_emit_helpers)) >>
  `fn_has_code sa c1 func /\ fn_has_code c1 c2 func /\ fn_has_code c2 c3 func /\
   fn_has_code c3 sb func` by
    (`cs_extends c3 sb /\ cs_extends c2 sb /\ cs_extends c1 sb` by metis_tac[cs_extends_trans] >>
     mp_tac (Q.SPECL [`sa`,`c1`,`sb`,`func`] fn_has_code_split) >> simp[] >> strip_tac >>
     mp_tac (Q.SPECL [`c1`,`c2`,`sb`,`func`] fn_has_code_split) >> simp[] >> strip_tac >>
     mp_tac (Q.SPECL [`c2`,`c3`,`sb`,`func`] fn_has_code_split) >> simp[]) >>
  drule_all allocated_member_head_add_origin >>
  disch_then (qspec_then `PG` (qx_choose_then `G1` (qx_choose_then `tn1` strip_assume_tac))) >>
  `sa.cs_next_var <= c1.cs_next_var /\ sa.cs_next_var <= c3.cs_next_var` by
    (imp_res_tac emitted_insts_emit_op >> fs[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at c1 x /\ not_fresh_at c3 x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `~r1.vs_halted /\ r1.vs_current_bb = c1.cs_current_bb /\
   B + (p+ao) + 32 <= r1.vs_alloca_next` by
    (qpat_assum `r1 = s with vs_vars := r1.vs_vars` (fn th => once_rewrite_tac [th]) >>
     imp_res_tac emit_op_same_blocks >> fs[same_blocks_def]) >>
  `lookup_var source r1 = SOME (n2w B) /\ ptr_covers G1 tn1 source r1 L /\
   (!i. B + (p+ao) <= i /\ i < B + (p+ao) + 32 ==> i NOTIN tn1.t_mem)` by
    (`w2n (n2w B : bytes32) = B` by (simp[w2n_n2w, LESS_MOD] >> decide_tac) >>
     rpt conj_tac
     >- (fs[abi_decode_ptr_window_def] >> metis_tac[])
     >- (fs[abi_decode_ptr_window_def] >> irule decoderGhostFramePtrTheory.ptr_covers_frame >>
         qexistsl_tac [`G`,`s`,`tn`] >> simp[])
     >> fs[abi_decode_ptr_window_def] >> rpt strip_tac >>
     qpat_assum `!i. B <= i /\ i < B + L ==> _` irule >> decide_tac) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp r1` by
    (qpat_assum `r1 = s with vs_vars := r1.vs_vars` (fn th => once_rewrite_tac [th]) >>
     rewrite_tac[allocas_below_fmp_updates] >> first_assum ACCEPT_TAC) >>
  drule_all allocated_member_address_read_origin >>
  disch_then (qspec_then `PG` (qx_choose_then `G3` (qx_choose_then `tn3` strip_assume_tac))) >>
  `~r3.vs_halted /\ r3.vs_current_bb = c3.cs_current_bb` by
    (qpat_assum `r3 = r1 with vs_vars := r3.vs_vars` (fn th => once_rewrite_tac [th]) >>
     imp_res_tac emit_op_same_blocks >> fs[same_blocks_def]) >>
  `op_taint tn3 pos = {} /\ op_prov G3 pos = NONE` by
    (Cases_on `pos` >> gvs[op_taint_def,op_prov_def] >> metis_tac[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp r3` by
    (qpat_assum `r3 = r1 with vs_vars := r3.vs_vars` (fn th => once_rewrite_tac [th]) >>
     rewrite_tac[allocas_below_fmp_updates] >> first_assum ACCEPT_TAC) >>
  drule_all allocated_dynamic_suffix_origin >>
  disch_then (qspec_then `PG` (qx_choose_then `H` (qx_choose_then `u` strip_assume_tac))) >>
  `sa.cs_next_var <= sb.cs_next_var /\ c4.cs_next_var <= sb.cs_next_var` by
    (imp_res_tac emitted_insts_emit_op >> imp_res_tac emitted_insts_emit_void >> fs[]) >>
  `abi_decoder_operand_live sb.cs_next_var out` by
    (irule abiDecoderReentryTheory.abi_decoder_operand_live_mono >> qexists_tac `c4.cs_next_var` >>
     simp[] >> metis_tac[abiDecoderReentryTheory.abi_decoder_operand_live_emit]) >>
  qexistsl_tac [`H`,`u`] >> simp[] >>
  conj_tac
  >- (rpt gen_tac >>
      qpat_assum `!D explicit. gas_origin_ptr_path _ (_,G,tn) _ _`
        (qspecl_then [`D`,`explicit`] mp_tac) >>
      qpat_assum `!D explicit. gas_origin_ptr_path _ (_,G1,tn1) _ _`
        (qspecl_then [`D`,`explicit`] mp_tac) >>
      qpat_assum `!D explicit. gas_origin_ptr_path _ (_,G3,tn3) _ _`
        (qspecl_then [`D`,`explicit`] mp_tac) >>
      POP_ASSUM_LIST (K all_tac) >> metis_tac[gas_origin_ptr_path_append, APPEND_NIL]) >>
  map_every (fn pat => qpat_assum pat (fn th => once_rewrite_tac [th]))
    [`t = r3 with vs_vars := t.vs_vars`, `r3 = r1 with vs_vars := r3.vs_vars`,
     `r1 = s with vs_vars := r1.vs_vars`] >> simp[]
QED

Theorem allocated_member_source_origin[local]:
  compile_getelemptr_abi pos dyn ao MLOAD (Var source) hi sa = (out,sb) /\
  hi <> Lit 0w /\ run_inst_seq (emitted_insts sa sb) s = OK t /\
  fn_has_code sa sb func /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  allocas_from lo s /\ abi_decode_ptr_window G tn s source (n2w B) L /\
  not_fresh_at sa source /\ (!x. pos = Var x ==> not_fresh_at sa x) /\
  eval_operand pos s = SOME (n2w p) /\ op_taint tn pos = {} /\ op_prov G pos = NONE /\
  (dyn ==> p + ao + 32 <= L /\ B + (p+ao) < dimword (:256) /\
           B + (p+ao) + 32 <= s.vs_alloca_next) ==>
  ?H u. op_taint u out = {} /\ op_prov H out = NONE /\
    sa.cs_next_var <= sb.cs_next_var /\ abi_decoder_operand_live sb.cs_next_var out /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),H,u)) /\
    t = s with vs_vars := t.vs_vars /\ allocas_from lo t /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x))
Proof
  Cases_on `dyn`
  >- (simp_tac bool_ss [] >> strip_tac >> irule allocated_dynamic_source_origin >>
      simp[] >> qexistsl_tac [`B`,`L`,`ao`,`hi`,`p`,`pos`,`source`] >> simp[]) >>
  simp_tac bool_ss [] >> strip_tac >>
  drule getelemptr_static_emit >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule abiDecoderReentryTheory.abi_decoder_operand_live_emit >> strip_tac >>
  drule_all allocated_member_head_add_origin >>
  disch_then (qspec_then `PG` strip_assume_tac) >> qexistsl_tac [`G'`,`tn'`] >> simp[]
QED

(* Join the destination ADD at the source-navigation cut of the same run. *)
Theorem allocated_member_setup_origin[local]:
  abi_decode_member_setup (Var output) pos MLOAD (Var source) hi dyn ao vo st = (ops,en) /\
  run_inst_seq (emitted_insts st en) s = OK t /\ fn_has_code st en func /\ hi <> Lit 0w /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\ allocas_from lo s /\
  abi_decode_ptr_window G tn s source (n2w B) L /\
  not_fresh_at st source /\ not_fresh_at st output /\
  (!x. pos = Var x ==> not_fresh_at st x) /\
  eval_operand pos s = SOME (n2w p) /\ op_taint tn pos = {} /\ op_prov G pos = NONE /\
  (dyn ==> p + ao + 32 <= L /\ B + (p+ao) < dimword (:256) /\
           B + (p+ao) + 32 <= s.vs_alloca_next) /\
  lookup_var output s = SOME (n2w d) /\ ptr_covers G tn output s capacity /\
  vo + n <= capacity /\ d + vo < dimword (:256) ==>
  ?x H u. SND ops = Var x /\ ptr_covers H u x t n /\
    op_taint u (FST ops) = {} /\ op_prov H (FST ops) = NONE /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (t with vs_inst_idx := LENGTH en.cs_current_insts),H,u)) /\
    t = s with vs_vars := t.vs_vars /\ allocas_from lo t /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all allocated_member_setup_split >> strip_tac >>
  `fn_has_code st mid func /\ fn_has_code mid en func` by
    (`cs_extends st mid` by fs[cs_extends_def, inst_extends_def, IS_PREFIX_APPEND] >>
     qpat_assum `emit_op ADD _ mid = _`
       (mp_then Any assume_tac (REWRITE_RULE [cs_appends_def] (cj 2 cs_appends_emit_helpers))) >>
     metis_tac[fn_has_code_split]) >>
  drule allocated_member_source_origin >>
  disch_then (drule_at (Pat `abi_decode_ptr_window _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `allocas_from _ _`)) >>
  disch_then (drule_at (Pat `ctx_has_dalloca ctx ==> allocas_below_fmp s`)) >>
  disch_then (qpat_assum `fn_has_code st mid func` o mp_then Any mp_tac) >>
  disch_then (qspecl_then [`r`,`PG`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `G1` (qx_choose_then `tn1` strip_assume_tac)) >>
  `!x. not_fresh_at st x ==> not_fresh_at mid x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `~r.vs_halted /\ r.vs_current_bb = mid.cs_current_bb` by
    (qpat_assum `r = s with vs_vars := r.vs_vars` (fn th => once_rewrite_tac [th]) >> simp[]) >>
  `lookup_var output r = SOME (n2w d) /\ ptr_covers G1 tn1 output r capacity` by
    (simp[] >> irule decoderGhostFramePtrTheory.ptr_covers_frame >>
     qexistsl_tac [`G`,`s`,`tn`] >> simp[]) >>
  `eval_operand (Lit (n2w vo)) r = SOME (n2w vo) /\
   op_taint tn1 (Lit (n2w vo)) = {} /\ op_prov G1 (Lit (n2w vo)) = NONE` by
    simp[eval_operand_def, op_taint_def, op_prov_def] >>
  `w2n (n2w d : bytes32) + vo < dimword (:256)` by
    (`d < dimword (:256)` by decide_tac >> simp[w2n_n2w, LESS_MOD]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp r` by
    (qpat_assum `r = s with vs_vars := r.vs_vars` (fn th => once_rewrite_tac [th]) >>
     rewrite_tac[allocas_below_fmp_updates] >> first_assum ACCEPT_TAC) >>
  drule_all member_navigation_emit_pointer_pc_uniform_origin >>
  disch_then (qspec_then `PG` (qx_choose_then `x`
    (qx_choose_then `H` (qx_choose_then `u` strip_assume_tac)))) >>
  `t = r with vs_vars := t.vs_vars` by
    (`eval_operand (Var output) r = SOME (n2w d)` by simp[eval_operand_def] >>
     drule_all buffer_emit_add_run >> simp[update_var_def]) >>
  `t = s with vs_vars := t.vs_vars` by
    (map_every (fn pat => qpat_assum pat (fn th => once_rewrite_tac [th]))
      [`t = r with vs_vars := t.vs_vars`, `r = s with vs_vars := r.vs_vars`] >> simp[]) >>
  `allocas_from lo t` by
    (qpat_assum `t = s with vs_vars := t.vs_vars` (fn th => once_rewrite_tac [th]) >>
     simp[allocas_from_def] >>
     qpat_assum `allocas_from lo s` (ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
  `op_taint u (FST ops) = {} /\ op_prov H (FST ops) = NONE` by
    (Cases_on `FST ops` >> gvs[op_taint_def, op_prov_def,
       abiDecoderReentryTheory.abi_decoder_operand_live_def,
       abiDecoderReentryTheory.abi_decoder_older_vars_def, not_fresh_at_def] >> metis_tac[]) >>
  qexistsl_tac [`x`,`H`,`u`] >> simp[] >>
  rpt gen_tac >>
  qpat_assum `!D explicit. gas_origin_ptr_path _ (_,G,tn) _ _`
    (qspecl_then [`D`,`explicit`] mp_tac) >>
  qpat_assum `~r.vs_halted ==> !D explicit. gas_origin_ptr_path _ _ _ _`
    (fn th => qpat_assum `~r.vs_halted` (qspecl_then [`D`,`explicit`] mp_tac o MATCH_MP th)) >>
  POP_ASSUM_LIST (K all_tac) >> metis_tac[gas_origin_ptr_path_append, APPEND_NIL]
QED

Theorem decoder_member_setup_reentry_ghosts[local]:
  abi_decode_member_setup (Var output) pos MLOAD (Var source) hi dyn ao vo st = (ops,middle) /\
  abi_malformed_entry H ctx func cenv cx es st sites dstid live
    (Var source) hi pos (Var output) B L xs p d outsz s /\
  run_inst_seq (emitted_insts st middle) s = OK t /\
  fn_has_code st middle func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  (dyn ==> p + ao + 32 <= L) /\ vo + n <= outsz /\
  abi_decode_ptr_window G tn s source (n2w B) L /\
  ptr_covers G tn output s outsz /\ op_prov G pos = NONE /\ op_prov G hi = NONE /\
  op_taint tn pos = {} /\ op_taint tn hi = {} /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ alloca_history func s ==>
  ?x G' tn'. SND ops = Var x /\
  ptr_covers G' tn' x (t with vs_inst_idx := LENGTH middle.cs_current_insts) n /\
    abi_decode_ptr_window G' tn' (t with vs_inst_idx := LENGTH middle.cs_current_insts) source (n2w B)
      L /\
    op_taint tn' (FST ops) = {} /\ op_prov G' (FST ops) = NONE /\
    op_taint tn' hi = {} /\ op_prov G' hi = NONE /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (t with vs_inst_idx := LENGTH middle.cs_current_insts),G',tn')) /\
    (t with vs_inst_idx := LENGTH middle.cs_current_insts).vs_memory = s.vs_memory /\
    (t with vs_inst_idx := LENGTH middle.cs_current_insts).vs_allocas = s.vs_allocas /\
    (t with vs_inst_idx := LENGTH middle.cs_current_insts).vs_alloca_next = s.vs_alloca_next /\
    (t with vs_inst_idx := LENGTH middle.cs_current_insts).vs_accounts = s.vs_accounts /\
    (t with vs_inst_idx := LENGTH middle.cs_current_insts).vs_transient = s.vs_transient /\
    (t with vs_inst_idx := LENGTH middle.cs_current_insts).vs_call_ctx = s.vs_call_ctx /\
    (t with vs_inst_idx := LENGTH middle.cs_current_insts).vs_immutables = s.vs_immutables /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. abi_decoder_operand_live st.cs_next_var (Var x) ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    alloca_history func (t with vs_inst_idx := LENGTH middle.cs_current_insts) /\
    allocas_from lo (t with vs_inst_idx := LENGTH middle.cs_current_insts) /\
    lo <= (t with vs_inst_idx := LENGTH middle.cs_current_insts).vs_alloca_next
Proof
  strip_tac >> simp[LET_THM] >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_member_setup_shape >> strip_tac >>
  qpat_x_assum `middle.cs_current_insts = _` kall_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st middle)` by
    fs[EVERY_MEM] >>
  `alloca_inv s` by
    metis_tac[abi_malformed_entry_def, stmt_state_rel_local_ptrs_alloca] >>
  drule_all entry_straight_line_alloca_history >> strip_tac >>
  `(dyn ==> p + ao + 32 <= L /\ B + (p+ao) < dimword (:256) /\
    B + (p+ao) + 32 <= s.vs_alloca_next)` by
    (strip_tac >> `p + ao + 32 <= L` by metis_tac[] >> simp[] >>
     drule_all allocated_member_head_read_bound >> simp[]) >>
  `hi <> Lit 0w /\ d + vo < dimword (:256) /\
   eval_operand pos s = SOME (n2w p) /\ lookup_var output s = SOME (n2w d) /\
   not_fresh_at st source /\ not_fresh_at st output /\
   (!x. pos = Var x ==> not_fresh_at st x) /\
   (!x. hi = Var x ==> not_fresh_at st x)` by
    (fs[abi_malformed_entry_def, EVAL ``EVERY f [a;b;c;d]``,
        eval_operand_def, abiDecoderReentryTheory.abi_decoder_operand_live_def,
        abiDecoderReentryTheory.abi_decoder_older_vars_def, not_fresh_at_def] >>
     Cases_on `pos` >> Cases_on `hi` >> gvs[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    (fs[abi_malformed_entry_def] >>
     qpat_assum `stmt_state_rel _ ctx func cenv cx es s`
       (mp_tac o MATCH_MP
         bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) >>
     DISCH_THEN ACCEPT_TAC) >>
  drule_all allocated_member_setup_origin >>
  disch_then (qspec_then `PG` (qx_choose_then `x` (qx_choose_then `H1`
    (qx_choose_then `tn1` strip_assume_tac)))) >>
  qexistsl_tac [`x`,`H1`,`tn1`] >> simp[] >>
  `op_taint tn1 hi = {} /\ op_prov H1 hi = NONE` by
    (Cases_on `hi` >> gvs[op_taint_def, op_prov_def] >> metis_tac[]) >>
  `abi_decode_ptr_window H1 tn1 (t with vs_inst_idx := LENGTH middle.cs_current_insts)
     source (n2w B) L` by
    (qpat_assum `!x. not_fresh_at st x ==> _`
       (drule_then strip_assume_tac) >>
     irule abi_decode_ptr_window_frame >> qexistsl_tac [`G`,`s`,`tn`] >>
     gvs[lookup_var_def]) >>
  `t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
   t.vs_alloca_next = s.vs_alloca_next /\ t.vs_accounts = s.vs_accounts /\
   t.vs_transient = s.vs_transient /\ t.vs_call_ctx = s.vs_call_ctx /\
   t.vs_immutables = s.vs_immutables` by
    (qpat_assum `t = s with vs_vars := t.vs_vars` (fn th => once_rewrite_tac [th]) >> simp[]) >>
  gs[abiDecoderReentryTheory.abi_decoder_operand_live_def,
     abiDecoderReentryTheory.abi_decoder_older_vars_def, GSYM not_fresh_at_def,
     allocas_from_def] >>
  rpt strip_tac >> metis_tac[]
QED

(* Transport the entry and ghosts through the very same navigation run. *)
Theorem decoder_joint_members_head_entry[local]:
  abi_valid_allocated_members_entry H ce env sf (ty::tys) (tv::tvs) vs
    ctx func cenv cx es st en (Var source) hi pos (Var output) B L xs p d outsz ao vo dstid live ceiling s /\
  abi_decode_member_setup (Var output) pos MLOAD (Var source) hi
    (dec_info_needs_offset (type_to_abi_dec_info sf ce ty)) ao vo st = (ops,middle) /\
  compile_abi_decode_to_buf (SND ops) (FST ops) MLOAD (Var source) hi
    (type_to_abi_dec_info sf ce ty) middle = ((),end_st) /\
  compile_abi_decode_complex_elems (Var output) pos MLOAD (Var source) hi
    (abi_decoder_member_infos sf ce tys)
    (ao + abi_embedded_static_size ce.ce_struct_fields ty)
    (vo + type_memory_bytes ce ty) end_st = ((),en) /\
  abi_decode_ptr_window G tn s source (n2w B) L /\
  ptr_covers G tn output s outsz /\ op_prov G pos = NONE /\ op_prov G hi = NONE /\
  op_taint tn pos = {} /\ op_taint tn hi = {} /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ alloca_history func s ==>
  ?v rest r x G' tn'. vs = v::rest /\ SND ops = Var x /\
    abi_valid_allocated_entry H ce env sf ty tv v ctx func cenv cx es middle end_st
      (Var source) hi (FST ops) (Var x) B L xs
      (p + if dec_info_needs_offset (type_to_abi_dec_info sf ce ty)
           then abi_head_word (DROP (p+ao) xs) else ao)
      (d+vo) dstid live ceiling r /\
    abi_decode_sim ctx func s r /\
    abi_malformed_resource_post ctx func cenv cx es st.cs_next_var
      (abi_malformed_scratch_sites st en func) dstid s r /\
    ptr_covers G' tn' x r (type_memory_bytes ce ty) /\
    abi_decode_ptr_window G' tn' r source (n2w B) L /\
    op_taint tn' (FST ops) = {} /\ op_prov G' (FST ops) = NONE /\
    op_taint tn' hi = {} /\ op_prov G' hi = NONE /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK r,G',tn')) /\
    r.vs_memory = s.vs_memory /\ r.vs_allocas = s.vs_allocas /\
    r.vs_alloca_next = s.vs_alloca_next /\ r.vs_accounts = s.vs_accounts /\
    r.vs_transient = s.vs_transient /\ r.vs_call_ctx = s.vs_call_ctx /\
    r.vs_immutables = s.vs_immutables /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. abi_decoder_operand_live st.cs_next_var (Var x) ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    alloca_history func r /\ allocas_from lo r /\ lo <= r.vs_alloca_next
Proof
  strip_tac >>
  qhdtm_assum `abi_valid_allocated_members_entry`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_valid_allocated_members_entry_def]) >>
  fs[LIST_REL_CONS1] >>
  drule (SIMP_RULE bool_ss [MAP] abi_valid_source_cons_values) >> strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_member_cons_code >> strip_tac >>
  drule abi_decoder_coherent_header >> strip_tac >>
  `LENGTH xs = L` by
    (fs[abi_malformed_entry_def, abi_malformed_allocated_window_def] >>
     qpat_x_assum `mem_bytes_at B L s.vs_memory = xs`
       (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
  `p+ao+abi_member_head_size (vyper_to_abi_type env ty) <= L /\
   vo+type_memory_bytes ce ty <= outsz /\ middle.cs_next_var <= ceiling.cs_next_var` by
    (fs[abi_decoder_header_def, type_memory_size_def] >> decide_tac) >>
  `vyper_decode_valid_enc (vyper_to_abi_type env ty)
    (abi_decode_member_bytes (vyper_to_abi_type env ty) (DROP p xs) (DROP (p+ao) xs))` by
    (Cases_on `is_dynamic (vyper_to_abi_type env ty)` >>
     fs[vyper_decode_valid_enc_def, abi_decode_member_bytes_def, abi_head_word_def,
        contractABITheory.dec_number_def, contractABITheory.dest_NumV_def]) >>
  drule_all abi_valid_allocated_member_navigate >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  drule_all abi_decode_member_setup_shape >> strip_tac >>
  `inst_extends st middle` by (irule abi_decoder_inst_extends_prefix >> simp[]) >>
  qpat_x_assum `middle.cs_current_insts = _` kall_tac >>
  `fn_has_code st middle func` by metis_tac[fn_has_code_split] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st middle)` by fs[EVERY_MEM] >>
  drule_all abi_decoder_run_sequence_reach >>
  disch_then (qspec_then `ctx` (qx_choose_then `r` strip_assume_tac)) >>
  `(dec_info_needs_offset (type_to_abi_dec_info sf ce ty) ==> p+ao+32 <= L)` by
    (drule abiDecoderDynamicTheory.abi_decoder_coherent_dynamic >> strip_tac >>
     fs[abiDecoderOffsetTheory.abi_decoder_needs_offset_iff, abi_member_head_size_def] >>
     strip_tac >> gvs[]) >>
  drule_all decoder_member_setup_reentry_ghosts >>
  disch_then (qspec_then `PG` mp_tac) >>
  simp_tac bool_ss [LET_THM] >>
  disch_then (qx_choose_then `x` (qx_choose_then `G1`
    (qx_choose_then `tn1` strip_assume_tac))) >>
  qpat_x_assum `r = _` SUBST_ALL_TAC >>
  qexistsl_tac [`v`,`rest`,`t with vs_inst_idx := LENGTH middle.cs_current_insts`,
    `x`,`G1`,`tn1`] >> simp[abiMalformedMemberSetupTheory.abi_malformed_resource_post_inst_idx] >>
  qabbrev_tac `q = p + (if dec_info_needs_offset (type_to_abi_dec_info sf ce ty)
                         then abi_head_word (DROP (ao+p) xs) else ao)` >>
  `q <= L /\ vyper_decode_valid_enc (vyper_to_abi_type env ty) (DROP q xs) /\
   (is_dynamic (vyper_to_abi_type env ty) \/
    q + static_length (vyper_to_abi_type env ty) <= L) /\
   dec (vyper_to_abi_type env ty)
     (abi_decode_member_bytes (vyper_to_abi_type env ty) (DROP p xs) (DROP (p+ao) xs)) =
   dec (vyper_to_abi_type env ty) (DROP q xs)` by
    (irule abi_valid_source_member_position >> simp[Abbr `q`] >> metis_tac[]) >>
  `abi_malformed_scratch_sites middle end_st func SUBSET
   abi_malformed_scratch_sites st en func` by
    (irule abi_malformed_scratch_sites_nested >> decide_tac) >>
  `fn_has_code middle end_st func` by metis_tac[fn_has_code_split] >>
  `~t.vs_halted` by
    (drule_all abiValidAllocatedMemberSetupTheory.abi_valid_allocated_member_setup_frame >> simp[]) >>
  simp[abi_valid_allocated_entry_def, fresh_vars_wrt_def,
       abiMalformedMemberSetupTheory.abi_malformed_entry_inst_idx] >>
  `ao+p = p+ao` by decide_tac >>
  gs[Abbr `q`, abi_malformed_entry_def, SUBSET_DEF, fresh_vars_wrt_def] >>
  metis_tac[]
QED

(* The tail writes after the head, and its scratch sites cannot overlap
   the destination allocation. Preserve the head for arbitrary clean witnesses. *)
Theorem decoder_member_robust_head_frame[local]:
  val_wf tv v /\
  abi_valid_allocated_frame sites (q+type_memory_size tv) n t u /\
  alloca_inv t /\ abi_malformed_destination func cenv scopes dstid q (type_memory_size tv) t /\
  dstid NOTIN sites /\
  (!a. ~(q+type_memory_size tv <= a /\ a < q+type_memory_size tv+n) /\
       ~abi_malformed_site_range sites t u a 1 ==> (a IN tn' <=> a IN tn)) /\
  (!m. mem_agree_outside tn t.vs_memory m ==> val_in_memory tv v q m) ==>
  !m. mem_agree_outside tn' u.vs_memory m ==> val_in_memory tv v q m
Proof
  strip_tac >>
  `!a. q <= a /\ a < q+type_memory_size tv ==>
       ~(q+type_memory_size tv <= a /\ a < q+type_memory_size tv+n) /\
       ~abi_malformed_site_range sites t u a 1` by
    (rpt gen_tac >> strip_tac >> conj_tac >- decide_tac >>
     qhdtm_assum `abi_malformed_destination`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_malformed_destination_def]) >>
     strip_tac >>
     `b+sz <= a \/ a+1 <= b` by
       (irule abi_malformed_site_range_protected >>
        goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]) >>
     decide_tac) >>
  drule_all abi_valid_allocated_frame_slice >> strip_tac >>
  `!i. i < type_memory_size tv ==> (q+i IN tn' <=> q+i IN tn)` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!a. _ ==> (a IN tn' <=> a IN tn)` (qspec_then `q+i` mp_tac) >>
     qpat_assum `!a. q <= a /\ _ ==> _` (qspec_then `q+i` mp_tac) >> simp[]) >>
  `val_footprint tv v <= type_memory_size tv` by simp[val_footprint_le] >>
  rpt strip_tac >> irule robust_val_in_memory_copy_transport >>
  rpt (goal_assum (drule_at Any))
QED

Theorem decoder_joint_members_cons[local]:
  (^decode_child_run) ty tv /\ (^decode_members_run) tys tvs ==> (^decode_members_run) (ty::tys) (tv::tvs)
Proof
  BETA_TAC >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "child") (mk_asm "tail")) >>
  rpt gen_tac >> disch_tac >> rpt gen_tac >> strip_tac >>
  qhdtm_assum `abi_valid_allocated_members_entry`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_valid_allocated_members_entry_def]) >>
  drule abi_decoder_member_cons_trace >>
  disch_then (qx_choose_then `ops` (qx_choose_then `middle`
    (qx_choose_then `end_st` strip_assume_tac))) >>
  drule_all decoder_joint_members_head_entry >>
  disch_then (qspec_then `PG` (qx_choose_then `v` (qx_choose_then `rest`
    (qx_choose_then `r` (qx_choose_then `x` (qx_choose_then `G1`
      (qx_choose_then `tn1` strip_assume_tac))))))) >>
  asm "child" drule >>
  disch_then (qspecl_then [`G1`,`tn1`,`PG`,`lo`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `t` (qx_choose_then `G2` (qx_choose_then `tn2` strip_assume_tac))) >>
  asm_x "child" kall_tac >>
  qpat_x_assum `vs = v::rest` SUBST_ALL_TAC >>
  drule_all abi_valid_allocated_members_tail_entry >> strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_member_cons_code >> strip_tac >>
  `!q. abi_decoder_operand_live st.cs_next_var (Var q) ==>
       FLOOKUP G2 q = FLOOKUP G q /\ op_taint tn2 (Var q) = op_taint tn (Var q)` by
    (gen_tac >> disch_tac >>
     `abi_decoder_operand_live middle.cs_next_var (Var q)` by
       (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
     qpat_assum `!x. abi_decoder_operand_live st.cs_next_var (Var x) ==> _`
       (qspec_then `q` mp_tac) >>
     qpat_assum `!x. abi_decoder_operand_live middle.cs_next_var (Var x) ==> _`
       (qspec_then `q` mp_tac) >>
     simp[]) >>
  `abi_decoder_operand_live st.cs_next_var (Var output) /\
   abi_decoder_operand_live st.cs_next_var pos /\ abi_decoder_operand_live st.cs_next_var hi /\
   lookup_var output t = lookup_var output s` by
    (qpat_assum `abi_valid_allocated_members_entry _ _ _ _ tys tvs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ t`
       (mp_tac o PURE_REWRITE_RULE [abi_valid_allocated_members_entry_def]) >>
     fs[abi_malformed_entry_def, eval_operand_def]) >>
  `ptr_covers G2 tn2 output t outsz` by
    (irule ptr_covers_frame >> qexistsl_tac [`G`,`s`,`tn`] >>
     qpat_assum `!q. abi_decoder_operand_live st.cs_next_var (Var q) ==> _ /\ _`
       (qspec_then `output` mp_tac) >> simp[]) >>
  `op_prov G2 pos = NONE /\ op_prov G2 hi = NONE /\
   op_taint tn2 pos = {} /\ op_taint tn2 hi = {}` by
    (Cases_on `pos` >> Cases_on `hi` >>
     fs[abi_decoder_operand_live_def, op_prov_def, op_taint_def] >> metis_tac[]) >>
  asm_x "tail" drule >>
  disch_then (qspecl_then [`G2`,`tn2`,`PG`,`lo`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `u` (qx_choose_then `G3` (qx_choose_then `tn3` strip_assume_tac))) >>
  qexistsl_tac [`u`, `G3`, `tn3`] >>
  conj_tac >- (drule_all abi_valid_allocated_members_cons_post >> simp[]) >>
  simp[] >> conj_tac
  >- (rpt gen_tac >>
      qpat_assum `!D explicit. gas_origin_ptr_path _ (s,G,tn) _ _`
        (qspecl_then [`D`,`explicit`] mp_tac) >>
      qpat_assum `!D explicit. gas_origin_ptr_path _ (r,G1,tn1) _ _`
        (qspecl_then [`D`,`explicit`] mp_tac) >>
      qpat_assum `!D explicit. gas_origin_ptr_path _ (t,G2,tn2) _ _`
        (qspecl_then [`D`,`explicit`] mp_tac) >>
      POP_ASSUM_LIST (K all_tac) >> metis_tac[gas_origin_ptr_path_append, APPEND_NIL]) >>
  `type_memory_size tv = type_memory_bytes ce ty /\ val_wf tv v` by
    (qhdtm_assum `abi_valid_allocated_entry`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_valid_allocated_entry_def]) >>
     drule abi_decoder_coherent_header >> strip_tac >>
     fs[abi_decoder_header_def] >>
     irule (cj 1 value_has_type_val_wf) >>
     irule (cj 1 abi_to_vyper_well_typed) >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any)) >>
  qhdtm_assum `abi_valid_allocated_post`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_valid_allocated_post_def]) >>
  qpat_assum `abi_valid_allocated_members_post tvs rest _ _ _ _ _ end_st en _ _ _ _ t u`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_valid_allocated_members_post_def]) >>
  `alloca_inv t` by
    (qpat_assum `abi_malformed_resource_post _ _ _ _ _ _ _ _ r t`
       (mp_then Any irule abi_malformed_resource_post_alloca_inv)) >>
  `abi_malformed_destination func cenv es.scopes dstid (d+vo) (type_memory_size tv) t /\
   dstid NOTIN abi_malformed_scratch_sites end_st en func` by
    (qpat_assum `abi_valid_allocated_members_entry _ _ _ _ tys tvs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ t`
       (mp_tac o PURE_REWRITE_RULE [abi_valid_allocated_members_entry_def]) >>
     simp[abi_malformed_entry_def] >> strip_tac >> simp[] >>
     irule abi_malformed_destination_subrange >>
     qexistsl_tac [`d`, `outsz`] >> simp[] >> fs[type_memory_size_def] >> decide_tac) >>
  conj_tac
  >- (rpt strip_tac >> once_rewrite_tac[val_in_memory_def] >>
      simp[] >> irule decoder_member_robust_head_frame >>
      `d + vo + type_memory_size tv = d + (vo + type_memory_bytes ce ty)` by decide_tac >>
      pop_assum SUBST1_TAC >> rpt (goal_assum (drule_at Any))) >>
  conj_tac
  >- (gen_tac >> disch_tac >>
      `abi_decoder_operand_live end_st.cs_next_var (Var x')` by
        (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
      qpat_assum `!q. abi_decoder_operand_live st.cs_next_var (Var q) ==> _ /\ _`
        (qspec_then `x'` mp_tac) >>
      qpat_assum `!q. abi_decoder_operand_live end_st.cs_next_var (Var q) ==> _`
        (qspec_then `x'` mp_tac) >> simp[]) >>
  qpat_assum `abi_malformed_resource_post _ _ _ _ _ _ _ _ r t`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_malformed_resource_post_def]) >>
  qpat_assum `abi_malformed_resource_post _ _ _ _ _ _ _ _ t u`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_malformed_resource_post_def]) >>
  `s.vs_alloca_next <= t.vs_alloca_next` by simp[] >>
  `!id b sz. FLOOKUP t.vs_allocas id = SOME (b,sz) ==>
     FLOOKUP s.vs_allocas id = SOME (b,sz) \/ s.vs_alloca_next <= b` by
    (qpat_assum `!id b sz. FLOOKUP t.vs_allocas id = _ ==>
        FLOOKUP r.vs_allocas id = _ \/ r.vs_alloca_next <= b` mp_tac >> gvs[]) >>
  `abi_malformed_scratch_sites middle end_st func SUBSET abi_malformed_scratch_sites st en func /\
   abi_malformed_scratch_sites end_st en func SUBSET abi_malformed_scratch_sites st en func` by
    (conj_tac >> irule abi_malformed_scratch_sites_nested >> decide_tac) >>
  qx_gen_tac `a` >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "outside") assume_tac) >>
  `~abi_malformed_site_range (abi_malformed_scratch_sites middle end_st func) r t a 1` by
    (disch_tac >> qpat_x_assum `~abi_malformed_site_range _ s u a 1` mp_tac >>
     simp[] >>
     qpat_x_assum `abi_malformed_site_range _ r t a 1`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_malformed_site_range_def]) >>
     rewrite_tac[abi_malformed_site_range_def]
     >- (disj1_tac >> qexistsl_tac [`aid`,`b`,`sz`] >> gvs[SUBSET_DEF]) >>
     disj2_tac >> simp[] >> decide_tac) >>
  `~abi_malformed_site_range (abi_malformed_scratch_sites end_st en func) t u a 1` by
    (disch_tac >> drule_all abi_valid_allocated_site_sequence >> disch_tac >>
     qpat_x_assum `~abi_malformed_site_range _ s u a 1` mp_tac >> simp[] >>
     qpat_x_assum `abi_malformed_site_range _ s u a 1`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_malformed_site_range_def]) >>
     rewrite_tac[abi_malformed_site_range_def]
     >- (disj1_tac >> qexistsl_tac [`aid`,`b`,`sz`] >> gvs[SUBSET_DEF]) >>
     disj2_tac >> simp[]) >>
  qpat_assum `!a. _ ==> (a IN tn3.t_mem <=> a IN tn2.t_mem)` (qspec_then `a` mp_tac) >>
  qpat_assum `!a. _ ==> (a IN tn2.t_mem <=> a IN tn1.t_mem)` (qspec_then `a` mp_tac) >>
  asm_x "outside" mp_tac >> simp[type_memory_size_list_sum] >> decide_tac
QED

Theorem decoder_joint_members_fold[local]:
  LIST_REL (^decode_child_run) tys tvs ==> (^decode_members_run) tys tvs
Proof
  BETA_TAC >> qid_spec_tac `tvs` >> Induct_on `tys` >-
    (simp_tac bool_ss [LIST_REL_NIL] >>
     ACCEPT_TAC (SIMP_RULE bool_ss [] (BETA_RULE decoder_joint_members_nil))) >>
  pure_rewrite_tac [LIST_REL_CONS1, PULL_EXISTS] >> BETA_TAC >>
  rpt gen_tac >> disch_then strip_assume_tac >>
  qpat_x_assum `_ = _::_` SUBST_ALL_TAC >>
  match_mp_tac (BETA_RULE decoder_joint_members_cons) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rename1 `LIST_REL _ tys tail` >>
  last_x_assum (qspec_then `tail` mp_tac) >> asm_rewrite_tac[]
QED

(* The physical guard and the pointer path start with the same sequence run. *)
Theorem decoder_joint_complex_guard[local]:
  abi_decode_complex_head_guard pos hi headsz st = ((),middle) /\
  fn_has_code st middle func /\ fn_inst_ids_distinct func /\
  abi_malformed_entry H ctx func cenv cx es st sites dstid live
    (Var source) hi pos (Var output) B L xs p d n s /\
  p + headsz <= L /\ middle.cs_next_var <= ceiling.cs_next_var /\
  fresh_vars_wrt ceiling s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts /\
  abi_decode_ptr_window G tn s source (n2w B) L /\
  ptr_covers G tn output s n /\ op_prov G pos = NONE /\ op_prov G hi = NONE /\
  op_taint tn pos = {} /\ op_taint tn hi = {} /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ alloca_history func s ==>
  ?r G' tn'. abi_decode_sim ctx func s r /\
    abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid s r /\
    fresh_vars_wrt ceiling r /\ ~r.vs_halted /\
    r.vs_current_bb = middle.cs_current_bb /\ r.vs_inst_idx = LENGTH middle.cs_current_insts /\
    r.vs_memory = s.vs_memory /\ r.vs_allocas = s.vs_allocas /\
    r.vs_alloca_next = s.vs_alloca_next /\ r.vs_accounts = s.vs_accounts /\
    r.vs_transient = s.vs_transient /\ r.vs_call_ctx = s.vs_call_ctx /\
    r.vs_immutables = s.vs_immutables /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK r,G',tn')) /\
    abi_decode_ptr_window G' tn' r source (n2w B) L /\ ptr_covers G' tn' output r n /\
    op_prov G' pos = NONE /\ op_prov G' hi = NONE /\
    op_taint tn' pos = {} /\ op_taint tn' hi = {} /\
    (!x. abi_decoder_operand_live st.cs_next_var (Var x) ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    alloca_history func r /\ allocas_from lo r /\ lo <= r.vs_alloca_next
Proof
  strip_tac >>
  qhdtm_assum `abi_malformed_entry`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_malformed_entry_def]) >>
  `L < dimword (:256)` by (fs[abi_malformed_allocated_window_def] >> decide_tac) >>
  `abi_decoder_operand_live st.cs_next_var pos /\ abi_decoder_operand_live st.cs_next_var hi` by fs[] >>
  drule abi_decoder_complex_guard_reentry >>
  disch_then (qspecl_then [`p`, `ceiling`, `s`] mp_tac) >>
  (impl_tac >- (simp[] >> qexists_tac `L` >> simp[])) >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  drule abi_malformed_complex_guard_writes >> strip_tac >>
  `abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid s t` by
    (first_assum (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) irule abi_malformed_read_sequence_resource) >>
     simp[] >> qexists_tac `emitted_insts st middle` >> simp[]) >>
  drule abi_decoder_complex_guard_code >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts st middle)` by
    (fs[EVERY_MEM] >> metis_tac[fresh_write_op_simple, abi_decode_source_opcode_def,
                              is_terminator_def]) >>
  drule_all abi_decoder_run_sequence_reach >>
  disch_then (qspec_then `ctx` (qx_choose_then `r` strip_assume_tac)) >>
  `alloca_inv s` by metis_tac[stmt_state_rel_local_ptrs_alloca] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st middle)` by fs[EVERY_MEM] >>
  drule_all entry_straight_line_alloca_history >> strip_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx es s`
       (ACCEPT_TAC o MATCH_MP stmt_state_rel_allocas_below_fmp)) >>
  drule_all member_scalar_guard_actual_run >>
  disch_then (qspec_then `PG` (qx_choose_then `G1` (qx_choose_then `tn1` strip_assume_tac))) >>
  qpat_x_assum `r = _` SUBST_ALL_TAC >>
  `t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
   t.vs_alloca_next = s.vs_alloca_next /\ t.vs_accounts = s.vs_accounts /\
   t.vs_transient = s.vs_transient /\ t.vs_call_ctx = s.vs_call_ctx /\
   t.vs_immutables = s.vs_immutables /\ ~t.vs_halted` by
    (qpat_assum `t = s with vs_vars := t.vs_vars` (once_rewrite_tac o single) >> simp[]) >>
  `!x. abi_decoder_operand_live st.cs_next_var (Var x) ==>
       lookup_var x t = lookup_var x s /\ FLOOKUP G1 x = FLOOKUP G x /\
       op_taint tn1 (Var x) = op_taint tn (Var x)` by
    fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, GSYM not_fresh_at_def] >>
  `abi_decoder_operand_live st.cs_next_var (Var source) /\
   abi_decoder_operand_live st.cs_next_var (Var output)` by fs[] >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH middle.cs_current_insts`,`G1`,`tn1`] >>
  fs[abi_malformed_resource_post_inst_idx, fresh_vars_wrt_def, allocas_from_def] >>
  conj_tac
  >- (irule abi_decode_ptr_window_frame >> qexistsl_tac [`G`,`s`,`tn`] >>
      fs[lookup_var_def]) >>
  conj_tac
  >- (irule ptr_covers_frame >> qexistsl_tac [`G`,`s`,`tn`] >> simp[]) >>
  Cases_on `pos` >> Cases_on `hi` >>
  fs[abi_decoder_operand_live_def, op_prov_def, op_taint_def] >> metis_tac[]
QED

Theorem decoder_joint_complex_members[local]:
  (^decode_members_run) tys tvs /\
  compile_abi_decode_to_buf (Var output) pos MLOAD (Var source) hi
    (DecComplex dyn (abi_decoder_member_infos sf ce tys)) st = ((),en) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  abi_malformed_entry H ctx func cenv cx es st
    (abi_malformed_scratch_sites st en func) dstid live
    (Var source) hi pos (Var output) B L xs p d (type_memory_size_list tvs) s /\
  LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\ p <= L /\
  vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type env) tys) (DROP p xs) (DROP p xs) /\
  abi_to_vyper_list env tys
    (abi_decode_members (MAP (vyper_to_abi_type env) tys) (DROP p xs) (DROP p xs)) = SOME vs /\
  en.cs_next_var <= ceiling.cs_next_var /\ fresh_vars_wrt ceiling s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts /\
  abi_decode_ptr_window G tn s source (n2w B) L /\
  ptr_covers G tn output s (type_memory_size_list tvs) /\
  op_prov G pos = NONE /\ op_prov G hi = NONE /\
  op_taint tn pos = {} /\ op_taint tn hi = {} /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ alloca_history func s ==>
  ?u G' tn'.
  abi_valid_allocated_members_post tvs vs ctx func cenv cx es st en ceiling dstid
    d (type_memory_size_list tvs) s u /\
  u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
  u.vs_call_ctx = s.vs_call_ctx /\ u.vs_immutables = s.vs_immutables /\
  (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK u,G',tn')) /\
  ptr_covers G' tn' output u (type_memory_size_list tvs) /\
  abi_decode_ptr_window G' tn' u source (n2w B) L /\
  (!mem. mem_agree_outside tn'.t_mem u.vs_memory mem ==> tuple_in_memory vs tvs d mem) /\
  (!x. abi_decoder_operand_live st.cs_next_var (Var x) ==>
    FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
  (!a. ~(d <= a /\ a < d+type_memory_size_list tvs) /\
     ~abi_malformed_site_range (abi_malformed_scratch_sites st en func) s u a 1 ==>
     (a IN tn'.t_mem <=> a IN tn.t_mem)) /\
  alloca_history func u /\ allocas_from lo u /\ lo <= u.vs_alloca_next
Proof
  BETA_TAC >> disch_then (CONJUNCTS_THEN2 (mk_asm "members") strip_assume_tac) >>
  drule abi_decoder_complex_trace >> disch_then (qx_choose_then `middle` strip_assume_tac) >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_complex_code >> strip_tac >>
  drule abi_decoder_member_infos_layout >> strip_tac >>
  `LENGTH xs = L` by
    (fs[abi_malformed_entry_def, abi_malformed_allocated_window_def] >>
     qpat_x_assum `mem_bytes_at B L s.vs_memory = xs`
       (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
  `p + SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) tys)) <= L` by
    (drule abiValidMembersTheory.abi_valid_members_view >> simp[LENGTH_DROP] >> decide_tac) >>
  `p + FOLDR (\(_,asz,_) acc. asz + acc) 0 (abi_decoder_member_infos sf ce tys) <= L /\
   middle.cs_next_var <= ceiling.cs_next_var` by (simp[] >> decide_tac) >>
  drule_all decoder_joint_complex_guard >>
  disch_then (qspec_then `PG` (qx_choose_then `r` (qx_choose_then `G1`
    (qx_choose_then `tn1` strip_assume_tac)))) >>
  `abi_malformed_scratch_sites middle en func SUBSET abi_malformed_scratch_sites st en func` by
    (irule abi_malformed_scratch_sites_nested >> decide_tac) >>
  `local_ptrs_reserved cenv middle` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `st` >> fs[abi_malformed_entry_def]) >>
  `abi_malformed_entry H ctx func cenv cx es middle
    (abi_malformed_scratch_sites middle en func) dstid live
    (Var source) hi pos (Var output) B L xs p d (type_memory_size_list tvs) r` by
    (drule_all abi_malformed_aggregate_reentry >> simp[]) >>
  `abi_valid_allocated_members_entry H ce env sf tys tvs vs ctx func cenv cx es
    middle en (Var source) hi pos (Var output) B L xs p d (type_memory_size_list tvs)
    0 0 dstid live ceiling r` by simp[abi_valid_allocated_members_entry_def] >>
  asm_x "members" drule >>
  disch_then (qspecl_then [`G1`,`tn1`,`PG`,`lo`] mp_tac) >> (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `u` (qx_choose_then `G2` (qx_choose_then `tn2` strip_assume_tac))) >>
  rule_assum_tac (PURE_REWRITE_RULE [ADD_CLAUSES]) >>
  qexistsl_tac [`u`,`G2`,`tn2`] >>
  conj_tac >- (irule abi_valid_allocated_complex_members_post >>
               qexistsl_tac [`middle`,`r`] >> gvs[]) >>
  simp[] >> conj_tac
  >- (rpt gen_tac >> metis_tac[gas_origin_ptr_path_append, APPEND_NIL]) >>
  conj_tac
  >- (gen_tac >> disch_tac >>
      `abi_decoder_operand_live middle.cs_next_var (Var x)` by
        (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
      simp[]) >>
  qx_gen_tac `a` >> disch_then (CONJUNCTS_THEN2 (mk_asm "outside") assume_tac) >>
  `~abi_malformed_site_range (abi_malformed_scratch_sites middle en func) r u a 1` by
    (disch_tac >> qpat_x_assum `~abi_malformed_site_range _ s u a 1` mp_tac >> simp[] >>
     qpat_x_assum `abi_malformed_site_range _ r u a 1`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_malformed_site_range_def]) >>
     rewrite_tac[abi_malformed_site_range_def]
     >- (disj1_tac >> qexistsl_tac [`aid`,`b`,`sz`] >> gvs[SUBSET_DEF]) >>
     disj2_tac >> simp[]) >>
  qpat_assum `!a. _ ==> (a IN tn2.t_mem <=> a IN tn1.t_mem)` (qspec_then `a` mp_tac) >>
  asm_x "outside" mp_tac >> simp[]
QED

Theorem abi_valid_allocated_joint_tuple:
  LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\
  LIST_REL (^decode_child_run) tys tvs ==> (^decode_child_run) (TupleT tys) (TupleTV tvs)
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac
    (mk_asm "members" o MATCH_MP decoder_joint_members_fold)) >>
  BETA_TAC >> rpt gen_tac >> disch_tac >> rpt gen_tac >> strip_tac >>
  qhdtm_assum `abi_valid_allocated_entry`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_valid_allocated_entry_def]) >>
  drule abi_decoder_coherent_header >> strip_tac >>
  `type_memory_bytes ce (TupleT tys) = type_memory_size_list tvs` by
    fs[abi_decoder_header_def, type_memory_size_def] >>
  `vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type env) tys)
     (DROP p xs) (DROP p xs)` by
    (fs[vyper_to_abi_type_def, vyper_to_abi_types_MAP] >>
     gvs[Once vyper_decode_valid_enc_def]) >>
  `dec (vyper_to_abi_type env (TupleT tys)) (DROP p xs) =
     ListV (abi_decode_members (MAP (vyper_to_abi_type env) tys) (DROP p xs) (DROP p xs))` by
    simp[vyper_to_abi_type_def, vyper_to_abi_types_MAP, Once dec_def, abi_decode_members_value] >>
  `?vs. v = ArrayV (TupleV vs) /\ abi_to_vyper_list env tys
      (abi_decode_members (MAP (vyper_to_abi_type env) tys) (DROP p xs) (DROP p xs)) = SOME vs` by
    (fs[Once abi_to_vyper_def, AllCaseEqs()] >> metis_tac[]) >>
  qpat_x_assum `v = ArrayV (TupleV vs)` SUBST_ALL_TAC >>
  `compile_abi_decode_to_buf (Var output) pos MLOAD (Var source) hi
     (DecComplex (EXISTS (is_abi_dynamic ce.ce_struct_fields) tys)
       (abi_decoder_member_infos sf ce tys)) st = ((),en)` by
    fs[abi_decoder_tuple_infos] >>
  qpat_assum `type_memory_bytes ce (TupleT tys) = _`
    (fn th => rewrite_tac[th] >> rule_assum_tac (PURE_REWRITE_RULE [th])) >>
  asm_x "members" (assume_tac o BETA_RULE) >>
  drule_all (BETA_RULE decoder_joint_complex_members) >>
  disch_then (qspec_then `PG`
    (qx_choose_then `u` (qx_choose_then `G'` (qx_choose_then `tn'` strip_assume_tac)))) >>
  qexistsl_tac [`u`,`G'`,`tn'`] >>
  fs[abi_valid_allocated_post_def, abi_valid_allocated_members_post_def, val_in_memory_def] >>
  first_assum ACCEPT_TAC
QED

Theorem abi_valid_allocated_joint_fixed_array:
  abi_decoder_coherent ce env sf ty tv /\ (^decode_child_run) ty tv ==>
  (^decode_child_run) (ArrayT ty (Fixed n)) (ArrayTV tv (Fixed n))
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac (mk_asm "child")) >>
  `LIST_REL (^decode_child_run) (REPLICATE n ty) (REPLICATE n tv)` by
    (simp[LIST_REL_REPLICATE_same] >> strip_tac >>
     asm "child" (ACCEPT_TAC o SIMP_RULE (srw_ss()) [] o BETA_RULE)) >>
  asm_x "child" kall_tac >>
  dxrule_then (mk_asm "members") decoder_joint_members_fold >>
  `LIST_REL (abi_decoder_coherent ce env sf) (REPLICATE n ty) (REPLICATE n tv)` by
    simp[LIST_REL_REPLICATE_same] >>
  BETA_TAC >> rpt gen_tac >> disch_tac >> rpt gen_tac >> strip_tac >>
  qhdtm_assum `abi_valid_allocated_entry`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_valid_allocated_entry_def]) >>
  `evaluate_type env ty = SOME tv` by
    (rev_drule abi_decoder_coherent_header >> simp[abi_decoder_header_def]) >>
  `type_memory_bytes ce (ArrayT ty (Fixed n)) = type_memory_size_list (REPLICATE n tv)` by
    (drule_at Any abi_decoder_coherent_header >>
     simp[abi_decoder_header_def, type_memory_size_def, type_memory_size_list_replicate]) >>
  `vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type env) (REPLICATE n ty))
     (DROP p xs) (DROP p xs)` by
    (fs[vyper_to_abi_type_def, Once vyper_decode_valid_enc_def] >>
     simp[map_replicate, vyper_decode_valid_enc_tuple_REPLICATE]) >>
  `dec (vyper_to_abi_type env (ArrayT ty (Fixed n))) (DROP p xs) = ListV
     (abi_decode_members (MAP (vyper_to_abi_type env) (REPLICATE n ty)) (DROP p xs) (DROP p xs))` by
    simp[vyper_to_abi_type_def, Once dec_def, abi_decode_array_members,
         map_replicate, abi_decode_members_value] >>
  qpat_assum `dec (vyper_to_abi_type env (ArrayT ty (Fixed n))) _ = _`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  `LENGTH (abi_decode_members (MAP (vyper_to_abi_type env) (REPLICATE n ty))
     (DROP p xs) (DROP p xs)) = n` by
    (drule abi_valid_members_view >> strip_tac >>
     drule has_types_length >> simp[]) >>
  `?vs. abi_to_vyper_list env (REPLICATE n ty)
     (abi_decode_members (MAP (vyper_to_abi_type env) (REPLICATE n ty)) (DROP p xs) (DROP p xs)) = SOME vs /\
     v = ArrayV (SArrayV (enumerate_static_array (default_value tv) 0 vs))` by
    (fs[Once abi_to_vyper_def, make_array_value_def, AllCaseEqs()] >> metis_tac[]) >>
  `LENGTH vs = n` by (drule abi_to_vyper_list_lengths >> simp[]) >>
  qpat_x_assum `v = ArrayV _` SUBST_ALL_TAC >>
  `compile_abi_decode_to_buf (Var output) pos MLOAD (Var source) hi
     (DecComplex (is_abi_dynamic ce.ce_struct_fields ty)
       (abi_decoder_member_infos sf ce (REPLICATE n ty))) st = ((),en)` by
    fs[abi_decoder_fixed_array_infos] >>
  qpat_assum `type_memory_bytes ce (ArrayT ty (Fixed n)) = _`
    (fn th => rewrite_tac[th] >> rule_assum_tac (PURE_REWRITE_RULE [th])) >>
  asm_x "members" (assume_tac o BETA_RULE) >>
  drule_all (BETA_RULE decoder_joint_complex_members) >>
  disch_then (qspec_then `PG`
    (qx_choose_then `u` (qx_choose_then `G'` (qx_choose_then `tn'` strip_assume_tac)))) >>
  `!mem. mem_agree_outside tn'.t_mem u.vs_memory mem ==>
     val_in_memory (ArrayTV tv (Fixed n))
       (ArrayV (SArrayV (enumerate_static_array (default_value tv) 0 vs))) d mem` by
    (rpt strip_tac >> irule abi_decoder_fixed_array_memory >> simp[]) >>
  `val_in_memory (ArrayTV tv (Fixed n))
     (ArrayV (SArrayV (enumerate_static_array (default_value tv) 0 vs))) d u.vs_memory` by
    (irule abi_decoder_fixed_array_memory >> fs[abi_valid_allocated_members_post_def]) >>
  qexistsl_tac [`u`,`G'`,`tn'`] >>
  fs[abi_valid_allocated_post_def, abi_valid_allocated_members_post_def] >>
  first_assum ACCEPT_TAC
QED

Theorem abi_valid_allocated_joint_struct:
  FLOOKUP env nsid = SOME (StructArgs args) /\
  FLOOKUP sf (nsid_to_string nsid) = SOME fields /\
  MAP (\(name,ty,sz). (name,ty)) fields = args /\
  LIST_REL (abi_decoder_coherent ce (env \\ nsid) (sf \\ nsid_to_string nsid))
    (MAP SND args) tvs /\
  LIST_REL (^(decode_child_run |> subst [``env:nsid |-> type_args`` |-> ``(env:nsid |-> type_args) \\ nsid``,
    ``sf:string |-> (string # vyperAST$type # num) list`` |->
      ``(sf:string |-> (string # vyperAST$type # num) list) \\ nsid_to_string nsid``]))
    (MAP SND args) tvs ==>
  (^decode_child_run) (StructT nsid) (StructTV (ZIP (MAP FST args,tvs)))
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
      (CONJUNCTS_THEN2 assume_tac
        (mk_asm "members" o MATCH_MP decoder_joint_members_fold))))) >>
  `LENGTH (MAP FST args) = LENGTH tvs` by
    (drule LIST_REL_LENGTH >> simp[]) >>
  `MAP (FST o SND) fields = MAP SND args` by
    (qpat_assum `MAP _ fields = args` (SUBST1_TAC o SYM) >>
     simp[MAP_MAP_o, combinTheory.o_DEF] >>
     irule MAP_CONG >> simp[pairTheory.FORALL_PROD]) >>
  BETA_TAC >> rpt gen_tac >> disch_tac >> rpt gen_tac >> strip_tac >>
  qhdtm_assum `abi_valid_allocated_entry`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_valid_allocated_entry_def]) >>
  drule abi_decoder_coherent_header >> strip_tac >>
  `type_memory_bytes ce (StructT nsid) = type_memory_size_list tvs` by
    (`type_memory_size_fields (ZIP (MAP FST args,tvs)) = type_memory_size_list tvs` by
       (irule type_memory_size_fields_zip >> simp[]) >>
     fs[abi_decoder_header_def, type_memory_size_def]) >>
  `vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type (env \\ nsid)) (MAP SND args))
     (DROP p xs) (DROP p xs)` by
    (fs[vyper_to_abi_type_def, vyper_to_abi_types_MAP] >>
     gvs[Once vyper_decode_valid_enc_def]) >>
  `dec (vyper_to_abi_type env (StructT nsid)) (DROP p xs) = ListV
     (abi_decode_members (MAP (vyper_to_abi_type (env \\ nsid)) (MAP SND args)) (DROP p xs) (DROP p xs))` by
    simp[vyper_to_abi_type_def, vyper_to_abi_types_MAP, Once dec_def, abi_decode_members_value] >>
  qpat_assum `dec (vyper_to_abi_type env (StructT nsid)) _ = _`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  drule abi_decoder_struct_values >> strip_tac >>
  qpat_x_assum `v = StructV _` SUBST_ALL_TAC >>
  drule_all abi_decoder_struct_conversion >> strip_tac >>
  `compile_abi_decode_to_buf (Var output) pos MLOAD (Var source) hi
     (DecComplex (EXISTS (is_abi_dynamic ce.ce_struct_fields) (MAP SND args))
       (abi_decoder_member_infos (sf \\ nsid_to_string nsid) ce (MAP SND args))) st = ((),en)` by
    (drule abi_decoder_struct_infos >> disch_then (qspec_then `ce` mp_tac) >>
     simp[] >> strip_tac >> gvs[]) >>
  qpat_assum `type_memory_bytes ce (StructT nsid) = _`
    (fn th => rewrite_tac[th] >> rule_assum_tac (PURE_REWRITE_RULE [th])) >>
  asm_x "members" (assume_tac o BETA_RULE) >>
  drule_all (BETA_RULE decoder_joint_complex_members) >>
  disch_then (qspec_then `PG`
    (qx_choose_then `u` (qx_choose_then `G'` (qx_choose_then `tn'` strip_assume_tac)))) >>
  qexistsl_tac [`u`,`G'`,`tn'`] >>
  fs[abi_valid_allocated_post_def, abi_valid_allocated_members_post_def,
     val_in_memory_def, fields_in_memory_tuple, MAP_ZIP] >> first_assum ACCEPT_TAC
QED

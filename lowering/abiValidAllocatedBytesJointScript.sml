(* Successful allocated bytes and strings, with ghosts replayed on the actual run. *)
Theory abiValidAllocatedBytesJoint
Ancestors
  abiValidAllocatedBytesRunPost abiDecodeValidBytesPruned abiValidAllocatedLeaves
  abiValidAllocatedContract abiMalformedRecursiveInterface abiCallerAllocation
  abiDecoderValidBytes abiDecoderBytesFrame abiDecoderBytesPhases abiDecoderContract
  abiDecodeMemReentry abiDecodePtrReentry abiDecodePtrReentryObservations
  abiDecoderReentry abiDecoderVarSequence abiDecoderVarExtend abiDecodePtrMemberFrame
  fragGasCopyLoop fragGasOriginPtr bodyFullPathHistory calldataTypedRobustPtr
  fragGasCopySeqLiftProps
  stateRelProj exprLoweringProps emitHelperProps compileEnv freshWrites
  bodyPtrDefs ptrDiscipline loweringStateRelDefs venomState venomInst
  contractABI vyperTypeABI list words arithmetic finite_map pred_set

Theorem abi_valid_allocated_bytes_joint_observations:
  (ty = BaseT (BytesT (Dynamic n)) \/ ty = BaseT (StringT n)) /\
  abi_valid_allocated_entry H ce env sf ty tv v ctx func cenv cx es
    st en (Var source) hi pos (Var output) B L xs p d dstid live ceiling s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  abi_decode_ptr_window G tn s source (n2w B) L /\
  ptr_covers G tn output s (type_memory_bytes ce ty) /\
  op_prov G pos = NONE /\ op_prov G hi = NONE /\
  op_taint tn pos = {} /\ op_taint tn hi = {} /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ alloca_history func s ==>
  !PG. ?t G' tn'.
    abi_valid_allocated_post tv v ctx func cenv cx es st en ceiling dstid
      d (type_memory_bytes ce ty) s t /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_immutables = s.vs_immutables /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G',tn')) /\
    ptr_covers G' tn' output t (type_memory_bytes ce ty) /\
    abi_decode_ptr_window G' tn' t source (n2w B) L /\
    (!mem. mem_agree_outside tn'.t_mem t.vs_memory mem ==> val_in_memory tv v d mem) /\
    (!x. abi_decoder_operand_live st.cs_next_var (Var x) ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!a. ~(d <= a /\ a < d+type_memory_bytes ce ty) /\
      ~abi_malformed_site_range (abi_malformed_scratch_sites st en func) s t a 1 ==>
      (a IN tn'.t_mem <=> a IN tn.t_mem)) /\
    alloca_history func t /\ allocas_from lo t /\ lo <= t.vs_alloca_next
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> gen_tac >>
  drule_all abi_valid_allocated_bytes_input >>
  disch_then (qx_choose_then `at` (qx_choose_then `payload`
    (map_every assume_tac o CONJUNCTS))) >>
  qhdtm_assum `abi_valid_allocated_entry`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_valid_allocated_entry_def]) >>
  qhdtm_assum `abi_malformed_entry`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_malformed_entry_def]) >>
  qpat_x_assum `EVERY _ [_;_;_;_]`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [EVERY_DEF]) >>
  drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
  qhdtm_x_assum `abi_malformed_allocated_window`
    (strip_assume_tac o REWRITE_RULE [abi_malformed_allocated_window_def]) >>
  qhdtm_x_assum `abi_malformed_destination`
    (strip_assume_tac o REWRITE_RULE [abi_malformed_destination_def]) >>
  rename1 `FLOOKUP s.vs_allocas live = SOME (B,src_cap)` >>
  qabbrev_tac `out_cap = abi_decode_bytes_copy_size n` >>
  `d+out_cap < dimword (:256) /\ d+out_cap <= b+sz /\ ptr_covers G tn output s out_cap` by
    (qpat_assum `type_memory_bytes ce ty = out_cap` (SUBST_ALL_TAC o SYM) >> simp[]) >>
  `B+L <= s.vs_alloca_next /\ d+out_cap <= s.vs_alloca_next` by
    (conj_tac
     >- (irule abi_caller_allocation_end >> simp[] >> qexistsl [`src_cap`,`live`,`B`] >> simp[]) >>
     irule abi_caller_allocation_end >> simp[] >> qexistsl [`sz`,`dstid`,`b`] >> simp[]) >>
  `regions_disjoint B L d out_cap` by
    (`B+src_cap <= b \/ b+sz <= B` by metis_tac[abi_caller_allocation_separate] >>
     rw[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  qmatch_asmsub_abbrev_tac `abi_decoder_valid_bytes_pre _ _ _ _ _ _ _ _ _ _ _ _ _ pruned` >>
  `compile_abi_decode_to_buf (Var output) pos MLOAD (Var source) hi
      (DecBytestring n) st = ((),en)` by metis_tac[] >>
  `?clean. run_inst_seq (emitted_insts st en) pruned = OK clean /\
      val_in_memory (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV payload) d clean.vs_memory` by
    (drule_at (Pat `abi_decoder_valid_bytes_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
       abi_decoder_valid_bytes_sequence >>
     disch_then (drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`)) >>
     simp[] >> metis_tac[]) >>
  `pruned.vs_inst_idx = LENGTH st.cs_current_insts /\
    B+L <= pruned.vs_alloca_next /\ d+out_cap <= pruned.vs_alloca_next` by
    simp[Abbr `pruned`, abi_decoder_prune_vars_def] >>
  `abi_decode_ptr_window G tn pruned source (n2w B) L /\
    ptr_covers G tn output pruned out_cap /\ eval_operand hi pruned = SOME (n2w L)` by
    simp[Abbr `pruned`, abi_decode_ptr_window_prune, abi_decode_ptr_prune_covers,
         abi_decoder_prune_eval] >>
  `not_fresh_at st source /\ not_fresh_at st output /\
    (!x. MEM (Var x) [pos;hi] ==> not_fresh_at st x)` by
    (conj_tac >- fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def] >>
     conj_tac >- fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def] >>
     simp[] >> rpt strip_tac >>
     gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
  `32 + contractABI$ceil32 n <= out_cap` by
    simp[Abbr `out_cap`, abiDecoderBytesTheory.abi_decode_bytes_copy_size_def, contractABITheory.ceil32_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp pruned` by
    (`pruned.vs_allocas = s.vs_allocas /\ pruned.vs_fmp = s.vs_fmp /\
       pruned.vs_initial_fmp = s.vs_initial_fmp` by
       simp[Abbr `pruned`, abi_decoder_prune_vars_def] >>
     PURE_REWRITE_TAC [allocas_below_fmp_def] >>
     qpat_assum `pruned.vs_allocas = s.vs_allocas` (PURE_REWRITE_TAC o single) >>
     qpat_assum `pruned.vs_fmp = s.vs_fmp` (PURE_REWRITE_TAC o single) >>
     qpat_assum `pruned.vs_initial_fmp = s.vs_initial_fmp` (PURE_REWRITE_TAC o single) >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s`
       (ACCEPT_TAC o PURE_REWRITE_RULE [allocas_below_fmp_def])) >>
  drule_all abi_decode_valid_bytes_pruned_certificate >>
  disch_then (qspecl_then [`func`, `PG`] (qx_choose_then `Gf` (qx_choose_then `tf`
    (map_every assume_tac o CONJUNCTS)))) >>
  (* Replay the two checks without changing the terminal ghost witnesses. *)
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_bytes_reentry_code >> strip_tac >>
  drule_all abi_decode_bytes_position_shape >> strip_tac >>
  `abi_decoder_vars_extend s.vs_vars pruned s` by
    simp[Abbr `pruned`, abi_decoder_prune_extension] >>
  drule_all abi_decoder_sequence_vars_extend >>
  disch_then (qx_choose_then `actual` strip_assume_tac) >>
  `run_inst_seq_mem_ok (emitted_insts st en) s` by
    (irule abi_decode_sequence_mem_reentry_result >> metis_tac[]) >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode /\ ~is_terminator i.inst_opcode)
     (emitted_insts st en)` by fs[EVERY_MEM] >>
  qabbrev_tac `empty_dead = <|d_stor := K (K {}); d_trans := K (K {});
                             d_imm := K {}; d_ret := K {}|>` >>
  `inst_seq_ptr empty_dead 0 ctx func PG G tn (emitted_insts st en) s Gf tf` by
    (irule abi_decode_ptr_sequence_reentry_result >> metis_tac[]) >>
  drule_all abi_valid_allocated_bytes_run_post >> simp_tac bool_ss [LET_THM] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `t = actual with vs_inst_idx := LENGTH en.cs_current_insts` >>
  `en.cs_current_insts = st.cs_current_insts ++ emitted_insts st en` by fs[inst_extends_def] >>
  drule_all stmtReasonLitFragMemoryTheory.fn_has_code_code >> strip_tac >>
  `s.vs_inst_idx + LENGTH (emitted_insts st en) = LENGTH en.cs_current_insts` by simp[] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
              i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) (emitted_insts st en)` by
    (simp_tac bool_ss [EVERY_MEM] >> rpt gen_tac >> disch_tac >>
     `i.inst_opcode <> GAS` by
       (disch_tac >> qpat_assum `EVERY (\i. abi_decoder_reentry_opcode _) _`
         (qspec_then `i` mp_tac o REWRITE_RULE [EVERY_MEM]) >>
        simp[abi_decoder_reentry_opcode_def]) >>
     qpat_assum `EVERY (\i. _ <> INVOKE /\ _ /\ ~is_alloca_op _) _`
       (qspec_then `i` mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     Cases_on `i.inst_opcode = ALLOCA` >> simp[is_alloca_op_def]) >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts st en) (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >>
  `(ctx_has_dalloca ctx ==> !pre i post u.
      emitted_insts st en = pre ++ i::post /\ run_inst_seq pre s = OK u ==>
      unitTransformDefs$dalloca_no_wrap i u)` by
    (rpt strip_tac >> irule memSafeRunTheory.dalloca_no_wrap_non_dalloca >>
     disch_tac >>
     qpat_assum `EVERY (\i. abi_decoder_reentry_opcode _) _`
       (qspec_then `i` mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     simp[abi_decoder_reentry_opcode_def, MEM_APPEND]) >>
  `!explicit. gas_origin_ptr_path (empty_dead,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK t,Gf,tf)` by
    (gen_tac >> drule_all run_inst_seq_origin_ptr_lift >> simp[Abbr `t`]) >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK t,Gf,tf)` by
    (rpt gen_tac >> irule fragGasOriginPtrDeadTheory.gas_origin_ptr_path_from_no_dead >>
     qpat_assum `!explicit. gas_origin_ptr_path (empty_dead,_,_,_,_,_) _ [] _`
       (qspec_then `explicit` mp_tac) >> simp[Abbr `empty_dead`]) >>
  `alloca_history func t` by
    (irule body_full_path_alloca_history >> simp[] >> metis_tac[]) >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by
    (simp[allocas_from_def] >>
     qpat_assum `allocas_from lo s` (mp_tac o REWRITE_RULE [allocas_from_def]) >> simp[]) >>
  `!x w. lookup_var x clean = SOME w ==> lookup_var x t = SOME w` by
    (rpt strip_tac >> simp[Abbr `t`, lookup_var_def] >>
     drule_at (Pat `abi_decoder_vars_extend _ clean actual`) abi_decoder_vars_extend_eval >>
     disch_then (qspecl_then [`w`,`Var x`] mp_tac) >> simp[eval_operand_def,lookup_var_def]) >>
  `t.vs_memory = clean.vs_memory` by
    (drule_at (Pat `abi_decoder_vars_extend _ clean actual`) abi_decoder_vars_extend_observations >>
     simp[Abbr `t`]) >>
  `ptr_covers Gf tf output t out_cap /\ abi_decode_ptr_window Gf tf t source (n2w B) L` by
    (conj_tac
     >- (qpat_x_assum `ptr_covers Gf tf output clean out_cap` mp_tac >>
         simp[ptr_covers_def] >> metis_tac[]) >>
     qpat_x_assum `abi_decode_ptr_window Gf tf clean source _ L` mp_tac >>
     simp[abi_decode_ptr_window_def,ptr_covers_def] >> metis_tac[]) >>
  (* Only the representation's actual footprint needs to be clean. *)
  `val_wf (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV payload) /\
    d < dimword (:256)` by
    (drule abi_decoder_valid_bytes_facts >> simp[]) >>
  `!i. d <= i /\ i < d + 32 + LENGTH payload ==> i NOTIN tf.t_mem` by
    (qpat_assum `abi_decode_ptr_window Gf tf clean output _ _`
       (mp_tac o REWRITE_RULE [abi_decode_ptr_window_def]) >>
     simp[w2n_n2w, LESS_MOD] >> strip_tac >> gen_tac >> strip_tac >>
     qpat_assum `!i. _ /\ _ ==> i NOTIN tf.t_mem` irule >>
     `LENGTH payload <= contractABI$ceil32 (LENGTH payload)` by simp[] >> decide_tac) >>
  `!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==> val_in_memory tv v d mem` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!mem. _ /\ _ ==> val_in_memory tv v d mem` irule >>
     simp[abiDecoderStringTheory.abi_decoder_string_memory] >>
     irule clean_footprint_val_in_memory_robust >>
     conj_tac >- simp[] >> qexistsl [`t.vs_memory`, `tf.t_mem`] >>
     reverse conj_tac
     >- (conj_tac >- first_assum ACCEPT_TAC >>
         qpat_assum `t.vs_memory = clean.vs_memory` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
     simp_tac (srw_ss()) [loweringPostsTheory.val_footprint_def] >>
     gen_tac >> strip_tac >> qpat_assum `!i. _ /\ _ ==> i NOTIN tf.t_mem` irule >>
     decide_tac) >>
  `32 + contractABI$ceil32 (LENGTH payload) <= out_cap` by
    (`LENGTH payload <= n` by
       (qhdtm_assum `abi_decoder_valid_bytes_pre`
         (mp_tac o cj 4 o REWRITE_RULE [abi_decoder_valid_bytes_pre_def]) >> simp[]) >>
     drule vyperTypeABITheory.ceil32_mono >> decide_tac) >>
  qexistsl [`t`, `Gf`, `tf`] >> simp[] >>
  simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def, GSYM not_fresh_at_def]
QED

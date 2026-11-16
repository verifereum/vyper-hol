(* Proof procedures for the finite phases of the allocated Dynamic case.
   These procedures introduce no HOL constants or theorem contracts. *)
structure abiDecodeJointFiniteStepsLib =
struct
open HolKernel Parse boolLib bossLib;
open abiValidAllocatedContractTheory abiDecoderCoherenceTheory
     abiDecoderArrayLoopInitTheory abiDecoderRecursiveArrayTheory
     abiDecoderArrayInitTheory abiValidAllocatedArraySourceTheory
     abiMalformedRecursiveInterfaceTheory abiDecoderContractTheory
     abiDecoderDynarrayPrefixTheory abiDecoderArrayHeaderTheory
     abiDecoderIndexInitTheory abiEncoderTheory vyperABITheory
     valueEncodingPropsTheory exprLoweringTheory
     abiValidAllocatedArrayInitTheory abiMalformedInitResourceTheory
     abiDecodeRangesTheory abiMalformedBulkIntegrationTheory
     exprLoweringPropsTheory venomExecSemanticsTheory emitHelperPropsTheory
     compileEnvTheory arithmeticTheory abiMalformedNavigationTheory
     emitHelperTheory contextTheory venomInstTheory fragExecTheory
     compileAllocaProvenanceTheory instSeqComposePtrTheory listTheory;

val dynamic_phases_tac =
  qhdtm_assum `abi_valid_allocated_entry`
    (strip_assume_tac o SIMP_RULE bool_ss
      [abi_valid_allocated_entry_def, vyper_to_abi_type_def,
       contractABITheory.is_dynamic_def, optionTheory.IS_NONE_DEF]) >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  `compile_abi_decode_to_buf (Var output) pos MLOAD (Var source) hi
    (DecDynArray (type_to_abi_dec_info sf ce et)
      (abi_embedded_static_size ce.ce_struct_fields et)
      (type_memory_bytes ce et) (is_abi_dynamic ce.ce_struct_fields et) maxn)
    st = ((),en)` by fs[type_to_abi_dec_info_def] >>
  drule_all abi_decoder_recursive_array_code >> strip_tac >>
  drule abi_decode_array_loop_init_trace >> strip_tac >>
  drule_all abi_decode_dynarray_position_prefix_shape >> strip_tac >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  `LENGTH xs = L` by
    (`mem_bytes_at B L s.vs_memory = xs` by
       fs[abi_malformed_entry_def, abi_malformed_allocated_window_def,
          Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >>
     metis_tac[LENGTH_mem_bytes_at]) >>
  drule_all abi_valid_allocated_array_source_view >> strip_tac >>
  `type_memory_bytes ce et = type_memory_size tv' /\
   abi_embedded_static_size ce.ce_struct_fields et =
     abi_member_head_size (vyper_to_abi_type env et)` by
    (qpat_assum `abi_decoder_coherent ce env sf et tv'`
       (mp_tac o MATCH_MP abi_decoder_coherent_header) >>
     simp[abi_decoder_header_def]);

val dynamic_runtime_tac =
  `maxn < dimword (:256)` by
    metis_tac[abi_decoder_coherent_array_capacity] >>
  `MEM (mk_inst header_st.cs_next_id ALLOCA [Lit 32w]
     [STRING #"%" (toString header_st.cs_next_var)])
     loop_st.cs_current_insts` by
    (qpat_x_assum `abi_decode_index_init _ = _` mp_tac >>
     simp[abi_decode_index_init_def, compile_alloc_buffer_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
     strip_tac >> gvs[MEM_APPEND]) >>
  `MEM (mk_inst (loop_st.cs_next_id-2) ALLOCA [Lit 32w]
     [STRING #"%" (toString (loop_st.cs_next_var-1))]) (fn_insts func)` by
    (simp[] >> irule fn_has_code_current_member >>
     qexistsl_tac [`st`, `loop_st`] >> simp[] >>
     qpat_x_assum `MEM _ loop_st.cs_current_insts` mp_tac >> simp[]) >>
  `loop_st.cs_next_id-2 IN abi_malformed_scratch_sites st en func` by
    (simp[abi_malformed_scratch_sites_def] >>
     goal_assum (drule_at Any) >> simp[mk_inst_def]) >>
  `32 <= type_memory_bytes ce (ArrayT et (Dynamic maxn)) /\
   loop_st.cs_next_var <= ceiling.cs_next_var /\
   LENGTH vs = abi_head_word (DROP p xs) /\
   p+32+LENGTH vs*abi_embedded_static_size ce.ce_struct_fields et <= L` by
    (simp[type_memory_bytes_def] >> decide_tac) >>
  drule_all abi_valid_allocated_array_init_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st loop_st) s = OK indexed` >>
  `emitted_insts st loop_st = emitted_insts st guard_st ++
     (emitted_insts guard_st header_st ++ emitted_insts header_st loop_st)` by
    (`inst_extends st header_st` by metis_tac[inst_extends_trans] >>
     `emitted_insts st loop_st = emitted_insts st header_st ++ emitted_insts header_st loop_st` by
       (irule emitted_insts_append >> fs[GSYM inst_extends_def]) >>
     `emitted_insts st header_st = emitted_insts st guard_st ++ emitted_insts guard_st header_st` by
       (irule emitted_insts_append >> fs[GSYM inst_extends_def]) >> simp[]) >>
  `?guarded prepared.
     run_inst_seq (emitted_insts st guard_st) s = OK guarded /\
     run_inst_seq (emitted_insts guard_st header_st) guarded = OK prepared /\
     run_inst_seq (emitted_insts header_st loop_st) prepared = OK indexed` by
    (qpat_x_assum `run_inst_seq (emitted_insts st loop_st) s = OK indexed`
       mp_tac >> simp[] >> strip_tac >>
     drule run_inst_seq_append_ok_split >> strip_tac >>
     drule run_inst_seq_append_ok_split >> metis_tac[]);

(* Attach canonical scalar ghosts to the actual successful header guard run.
   The selected ghost pair is independent of dead/storage masks. *)
val dynamic_guard_head_shape_tac =
  qpat_assum `abi_decode_dynarray_position_prefix _ _ _ _ _ _ _ = _`
    (strip_assume_tac o REWRITE_RULE [abi_decode_dynarray_position_prefix_trace]) >>
  rename1 `abi_decode_bytes_head pos hi st = (head,head_st)` >>
  rename1 `compile_abi_dec_addr (Var source) pos head_st = (addr,addr_st)` >>
  rename1 `abi_decode_count_guard MLOAD addr maxn addr_st = (guard_count,count_st)` >>
  `hi <> Lit 0w /\ eval_operand pos s = SOME (n2w p) /\
   eval_operand hi s = SOME (n2w L)` by
    fs[abi_malformed_entry_def, abi_malformed_allocated_window_def] >>
  `inst_extends st head_st /\ inst_extends head_st guard_st` by
    (drule abiDecoderBytesBoundTheory.abi_decode_bytes_head_shape >> strip_tac >>
     `inst_extends head_st addr_st` by
       (qpat_assum `compile_abi_dec_addr _ _ _ = _`
          (mp_tac o REWRITE_RULE [abiEncoderTheory.compile_abi_dec_addr_def]) >>
        simp_tac (srw_ss()) [] >> metis_tac[inst_extends_emit_op]) >>
     drule abiDecoderGuardsTheory.abi_decode_count_guard_shape >> strip_tac >>
     drule abiDecoderDynarrayBoundTheory.abi_decode_dynarray_payload_guard_shape >> strip_tac >>
     metis_tac[inst_extends_trans]);

val dynamic_guard_head_tac =
  `emitted_insts st guard_st = emitted_insts st head_st ++ emitted_insts head_st guard_st` by
    (irule emitted_insts_append >> fs[GSYM inst_extends_def]) >>
  `?headed. run_inst_seq (emitted_insts st head_st) s = OK headed /\
    run_inst_seq (emitted_insts head_st guard_st) headed = OK guarded` by
    (qpat_x_assum `run_inst_seq (emitted_insts st guard_st) s = OK guarded` mp_tac >>
     simp[] >> metis_tac[run_inst_seq_append_ok_split]) >>
  `?A1. bodyPtrBopScalarSeq$bop_scalar_seq {x | not_fresh_at st x}
    ({pos;hi} UNION IMAGE Lit UNIV) (emitted_insts st head_st) A1 /\
    ({pos;hi} UNION IMAGE Lit UNIV) SUBSET A1 /\ head IN A1` by
    (irule abiDecodePtrBytesMemberTheory.abi_decode_bytes_head_scalar >> simp[] >> metis_tac[]) >>
  `!op. op IN {pos;hi} UNION IMAGE Lit UNIV ==>
    op_prov G op = NONE /\ op_taint tn op = {}` by
    (simp[pred_setTheory.IN_UNION, pred_setTheory.IN_IMAGE] >> rpt strip_tac >>
     gvs[ptrDisciplineTheory.op_prov_def, ptrDisciplineTheory.op_taint_def]) >>
  drule_all (abiDecodePtrScalarFrameTheory.abi_decode_scalar_success_frame |>
    Q.INST [`D` |-> `<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>`]) >>
  disch_then (qspecl_then [`LENGTH head_st.cs_current_insts`, `func`, `PG`] strip_assume_tac);

(* Exact-entry adapter: obtain actual loaded count, not maximum payload size. *)
val dynamic_guard_entry_tac =
  `hi <> Lit 0w /\ eval_operand pos s = SOME (n2w p) /\
   eval_operand hi s = SOME (n2w L) /\
   eval_operand (Var source) s = SOME (n2w B) /\
   B+L < dimword (:256) /\ B+L <= s.vs_alloca_next /\
   mem_bytes_at B L (abi_decode_source MLOAD s) = xs` by
    (qhdtm_assum `abi_malformed_entry`
       (strip_assume_tac o SIMP_RULE bool_ss
         [abi_malformed_entry_def, abi_malformed_allocated_window_def]) >>
     simp[abi_decode_source_def, venomStateTheory.eval_operand_def] >>
     fs[stmt_state_rel_def, venomMemDefsTheory.alloca_inv_def,
        venomMemDefsTheory.alloca_next_valid_def] >>
     qpat_x_assum `!aid base sz. _ ==> base+sz <= s.vs_alloca_next` drule >>
     decide_tac) >>
  `not_fresh_at st source /\
   (!x. pos = Var x ==> not_fresh_at st x) /\
   (!x. hi = Var x ==> not_fresh_at st x)` by
    (qhdtm_assum `abi_malformed_entry`
       (mp_tac o SIMP_RULE bool_ss [abi_malformed_entry_def]) >>
     disch_then (assume_tac o last o CONJUNCTS) >>
     qpat_x_assum `EVERY _ [Var source;hi;pos;Var output]` mp_tac >>
     simp_tac (srw_ss()) [abiDecoderReentryTheory.abi_decoder_operand_live_def,
       abiDecoderReentryTheory.abi_decoder_older_vars_def,
       loweringStateRelDefsTheory.not_fresh_at_def] >>
     Cases_on `pos` >> Cases_on `hi` >> simp[]) >>
  `p+32 <= L /\ p < dimword (:256) /\
   B < dimword (:256) /\ L < dimword (:256)` by decide_tac >>
  `abi_decode_load MLOAD (n2w (B+p):bytes32) s = n2w (LENGTH vs)` by
    (drule_all abi_checked_offset_load >> strip_tac >> fs[]) >>
  `B+p < dimword (:256) /\ LENGTH vs < dimword (:256)` by decide_tac >>
  `w2n (mload (B+p) s) = LENGTH vs` by
    (qpat_x_assum `abi_decode_load MLOAD _ s = _` mp_tac >>
     rewrite_tac[abi_decode_load_def] >>
     gvs[GSYM venomStateTheory.mload_def, wordsTheory.w2n_n2w]);

(* Drop semantic/compiler facts outside the finite guard boundary. The
   selectors inspect variable names only; they construct no logical facts. *)
val guard_context_tac =
  rpt (WEAKEN_TAC (fn tm => List.exists
    (fn v => List.exists (fn n => fst (dest_var v) = n)
      ["ce", "env", "sf", "vs", "tv'", "v", "xs", "output",
       "loop_st", "header_st", "prepared", "indexed", "setup",
       "ip", "cnt", "ceiling", "H0", "en"])
    (free_vars tm)));

(* Keep canonical fresh/reentry calls separate at the consumer: each has a
   bounded tactic budget. These adapters prepare only the actual-count facts. *)
fun dynamic_guard_prune_tac () =
  qmatch_asmsub_abbrev_tac `abi_decode_dynarray_position_prefix pos MLOAD (Var source) hi maxn stride` >>
  rename1 `abi_decode_dynarray_position_prefix pos MLOAD (Var source) hi maxn stride sa = (addr,sb)` >>
  abiDecodePtrArrayPrefixProofLib.reentry_prune
    abiDecodePtrArrayJointTheory.abi_decode_dynarray_position_prefix_joint_code;

val dynamic_guard_bounds_tac =
  `w2n (mload (B+p) initial) <= maxn /\
   p+32+w2n (mload (B+p) initial)*stride <= L` by
    (qpat_assum `w2n (mload (B+p) initial) = LENGTH vs`
       (fn th => pure_rewrite_tac [th]) >>
     conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC);

val dynamic_guard_code_tac =
  `cs_extends sa sb /\ cs_extends sb loop_st` by
    (conj_tac >> irule cs_extends_same_block >>
     fs[inst_extends_def, rich_listTheory.IS_PREFIX_APPEND] >> metis_tac[]) >>
  `fn_has_code sa sb func` by metis_tac[fn_has_code_split] >>
  guard_context_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def];

val dynamic_guard_fresh_context_tac =
  qpat_x_assum `Abbrev (s = _)` kall_tac >>
  qpat_x_assum `run_inst_seq _ initial = OK final` kall_tac >>
  qpat_x_assum `abi_decode_ptr_window G tn initial _ _ _` kall_tac >>
  qpat_x_assum `abi_decode_load _ _ s = _` kall_tac >>
  qpat_x_assum `alloca_history func initial` kall_tac >>
  qpat_x_assum `allocas_from lo initial` kall_tac >>
  qpat_x_assum `lo <= initial.vs_alloca_next` kall_tac;

val dynamic_header_run_tac =
  qabbrev_tac `gs = guarded with vs_inst_idx := LENGTH guard_st.cs_current_insts` >>
  qabbrev_tac `ps = prepared with vs_inst_idx := LENGTH guard_st.cs_current_insts` >>
  `run_inst_seq (emitted_insts guard_st header_st) gs = OK ps` by
    (`EVERY (\i. ~is_terminator i.inst_opcode)
         (emitted_insts guard_st header_st)` by fs[EVERY_MEM] >>
     qpat_assum `run_inst_seq (emitted_insts guard_st header_st) guarded = OK prepared` mp_tac >>
     qpat_assum `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts guard_st header_st)` mp_tac >>
     simp_tac bool_ss [Abbr `gs`, Abbr `ps`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     rpt strip_tac >> simp[fragExecTheory.run_inst_seq_inst_idx,
       instIdxIndepTheory.exec_result_map_def]);

val dynamic_header_resources_tac =
  `not_fresh_at st output /\ lookup_var output s = SOME (n2w d) /\
   d+type_memory_bytes ce (ArrayT et (Dynamic maxn)) < dimword (:256) /\
   alloca_inv s /\ abi_malformed_allocated_window live B L xs s /\
   abi_malformed_destination func cenv es.scopes dstid d
     (type_memory_bytes ce (ArrayT et (Dynamic maxn))) s /\ live <> dstid` by
    fs[abi_malformed_entry_def, exprLoweringPropsTheory.stmt_state_rel_def,
       abiDecoderReentryTheory.abi_decoder_operand_live_def,
       abiDecoderReentryTheory.abi_decoder_older_vars_def,
       loweringStateRelDefsTheory.not_fresh_at_def, venomStateTheory.eval_operand_def] >>
  `d+type_memory_bytes ce (ArrayT et (Dynamic maxn)) <= s.vs_alloca_next` by
    metis_tac[abi_malformed_allocated_bounds];

val dynamic_header_code_tac =
  `cs_extends st guard_st /\ cs_extends guard_st header_st /\ cs_extends header_st loop_st` by
    (rpt conj_tac >> irule compileEnvTheory.cs_extends_same_block >>
     fs[emitHelperPropsTheory.inst_extends_def, rich_listTheory.IS_PREFIX_APPEND] >> metis_tac[]) >>
  `fn_has_code guard_st header_st func` by
    (qpat_assum `cs_extends st guard_st` mp_tac >>
     qpat_assum `cs_extends guard_st header_st` mp_tac >>
     qpat_assum `cs_extends header_st loop_st` mp_tac >>
     qpat_assum `fn_has_code st loop_st func` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     `cs_extends st header_st` by metis_tac[compileEnvTheory.cs_extends_trans] >>
     qspecl_then [`st`,`header_st`,`loop_st`,`func`] mp_tac fragExecTheory.fn_has_code_split >>
     simp[] >> strip_tac >>
     qspecl_then [`st`,`guard_st`,`header_st`,`func`] mp_tac fragExecTheory.fn_has_code_split >> simp[]);

val dynamic_header_frame_tac =
  `lookup_var output guarded = lookup_var output s /\
   FLOOKUP Gguard output = FLOOKUP G output /\
   op_taint tnguard (Var output) = op_taint tn (Var output)` by
    (qpat_assum `!x. not_fresh_at st x ==> _` (qspec_then `output` mp_tac) >> simp[]) >>
  `ptr_covers Gguard tnguard output guarded
     (type_memory_bytes ce (ArrayT et (Dynamic maxn)))` by
    (irule decoderGhostFramePtrTheory.ptr_covers_frame >>
     qexistsl_tac [`G`,`s`,`tn`] >> simp[]) >>
  `not_fresh_at guard_st output` by
    (fs[loweringStateRelDefsTheory.not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `lookup_var output gs = SOME (n2w d) /\
   ptr_covers Gguard tnguard output gs (type_memory_bytes ce (ArrayT et (Dynamic maxn))) /\
   abi_decode_ptr_window Gguard tnguard gs ar (n2w (B+p)) 32 /\
   ~gs.vs_halted /\ gs.vs_current_bb = guard_st.cs_current_bb /\
   gs.vs_inst_idx = LENGTH guard_st.cs_current_insts /\
   allocas_from lo gs /\ gs.vs_alloca_next = s.vs_alloca_next` by
    (`guarded.vs_halted = s.vs_halted /\ guarded.vs_current_bb = s.vs_current_bb /\
      guarded.vs_alloca_next = s.vs_alloca_next` by
       (qpat_assum `guarded = s with vs_vars := _`
          (fn th => pure_once_rewrite_tac [th]) >> simp_tac (srw_ss()) []) >>
     `abi_decode_ptr_window Gguard tnguard
       (guarded with vs_inst_idx := LENGTH guard_st.cs_current_insts)
       ar (n2w (B+p)) 32` by
       (qpat_assum `abi_decode_ptr_window Gguard tnguard guarded ar _ _` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp[abiDecodePtrMemberFrameTheory.abi_decode_ptr_window_def, venomStateTheory.lookup_var_def]) >>
     `lookup_var output guarded = SOME (n2w d)` by simp[] >>
     simp[Abbr `gs`] >>
     qpat_assum `lookup_var output guarded = SOME (n2w d)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[venomStateTheory.lookup_var_def]) >>
  `B+p+32 < dimword (:256) /\ B+p+32 <= gs.vs_alloca_next /\
   d+type_memory_bytes ce (ArrayT et (Dynamic maxn)) <= gs.vs_alloca_next` by decide_tac;

val dynamic_header_joint_tac =
  `abi_decode_array_header (Var output) (Var ar) MLOAD guard_st = (cnt,header_st)` by
    (qpat_assum `abi_decode_array_header (Var output) addr MLOAD guard_st = _` mp_tac >>
     qpat_assum `addr = Var ar` (fn th => pure_rewrite_tac [th]) >> disch_then ACCEPT_TAC) >>
  drule_all abiDecodePtrArrayJointTheory.abi_decode_array_header_success_joint >>
  disch_then (qspec_then `PG`
    (qx_choose_then `Gheader` (qx_choose_then `tnheader` strip_assume_tac)));

val dynamic_index_credit_tac =
  `stmt_state_rel H0 ctx func cenv cx es s` by
    (qhdtm_assum `abi_malformed_entry`
       (mp_tac o REWRITE_RULE [abi_malformed_entry_def]) >>
     simp_tac bool_ss [] >> metis_tac[]) >>
  `alloca_room ctx func s` by metis_tac[stmt_state_rel_def] >>
  `MEM (mk_inst header_st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString header_st.cs_next_var)]) (fn_insts func)` by
    (irule fn_has_code_current_member >>
     qexistsl_tac [`st`, `loop_st`] >> simp[] >>
     qpat_x_assum `MEM _ loop_st.cs_current_insts` mp_tac >> simp[]) >>
  Q.SUBGOAL_THEN
    `((FLOOKUP s.vs_allocas header_st.cs_next_id = NONE /\
       s.vs_alloca_next+32 < dimword (:256)) \/
     (?b. FLOOKUP s.vs_allocas header_st.cs_next_id = SOME (b,32) /\
       b+32 <= s.vs_alloca_next /\ s.vs_alloca_next < dimword (:256)))` assume_tac >-
    (Cases_on `FLOOKUP s.vs_allocas header_st.cs_next_id`
     >- (disj1_tac >> simp[] >>
         qpat_assum `MEM (mk_inst header_st.cs_next_id _ _ _) (fn_insts func)` mp_tac >>
         qpat_assum `alloca_room ctx func s` mp_tac >>
         qpat_assum `FLOOKUP s.vs_allocas header_st.cs_next_id = NONE` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
         drule alloca_room_fresh >>
         disch_then (qspecl_then
           [`mk_inst header_st.cs_next_id ALLOCA [Lit 32w]
              [STRING #"%" (toString header_st.cs_next_var)]`, `32w`] mp_tac) >>
         `header_st.cs_next_id NOTIN FDOM s.vs_allocas` by
           gvs[finite_mapTheory.FLOOKUP_DEF, AllCaseEqs()] >>
         simp[mk_inst_def, wordsTheory.dimword_def]) >>
     PairCases_on `x` >> disj2_tac >> qexists_tac `x0` >>
     `x1 = 32` by
       (qpat_assum `MEM (mk_inst header_st.cs_next_id _ _ _) (fn_insts func)` mp_tac >>
        qpat_assum `FLOOKUP s.vs_allocas header_st.cs_next_id = SOME _` mp_tac >>
        qhdtm_assum `stmt_state_rel`
          (mp_tac o REWRITE_RULE [stmt_state_rel_def]) >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        qpat_x_assum `!inst n base sz. _` drule >>
        simp[mk_inst_def, wordsTheory.dimword_def]) >>
     `x0+32 <= s.vs_alloca_next` by
       (qpat_assum `FLOOKUP s.vs_allocas header_st.cs_next_id = SOME _` mp_tac >>
        qpat_assum `x1 = 32` mp_tac >>
        qpat_assum `alloca_inv s` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        rewrite_tac[venomMemDefsTheory.alloca_inv_def, venomMemDefsTheory.alloca_next_valid_def] >>
        metis_tac[]) >>
     simp[] >> metis_tac[alloca_room_next_lt]);

(* Transport physical index-slot credit through the non-allocating guard/header. *)
val dynamic_index_slot_frame_tac =
  `gs.vs_allocas = s.vs_allocas` by
    (simp_tac (srw_ss()) [Abbr `gs`] >>
     qpat_assum `guarded = s with vs_vars := _`
       (fn th => pure_once_rewrite_tac [th]) >> simp_tac (srw_ss()) []) >>
  `ps.vs_allocas = s.vs_allocas /\ ps.vs_alloca_next = s.vs_alloca_next` by simp[] >>
  Q.SUBGOAL_THEN
    `((FLOOKUP ps.vs_allocas header_st.cs_next_id = NONE /\
       ps.vs_alloca_next+32 < dimword (:256)) \/
     (?b. FLOOKUP ps.vs_allocas header_st.cs_next_id = SOME (b,32) /\
       b+32 <= ps.vs_alloca_next /\ ps.vs_alloca_next < dimword (:256)))` assume_tac
    >- (qpat_assum `ps.vs_allocas = s.vs_allocas`
          (fn th => pure_rewrite_tac [th]) >>
        qpat_assum `ps.vs_alloca_next = s.vs_alloca_next`
          (fn th => pure_rewrite_tac [th]) >> first_assum ACCEPT_TAC);

val dynamic_index_run_tac =
  `~ps.vs_halted` by
    (qpat_assum `run_inst_seq (emitted_insts guard_st header_st) gs = OK ps` mp_tac >>
     qpat_assum `EVERY _ (emitted_insts guard_st header_st)` mp_tac >>
     qpat_assum `~gs.vs_halted` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
        (emitted_insts guard_st header_st)` by fs[EVERY_MEM] >>
     drule_all fragExecTheory.run_inst_seq_preserves_halted >> simp[]) >>
  qabbrev_tac `hs = ps with vs_inst_idx := LENGTH header_st.cs_current_insts` >>
  qabbrev_tac `ix = indexed with vs_inst_idx := LENGTH header_st.cs_current_insts` >>
  `run_inst_seq (emitted_insts header_st loop_st) hs = OK ix` by
    (qpat_assum `run_inst_seq (emitted_insts header_st loop_st) prepared = OK indexed` mp_tac >>
     qpat_assum `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
       (emitted_insts header_st loop_st)` mp_tac >>
     simp_tac (srw_ss()) [Abbr `hs`, Abbr `ps`, Abbr `ix`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts header_st loop_st)` by
       fs[EVERY_MEM] >>
     simp[fragExecTheory.run_inst_seq_inst_idx, instIdxIndepTheory.exec_result_map_def]);

val dynamic_index_joint_tac =
  `~hs.vs_halted` by simp[Abbr `hs`] >>
  Q.SUBGOAL_THEN
    `((FLOOKUP hs.vs_allocas header_st.cs_next_id = NONE /\
       hs.vs_alloca_next+32 < dimword (:256)) \/
     (?b. FLOOKUP hs.vs_allocas header_st.cs_next_id = SOME (b,32) /\
       b+32 <= hs.vs_alloca_next /\ hs.vs_alloca_next < dimword (:256)))` assume_tac
    >- (simp_tac (srw_ss()) [Abbr `hs`, NoAsms] >> first_assum ACCEPT_TAC) >>
  drule_all (actualIndexInitPtrTheory.actual_index_init_endpoint_ptr_origin_core |>
    Q.INST [`G` |-> `Gheader`, `tn` |-> `tnheader`]) >>
  disch_then (mp_tac o SPEC_ALL) >>
  disch_then (qx_choose_then `Gindex` (qx_choose_then `tnindex`
    (qx_choose_then `qi` (qx_choose_then `slot` strip_assume_tac))));

(* Control normalization and mask-uniform composition of the three phases. *)
val dynamic_index_control_tac =
  `ps.vs_current_bb = gs.vs_current_bb` by
    (qpat_assum `run_inst_seq (emitted_insts guard_st header_st) gs = OK ps` mp_tac >>
     qpat_assum `EVERY _ (emitted_insts guard_st header_st)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
       (emitted_insts guard_st header_st)` by fs[EVERY_MEM] >>
     drule_all entrySinkExtractionTheory.run_inst_seq_preserves_entry_control >> simp[]) >>
  `hs.vs_current_bb = header_st.cs_current_bb /\
   hs.vs_inst_idx = LENGTH header_st.cs_current_insts /\
   allocas_from lo hs /\ lo <= hs.vs_alloca_next` by
    (simp[Abbr `hs`] >> decide_tac) >>
  `fn_has_code header_st loop_st func` by
    (qpat_assum `cs_extends st guard_st` mp_tac >>
     qpat_assum `cs_extends guard_st header_st` mp_tac >>
     qpat_assum `cs_extends header_st loop_st` mp_tac >>
     qpat_assum `fn_has_code st loop_st func` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     `cs_extends st header_st` by metis_tac[cs_extends_trans] >>
     drule_all fn_has_code_split >> simp[]);

val dynamic_init_path_tac =
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (hs,Gheader,tnheader) []
    (OK (ix with vs_inst_idx := LENGTH loop_st.cs_current_insts),Gindex,tnindex)` by
    (rpt gen_tac >> first_x_assum irule >> simp[]) >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) []
    (OK (indexed with vs_inst_idx := LENGTH loop_st.cs_current_insts),Gindex,tnindex)` by
    (rpt gen_tac >>
     `ix with vs_inst_idx := LENGTH loop_st.cs_current_insts =
        indexed with vs_inst_idx := LENGTH loop_st.cs_current_insts` by simp[Abbr `ix`] >>
     irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl_tac [`Gheader`,`hs`,`tnheader`] >> conj_tac
     >- (irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
         qexistsl_tac [`Gguard`,`gs`,`tnguard`] >> simp[]) >> metis_tac[]);

val dynamic_init_effect_tac =
  drule_all (abi_valid_allocated_array_init_effect |> Q.INST [`n` |-> `LENGTH vs`]) >>
  disch_then (qx_choose_then `same_indexed` (qx_choose_then `physical_slot` strip_assume_tac)) >>
  `same_indexed = indexed` by
    (qpat_assum `run_inst_seq (emitted_insts st loop_st) s = OK same_indexed` mp_tac >>
     qpat_assum `run_inst_seq (emitted_insts st loop_st) s = OK indexed` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
  qpat_x_assum `same_indexed = indexed` SUBST_ALL_TAC;

(* Preserve every operand present at the exact entry, through all phases. *)
val dynamic_init_live_tac =
  `!x. not_fresh_at st x ==>
    lookup_var x indexed = lookup_var x s /\ FLOOKUP Gindex x = FLOOKUP G x /\
    op_taint tnindex (Var x) = op_taint tn (Var x)` by
    (qpat_assum `!x. not_fresh_at st x ==> _` mp_tac >>
     qpat_assum `!x. not_fresh_at guard_st x ==> _` mp_tac >>
     qpat_assum `!x. not_fresh_at header_st x ==> _` mp_tac >>
     qpat_assum `st.cs_next_var <= guard_st.cs_next_var` mp_tac >>
     qpat_assum `header_st.cs_next_var = guard_st.cs_next_var + 1` mp_tac >>
     simp_tac (srw_ss()) [Abbr `ix`, Abbr `hs`, Abbr `ps`, Abbr `gs`,
       venomStateTheory.lookup_var_def] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     `not_fresh_at guard_st x /\ not_fresh_at header_st x` by
       (fs[loweringStateRelDefsTheory.not_fresh_at_def] >> decide_tac) >>
     metis_tac[]);

val dynamic_init_windows_tac =
  `tnindex.t_mem SUBSET tn.t_mem` by
    (simp[] >> pred_setLib.SET_TAC[]) >>
  `ptr_covers Gindex tnindex output indexed (type_memory_bytes ce (ArrayT et (Dynamic maxn)))` by
    (irule decoderGhostFramePtrTheory.ptr_covers_frame >>
     qexistsl_tac [`G`,`s`,`tn`] >> simp[]) >>
  `abi_decode_ptr_window Gindex tnindex indexed source (n2w B) L` by
    (qpat_assum `abi_decode_ptr_window G tn s source _ _` mp_tac >>
     rewrite_tac[abiDecodePtrMemberFrameTheory.abi_decode_ptr_window_def] >> strip_tac >>
     simp[] >> irule decoderGhostFramePtrTheory.ptr_covers_frame >>
     qexistsl_tac [`G`,`s`,`tn`] >> simp[]);

(* Align physical and ghost index resources with the semantic common endpoint. *)
val dynamic_init_index_resources_tac =
  `eval_operand ip indexed = SOME (n2w slot)` by
    (qpat_x_assum `eval_operand ip ix = SOME (n2w slot)` mp_tac >>
     simp[Abbr `ix`, venomStateTheory.eval_operand_def,
       venomStateTheory.lookup_var_def]) >>
  `slot = physical_slot` by
    (qpat_assum `eval_operand (FST setup) indexed = SOME (n2w physical_slot)` mp_tac >>
     qpat_assum `eval_operand ip indexed = SOME (n2w slot)` mp_tac >>
     qpat_assum `setup = (ip,cnt)` mp_tac >>
     qpat_assum `slot+32 < dimword (:256)` mp_tac >>
     qpat_assum `physical_slot+32 < dimword (:256)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     `slot < dimword (:256) /\ physical_slot < dimword (:256)` by decide_tac >>
     gvs[wordsTheory.n2w_11]) >>
  `ptr_covers Gindex tnindex qi indexed 32` by
    (qpat_x_assum `ptr_covers Gindex tnindex qi _ 32` mp_tac >>
     simp[Abbr `ix`, ghostPcTransportPtrTheory.ptr_covers_inst_idx]) >>
  `!x. cnt = Var x ==> not_fresh_at header_st x` by
    (qpat_assum `abi_decode_array_header (Var output) (Var ar) MLOAD guard_st = (cnt,header_st)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[abi_decode_array_header_def, emit_op_def, emit_void_def,
       fresh_var_def, fresh_id_def, emit_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, loweringStateRelDefsTheory.not_fresh_at_def] >>
     rpt strip_tac >> gvs[] >> metis_tac[ASCIInumbersTheory.toString_inj]) >>
  `op_prov Gindex cnt = NONE /\ op_taint tnindex cnt = {}` by
    (qpat_assum `op_prov Gheader cnt = NONE` mp_tac >>
     qpat_assum `op_taint tnheader cnt = {}` mp_tac >>
     qpat_assum `!x. not_fresh_at header_st x ==> _` mp_tac >>
     qpat_assum `!x. cnt = Var x ==> not_fresh_at header_st x` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     Cases_on `cnt` >> gvs[ptrDisciplineTheory.op_prov_def,
       ptrDisciplineTheory.op_taint_def] >> metis_tac[]);

val dynamic_init_history_tac =
  `loop_st.cs_current_bb = st.cs_current_bb /\
   isPREFIX st.cs_current_insts loop_st.cs_current_insts` by
    (conj_tac >- simp[] >>
     qpat_assum `inst_extends st guard_st` mp_tac >>
     qpat_assum `inst_extends guard_st header_st` mp_tac >>
     qpat_assum `inst_extends header_st loop_st` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     `inst_extends st loop_st` by metis_tac[inst_extends_trans] >>
     fs[inst_extends_def, rich_listTheory.IS_PREFIX_APPEND]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st loop_st)` by
    (simp[] >> fs[EVERY_MEM]) >>
  `alloca_history func (indexed with vs_inst_idx := LENGTH loop_st.cs_current_insts)` by
    (irule entryDecoderHistoryFrameTheory.entry_straight_line_alloca_history >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`s`,`st`] >> simp[]);

(* Finish initialization at the instruction cursor used by the ghost path. *)
val dynamic_init_endpoint_tac =
  qabbrev_tac `initialized = indexed with vs_inst_idx := LENGTH loop_st.cs_current_insts` >>
  `abi_valid_allocated_effect ctx func cenv cx es st.cs_next_var
     (abi_malformed_scratch_sites st en func) dstid d
     (type_memory_bytes ce (ArrayT et (Dynamic maxn))) s initialized` by
    (simp_tac bool_ss [Abbr `initialized`] >>
     qpat_assum `abi_valid_allocated_effect _ _ _ _ _ _ _ _ _ _ s indexed` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[ abiValidAllocatedArrayPrefixTheory.abi_valid_allocated_effect_def,
       abiMalformedMemberSetupTheory.abi_malformed_resource_post_inst_idx,
       abiValidAllocatedContractTheory.abi_valid_allocated_frame_def,
       abiMalformedSiteFrameTheory.abi_malformed_site_range_def] >> strip_tac >> simp[]);

val dynamic_init_endpoint_resources_tac =
  `ptr_covers Gindex tnindex output initialized
       (type_memory_bytes ce (ArrayT et (Dynamic maxn))) /\
   abi_decode_ptr_window Gindex tnindex initialized source (n2w B) L /\
   ptr_covers Gindex tnindex qi initialized 32 /\
   eval_operand ip initialized = SOME (n2w slot) /\
   eval_operand cnt initialized = SOME (n2w (LENGTH vs)) /\
   mload slot initialized = 0w /\
   abi_valid_allocated_array_prefix tv' vs 0 d initialized /\
   fresh_vars_wrt ceiling initialized` by
    (simp_tac bool_ss [Abbr `initialized`] >>
     map_every (fn q => qpat_assum q mp_tac)
       [`ptr_covers Gindex tnindex output indexed _`,
        `abi_decode_ptr_window Gindex tnindex indexed source _ _`,
        `ptr_covers Gindex tnindex qi indexed 32`,
        `eval_operand ip indexed = SOME (n2w slot)`,
        `eval_operand (SND setup) indexed = SOME (n2w (LENGTH vs))`,
        `setup = (ip,cnt)`, `slot = physical_slot`,
        `mload physical_slot indexed = 0w`,
        `mem_word_at d indexed.vs_memory = n2w (LENGTH vs)`,
        `fresh_vars_wrt ceiling indexed`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     gvs[abiDecodePtrMemberFrameTheory.abi_decode_ptr_window_def,
       abiValidAllocatedArrayPrefixTheory.abi_valid_allocated_array_prefix_zero,
       venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
       venomStateTheory.mload_def, loweringStateRelDefsTheory.fresh_vars_wrt_def]);

val dynamic_init_transport_tac =
  `abi_decode_array_loop_init (Var output) pos MLOAD (Var source) hi maxn
     (abi_embedded_static_size ce.ce_struct_fields et) st = ((ip,cnt),loop_st)` by
    (qpat_assum `abi_decode_array_loop_init _ _ _ _ _ _ _ _ = _` mp_tac >>
     qpat_assum `setup = (ip,cnt)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
  `!x. not_fresh_at st x ==> lookup_var x initialized = lookup_var x s /\
     FLOOKUP Gindex x = FLOOKUP G x /\ op_taint tnindex (Var x) = op_taint tn (Var x)` by
    (qpat_assum `!x. not_fresh_at st x ==> lookup_var x indexed = _ /\ _` mp_tac >>
     simp_tac bool_ss [Abbr `initialized`, venomStateTheory.lookup_var_def] >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
  `tnindex.t_stor = tn.t_stor /\ tnindex.t_trans = tn.t_trans /\ tnindex.t_imm = tn.t_imm` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`tnindex.t_stor = tnheader.t_stor`, `tnheader.t_stor = tnguard.t_stor`,
        `tnguard.t_stor = tn.t_stor`, `tnindex.t_trans = tnheader.t_trans`,
        `tnheader.t_trans = tnguard.t_trans`, `tnguard.t_trans = tn.t_trans`,
        `tnindex.t_imm = tnheader.t_imm`, `tnheader.t_imm = tnguard.t_imm`,
        `tnguard.t_imm = tn.t_imm`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
  `allocas_from lo initialized /\ lo <= initialized.vs_alloca_next` by
    (qpat_assum `abi_valid_allocated_effect _ _ _ _ _ _ _ _ _ _ s initialized` mp_tac >>
     qpat_assum `allocas_from lo s` mp_tac >>
     qpat_assum `lo <= s.vs_alloca_next` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [abiValidAllocatedArrayPrefixTheory.abi_valid_allocated_effect_def,
       abi_malformed_resource_post_def, ptrDisciplineTheory.allocas_from_def] >>
     rpt strip_tac >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]);

(* Iteration handoff. The physical slot is the preserved index allocation;
   nv is the compiler's first fresh variable after the child decoder. *)
val dynamic_backedge_resources_tac =
  `q <> nv` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`abi_decoder_operand_live middle.cs_next_var (Var q)`,
       `middle.cs_next_var <= end_st.cs_next_var`,
       `nv = STRING #"%" (toString end_st.cs_next_var)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[abiDecoderReentryTheory.abi_decoder_operand_live_def] >> rpt strip_tac >>
     gvs[abiDecoderReentryTheory.abi_decoder_older_vars_def] >> metis_tac[]) >>
  `lookup_block child_end.vs_current_bb func.fn_blocks = SOME back_bb` by
    (qpat_assum `child_end.vs_current_bb = _` mp_tac >>
     qpat_assum `lookup_block end_st.cs_current_bb func.fn_blocks = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp child_end` by simp[] >>
  `slot+32 <= child_end.vs_alloca_next` by
    (qpat_assum `alloca_inv child_end` mp_tac >>
     qpat_assum `FLOOKUP child_end.vs_allocas index_id = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[venomMemDefsTheory.alloca_inv_def, venomMemDefsTheory.alloca_next_valid_def] >>
     metis_tac[]);

val dynamic_backedge_joint_tac =
  drule_all decoderLoopBackedgeCorePtrTheory.decoder_index_backedge_ptr_core_uniform_origin >>
  disch_then (qspec_then `PG`
    (qx_choose_then `backG` (qx_choose_then `backtn`
      (qx_choose_then `backstate` strip_assume_tac)))) >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
     (child_end,childG,childtn) [] (OK backstate,backG,backtn)` by
    (qpat_x_assum `slot+32 <= child_end.vs_alloca_next ==> _` irule >>
     first_assum ACCEPT_TAC);

val dynamic_backedge_frame_tac =
  `fresh_vars_wrt ceiling backstate /\
   backstate.vs_allocas = child_end.vs_allocas /\
   backstate.vs_alloca_next = child_end.vs_alloca_next /\
   backstate.vs_call_ctx = child_end.vs_call_ctx` by
    (drule_all decoderLoopBackedgeCorePtrTheory.decoder_index_backedge_replay_frame >>
     simp_tac bool_ss []) >>
  `~backstate.vs_halted /\ backstate.vs_current_bb = hdr /\ backstate.vs_inst_idx = 0` by
    (qpat_assum `backstate = _` mp_tac >>
     qpat_assum `~child_end.vs_halted` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[venomStateTheory.jump_to_def, venomStateTheory.mstore_def,
       venomStateTheory.write_memory_with_expansion_def, venomStateTheory.update_var_def]);

end

Theory bodyFullAbiDecodeLoopBodyObserved
Ancestors
  bodyFullHashKeccakFixed[qualified,ignore_grammar]
  bodyFullAbiDecodeLoopPhasesObserved bodyFullAbiDecodeLoopResource
  gasOriginPtrLabels abiDecoderCoherence abiDecoderMemberInfos abiDecoderReentry
  abiDecoderOffset abiEncoder compileEnv venomInst venomExecSemantics venomState
  loweringStateRelDefs stateRelProj words list rich_list finite_map arithmetic
  valueEncodingProps abiStaticAggregateProps ptrDiscipline robustCopyTransportPtr fragGasPath
Libs
  bodyFullAbiDecodeRuntimeLoopSyntaxLib bodyFullAbiDecodeLoopObservedSyntaxLib

Theorem loop_body_setup_snapshots[local]:
  (^loop_resource) anchor j s G tn /\ not_fresh_at anchor counter /\
  anchor.cs_next_var <= loop_body.cs_next_var /\
  anchor.cs_next_id <= loop_body.cs_next_id ==>
  (^owned_decoder_state)
    ((aid,counter,cell,32,mem_bytes_at cell 32 s.vs_memory)::live)
    ((d,mem_bytes_at d (32+j*msz) s.vs_memory)::protected) loop_body s G tn
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?inst. MEM inst (fn_insts fn) /\ _ /\ _ /\ inst.inst_id = output_id`
    (qx_choose_then `inst` strip_assume_tac) >>
  asm_rewrite_tac[EVERY_DEF] >> simp[] >>
  conj_tac >-
    (qpat_assum `EVERY (\(aid,p,b,k,bytes). aid < anchor.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,k) /\ _) live` mp_tac >>
     qpat_assum `anchor.cs_next_id <= loop_body.cs_next_id` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[EVERY_MEM, pairTheory.FORALL_PROD] >> rpt strip_tac >>
     first_x_assum (drule_then strip_assume_tac) >> simp[] >> decide_tac) >>
  conj_tac >- (qexists_tac `inst` >> asm_rewrite_tac[]) >>
  conj_tac >- metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  conj_tac >- metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  qpat_assum `EVERY (\(id,p,b,k,bytes). not_fresh_at anchor p) live` mp_tac >>
  qpat_assum `anchor.cs_next_var <= loop_body.cs_next_var` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[EVERY_MEM, pairTheory.FORALL_PROD] >>
  metis_tac[freshWritesTheory.not_fresh_at_mono]
QED

Theorem loop_snapshot_word[local]:
  mem_bytes_at d (32+n) m = mem_bytes_at d (32+n) m' ==>
  mem_word_at d m = mem_word_at d m'
Proof
  strip_tac >> rewrite_tac[abiStaticAggregatePropsTheory.mem_word_at_bytes] >>
  AP_TERM_TAC >>
  drule_then (qspecl_then [`0`,`32`] mp_tac) mem_bytes_at_translated_window >>
  simp[]
QED

val loop_body_length_statement = close_statement
  (mk_body_observed_statement guarded_plus_typed
    ``\j0 k s tn. (^completed_robust_typed) j0 k s tn /\
                  mem_word_at d s.vs_memory = (w:256 word)``);

Theorem abi_decode_loop_body_length_observed_conditional:
  ^loop_body_length_statement
Proof
  rpt gen_tac >> strip_tac >>
  qmatch_asmsub_rename_tac `(^loop_resource) anchor j s G tn` >>
  qpat_x_assum `(\j0 k s tn. (^completed_robust_typed) j0 k s tn /\ _) j0 j s tn`
    (map_every assume_tac o CONJUNCTS o BETA_RULE) >>
  `not_fresh_at anchor counter /\ not_fresh_at anchor input` by
    (qpat_assum `abi_decoder_operand_live anchor.cs_next_var (Var counter)` mp_tac >>
     qpat_assum `abi_decoder_operand_live anchor.cs_next_var (Var input)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
       not_fresh_at_def, pred_setTheory.GSPECIFICATION] >> metis_tac[]) >>
  drule_all loop_body_setup_snapshots >> strip_tac >>
  qpat_assum `(^loop_resource) anchor j s G tn`
    (map_every assume_tac o CONJUNCTS o BETA_RULE) >>
  `local_ptrs_reserved ce loop_body /\ not_fresh_at loop_body input /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at loop_body x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at loop_body x)` by
    (qpat_assum `local_ptrs_reserved ce anchor` mp_tac >>
     qpat_assum `!x sz. ce.ce_return_buf = _ ==> _` mp_tac >>
     qpat_assum `!x sz. ce.ce_return_pc = _ ==> _` mp_tac >>
     qpat_assum `not_fresh_at anchor input` mp_tac >>
     qpat_assum `origin.cs_next_var <= anchor.cs_next_var` mp_tac >>
     qpat_assum `anchor.cs_next_var <= loop_body.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var,
       freshWritesTheory.not_fresh_at_mono, LESS_EQ_TRANS]) >>
  `abi_decoder_operand_live loop_body.cs_next_var src /\
   abi_decoder_operand_live loop_body.cs_next_var hi /\
   abi_decoder_operand_live loop_body.cs_next_var (Var dst) /\
   abi_decoder_operand_live loop_body.cs_next_var (Var counter)` by
    (qpat_assum `abi_decoder_operand_live _ src` mp_tac >>
     qpat_assum `abi_decoder_operand_live _ hi` mp_tac >>
     qpat_assum `abi_decoder_operand_live _ (Var dst)` mp_tac >>
     qpat_assum `abi_decoder_operand_live _ (Var counter)` mp_tac >>
     qpat_assum `anchor.cs_next_var <= loop_body.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[abi_decoder_operand_live_mono]) >>
  `dec_info_needs_offset ei ==> 32 <= asz` by
    (qpat_assum `abi_decoder_coherent ce env sf ty tv` mp_tac >>
     qpat_assum `ei = _` mp_tac >> qpat_assum `asz = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     drule abi_decoder_coherent_header >>
     drule abiDecoderDynamicTheory.abi_decoder_coherent_dynamic >>
     gvs[abi_decoder_header_def, abi_decoder_needs_offset_iff,
       abiDecodeRangesTheory.abi_member_head_size_def]) >>
  `cell < dimword (:256)` by
    (qpat_assum `!H. V H ==> stmt_state_rel _ _ _ _ _ _ s /\ _` drule >>
     strip_tac >>
     drule stmt_state_rel_alloca_room >>
     disch_then (mp_then Any mp_tac exprLoweringPropsTheory.alloca_room_next_lt) >>
     decide_tac) >>
  `asz < dimword (:256)` by
    (qpat_assum `srcoff+32+n*asz <= h` mp_tac >>
     qpat_assum `h <= LENGTH input_bytes` mp_tac >>
     qpat_assum `w2n input_word+LENGTH input_bytes < dimword (:256)` mp_tac >>
     qpat_assum `j<n` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     Cases_on `n` >> simp[ADD1, RIGHT_ADD_DISTRIB] >> decide_tac) >>
  `lookup_var dst s = SOME (n2w d)` by
    (qpat_assum `eval_operand (Var dst) s = SOME (n2w d)` mp_tac >>
     pure_rewrite_tac[eval_operand_def] >> disch_then irule) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    (qpat_assum `!H. V H ==> stmt_state_rel H ctx fn ce cx es s /\ _`
       (drule_then (mp_tac o CONJUNCT1)) >>
     MATCH_ACCEPT_TAC bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) >>
  mp_tac (Q.INST [
    `sa` |-> `loop_body`, `sb` |-> `child`,
    `live` |-> `(aid,counter,cell,32,mem_bytes_at cell 32 s.vs_memory)::live`,
    `protected` |-> `(d,mem_bytes_at d (32+j*msz) s.vs_memory)::protected`]
    (SPEC_ALL abi_decode_loop_setup_observed)) >>
  (impl_tac >- (asm_rewrite_tac[] >> BETA_TAC >> asm_rewrite_tac[])) >>
  (impl_tac >- (BETA_TAC >> first_assum (ACCEPT_TAC o BETA_RULE))) >>
  strip_tac
  >- (disj1_tac >> qexistsl_tac [`t`,`Gf`,`tnf`] >> conj_tac
      >- (rpt strip_tac >> first_assum MATCH_ACCEPT_TAC) >>
      rpt strip_tac >>
      qpat_assum `!obs. fn_has_code obs_start obs_finish obs ==> _` drule >>
      strip_tac >> first_assum drule >> simp[]) >>
  rename1 `child_dst = Var child_ptr` >>
  `FLOOKUP Gu child_ptr = SOME (output_base,output_cap)` by asm_rewrite_tac[] >>
  `asz = abi_member_head_size (vyper_to_abi_type env ty)` by
    (drule abi_decoder_coherent_header >> simp[abi_decoder_header_def]) >>
  `local_ptrs_reserved ce child /\
   abi_decoder_operand_live child.cs_next_var (Var input)` by
    (qpat_assum `local_ptrs_reserved ce loop_body` mp_tac >>
     qpat_assum `abi_decoder_operand_live anchor.cs_next_var (Var input)` mp_tac >>
     qpat_assum `anchor.cs_next_var <= loop_body.cs_next_var` mp_tac >>
     qpat_assum `loop_body.cs_next_var <= child.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var,
       abi_decoder_operand_live_mono, LESS_EQ_TRANS]) >>
  `op_prov Gu hi = NONE /\ op_taint tnu hi = {} /\
   op_taint tnu (Var input) = {}` by
    (`eval_operand hi u = eval_operand hi s /\
      op_taint tnu hi = op_taint tn hi /\ op_prov Gu hi = op_prov G hi` by
       (irule decoderArraySetupPtrTheory.old_operand_ghost_frame >>
        reverse conj_tac >- asm_rewrite_tac[] >>
        qexists_tac `loop_body` >>
        conj_tac >-
          (rpt strip_tac >>
           qpat_assum `abi_decoder_operand_live loop_body.cs_next_var hi` mp_tac >>
           qpat_assum `hi = Var x` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
           rpt strip_tac >> gvs[abi_decoder_operand_live_def,
             abi_decoder_older_vars_def, not_fresh_at_def]) >>
        asm_rewrite_tac[]) >>
     `op_taint tn (Var input) = {}` by
       (qpat_assum `abi_decode_ptr_window G tn s input _ _` mp_tac >>
        pure_rewrite_tac[abiDecodePtrMemberFrameTheory.abi_decode_ptr_window_def,
          bodyPtrDefsTheory.ptr_covers_def] >> strip_tac >> asm_rewrite_tac[]) >>
     asm_rewrite_tac[] >>
     qpat_assum `!x. not_fresh_at loop_body x ==> _` drule >> simp[]) >>
  `j*msz+msz <= n*msz` by
    (qpat_assum `j<n` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     once_rewrite_tac[MULT_COMM] >> once_rewrite_tac[ADD_COMM] >>
     rewrite_tac[GSYM MULT_SUC, LE_MULT_LCANCEL] >> decide_tac) >>
  `(^guarded_to_buf_entry) child_dst child_src MLOAD (Var input) hi ei env sf ty tv
    ((aid,counter,cell,32,mem_bytes_at cell 32 s.vs_memory)::live)
    ((d,mem_bytes_at d (32+j*msz) s.vs_memory)::protected)
    child returned u Gu tnu (d+32+j*msz)` by
    (qpat_assum `(^owned_decoder_state) _ _ child u Gu tnu`
       (map_every assume_tac o CONJUNCTS o BETA_RULE) >>
     BETA_TAC >> asm_rewrite_tac[] >>
     qpat_assum `msz = type_memory_size tv` (fn th => rewrite_tac[GSYM th]) >>
     conj_tac >- (qexistsl_tac [`q`,`h`] >> asm_rewrite_tac[] >>
       rpt strip_tac >>
       qpat_assum `q + asz <= h` mp_tac >>
       qpat_assum `asz = abi_member_head_size _` (fn th => rewrite_tac[th])) >>
     conj_tac >- (qexists_tac `H` >> asm_rewrite_tac[]) >>
     conj_tac >- (qexists_tac `child_ptr` >>
       pure_rewrite_tac[SUB_EQUAL_0, ADD_CLAUSES] >>
       conj_tac >- REFL_TAC >> conj_tac >- first_assum MATCH_ACCEPT_TAC >>
       first_assum MATCH_ACCEPT_TAC) >>
     BETA_TAC >> conj_tac >- (qexistsl_tac [`q`,`h`] >> asm_rewrite_tac[]) >>
     conj_tac >- first_assum MATCH_ACCEPT_TAC >>
     conj_tac >-
       (qpat_assum `abi_decoder_operand_live loop_body.cs_next_var hi` mp_tac >>
        qpat_assum `loop_body.cs_next_var <= child.cs_next_var` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> metis_tac[abi_decoder_operand_live_mono]) >>
     conj_tac >- (simp[]) >> conj_tac >- rewrite_tac[LESS_EQ_REFL] >>
     conj_tac >-
       (qpat_assum `d+32+n*msz <= output_base+output_cap` mp_tac >>
        qpat_assum `j*msz+msz <= n*msz` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
     conj_tac >-
       (qpat_assum `w2n input_word + LENGTH input_bytes <= d \/ d+32+n*msz <= _` mp_tac >>
        qpat_assum `j*msz+msz <= n*msz` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
     conj_tac >-
       (qpat_assum `EVERY (\(id,p,b,k,bytes). id < anchor.cs_next_id /\ (b+k <= d \/ _)) live` mp_tac >>
        qpat_assum `cell+32 <= d \/ d+32+n*msz <= cell` mp_tac >>
        qpat_assum `EVERY (\(aid,p,b,k,bytes). aid < child.cs_next_id /\ _) (_::live)` mp_tac >>
        qpat_assum `j*msz+msz <= n*msz` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >>
        simp[EVERY_DEF, EVERY_MEM, pairTheory.FORALL_PROD] >>
        rpt strip_tac >>
        rpt (first_x_assum (drule_then strip_assume_tac)) >>
        asm_rewrite_tac[] >> decide_tac) >>
     qpat_assum `EVERY (\(a,bytes). a+LENGTH bytes <= d \/ _) protected` mp_tac >>
     qpat_assum `j*msz+msz <= n*msz` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[EVERY_DEF, EVERY_MEM, pairTheory.FORALL_PROD] >>
     rpt strip_tac >> first_x_assum drule >> decide_tac) >>
  `(^contained) ((d,mem_bytes_at d (32+j*msz) s.vs_memory)::protected)` by
    (qpat_assum `(^contained) protected` (mp_tac o BETA_RULE) >>
     qpat_assum `output_base <= d` mp_tac >>
     qpat_assum `d+32+n*msz <= output_base+output_cap` mp_tac >>
     qpat_assum `j*msz+msz <= n*msz` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[EVERY_DEF,LENGTH_mem_bytes_at] >> decide_tac) >>
  qpat_x_assum `(^guarded_plus_typed) child_dst child_src MLOAD (Var input) hi ei`
    (fn ih => qpat_assum `(^guarded_to_buf_entry) child_dst child_src MLOAD (Var input) hi ei env sf ty tv _ _ child returned u Gu tnu _`
      (fn entry => qpat_assum `(^contained) (_::protected)` (fn bounds =>
        qpat_assum `(^input_origin) u` (fn origin =>
          mp_tac (MATCH_MP (BETA_RULE ih)
            (BETA_RULE (LIST_CONJ [entry,bounds,origin]))))))) >>
  reverse (disch_then (qx_choose_then `r` (qx_choose_then `G'` (qx_choose_then `tn'`
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac DISJ_CASES_TAC))))))
  >- (pop_assum (qx_choose_then `t` assume_tac) >>
      disj1_tac >> qexistsl_tac [`t`,`G'`,`tn'`] >> conj_tac
      >- (qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _` mp_tac >>
          qpat_assum `!H. V H ==> gas_origin_ptr_path _ (u,Gu,tnu) _ _` mp_tac >>
          qpat_assum `r = Abort _ _` mp_tac >>
          POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
          metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_append,APPEND]) >>
      rpt strip_tac >>
      qpat_assum `!obs. fn_has_code anchor _ obs ==> fn_has_code loop_body child obs /\ _`
        (qspec_then `obs` mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
      qpat_assum `!obs. fn_has_code loop_body child obs ==> gas_path ctx obs s 0 (OK u)`
        (qspec_then `obs` mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >> disch_tac >>
      qpat_assum `!obs. fn_has_code child returned obs ==> gas_path ctx obs u 0 r`
        (qspec_then `obs` mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >> disch_tac >>
      qpat_assum `gas_path ctx obs s 0 (OK u)` mp_tac >>
      qpat_assum `gas_path ctx obs u 0 r` mp_tac >>
      qpat_assum `r = Abort Revert_abort t` SUBST1_TAC >>
      POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
      drule_all gas_path_then >> simp[]) >>
  pop_assum (qx_choose_then `t` (map_every assume_tac o CONJUNCTS)) >>
  `t.vs_labels = s.vs_labels` by
    (qpat_assum `!H. V H ==> gas_origin_ptr_path _ (u,Gu,tnu) _ _` mp_tac >>
     qpat_assum `V H` mp_tac >> qpat_assum `r = OK t` mp_tac >>
     qpat_assum `u.vs_labels = s.vs_labels` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     metis_tac[gas_origin_ptr_path_preserves_labels]) >>
  `!x. not_fresh_at anchor x ==> lookup_var x t = lookup_var x s /\
       FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x)` by
    (qpat_assum `!x. not_fresh_at child x ==> _` mp_tac >>
     qpat_assum `!x. not_fresh_at loop_body x ==> _` mp_tac >>
     qpat_assum `anchor.cs_next_var <= loop_body.cs_next_var` mp_tac >>
     qpat_assum `loop_body.cs_next_var <= child.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `eval_operand (Var iv) t = SOME (n2w j) /\
   op_prov G' (Var iv) = NONE /\ op_taint tn' (Var iv) = {}` by
    (qpat_assum `!x. not_fresh_at child x ==> _`
       (qspec_then `iv` mp_tac) >>
     qpat_assum `abi_decoder_operand_live child.cs_next_var idx` mp_tac >>
     qpat_assum `eval_operand idx u = SOME (n2w j)` mp_tac >>
     qpat_assum `op_prov Gu idx = NONE` mp_tac >>
     qpat_assum `op_taint tnu idx = {}` mp_tac >>
     qpat_assum `idx = Var iv` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
       not_fresh_at_def, eval_operand_def, op_prov_def] >> metis_tac[]) >>
  qpat_assum `EVERY (\(id,p,b,k,bytes). id < returned.cs_next_id /\
        FLOOKUP t.vs_allocas id = SOME (b,k) /\ _) (_::live)`
    ((map_every assume_tac o CONJUNCTS) o SIMP_RULE (srw_ss()) [EVERY_DEF]) >>
  qpat_assum `EVERY (\(a,bytes). mem_bytes_at a (LENGTH bytes) t.vs_memory = bytes)
      (_::protected)`
    ((map_every assume_tac o CONJUNCTS) o
      SIMP_RULE (srw_ss()) [EVERY_DEF,LENGTH_mem_bytes_at]) >>
  `!name b k. local_region ce es.scopes t name b k ==>
      cell+32 <= b \/ b+k <= cell` by
    (rpt strip_tac >>
     `local_region ce es.scopes t name b k <=> local_region ce es.scopes s name b k` by
       (MATCH_MP_TAC local_region_lookup_cong >>
        qpat_assum `local_ptrs_reserved ce anchor` mp_tac >>
        qpat_assum `!x. not_fresh_at anchor x ==> _` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >>
        simp[local_ptrs_reserved_def] >> metis_tac[]) >>
     qpat_assum `!name b k. local_region ce es.scopes s name b k ==> cell+32 <= b \/ b+k <= cell`
       (qspecl_then [`name`,`b`,`k`] mp_tac) >>
     qpat_assum `local_region ce es.scopes t name b k <=> _` mp_tac >>
     qpat_assum `local_region ce es.scopes t name b k` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `stmt_state_rel H ctx fn ce cx es t` by
    (qpat_assum `!H. V H ==> stmt_state_rel H ctx fn ce cx es t /\ _`
       (qspec_then `H` mp_tac) >> simp[]) >>
  `local_ptrs_rel fn ce es.scopes t` by
    (drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
  `cell+32 < dimword (:256)` by
    (drule stmt_state_rel_alloca_room >>
     disch_then (mp_then Any mp_tac exprLoweringPropsTheory.alloca_room_next_lt) >>
     qpat_assum `cell+32 <= t.vs_alloca_next` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  `loop_body.cs_next_var <= returned.cs_next_var /\
   anchor.cs_next_var <= returned.cs_next_var` by
    (qpat_assum `anchor.cs_next_var <= loop_body.cs_next_var` mp_tac >>
     qpat_assum `loop_body.cs_next_var <= child.cs_next_var` mp_tac >>
     qpat_assum `child.cs_next_var <= returned.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  `local_ptrs_reserved ce returned /\ not_fresh_at returned counter /\
   not_fresh_at returned input /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at returned x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at returned x)` by
    (qpat_assum `local_ptrs_reserved ce loop_body` mp_tac >>
     qpat_assum `not_fresh_at anchor counter` mp_tac >>
     qpat_assum `not_fresh_at anchor input` mp_tac >>
     qpat_assum `!x sz. ce.ce_return_buf = _ ==> not_fresh_at loop_body x` mp_tac >>
     qpat_assum `!x sz. ce.ce_return_pc = _ ==> not_fresh_at loop_body x` mp_tac >>
     qpat_assum `loop_body.cs_next_var <= returned.cs_next_var` mp_tac >>
     qpat_assum `anchor.cs_next_var <= returned.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var,
       freshWritesTheory.not_fresh_at_mono]) >>
  `!H. V H ==> gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,G',tn')` by
    (qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _` mp_tac >>
     qpat_assum `!H. V H ==> gas_origin_ptr_path _ (u,Gu,tnu) _ _` mp_tac >>
     qpat_assum `r = OK t` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_append, APPEND]) >>
  `allocas_from lo t` by
    (qpat_assum `!H. V H ==> gas_origin_ptr_path _ (s,G,tn) _ _`
       (qspec_then `H` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     disch_then (mp_then Any mp_tac member_origin_allocas_from) >> simp[]) >>
  `!H. V H ==> ghost_inv_at (DF H) lo delta ce cx es G' tn' t /\
      ghost_kept_at lo ce es0 origin G0 tn0 s0 G' tn' /\
      stmt_state_rel H ctx fn ce cx es t` by
    (qpat_assum `!H. V H ==> stmt_state_rel H ctx fn ce cx es t /\ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  qabbrev_tac `snapshots =
    (w2n input_word,input_bytes)::
    (d,mem_bytes_at d (32+SUC j*msz) t.vs_memory)::
    (MAP (\(id,p,b,k,bytes). (b,bytes)) live ++ protected)` >>
  `EVERY (\(a,bytes). a+LENGTH bytes <= cell \/ cell+32 <= a) snapshots` by
    (simp[Abbr `snapshots`, EVERY_DEF, EVERY_APPEND, EVERY_MAP,
       LENGTH_mem_bytes_at] >>
     conj_tac >-
       (qpat_assum `cell+32 <= d \/ _` mp_tac >>
        qpat_assum `j*msz+msz <= n*msz` mp_tac >>
        qpat_assum `msz = type_memory_size tv` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> strip_tac >> gvs[MULT] >> decide_tac) >>
     qpat_assum `EVERY (\(id,p,b,k,bytes). id <> aid /\ _) live` mp_tac >>
     qpat_assum `EVERY (\(id,p,b,k,bytes). _ /\ FLOOKUP s.vs_allocas id = SOME (b,k) /\ _) live` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[EVERY_MEM, pairTheory.FORALL_PROD] >> metis_tac[]) >>
  `EVERY (\(a,bytes). mem_bytes_at a (LENGTH bytes) t.vs_memory = bytes) snapshots` by
    (simp[Abbr `snapshots`, EVERY_DEF, EVERY_APPEND, EVERY_MAP,
       LENGTH_mem_bytes_at] >>
     qpat_assum `EVERY (\(id,p,b,k,bytes). _ /\ FLOOKUP t.vs_allocas id = SOME (b,k) /\ _) live` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[EVERY_MEM, pairTheory.FORALL_PROD] >> metis_tac[]) >>
  qpat_x_assum `?ci cp. MEM ci (fn_insts fn) /\ _ /\ _ /\ ci.inst_id = aid /\ _`
    (qx_choose_then `ci` (qx_choose_then `counter_owner` strip_assume_tac)) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (qpat_assum `!H. V H ==> stmt_state_rel H ctx fn ce cx es t /\ _`
       (drule_then (mp_tac o CONJUNCT1)) >>
     MATCH_ACCEPT_TAC bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) >>
  mp_tac (Q.INST [
    `s` |-> `t`, `G` |-> `G'`, `tn` |-> `tn'`, `sa` |-> `returned`,
    `id` |-> `returned.cs_next_id`, `prefix` |-> `returned.cs_current_insts`,
    `start` |-> `anchor`, `end_st` |-> `finish'`,
    `bb` |-> `<|bb_label := returned.cs_current_bb;
      bb_instructions := returned.cs_current_insts ++
        abi_decode_backedge_insts returned.cs_next_id iv nv (Var counter) hdr|>`]
    (SPEC_ALL abi_decode_loop_backedge_observed)) >>
  (impl_tac >- (asm_rewrite_tac[] >> simp[])) >>
  (impl_tac >- (qpat_assum `cell+32 <= w2n input_word \/ _` mp_tac >> simp[])) >>
  (impl_tac >- (BETA_TAC >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `back` (qx_choose_then `Gb` (qx_choose_then `tnb`
    (map_every assume_tac o CONJUNCTS o BETA_RULE)))) >>
  disj2_tac >> qexistsl_tac [`back`,`Gb`,`tnb`] >>
  conj_tac >- suspend "success_origin" >>
  conj_tac >- suspend "success_observer" >>
  `~back.vs_halted /\ back.vs_current_bb = hdr /\ back.vs_inst_idx = 0` by
    (qpat_assum `back = jump_to hdr _` (fn th => rewrite_tac[th]) >>
     simp[jump_to_def, venomStateTheory.mstore_def, update_var_def]) >>
  ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >>
  qpat_x_assum `back = jump_to hdr _` kall_tac >>
  conj_asm2_tac >- suspend "success_resource" >>
  conj_tac >- suspend "success_frame" >>
  conj_tac >- (BETA_TAC >> first_assum ACCEPT_TAC) >>
  conj_asm1_tac >- suspend "success_taint" >>
  `mem_bytes_at d (32+SUC j*msz) back.vs_memory =
   mem_bytes_at d (32+SUC j*msz) t.vs_memory` by
    (qpat_assum `EVERY (\(a,bytes). mem_bytes_at a (LENGTH bytes) back.vs_memory = bytes) snapshots` mp_tac >>
     qpat_assum `Abbrev (snapshots = _)` (fn th => rewrite_tac[REWRITE_RULE[markerTheory.Abbrev_def] th]) >>
     POP_ASSUM_LIST (K all_tac) >> simp[EVERY_DEF,LENGTH_mem_bytes_at]) >>
  BETA_TAC >> conj_tac >- suspend "success_robust" >>
  suspend "success_length"
QED

Resume abi_decode_loop_body_length_observed_conditional[success_origin]:
  qpat_assum `!H. V H ==> gas_origin_ptr_path _ (s,G,tn) [] (OK t,G',tn')` mp_tac >>
  qpat_assum `!H. V H ==> gas_origin_ptr_path _ (t,G',tn') [] (OK back,Gb,tnb)` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_append, APPEND]
QED

Resume abi_decode_loop_body_length_observed_conditional[success_observer]:
  rpt strip_tac >>
  qpat_assum `!obs. fn_has_code anchor finish' obs ==> fn_has_code loop_body child obs /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!obs. fn_has_code loop_body child obs ==> gas_path ctx obs s 0 (OK u)`
    (drule_then assume_tac) >>
  qpat_assum `!obs. fn_has_code child returned obs ==> gas_path ctx obs u 0 r`
    (drule_then assume_tac) >>
  qpat_assum `!obs. fn_has_code anchor finish' obs ==> gas_path ctx obs t 0 (OK back)`
    (drule_then assume_tac) >>
  qpat_assum `gas_path ctx obs s 0 (OK u)` mp_tac >>
  qpat_assum `gas_path ctx obs u 0 r` mp_tac >>
  qpat_assum `gas_path ctx obs t 0 (OK back)` mp_tac >>
  qpat_assum `r = OK t` SUBST1_TAC >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  metis_tac[REWRITE_RULE[ADD_CLAUSES] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_then)]
QED

Resume abi_decode_loop_body_length_observed_conditional[success_resource]:
  qpat_x_assum `(^frame) anchor s G tn back Gb tnb /\ _`
    (assume_tac o CONJUNCT1 o BETA_RULE) >>
  `(^owned_decoder_state) live protected returned t G' tn'` by
    (BETA_TAC >> asm_rewrite_tac[] >>
     qpat_assum `EVERY (\(id,p,b,k,bytes). not_fresh_at returned p) (_::live)`
       (ACCEPT_TAC o CONJUNCT2 o SIMP_RULE (srw_ss()) [EVERY_DEF])) >>
  `alloca_history fn back` by
    (qpat_assum `alloca_history fn t` mp_tac >>
     qpat_assum `back.vs_allocas = t.vs_allocas` mp_tac >>
     qpat_assum `back.vs_inst_idx = 0` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[allocaHistoryTheory.alloca_history_jump]) >>
  `allocas_from lo back` by
    (qpat_assum `!H. V H ==> gas_origin_ptr_path _ (t,G',tn') [] (OK back,Gb,tnb)`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (mp_then Any mp_tac member_origin_allocas_from) >> simp[]) >>
  `back.vs_labels = s.vs_labels` by
    (qpat_assum `back.vs_labels = t.vs_labels` (fn th => rewrite_tac[th]) >>
     first_assum ACCEPT_TAC) >>
  `EVERY (\(a,bytes). mem_bytes_at a (LENGTH bytes) back.vs_memory = bytes)
    ((w2n input_word,input_bytes)::
      (MAP (\(id,p,b,k,bytes). (b,bytes)) live ++ protected))` by
    (qpat_assum `EVERY (\(a,bytes). mem_bytes_at a (LENGTH bytes) back.vs_memory = bytes) snapshots` mp_tac >>
     qpat_assum `Abbrev (snapshots = _)` (fn th => rewrite_tac[REWRITE_RULE[markerTheory.Abbrev_def] th]) >>
     POP_ASSUM_LIST (K all_tac) >> simp[EVERY_DEF]) >>
  `abi_decode_ptr_window Gb tnb back input input_word (LENGTH input_bytes) /\
   (!D. V D ==> stmt_state_rel D ctx fn ce cx es back /\
      ghost_inv_at (DF D) lo delta ce cx es Gb tnb back /\
      ghost_kept_at lo ce es0 origin G0 tn0 s0 Gb tnb)` by
    (qpat_assum `!D. V D ==>
        abi_decode_ptr_window Gb tnb back input input_word (LENGTH input_bytes) /\ _` mp_tac >>
     qpat_assum `V H` mp_tac >> POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  irule abi_decode_loop_resource_reconstruct >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >-
    (qexistsl_tac [`G'`,`returned`,`t`,`tn'`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`G`,`s`,`tn`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume abi_decode_loop_body_length_observed_conditional[success_frame]:
  BETA_TAC >>
  qpat_assum `!x. not_fresh_at returned x ==> _` mp_tac >>
  qpat_assum `!x. not_fresh_at anchor x ==> _` mp_tac >>
  qpat_assum `anchor.cs_next_var <= returned.cs_next_var` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  metis_tac[freshWritesTheory.not_fresh_at_mono]
QED

Resume abi_decode_loop_body_length_observed_conditional[success_taint]:
  BETA_TAC >>
  qpat_assum `!i. output_base <= i /\ i < output_base+output_cap /\ i IN tnb.t_mem ==> _` mp_tac >>
  qpat_assum `!i. output_base <= i /\ i < output_base+output_cap /\ i IN tn'.t_mem ==> _` mp_tac >>
  qpat_assum `tnu.t_mem = tn.t_mem` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> metis_tac[]
QED

Resume abi_decode_loop_body_length_observed_conditional[success_robust]:
  BETA_TAC >> qx_gen_tac `i` >> strip_tac >>
  qx_gen_tac `v` >> strip_tac >> qx_gen_tac `mem` >> strip_tac >>
  `i*msz+msz <= SUC j*msz` by
    (qpat_assum `i < SUC j` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     rewrite_tac[GSYM (CONJUNCT2 MULT), LE_MULT_RCANCEL] >> decide_tac) >>
  qabbrev_tac `a = d+32+i*msz` >>
  `mem_bytes_at a msz back.vs_memory = mem_bytes_at a msz t.vs_memory` by
    (qpat_assum `Abbrev (a = _)` (fn th => rewrite_tac[REWRITE_RULE[markerTheory.Abbrev_def, GSYM ADD_ASSOC] th]) >>
     irule mem_bytes_at_translated_window >>
     qexists_tac `32+SUC j*msz` >>
     qpat_assum `i*msz+msz <= SUC j*msz` mp_tac >>
     qpat_assum `mem_bytes_at d (32+SUC j*msz) back.vs_memory = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[] >> decide_tac) >>
  (* The new element uses the child postcondition. Older elements use
     the entry suffix, with their bytes also protected across the child. *)
  `?old old_taint.
     mem_bytes_at a msz back.vs_memory = mem_bytes_at a msz old /\
     (!k. k < msz /\ a+k IN tnb.t_mem ==> a+k IN old_taint) /\
     (!w. value_has_type tv w /\ val_wf tv w /\ val_in_memory tv w a old ==>
          !m. mem_agree_outside old_taint old m ==> val_in_memory tv w a m)` by
    (Cases_on `i = j` >-
       (qexistsl_tac [`t.vs_memory`,`tn'.t_mem`] >>
        conj_tac >- first_assum ACCEPT_TAC >>
        conj_tac >-
          (qpat_assum `tnb.t_mem SUBSET tn'.t_mem` mp_tac >>
           POP_ASSUM_LIST (K all_tac) >> simp[pred_setTheory.SUBSET_DEF]) >>
        qpat_assum `(\s tn. !v. value_has_type tv v /\ val_wf tv v /\ _ ==> _) t tn'`
          (mp_tac o BETA_RULE) >>
        `a = d+32+j*msz` by simp[Abbr `a`] >>
        qpat_assum `a = d+32+j*msz` (fn th => rewrite_tac[GSYM th])) >>
     `i < j` by (qpat_assum `i < SUC j` mp_tac >>
                qpat_assum `i <> j` mp_tac >> POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
     `i*msz+msz <= j*msz` by
       (qpat_assum `i < j` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
        rewrite_tac[GSYM (CONJUNCT2 MULT), LE_MULT_RCANCEL] >> decide_tac) >>
     `mem_bytes_at a msz t.vs_memory = mem_bytes_at a msz s.vs_memory` by
       (qpat_assum `Abbrev (a = _)` (fn th => rewrite_tac[REWRITE_RULE[markerTheory.Abbrev_def, GSYM ADD_ASSOC] th]) >>
        irule mem_bytes_at_translated_window >>
        qexists_tac `32+j*msz` >>
        qpat_assum `i*msz+msz <= j*msz` mp_tac >>
        qpat_assum `mem_bytes_at d (32+j*msz) t.vs_memory = _` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> simp[] >> decide_tac) >>
     qexistsl_tac [`s.vs_memory`,`tn.t_mem`] >>
     conj_tac >-
       (qpat_assum `mem_bytes_at a msz back.vs_memory = _` (fn th => rewrite_tac[th]) >>
        first_assum ACCEPT_TAC) >>
     conj_tac >-
       (`a+msz <= output_base+output_cap /\ output_base <= a` by
          (qpat_assum `i*msz+msz <= j*msz` mp_tac >>
           qpat_assum `j*msz+msz <= n*msz` mp_tac >>
           qpat_assum `output_base <= d` mp_tac >>
           qpat_assum `d+32+n*msz <= output_base+output_cap` mp_tac >>
           qpat_assum `Abbrev (a = _)` (fn th => rewrite_tac[REWRITE_RULE[markerTheory.Abbrev_def] th]) >>
           POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
        qx_gen_tac `k` >> strip_tac >>
        qpat_assum `(\tn tnf. !k. output_base <= k /\ _ ==> _) tn tnb`
          (qspec_then `a+k` irule o BETA_RULE) >>
        qpat_assum `a+k IN tnb.t_mem` (fn th => rewrite_tac[th]) >>
        qpat_assum `a+msz <= output_base+output_cap` mp_tac >>
        qpat_assum `output_base <= a` mp_tac >>
        qpat_assum `k < msz` mp_tac >> POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
     qpat_assum `!i. j0 <= i /\ i < j ==> !v. value_has_type tv v /\ _ ==> _`
       (qspec_then `i` mp_tac) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
     qpat_assum `Abbrev (a = _)` (fn th => rewrite_tac[GSYM (REWRITE_RULE[markerTheory.Abbrev_def] th)])) >>
  `val_in_memory tv v a old` by
    (irule val_in_memory_mem_agree >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`msz`,`back.vs_memory`] >> asm_rewrite_tac[LESS_EQ_REFL]) >>
  `val_footprint tv v <= msz` by
    (qpat_assum `msz = type_memory_size tv` (fn th => rewrite_tac[th]) >>
     irule exprSimPropsTheory.val_footprint_le >> first_assum ACCEPT_TAC) >>
  mp_tac
    (Q.SPECL [`tv`, `v`, `a`, `a`, `msz`, `old_taint`, `tnb.t_mem`,
       `old`, `back.vs_memory`] robust_val_in_memory_decreasing_taint_transport) >>
  (impl_tac >-
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     qpat_assum `!w. value_has_type tv w /\ val_wf tv w /\ val_in_memory tv w a old ==> _`
       (qspec_then `v` mp_tac) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then ACCEPT_TAC)) >>
  disch_then (qspec_then `mem` match_mp_tac) >> first_assum ACCEPT_TAC
QED

Resume abi_decode_loop_body_length_observed_conditional[success_length]:
  (* Both snapshots include the header, even for an empty completed suffix. *)
  `mem_word_at d back.vs_memory = mem_word_at d t.vs_memory` by
    (irule loop_snapshot_word >> qexists_tac `SUC j*msz` >> first_assum ACCEPT_TAC) >>
  `mem_word_at d t.vs_memory = mem_word_at d s.vs_memory` by
    (irule loop_snapshot_word >> qexists_tac `j*msz` >> first_assum ACCEPT_TAC) >>
  asm_rewrite_tac[]
QED

Finalise abi_decode_loop_body_length_observed_conditional

Theorem abi_decode_loop_body_observed_conditional:
  ^closed_body_observed_statement_typed
Proof
  map_every X_GEN_TAC (fst (strip_forall closed_body_observed_statement_typed)) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  (* The two closed statements share their named parameters; only w is new. *)
  mp_tac (SPECL
    (map (fn v => if aconv v ``w:256 word`` then
                    ``mem_word_at d (s:venom_state).vs_memory`` else v)
      (fst (strip_forall loop_body_length_statement)))
    abi_decode_loop_body_length_observed_conditional) >>
  (impl_tac >-
    (qpat_assum `(^completed_robust_typed) j0 k s tn` (assume_tac o BETA_RULE) >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     conj_tac >- (BETA_TAC >> conj_tac >- first_assum ACCEPT_TAC >> REFL_TAC) >>
     first_assum ACCEPT_TAC)) >>
  strip_tac
  >- (disj1_tac >> qexistsl_tac [`t`,`Gf`,`tnf`] >> asm_rewrite_tac[]) >>
  disj2_tac >> qexistsl_tac [`t`,`Gf`,`tnf`] >>
  qpat_assum `(\j0 k s tn. (^completed_robust_typed) j0 k s tn /\ _) _ _ _ _`
    (assume_tac o CONJUNCT1 o BETA_RULE) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  BETA_TAC >> first_assum ACCEPT_TAC
QED

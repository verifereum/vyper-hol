(* The abi_decode builtin's decoder on arbitrary memory input: it either
   decodes the bytes as evaluate_abi_decode does, or reverts exactly when
   evaluate_abi_decode rejects them. *)
Theory exprSimAbiDecodeBuiltin
Ancestors
  abiBuiltinDecodeCorrect abiBuiltinSource abiBuiltinDecodeEffect
  exprSimAbiDecodeTupleSource exprSimAbiDecodeMemberOutcome
  exprSimAbiDecodeCompositePrefix exprSimAbiDecodeMemberReject
  builtinAbi fragExec vyperABI venomState venomExecSemantics
  abiDecoderSiteEffect actualDecoderSites
  exprSimAbiDecodeBuiltinLayout exprSimAbiDecodeRecursiveClosure
  exprSimAbiDecodeBuiltinHeader abiBuiltinDecodeSetup abiBuiltinDecodeHeader
  abiBuiltinAllocation emitHelperProps exprLoweringProps valueEncoding
  abiDecoderFiniteControl words compileEnv valueEncodingProps arithmetic list finite_map
  exprSimAbiDecodeBuiltinSetup exprSimAbiDecodeBuiltinContext
  exprSimAbiDecodeOwnedContext exprSimAbiDecodeMemberExecute
  exprSimAbiDecodeSiteProvenance exprSimAbiDecodeSiteTransport
  abiDecoderWordTyped abiBuiltinSetupReach abiDecoderContract pred_set

(* Resources for the decode on arbitrary input, per allocation site: the
   source lies below the next allocation and away from the output and from
   the fragment's allocations (IDs st.cs_next_id .. last) that already
   exist (a decode re-run in a loop reuses its sites), and the
   registered function's allocation sites have room (decode_site_resources).
   The size guard is not assumed: on arbitrary input it is what the emitted
   size check tests. *)
Definition abi_builtin_decode_site_resources_def:
  abi_builtin_decode_site_resources ctx func st last min_size max_size outsz cnt p d s <=>
    max_size < dimword (:256) /\ p + 32 + cnt <= s.vs_alloca_next /\
    d + outsz < dimword (:256) /\ abi_footprint_disjoint (p + 32) cnt [(d,outsz)] /\
    (!id b sz. st.cs_next_id <= id /\ id < last /\
       FLOOKUP s.vs_allocas id = SOME (b,sz) ==>
       abi_footprint_disjoint (p + 32) cnt [(b,sz)]) /\
    decode_site_resources ctx func s /\ fn_inst_ids_distinct func /\
    ((FLOOKUP s.vs_allocas (abi_builtin_decode_output_site st min_size max_size) = NONE /\
        d = s.vs_alloca_next) \/
      FLOOKUP s.vs_allocas (abi_builtin_decode_output_site st min_size max_size) =
        SOME (d,outsz))
End

Theorem abi_decode_builtin_min_le_max[local]:
  abi_static_size sf ty <= abi_size_bound sf ty
Proof
  Cases_on `ty`
  >- (Cases_on `b` >> simp[abi_static_size_def, abi_size_bound_def] >>
      Cases_on `b'` >> simp[abi_static_size_def, abi_size_bound_def]) >>
  simp[abi_static_size_def, abi_size_bound_def, abi_embedded_static_size_def]
  >- (Induct_on `l` >> simp[] >> gen_tac >> decide_tac)
  >- (Cases_on `b` >> simp[abi_static_size_def, abi_size_bound_def,
         abi_embedded_static_size_def, LEFT_ADD_DISTRIB]) >>
  Cases_on `p` >> simp[abi_static_size_def, abi_size_bound_def] >>
  CASE_TAC >> simp[abi_embedded_static_size_def] >>
  pop_assum kall_tac >> Induct_on `x` >> simp[] >> gen_tac >> decide_tac
QED

Theorem abi_decode_builtin_setup_abort:
  abi_builtin_decode_setup data lo hi outsz st = (ops,ready) /\
  fn_has_code st ready fn /\
  eval_operand data s = SOME p /\ mload (w2n p) s = n2w cnt /\
  lo < dimword(:256) /\ hi < dimword(:256) /\ cnt < dimword(:256) /\
  ~(lo <= cnt /\ cnt <= hi) /\
  abi_decoder_operand_live st.cs_next_var data /\
  ready.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. Dabort ctx fn s Revert_abort t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule abi_builtin_decode_setup_trace >> strip_tac >>
  drule abi_builtin_decode_header_shape >> strip_tac >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >>
  drule abi_builtin_decode_setup_shape >> strip_tac >>
  `cs_extends st header_st /\ cs_extends header_st ready` by
    (conj_tac >> irule cs_extends_same_block >> simp[]) >>
  `fn_has_code st header_st fn` by metis_tac[fn_has_code_split] >>
  `header_st.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all abi_decode_builtin_header_abort >> simp[]
QED

Theorem abi_decode_owned_child_contract_apply_exact[local]:
  abi_decode_owned_child_contract ce env ty tv /\
  compile_abi_decode_to_buf dst src MLOAD base_op hi
    (type_to_abi_dec_info ce.ce_struct_fields ce ty) st = ((),last) /\
  abi_decode_code_context func fn st last /\
  last.cs_next_var <= limit_st.cs_next_var /\
  abi_decode_owned (abi_decode_sites st.cs_next_id last.cs_next_id) scratch
    d (type_memory_bytes ce ty) s /\
  abi_decode_context_pre ctx func ce env ty tv limit_st next
    (scratch UNION {a | d <= a /\ a < d + type_memory_bytes ce ty})
    (abi_decode_sites st.cs_next_id last.cs_next_id)
    st dst src base_op hi B bs pos d s ==>
  abi_decode_context_result ctx func fn tv limit_st next
    (scratch UNION {a | d <= a /\ a < d + type_memory_bytes ce ty})
    (abi_decode_sites st.cs_next_id last.cs_next_id) last
    (abi_decode_source_view (vyper_to_abi_type env ty) bs pos) env ty d s
Proof
  simp_tac bool_ss [abi_decode_owned_child_contract_def] >>
  metis_tac[SUBSET_REFL]
QED

Theorem lower_abi_decode_outcome:
  lower_abi_decode data (type_to_abi_dec_info ce.ce_struct_fields ce ty)
    (abi_static_size ce.ce_struct_fields ty) (abi_size_bound ce.ce_struct_fields ty)
    (type_memory_bytes ce ty) start = (out,final) /\
  abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
  assignable_type env ty /\ abi_decode_bytes_widths env ty /\
  abi_decoder_operand_live start.cs_next_var data /\
  final.cs_next_var <= limit_st.cs_next_var ==>
  !s0. eval_operand data s0 = SOME (n2w p) /\
    val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bs) p s0.vs_memory /\
    abi_builtin_decode_site_resources ctx func start final.cs_next_id
      (abi_static_size ce.ce_struct_fields ty) (abi_size_bound ce.ce_struct_fields ty)
      (type_memory_bytes ce ty) (LENGTH bs) p d s0 /\
    fresh_vars_wrt limit_st s0 ==>
  !fn. fn_has_code start final fn /\ fn_inst_ids_distinct fn /\
    (!i. MEM i (fn_insts fn) /\ i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==>
         MEM i (fn_insts func)) /\
    (start.cs_blocks = final.cs_blocks \/ final.cs_current_insts <> [] \/
     !bb. lookup_block final.cs_current_bb fn.fn_blocks = SOME bb ==>
          phi_prefix_length bb.bb_instructions = 0) /\
    ~s0.vs_halted /\ s0.vs_current_bb = start.cs_current_bb /\
    s0.vs_inst_idx = LENGTH start.cs_current_insts ==>
    (?t v. evaluate_abi_decode env ty bs = INL v /\
       eval_operand out t = SOME (n2w d) /\ val_in_memory tv v d t.vs_memory /\
       fresh_vars_wrt limit_st t /\
       decode_site_effect ctx func start.cs_next_var
         ({a | d <= a /\ a < d + type_memory_bytes ce ty} UNION
          {a | s0.vs_alloca_next <= a} UNION
          {a | ?id b sz. start.cs_next_id <= id /\ id < final.cs_next_id /\
                 FLOOKUP t.vs_allocas id = SOME (b,sz) /\ b <= a /\ a < b + sz})
         s0 t /\
       (!id. id < start.cs_next_id \/ final.cs_next_id <= id ==>
             FLOOKUP t.vs_allocas id = FLOOKUP s0.vs_allocas id) /\
       ~t.vs_halted /\ t.vs_current_bb = final.cs_current_bb /\
       t.vs_inst_idx = LENGTH final.cs_current_insts /\
       !fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
                ?fuel'. run_from fuel' ctx fn s0 = r) \/
    (?fuel r e u. run_from fuel ctx fn s0 = r /\ exit_result r /\
       r = Abort Revert_abort u /\ evaluate_abi_decode env ty bs = INR e)
Proof
  ntac 3 (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS)) >>
  drule lower_abi_decode_setup_trace >> strip_tac >>
  drule_all abi_builtin_decode_code >> strip_tac >>
  `ready.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  qpat_assum `abi_builtin_decode_site_resources _ _ _ _ _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o
     PURE_REWRITE_RULE [abi_builtin_decode_site_resources_def]) >>
  `s0.vs_alloca_next < dimword(:256)` by
    (fs[decode_site_resources_def, alloca_room_def] >> decide_tac) >>
  `p < dimword(:256) /\ LENGTH bs < dimword(:256) /\
   abi_static_size ce.ce_struct_fields ty < dimword(:256)` by
    (`abi_static_size ce.ce_struct_fields ty <= abi_size_bound ce.ce_struct_fields ty`
       by simp[abi_decode_builtin_min_le_max] >> decide_tac) >>
  `mload p s0 = n2w (LENGTH bs)` by
    fs[val_in_memory_def, mem_word_at_eq_mload] >>
  Cases_on `abi_static_size ce.ce_struct_fields ty <= LENGTH bs /\
            LENGTH bs <= abi_size_bound ce.ce_struct_fields ty`
  >- (pop_assum (map_every assume_tac o CONJUNCTS) >>
      `mload (w2n (n2w p:bytes32)) s0 = n2w (LENGTH bs)` by simp[w2n_n2w] >>
      `type_memory_bytes ce ty < dimword(:256)` by decide_tac >>
      drule_all abi_decode_builtin_setup_site_reach >> strip_tac >>
      rename1 `Dreach ctx fn s0 prepared` >>
      qmatch_asmsub_abbrev_tac `abi_decode_alloc_progress output_site s0 prepared` >>
      `!clamp. type_to_abi_dec_info ce.ce_struct_fields ce ty = DecPrimWord clamp ==>
         32 <= LENGTH bs` by
        (rpt strip_tac >> drule_all abi_decoder_primitive_cases >> strip_tac >>
         gvs[abi_static_size_def] >>
         Cases_on `bt` >> gvs[is_word_type_def, abi_static_size_def] >>
         Cases_on `b` >> gvs[is_word_type_def, abi_static_size_def]) >>
      `bs = mem_bytes_at (p+32) (LENGTH bs) s0.vs_memory` by
        fs[val_in_memory_def] >>
      `decode_site_resources ctx func prepared` by
        metis_tac[decode_site_effect_resources] >>
      `abi_decode_entry ready prepared` by simp[abi_decode_entry_def] >>
      `p+32+LENGTH bs < dimword(:256)` by decide_tac >>
      `!id b sz. id IN abi_decode_sites ready.cs_next_id final.cs_next_id /\
         FLOOKUP s0.vs_allocas id = SOME(b,sz) ==>
         abi_footprint_disjoint (p+32) (LENGTH bs) [(b,sz)]` by
        (simp_tac (srw_ss()) [abi_decode_sites_def] >> rpt strip_tac >>
         qpat_x_assum `!id b sz. start.cs_next_id <= id /\ _ ==> _` irule >>
         qexists `id` >> simp[] >> decide_tac) >>
      qabbrev_tac `scratch = {a | prepared.vs_alloca_next <= a} UNION
        {a | ?id b sz. id IN abi_decode_sites ready.cs_next_id final.cs_next_id /\
          FLOOKUP prepared.vs_allocas id = SOME(b,sz) /\ b <= a /\ a < b+sz}` >>
      `abi_decode_owned (abi_decode_sites ready.cs_next_id final.cs_next_id) scratch
         d (type_memory_bytes ce ty) prepared /\
       abi_decode_context_pre ctx func ce env ty tv limit_st start.cs_next_var
         (scratch UNION {a | d <= a /\ a < d+type_memory_bytes ce ty})
         (abi_decode_sites ready.cs_next_id final.cs_next_id) ready
         (FST ops) (Lit 0w) (FST (SND ops)) (SND (SND ops)) (p+32) bs 0 d prepared` by
        (irule abi_decode_builtin_context >> simp[Abbr `scratch`, word_add_n2w] >>
         qexistsl [`data`, `abi_size_bound ce.ce_struct_fields ty`,
           `abi_static_size ce.ce_struct_fields ty`] >>
         qexists `s0` >>
         rpt conj_tac >- first_assum ACCEPT_TAC >- decide_tac >>
         first_assum ACCEPT_TAC) >>
      `abi_decode_code_context func fn ready final` by
        (pure_rewrite_tac[abi_decode_code_context_def] >>
         metis_tac[]) >>
      `!v. abi_decode_source_accepts env ty
        (abi_decode_source_view (vyper_to_abi_type env ty) bs 0) v <=>
        evaluate_abi_decode env ty bs = INL v` by
        (gen_tac >> irule abi_decode_builtin_guard_view >> metis_tac[]) >>
      qpat_x_assum `abi_decode_context_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
        mp_tac >>
      simp_tac bool_ss [abi_decode_context_pre_def] >> strip_tac >>
      `abi_decode_context_pre ctx func ce env ty tv limit_st ready.cs_next_var
        (scratch UNION {a | d <= a /\ a < d+type_memory_bytes ce ty})
        (abi_decode_sites ready.cs_next_id final.cs_next_id) ready
        (FST ops) (Lit 0w) (FST (SND ops)) (SND (SND ops)) (p+32) bs 0 d prepared` by
        (pure_rewrite_tac[abi_decode_context_pre_def, LESS_EQ_REFL, AND_CLAUSES] >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
      drule_all abi_decode_owned_recursive_contract >> strip_tac >>
      drule_all abi_decode_owned_child_contract_apply_exact >>
      rewrite_tac[abi_decode_context_result_def] >>
      reverse strip_tac
      >- (disj2_tac >>
          `Dabort ctx fn s0 Revert_abort u` by metis_tac[Dreach_abort] >>
          Cases_on `evaluate_abi_decode env ty bs`
          >- metis_tac[] >>
          fs[Dabort_def] >> metis_tac[exit_result_def]) >>
      `eval_operand out t = SOME(n2w d)` by
        (qpat_x_assum `decode_site_effect _ _ ready.cs_next_var _ _ _` mp_tac >>
         pure_rewrite_tac[decode_site_effect_def] >> strip_tac >>
         `abi_decoder_operand_live ready.cs_next_var out` by
           metis_tac[abi_builtin_decode_setup_live] >> metis_tac[]) >>
      `Dreach ctx fn s0 t` by metis_tac[Dreach_trans] >>
      disj1_tac >> qexistsl [`t`, `v`] >>
      conj_tac >- metis_tac[] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      reverse conj_tac
      >- (conj_tac
          >- (qpat_x_assum `abi_decode_alloc_progress output_site _ _` mp_tac >>
              qpat_x_assum `abi_decode_alloc_progress (abi_decode_sites _ _) _ _` mp_tac >>
              simp_tac (srw_ss()) [abi_decode_alloc_progress_def,
                abi_decode_sites_def, Abbr `output_site`] >>
              rpt strip_tac >>
              `id <> abi_builtin_decode_output_site start
                (abi_static_size ce.ce_struct_fields ty)
                (abi_size_bound ce.ce_struct_fields ty)` by decide_tac >>
              `~(ready.cs_next_id <= id /\ id < final.cs_next_id)` by decide_tac >>
              metis_tac[]) >>
          conj_tac >- fs[abi_decode_entry_def] >>
          conj_tac >- fs[abi_decode_entry_def] >>
          conj_tac >- fs[abi_decode_entry_def] >>
          metis_tac[Dreach_fuel]) >>
      `decode_site_effect ctx func start.cs_next_var
        (scratch UNION {a | d <= a /\ a < d+type_memory_bytes ce ty}) s0 t` by
        (`decode_site_effect ctx func start.cs_next_var
          (scratch UNION {a | d <= a /\ a < d+type_memory_bytes ce ty}) prepared t` by
           metis_tac[decode_site_effect_threshold] >>
         drule_all decode_site_effect_trans >> simp_tac (srw_ss()) [EMPTY_UNION]) >>
      irule decode_site_effect_weaken >> goal_assum (drule_at Any) >>
      qpat_x_assum `abi_decode_alloc_progress (abi_decode_sites _ _) _ _` mp_tac >>
      qpat_x_assum `abi_decode_alloc_progress output_site _ _` mp_tac >>
      simp_tac (srw_ss()) [abi_decode_alloc_progress_def] >>
      rpt strip_tac >>
      simp_tac (srw_ss()) [SUBSET_DEF, Abbr `scratch`, abi_decode_sites_def] >>
      rpt strip_tac
      >- (disj1_tac >> disj2_tac >> decide_tac)
      >- (disj2_tac >> qexistsl [`id`, `b`, `sz`] >>
          conj_tac >- decide_tac >> conj_tac >- first_assum ACCEPT_TAC >>
          conj_tac >- metis_tac[] >> simp[])) >>
  disj2_tac >>
  `evaluate_abi_decode env ty bs = INR "abi_decode invalid"` by
    metis_tac[abi_decode_builtin_guard_reject] >>
  `mload (w2n (n2w p:bytes32)) s0 = n2w (LENGTH bs)` by simp[w2n_n2w] >>
  drule_all abi_decode_builtin_setup_abort >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  fs[Dabort_def] >> metis_tac[exit_result_def]
QED

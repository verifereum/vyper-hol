Theory bodyFullExtCallDirectWindows
Ancestors
  abiEncodeValuesPhases abiEncoderWindowPhase abiEncoderRegisteredEffect
  bodyFullIntCallReturnFrame exprSimAbiEncodeCallerFrame
  stateRelProj localPtrsProps allocaSiteResource
  emitHelperProps compileAllocaProvenance
  bodyPtrDefs loweringStateRelDefs loweringPosts exprLoweringProps
  ptrDiscipline valueEncodingDefs venomState venomMemDefs venomInst
  finite_map pred_set list alist words arithmetic pair

(* Each explicit write lies in the request allocation. Every extra write
   lies in an identified cursor or scratch allocation. *)
Theorem extcall_direct_encode_windows:
  window_phase ctx func st en ids outs s t /\
  stmt_state_rel (H:(bool # bytes32 # type_value) list # num list) ctx func ce cx ee s /\
  fn_inst_ids_distinct func /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  FLOOKUP s.vs_allocas shared = SOME (p,cap) /\ cut <= shared /\
  (!aid. aid IN ids ==> cut <= aid) /\
  EVERY (\(b,n). p <= b /\ b+n <= p+cap) outs /\
  (!aid. aid IN shared INSERT ids ==>
    ?inst x. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id = aid /\ inst.inst_outputs = [x] /\ not_local_ptr ce ee.scopes x) /\
  (!i. EVERY (\(b,n). i < b \/ b+n <= i) outs /\
    (!aid b n. aid IN ids /\ FLOOKUP t.vs_allocas aid = SOME (b,n) ==>
      i < b \/ b+n <= i) /\ i IN tn'.t_mem ==> i IN tn.t_mem) ==>
  (!b n. ((b = 0 /\ n = lo) \/
          (?name. local_region ce ee.scopes s name b n) \/
          (?aid. FLOOKUP s.vs_allocas aid = SOME (b,n) /\ aid < cut)) ==>
     mem_bytes_at b n t.vs_memory = mem_bytes_at b n s.vs_memory /\
     (!i. b <= i /\ i < b+n /\ i IN tn'.t_mem ==> i IN tn.t_mem)) /\
  (ce.ce_is_ctor ==> !src name tv v off.
    (src = ce.ce_module \/ IS_SOME (ALOOKUP ce.ce_modules src)) /\
    FLOOKUP ce.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables src imms) name = SOME (tv,v) ==>
    mem_bytes_at off (type_memory_size tv) t.vs_memory =
    mem_bytes_at off (type_memory_size tv) s.vs_memory)
Proof
  strip_tac >>
  drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  `!q k. q+k <= s.vs_alloca_next /\
     (!aid b n. aid IN shared INSERT ids /\ FLOOKUP s.vs_allocas aid = SOME (b,n) ==>
        venomMemDefs$regions_disjoint (q,k) (b,n)) ==>
     mem_bytes_at q k t.vs_memory = mem_bytes_at q k s.vs_memory /\
     (!i. q <= i /\ i < q+k /\ i IN tn'.t_mem ==> i IN tn.t_mem)` by
    (rpt gen_tac >> strip_tac >>
     mp_tac (Q.INST [`q` |-> `q`, `n` |-> `k`] abi_encode_values_protected_window) >>
     impl_tac
     >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
         simp[EVERY_MEM, FORALL_PROD] >> rpt strip_tac
         >- (qpat_assum `EVERY _ outs` (mp_tac o REWRITE_RULE [EVERY_MEM, FORALL_PROD]) >>
             disch_then (drule_then strip_assume_tac) >>
             `venomMemDefs$regions_disjoint (q,k) (p,cap)` by metis_tac[IN_INSERT] >>
             fs[venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
         metis_tac[IN_INSERT]) >>
     disch_then ACCEPT_TAC) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac
      >- (first_assum irule >> simp[venomMemDefsTheory.regions_disjoint_def] >>
          metis_tac[allocas_from_def])
      >- (`b+n <= s.vs_alloca_next` by
            (qpat_assum `local_region ce ee.scopes s name b n` mp_tac >>
             simp[NoAsms, local_region_def] >>
             disch_then (qx_choosel_then [`entry`,`lp`,`lw`] strip_assume_tac) >>
             qpat_assum `local_ptrs_rel _ _ _ _`
               (drule_all_then strip_assume_tac o cj 1 o REWRITE_RULE [local_ptrs_rel_def]) >>
             gvs[lookup_var_def] >> first_assum ACCEPT_TAC) >>
          qpat_assum `!q k. _ ==> mem_bytes_at q k t.vs_memory = _ /\ _`
            (qspecl_then [`b`,`n`] mp_tac) >>
          impl_tac
          >- (asm_rewrite_tac[] >> qx_genl_tac [`row_id`,`row_base`,`row_size`] >> strip_tac >>
              qpat_assum `!aid. aid IN shared INSERT ids ==> _` (drule_then strip_assume_tac) >>
              `loweringStateRelDefs$regions_disjoint row_base row_size b n` by
                metis_tac[local_ptrs_rel_alloca_disjoint] >>
              fs[loweringStateRelDefsTheory.regions_disjoint_def,
                 venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
          disch_then ACCEPT_TAC) >>
      `b+n <= s.vs_alloca_next` by metis_tac[alloca_site_registered_below] >>
      qpat_assum `!q k. _ ==> mem_bytes_at q k t.vs_memory = _ /\ _`
        (qspecl_then [`b`,`n`] mp_tac) >>
      impl_tac
      >- (asm_rewrite_tac[] >> qx_genl_tac [`row_id`,`row_base`,`row_size`] >> strip_tac >>
          `row_id <> aid` by (fs[IN_INSERT] >> res_tac >> decide_tac) >>
          metis_tac[alloca_site_registered_disjoint]) >>
      disch_then ACCEPT_TAC) >>
  disch_tac >> rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  `immutable_alloca_sep func (ce with ce_module := src) cx ee s` by
    (fs[stmt_state_rel_def, optionTheory.IS_SOME_EXISTS] >>
     Cases_on `src = ce.ce_module` >>
     gvs[compileEnvTheory.compile_env_component_equality] >> metis_tac[]) >>
  qpat_x_assum `immutable_alloca_sep _ _ _ _ _`
    (mp_tac o CONJUNCT2 o REWRITE_RULE [immutable_alloca_sep_def]) >>
  simp[] >> disch_then (drule_then assume_tac) >>
  qpat_assum `!tv v. _ ==> off + type_memory_size tv <= _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!q k. _ ==> mem_bytes_at q k t.vs_memory = _ /\ _`
    (qspecl_then [`off`,`type_memory_size tv`] mp_tac) >>
  impl_tac
  >- (asm_rewrite_tac[] >> rpt gen_tac >> strip_tac >>
      qpat_assum `!aid. aid IN shared INSERT ids ==> _` (drule_then strip_assume_tac) >>
      `loweringStateRelDefs$regions_disjoint off (type_memory_size tv) b n` by
        metis_tac[] >>
      fs[loweringStateRelDefsTheory.regions_disjoint_def, venomMemDefsTheory.regions_disjoint_def]) >>
  simp[]
QED

Theorem extcall_direct_alloca_site:
  emit_op ALLOCA [Lit n] st = (out,en) /\ fn_has_code st en func /\
  local_ptrs_reserved ce cut /\ cut.cs_next_var <= st.cs_next_var ==>
  ?inst q. out = Var q /\ MEM inst (fn_insts func) /\
    inst.inst_opcode = ALLOCA /\ inst.inst_id = st.cs_next_id /\
    inst.inst_operands = [Lit n] /\ inst.inst_outputs = [q] /\
    not_local_ptr ce scopes q
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  qabbrev_tac `q = STRING #"%" (toString st.cs_next_var)` >>
  qabbrev_tac `inst = mk_inst st.cs_next_id ALLOCA [Lit n] [q]` >>
  qexistsl_tac [`inst`,`q`] >>
  `not_local_ptr ce scopes q` by
    (simp[Abbr `q`] >> irule local_ptrs_reserved_fresh >>
     qexists_tac `cut` >> asm_rewrite_tac[]) >>
  `MEM inst (fn_insts func)` by
    (mp_tac (Q.SPECL [`st`,`en`,`func`,`inst`] fn_has_code_current_member) >>
     qpat_assum `en.cs_current_insts = _` (fn th => simp[th, Abbr `inst`, Abbr `q`])) >>
  simp[Abbr `inst`, Abbr `q`, mk_inst_def]
QED

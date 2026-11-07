(* Explicit-resource allocation for the external ABI output prefix. *)
Theory externalReturnAllocPtr
Ancestors externalReturnTupleWindowPtr allocaSiteResource normalizationAllocExecPtr

Theorem alloca_step_resource_observations:
  alloca_inv s /\ alloca_room ctx func s /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
  n < dimword(:256) /\
  (!b sz. FLOOKUP s.vs_allocas id = SOME (b,sz) ==> sz = n) ==>
  ?t b. step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK t /\
    alloca_inv t /\ alloca_room ctx func t /\
    lookup_var out t = SOME (n2w b) /\ FLOOKUP t.vs_allocas id = SOME (b,n) /\
    b+n <= t.vs_alloca_next /\ s.vs_alloca_next <= t.vs_alloca_next /\
    b+n < dimword(:256) /\
    (!aid p sz. FLOOKUP s.vs_allocas aid = SOME (p,sz) ==>
      FLOOKUP t.vs_allocas aid = SOME (p,sz))
Proof
  strip_tac >>
  drule_at (Pat `MEM _ _`) alloca_site_execute >>
  disch_then (qspecl_then [`s`, `out`, `n2w n`, `ctx`] mp_tac) >>
  simp[venomInstTheory.mk_inst_def, wordsTheory.w2n_n2w] >> strip_tac >>
  `t.vs_alloca_next < dimword(:256)` by
    (irule exprLoweringPropsTheory.alloca_room_next_lt >> metis_tac[]) >>
  qexistsl_tac [`t`, `b`] >> asm_rewrite_tac[] >>
  conj_tac >-
    (pure_rewrite_tac[Once venomExecSemanticsTheory.step_inst_base_def,
       venomInstTheory.mk_inst_def] >>
     simp_tac (srw_ss()) [venomStateTheory.eval_operand_def] >>
     asm_rewrite_tac[venomInstTheory.mk_inst_def]) >> decide_tac
QED

Theorem compile_alloc_buffer_protected_source_frag_ptr:
  compile_alloc_buffer n sa = (buf,sb) /\ fn_has_code sa sb func /\
  alloca_inv s /\ alloca_room ctx func s /\ n < dimword(:256) /\
  not_fresh_at sa src /\ eval_operand (Var src) s = SOME (n2w p) /\
  p+cap <= s.vs_alloca_next /\ val_wf tv v /\ val_footprint tv v <= cap /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory tv v p mem) /\
  (!b sz. FLOOKUP s.vs_allocas sa.cs_next_id = SOME (b,sz) ==>
    sz = n /\ (p+cap <= b \/ b+n <= p)) ==>
  ?out b G1 tn1 sf.
    buf.buf_operand = Var out /\
    frag_exec_ptr cx ctx PG sa sb
      (\g t w. g = G /\ t = tn /\ w = s)
      (\g t w. g = G1 /\ t = tn1 /\ w = sf) R /\
    eval_operand (Var out) sf = SOME (n2w b) /\ ptr_covers G1 tn1 out sf n /\
    (p+cap <= b \/ b+n <= p) /\ eval_operand (Var src) sf = SOME (n2w p) /\
    (!mem. mem_agree_outside tn1.t_mem sf.vs_memory mem ==> val_in_memory tv v p mem) /\
    (!q k. not_fresh_at sa q /\ ptr_covers G tn q s k ==> ptr_covers G1 tn1 q sf k) /\
    (stor_taint_ok cx tn s ==> stor_taint_ok cx tn1 sf) /\
    alloca_inv sf /\ alloca_room ctx func sf /\
    FLOOKUP sf.vs_allocas sa.cs_next_id = SOME (b,n) /\
    b+n <= sf.vs_alloca_next /\ s.vs_alloca_next <= sf.vs_alloca_next /\
    b+n < dimword(:256) /\
    (!aid q sz. FLOOKUP s.vs_allocas aid = SOME (q,sz) ==>
      FLOOKUP sf.vs_allocas aid = SOME (q,sz))
Proof
  strip_tac >>
  drule loweringHaltTheory.compile_alloc_buffer_emission >> strip_tac >>
  rename1 `buf.buf_operand = Var out` >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out]) (fn_insts func)` by
    (drule_all fragExecTheory.fn_has_code_split >> strip_tac >>
     drule_all loweringHaltTheory.emit_inst_fn_member >> simp[]) >>
  `!b sz. FLOOKUP s.vs_allocas sa.cs_next_id = SOME (b,sz) ==> sz = n` by metis_tac[] >>
  drule_all alloca_step_resource_observations >> strip_tac >>
  `(p+cap <= b \/ b+n <= p) = T` by suspend "separation" >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out]` >>
  qabbrev_tac `G1 = step_prov PG G inst t` >>
  qabbrev_tac `tn1 = step_taint inst s t tn` >>
  qabbrev_tac `sf = t with vs_inst_idx := SUC s.vs_inst_idx` >>
  `frag_exec_ptr cx ctx PG sa sb
    (\g u w. g = G /\ u = tn /\ w = s)
    (\g u w. g = G1 /\ u = tn1 /\ w = sf) R` by
    (simp[Abbr `G1`, Abbr `tn1`, Abbr `sf`, Abbr `inst`] >>
     irule compile_alloc_buffer_step_frag_ptr >> simp[]) >>
  `!q. not_fresh_at sa q ==> q <> out` by metis_tac[] >>
  `!q. not_fresh_at sa q ==> lookup_var q sf = lookup_var q s` by
    (rpt strip_tac >> qunabbrev_tac `inst` >>
     drule alloca_step_old_register_frame >>
     disch_then (qspecl_then [`tn`, `PG`, `G`] strip_assume_tac) >>
     `q <> out` by (first_x_assum irule >> simp[]) >>
     qpat_x_assum `!q. q <> out ==> _` (qspec_then `q` mp_tac) >>
     simp[Abbr `sf`, venomStateTheory.lookup_var_def]) >>
  `ptr_covers G1 tn1 out t n /\
   (!q k. q <> out /\ ptr_covers G tn q s k ==> ptr_covers G1 tn1 q t k)`
    by suspend "cover_resources" >>
  qexistsl_tac [`out`, `b`, `G1`, `tn1`, `sf`] >>
  asm_rewrite_tac[] >>
  conj_tac >-
    (qpat_x_assum `lookup_var out t = _` mp_tac >>
     simp[Abbr `sf`, venomStateTheory.eval_operand_def,
       venomStateTheory.lookup_var_def]) >>
  conj_tac >- suspend "covers" >>
  conj_tac >-
    (qpat_x_assum `eval_operand (Var src) s = _` mp_tac >>
     simp[venomStateTheory.eval_operand_def]) >>
  conj_tac >- suspend "robust" >>
  conj_tac >- suspend "old_covers" >>
  conj_tac >- suspend "stor" >>
  simp[Abbr `sf`] >> conj_tac >-
    (irule localPtrsPropsTheory.alloca_inv_fields >> qexists_tac `t` >> simp[]) >>
  irule exprLoweringPropsTheory.alloca_room_fields >> qexists_tac `t` >> simp[]
QED

Resume compile_alloc_buffer_protected_source_frag_ptr[separation]:
  Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id`
  >- (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
      pure_rewrite_tac[Once venomExecSemanticsTheory.step_inst_base_def,
        venomInstTheory.mk_inst_def] >>
      simp_tac (srw_ss()) [venomStateTheory.eval_operand_def,
        venomExecSemanticsTheory.exec_alloca_def] >> strip_tac >>
      gvs[venomStateTheory.update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >> decide_tac) >>
  rename1 `FLOOKUP s.vs_allocas sa.cs_next_id = SOME site` >> PairCases_on `site` >>
  qpat_x_assum `!aid q sz. _` (qspecl_then [`sa.cs_next_id`, `site0`, `site1`] mp_tac) >>
  asm_rewrite_tac[] >>
  simp[] >> strip_tac >>
  qpat_x_assum `!b sz. _ ==> _ /\ _` (qspecl_then [`site0`, `site1`] mp_tac) >>
  simp[]
QED

Resume compile_alloc_buffer_protected_source_frag_ptr[robust]:
  qunabbrev_tac `inst` >>
  drule_all normalizationTupleBytesPtrTheory.alloca_step_exterior_effects >>
  disch_then (qspec_then `tn` strip_assume_tac) >>
  simp[Abbr `sf`] >> rpt strip_tac >>
  irule robustCopyTransportPtrTheory.robust_val_in_memory_exterior_frame >>
  conj_tac >- simp[] >>
  qexistsl_tac [`s.vs_memory`, `t.vs_memory`, `tn.t_mem`,
    `tn1.t_mem`, `{j | b <= j /\ j < b+n}`] >>
  simp[Abbr `tn1`] >> rpt strip_tac >>
  qpat_x_assum `(_ \/ _) = T` mp_tac >>
  pure_rewrite_tac[boolTheory.EQ_CLAUSES] >> decide_tac
QED

Resume compile_alloc_buffer_protected_source_frag_ptr[cover_resources]:
  qunabbrev_tac `inst` >>
  simp[Abbr `G1`, Abbr `tn1`] >>
  Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id`
  >- (`sa.cs_next_id NOTIN FDOM s.vs_allocas` by
        (qpat_x_assum `FLOOKUP s.vs_allocas _ = NONE` mp_tac >>
         simp[finite_mapTheory.FLOOKUP_DEF]) >>
      drule_at (Pat `MEM _ _`) exprLoweringPropsTheory.alloca_room_fresh >>
      disch_then (qspecl_then [`s`, `n2w n`, `ctx`] mp_tac) >>
      simp[venomInstTheory.mk_inst_def, wordsTheory.w2n_n2w] >> strip_tac >>
      `s.vs_alloca_next + n < dimword(:256)` by decide_tac >>
      pure_rewrite_tac[GSYM venomInstTheory.mk_inst_def] >>
      drule_all allocationPtrTheory.fresh_alloca_ptr_covers >>
      disch_then (qspecl_then [`PG`, `G`, `tn`] mp_tac) >> simp[]) >>
  rename1 `FLOOKUP s.vs_allocas sa.cs_next_id = SOME site` >> PairCases_on `site` >>
  qpat_x_assum `!b sz. _ ==> sz = n`
    (qspecl_then [`site0`, `site1`] mp_tac) >>
  simp_tac (srw_ss()) [] >> disch_then SUBST_ALL_TAC >>
  drule_all allocationPtrTheory.reused_alloca_step >>
  disch_then (qspec_then `out` assume_tac) >>
  qpat_x_assum `!aid q sz. _` (qspecl_then [`sa.cs_next_id`, `site0`, `n`] mp_tac) >>
  asm_rewrite_tac[] >> simp_tac (srw_ss()) [] >> disch_then SUBST_ALL_TAC >>
  qpat_x_assum `step_inst_base _ s = OK (update_var _ _ _)` mp_tac >>
  asm_rewrite_tac[] >> simp_tac (srw_ss()) [] >> disch_then SUBST_ALL_TAC >>
  drule_all allocationPtrTheory.reused_alloca_ptr_covers >>
  disch_then (qspecl_then [`out`, `PG`, `G`, `tn`] mp_tac) >> simp[]
QED

Resume compile_alloc_buffer_protected_source_frag_ptr[covers]:
  qpat_x_assum `ptr_covers G1 tn1 out t n` mp_tac >>
  simp_tac (srw_ss()) [Abbr `sf`, bodyPtrDefsTheory.ptr_covers_def,
    venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def]
QED

Resume compile_alloc_buffer_protected_source_frag_ptr[old_covers]:
  rpt strip_tac >>
  `q <> out` by (first_x_assum irule >> simp[]) >>
  qpat_x_assum `!q k. q <> out /\ _ ==> _` (qspecl_then [`q`, `k`] mp_tac) >>
  (impl_tac >- simp[]) >>
  simp_tac (srw_ss()) [Abbr `sf`, bodyPtrDefsTheory.ptr_covers_def,
    venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def]
QED

Resume compile_alloc_buffer_protected_source_frag_ptr[stor]:
  simp[Abbr `sf`, bodyPtrDefsTheory.stor_taint_ok_def, Abbr `tn1`, Abbr `inst`,
    ptrDisciplineTheory.step_taint_def, venomInstTheory.mk_inst_def,
    ptrDisciplineTheory.set_var_taint_def] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[Once venomExecSemanticsTheory.step_inst_base_def,
    venomInstTheory.mk_inst_def, venomStateTheory.eval_operand_def,
    venomExecSemanticsTheory.exec_alloca_def,
    ptrDisciplineTheory.adopt_reset_def, ptrDisciplineTheory.store_taint_def,
    ptrDisciplineTheory.imm_taint_def] >>
  Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id` >> simp[] >>
  rpt strip_tac >> gvs[AllCaseEqs(), venomStateTheory.update_var_def]
QED

Finalise compile_alloc_buffer_protected_source_frag_ptr

(* The actual complex-return prefix, stopping before the encoder executes. *)
Theorem compile_external_return_tuple_bytes_alloc_prefix_ptr:
  compile_external_return (SOME (Var src)) F F next.ce_ret_enc_info n nr key ut iv sa = (x,sc) /\
  (nr ==> iv) /\ fn_has_code sa sc func /\
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut,nr0,rr,name,args,defaults,TupleT ts,(fbody:stmt list))) =
      (lbl,cenv0,pos,cds,payable,nr',key0,ut0,view,body',rt) /\
  compile_register_positional_args cenv0 pos off st = (cenv,sa0) /\
  same_frame cenv next /\
  ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
  assignable_type (type_env tops) (TupleT ts) /\ ts <> [] /\
  EVERY (\t. (?k. t = BaseT (BytesT (Dynamic k))) \/
             (?k. t = BaseT (StringT k))) ts /\
  evaluate_type (type_env tops) (TupleT ts) = SOME (TupleTV tvs) /\
  value_has_type (TupleTV tvs) (ArrayV (TupleV vs)) /\
  vyper_to_abi_list (type_env tops) ts vs = SOME avs /\
  alloca_inv s /\ alloca_room ctx func s /\ n < dimword(:256) /\
  not_fresh_at sa src /\ eval_operand (Var src) s = SOME (n2w p) /\
  p+cap <= s.vs_alloca_next /\ val_wf (TupleTV tvs) (ArrayV (TupleV vs)) /\
  val_footprint (TupleTV tvs) (ArrayV (TupleV vs)) <= cap /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) p mem) /\
  (!b sz. FLOOKUP s.vs_allocas sa.cs_next_id = SOME (b,sz) ==>
    sz = n /\ (p+cap <= b \/ b+n <= p)) ==>
  ?buf sb len sd out b G1 tn1 sf.
    compile_alloc_buffer n sa = (buf,sb) /\
    compile_abi_encode_to_buf buf.buf_operand (Var src) next.ce_ret_enc_info sb = (len,sd) /\
    emit_inst RETURN [buf.buf_operand;len] [] sd = (x,sc) /\
    buf.buf_operand = Var out /\
    frag_exec_ptr cx ctx PG sa sb
      (\g t w. g = G /\ t = tn /\ w = s)
      (\g t w. g = G1 /\ t = tn1 /\ w = sf) R /\
    eval_operand (Var out) sf = SOME (n2w b) /\ ptr_covers G1 tn1 out sf n /\
    (p+cap <= b \/ b+n <= p) /\ eval_operand (Var src) sf = SOME (n2w p) /\
    (!mem. mem_agree_outside tn1.t_mem sf.vs_memory mem ==>
      abi_encoder_window_input next.ce_ret_enc_info
        (if needs_external_call_wrap (TupleT ts)
         then Tuple [vyper_to_abi_type (type_env tops) (TupleT ts)]
         else vyper_to_abi_type (type_env tops) (TupleT ts))
        (if needs_external_call_wrap (TupleT ts) then ListV [ListV avs] else ListV avs)
        p (SUM (MAP type_memory_size tvs)) mem) /\
    (!q k. not_fresh_at sa q /\ ptr_covers G tn q s k ==> ptr_covers G1 tn1 q sf k) /\
    (stor_taint_ok cx tn s ==> stor_taint_ok cx tn1 sf) /\
    alloca_inv sf /\ alloca_room ctx func sf /\
    FLOOKUP sf.vs_allocas sa.cs_next_id = SOME (b,n) /\
    b+n <= sf.vs_alloca_next /\ s.vs_alloca_next <= sf.vs_alloca_next /\
    b+n < dimword(:256) /\
    (!aid q sz. FLOOKUP s.vs_allocas aid = SOME (q,sz) ==>
      FLOOKUP sf.vs_allocas aid = SOME (q,sz))
Proof
  strip_tac >> drule_all loweringHaltTheory.compile_external_return_abi_parts >> strip_tac >>
  qmatch_asmsub_rename_tac `compile_alloc_buffer n sa = (buf,alloc_st)` >>
  qmatch_asmsub_rename_tac `compile_abi_encode_to_buf _ _ _ alloc_st = (len,enc_st)` >>
  `cs_extends sa alloc_st` by (drule loweringHaltTheory.compile_alloc_buffer_extends >> simp[]) >>
  `cs_extends alloc_st sc` by
    (drule loweringHaltTheory.compile_abi_encode_to_buf_extends >> strip_tac >>
     drule fragExecTheory.cs_extends_emit_inst >> strip_tac >>
     metis_tac[compileEnvTheory.cs_extends_trans]) >>
  `fn_has_code sa alloc_st func` by (drule_all fragExecTheory.fn_has_code_split >> simp[]) >>
  drule_all compile_alloc_buffer_protected_source_frag_ptr >>
  disch_then (qspecl_then [`cx`, `R`, `PG`, `G`] strip_assume_tac) >>
  qexistsl_tac [`buf`, `alloc_st`, `len`, `enc_st`, `out`, `b`, `G1`, `tn1`, `sf`] >>
  asm_rewrite_tac[] >>
  rpt strip_tac >> drule_all external_frame_tuple_bytes_robust_window >> simp[]
QED

(* At the passing selected-entry check, decode the supplied keyword prefix. *)
Theory groupedDefaultSuppliedCut
Ancestors
  groupedDefaultArguments groupedDefaultSyntax groupedEntryAllocation
  groupedKeywordInitialize groupedKeywordDecode calldataSourceCorrespondence
  vyperABIEntries abiDecoderCoherence list rich_list arithmetic pair

Theorem grouped_default_supplied_cut:
  LENGTH ds <= LENGTH args /\
  MEM (prefix,k) (abi_entries args ds) /\
  OPT_MMAP (evaluate_type env) (MAP SND args) = SOME tvs /\
  OPT_MMAP (evaluate_type env) (MAP SND prefix) = SOME provided /\
  calldata_decode_args s.vs_call_ctx.cc_calldata provided 0 = SOME vals /\
  LIST_REL (\arg tv. abi_decoder_coherent ce env ce.ce_struct_fields (SND arg) tv)
    args tvs /\
  4 + SUM (MAP tv_abi_size tvs) < dimword (:256) /\
  specs = MAP (\((n,ty),e). (n,ty,e)) (ZIP (DROP (LENGTH args - LENGTH ds) args,ds)) /\
  compile_create_kwarg_allocas ce specs a = (vars,b) /\
  compile_init_kwargs ce vars (4 + SUM (MAP tv_abi_size (TAKE (LENGTH args - LENGTH ds) tvs))) k hi si = ((),sb) /\
  compile_init_kwargs ce (MAP (\(n,p,ty,e). (n,p,ty,gas_shadow_expr e)) vars)
    (4 + SUM (MAP tv_abi_size (TAKE (LENGTH args - LENGTH ds) tvs))) k hi sha = ((),shb) /\
  fn_has_code si sb fn /\ fn_has_code sha shb shfn /\ gas_shadow_state si sha /\
  (!name op ty e. MEM (name,op,ty,e) vars ==>
    ?id q base. op = Var q /\ not_fresh_at si q /\ lookup_var q s = SOME (n2w base) /\
      MEM (mk_inst id ALLOCA [Lit (n2w (type_memory_bytes ce ty))] [q]) (fn_insts fn) /\
      FLOOKUP s.vs_allocas id = SOME (base,type_memory_bytes ce ty) /\
      base + type_memory_bytes ce ty < dimword (:256) /\ id < si.cs_next_id /\
      ptr_covers G tn q s (type_memory_bytes ce ty)) /\
  selected_registration_resources ctx fn site lo si s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size fn s <= w2n s.vs_initial_fmp) /\
  unit_alloca_budget ctx < dimword (:256) /\ fn_inst_ids_distinct fn /\
  (!label bb. lookup_block label fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) ==>
  ?slots last shlast t J tz.
    ALL_DISTINCT (MAP FST slots) /\
    MAP (\(_,_,_,tv). tv) slots = DROP (LENGTH args - LENGTH ds) tvs /\
    LIST_REL (\(name,op,ty,e) (id,q,base,tv).
      op = Var q /\ type_memory_bytes ce ty = type_memory_size tv /\
      not_fresh_at si q /\ lookup_var q s = SOME (n2w base) /\
      MEM (mk_inst id ALLOCA [Lit (n2w (type_memory_size tv))] [q]) (fn_insts fn) /\
      FLOOKUP s.vs_allocas id = SOME (base,type_memory_size tv) /\
      base + type_memory_size tv < dimword (:256) /\ id < si.cs_next_id /\
      ptr_covers G tn q s (type_memory_size tv)) vars slots /\
    MAP (\(name,_,ty,_). (name,ty)) vars = DROP (LENGTH args - LENGTH ds) args /\
    MAP (\(_,_,_,e). e) vars = ds /\
    LENGTH vals = LENGTH args - LENGTH ds + k /\
    calldata_decode_args s.vs_call_ctx.cc_calldata (TAKE (LENGTH args - LENGTH ds) tvs) 0 =
      SOME (TAKE (LENGTH args - LENGTH ds) vals) /\
    compile_init_kwargs ce (DROP k vars)
      (4 + SUM (MAP tv_abi_size (TAKE (LENGTH args - LENGTH ds) tvs)) +
        SUM (MAP tv_abi_size (TAKE k (DROP (LENGTH args - LENGTH ds) tvs)))) 0 hi last = ((),sb) /\
    compile_init_kwargs ce (MAP (\(n,p,ty,e). (n,p,ty,gas_shadow_expr e)) (DROP k vars))
      (4 + SUM (MAP tv_abi_size (TAKE (LENGTH args - LENGTH ds) tvs)) +
        SUM (MAP tv_abi_size (TAKE k (DROP (LENGTH args - LENGTH ds) tvs)))) 0 hi shlast = ((),shb) /\
    fn_has_code last sb fn /\ fn_has_code shlast shb shfn /\ gas_shadow_state last shlast /\
    selected_registration_resources ctx fn site lo last t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t /\
      t.vs_alloca_next + pending_alloca_size fn t <= w2n t.vs_initial_fmp) /\
    EVERY (\(id,q,base,tv).
      id < last.cs_next_id /\ not_fresh_at last q /\ base < dimword (:256) /\
      FLOOKUP t.vs_allocas id = SOME (base,type_memory_size tv) /\
      lookup_var q t = SOME (n2w base) /\ ptr_covers J tz q t (type_memory_size tv)) (DROP k slots) /\
    LIST_REL (\(id,q,base,tv) v.
      id < last.cs_next_id /\ not_fresh_at last q /\ base < dimword (:256) /\
      FLOOKUP t.vs_allocas id = SOME (base,type_memory_size tv) /\
      lookup_var q t = SOME (n2w base) /\ ptr_covers J tz q t (type_memory_size tv) /\
      value_has_type tv v /\
      (!mem. mem_agree_outside tz.t_mem t.vs_memory mem ==> val_in_memory tv v base mem))
      (TAKE k slots) (DROP (LENGTH args - LENGTH ds) vals) /\
    selected_registration_frame s tn t tz /\ tz.t_mem SUBSET tn.t_mem /\
    (!D exp. gas_origin_ptr_path (D,lo,exp,ctx,fn,PG) (s,G,tn) [] (OK t,J,tz))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all grouped_default_decode_split >> strip_tac >>
  qabbrev_tac `pos = LENGTH args - LENGTH ds` >>
  `LENGTH (DROP pos args) = LENGTH ds` by (simp[Abbr `pos`, LENGTH_DROP] >> decide_tac) >>
  `k <= LENGTH ds` by fs[abi_entries_member] >>
  drule compile_create_kwarg_allocas_preserves_specs >> disch_tac >>
  `MAP (\(name,_,ty,_). (name,ty)) vars = DROP pos args /\
   MAP (\(_,_,_,e). e) vars = ds` by
    (irule grouped_keyword_initializer_specs >> asm_rewrite_tac[]) >>
  drule grouped_keyword_allocations_distinct >> strip_tac >>
  `LIST_REL (\arg tv. abi_decoder_coherent ce env ce.ce_struct_fields (SND arg) tv)
     (DROP pos args) (DROP pos tvs)` by metis_tac[LIST_REL_DROP] >>
  `LIST_REL (\(_,_,ty,_) tv. abi_decoder_coherent ce env ce.ce_struct_fields ty tv)
     vars (DROP pos tvs)` by
    (qpat_assum `LIST_REL _ (DROP pos args) (DROP pos tvs)` mp_tac >>
     qpat_assum `MAP _ vars = DROP pos args` (fn th => rewrite_tac[GSYM th]) >>
     simp[LIST_REL_MAP1, combinTheory.o_DEF, pairTheory.LAMBDA_PROD]) >>
  `LIST_REL (\(_,_,ty,_) tv. type_memory_bytes ce ty = type_memory_size tv)
     vars (DROP pos tvs)` by
    (irule LIST_REL_mono >> goal_assum (drule_at Any) >>
     simp[FORALL_PROD] >> metis_tac[abi_decoder_coherent_header, abi_decoder_header_def]) >>
  drule_all grouped_keyword_allocation_slots >>
  disch_then (qx_choose_then `slots` (map_every assume_tac o CONJUNCTS o BETA_RULE)) >>
  `LIST_REL (\(n,dst,ty,e) (aid,q,base,tv).
    dst = Var q /\ abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
    is_abi_dynamic ce.ce_struct_fields ty = tv_abi_dynamic tv /\
    base + type_memory_size tv < dimword (:256)) vars slots` by
    (qpat_assum `LIST_REL (\(_,_,ty,_) tv. abi_decoder_coherent _ _ _ ty tv) _ _`
       (strip_assume_tac o REWRITE_RULE [LIST_REL_EL_EQN]) >>
     qpat_assum `LIST_REL _ vars slots` (strip_assume_tac o REWRITE_RULE [LIST_REL_EL_EQN]) >>
     pure_rewrite_tac[LIST_REL_EL_EQN] >> conj_tac >- simp[] >>
     qx_gen_tac `i` >> strip_tac >>
     `i < LENGTH slots` by decide_tac >>
     `EL i (DROP pos tvs) = SND (SND (SND (EL i slots)))` by
       (qpat_assum `MAP _ slots = DROP pos tvs` (fn th => pure_rewrite_tac[GSYM th]) >>
        simp[EL_MAP, pairTheory.UNCURRY]) >>
     qpat_assum `!j. j < LENGTH vars ==> _ (EL j vars) (EL j slots)`
       (qspec_then `i` mp_tac) >>
     qpat_assum `!j. j < LENGTH vars ==> _ (EL j vars) (EL j (DROP pos tvs))`
       (qspec_then `i` mp_tac) >>
     simp_tac bool_ss [pairTheory.UNCURRY] >>
     rpt strip_tac >> fs[] >> metis_tac[calldata_coherent_dynamic]) >>
  `EVERY (\(aid,q,base,tv).
    aid < si.cs_next_id /\ not_fresh_at si q /\ base < dimword (:256) /\
    FLOOKUP s.vs_allocas aid = SOME (base,type_memory_size tv) /\
    lookup_var q s = SOME (n2w base) /\ ptr_covers G tn q s (type_memory_size tv)) slots` by
    (qpat_assum `LIST_REL (\(n,op,ty,e) (id,q,b,tv).
         op = Var q /\ type_memory_bytes ce ty = type_memory_size tv /\ _) vars slots`
       (strip_assume_tac o REWRITE_RULE [LIST_REL_EL_EQN]) >>
     simp[EVERY_EL] >> qx_gen_tac `i` >> strip_tac >>
     qpat_assum `!j. j < LENGTH vars ==> _ (EL j vars) (EL j slots)`
       (qspec_then `i` mp_tac) >>
     simp_tac bool_ss [pairTheory.UNCURRY] >> strip_tac >>
     `i < LENGTH vars` by decide_tac >> fs[] >> decide_tac) >>
  `LENGTH (DROP pos tvs) = LENGTH ds` by metis_tac[LIST_REL_LENGTH] >>
  `LENGTH (TAKE k (DROP pos tvs)) = k` by simp[LENGTH_TAKE] >>
  `TAKE k (DROP pos tvs) = MAP (\(_,_,_,tv). tv) (TAKE k slots)` by simp[MAP_TAKE] >>
  `4 + SUM (MAP tv_abi_size (TAKE pos tvs)) + SUM (MAP tv_abi_size (TAKE k (DROP pos tvs))) <
   dimword (:256)` by
    (qspecl_then [`pos`,`tvs`] (mp_tac o AP_TERM ``\xs. SUM (MAP tv_abi_size xs)``) TAKE_DROP >>
     qspecl_then [`k`,`DROP pos tvs`] (mp_tac o AP_TERM ``\xs. SUM (MAP tv_abi_size xs)``) TAKE_DROP >>
     simp_tac bool_ss [MAP_APPEND, listTheory.SUM_APPEND] >> decide_tac) >>
  qpat_assum `LENGTH (TAKE k (DROP pos tvs)) = k` (fn len =>
    drule_all (SIMP_RULE bool_ss [len, EVERY_DEF, listTheory.MAP, APPEND_NIL]
      (BETA_RULE (Q.INST [`tvs` |-> `TAKE k (DROP pos tvs)`, `kept` |-> `[]`]
        (SPEC_ALL grouped_supplied_initializers))))) >>
  disch_then (qspec_then `PG` (qx_choosel_then [`last`,`shlast`,`t`,`J`,`tz`]
    (map_every assume_tac o CONJUNCTS o SIMP_RULE bool_ss [pairTheory.UNCURRY_DEF, GSYM CONJ_ASSOC]))) >>
  qexistsl_tac [`slots`,`last`,`shlast`,`t`,`J`,`tz`] >>
  asm_rewrite_tac[]
QED

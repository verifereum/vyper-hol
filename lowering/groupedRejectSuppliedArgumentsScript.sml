(* Replay the supplied suffix and recover its initialized argument slots. *)
Theory groupedRejectSuppliedArguments
Ancestors
  ptrDiscipline fragGasOriginPtr list pred_set venomInst venomState
  callRejectMemory[ignore_grammar] groupedKeywordDecode abiDecoderCoherence compileEnv
  vyperContext finite_map rich_list words groupedKeywordInitialize pair groupedEntryAllocation
  calldataSourceCorrespondence groupedDefaultArguments arithmetic relation vyperAST vyperTypeBuiltins
Libs
  groupedRejectSlotsLib

val _ = Parse.hide "tops";

Theorem row22_kwarg_metadata[local]:
  LIST_REL (\(name,ty) tv. abi_decoder_coherent ce env ce.ce_struct_fields ty tv)
    args all_tvs /\ LENGTH defaults <= LENGTH args /\
  n = LENGTH args - LENGTH defaults /\
  MAP (\(name,_,ty,e). (name,ty,e)) vars =
    MAP (\((name,ty),e). (name,ty,e)) (ZIP (DROP n args,defaults)) ==>
  LIST_REL (^row22_kw_abi ce env) vars (DROP n all_tvs) /\
  MAP (\(_,_,_,e). e) vars = defaults
Proof
  strip_tac >>
  `LENGTH args = LENGTH all_tvs` by metis_tac[LIST_REL_LENGTH] >>
  `LENGTH (DROP n args) = LENGTH defaults /\ LENGTH (DROP n all_tvs) = LENGTH defaults` by
    (simp[LENGTH_DROP] >> decide_tac) >>
  `LENGTH vars = LENGTH defaults` by
    (qpat_assum `MAP _ vars = _` (mp_tac o Q.AP_TERM `LENGTH`) >> simp[LENGTH_ZIP]) >>
  `n + LENGTH defaults = LENGTH args` by decide_tac >>
  qpat_x_assum `n = _` kall_tac >>
  simp[LIST_REL_EL_EQN, LIST_EQ_REWRITE] >> conj_tac
  >- (qx_gen_tac `j` >> strip_tac >>
      `j < LENGTH vars /\ n+j < LENGTH args` by decide_tac >>
      Cases_on `EL j vars` >> PairCases_on `r` >>
      rename1 `EL j vars = (name,op,ty,e)` >>
      `EL (n+j) args = (name,ty)` by
        (qpat_assum `MAP _ vars = _` (mp_tac o Q.AP_TERM `EL j`) >>
         simp[EL_MAP, EL_ZIP, EL_DROP] >>
         Cases_on `EL (j+n) args` >> asm_rewrite_tac[] >> simp[]) >>
      qpat_assum `LIST_REL _ args all_tvs`
        (qspec_then `n+j` mp_tac o CONJUNCT2 o REWRITE_RULE [LIST_REL_EL_EQN]) >>
      simp[EL_DROP, ADD_COMM]) >>
  qx_gen_tac `j` >> strip_tac >> simp[EL_MAP] >>
  qpat_assum `MAP _ vars = _` (mp_tac o Q.AP_TERM `EL j`) >>
  simp[EL_MAP, EL_ZIP] >>
  Cases_on `EL j vars` >> PairCases_on `r` >> Cases_on `EL j (DROP n args)` >> simp[]
QED

Theorem row22_supplied_suffix_start:
  LENGTH defaults <= LENGTH args /\ n = LENGTH args - LENGTH defaults /\
  k <= LENGTH defaults /\ tvs = TAKE (n+k) all_tvs /\
  LIST_REL (\(name,ty) tv. abi_decoder_coherent ce env ce.ce_struct_fields ty tv)
    args all_tvs /\
  specs = MAP (\((name,ty),e). (name,ty,e)) (ZIP (DROP n args,defaults)) /\
  off = min_calldata_size ce (TAKE n args) 0 /\
  compile_create_kwarg_allocas ce specs alloc_start = (vars,alloc_end) /\
  compile_init_kwargs ce vars off k (Lit 0w) sa = ((),sb) /\
  compile_init_kwargs (gas_shadow_env T ce) (MAP (\(name,p,ty,e). (name,p,ty,gas_shadow_expr e)) vars)
    off k (Lit 0w) sha = ((),shb) /\
  fn_has_code sa sb fn /\ fn_has_code sha shb shfn /\ gas_shadow_state sa sha /\
  4 + SUM (MAP tv_abi_size tvs) <= LENGTH s.vs_call_ctx.cc_calldata /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
  calldata_decode_args s.vs_call_ctx.cc_calldata (DROP n tvs)
    (SUM (MAP tv_abi_size (TAKE n tvs))) <> NONE /\
  (!name op ty e. MEM (name,op,ty,e) vars ==>
    ?id q b. op = Var q /\ not_fresh_at sa q /\ lookup_var q s = SOME (n2w b) /\
      MEM (mk_inst id ALLOCA [Lit (n2w (type_memory_bytes ce ty))] [q]) (fn_insts fn) /\
      FLOOKUP s.vs_allocas id = SOME (b,type_memory_bytes ce ty) /\
      b + type_memory_bytes ce ty < dimword (:256) /\ id < sa.cs_next_id /\
      ptr_covers G tn q s (type_memory_bytes ce ty)) /\
  selected_registration_resources ctx fn site 0 sa s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size fn s <= w2n s.vs_initial_fmp) /\
  unit_alloca_budget ctx < dimword (:256) /\ fn_inst_ids_distinct fn /\
  (!label bb. lookup_block label fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) ==>
  ?last shlast t J tz slots vals.
    compile_init_kwargs ce (DROP k vars) (4 + SUM (MAP tv_abi_size tvs)) 0
      (Lit 0w) last = ((),sb) /\
    compile_init_kwargs (gas_shadow_env T ce)
      (MAP (\(name,p,ty,e). (name,p,ty,gas_shadow_expr e)) (DROP k vars))
      (4 + SUM (MAP tv_abi_size tvs)) 0 (Lit 0w) shlast = ((),shb) /\
    fn_has_code last sb fn /\ fn_has_code shlast shb shfn /\ gas_shadow_state last shlast /\
    selected_registration_resources ctx fn site 0 last t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t /\
      t.vs_alloca_next + pending_alloca_size fn t <= w2n t.vs_initial_fmp) /\
    EVERY (^row22_kw_alloc last t J tz) (DROP k slots) /\
    LIST_REL (\(aid,p,base,tv) v. ^row22_kw_initialized last t J tz (aid,p,base,tv,v))
      (TAKE k slots) vals /\
    calldata_decode_args s.vs_call_ctx.cc_calldata (DROP n tvs)
      (SUM (MAP tv_abi_size (TAKE n tvs))) = SOME vals /\
    ALL_DISTINCT (MAP FST slots) /\
    LIST_REL (^row22_kw_meta ce env) (DROP k vars) (DROP k slots) /\
    MAP (\(_,_,_,tv). tv) slots = DROP n all_tvs /\
    MAP (\(_,_,_,e). e) (DROP k vars) = DROP k defaults /\
    selected_registration_frame s tn t tz /\ tz.t_mem SUBSET tn.t_mem /\
    (!D exp. gas_origin_ptr_path (D,0,exp,ctx,fn,[]) (s,G,tn) [] (OK t,J,tz))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule compile_create_kwarg_allocas_preserves_specs >> strip_tac >>
  drule grouped_keyword_allocations_distinct >> strip_tac >>
  `MAP (\(name,_,ty,e). (name,ty,e)) vars =
    MAP (\((name,ty),e). (name,ty,e)) (ZIP (DROP n args,defaults))` by metis_tac[] >>
  drule_all row22_kwarg_metadata >> strip_tac >>
  suspend "slots"
QED

Resume row22_supplied_suffix_start[slots]:
  `LIST_REL (\(_,_,ty,_) tv. type_memory_bytes ce ty = type_memory_size tv)
     vars (DROP n all_tvs)` by
    (qpat_assum `LIST_REL _ vars (DROP n all_tvs)` mp_tac >>
     ho_match_mp_tac LIST_REL_mono >> qx_gen_tac `arg` >> PairCases_on `arg` >>
     simp[] >> metis_tac[abi_decoder_coherent_header, abi_decoder_header_def]) >>
  drule_all grouped_keyword_allocation_slots >>
  disch_then (qx_choose_then `slots` (map_every assume_tac o CONJUNCTS)) >>
  `LIST_REL (^row22_kw_meta ce env) vars slots /\
   EVERY (^row22_kw_alloc sa s G tn) slots` by
    (qpat_assum `LIST_REL _ vars slots`
       (strip_assume_tac o REWRITE_RULE [LIST_REL_EL_EQN]) >>
     qpat_assum `LIST_REL (^row22_kw_abi ce env) vars (DROP n all_tvs)`
       (strip_assume_tac o REWRITE_RULE [LIST_REL_EL_EQN]) >>
     pure_rewrite_tac [LIST_REL_EL_EQN, EVERY_EL] >> rpt conj_tac >>
     TRY (first_assum ACCEPT_TAC) >> qx_gen_tac `i` >> strip_tac >>
     `i < LENGTH vars /\ i < LENGTH slots` by decide_tac >>
     Cases_on `EL i vars` >> rename1 `EL i vars = (_,var_tail)` >> PairCases_on `var_tail` >>
     Cases_on `EL i slots` >> rename1 `EL i slots = (_,slot_tail)` >> PairCases_on `slot_tail` >>
     qpat_assum `!i. i < LENGTH vars ==> _ (EL i vars) (EL i slots)`
       (qspec_then `i` (drule_then assume_tac)) >>
     qpat_assum `!i. i < LENGTH vars ==> (^row22_kw_abi ce env) _ _`
       (qspec_then `i` (drule_then assume_tac)) >>
     `EL i (DROP n all_tvs) = (\(_,_,_,tv). tv) (EL i slots)` by
       (qpat_assum `MAP _ slots = DROP n all_tvs` (SUBST1_TAC o SYM) >> simp[EL_MAP]) >>
     qpat_assum `EL i vars = _` (fn vr =>
       qpat_assum `EL i slots = _` (fn sr =>
         qpat_assum `EL i (DROP n all_tvs) = _` (fn tr =>
           map_every (fn pat =>
             qpat_x_assum pat (strip_assume_tac o SIMP_RULE (srw_ss()) [vr,sr,tr]))
             [`_ (EL i vars) (EL i slots)`, `(^row22_kw_abi ce env) (EL i vars) _`]))) >>
     simp[] >> (decide_tac ORELSE (drule calldata_coherent_dynamic >> simp[]))) >>
  suspend "run"
QED

Resume row22_supplied_suffix_start[run]:
  `LENGTH args = LENGTH all_tvs` by metis_tac[LIST_REL_LENGTH] >>
  `n <= LENGTH all_tvs /\ LENGTH (DROP n all_tvs) = LENGTH defaults` by
    (simp[LENGTH_DROP] >> decide_tac) >>
  qpat_x_assum `n = _` kall_tac >>
  `TAKE n tvs = TAKE n all_tvs` by simp[TAKE_TAKE_T] >>
  `DROP n tvs = TAKE k (DROP n all_tvs)` by simp[DROP_TAKE] >>
  `LENGTH (DROP n tvs) = k` by
    (qpat_assum `DROP n tvs = _` SUBST1_TAC >> simp[]) >>
  `LIST_REL (\arg tv. abi_decoder_coherent ce env ce.ce_struct_fields (SND arg) tv)
    args all_tvs` by
    (qpat_assum `LIST_REL (\(name,ty) tv. abi_decoder_coherent _ _ _ ty tv) args all_tvs`
       mp_tac >> ho_match_mp_tac LIST_REL_mono >> Cases >> simp[]) >>
  `off = 4 + SUM (MAP tv_abi_size (TAKE n tvs))` by
    (qpat_assum `LIST_REL (\arg tv. abi_decoder_coherent _ _ _ (SND arg) tv) args all_tvs`
       (mp_tac o Q.INST [`n` |-> `n`] o MATCH_MP grouped_argument_min_calldata_size) >>
     simp[]) >>
  `4 + SUM (MAP tv_abi_size tvs) = off + SUM (MAP tv_abi_size (DROP n tvs))` by
    (qspecl_then [`n`,`tvs`] (mp_tac o Q.AP_TERM `SUM o MAP tv_abi_size`) TAKE_DROP >>
     qpat_assum `off = 4 + _` (fn eq =>
       simp_tac (srw_ss()) [eq, MAP_APPEND, SUM_APPEND, ADD_ASSOC]) >> decide_tac) >>
  qabbrev_tac `kw = DROP n tvs` >>
  qabbrev_tac `pos = SUM (MAP tv_abi_size (TAKE n tvs))` >>
  `?vals. calldata_decode_args s.vs_call_ctx.cc_calldata kw pos = SOME vals` by
    (qpat_assum `calldata_decode_args _ kw pos <> NONE` mp_tac >>
     metis_tac[optionTheory.option_nchotomy]) >>
  `kw = MAP (\(_,_,_,tv). tv) (TAKE (LENGTH kw) slots)` by
    (pure_rewrite_tac [MAP_TAKE] >>
     qpat_assum `MAP _ slots = DROP n all_tvs` (pure_once_rewrite_tac o single) >>
     asm_rewrite_tac[]) >>
  `4 + pos + SUM (MAP tv_abi_size kw) < dimword (:256)` by decide_tac >>
  qpat_assum `off = 4 + pos` (fn offset =>
    qpat_assum `LENGTH kw = k` (fn count =>
      map_every (fn pat => qpat_assum pat
        (assume_tac o PURE_REWRITE_RULE [offset, SYM count]))
        [`compile_init_kwargs ce vars _ _ _ sa = _`,
         `compile_init_kwargs _ (MAP _ vars) _ _ _ sha = _`])) >>
  qpat_assum `LIST_REL (^row22_kw_meta ce env) vars slots`
    (assume_tac o SIMP_RULE bool_ss []) >>
  qpat_assum `EVERY (^row22_kw_alloc sa s G tn) slots`
    (assume_tac o SIMP_RULE bool_ss []) >>
  drule_all (SIMP_RULE bool_ss [EVERY_DEF, MAP, APPEND_NIL]
    (Q.INST [`kept` |-> `[]`, `PG` |-> `[]`]
      (SPEC_ALL (INST_TYPE [alpha |-> ``:string``] grouped_supplied_initializers)))) >>
  disch_then (qx_choosel_then [`last`,`shlast`,`t`,`J`,`tz`]
    (map_every assume_tac o CONJUNCTS)) >>
  `4 + pos + SUM (MAP tv_abi_size kw) = 4 + SUM (MAP tv_abi_size tvs)` by decide_tac >>
  qpat_assum `LENGTH kw = k` (fn count =>
    qpat_assum `4 + pos + SUM _ = _` (fn offset =>
      map_every (fn pat => qpat_x_assum pat
        (assume_tac o PURE_REWRITE_RULE [count, offset]))
        [`compile_init_kwargs _ _ _ _ _ last = _`,
         `compile_init_kwargs _ _ _ _ _ shlast = _`,
         `EVERY _ (DROP (LENGTH kw) slots)`, `LIST_REL _ (TAKE (LENGTH kw) slots) vals`])) >>
  qexistsl_tac [`last`,`shlast`,`t`,`J`,`tz`,`slots`,`vals`] >>
  simp_tac bool_ss [] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (irule LIST_REL_DROP >> first_assum ACCEPT_TAC) >>
  simp[MAP_DROP]
QED

Finalise row22_supplied_suffix_start

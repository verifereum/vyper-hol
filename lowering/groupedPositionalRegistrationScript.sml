Theory groupedPositionalRegistration
Ancestors
  selectedAcceptedFold fragGasOriginPtr exprLoweringProps entryStateRel
  loweringStateRelDefs moduleLowering compileEnv ptrDiscipline venomState
  venomMemDefs allocaFrontierBound vyperCalldata list rich_list arithmetic

Theorem grouped_register_positional_suffix:
  LENGTH kw = LENGTH kwtvs /\ LENGTH kw = LENGTH kwvals /\
  LENGTH pos = LENGTH ptvs /\ LENGTH pos = LENGTH pvals /\
  ALL_DISTINCT (MAP FST (pos ++ kw)) /\
  (!c arg tv. MEM (arg,tv) (ZIP (pos ++ kw,ptvs ++ kwtvs)) /\
    c = ce with ce_vars := c.ce_vars ==>
      selected_slot_accepts c env c.ce_struct_fields (SND arg) tv /\
      abi_decoder_coherent c env c.ce_struct_fields (SND arg) tv) /\
  EVERY (\tv. type_memory_size tv < dimword (:256)) (ptvs ++ kwtvs) /\
  LIST_REL (\(name,ty) tv. ?loc. FLOOKUP ce.ce_vars name = SOME loc /\
    var_location_memory_size loc = SOME (type_memory_size tv)) pos ptvs /\
  compile_register_positional_args ce (build_positional_args ce pos) 4
    entry = (cf,last) /\ fn_has_code entry last fn /\ fn_inst_ids_distinct fn /\
  (!lbl bb. lookup_block lbl fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  calldata_decode_args s.vs_call_ctx.cc_calldata ptvs 0 = SOME pvals /\
  4+SUM (MAP tv_abi_size ptvs) < dimword (:256) /\
  selected_registration_owners fn (MAP FST kw) kwtvs kwvals (LENGTH kw) ce entry s G tn /\
  selected_registration_resources ctx fn site lo entry s /\
  unit_alloca_budget ctx < dimword (:256) /\ fresh_vars_wrt last s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size fn s <= w2n s.vs_initial_fmp) /\
  bind_arguments env (pos ++ kw) (pvals ++ kwvals) = SOME envb /\
  LIST_REL (\ty tv. evaluate_type env ty = SOME tv) (MAP SND (pos ++ kw)) (ptvs ++ kwtvs) /\
  (!k. ~MEM k (MAP FST (pos ++ kw)) ==> FLOOKUP cf.ce_vars k = NONE) /\
  local_ptrs_reserved cf last ==>
  ?t J tz.
    selected_registration_owners fn (MAP FST (pos ++ kw)) (ptvs ++ kwtvs)
      (pvals ++ kwvals) (LENGTH (pos ++ kw)) cf last t J tz /\
    selected_registration_resources ctx fn site lo last t /\
    local_ptrs_rel fn cf [envb] t /\
    fresh_vars_wrt last t /\ selected_registration_frame s tn t tz /\
    !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,J,tz)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `LENGTH (kw ++ pos) = LENGTH (kwtvs ++ ptvs) /\
   LENGTH (kw ++ pos) = LENGTH (kwvals ++ pvals) /\
   ALL_DISTINCT (MAP FST (kw ++ pos))` by (fs[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  `!c j. j < LENGTH (kw ++ pos) /\ c = ce with ce_vars := c.ce_vars ==>
    selected_slot_accepts c env c.ce_struct_fields (SND (EL j (kw ++ pos)))
      (EL j (kwtvs ++ ptvs)) /\
    abi_decoder_coherent c env c.ce_struct_fields (SND (EL j (kw ++ pos)))
      (EL j (kwtvs ++ ptvs))` by suspend "decode" >>
  `!j. j < LENGTH (kwtvs ++ ptvs) ==>
    type_memory_size (EL j (kwtvs ++ ptvs)) < dimword (:256)` by
    (gen_tac >> strip_tac >>
     `MEM (EL j (kwtvs ++ ptvs)) (kwtvs ++ ptvs)` by
       (irule EL_MEM >> first_assum ACCEPT_TAC) >>
     `EVERY (\tv. type_memory_size tv < dimword (:256)) (kwtvs ++ ptvs)` by
       fs[EVERY_APPEND] >>
     qpat_assum `EVERY _ (kwtvs ++ ptvs)`
       (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     disch_then (qspec_then `EL j (kwtvs ++ ptvs)` mp_tac) >>
     BETA_TAC >> asm_rewrite_tac[]) >>
  `!j. LENGTH kw <= j /\ j < LENGTH (kw ++ pos) ==> ?loc.
    FLOOKUP ce.ce_vars (FST (EL j (kw ++ pos))) = SOME loc /\
    var_location_memory_size loc = SOME (type_memory_size (EL j (kwtvs ++ ptvs)))` by suspend "location" >>
  `selected_registration_owners fn (MAP FST (kw ++ pos)) (kwtvs ++ ptvs)
    (kwvals ++ pvals) (LENGTH kw) ce entry s G tn` by
    (qpat_assum `selected_registration_owners _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [selected_registration_owners_def, MAP_APPEND] >>
     simp[EL_APPEND_EQN]) >>
  mp_tac (Q.INST [`args` |-> `kw ++ pos`, `tvs` |-> `kwtvs ++ ptvs`,
    `vals` |-> `kwvals ++ pvals`, `ce0` |-> `ce`, `cf` |-> `cf`,
    `last` |-> `last`, `limit` |-> `last`, `fn` |-> `fn`, `ctx` |-> `ctx`,
    `site` |-> `site`, `cd` |-> `s.vs_call_ctx.cc_calldata`, `PG` |-> `PG`,
    `lo` |-> `lo`, `env` |-> `env`] (SPEC_ALL selected_registration_suffix)) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> fs[]) >>
  disch_then (qspecl_then [`LENGTH kw`,`ce`,`0`,`entry`,`s`,`G`,`tn`] mp_tac) >>
  impl_tac >- suspend "suffix" >>
  disch_then (qx_choosel_then [`t`,`J`,`tz`] strip_assume_tac) >>
  `selected_registration_owners fn (MAP FST (pos ++ kw)) (ptvs ++ kwtvs)
    (pvals ++ kwvals) (LENGTH (pos ++ kw)) cf last t J tz` by
    (mp_tac (Q.INST [`names1` |-> `MAP FST (kw:(string # type) list)`,
       `names2` |-> `MAP FST (pos:(string # type) list)`,
       `tvs1` |-> `kwtvs`,`tvs2` |-> `ptvs`,`vals1` |-> `kwvals`,`vals2` |-> `pvals`,
       `fn` |-> `fn`,`ce` |-> `cf`,`st` |-> `last`,`s` |-> `t`,`G` |-> `J`,`tn` |-> `tz`]
       (SPEC_ALL selected_registration_owners_swap_append)) >>
     simp_tac bool_ss [LENGTH_MAP, GSYM LENGTH_APPEND, GSYM MAP_APPEND] >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then ACCEPT_TAC) >>
  `alloca_inv t /\ alloca_frontier_inv ctx fn site t` by
    fs[selected_registration_resources_def] >>
  `t.vs_alloca_next < dimword (:256)` by
    (qpat_assum `alloca_frontier_inv _ _ _ _` mp_tac >>
     simp_tac bool_ss [alloca_frontier_inv_def] >> strip_tac >> decide_tac) >>
  qexistsl_tac [`t`,`J`,`tz`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  mp_tac (Q.INST [`H` |-> `J`,`args` |-> `pos ++ kw`,`last` |-> `last`,
    `env` |-> `env`,`u` |-> `tz`,`tvs` |-> `ptvs ++ kwtvs`,
    `vals` |-> `pvals ++ kwvals`,`envb` |-> `envb`,`cf` |-> `cf`,`fn` |-> `fn`,`t` |-> `t`]
    (SPEC_ALL selected_registration_terminal_locals)) >>
  asm_rewrite_tac[LENGTH_APPEND] >> fs[]
QED

Resume grouped_register_positional_suffix[decode]:
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  first_x_assum irule >> conj_tac >- first_assum ACCEPT_TAC >>
  `LENGTH (pos ++ kw) = LENGTH (ptvs ++ kwtvs)` by
    (fs[LENGTH_APPEND] >> decide_tac) >>
  qpat_assum `LENGTH (pos ++ kw) = LENGTH (ptvs ++ kwtvs)`
    (fn len => PURE_REWRITE_TAC [MATCH_MP
      (Q.SPECL [`pos ++ kw`,`ptvs ++ kwtvs`,
        `(EL j (kw ++ pos), EL j (kwtvs ++ ptvs))`] MEM_ZIP) len]) >>
  `j < LENGTH kw + LENGTH pos` by fs[LENGTH_APPEND] >>
  Cases_on `j < LENGTH kw`
  >- (qexists_tac `LENGTH pos+j` >>
      conj_tac >- fs[LENGTH_APPEND] >>
      simp[EL_APPEND_EQN] >> AP_THM_TAC >> AP_TERM_TAC >> decide_tac) >>
  qexists_tac `j - LENGTH kw` >>
  conj_tac >- (fs[LENGTH_APPEND] >> decide_tac) >>
  simp[EL_APPEND_EQN] >> AP_THM_TAC >> AP_TERM_TAC >> decide_tac
QED

Resume grouped_register_positional_suffix[location]:
  gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `LIST_REL _ pos ptvs`
    (strip_assume_tac o REWRITE_RULE [LIST_REL_EL_EQN]) >>
  `j - LENGTH kw < LENGTH pos` by (fs[LENGTH_APPEND] >> decide_tac) >>
  `LENGTH kwtvs <= j` by decide_tac >>
  `EL j (kw ++ pos) = EL (j - LENGTH kw) pos` by
    (irule EL_APPEND2 >> first_assum ACCEPT_TAC) >>
  `EL j (kwtvs ++ ptvs) = EL (j - LENGTH kw) ptvs` by
    (drule_then (qspec_then `ptvs` mp_tac) (Q.SPECL [`kwtvs`,`j`] EL_APPEND2) >>
     `j - LENGTH kwtvs = j - LENGTH kw` by decide_tac >>
     asm_simp_tac bool_ss []) >>
  qpat_assum `!n. n < LENGTH pos ==> _`
    (qspec_then `j - LENGTH kw` mp_tac) >>
  Cases_on `EL (j - LENGTH kw) pos` >>
  asm_rewrite_tac[pairTheory.UNCURRY, pairTheory.FST] >> BETA_TAC >> simp_tac bool_ss []
QED

Resume grouped_register_positional_suffix[suffix]:
  `DROP (LENGTH kw) (kwtvs ++ ptvs) = ptvs` by
    (qpat_assum `LENGTH kw = LENGTH kwtvs`
       (fn th => pure_rewrite_tac [th,DROP_LENGTH_APPEND] >> REFL_TAC)) >>
  `DROP (LENGTH kw) (kwvals ++ pvals) = pvals` by
    (qpat_assum `LENGTH kw = LENGTH kwvals`
       (fn th => pure_rewrite_tac [th,DROP_LENGTH_APPEND] >> REFL_TAC)) >>
  asm_rewrite_tac[DROP_LENGTH_APPEND, compile_env_component_equality,
    arithmeticTheory.ADD_0, arithmeticTheory.LESS_EQ_REFL, arithmeticTheory.LESS_EQ_ADD,
    LENGTH_APPEND] >>
  simp_tac (srw_ss()) [] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise grouped_register_positional_suffix

(* Positional registration on the fixed source calldata. *)
Theory selectedAcceptedFold
Ancestors
  decoderOriginAllocationFrame
  selectedAcceptedInterfaces calldataRegistrationExec calldataSourceSize
  calldataSourceCorrespondence calldataRegistrationTerminalBindings
  defaultConcreteRegistrationCompiler fragGasPathFrameMem
  entryPtrSeamRegister entryStateRel allocaFrontierBound rich_list
  compileVyper calldataRegistration ctorRegisterArgs
  fragGasOriginPtrLoop bodyMemAggregatePath

Definition selected_registration_resources_def:
  selected_registration_resources ctx fn site lo st s <=>
    (!id entry. FLOOKUP s.vs_allocas id = SOME entry ==> id < st.cs_next_id) /\
    (!inst w b n. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_operands = [Lit w] /\
      FLOOKUP s.vs_allocas inst.inst_id = SOME (b,n) ==> n = w2n w) /\
    alloca_inv s /\ alloca_frontier_inv ctx fn site s /\ allocas_from lo s /\
    lo <= s.vs_alloca_next /\ fresh_vars_wrt st s /\ ~s.vs_halted /\
    s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts
End

Definition selected_registration_frame_def:
  selected_registration_frame s Gtn t Utn <=>
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\
    t.vs_code = s.vs_code /\ t.vs_accounts = s.vs_accounts /\
    t.vs_transient = s.vs_transient /\ t.vs_logs = s.vs_logs /\
    t.vs_outcomes = s.vs_outcomes /\ t.vs_requests = s.vs_requests /\
    t.vs_pending_deletions = s.vs_pending_deletions /\
    t.vs_tx_ctx = s.vs_tx_ctx /\ t.vs_block_ctx = s.vs_block_ctx /\
    t.vs_fmp = s.vs_fmp /\ t.vs_gas_readings = s.vs_gas_readings /\
    Utn.t_stor = Gtn.t_stor /\ Utn.t_trans = Gtn.t_trans /\ Utn.t_imm = Gtn.t_imm
End

Definition selected_registration_owners_def:
  selected_registration_owners fn names tvs vals i ce st s G tn <=>
    !j. j < i ==> ?aid q p n.
      MEM (mk_inst aid ALLOCA [Lit (n2w n)] [q]) (fn_insts fn) /\
      aid < st.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (p,n) /\
      FLOOKUP ce.ce_vars (EL j names) = SOME (PtrVar (Var q) n) /\
      lookup_var q s = SOME (n2w p) /\ n = type_memory_size (EL j tvs) /\
      ptr_covers G tn q s n /\ val_wf (EL j tvs) (EL j vals) /\
      val_footprint (EL j tvs) (EL j vals) <= n /\
      (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
        val_in_memory (EL j tvs) (EL j vals) p mem)
End

Theorem selected_registration_frame_trans[local]:
  selected_registration_frame s tn t u /\ selected_registration_frame t u v z ==>
  selected_registration_frame s tn v z
Proof
  rw[selected_registration_frame_def]
QED

Theorem selected_registration_head[local]:
  selected_slot_accepts ce env ce.ce_struct_fields ty (EL i tvs) /\
  abi_decoder_coherent ce env ce.ce_struct_fields ty (EL i tvs) /\
  (?loc. FLOOKUP ce.ce_vars (EL i names) = SOME loc /\
    var_location_memory_size loc = SOME (type_memory_size (EL i tvs))) /\
  type_memory_size (EL i tvs) < dimword (:256) /\
  ALL_DISTINCT names /\ i < LENGTH names /\
  compile_register_positional_args ce [build_positional_arg ce (EL i names,ty)]
    (4+ofs) st = (ce1,st1) /\
  cd = s.vs_call_ctx.cc_calldata /\ 4+ofs < dimword (:256) /\
  calldata_decode_args cd (EL i tvs::more) ofs = SOME (EL i vals::xs) /\
  selected_registration_owners fn names tvs vals i ce st s G tn /\
  selected_registration_resources ctx fn site lo st s /\
  fn_has_code st st1 fn /\ fn_inst_ids_distinct fn /\
  (!lbl bb. lookup_block lbl fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  st1.cs_next_var <= limit.cs_next_var /\ fresh_vars_wrt limit s /\
  unit_alloca_budget ctx < dimword (:256) /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size fn s <= w2n s.vs_initial_fmp) ==>
  ?t H u.
    selected_registration_owners fn names tvs vals (SUC i) ce1 st1 t H u /\
    selected_registration_resources ctx fn site lo st1 t /\
    fresh_vars_wrt limit t /\ selected_registration_frame s tn t u /\
    calldata_decode_args cd more (ofs + tv_abi_size (EL i tvs)) = SOME xs /\
    !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,H,u)
Proof
  strip_tac >>
  qabbrev_tac `tv = EL i tvs` >>
  qabbrev_tac `dyn = tv_abi_dynamic tv` >>
  qabbrev_tac `delta = w2n (cd_word cd (4+ofs))` >>
  qabbrev_tac `srcpos = if dyn then (4+delta) MOD dimword (:256) else 4+ofs` >>
  `dyn = tv_abi_dynamic tv /\ delta = w2n (cd_word cd (4+ofs)) /\
   srcpos = (if dyn then (4+delta) MOD dimword (:256) else 4+ofs)` by
    metis_tac[markerTheory.Abbrev_def] >>
  drule_all selected_slot_source_input >> strip_tac >>
  `is_abi_dynamic ce.ce_struct_fields ty = dyn` by metis_tac[calldata_coherent_dynamic] >>
  `abi_embedded_static_size ce.ce_struct_fields ty = tv_abi_size tv` by
    metis_tac[calldata_coherent_embedded_size] >>
  `is_word_type ty ==> ~dyn /\ ?clamp.
      type_to_abi_dec_info ce.ce_struct_fields ce ty = DecPrimWord clamp` by
    (strip_tac >> conj_tac
     >- (qpat_assum `is_abi_dynamic _ _ <=> dyn`
           (once_rewrite_tac o single o GSYM) >>
         irule ctor_word_type_static >> first_assum ACCEPT_TAC) >>
     irule word_type_decoder_primitive >> first_assum ACCEPT_TAC) >>
  `delta = w2n (cd_word s.vs_call_ctx.cc_calldata (4+ofs))` by metis_tac[] >>
  qpat_x_assum `compile_register_positional_args _ _ _ _ = _`
    (mp_tac o BETA_RULE o REWRITE_RULE [build_positional_arg_def, LET_THM]) >>
  qpat_assum `is_abi_dynamic _ _ <=> dyn` (once_rewrite_tac o single) >>
  qpat_assum `abi_embedded_static_size _ _ = _` (once_rewrite_tac o single) >>
  strip_tac >>
  qpat_x_assum `selected_registration_resources _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [selected_registration_resources_def]) >>
  `!bb. lookup_block st1.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0` by metis_tac[] >>
  qpat_x_assum `selected_slot_accepts _ _ _ _ _`
    (drule o REWRITE_RULE [selected_slot_accepts_def]) >>
  disch_then drule >> disch_then drule >>
  disch_then (drule_at (Pat `cd_decode _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `abi_decode_load _ _ _ = _`)) >>
  disch_then (drule_at (Pat `alloca_frontier_inv _ _ _ _`)) >>
  disch_then (drule_at (Pat `allocas_from _ _`)) >>
  disch_then (drule_at (Pat `_ <= limit.cs_next_var`)) >>
  disch_then (qspecl_then [`PG`,`G`,`tn`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE REFL_TAC))) >>
  strip_tac >>
  qexistsl [`t`,`H`,`u`] >> simp[selected_registration_resources_def,
    selected_registration_frame_def] >>
  conj_tac
  >- (qpat_x_assum `selected_registration_owners _ _ _ _ _ _ _ _ _ _` mp_tac >>
      rewrite_tac[selected_registration_owners_def] >> strip_tac >>
      gen_tac >> strip_tac >>
      irule (BETA_RULE (Q.INST
        [`R` |-> `\aid q n. MEM (mk_inst aid ALLOCA [Lit (n2w n)] [q]) (fn_insts fn)`]
        registration_owned_prefix_invariant_update)) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`G`,`ce`,`i`,`p`,`q`,`s`,`st`,`tn`] >>
      qpat_assum `Abbrev (tv = _)`
        (fn th => pure_once_rewrite_tac [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
      rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE REFL_TAC))
  >- (qpat_assum `(!inst w b k. _ ==> _) ==> !inst w b k. _ ==> _` mp_tac >>
      impl_tac >- first_assum ACCEPT_TAC >> simp[]) >>
  decide_tac
QED

Theorem selected_registration_compile_cons[local]:
  abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
  compile_register_positional_args ce (build_positional_args ce ((name,ty)::args))
    (4+ofs) st = (cf,last) /\ fn_has_code st last fn ==>
  ?ce1 mid.
    compile_register_positional_args ce [build_positional_arg ce (name,ty)]
      (4+ofs) st = (ce1,mid) /\ fn_has_code st mid fn /\
    compile_register_positional_args ce1 (build_positional_args ce1 args)
      (4+(ofs+tv_abi_size tv)) mid = (cf,last) /\ fn_has_code mid last fn /\
    ce1 = ce with ce_vars := ce1.ce_vars /\
    (!k. k <> name ==> FLOOKUP ce1.ce_vars k = FLOOKUP ce.ce_vars k) /\
    mid.cs_next_var <= last.cs_next_var
Proof
  strip_tac >>
  `abi_embedded_static_size ce.ce_struct_fields ty = tv_abi_size tv` by
    metis_tac[calldata_coherent_embedded_size] >>
  `build_positional_args ce ((name,ty)::args) =
   [build_positional_arg ce (name,ty)] ++ build_positional_args ce args` by
    simp[build_positional_args_def] >>
  qpat_x_assum `compile_register_positional_args _ _ _ _ = _` mp_tac >>
  qpat_x_assum `build_positional_args _ (_::_) = _` (pure_once_rewrite_tac o single) >>
  rewrite_tac[actualRegistrationCodeTheory.register_positional_args_append] >>
  `SUM (MAP (\(n,p,d,sz,di). sz) [build_positional_arg ce (name,ty)]) =
    tv_abi_size tv` by simp[build_positional_arg_def] >>
  `4 + ofs + SUM (MAP (\(n,p,d,sz,di). sz) [build_positional_arg ce (name,ty)]) =
    4 + (ofs + tv_abi_size tv)` by decide_tac >>
  qpat_assum `4 + ofs + SUM _ = _` (pure_once_rewrite_tac o single) >>
  strip_tac >>
  rename1 `compile_register_positional_args ce [_] _ st = (ce1,mid)` >>
  `cs_extends st mid /\ cs_extends mid last` by
    metis_tac[actualRegistrationCodeTheory.register_positional_args_suffix_extends] >>
  `fn_has_code st mid fn /\ fn_has_code mid last fn` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  qpat_assum `compile_register_positional_args _ [_] _ _ = _`
    (mp_tac o MATCH_MP compile_register_positional_args_cenv) >> strip_tac >>
  `build_positional_args ce1 args = build_positional_args ce args` by
    (irule build_positional_args_layout_cong >>
     qpat_assum `ce1 = ce with ce_vars := ce1.ce_vars` (once_rewrite_tac o single) >>
     simp[]) >>
  `mid.cs_next_var <= last.cs_next_var` by metis_tac[registration_compile_counters] >>
  qexistsl [`ce1`,`mid`] >>
  ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac
  >- (qpat_assum `build_positional_args ce1 _ = _` (once_rewrite_tac o single) >>
      first_assum ACCEPT_TAC) >>
  ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- (rpt strip_tac >> first_x_assum irule >> simp[build_positional_arg_def]) >>
  first_assum ACCEPT_TAC
QED

Theorem selected_registration_suffix:
  LENGTH args = LENGTH tvs /\ LENGTH args = LENGTH vals /\
  ALL_DISTINCT (MAP FST args) /\
  (!ce j. j < LENGTH args /\ ce = ce0 with ce_vars := ce.ce_vars ==>
    selected_slot_accepts ce env ce.ce_struct_fields (SND (EL j args)) (EL j tvs) /\
    abi_decoder_coherent ce env ce.ce_struct_fields (SND (EL j args)) (EL j tvs)) /\
  (!j. j < LENGTH args ==> type_memory_size (EL j tvs) < dimword (:256)) /\
  fn_inst_ids_distinct fn /\
  (!lbl bb. lookup_block lbl fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  unit_alloca_budget ctx < dimword (:256) ==>
  !i ce ofs st s G tn.
    i <= LENGTH args /\ ce = ce0 with ce_vars := ce.ce_vars /\
    (!j. i <= j /\ j < LENGTH args ==> ?loc.
      FLOOKUP ce.ce_vars (FST (EL j args)) = SOME loc /\
      var_location_memory_size loc = SOME (type_memory_size (EL j tvs))) /\
    compile_register_positional_args ce (build_positional_args ce (DROP i args))
      (4+ofs) st = (cf,last) /\ fn_has_code st last fn /\
    cd = s.vs_call_ctx.cc_calldata /\
    calldata_decode_args cd (DROP i tvs) ofs = SOME (DROP i vals) /\
    4+ofs+SUM (MAP tv_abi_size (DROP i tvs)) < dimword (:256) /\
    last.cs_next_var <= limit.cs_next_var /\ fresh_vars_wrt limit s /\
    selected_registration_owners fn (MAP FST args) tvs vals i ce st s G tn /\
    selected_registration_resources ctx fn site lo st s /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
      s.vs_alloca_next + pending_alloca_size fn s <= w2n s.vs_initial_fmp) ==>
    ?t H u.
      selected_registration_owners fn (MAP FST args) tvs vals (LENGTH args) cf last t H u /\
      selected_registration_resources ctx fn site lo last t /\
      fresh_vars_wrt limit t /\ selected_registration_frame s tn t u /\
      !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,H,u)
Proof
  strip_tac >> gen_tac >> measureInduct_on `LENGTH args - i` >>
  rpt gen_tac >> strip_tac >> Cases_on `i = LENGTH args`
  >- (qpat_x_assum `i = _` SUBST_ALL_TAC >>
      qpat_x_assum `compile_register_positional_args _ _ _ _ = _` mp_tac >>
      simp[NoAsms, build_positional_args_def, entryArgPtrsTheory.register_positional_args_nil] >>
      strip_tac >> qexistsl [`s`,`G`,`tn`] >>
      rpt conj_tac >- metis_tac[] >- metis_tac[] >- first_assum ACCEPT_TAC
      >- simp[selected_registration_frame_def] >>
      rpt gen_tac >> irule (cj 1 fragGasOriginPtrTheory.gas_origin_ptr_path_rules) >>
      gvs[selected_registration_resources_def]) >>
  `i < LENGTH args /\ i < LENGTH tvs /\ i < LENGTH vals` by decide_tac >>
  `DROP i args = EL i args :: DROP (SUC i) args /\
   DROP i tvs = EL i tvs :: DROP (SUC i) tvs /\
   DROP i vals = EL i vals :: DROP (SUC i) vals` by metis_tac[DROP_CONS_EL] >>
  qpat_assum `!ce j. _` (qspecl_then [`ce`,`i`] mp_tac) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  Cases_on `EL i args` >> rename1 `EL i args = (name,ty)` >>
  qpat_x_assum `compile_register_positional_args _ _ _ _ = _` mp_tac >>
  qpat_assum `DROP i args = _` (pure_once_rewrite_tac o single) >>
  qpat_assum `EL i args = _` (pure_once_rewrite_tac o single) >>
  disch_tac >>
  `abi_decoder_coherent ce env ce.ce_struct_fields ty (EL i tvs)` by metis_tac[pairTheory.SND] >>
  drule_all selected_registration_compile_cons >> strip_tac >>
  rename1 `compile_register_positional_args ce [_] _ st = (ce1,mid)` >>
  `selected_slot_accepts ce env ce.ce_struct_fields ty (EL i tvs)` by
    metis_tac[pairTheory.SND] >>
  `i < LENGTH (MAP FST args)` by simp[] >>
  `EL i (MAP FST args) = name` by simp[EL_MAP] >>
  Q.SUBGOAL_THEN `?loc. FLOOKUP ce.ce_vars (EL i (MAP FST args)) = SOME loc /\
    var_location_memory_size loc = SOME (type_memory_size (EL i tvs))` ASSUME_TAC
  >- (qpat_assum `!j. i <= j /\ _ ==> _` (qspec_then `i` mp_tac) >>
     (impl_tac >- decide_tac) >>
     qpat_assum `EL i (MAP FST args) = name` (pure_once_rewrite_tac o single) >>
     qpat_assum `EL i args = (name,ty)` (pure_once_rewrite_tac o single) >>
     rewrite_tac[pairTheory.FST]) >>
  `compile_register_positional_args ce
      [build_positional_arg ce (EL i (MAP FST args),ty)] (4+ofs) st = (ce1,mid)` by
    (qpat_assum `EL i (MAP FST args) = name` (pure_once_rewrite_tac o single) >>
     first_assum ACCEPT_TAC) >>
  `calldata_decode_args cd (EL i tvs :: DROP (SUC i) tvs) ofs =
      SOME (EL i vals :: DROP (SUC i) vals)` by
    metis_tac[] >>
  `4+ofs+tv_abi_size (EL i tvs)+SUM (MAP tv_abi_size (DROP (SUC i) tvs)) <
      dimword (:256)` by
    (qpat_assum `4+ofs+SUM _ < _` mp_tac >>
     qpat_assum `DROP i tvs = _` (pure_once_rewrite_tac o single) >>
     rewrite_tac[MAP,SUM] >> decide_tac) >>
  `4+ofs < dimword (:256) /\
    4+(ofs+tv_abi_size (EL i tvs))+SUM (MAP tv_abi_size (DROP (SUC i) tvs)) <
      dimword (:256) /\ mid.cs_next_var <= limit.cs_next_var` by decide_tac >>
  `type_memory_size (EL i tvs) < dimword (:256)` by metis_tac[] >>
  drule_at (Pat `selected_registration_owners _ _ _ _ _ _ _ _ _ _`)
    selected_registration_head >>
  disch_then (drule_at (Pat `compile_register_positional_args _ [_] _ _ = _`)) >>
  disch_then (drule_at (Pat `calldata_decode_args _ (_::_) _ = _`)) >>
  disch_then (drule_at (Pat `_ <= limit.cs_next_var`)) >>
  disch_then (drule_at (Pat `selected_registration_resources _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `selected_slot_accepts _ _ _ _ _`)) >>
  disch_then (qspec_then `PG` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  `ce1 = ce0 with ce_vars := ce1.ce_vars` by
    (qpat_assum `ce1 = ce with ce_vars := ce1.ce_vars` (SUBST1_TAC) >>
     qpat_assum `ce = ce0 with ce_vars := ce.ce_vars` (SUBST1_TAC) >>
     simp[NoAsms]) >>
  `cd = t.vs_call_ctx.cc_calldata` by
    (qpat_assum `selected_registration_frame s tn t u`
       (mp_tac o REWRITE_RULE [selected_registration_frame_def]) >>
     strip_tac >> metis_tac[]) >>
  `!j. SUC i <= j /\ j < LENGTH args ==> ?loc.
    FLOOKUP ce1.ce_vars (FST (EL j args)) = SOME loc /\
    var_location_memory_size loc = SOME (type_memory_size (EL j tvs))` by
    (rpt gen_tac >> strip_tac >>
     `FST (EL j args) <> name` by
       (qspecl_then [`MAP FST args`,`i`,`j`] mp_tac listTheory.ALL_DISTINCT_EL_IMP >>
        `i <> j` by decide_tac >>
        simp[EL_MAP] >> metis_tac[]) >>
     `FLOOKUP ce1.ce_vars (FST (EL j args)) = FLOOKUP ce.ce_vars (FST (EL j args))` by
       (first_assum irule >> first_assum ACCEPT_TAC) >>
     pop_assum (pure_once_rewrite_tac o single) >>
     first_assum irule >> decide_tac) >>
  `t.vs_fmp = s.vs_fmp` by
    (qpat_assum `selected_registration_frame s tn t u`
       (strip_assume_tac o REWRITE_RULE [selected_registration_frame_def]) >>
     first_assum ACCEPT_TAC) >>
  `alloca_inv t` by
    (qpat_assum `selected_registration_resources ctx fn site lo mid t`
       (strip_assume_tac o REWRITE_RULE [selected_registration_resources_def]) >>
     first_assum ACCEPT_TAC) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp t /\
    t.vs_alloca_next + pending_alloca_size fn t <= w2n t.vs_initial_fmp)` by
    (qpat_assum `!D explicit. gas_origin_ptr_path _ (s,G,tn) [] (OK t,H,u)`
       (qspecl_then [`ARB`,`{}`] mp_tac) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`fn_inst_ids_distinct fn`,`t.vs_fmp = s.vs_fmp`,`alloca_inv t`,
        `ctx_has_dalloca ctx ==> allocas_below_fmp s /\ _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[decoder_origin_path_room]) >>
  qpat_x_assum `!y. LENGTH args - y < _ ==> _` (qspec_then `SUC i` mp_tac) >>
  (impl_tac >- decide_tac) >>
  disch_then (drule_at (Pat `compile_register_positional_args _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `selected_registration_owners _ _ _ _ _ _ _ _ _ _`)) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE decide_tac))) >>
  strip_tac >>
  rename1 `selected_registration_owners _ _ _ _ (LENGTH args) cf last out J v` >>
  qexistsl [`out`,`J`,`v`] >>
  ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- metis_tac[selected_registration_frame_trans] >>
  qpat_assum `!D explicit. gas_origin_ptr_path _ (s,G,tn) _ _` mp_tac >>
  qpat_assum `!D explicit. gas_origin_ptr_path _ (t,H,u) _ _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  metis_tac[gas_origin_ptr_path_trans]
QED

(* The grouped entry installs keywords first. The source binds positionals first. *)
Theorem selected_registration_owners_swap_append:
  LENGTH names1 = LENGTH tvs1 /\ LENGTH names1 = LENGTH vals1 /\
  LENGTH names2 = LENGTH tvs2 /\ LENGTH names2 = LENGTH vals2 /\
  selected_registration_owners fn (names1 ++ names2) (tvs1 ++ tvs2) (vals1 ++ vals2)
    (LENGTH names1 + LENGTH names2) ce st s G tn ==>
  selected_registration_owners fn (names2 ++ names1) (tvs2 ++ tvs1) (vals2 ++ vals1)
    (LENGTH names2 + LENGTH names1) ce st s G tn
Proof
  simp_tac bool_ss [selected_registration_owners_def] >> strip_tac >>
  gen_tac >> strip_tac >> Cases_on `j < LENGTH (names2 : string list)`
  >- (first_x_assum (qspec_then `LENGTH names1 + j` mp_tac) >>
      impl_tac >- decide_tac >>
      simp[listTheory.EL_APPEND_EQN] >> fs[]) >>
  first_x_assum (qspec_then `j - LENGTH names2` mp_tac) >>
  `j - LENGTH names2 < LENGTH names1` by decide_tac >>
  simp[listTheory.EL_APPEND_EQN] >> fs[]
QED

Theorem selected_registration_terminal_locals:
  bind_arguments env args vals = SOME envb /\
  ALL_DISTINCT (MAP FST args) /\
  LIST_REL (\ty tv. evaluate_type env ty = SOME tv) (MAP SND args) tvs /\
  LENGTH vals = LENGTH args /\
  (!k. ~MEM k (MAP FST args) ==> FLOOKUP cf.ce_vars k = NONE) /\
  local_ptrs_reserved cf last /\ fn_inst_ids_distinct fn /\
  alloca_inv t /\ t.vs_alloca_next < dimword (:256) /\
  selected_registration_owners fn (MAP FST args) tvs vals (LENGTH args) cf last t H u ==>
  local_ptrs_rel fn cf [envb] t
Proof
  strip_tac >> irule registration_indexed_terminal_local_ptrs >>
  simp[] >> qexistsl [`H`,`args`,`last`,`env`,`u`,`tvs`,`vals`] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `selected_registration_owners _ _ _ _ _ _ _ _ _ _`
    (qspec_then `j` mp_tac o REWRITE_RULE [selected_registration_owners_def]) >>
  simp[EL_MAP] >> strip_tac >>
  rename1 `FLOOKUP t.vs_allocas aid = SOME (p,n)` >>
  `p+n <= t.vs_alloca_next` by
    metis_tac[venomMemDefsTheory.alloca_inv_def, venomMemDefsTheory.alloca_next_valid_def] >>
  qexistsl [`q`,`p`,`mk_inst aid ALLOCA [Lit (n2w n)] [q]`] >>
  simp[venomInstTheory.mk_inst_def] >> decide_tac
QED

(* The sole execution assumption is per-slot acceptance on the actual bytes.
   All projections concern the same terminal concrete state and ghosts. *)
Theorem selected_registration_fold:
  LENGTH args = LENGTH tvs /\ LENGTH args = LENGTH vals /\
  ALL_DISTINCT (MAP FST args) /\
  (!ce j. j < LENGTH args /\ ce = ce0 with ce_vars := ce.ce_vars ==>
    selected_slot_accepts ce env ce.ce_struct_fields (SND (EL j args)) (EL j tvs) /\
    abi_decoder_coherent ce env ce.ce_struct_fields (SND (EL j args)) (EL j tvs)) /\
  (!j. j < LENGTH args ==> type_memory_size (EL j tvs) < dimword (:256)) /\
  (!j. j < LENGTH args ==> ?loc.
    FLOOKUP ce0.ce_vars (FST (EL j args)) = SOME loc /\
    var_location_memory_size loc = SOME (type_memory_size (EL j tvs))) /\
  (!k. ~MEM k (MAP FST args) ==> FLOOKUP ce0.ce_vars k = NONE) /\
  bind_arguments env args vals = SOME envb /\
  LIST_REL (\ty tv. evaluate_type env ty = SOME tv) (MAP SND args) tvs /\
  local_ptrs_reserved cf last /\
  compile_register_positional_args ce0 (build_positional_args ce0 args) 4 st = (cf,last) /\
  fn_has_code st last fn /\ fn_inst_ids_distinct fn /\
  (!lbl bb. lookup_block lbl fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  calldata_decode_args s.vs_call_ctx.cc_calldata tvs 0 = SOME vals /\
  4+SUM (MAP tv_abi_size tvs) < dimword (:256) /\
  last.cs_next_var <= limit.cs_next_var /\ fresh_vars_wrt limit s /\
  selected_registration_resources ctx fn site lo st s /\ alloca_history fn s /\
  unit_alloca_budget ctx < dimword (:256) /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size fn s <= w2n s.vs_initial_fmp) ==>
  ?t H u.
    local_ptrs_rel fn cf [envb] t /\
    selected_registration_owners fn (MAP FST args) tvs vals (LENGTH args) cf last t H u /\
    cf = ce0 with ce_vars := cf.ce_vars /\
    selected_registration_resources ctx fn site lo last t /\
    fresh_vars_wrt limit t /\ selected_registration_frame s tn t u /\
    alloca_history fn t /\ gas_path_mem ctx fn s 0 (OK t) /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,H,u)) /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H u t) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >>
  drule_at (Pat `compile_register_positional_args _ _ _ _ = _`)
    (selected_registration_suffix |> UNDISCH |> Q.SPECL [`0`,`ce0`,`0`] |>
     SPEC_ALL |> DISCH_ALL |>
     REWRITE_RULE [listTheory.DROP_0, arithmeticTheory.ADD_0,
       arithmeticTheory.ZERO_LESS_EQ]) >>
  disch_then (drule_at (Pat `calldata_decode_args _ _ _ = _`)) >>
  disch_then (drule_at (Pat `selected_registration_resources _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `_ <= limit.cs_next_var`)) >>
  disch_then (mp_tac o Q.INST [`G` |-> `G`, `tn` |-> `tn`,
    `PG` |-> `PG`, `env` |-> `env`] o SPEC_ALL) >>
  (impl_tac >-
    (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
      simp[selected_registration_owners_def]))) >> strip_tac >>
  drule compile_register_positional_args_cenv >> strip_tac >>
  `!k. ~MEM k (MAP FST args) ==> FLOOKUP cf.ce_vars k = NONE` by
    metis_tac[entryStateRelTheory.build_positional_args_names] >>
  `alloca_inv s /\ alloca_inv t /\ alloca_frontier_inv ctx fn site t` by
    metis_tac[selected_registration_resources_def] >>
  `t.vs_alloca_next < dimword (:256)` by
    (qpat_assum `alloca_frontier_inv ctx fn site t` mp_tac >>
     rewrite_tac[alloca_frontier_inv_def] >> strip_tac >> decide_tac) >>
  `local_ptrs_rel fn cf [envb] t` by metis_tac[selected_registration_terminal_locals] >>
  `gas_path_mem ctx fn s 0 (OK t)` by metis_tac[selected_zero_path_mem] >>
  `alloca_history fn t` by
    metis_tac[gas_path_mem_zero_history, aggregate_mem_path_alloca_inv] >>
  qexistsl [`t`,`H`,`u`] >>
  ntac 9 (conj_tac >- first_assum ACCEPT_TAC) >>
  metis_tac[selected_zero_path_ptr_pullback]
QED

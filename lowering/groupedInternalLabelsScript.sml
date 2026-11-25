Theory groupedInternalLabels
Ancestors
  externalEntryShape loweringShapeRules compileUnit compileVyper vyperCompiler
  moduleLowering compileEnv emitHelper exprLowering loweringShapeDefs list
  entryInternalAppend entryCompileIntervals fragExec emitHelperProps exprLoweringProps venomInst pair
  abiDecoderCounters externalEntryChecks placeMemoryCodeLayout venomExecSemantics context
  groupedKeywordDecode groupedEntryCounters
  gasShadowState gasShadowRuntimeOps gasShadowRuntimeDispatch gasShadowModuleArgs
  gasShadowCompileBase gasShadowCompileContext
Libs monadsyntax

fun label_steps rws =
  let
    val rules = [comp_return_labels, emit_op_labels, emit_void_labels,
      emit_inst_labels, pairTheory.ELIM_UNCURRY] @ rws
    val step =
      FIRST [irule fresh_label_bind_labels,
             irule new_block_action_labels,
             irule comp_ignore_bind_labels >> conj_tac,
             irule comp_bind_labels >> conj_tac,
             FIRST_ASSUM MATCH_ACCEPT_TAC,
             disch_tac, IF_CASES_TAC, BasicProvers.TOP_CASE_TAC]
  in
    rpt gen_tac >> simp rules >> rpt (step >> rpt gen_tac >> simp rules)
  end

Theorem group_kwarg_alloca_labels[local]:
  !specs ce s.
    cs_extends s (SND (compile_create_kwarg_allocas ce specs s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_create_kwarg_allocas ce specs s)))
Proof
  Induct >> simp[compile_create_kwarg_allocas_def, comp_return_labels] >>
  qx_gen_tac `item` >> PairCases_on `item` >> once_rewrite_tac[compile_create_kwarg_allocas_def] >>
  label_steps [compile_alloc_buffer_labels]
QED

Theorem group_init_kwarg_labels[local]:
  !vars ce off k hi s.
    cs_extends s (SND (compile_init_kwargs ce vars off k hi s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_init_kwargs ce vars off k hi s)))
Proof
  Induct >> simp[compile_init_kwargs_def, comp_return_labels] >>
  qx_gen_tac `item` >> PairCases_on `item` >> once_rewrite_tac[compile_init_kwargs_def] >>
  label_steps [compile_abi_arg_ptr_guard_labels, CONJUNCT1 compile_abi_decode_labels,
    lower_value_labels, compile_expr_labels, compile_store_bytestring_labels]
QED

Theorem compile_init_kwargs_extends:
  compile_init_kwargs ce vars off k hi a = ((),b) ==> cs_extends a b
Proof
  metis_tac[group_init_kwarg_labels, SND]
QED

Theorem compile_init_kwargs_supplied_intervals:
  0 < k /\
  compile_init_kwargs ce ((name,dst,ty,default_e)::vars) off k hi sa = ((),sb) /\
  fn_has_code sa sb fn ==>
  ?src mid first last.
    compile_getelemptr_abi (Lit 4w) (is_abi_dynamic ce.ce_struct_fields ty)
      (off - 4) CALLDATALOAD (Lit 0w) (Lit 0w) sa = (src,mid) /\
    (if is_abi_dynamic ce.ce_struct_fields ty then
       compile_abi_arg_ptr_guard CALLDATALOAD src (Lit 4w) mid = ((),first)
     else first = mid) /\
    compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
      (type_to_abi_dec_info ce.ce_struct_fields ce ty) first = ((),last) /\
    compile_init_kwargs ce vars (off + abi_embedded_static_size ce.ce_struct_fields ty)
      (k - 1) hi last = ((),sb) /\
    fn_has_code sa mid fn /\ fn_has_code mid first fn /\
    fn_has_code first last fn /\ fn_has_code last sb fn
Proof
  strip_tac >> drule_all compile_init_kwargs_supplied_parts >> strip_tac >>
  `cs_extends sa mid` by metis_tac[compile_getelemptr_abi_labels, SND] >>
  `cs_extends mid first` by
    (Cases_on `is_abi_dynamic ce.ce_struct_fields ty` >> fs[cs_extends_refl] >>
     metis_tac[compile_abi_arg_ptr_guard_labels, SND]) >>
  `cs_extends first last` by metis_tac[CONJUNCT1 compile_abi_decode_labels, SND] >>
  `cs_extends last sb` by metis_tac[group_init_kwarg_labels, SND] >>
  qexistsl_tac [`src`,`mid`,`first`,`last`] >> simp[] >>
  metis_tac[fn_has_code_split, cs_extends_trans]
QED

Theorem compile_init_kwargs_omitted_intervals:
  compile_init_kwargs ce ((name,dst,ty,default_e)::vars) off 0 hi sa = ((),sb) /\
  fn_has_code sa sb fn ==>
  ?value mid last.
    lower_value compile_expr ce ty default_e sa = (value,mid) /\
    (if is_word_type ty then emit_void MSTORE [dst;value]
     else if is_bytestring_type ty then compile_store_bytestring value dst
     else emit_void MCOPY [dst;value;Lit (n2w (type_memory_bytes ce ty))]) mid = ((),last) /\
    compile_init_kwargs ce vars off 0 hi last = ((),sb) /\
    fn_has_code sa mid fn /\ fn_has_code mid last fn /\ fn_has_code last sb fn
Proof
  strip_tac >> drule compile_init_kwargs_omitted_parts >> strip_tac >>
  `cs_extends sa (SND (lower_value compile_expr ce ty default_e sa))` by
    (mp_tac (ISPEC (Term `exprLowering$compile_expr`) lower_value_labels) >>
     simp[compile_expr_labels]) >>
  `cs_extends sa mid` by
    (qpat_assum `lower_value compile_expr ce ty default_e sa = _` (fn eq =>
       qpat_assum `cs_extends sa (SND _)`
         (ACCEPT_TAC o SIMP_RULE bool_ss [eq, SND]))) >>
  `cs_extends mid last` by
    (qpat_assum `(if _ then _ else _) mid = _` mp_tac >>
     Cases_on `is_word_type ty` >> Cases_on `is_bytestring_type ty` >>
     simp[] >> metis_tac[emit_void_labels, compile_store_bytestring_labels, SND]) >>
  `cs_extends last sb` by metis_tac[group_init_kwarg_labels, SND] >>
  qexistsl_tac [`value`,`mid`,`last`] >> simp[] >>
  metis_tac[fn_has_code_split, cs_extends_trans]
QED

Theorem group_entry_kwargs_labels[local]:
  !ce vars off k lbl s.
    cs_extends s (SND (compile_entry_point_kwargs ce vars off k lbl s)) /\
    EVERY (isPREFIX "@")
      (added_labels s (SND (compile_entry_point_kwargs ce vars off k lbl s)))
Proof
  simp[compile_entry_point_kwargs_def] >> label_steps [group_init_kwarg_labels]
QED

Theorem compile_entry_point_kwargs_layout:
  compile_entry_point_kwargs ce (vars : (string # operand # type # expr) list)
    off k label sa = ((),sb) /\
  fn_has_code sa sb fn ==>
  ?mid.
    compile_init_kwargs ce vars off k (Lit 0w) sa = ((),mid) /\
    fn_has_code sa mid fn /\ fn_has_code mid sb fn /\
    emit_inst JMP [Label label] [] mid = ((),sb)
Proof
  simp[compile_entry_point_kwargs_def, comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_init_kwargs _ _ _ _ _ sa = (u,mid)` >>
  Cases_on `u` >> fs[] >>
  `cs_extends sa mid /\ cs_extends mid sb` by
    (conj_tac
     >- (mp_tac (Q.ISPECL [`vars : (string # operand # type # expr) list`,`ce : compile_env`,
              `off : num`,`k : num`,`Lit 0w : operand`,`sa : compile_state`]
            group_init_kwarg_labels) >> asm_rewrite_tac[SND] >> simp[]) >>
     qpat_assum `emit_inst JMP _ _ mid = _`
       (mp_tac o MATCH_MP emit_inst_extends) >>
     strip_tac >> simp[cs_extends_def, rich_listTheory.IS_PREFIX_APPEND]) >>
  metis_tac[fn_has_code_split]
QED

Theorem selector_chain_labels[local]:
  !sels mid s. cs_extends s (SND (compile_selector_checks mid sels s)) /\
    EVERY (isPREFIX "@") (added_labels s (SND (compile_selector_checks mid sels s)))
Proof
  Induct >> simp[compile_selector_checks_def, comp_return_labels] >>
  qx_gen_tac `item` >> PairCases_on `item` >> once_rewrite_tac[compile_selector_checks_def] >>
  label_steps []
QED

Definition group_entry_labels_ok_def:
  (group_entry_labels_ok (ExternalSingle selector package) <=>
    ~internal_label_ok (FST package)) /\
  (group_entry_labels_ok (ExternalDefaults common entries specs off) <=>
    ~internal_label_ok common.ec_common_label /\
    EVERY (\(sel,lbl,mc,k). ~internal_label_ok lbl) entries)
End

Definition group_job_label_ok_def[local]:
  (group_job_label_ok (ExternalLegacyJob package) <=> ~internal_label_ok (FST package)) /\
  (group_job_label_ok (ExternalCommonJob common vars) <=> ~internal_label_ok common.ec_common_label)
End

Theorem fresh_noninternal:
  !lbl. isPREFIX "@" lbl ==> ~internal_label_ok lbl
Proof
  Cases >> simp[internal_label_ok_def]
QED

Theorem fresh_group_label_bind[local]:
  !suffix k.
    (!lbl s. isPREFIX "@" lbl ==>
       cs_extends s (SND (k lbl s)) /\
       EVERY (\l. ~internal_label_ok l) (added_labels s (SND (k lbl s)))) ==>
    !s. cs_extends s (SND (comp_bind (fresh_label suffix) k s)) /\
       EVERY (\l. ~internal_label_ok l)
         (added_labels s (SND (comp_bind (fresh_label suffix) k s)))
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> simp[comp_bind_def] >>
  pairarg_tac >> gvs[] >>
  drule fresh_label_prefix >> strip_tac >>
  drule fresh_label_labels >>
  disch_then (qspec_then `\l. ~internal_label_ok l` strip_assume_tac) >>
  irule cs_extends_labels_trans >> qexists_tac `cs'` >> simp[] >>
  first_x_assum (qspecl_then [`a`, `cs'`] mp_tac) >>
  (impl_tac >- (Cases_on `a` >> gvs[])) >> simp[]
QED

Theorem group_entry_labels[local]:
  !entries mid common vars off.
    EVERY (\(sel,lbl,mc,k). ~internal_label_ok lbl) entries ==>
    !s. cs_extends s (SND (compile_group_entries mid entries common vars off s)) /\
      EVERY (\l. ~internal_label_ok l)
        (added_labels s (SND (compile_group_entries mid entries common vars off s)))
Proof
  Induct >> simp[compile_group_entries_def, comp_return_labels] >>
  qx_gen_tac `item` >> PairCases_on `item` >> rpt gen_tac >> strip_tac >>
  once_rewrite_tac[compile_group_entries_def] >>
  irule comp_bind_labels >> simp[emit_op_labels] >> gen_tac >> BETA_TAC >>
  irule fresh_group_label_bind >> rpt gen_tac >> disch_tac >> BETA_TAC >>
  `~internal_label_ok lbl` by metis_tac[fresh_noninternal] >>
  fs[] >>
  irule comp_ignore_bind_labels >> conj_tac
  >- simp[emit_inst_labels] >>
  irule comp_ignore_bind_labels >> conj_tac
  >- (gen_tac >> irule new_block_action_labels >> simp[]) >>
  irule comp_ignore_bind_labels >> conj_tac
  >- (gen_tac >> irule fresh_namespace_labels_mono >>
      simp[compile_entry_checks_labels, fresh_noninternal]) >>
  irule comp_ignore_bind_labels >> conj_tac
  >- (gen_tac >> irule fresh_namespace_labels_mono >>
      simp[group_entry_kwargs_labels, fresh_noninternal]) >>
  irule comp_ignore_bind_labels >> conj_tac
  >- (gen_tac >> irule new_block_action_labels >> simp[]) >>
  simp[]
QED

Theorem lower_kwarg_value_vars_mono[local]:
  abi_decoder_vars_mono (lower_value compile_expr ce ty e) /\
  abi_decoder_vars_mono (compile_store_bytestring src dst)
Proof
  rewrite_tac[abi_decoder_vars_mono_def] >> conj_tac >> gen_tac
  >- (`ci_mono st (SND (lower_value compile_expr ce ty e st))` by
        (irule ci_mono_lower_value_cfn >> simp[compile_expr_ci_mono]) >>
      gvs[ci_mono_def]) >>
  `ci_mono st (SND (compile_store_bytestring src dst st))` by
    irule ci_mono_compile_store_bytestring >>
  gvs[ci_mono_def]
QED

Theorem compile_entry_point_kwargs_vars_mono[local]:
  abi_decoder_vars_mono (compile_entry_point_kwargs ce vars off k label)
Proof
  `!vars ce off k (hi:operand). abi_decoder_vars_mono (compile_init_kwargs ce vars off k hi)` by
    (Induct >> simp[compile_init_kwargs_def, abi_decoder_vars_mono_return] >>
     qx_gen_tac `item` >> PairCases_on `item` >> simp[compile_init_kwargs_def] >> rpt gen_tac >>
     Cases_on `k > 0` >> simp[] >>
     rpt (FIRST [
       CHANGED_TAC (simp[abi_decoder_vars_mono_prims, lower_kwarg_value_vars_mono,
         abi_decoder_vars_mono_return, CONJUNCT1 abi_decoder_vars_mono_mutual,
         compile_abi_arg_ptr_guard_def]),
       (ho_match_mp_tac abi_decoder_vars_mono_bind >> conj_tac),
       (ho_match_mp_tac abi_decoder_vars_mono_ignore_bind >> conj_tac),
       gen_tac,
       (IF_CASES_TAC >> simp[])])) >>
  rewrite_tac[compile_entry_point_kwargs_def] >>
  irule abi_decoder_vars_mono_ignore_bind >> simp[abi_decoder_vars_mono_prims] >>
  first_assum MATCH_ACCEPT_TAC
QED

Theorem compile_group_entries_extends:
  compile_group_entries mid entries common vars off sa = ((),sb) /\
  EVERY (\(_,name,_,_). ~internal_label_ok name) entries ==>
  cs_extends sa sb
Proof
  metis_tac[group_entry_labels, SND]
QED

val group_entry_prefix = ``\mid sel lbl.
  do matched <- emit_op EQ [mid; Lit (n2w sel)];
     next <- fresh_label "next";
     emit_inst JNZ [matched; Label lbl; Label next] [];
     new_block lbl;
     return next
  od``;

Theorem group_entry_prefix_shadow[local]:
  gas_shadow_compiles (^group_entry_prefix mid sel lbl) (^group_entry_prefix mid sel lbl)
Proof
  BETA_TAC >> simp_tac bool_ss [comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
    >- simp[gas_shadow_compiles_emit_op_same, gas_shadow_compiles_fresh_label,
      gas_shadow_compiles_emit_inst, gas_shadow_compiles_new_block] >>
    gen_tac >> BETA_TAC) >>
  simp[gas_shadow_compiles_return]
QED

(* The grouped comparison jumps directly into the selected entry. *)
Theorem compile_group_entries_cons_layout_with_frame:
  compile_group_entries mid ((sel,lbl,mincd,k)::entries) common vars off sa =
    ((),sb) /\ fn_has_code sa sb fn /\
  EVERY (\(_,name,_,_). ~internal_label_ok name) entries ==>
  ?next st checks init done bb.
    compile_group_entries mid entries common vars off st = ((),sb) /\
    fn_has_code st sb fn /\ st.cs_current_bb = next /\ st.cs_current_insts = [] /\
    cs_extends sa checks /\ cs_extends sa st /\ cs_extends done sb /\ ci_mono done sb /\
    sa.cs_next_var < st.cs_next_var /\ sa.cs_next_var < checks.cs_next_var /\
    sa.cs_next_id <= st.cs_next_id /\ sa.cs_next_id <= checks.cs_next_id /\
    init.cs_next_var <= done.cs_next_var /\ done.cs_next_var <= st.cs_next_var /\
    lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH sa.cs_current_insts) =
      SOME (mk_inst sa.cs_next_id EQ [mid; Lit (n2w sel)]
        [STRING #"%" (toString sa.cs_next_var)]) /\
    get_instruction bb (SUC (LENGTH sa.cs_current_insts)) =
      SOME (mk_inst (sa.cs_next_id + 1) JNZ
        [Var (STRING #"%" (toString sa.cs_next_var)); Label lbl; Label next] []) /\
    ^group_entry_prefix mid sel lbl sa = (next,checks) /\
    new_block next done = (done.cs_current_bb,st) /\
    checks.cs_current_bb = lbl /\ checks.cs_current_insts = [] /\
    compile_entry_checks mincd common.ec_payable checks = ((),init) /\
    fn_has_code checks init fn /\
    compile_entry_point_kwargs common.ec_env vars off k common.ec_common_label init =
      ((),done) /\ fn_has_code init done fn
Proof
  simp[compile_group_entries_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> fs[]) >> strip_tac >>
  rename1 `emit_op EQ _ sa = (_,s1)` >>
  rename1 `fresh_label "next" s1 = (next,s2)` >>
  rename1 `emit_inst JNZ _ _ s2 = (_,s3)` >>
  rename1 `new_block lbl s3 = (_,checks)` >>
  rename1 `compile_entry_checks _ _ checks = (_,init)` >>
  rename1 `compile_entry_point_kwargs _ _ _ _ _ init = (_,done)` >>
  rename1 `new_block next done = (_,st)` >>
  `cs_extends sa s1 /\ cs_extends s1 s2 /\ cs_extends s2 s3 /\
   cs_extends s3 checks /\ cs_extends done st` by
    (rpt conj_tac >> metis_tac[cs_appends_def, cs_appends_prims,
      cs_appends_emit_helpers]) >>
  `cs_extends checks init` by
    metis_tac[compile_entry_checks_labels, SND] >>
  `cs_extends init done` by
    metis_tac[group_entry_kwargs_labels, SND] >>
  `cs_extends st sb` by
    metis_tac[group_entry_labels, SND] >>
  `fn_has_code s3 checks fn /\ fn_has_code checks init fn /\
    fn_has_code init done fn /\ fn_has_code st sb fn` by
    (rpt conj_tac >> metis_tac[fn_has_code_mid, cs_extends_trans, cs_extends_refl]) >>
  drule_all fn_has_code_new_block >> strip_tac >>
  imp_res_tac new_block_props >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac emit_op_extends >>
  imp_res_tac emit_inst_extends >> imp_res_tac fresh_label_props >>
  `s1.cs_next_var = sa.cs_next_var + 1` by
    (drule placeMemoryCodeLayoutTheory.emit_op_next_var >> simp[]) >>
  `s1.cs_next_var <= s2.cs_next_var /\ s2.cs_next_var <= s3.cs_next_var /\
   s3.cs_next_var <= checks.cs_next_var /\ done.cs_next_var <= st.cs_next_var /\
   init.cs_next_var <= done.cs_next_var` by
    (rpt conj_tac >> fs[GSYM abi_decoder_vars_mono_def,
       abi_decoder_vars_mono_prims, compile_entry_point_kwargs_vars_mono] >>
     metis_tac[abi_decoder_vars_mono_prims, compile_entry_point_kwargs_vars_mono,
       abi_decoder_vars_mono_def, SND]) >>
  `ci_mono sa s1 /\ ci_mono s1 s2 /\ ci_mono s2 s3 /\
    ci_mono s3 checks /\ ci_mono checks init /\ ci_mono init done /\ ci_mono done st` by
    (rpt conj_tac >> metis_tac[ci_mono_emit_op, ci_mono_fresh_label, ci_mono_emit_inst,
       ci_mono_new_block, compile_entry_checks_ci_mono, compile_entry_point_kwargs_ci_mono, SND]) >>
  `sa.cs_next_id <= st.cs_next_id /\ sa.cs_next_id <= checks.cs_next_id /\
    init.cs_next_var <= done.cs_next_var /\ done.cs_next_var <= st.cs_next_var` by
    fs[ci_mono_def] >>
  `cs_extends sa checks /\ cs_extends sa st /\ cs_extends done sb` by
    (rpt conj_tac >> metis_tac[cs_extends_trans]) >>
  `ci_mono done sb` by metis_tac[ci_mono_trans, compile_group_entries_ci_mono, SND] >>
  imp_res_tac compile_entry_checks_next_var >>
  `^group_entry_prefix mid sel lbl sa = (next,checks)` by
    (simp_tac bool_ss [comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
     MAP_EVERY (fn pattern => qpat_assum pattern
       (fn th => simp_tac bool_ss [th,FST,SND,pairTheory.UNCURRY,LET_THM]))
       [`emit_op EQ _ sa = _`,`fresh_label "next" s1 = _`,
        `emit_inst JNZ _ _ s2 = _`,`new_block lbl s3 = _`]) >>
  fs[same_blocks_def] >>
  qmatch_asmsub_abbrev_tac `lookup_block sa.cs_current_bb fn.fn_blocks = SOME blk` >>
  qexistsl_tac [`st`,`checks`,`init`,`done`] >>
  simp[Abbr `blk`, get_instruction_def, EL_APPEND_EQN, arithmeticTheory.ADD1,
    comp_return_def]
QED

Theorem compile_group_entries_cons_layout:
  compile_group_entries mid ((sel,lbl,mincd,k)::entries) common vars off sa =
    ((),sb) /\ fn_has_code sa sb fn /\
  EVERY (\(_,name,_,_). ~internal_label_ok name) entries ==>
  ?next st checks init done bb.
    compile_group_entries mid entries common vars off st = ((),sb) /\
    fn_has_code st sb fn /\ cs_extends done sb /\ st.cs_current_bb = next /\ st.cs_current_insts = [] /\
    sa.cs_next_var < st.cs_next_var /\ sa.cs_next_var < checks.cs_next_var /\
    sa.cs_next_id <= st.cs_next_id /\ sa.cs_next_id <= checks.cs_next_id /\
    init.cs_next_var <= done.cs_next_var /\ done.cs_next_var <= st.cs_next_var /\
    lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH sa.cs_current_insts) =
      SOME (mk_inst sa.cs_next_id EQ [mid; Lit (n2w sel)]
        [STRING #"%" (toString sa.cs_next_var)]) /\
    get_instruction bb (SUC (LENGTH sa.cs_current_insts)) =
      SOME (mk_inst (sa.cs_next_id + 1) JNZ
        [Var (STRING #"%" (toString sa.cs_next_var)); Label lbl; Label next] []) /\
    checks.cs_current_bb = lbl /\ checks.cs_current_insts = [] /\
    compile_entry_checks mincd common.ec_payable checks = ((),init) /\
    fn_has_code checks init fn /\
    compile_entry_point_kwargs common.ec_env vars off k common.ec_common_label init =
      ((),done) /\ fn_has_code init done fn
Proof
  strip_tac >> drule_all compile_group_entries_cons_layout_with_frame >>
  disch_then (qx_choosel_then [`next`,`st`,`checks`,`init`,`done`,`bb`] strip_assume_tac) >>
  qexistsl_tac [`next`,`st`,`checks`,`init`,`done`,`bb`] >> asm_rewrite_tac[]
QED

(* The selector and entry checks are shared. Only the initializer
   expressions change in the shadow compiler. *)
Theorem compile_group_entry_shadow_states:
  ^group_entry_prefix mid sel lbl sa = (next,checks) /\
  ^group_entry_prefix mid sel lbl sha = (shnext,shchecks) /\
  compile_entry_checks mincd common.ec_payable checks = ((),init) /\
  compile_entry_checks mincd common.ec_payable shchecks = ((),shinit) /\
  compile_entry_point_kwargs common.ec_env vars off k common.ec_common_label init = ((),done) /\
  compile_entry_point_kwargs (gas_shadow_env T common.ec_env)
    (MAP (\(n,p,ty,e). (n,p,ty,gas_shadow_expr e)) vars) off k common.ec_common_label shinit =
    ((),shdone) /\
  new_block next done = (done.cs_current_bb,st) /\
  new_block shnext shdone = (shdone.cs_current_bb,shst) /\
  gas_shadow_state sa sha ==>
  shnext = next /\ gas_shadow_state init shinit /\
  gas_shadow_state done shdone /\ gas_shadow_state st shst
Proof
  disch_then (map_every (assume_tac o BETA_RULE) o CONJUNCTS) >>
  `next = shnext /\ gas_shadow_state checks shchecks` by
    (mp_tac (Q.INST [`mid` |-> `mid`,`sel` |-> `sel`,`lbl` |-> `lbl`]
        (SPEC_ALL group_entry_prefix_shadow)) >>
     simp_tac bool_ss [gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`,`sha`] mp_tac) >>
     asm_rewrite_tac[FST,SND]) >>
  `gas_shadow_state init shinit` by
    (mp_tac (Q.INST [`min_cds` |-> `mincd`,`payable` |-> `common.ec_payable`]
       (SPEC_ALL gas_shadow_compiles_compile_entry_checks)) >>
     simp_tac bool_ss [gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`checks`,`shchecks`] mp_tac) >>
     asm_rewrite_tac[FST,SND]) >>
  `gas_shadow_state done shdone` by
    (`gas_shadow_compiles
        (compile_entry_point_kwargs common.ec_env vars off k common.ec_common_label)
        (compile_entry_point_kwargs (gas_shadow_env T common.ec_env)
          (MAP (\(n,p,ty,e). (n,p,ty,gas_shadow_expr e)) vars)
          off k common.ec_common_label)` by
       irule gas_shadow_compiles_entry_point_kwargs >>
     pop_assum mp_tac >> simp_tac bool_ss [gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`init`,`shinit`] mp_tac) >>
     asm_rewrite_tac[FST,SND]) >>
  qpat_x_assum `next = shnext` SUBST_ALL_TAC >>
  asm_rewrite_tac[] >>
  qspec_then `shnext` mp_tac (GEN_ALL gas_shadow_compiles_new_block) >>
  simp_tac bool_ss [gas_shadow_compiles_def] >>
  disch_then (qspecl_then [`done`,`shdone`] mp_tac) >>
  asm_rewrite_tac[FST,SND] >>
  simp[]
QED

Theorem compile_group_entry_shadow_layout:
  ^group_entry_prefix mid sel lbl sa = (next,checks) /\
  compile_entry_checks mincd common.ec_payable checks = ((),init) /\
  compile_entry_point_kwargs common.ec_env vars off k common.ec_common_label init = ((),done) /\
  new_block next done = (done.cs_current_bb,st) /\
  gas_shadow_state sa sha /\
  compile_group_entries mid ((sel,lbl,mincd,k)::entries)
    (common with <| ec_env := gas_shadow_env T common.ec_env;
                   ec_body := MAP gas_shadow_stmt common.ec_body |>)
    (MAP (\(n,p,ty,e). (n,p,ty,gas_shadow_expr e)) vars) off sha = ((),shb) /\
  fn_has_code sha shb shfn /\
  EVERY (\(_,name,_,_). ~internal_label_ok name) entries ==>
  ?shst shinit shdone.
    compile_group_entries mid entries
      (common with <| ec_env := gas_shadow_env T common.ec_env;
                   ec_body := MAP gas_shadow_stmt common.ec_body |>)
      (MAP (\(n,p,ty,e). (n,p,ty,gas_shadow_expr e)) vars) off shst = ((),shb) /\
    fn_has_code shst shb shfn /\ gas_shadow_state st shst /\
    compile_entry_point_kwargs (gas_shadow_env T common.ec_env)
      (MAP (\(n,p,ty,e). (n,p,ty,gas_shadow_expr e)) vars)
      off k common.ec_common_label shinit = ((),shdone) /\
    fn_has_code shinit shdone shfn /\ gas_shadow_state init shinit
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all compile_group_entries_cons_layout_with_frame >>
  disch_then (qx_choosel_then [`shnext`,`shst`,`shchecks`,`shinit`,`shdone`,`shbb`]
    strip_assume_tac) >>
  fs[external_common_accfupds, combinTheory.K_THM] >>
  RULE_ASSUM_TAC BETA_RULE >>
  drule_all (BETA_RULE compile_group_entry_shadow_states) >> strip_tac >>
  qexistsl_tac [`shst`,`shinit`,`shdone`] >>
  asm_rewrite_tac[]
QED

Theorem common_job_labels[local]:
  !ce args vars nr key trans view body rt s.
    cs_extends s (SND (compile_common_function_body ce args vars nr key trans view body rt s)) /\
    EVERY (isPREFIX "@")
      (added_labels s (SND (compile_common_function_body ce args vars nr key trans view body rt s)))
Proof
  simp[compile_common_function_body_def] >>
  label_steps [compile_register_positional_args_labels, compile_guarded_body_labels]
QED

Theorem group_jobs_labels[local]:
  !jobs. EVERY group_job_label_ok jobs ==>
    !s. cs_extends s (SND (compile_external_jobs jobs s)) /\
      EVERY (\l. ~internal_label_ok l) (added_labels s (SND (compile_external_jobs jobs s)))
Proof
  Induct >> simp[compile_external_jobs_def, comp_return_labels] >>
  qx_gen_tac `job` >> Cases_on `job` >>
  simp[group_job_label_ok_def, compile_external_jobs_def] >>
  rpt gen_tac >> strip_tac >> irule comp_ignore_bind_labels >> simp[]
  >- (gen_tac >> irule compile_external_fn_bodies_labels >> simp[fresh_noninternal]) >>
  conj_tac
  >- (gen_tac >> irule new_block_action_labels >> simp[]) >>
  irule comp_ignore_bind_labels >> simp[] >>
  gen_tac >> irule fresh_namespace_labels_mono >>
  simp[common_job_labels, fresh_noninternal]
QED

Theorem compile_external_jobs_append:
  !left right s.
    compile_external_jobs (left ++ right) s =
      compile_external_jobs right (SND (compile_external_jobs left s))
Proof
  Induct >- simp[compile_external_jobs_def, comp_return_def] >>
  Cases_on `h` >> simp[compile_external_jobs_def,
    comp_ignore_bind_def, comp_bind_def] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[])
QED

Theorem compile_external_legacy_job_interval:
  compile_external_jobs jobs sa = ((),sb) /\
  EVERY group_job_label_ok jobs /\ MEM (ExternalLegacyJob pkg) jobs /\
  fn_has_code sa sb fn ==>
  ?start finish pre post.
    jobs = pre ++ ExternalLegacyJob pkg::post /\
    compile_external_jobs pre sa = ((),start) /\
    compile_external_fn_bodies [pkg] start = ((),finish) /\
    cs_extends sa start /\ cs_extends start finish /\ cs_extends finish sb /\
    fn_has_code start finish fn
Proof
  strip_tac >>
  qpat_x_assum `MEM (ExternalLegacyJob pkg) jobs`
    (qx_choosel_then [`pre`,`post`] SUBST_ALL_TAC o REWRITE_RULE [MEM_SPLIT]) >>
  Cases_on `compile_external_jobs pre sa` >>
  rename1 `compile_external_jobs pre sa = (u,start)` >> Cases_on `u` >>
  qpat_x_assum `compile_external_jobs (_ ++ _) _ = _` mp_tac >>
  simp[compile_external_jobs_append, compile_external_jobs_def,
       comp_ignore_bind_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  qexistsl_tac [`start`,`cs'`,`pre`,`post`] >> simp[] >>
  `cs_extends sa start /\ cs_extends cs' sb` by metis_tac[group_jobs_labels, SND] >>
  `cs_extends start cs'` by
    metis_tac[cs_appends_external_fn_bodies, cs_appends_def] >>
  metis_tac[fn_has_code_mid]
QED

Theorem compile_external_common_job_interval:
  compile_external_jobs (pre ++ ExternalCommonJob common kwvars::post) sa = ((),sb) /\
  EVERY group_job_label_ok (pre ++ ExternalCommonJob common kwvars::post) ==>
  ?start entry cenv registered done.
    compile_external_jobs pre sa = ((),start) /\
    new_block common.ec_common_label start = (start.cs_current_bb,entry) /\
    compile_register_positional_args
      (compile_register_kwarg_vars common.ec_env kwvars) common.ec_pos_args 4 entry =
      (cenv,registered) /\
    compile_guarded_body cenv common.ec_nonreentrant common.ec_nkey
      common.ec_transient common.ec_view common.ec_body common.ec_return registered =
      ((),done) /\
    compile_external_jobs post done = ((),sb) /\
    cs_extends sa start /\ cs_extends start entry /\ cs_extends entry registered /\
    cs_extends registered done /\ cs_extends done sb
Proof
  strip_tac >>
  Cases_on `compile_external_jobs pre sa` >>
  rename1 `compile_external_jobs pre sa = (u,start)` >> Cases_on `u` >>
  qpat_x_assum `compile_external_jobs (_ ++ _) _ = _` mp_tac >>
  simp[compile_external_jobs_append, compile_external_jobs_def,
       compile_common_function_body_def, comp_ignore_bind_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  fs[EVERY_APPEND] >>
  conj_tac >- fs[new_block_def] >>
  rpt conj_tac
  >- metis_tac[group_jobs_labels, SND]
  >- metis_tac[cs_extends_new_block]
  >- metis_tac[compile_register_positional_args_labels, SND]
  >- metis_tac[compile_guarded_body_labels, SND] >>
  metis_tac[group_jobs_labels, SND]
QED

Theorem external_groups_labels[local]:
  !groups mid. EVERY group_entry_labels_ok groups ==>
    !s. cs_extends s (SND (compile_external_groups mid groups s)) /\
      EVERY (\l. ~internal_label_ok l) (added_labels s (SND (compile_external_groups mid groups s)))
Proof
  Induct >> simp[compile_external_groups_def, comp_return_labels] >>
  qx_gen_tac `group` >> Cases_on `group`
  >- (PairCases_on `p` >>
      simp[compile_external_groups_def, group_entry_labels_ok_def] >>
      rpt gen_tac >> strip_tac >> irule comp_ignore_bind_labels >> conj_tac
      >- (gen_tac >> irule fresh_namespace_labels_mono >>
          simp[selector_chain_labels, fresh_noninternal]) >>
      irule comp_bind_labels >> simp[comp_return_labels]) >>
  simp[compile_external_groups_def, group_entry_labels_ok_def] >>
  rpt gen_tac >> strip_tac >> irule comp_bind_labels >> reverse conj_tac
  >- (gen_tac >> irule fresh_namespace_labels_mono >>
      simp[group_kwarg_alloca_labels, fresh_noninternal]) >>
  gen_tac >> BETA_TAC >> irule comp_ignore_bind_labels >>
  simp[group_entry_labels] >> irule comp_bind_labels >> simp[comp_return_labels]
QED

Theorem compile_external_groups_extends:
  compile_external_groups mid groups sa = (jobs,sb) /\
  EVERY group_entry_labels_ok groups ==> cs_extends sa sb
Proof
  strip_tac >> drule external_groups_labels >>
  disch_then (qspecl_then [`mid`,`sa`] mp_tac) >> simp[]
QED

Theorem compile_external_groups_append:
  !pre post mid sa jobs sb.
    compile_external_groups mid (pre ++ post) sa = (jobs,sb) ==>
    ?left right cut.
      compile_external_groups mid pre sa = (left,cut) /\
      compile_external_groups mid post cut = (right,sb) /\ jobs = left ++ right
Proof
  Induct >- (simp[compile_external_groups_def, comp_return_def] >> metis_tac[]) >>
  Cases_on `h` >> TRY (PairCases_on `p`) >>
  simp[compile_external_groups_def, comp_return_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt gen_tac >> rpt (pairarg_tac >> fs[]) >> strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem external_groups_jobs[local]:
  !groups mid s. EVERY group_entry_labels_ok groups ==>
    EVERY group_job_label_ok (FST (compile_external_groups mid groups s))
Proof
  Induct >> simp[compile_external_groups_def, comp_return_def] >>
  qx_gen_tac `group` >> Cases_on `group`
  >- (PairCases_on `p` >>
      simp[compile_external_groups_def, group_entry_labels_ok_def,
           comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
      rpt gen_tac >> strip_tac >>
      rpt (pairarg_tac >> gvs[]) >> simp[group_job_label_ok_def] >>
      metis_tac[pairTheory.FST]) >>
  simp[compile_external_groups_def, group_entry_labels_ok_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt gen_tac >> strip_tac >>
  rpt (pairarg_tac >> gvs[]) >> simp[group_job_label_ok_def] >>
  metis_tac[pairTheory.FST]
QED

Theorem compile_external_defaults_cons_layout:
  compile_external_groups mid (ExternalDefaults common entries specs off::groups)
    sa = (jobs,sb) /\
  fn_has_code sa sb fn /\
  EVERY group_entry_labels_ok (ExternalDefaults common entries specs off::groups) ==>
  ?vars sc sd rest.
    compile_create_kwarg_allocas common.ec_env specs sa = (vars,sc) /\
    fn_has_code sa sc fn /\
    compile_group_entries mid entries common vars off sc = ((),sd) /\
    fn_has_code sc sd fn /\
    compile_external_groups mid groups sd = (rest,sb) /\
    fn_has_code sd sb fn /\
    jobs = ExternalCommonJob common vars::rest
Proof
  simp[compile_external_groups_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, group_entry_labels_ok_def] >>
  rpt (pairarg_tac >> fs[]) >> strip_tac >> gvs[] >>
  rename1 `compile_create_kwarg_allocas common.ec_env specs sa = (vars,sc)` >>
  rename1 `compile_group_entries mid entries common vars off sc = ((),sd)` >>
  rename1 `compile_external_groups mid groups sd = (rest,sb)` >>
  `cs_extends sa sc /\ cs_extends sc sd /\ cs_extends sd sb` by
    (rpt conj_tac >> metis_tac[group_kwarg_alloca_labels, group_entry_labels,
                            external_groups_labels, SND]) >>
  metis_tac[fn_has_code_split, cs_extends_trans]
QED

Theorem compile_external_single_cons_layout:
  compile_external_groups mid (ExternalSingle (sel,lbl,tz) pkg::groups) sa = (jobs,sb) /\
  fn_has_code sa sb fn /\ EVERY group_entry_labels_ok groups ==>
  ?sc rest.
    compile_selector_checks mid [(sel,lbl)] sa = ((),sc) /\
    fn_has_code sa sc fn /\
    compile_external_groups mid groups sc = (rest,sb) /\
    fn_has_code sc sb fn /\
    jobs = ExternalLegacyJob pkg::rest
Proof
  simp[compile_external_groups_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> fs[]) >> strip_tac >> gvs[] >>
  rename1 `compile_selector_checks mid [(sel,lbl)] sa = ((),sc)` >>
  rename1 `compile_external_groups mid groups sc = (rest,sb)` >>
  `cs_extends sa sc /\ cs_extends sc sb` by
    (rpt conj_tac >> metis_tac[selector_chain_labels, external_groups_labels, SND]) >>
  metis_tac[fn_has_code_split]
QED

Theorem compile_group_dispatch_linear_layout_with_frame:
  compile_group_dispatch_linear groups fallback st = (jobs,st') /\
  fn_has_code st st' fn /\ EVERY group_entry_labels_ok groups ==>
  ?d q r b0 bd br.
    compile_external_groups (Var (STRING #"%" (toString (st.cs_next_var + 4))))
      groups q = (jobs,r) /\ fn_has_code q r fn /\ ci_mono r st' /\ cs_extends r st' /\
    q.cs_current_bb = d /\ LENGTH q.cs_current_insts = 2 /\
    q.cs_next_var = st.cs_next_var + 5 /\
    lookup_block st.cs_current_bb fn.fn_blocks = SOME b0 /\
    get_instruction b0 (LENGTH st.cs_current_insts) =
      SOME (mk_inst st.cs_next_id CALLDATASIZE []
        [STRING #"%" (toString st.cs_next_var)]) /\
    get_instruction b0 (SUC (LENGTH st.cs_current_insts)) =
      SOME (mk_inst (st.cs_next_id + 1) LT
        [Var (STRING #"%" (toString st.cs_next_var)); Lit 4w]
        [STRING #"%" (toString (st.cs_next_var + 1))]) /\
    get_instruction b0 (SUC (SUC (LENGTH st.cs_current_insts))) =
      SOME (mk_inst (st.cs_next_id + 2) ISZERO
        [Var (STRING #"%" (toString (st.cs_next_var + 1)))]
        [STRING #"%" (toString (st.cs_next_var + 2))]) /\
    get_instruction b0 (SUC (SUC (SUC (LENGTH st.cs_current_insts)))) =
      SOME (mk_inst (st.cs_next_id + 3) JNZ
        [Var (STRING #"%" (toString (st.cs_next_var + 2))); Label d; Label fallback] []) /\
    lookup_block d fn.fn_blocks = SOME bd /\
    get_instruction bd 0 = SOME (mk_inst (st.cs_next_id + 4) CALLDATALOAD
      [Lit 0w] [STRING #"%" (toString (st.cs_next_var + 3))]) /\
    get_instruction bd 1 = SOME (mk_inst (st.cs_next_id + 5) SHR
      [Lit 224w; Var (STRING #"%" (toString (st.cs_next_var + 3)))]
      [STRING #"%" (toString (st.cs_next_var + 4))]) /\
    phi_prefix_length bd.bb_instructions = 0 /\
    lookup_block r.cs_current_bb fn.fn_blocks = SOME br /\
    get_instruction br (LENGTH r.cs_current_insts) =
      SOME (mk_inst r.cs_next_id JMP [Label fallback] []) /\
    (r.cs_current_insts = [] ==> phi_prefix_length br.bb_instructions = 0) /\
    (!other other_jobs other_end other_fn.
      compile_group_dispatch_linear other fallback st = (other_jobs,other_end) /\
      fn_has_code st other_end other_fn /\ EVERY group_entry_labels_ok other ==>
      ?rr. compile_external_groups (Var (STRING #"%" (toString (st.cs_next_var + 4))))
          other q = (other_jobs,rr) /\ fn_has_code q rr other_fn)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `compile_group_dispatch_linear groups fallback st = _` mp_tac >>
  simp[compile_group_dispatch_linear_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> fs[]) >> strip_tac >> gvs[] >>
  rename1 `emit_inst JMP _ _ a9 = (_, st')` >>
  `ci_mono a9 st'` by metis_tac[ci_mono_emit_inst, SND] >>
  rename1 `compile_external_groups _ _ a8 = (_, a9)` >>
  rename1 `emit_op SHR _ a7 = (_, a8)` >>
  rename1 `emit_op CALLDATALOAD _ a6 = (_, a7)` >>
  rename1 `new_block dispatch_lbl a5 = (_, a6)` >>
  rename1 `emit_inst JNZ _ _ a4 = (_, a5)` >>
  rename1 `fresh_label "dispatch" a3 = (_, a4)` >>
  rename1 `emit_op ISZERO _ a2 = (_, a3)` >>
  rename1 `emit_op LT _ a1 = (_, a2)` >>
  rename1 `emit_op CALLDATASIZE _ st = (_, a1)` >>
  `cs_extends st a1 /\ cs_extends a1 a2 /\ cs_extends a2 a3 /\
   cs_extends a3 a4 /\ cs_extends a4 a5 /\ cs_extends a5 a6 /\
   cs_extends a6 a7 /\ cs_extends a7 a8 /\ cs_extends a8 a9 /\
   cs_extends a9 st'` by
    (rpt conj_tac >> metis_tac[cs_appends_def, cs_appends_emit_helpers,
      cs_appends_prims, external_groups_labels, SND]) >>
  `fn_has_code a5 a6 fn /\ fn_has_code a6 a8 fn /\
   fn_has_code a8 a9 fn /\ fn_has_code a9 st' fn` by
    (rpt conj_tac >> metis_tac[fn_has_code_mid, fn_has_code_split,
                             cs_extends_trans]) >>
  `lookup_block a5.cs_current_bb fn.fn_blocks =
   SOME <|bb_label := a5.cs_current_bb;
          bb_instructions := a5.cs_current_insts|>` by
    metis_tac[fn_has_code_new_block] >>
  imp_res_tac new_block_props >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac emit_op_extends >>
  imp_res_tac emit_inst_extends >> imp_res_tac fresh_label_props >>
  fs[same_blocks_def] >>
  `?bd. lookup_block dispatch_lbl fn.fn_blocks = SOME bd /\
     get_instruction bd 0 = SOME (mk_inst (st.cs_next_id + 4) CALLDATALOAD
       [Lit 0w] [STRING #"%" (toString (st.cs_next_var + 3))]) /\
     get_instruction bd 1 = SOME (mk_inst (st.cs_next_id + 5) SHR
       [Lit 224w; Var (STRING #"%" (toString (st.cs_next_var + 3)))]
       [STRING #"%" (toString (st.cs_next_var + 4))])` by
    (qspecl_then [`a6`, `a8`, `fn`,
       `emitted_insts a6 a7 ++ emitted_insts a7 a8`]
       mp_tac fn_has_code_same_block >>
     (impl_tac >- fs[]) >> strip_tac >>
     rename1 `lookup_block a6.cs_current_bb fn.fn_blocks = SOME bd` >>
     first_assum (qspec_then `0` mp_tac) >>
     first_x_assum (qspec_then `1` mp_tac) >>
     simp[] >> rpt strip_tac >> qexists_tac `bd` >> gvs[]) >>
  `?br. lookup_block a9.cs_current_bb fn.fn_blocks = SOME br /\
     get_instruction br (LENGTH a9.cs_current_insts) =
       SOME (mk_inst a9.cs_next_id JMP [Label fallback] [])` by
    (qspecl_then [`a9`, `st'`, `fn`,
       `[mk_inst a9.cs_next_id JMP [Label fallback] []]`]
       mp_tac fn_has_code_same_block >>
     (impl_tac >- fs[]) >> strip_tac >>
     first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  qmatch_asmsub_abbrev_tac
    `lookup_block st.cs_current_bb fn.fn_blocks = SOME blk` >>
  `phi_prefix_length bd.bb_instructions = 0` by
    (qpat_x_assum `get_instruction bd 0 = _` mp_tac >>
     Cases_on `bd.bb_instructions` >>
     simp[get_instruction_def, phi_prefix_length_def, mk_inst_def] >>
     strip_tac >> gvs[phi_prefix_length_def, mk_inst_def]) >>
  `a9.cs_current_insts = [] ==> phi_prefix_length br.bb_instructions = 0` by
    (strip_tac >> qpat_x_assum `get_instruction br _ = _` mp_tac >>
     Cases_on `br.bb_instructions` >>
     simp[get_instruction_def, phi_prefix_length_def, mk_inst_def] >>
     strip_tac >> gvs[phi_prefix_length_def, mk_inst_def]) >>
  qexistsl_tac [`a8`, `a9`] >>
  gvs[Abbr `blk`, get_instruction_def, EL_APPEND_EQN,
       arithmeticTheory.ADD1] >>
  rpt gen_tac >>
  simp_tac bool_ss [compile_group_dispatch_linear_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def] >>
  asm_simp_tac bool_ss [pairTheory.UNCURRY] >>
  Cases_on `compile_external_groups (Var (STRING #"%" (toString (st.cs_next_var + 4))))
    other a8` >>
  fs[comp_bind_def] >>
  rpt strip_tac >>
  `cs_extends a8 r` by metis_tac[external_groups_labels, SND] >>
  `cs_extends r other_end` by
    (qpat_assum `SND (emit_inst JMP _ [] r) = other_end` (SUBST1_TAC o SYM) >>
     metis_tac[ci_mono_emit_inst, ci_mono_def]) >>
  `cs_extends st a8` by metis_tac[cs_extends_trans] >>
  metis_tac[fn_has_code_mid]
QED

Theorem compile_group_dispatch_linear_layout:
  compile_group_dispatch_linear groups fallback st = (jobs,st') /\
  fn_has_code st st' fn /\ EVERY group_entry_labels_ok groups ==>
  ?d q r b0 bd br.
    compile_external_groups (Var (STRING #"%" (toString (st.cs_next_var + 4))))
      groups q = (jobs,r) /\ fn_has_code q r fn /\ cs_extends r st' /\
    r.cs_next_var <= st'.cs_next_var /\
    q.cs_current_bb = d /\ LENGTH q.cs_current_insts = 2 /\
    q.cs_next_var = st.cs_next_var + 5 /\
    lookup_block st.cs_current_bb fn.fn_blocks = SOME b0 /\
    get_instruction b0 (LENGTH st.cs_current_insts) =
      SOME (mk_inst st.cs_next_id CALLDATASIZE []
        [STRING #"%" (toString st.cs_next_var)]) /\
    get_instruction b0 (SUC (LENGTH st.cs_current_insts)) =
      SOME (mk_inst (st.cs_next_id + 1) LT
        [Var (STRING #"%" (toString st.cs_next_var)); Lit 4w]
        [STRING #"%" (toString (st.cs_next_var + 1))]) /\
    get_instruction b0 (SUC (SUC (LENGTH st.cs_current_insts))) =
      SOME (mk_inst (st.cs_next_id + 2) ISZERO
        [Var (STRING #"%" (toString (st.cs_next_var + 1)))]
        [STRING #"%" (toString (st.cs_next_var + 2))]) /\
    get_instruction b0 (SUC (SUC (SUC (LENGTH st.cs_current_insts)))) =
      SOME (mk_inst (st.cs_next_id + 3) JNZ
        [Var (STRING #"%" (toString (st.cs_next_var + 2))); Label d; Label fallback] []) /\
    lookup_block d fn.fn_blocks = SOME bd /\
    get_instruction bd 0 = SOME (mk_inst (st.cs_next_id + 4) CALLDATALOAD
      [Lit 0w] [STRING #"%" (toString (st.cs_next_var + 3))]) /\
    get_instruction bd 1 = SOME (mk_inst (st.cs_next_id + 5) SHR
      [Lit 224w; Var (STRING #"%" (toString (st.cs_next_var + 3)))]
      [STRING #"%" (toString (st.cs_next_var + 4))]) /\
    phi_prefix_length bd.bb_instructions = 0 /\
    lookup_block r.cs_current_bb fn.fn_blocks = SOME br /\
    get_instruction br (LENGTH r.cs_current_insts) =
      SOME (mk_inst r.cs_next_id JMP [Label fallback] []) /\
    (r.cs_current_insts = [] ==> phi_prefix_length br.bb_instructions = 0)
Proof
  strip_tac >> drule_all compile_group_dispatch_linear_layout_with_frame >>
  disch_then (qx_choosel_then [`d`,`q`,`r`,`b0`,`bd`,`br`] strip_assume_tac) >>
  qexistsl_tac [`d`,`q`,`r`,`b0`,`bd`,`br`] >> asm_rewrite_tac[] >> fs[ci_mono_def]
QED

Theorem group_dispatch_labels[local]:
  !groups fb. EVERY group_entry_labels_ok groups ==>
    !s. cs_extends s (SND (compile_group_dispatch_linear groups fb s)) /\
      EVERY (\l. ~internal_label_ok l)
        (added_labels s (SND (compile_group_dispatch_linear groups fb s)))
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac[compile_group_dispatch_linear_def] >>
  ntac 3 (irule comp_bind_labels >> simp[emit_op_labels] >> gen_tac >> BETA_TAC) >>
  irule fresh_group_label_bind >> rpt gen_tac >> disch_tac >> BETA_TAC >>
  irule comp_ignore_bind_labels >> conj_tac
  >- simp[emit_inst_labels] >>
  irule comp_ignore_bind_labels >> conj_tac
  >- (gen_tac >> irule new_block_action_labels >> simp[fresh_noninternal]) >>
  ntac 2 (irule comp_bind_labels >> simp[emit_op_labels] >> gen_tac >> BETA_TAC) >>
  irule comp_bind_labels >> simp[external_groups_labels] >>
  gen_tac >> BETA_TAC >> irule comp_ignore_bind_labels >>
  simp[emit_inst_labels, comp_return_labels]
QED

Theorem group_dispatch_job_labels[local]:
  !groups fb s. EVERY group_entry_labels_ok groups ==>
    EVERY group_job_label_ok (FST (compile_group_dispatch_linear groups fb s))
Proof
  rpt gen_tac >> strip_tac >>
  simp[compile_group_dispatch_linear_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  drule external_groups_jobs >> metis_tac[pairTheory.FST]
QED

Theorem compile_grouped_runtime_entry_layout:
  EVERY group_entry_labels_ok groups /\
  compile_generate_grouped_runtime groups [] fallback sa = ((),se) ==>
  ?fl sf jobs sd sx sn.
    fresh_label "fallback" sa = (fl,sf) /\
    compile_group_dispatch_linear groups fl sf = (jobs,sd) /\
    compile_external_jobs jobs sd = ((),sx) /\
    new_block fl sx = (sx.cs_current_bb,sn) /\
    (case fallback of
       NONE => emit_inst REVERT [Lit 0w; Lit 0w] []
     | SOME (ce,pay,nr,key,tr,view,stmts,rt) =>
         compile_fallback_body ce pay nr key tr view stmts rt) sn = ((),se) /\
    EVERY group_job_label_ok jobs /\
    cs_extends sf sd /\ cs_extends sd sx /\ cs_extends sx se
Proof
  strip_tac >>
  qpat_x_assum `compile_generate_grouped_runtime _ _ _ _ = _` mp_tac >>
  simp[compile_generate_grouped_runtime_def, compile_internal_fn_bodies_def,
       comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  rename1 `fresh_label "fallback" sa = (fl,sf)` >>
  rename1 `compile_group_dispatch_linear groups fl sf = (jobs,sd)` >>
  rename1 `compile_external_jobs jobs sd = ((),sx)` >>
  rename1 `new_block fl sx = (_,sn)` >>
  drule group_dispatch_job_labels >>
  disch_then (qspecl_then [`fl`,`sf`] mp_tac) >> simp[] >> strip_tac >>
  drule group_dispatch_labels >>
  disch_then (qspecl_then [`fl`,`sf`] mp_tac) >> simp[] >> strip_tac >>
  drule group_jobs_labels >> disch_then (qspec_then `sd` mp_tac) >>
  simp[] >> strip_tac >>
  conj_tac >- fs[new_block_def] >>
  mp_tac (Q.INST [`lbl` |-> `fl`, `fb` |-> `fallback`]
    (SPEC_ALL cs_appends_runtime_fallback_suffix)) >>
  simp_tac bool_ss [cs_appends_def] >>
  disch_then (qspecl_then [`sx`,`()`,`se`] irule) >>
  fs[comp_ignore_bind_def, comp_bind_def]
QED

Theorem grouped_prefix_labels[local]:
  !groups fallback. EVERY group_entry_labels_ok groups ==>
    !s. cs_extends s (SND (compile_generate_grouped_runtime groups [] fallback s)) /\
      EVERY (\l. ~internal_label_ok l)
        (added_labels s (SND (compile_generate_grouped_runtime groups [] fallback s)))
Proof
  rpt gen_tac >> strip_tac >>
  simp[compile_generate_grouped_runtime_def, compile_internal_fn_bodies_def,
       comp_ignore_bind_def, comp_bind_assoc] >>
  irule fresh_group_label_bind >> qx_genl_tac [`lbl`, `s`] >>
  disch_tac >> BETA_TAC >>
  Cases_on `compile_group_dispatch_linear groups lbl s` >>
  rename1 `compile_group_dispatch_linear groups lbl s = (jobs,st)` >>
  drule group_dispatch_job_labels >>
  disch_then (qspecl_then [`lbl`, `s`] mp_tac) >> simp[] >> strip_tac >>
  drule group_dispatch_labels >>
  disch_then (qspecl_then [`lbl`, `s`] mp_tac) >> simp[] >> strip_tac >>
  irule cs_extends_labels_trans >> qexists_tac `st` >> simp[] >>
  once_rewrite_tac[comp_bind_def] >> asm_rewrite_tac[] >> BETA_TAC >>
  simp[GSYM comp_ignore_bind_def, CONJ_COMM] >>
  irule comp_ignore_bind_labels >> conj_tac
  >- simp[group_jobs_labels] >>
  irule comp_ignore_bind_labels >> conj_tac
  >- (gen_tac >> irule new_block_action_labels >> simp[fresh_noninternal]) >>
  irule comp_ignore_bind_labels >> conj_tac
  >- (Cases_on `fallback` >- simp[emit_inst_labels] >>
      PairCases_on `x` >> simp[] >> gen_tac >>
      irule fresh_namespace_labels_mono >>
      simp[compile_fallback_body_labels, fresh_noninternal]) >>
  irule comp_ignore_bind_labels >> simp[comp_return_labels]
QED

Theorem package_external_group_unit_labels:
  !mods target trans nkeys f.
    group_entry_labels_ok (package_external_group_unit mods target trans nkeys f)
Proof
  rpt gen_tac >> PairCases_on `f` >>
  simp[package_external_group_unit_def, package_external_fn_unit_def,
       set_external_package_target_def, group_entry_labels_ok_def] >>
  CASE_TAC >> Cases_on `NULL f6` >>
  simp[group_entry_labels_ok_def, external_common_label_def,
       external_prefix_label_def, internal_label_ok_def, EVERY_MAP,
       pairTheory.FORALL_PROD, compute_selector_def] >>
  simp[EVERY_MEM] >> qx_gen_tac `prefix` >> PairCases_on `prefix` >> simp[]
QED

Theorem package_external_group_labels:
  !tops target trans nkeys f.
    group_entry_labels_ok (package_external_group tops target trans nkeys f)
Proof
  metis_tac[package_external_group_unit_labels, package_external_group_unit_singleton]
QED

Theorem compile_grouped_internal_suffix[local]:
  compile_generate_grouped_runtime groups ips fb st =
  compile_internal_fn_bodies ips
    (SND (compile_generate_grouped_runtime groups [] fb st))
Proof
  simp[compile_generate_grouped_runtime_def, LET_THM, compile_internal_fn_bodies_def,
       comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem compile_grouped_runtime_extends:
  EVERY group_entry_labels_ok groups /\
  compile_generate_grouped_runtime groups ips fb start = ((),final) ==>
  cs_extends start final
Proof
  strip_tac >>
  drule grouped_prefix_labels >>
  disch_then (qspecl_then [`fb`, `start`] strip_assume_tac) >>
  qpat_x_assum `compile_generate_grouped_runtime _ _ _ _ = _`
    (assume_tac o ONCE_REWRITE_RULE [compile_grouped_internal_suffix]) >>
  metis_tac[cs_appends_internal_fn_bodies, cs_appends_def, cs_extends_trans]
QED

Theorem grouped_internal_run_labels:
  run_grouped_lowering groups ips fb rp "__entry" = SOME unit /\
  EVERY group_entry_labels_ok groups ==>
  ?start final data.
    compile_generate_grouped_runtime groups [] fb
      (initial_compile_state "__entry") = ((),start) /\
    compile_internal_fn_bodies ips start = ((),final) /\
    extract_context_with_internals "__entry" ips final = SOME (unit.cu_context,data) /\
    lowering_context_ok unit.cu_context /\
    EVERY (\bb. ~internal_label_ok bb.bb_label) (all_blocks start)
Proof
  strip_tac >>
  Cases_on `compile_generate_grouped_runtime groups [] fb
    (initial_compile_state "__entry")` >>
  rename1 `compile_generate_grouped_runtime _ [] _ _ = (u,start)` >> Cases_on `u` >>
  drule grouped_prefix_labels >>
  disch_then (qspecl_then [`fb`, `initial_compile_state "__entry"`] mp_tac) >>
  simp[] >> strip_tac >>
  `EVERY (\bb. ~internal_label_ok bb.bb_label) (all_blocks start)` by
    (drule cs_extends_block_stream_labels >> strip_tac >>
     fs[initial_compile_state_def, internal_label_ok_def] >>
     rename1 `MAP _ _ = added_labels _ _` >>
     pop_assum (assume_tac o SYM) >> fs[EVERY_MAP, internal_label_ok_def]) >>
  Cases_on `compile_internal_fn_bodies ips start` >>
  rename1 `compile_internal_fn_bodies ips start = (u,final)` >> Cases_on `u` >>
  qpat_x_assum `run_grouped_lowering _ _ _ _ _ = _` mp_tac >>
  once_rewrite_tac[run_grouped_lowering_def] >>
  once_rewrite_tac[compile_grouped_internal_suffix] >>
  simp[AllCaseEqs()] >> strip_tac >>
  qexists_tac `data` >> gvs[]
QED

Theorem compile_external_groups_append_layout:
  compile_external_groups mid (pref ++ rest) sa = (jobs,sb) /\
  fn_has_code sa sb fn ==>
  ?pref_jobs tail_jobs sc.
    compile_external_groups mid pref sa = (pref_jobs,sc) /\
    fn_has_code sa sc fn /\
    compile_external_groups mid rest sc = (tail_jobs,sb) /\
    fn_has_code sc sb fn /\
    jobs = pref_jobs ++ tail_jobs
Proof
  strip_tac >> drule compile_external_groups_append >>
  disch_then (qx_choosel_then [`left`,`right`,`cut`] strip_assume_tac) >>
  qexistsl_tac [`left`,`right`,`cut`] >> simp[] >>
  `ci_mono sa cut /\ ci_mono cut sb` by
    metis_tac[compile_external_groups_ci_mono, pairTheory.SND] >>
  fs[ci_mono_def] >> metis_tac[fn_has_code_split]
QED

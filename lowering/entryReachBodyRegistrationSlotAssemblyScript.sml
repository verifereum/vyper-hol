(* One actual selected registration slot, with a shared execution endpoint. *)
Theory entryReachBodyRegistrationSlotAssembly
Ancestors
  valueEncodingDefs loweringStateRelDefs entryReachBodyRegistrationSlotWitness entryReachBodyRegistrationSingleton
  entryReachBodyRegistrationIndexedShell entryReachBodyRegistrationSlotCertificate
  entryReachBodyRegistrationCanonical entryReachBodyRegistrationSizeBoundary
  entryReachBodyPackageAlignment entryReachBodyCallerResources
  entryReachBodyRegistrationPrefixSupport entryReachBodySourceMemberEntry
  entryReachBodySourceMemory entryReachBodyExactArrayLoop entryReachBodyCanonicalArrayChild
  compileVyper compileEnv finite_map rich_list list words arithmetic

Theorem entry_slot_block_ids[local]:
  !bbs. MAP (\i. i.inst_id) (venomInst$fn_insts_blocks bbs) =
    FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) bbs)
Proof
  Induct >> simp[venomInstTheory.fn_insts_blocks_def]
QED

Theorem entry_slot_canonical_split[local]:
  LENGTH avs = LENGTH args /\ i < LENGTH args ==>
  avs = TAKE i avs ++ EL i avs :: DROP (SUC i) avs /\
  MAP (vyper_to_abi_type env) (MAP SND args) =
    TAKE i (MAP (vyper_to_abi_type env) (MAP SND args)) ++
    vyper_to_abi_type env (SND (EL i args)) ::
    DROP (SUC i) (MAP (vyper_to_abi_type env) (MAP SND args)) /\
  LENGTH (TAKE i (MAP (vyper_to_abi_type env) (MAP SND args))) = LENGTH (TAKE i avs)
Proof
  strip_tac >> conj_tac >- metis_tac[TAKE_DROP_SUC, APPEND_ASSOC, APPEND] >>
  conj_tac >- (qspecl_then [`i`, `MAP (vyper_to_abi_type env) (MAP SND args)`]
    mp_tac TAKE_DROP_SUC >> simp[EL_MAP]) >>
  simp[LENGTH_TAKE]
QED

Theorem entry_slot_endpoint_resources[local]:
  array_child_result ctx fn k root extent ambient ids b cap site limit
    first last cell tv value ready t ==>
  alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
  abi_alloca_history (fn_insts fn) t /\ fresh_vars_wrt limit t /\
  ~t.vs_halted /\ t.vs_current_bb = last.cs_current_bb /\
  t.vs_inst_idx = LENGTH last.cs_current_insts
Proof
  simp[array_child_result_def]
QED

Theorem entry_slot_tail_code[local]:
  compile_register_positional_args ce pre 4 start = (cei,st) /\
  compile_register_positional_args cei singleton off st = (cei1,last) /\
  compile_register_positional_args cei1 post next last = (cef,registered) /\
  compile_guarded_body cef F key ut view fbody rt registered = ((),final) /\
  fn_has_code start final fn ==>
  fn_has_code last final fn
Proof
  strip_tac >>
  `cs_extends start st /\ cs_extends st last /\ cs_extends last registered` by
    metis_tac[actualRegistrationCodeTheory.register_positional_args_suffix_extends] >>
  `cs_extends registered final` by
    (mp_tac externalEntryShapeTheory.compile_guarded_body_labels >>
     disch_then (qspecl_then [`cef`, `F`, `key`, `ut`, `view`, `fbody`, `rt`, `registered`] mp_tac) >> simp[]) >>
  `cs_extends start last` by metis_tac[cs_extends_trans] >>
  `cs_extends last final` by metis_tac[cs_extends_trans] >>
  metis_tac[fragExecTheory.fn_has_code_split]
QED

Theorem entry_slot_ctor_flag[local]:
  compile_register_positional_args ce slots off st = (ce1,last) ==>
  ce1.ce_is_ctor = ce.ce_is_ctor
Proof
  strip_tac >> drule entryStateRelTheory.compile_register_positional_args_cenv >>
  disch_then (mp_tac o CONJUNCT1) >>
  disch_then (mp_tac o AP_TERM ``\ce:compile_env. ce.ce_is_ctor``) >> simp[]
QED

Theorem entry_selected_slot_run:
  lower_vyper_runtime_unit tops policy = SOME unit /\
  supported_program tops /\ source_typing_ok tops am tx /\
  initial_venom_state_rel tops am tx vs /\
  valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
  lookup_function NONE tx.function_name External tops = SOME (mut,F,args,[],ret,fbody) /\
  bind_arguments (type_env tops) args tx.args = SOME scope /\
  set_external_package_target target
    (package_external_fn tops F keys (mut,F,raw,tx.function_name,args,([]:expr list),ret,fbody)) =
    (lbl,ce,pos,cds,pay,F,key,ut,view,fbody,rt) /\
  compile_register_positional_args ce pos 4 start = (cef,registered) /\
  compile_guarded_body cef F key ut view fbody rt registered = ((),final) /\
  compile_register_positional_args ce (TAKE i pos) 4 start = (cei,st) /\
  compile_register_positional_args cei [EL i pos] off st = (cei1,last) /\
  off = 4 + SUM (MAP abi_member_head_size
    (TAKE i (MAP (vyper_to_abi_type (type_env tops)) (MAP SND args)))) /\
  fn_has_code start final fn /\ cs_extends final entry_end /\
  fn = mk_raw_function "__entry" (all_blocks entry_end) /\ fn_inst_ids_distinct fn /\
  i < LENGTH args /\ entry_prefix_witness fn (type_env tops) args tx.args i cei st s /\
  alloca_inv s /\ alloca_frontier_inv unit.cu_context fn site s /\
  abi_alloca_history (fn_insts fn) s /\ fresh_vars_wrt final s /\
  (!id r. FLOOKUP s.vs_allocas id = SOME r ==> id < st.cs_next_id) /\
  entry_loop_fields vs s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. entry_prefix_witness fn (type_env tops) args tx.args (SUC i) cei1 last t /\
    alloca_inv t /\ alloca_frontier_inv unit.cu_context fn site t /\
    abi_alloca_history (fn_insts fn) t /\ fresh_vars_wrt final t /\
    (!id r. FLOOKUP t.vs_allocas id = SOME r ==> id < last.cs_next_id) /\
    entry_loop_fields vs t /\ ~t.vs_halted /\
    t.vs_current_bb = last.cs_current_bb /\ t.vs_inst_idx = LENGTH last.cs_current_insts /\
    cei1.ce_is_ctor = F /\
    (!fuel r. run_from fuel unit.cu_context fn t = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' unit.cu_context fn s = r)
Proof
  strip_tac >> drule_all entry_selected_indexed_shell >> strip_tac >> gvs[] >>
  drule_all entry_selected_indexed_metadata >> strip_tac >>
  drule_all entry_selected_slot_allocation >> strip_tac >>
  gvs[] >>
  `cs_extends last entry_end` by
    (irule cs_extends_trans >> qexists_tac `final` >> simp[] >>
     irule cs_extends_trans >> qexists_tac `registered` >> conj_tac
     >- (irule actualRegistrationCodeTheory.register_positional_args_suffix_extends >>
         goal_assum (drule_at Any)) >>
     mp_tac externalEntryShapeTheory.compile_guarded_body_labels >>
     disch_then (qspecl_then [`cef`, `F`, `key`, `ut`, `view`, `fbody`, `rt`, `registered`] mp_tac) >> simp[]) >>
  qmatch_asmsub_abbrev_tac `emit_op ADD [Lit 4w; Lit (n2w head_off)] allocated` >>
  drule_all (SRULE [] (Q.INST [`off` |-> `head_off + 4`] entry_slot_compiler_counters)) >>
  disch_then (qspec_then `mk_raw_function "__entry" (all_blocks entry_end)` strip_assume_tac) >>
  drule entry_packaged_slot_scratch >> disch_then drule >> simp[] >> strip_tac >>
  drule_all entry_selected_indexed_location >> strip_tac >>
  drule_all entry_selected_parameter_size_bound >> disch_tac >>
  drule caller_runtime_allocation_budget >> disch_tac >>
  drule_all entry_registration_canonical_payload >> strip_tac >>
  drule_all entry_slot_canonical_split >>
  disch_then (qspec_then `type_env tops` strip_assume_tac) >>
  `FLOOKUP s.vs_allocas st.cs_next_id = NONE` by
    (irule registration_support_absent >> goal_assum (drule_at Any) >> simp[]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts (mk_raw_function "__entry" (all_blocks entry_end))))` by
    fs[venomWfTheory.fn_inst_ids_distinct_def, venomInstTheory.fn_insts_def, entry_slot_block_ids] >>
  gvs[abiDecoderMembersTheory.vyper_to_abi_types_MAP] >>
  suspend "endpoint"
QED

Resume entry_selected_slot_run[endpoint]:
  `?ready root t.
    FLOOKUP cei1.ce_vars (FST (EL i args)) =
      SOME (PtrVar buf.buf_operand (type_memory_size tv)) /\
    array_child_result unit.cu_context
      (mk_raw_function "__entry" (all_blocks entry_end)) st.cs_next_id root
      (type_memory_size tv)
      (window_alloca_sites (mk_raw_function "__entry" (all_blocks entry_end))
        (abi_decoder_ids first.cs_next_id last.cs_next_id))
      (window_alloca_sites (mk_raw_function "__entry" (all_blocks entry_end))
        (abi_decoder_ids first.cs_next_id last.cs_next_id))
      0 (unit_alloca_budget unit.cu_context) site final first last root tv
      (EL i tx.args) ready t /\
    eval_operand buf.buf_operand t = SOME (n2w root) /\
    entry_loop_fields s t /\
    s.vs_alloca_next <= ready.vs_alloca_next /\ ready.vs_memory = s.vs_memory /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op ready = eval_operand op s) /\
    (!id entry. FLOOKUP s.vs_allocas id = SOME entry ==>
      FLOOKUP ready.vs_allocas id = SOME entry) /\
    (!id. id <> st.cs_next_id ==>
      FLOOKUP ready.vs_allocas id = FLOOKUP s.vs_allocas id) /\
    (!fuel r. run_from fuel unit.cu_context
      (mk_raw_function "__entry" (all_blocks entry_end)) t = r /\
      (!err. r <> Error err) ==> ?fuel'. run_from fuel' unit.cu_context
      (mk_raw_function "__entry" (all_blocks entry_end)) s = r)` by
    (suspend "decoder") >>
  suspend "prefix"
QED

Resume entry_selected_slot_run[decoder]:
  irule registration_resource_decoder_run >>
     qpat_assum `compile_register_positional_args cei [_] _ _ = _` (irule_at Any) >>
     qpat_assum `entry_source_metadata _ _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `compile_guarded_body _ _ _ _ _ _ _ _ = _` (irule_at Any) >>
     qpat_assum `compile_register_positional_args cei1 _ _ _ = _` (irule_at Any) >>
     simp[] >>
     qpat_assum `LIST_REL _ (MAP SND args) tx.args` (irule_at Any) >>
     qpat_assum `compile_abi_decode_to_buf _ src _ (Lit 0w) _ _ _ = _` (irule_at Any) >>
     qexistsl_tac [`DROP (SUC i) avs`, `TAKE i avs`,
       `TAKE i (MAP (vyper_to_abi_type (type_env tops)) (MAP SND args))`,
       `DROP (SUC i) (MAP (vyper_to_abi_type (type_env tops)) (MAP SND args))`] >>
     qpat_assum `avs = _` (fn th =>
       pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
       pure_rewrite_tac [GSYM (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND] th)]) >>
     qpat_assum `MAP (vyper_to_abi_type _) _ = _` (fn th =>
       pure_rewrite_tac [GSYM (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND] th)]) >>
     qpat_x_assum `avs = _` kall_tac >>
     qpat_x_assum `MAP (vyper_to_abi_type _) _ = _` kall_tac >>
     simp[LENGTH_TAKE, Abbr `head_off`] >>
     irule entry_slot_tail_code >>
     qpat_assum `compile_register_positional_args ce (TAKE i pos) _ _ = _` (irule_at Any) >>
     qpat_assum `compile_register_positional_args cei [_] _ _ = _` (irule_at Any) >>
     qpat_assum `compile_register_positional_args cei1 _ _ _ = _` (irule_at Any) >>
     qpat_assum `compile_guarded_body _ _ _ _ _ _ _ _ = _` (irule_at Any) >> simp[]
QED

Resume entry_selected_slot_run[prefix]:
  drule_all externalBodyFrameTheory.external_selected_args_distinct >> disch_tac >>
  `val_wf tv (EL i tx.args)` by
    (irule valueTypingMemoryPropsTheory.value_has_type_memory_wf >>
     fs[entry_source_metadata_def]) >>
  `t.vs_alloca_next < dimword (:256)` by
    (irule allocaFrontierBoundTheory.alloca_frontier_inv_bound >>
     fs[array_child_result_def] >> metis_tac[]) >>
  `root < dimword (:256)` by
    (fs[array_child_result_def, entryReachBodyOwnedRegionTheory.entry_owned_region_def,
        venomMemDefsTheory.alloca_inv_def, venomMemDefsTheory.alloca_next_valid_def] >>
     first_x_assum drule >> decide_tac) >>
  `?vname ins. buf.buf_operand = Var vname /\
    MEM ins (fn_insts (mk_raw_function "__entry" (all_blocks entry_end))) /\
    ins.inst_opcode = ALLOCA /\ ins.inst_outputs = [vname] /\
    ins.inst_id = st.cs_next_id` by
    (suspend "provenance") >>
  `entry_slot_witness (mk_raw_function "__entry" (all_blocks entry_end)) (type_env tops) args tx.args i cei1 last t` by
    (irule entry_slot_witness_new >>
     qpat_assum `array_child_result _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     simp[] >> goal_assum (drule_at Any) >> simp[] >> fs[] >> decide_tac) >>
  `!j. j < i ==> entry_slot_witness (mk_raw_function "__entry" (all_blocks entry_end)) (type_env tops) args tx.args j cei1 last t` by
    (rpt strip_tac >> irule entry_slot_witness_old >>
     qpat_assum `compile_register_positional_args cei [_] _ _ = _` (irule_at Any) >>
     qpat_assum `array_child_result _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     qexists_tac `s` >> simp[] >> conj_tac
     >- (irule entry_slot_names_distinct >> simp[]) >>
     fs[entry_prefix_witness_def]) >>
  drule entry_slot_endpoint_resources >> strip_tac >>
  `!id r. FLOOKUP t.vs_allocas id = SOME r ==> id < last.cs_next_id` by
    (rpt gen_tac >> strip_tac >> irule registration_result_support >>
     qpat_assum `array_child_result _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     goal_assum (drule_at Any) >> qexists_tac `s` >> simp[]) >>
  `entry_loop_fields vs t` by fs[entry_loop_fields_def] >>
  `cei1.ce_is_ctor = F` by
    (qpat_assum `compile_register_positional_args cei [_] _ _ = _`
      (mp_tac o MATCH_MP entry_slot_ctor_flag) >> simp[]) >>
  qexists_tac `t` >> simp[] >>
  conj_tac >- (irule entry_prefix_witness_step >> simp[]) >>
  rpt strip_tac >> first_x_assum irule >> simp[] >> qexists_tac `fuel` >> simp[]
QED

Resume entry_selected_slot_run[provenance]:
  drule_all calldataRegistrationTheory.register_singleton_alloca_output >> strip_tac >>
  gvs[] >> goal_assum (drule_at Any) >> simp[]
QED

Finalise entry_selected_slot_run

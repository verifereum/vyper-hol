(* Conditional source-valued positional registration, at chosen endpoints.
   Body-state initial agreement, fmp_room and literal-size history are not
   consequences asserted by this theory. *)
Theory entrySourceRegistrationFold
Ancestors
  entrySingletonProducer entryRegistrationFoldBoundary calldataRegistrationExec
  calldataSourceMemberFold calldataMemberResourceFrame abiDecoderReentry
  abiDecoderFrame calldataRegistration moduleLowering exprLoweringProps
  actualRegistrationCode abiDecoderAppend abiDecoderCounters fragExec entryCompileIntervals
  entryDecoderStateFrame abiDecoderContract
  compileEnv venomState venomExecSemantics words list arithmetic finite_map

(* The singleton's freshly allocated parameter survives its own decoder.
   This is not scratch ownership: cap may differ from 32. *)
Theorem entry_registration_new_owned_endpoint[local]:
  id < first.cs_next_id /\ first.cs_next_id <= last.cs_next_id /\
  first.cs_next_var <= last.cs_next_var /\
  FLOOKUP ready.vs_allocas id = SOME (p,cap) /\
  eval_operand dst ready = SOME (n2w p) /\
  abi_decoder_operand_live first.cs_next_var dst /\
  calldata_member_success ctx fn site limit_st first last p cap tv v ready out scratch ==>
  FLOOKUP out.vs_allocas id = SOME (p,cap) /\
  eval_operand dst out = SOME (n2w p) /\
  abi_decoder_operand_live last.cs_next_var dst /\
  val_wf tv v /\ val_in_memory tv v p out.vs_memory
Proof
  strip_tac >> drule calldata_member_success_observations >> strip_tac >>
  drule calldata_member_resource_observations >> strip_tac >>
  simp[] >> metis_tac[abi_decoder_operand_live_mono]
QED

(* Lift the chosen-old-local boundary positionally. The left list contains
   original type/value pairs; equal decoder descriptors never merge slots. *)
Theorem entry_registration_old_prefix_endpoint[local]:
  st.cs_next_id < first.cs_next_id /\ st.cs_next_id < last.cs_next_id /\
  st.cs_next_var <= first.cs_next_var /\ st.cs_next_var <= last.cs_next_var /\
  ready.vs_memory = initial.vs_memory /\
  (!id entry. FLOOKUP initial.vs_allocas id = SOME entry ==>
    FLOOKUP ready.vs_allocas id = SOME entry) /\
  (!op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op ready = eval_operand op initial) /\
  FLOOKUP ready.vs_allocas st.cs_next_id = SOME (q,n) /\
  calldata_member_resource_frame ctx fn site limit_st first.cs_next_id last.cs_next_id
    first.cs_next_var q n ready out scratch /\
  LIST_REL (\(tv,v) (dst,p,id).
    id < st.cs_next_id /\ abi_decoder_operand_live st.cs_next_var dst /\
    FLOOKUP initial.vs_allocas id = SOME (p,type_memory_size tv) /\
    eval_operand dst initial = SOME (n2w p) /\
    val_wf tv v /\ val_in_memory tv v p initial.vs_memory) values outputs ==>
  LIST_REL (\(tv,v) (dst,p,id).
    id < last.cs_next_id /\ abi_decoder_operand_live last.cs_next_var dst /\
    FLOOKUP out.vs_allocas id = SOME (p,type_memory_size tv) /\
    eval_operand dst out = SOME (n2w p) /\
    val_wf tv v /\ val_in_memory tv v p out.vs_memory) values outputs
Proof
  strip_tac >> irule LIST_REL_mono >>
  goal_assum $ drule_at Any >>
  simp_tac (srw_ss()) [pairTheory.FORALL_PROD] >>
  rpt gen_tac >> strip_tac >>
  drule_all entry_registration_preserves_owned_local >> strip_tac >>
  simp[] >> metis_tac[abi_decoder_operand_live_mono, LESS_TRANS]
QED

(* Source/descriptor facts depend on the stable type-layout fields, not on
   the PtrVar bindings introduced while processing earlier parameters. *)
Theorem entry_registration_source_metadata_transport[local]:
  compile_register_positional_args ce done off st = (ce',middle) /\
  LIST_REL (\(name,prim,dyn,sz,info) (ty,tv,v,at,av).
    abi_decoder_coherent ce env sf ty tv /\
    info = type_to_abi_dec_info sf ce ty /\
    sz = abi_embedded_static_size ce.ce_struct_fields ty /\
    sz = abi_member_head_size at /\
    type_memory_bytes ce ty = type_memory_size tv /\
    (prim ==> ?c. info = DecPrimWord c) /\
    (dyn /\ ~prim <=> is_dynamic at) /\
    value_has_type tv v /\ vyper_to_abi env ty v = SOME av /\
    at = vyper_to_abi_type env ty /\ type_memory_size tv < dimword (:256)) specs values ==>
  LIST_REL (\(name,prim,dyn,sz,info) (ty,tv,v,at,av).
    abi_decoder_coherent ce' env sf ty tv /\
    info = type_to_abi_dec_info sf ce' ty /\
    sz = abi_embedded_static_size ce'.ce_struct_fields ty /\
    sz = abi_member_head_size at /\
    type_memory_bytes ce' ty = type_memory_size tv /\
    (prim ==> ?c. info = DecPrimWord c) /\
    (dyn /\ ~prim <=> is_dynamic at) /\
    value_has_type tv v /\ vyper_to_abi env ty v = SOME av /\
    at = vyper_to_abi_type env ty /\ type_memory_size tv < dimword (:256)) specs values
Proof
  strip_tac >> drule registration_env_fields >> strip_tac >>
  irule LIST_REL_mono >> goal_assum $ drule_at Any >>
  simp_tac (srw_ss()) [pairTheory.FORALL_PROD] >>
  rpt gen_tac >> strip_tac >>
  rename1 `abi_decoder_coherent ce env sf ty tv` >>
  drule registration_coherent_env_cong >>
  disch_then (qspec_then `ce'` mp_tac) >> simp[] >> strip_tac >>
  `type_memory_bytes ce' ty = type_memory_bytes ce ty` by
    metis_tac[type_memory_bytes_struct_fields] >>
  simp[registration_dec_info_env_cong]
QED

(* Binding preservation is independent of runtime memory preservation. *)
Theorem entry_registration_prefix_bindings[local]:
  !names outputs ce done off st ce' final.
    compile_register_positional_args ce done off st = (ce',final) /\
    EVERY (\(name,tv). ~MEM name (MAP (\(n,prim,dyn,sz,info). n) done)) names /\
    LIST_REL (\(name,tv) (dst,p,id).
      FLOOKUP ce.ce_vars name = SOME (PtrVar dst (type_memory_size tv))) names outputs ==>
    LIST_REL (\(name,tv) (dst,p,id).
      FLOOKUP ce'.ce_vars name = SOME (PtrVar dst (type_memory_size tv))) names outputs
Proof
  Induct >- simp[] >>
  gen_tac >> Cases_on `outputs` >> simp[] >>
  PairCases_on `h` >> PairCases_on `h'` >>
  rpt gen_tac >> strip_tac >> fs[] >>
  `FLOOKUP ce'.ce_vars h0 = FLOOKUP ce.ce_vars h0` by
    (drule registration_unmentioned_binding >>
     disch_then (qspec_then `h0` mp_tac) >> simp[]) >>
  simp[] >> first_x_assum drule >> simp[]
QED

(* The arbitrary accumulator is essential: both canonical ABI prefixes and
   the source-valued owned-local prefix grow at the recursive call. *)
Theorem entry_registration_singleton_anchored[local]:
  compile_register_positional_args ce [(name,prim,dyn,sz,info)] off st = (cef,final) ==>
  compile_register_positional_args cef remaining next_off final = (cer,registered) ==>
  compile_guarded_body cer F nk ut iv stmts rt registered = ((),completed) ==>
  abi_decoder_coherent ce env sf ty tv ==>
  vyper_to_abi env ty v = SOME av ==>
  has_types (pre ++ at::post) (pvs ++ av::rest) ==>
  bs = enc (Tuple (pre ++ at::post)) (ListV (pvs ++ av::rest)) ==>
  FLOOKUP ce.ce_vars name = SOME loc /\
  var_location_memory_size loc = SOME (type_memory_size tv) /\
  (prim ==> ?c. info = DecPrimWord c) /\ fn_has_code st final fn /\
  alloca_inv initial /\ alloca_frontier_inv ctx fn site initial /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  type_memory_size tv < dimword (:256) /\ unit_alloca_budget ctx < dimword (:256) /\
  (!entry. FLOOKUP initial.vs_allocas st.cs_next_id = SOME entry ==>
    ?p. entry = (p,type_memory_size tv) /\ p+type_memory_size tv < dimword (:256)) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  fn_inst_ids_distinct fn /\ alloca_history fn initial /\
  fresh_vars_wrt limit_st initial /\ final.cs_next_var <= limit_st.cs_next_var /\
  type_memory_size tv = type_memory_bytes ce ty /\
  info = type_to_abi_dec_info sf ce ty /\ value_has_type tv v /\
  at = vyper_to_abi_type env ty /\ LENGTH pre = LENGTH pvs /\
  mem_bytes_at 4 (LENGTH bs) (abi_decode_source CALLDATALOAD initial) = bs /\
  4 + LENGTH bs < dimword (:256) /\ off = 4 + SUM (MAP abi_member_head_size pre) /\
  (dyn /\ ~prim <=> is_dynamic at) /\
  (!id. st.cs_next_id <= id ==> FLOOKUP initial.vs_allocas id = NONE) /\
  ~block_is_terminated registered /\ fn_has_code final completed fn ==>
  ?dst src first ready p out scratch.
    FLOOKUP cef.ce_vars name = SOME (PtrVar dst (type_memory_size tv)) /\
    (?vname ins. dst = Var vname /\ MEM ins (fn_insts fn) /\
      ins.inst_opcode = ALLOCA /\ ins.inst_outputs = [vname] /\
      ins.inst_id = st.cs_next_id) /\
    compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w) info first = ((),final) /\
    fn_has_code first final fn /\ st.cs_next_id < first.cs_next_id /\
    st.cs_next_var <= first.cs_next_var /\
    ~ready.vs_halted /\ ready.vs_current_bb = first.cs_current_bb /\
    ready.vs_inst_idx = LENGTH first.cs_current_insts /\
    eval_operand dst ready = SOME (n2w p) /\
    eval_operand src ready = SOME (n2w (4 + abi_decode_member_offset at bs
      (SUM (MAP abi_member_head_size pre)))) /\
    abi_decoder_operand_live first.cs_next_var src /\
    abi_decoder_operand_live first.cs_next_var dst /\
    FLOOKUP ready.vs_allocas st.cs_next_id = SOME (p,type_memory_size tv) /\
    p+type_memory_size tv < dimword (:256) /\
    alloca_inv ready /\ alloca_frontier_inv ctx fn site ready /\
    initial.vs_alloca_next <= ready.vs_alloca_next /\
    ready.vs_memory = initial.vs_memory /\ ready.vs_call_ctx = initial.vs_call_ctx /\
    ready.vs_data_section = initial.vs_data_section /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op ready = eval_operand op initial) /\
    (!id entry. FLOOKUP initial.vs_allocas id = SOME entry ==>
      FLOOKUP ready.vs_allocas id = SOME entry) /\
    (!id. id <> st.cs_next_id ==>
      FLOOKUP ready.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!fuel r. run_from fuel ctx fn ready = r /\ (!err. r <> Error err) ==>
      ?fuel'. run_from fuel' ctx fn initial = r /\
        (mem_safe_run fuel ctx fn ready ==> mem_safe_run fuel' ctx fn initial)) /\
    entry_decoder_obs initial ready /\ alloca_history fn ready /\
    (abi_alloca_history (fn_insts fn) initial ==> abi_alloca_history (fn_insts fn) ready) /\
    fresh_vars_wrt limit_st ready /\
    ((!fuel. mem_safe_run fuel ctx fn ready) ==> !fuel. mem_safe_run fuel ctx fn initial) /\
    calldata_member_success ctx fn site limit_st first final p (type_memory_size tv)
      tv v ready out scratch /\
    entry_decoder_obs initial out /\ alloca_history fn out /\
    (abi_alloca_history (fn_insts fn) initial ==> abi_alloca_history (fn_insts fn) out) /\
    (!id. final.cs_next_id <= id ==> FLOOKUP out.vs_allocas id = NONE)
Proof
  rpt strip_tac >> irule entry_registration_singleton_source_endpoint >>
  asm_simp_tac bool_ss [] >> conj_tac
  >- (goal_assum (drule_at (Pat `compile_register_positional_args _ _ _ _ = _`)) >>
      goal_assum (drule_at (Pat `compile_guarded_body _ _ _ _ _ _ _ _ = _`)) >>
      asm_rewrite_tac[]) >>
  qpat_x_assum `compile_register_positional_args ce [_] off st = _` mp_tac >>
  asm_rewrite_tac[] >> disch_then (irule_at Any) >>
  goal_assum (drule_at (Pat `abi_decoder_coherent _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `vyper_to_abi _ _ _ = _`)) >>
  qpat_x_assum `has_types _ _` mp_tac >> asm_rewrite_tac[] >>
  disch_then (irule_at Any) >>
  qexists_tac `loc` >> asm_rewrite_tac[] >> metis_tac[]
QED

Theorem entry_registration_source_accumulator[local]:
  let M = (\ce specs values. LIST_REL
       (\(name,prim,dyn,sz,info) (ty,tv,v,at,av).
         abi_decoder_coherent ce env sf ty tv /\
         info = type_to_abi_dec_info sf ce ty /\
         sz = abi_embedded_static_size ce.ce_struct_fields ty /\
         sz = abi_member_head_size at /\
         type_memory_bytes ce ty = type_memory_size tv /\
         (prim ==> ?c. info = DecPrimWord c) /\
         (dyn /\ ~prim <=> is_dynamic at) /\
         value_has_type tv v /\ vyper_to_abi env ty v = SOME av /\
         at = vyper_to_abi_type env ty /\ type_memory_size tv < dimword (:256)) specs values);
      R = (\st s. alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
         alloca_history fn s /\ fresh_vars_wrt limit_st s /\
         (!id. st.cs_next_id <= id ==> FLOOKUP s.vs_allocas id = NONE) /\
         ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
         s.vs_inst_idx = LENGTH st.cs_current_insts);
      Owned = (\ce st s named outs. LIST_REL
       (\(name,tv,v) (dst,p,id).
         FLOOKUP ce.ce_vars name = SOME (PtrVar dst (type_memory_size tv)) /\
         (?vname ins. dst = Var vname /\ MEM ins (fn_insts fn) /\
           ins.inst_opcode = ALLOCA /\ ins.inst_outputs = [vname] /\ ins.inst_id = id) /\
         id < st.cs_next_id /\ abi_decoder_operand_live st.cs_next_var dst /\
         FLOOKUP s.vs_allocas id = SOME (p,type_memory_size tv) /\
         eval_operand dst s = SOME (n2w p) /\
         val_wf tv v /\ val_in_memory tv v p s.vs_memory) named outs);
      T = (\s t. entry_decoder_obs s t /\
         ((!fuel. mem_safe_run fuel ctx fn t) ==> !fuel. mem_safe_run fuel ctx fn s) /\
         (!fuel r. run_from fuel ctx fn t = r /\ (!err. r <> Error err) ==>
           ?fuel'. run_from fuel' ctx fn s = r /\
             (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s)) /\
         (abi_alloca_history (fn_insts fn) s ==> abi_alloca_history (fn_insts fn) t))
  in
  !specs values ce st initial prior old pre pvs off.
    compile_register_positional_args ce specs off st = (cer,registered) /\
    compile_guarded_body cer F nk ut iv stmts rt registered = ((),completed) /\
    ~block_is_terminated registered /\ fn_has_code st completed fn /\
    fn_inst_ids_distinct fn /\ ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
    unit_alloca_budget ctx < dimword (:256) /\
    registered.cs_next_var <= limit_st.cs_next_var /\
    R st initial /\ M ce specs values /\
    LIST_REL (\(name,prim,dyn,sz,info) (ty,tv,v,at,av).
      ?loc. FLOOKUP ce.ce_vars name = SOME loc /\
        var_location_memory_size loc = SOME (type_memory_size tv)) specs values /\
    ALL_DISTINCT (MAP (\(name,tv,v). name) prior ++
      MAP (\(name,prim,dyn,sz,info). name) specs) /\
    Owned ce st initial prior old /\ ALL_DISTINCT (MAP (\(dst,p,id). id) old) /\
    has_types (pre ++ MAP (\(ty,tv,v,at,av). at) values)
      (pvs ++ MAP (\(ty,tv,v,at,av). av) values) /\ LENGTH pre = LENGTH pvs /\
    bs = enc (Tuple (pre ++ MAP (\(ty,tv,v,at,av). at) values))
      (ListV (pvs ++ MAP (\(ty,tv,v,at,av). av) values)) /\
    mem_bytes_at 4 (LENGTH bs) (abi_decode_source CALLDATALOAD initial) = bs /\
    4 + LENGTH bs < dimword (:256) /\ off = 4 + SUM (MAP abi_member_head_size pre) ==>
    ?out added. R registered out /\ T initial out /\
      Owned cer registered out
        (prior ++ MAP (\((name,prim,dyn,sz,info),(ty,tv,v,at,av)). (name,tv,v))
          (ZIP (specs,values))) (old ++ added) /\
      ALL_DISTINCT (MAP (\(dst,p,id). id) (old ++ added))
Proof
  qmatch_goalsub_abbrev_tac `LET _ Meta` >>
  pure_rewrite_tac[Once LET_THM] >> BETA_TAC >>
  qmatch_goalsub_abbrev_tac `LET _ Ready` >>
  pure_rewrite_tac[Once LET_THM] >> BETA_TAC >>
  qmatch_goalsub_abbrev_tac `LET _ Own` >>
  pure_rewrite_tac[Once LET_THM] >> BETA_TAC >>
  qmatch_goalsub_abbrev_tac `LET _ Transfer` >>
  pure_rewrite_tac[Once LET_THM] >> BETA_TAC >>
  Induct
  >- (simp[compile_register_positional_args_def, comp_return_def] >>
      rpt gen_tac >> strip_tac >> gvs[] >>
      qexistsl_tac [`initial`,`[]`] >>
      simp[Abbr `Transfer`] >> rpt strip_tac >> qexists_tac `fuel` >> simp[]) >>
  suspend "successor"
QED

Resume entry_registration_source_accumulator[successor]:
  qx_gen_tac `spec` >> qx_gen_tac `values` >>
  Cases_on `values`
  >- (simp[Abbr `Meta`]) >>
  PairCases_on `spec` >> PairCases_on `h` >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_register_positional_args ce (_::_) off st = _` mp_tac >>
  once_rewrite_tac[SIMP_RULE (srw_ss()) []
    (Q.SPEC `[(spec0,spec1,spec2,spec3,spec4)]` register_positional_args_append)] >>
  strip_tac >>
  `cs_extends st stm /\ cs_extends stm registered` by
    metis_tac[register_positional_args_suffix_extends] >>
  `cs_extends registered completed` by
    (drule (SRULE [cs_appends_def] cs_appends_guarded_body) >> simp[]) >>
  `cs_extends stm completed` by metis_tac[cs_extends_trans] >>
  drule_all fn_has_code_split >> strip_tac >>
  suspend "chosen"
QED

Resume entry_registration_source_accumulator[chosen]:
  qpat_x_assum `Meta ce (_::_) (_::_)` mp_tac >>
  qpat_assum `Abbrev (Meta = _)` (fn th =>
    pure_rewrite_tac[REWRITE_RULE[markerTheory.Abbrev_def] th]) >>
  simp_tac (srw_ss()) [] >> strip_tac >>
  qpat_x_assum `Ready st initial` mp_tac >>
  qpat_assum `Abbrev (Ready = _)` (fn th =>
    pure_rewrite_tac[REWRITE_RULE[markerTheory.Abbrev_def] th]) >>
  BETA_TAC >> strip_tac >>
  qpat_x_assum `LIST_REL _ (_::_) (_::_)` mp_tac >>
  simp_tac (srw_ss()) [] >> strip_tac >>
  `stm.cs_next_var <= limit_st.cs_next_var` by
    (drule_all registration_compile_counters >> strip_tac >> decide_tac) >>
  `type_memory_size h1 = type_memory_bytes ce h0` by simp[] >>
  `!entry. FLOOKUP initial.vs_allocas st.cs_next_id = SOME entry ==>
    ?p. entry = (p,type_memory_size h1) /\ p + type_memory_size h1 < dimword (:256)` by
    (`FLOOKUP initial.vs_allocas st.cs_next_id = NONE` by simp[] >> simp[]) >>
  RULE_ASSUM_TAC (CONV_RULE (DEPTH_CONV pairLib.GEN_BETA_CONV) o
    PURE_REWRITE_RULE [MAP]) >>
  drule entry_registration_singleton_anchored >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then drule_all >> strip_tac >>
  suspend "accumulate"
QED

Resume entry_registration_source_accumulator[accumulate]:
  drule calldata_member_success_observations >> strip_tac >>
  drule calldata_member_resource_endpoint >> strip_tac >>
  `Ready stm out` by (simp[Abbr `Ready`]) >>
  `Transfer initial out` by
    (simp[Abbr `Transfer`] >>
     qpat_x_assum `calldata_member_transfers _ _ _ _` mp_tac >>
     rewrite_tac[calldata_member_transfers_def] >> strip_tac >>
     conj_tac >- metis_tac[] >> metis_tac[]) >>
  suspend "owned"
QED

Resume entry_registration_source_accumulator[owned]:
  drule abi_decoder_variable_counter >> strip_tac >>
  `first.cs_next_id <= stm.cs_next_id` by
    (qpat_x_assum `compile_abi_decode_to_buf _ _ _ (Lit 0w) _ _ first = ((),stm)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[cj 1 ci_mono_compile_abi_decode, ci_mono_def, pairTheory.SND]) >>
  `st.cs_next_id < stm.cs_next_id /\ st.cs_next_var <= stm.cs_next_var` by decide_tac >>
  drule_all entry_registration_new_owned_endpoint >> strip_tac >>
  suspend "old"
QED

Resume entry_registration_source_accumulator[old]:
  `Own cenvm stm out prior old` by
    (qpat_x_assum `Own ce st initial prior old` mp_tac >>
     qpat_assum `Abbrev (Own = _)` (fn th =>
       pure_rewrite_tac[REWRITE_RULE[markerTheory.Abbrev_def] th]) >>
     BETA_TAC >> strip_tac >>
     qpat_x_assum `LIST_REL _ prior old` mp_tac >>
     rewrite_tac[LIST_REL_EL_EQN] >> strip_tac >> asm_rewrite_tac[] >>
     qx_gen_tac `k` >> strip_tac >>
     first_x_assum (qspec_then `k` mp_tac) >> asm_rewrite_tac[] >>
     qabbrev_tac `named = EL k prior` >> qabbrev_tac `output = EL k old` >>
     PairCases_on `named` >> PairCases_on `output` >>
     simp_tac (srw_ss()) [] >> strip_tac >>
     rename1 `FLOOKUP ce.ce_vars name = SOME (PtrVar old_dst (type_memory_size tv))` >>
     `MEM name (MAP (\(name,tv,v). name) prior)` by
       (rewrite_tac[MEM_MAP] >> qexists_tac `(name,tv,named2)` >> simp[] >>
        metis_tac[EL_MEM]) >>
     `name <> spec0` by
       (qpat_x_assum `ALL_DISTINCT (_ ++ _)` mp_tac >>
        simp[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
     `FLOOKUP cenvm.ce_vars name = FLOOKUP ce.ce_vars name` by
       (qpat_x_assum `compile_register_positional_args ce [_] off st = _` mp_tac >>
        qpat_x_assum `name <> spec0` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
        drule registration_unmentioned_binding >>
        disch_then (qspec_then `name` mp_tac) >> simp[]) >>
     drule calldata_member_success_observations >> strip_tac >>
     drule_all entry_registration_preserves_owned_local >> strip_tac >>
     simp[] >> metis_tac[abi_decoder_operand_live_mono, LESS_TRANS]) >>
  suspend "extend"
QED

Resume entry_registration_source_accumulator[extend]:
  `Own cenvm stm out (prior ++ [(spec0,h1,h2)])
     (old ++ [(dst,p,st.cs_next_id)])` by
    (qpat_assum `Own cenvm stm out prior old` mp_tac >>
     qpat_assum `Abbrev (Own = _)` (fn th =>
       pure_rewrite_tac[REWRITE_RULE[markerTheory.Abbrev_def] th]) >>
     BETA_TAC >> strip_tac >> irule LIST_REL_APPEND_suff >>
     conj_tac >- (first_assum MATCH_ACCEPT_TAC) >>
     qpat_assum `Abbrev (Own = _)` (fn th =>
       pure_rewrite_tac[REWRITE_RULE[markerTheory.Abbrev_def] th]) >>
     BETA_TAC >> qpat_x_assum `Abbrev (Own = _)` kall_tac >>
     pure_rewrite_tac[LIST_REL_def, pairTheory.pair_case_thm] >>
     CONV_TAC (DEPTH_CONV pairLib.GEN_BETA_CONV) >>
     rewrite_tac[] >> conj_tac >- (first_assum ACCEPT_TAC) >>
     conj_tac
     >- (qexists_tac `vname` >>
         goal_assum (drule_at (Pat `MEM _ (fn_insts fn)`)) >> asm_rewrite_tac[]) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "tail"
QED

Resume entry_registration_source_accumulator[tail]:
  `Meta cenvm specs t` by
    (qpat_assum `Abbrev (Meta = _)` (fn th =>
       pure_rewrite_tac[REWRITE_RULE[markerTheory.Abbrev_def] th]) >>
     BETA_TAC >> irule entry_registration_source_metadata_transport >>
     qexistsl_tac [`ce`,`[(spec0,spec1,spec2,spec3,spec4)]`,`stm`,`off`,`st`] >>
     conj_tac >- (first_assum ACCEPT_TAC) >>
     first_assum MATCH_ACCEPT_TAC) >>
  suspend "capacity"
QED

Resume entry_registration_source_accumulator[capacity]:
  `LIST_REL (\(name,prim,dyn,sz,info) (ty,tv,v,at,av).
      ?loc. FLOOKUP cenvm.ce_vars name = SOME loc /\
        var_location_memory_size loc = SOME (type_memory_size tv)) specs t` by
    (qpat_x_assum `LIST_REL _ specs t` mp_tac >>
     rewrite_tac[LIST_REL_EL_EQN] >> strip_tac >>
     conj_tac >- (first_assum ACCEPT_TAC) >>
     qx_gen_tac `k` >> strip_tac >>
     first_x_assum (qspec_then `k` mp_tac) >>
     asm_simp_tac bool_ss [] >>
     qabbrev_tac `sp = EL k specs` >> qabbrev_tac `value = EL k t` >>
     PairCases_on `sp` >> PairCases_on `value` >>
     simp_tac (srw_ss()) [] >> strip_tac >>
     `MEM sp0 (MAP (\(name,prim,dyn,sz,info). name) specs)` by
       (rewrite_tac[MEM_MAP] >> qexists_tac `(sp0,sp1,sp2,sp3,sp4)` >>
        simp[] >> metis_tac[EL_MEM]) >>
     `sp0 <> spec0` by
       (qpat_x_assum `ALL_DISTINCT (_ ++ _)` mp_tac >>
        simp[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
     `FLOOKUP cenvm.ce_vars sp0 = FLOOKUP ce.ce_vars sp0` by
       (qpat_x_assum `compile_register_positional_args ce [_] off st = _` mp_tac >>
        qpat_x_assum `sp0 <> spec0` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
        drule registration_unmentioned_binding >>
        disch_then (qspec_then `sp0` mp_tac) >> simp[]) >>
     metis_tac[]) >>
  suspend "fresh_ids"
QED

Resume entry_registration_source_accumulator[fresh_ids]:
  `EVERY (\(dst,p,id). id < st.cs_next_id) old` by
    (qpat_assum `Own ce st initial prior old` mp_tac >>
     qpat_assum `Abbrev (Own = _)` (fn th =>
       pure_rewrite_tac[REWRITE_RULE[markerTheory.Abbrev_def] th]) >>
     BETA_TAC >> rewrite_tac[LIST_REL_EL_EQN, EVERY_EL] >> strip_tac >>
     qx_gen_tac `k` >> strip_tac >>
     first_x_assum (qspec_then `k` mp_tac) >>
     asm_simp_tac bool_ss [] >>
     qabbrev_tac `nm = EL k prior` >> qabbrev_tac `slot = EL k old` >>
     PairCases_on `nm` >> PairCases_on `slot` >> simp[]) >>
  `ALL_DISTINCT (MAP (\(dst,p,id). id) (old ++ [(dst,p,st.cs_next_id)]))` by
    (simp[ALL_DISTINCT_APPEND, MEM_MAP, pairTheory.EXISTS_PROD] >>
     qpat_x_assum `EVERY _ old` mp_tac >> rewrite_tac[EVERY_MEM] >>
     simp_tac (srw_ss()) [pairTheory.FORALL_PROD] >> rpt strip_tac >> first_x_assum drule >> simp[]) >>
  suspend "invoke"
QED

Resume entry_registration_source_accumulator[invoke]:
  `ALL_DISTINCT (MAP (\(name,tv,v). name) (prior ++ [(spec0,h1,h2)]) ++
      MAP (\(name,prim,dyn,sz,info). name) specs)` by
    (qpat_x_assum `ALL_DISTINCT (_ ++ _)` mp_tac >>
     simp[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  `mem_bytes_at 4 (LENGTH bs) (abi_decode_source CALLDATALOAD out) = bs` by
    (qpat_x_assum `entry_decoder_obs initial out` mp_tac >>
     rewrite_tac[entry_decoder_obs_def] >> strip_tac >>
     `abi_decode_source CALLDATALOAD out = abi_decode_source CALLDATALOAD initial` by
       (qpat_x_assum `out.vs_call_ctx = initial.vs_call_ctx` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> simp[abi_decode_source_def]) >>
     qpat_x_assum `abi_decode_source CALLDATALOAD out = _` SUBST1_TAC >>
     first_assum ACCEPT_TAC) >>
  qpat_x_assum `!values ce st initial prior old pre pvs off. _` mp_tac >>
  disch_then (qspecl_then [`t`,`cenvm`,`stm`,`out`] mp_tac) >>
  disch_then (qspecl_then [`prior ++ [(spec0,h1,h2)]`,
    `old ++ [(dst,p,st.cs_next_id)]`] mp_tac) >>
  disch_then (qspecl_then [`pre ++ [h3]`,`pvs ++ [h4]`,`off + spec3`] mp_tac) >>
  impl_tac >- suspend "premises" >>
  strip_tac >> suspend "compose"
QED

Resume entry_registration_source_accumulator[premises]:
  asm_simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND, MAP, MAP_APPEND, LENGTH_APPEND, LENGTH, SUM_APPEND, SUM] >>
  conj_tac
  >- (qpat_x_assum `has_types _ _` mp_tac >> asm_simp_tac bool_ss []) >>
  decide_tac
QED

Resume entry_registration_source_accumulator[compose]:
  `Transfer initial out'` by
    (qpat_x_assum `Transfer initial out` mp_tac >>
     qpat_x_assum `Transfer out out'` mp_tac >>
     qpat_assum `Abbrev (Transfer = _)` (fn th =>
       pure_rewrite_tac[REWRITE_RULE[markerTheory.Abbrev_def] th]) >>
     BETA_TAC >> POP_ASSUM_LIST (K all_tac) >> rpt strip_tac
     >- metis_tac[entry_decoder_obs_trans]
     >- metis_tac[] >> metis_tac[]) >>
  qexistsl_tac [`out'`,`(dst,p,st.cs_next_id)::added`] >>
  conj_tac
  >- (qpat_x_assum `Ready registered out'` mp_tac >>
      qpat_assum `Abbrev (Ready = _)` (fn th =>
        pure_rewrite_tac[REWRITE_RULE[markerTheory.Abbrev_def] th]) >>
      BETA_TAC >> disch_then ACCEPT_TAC) >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND, MAP_APPEND, MAP]) >>
  RULE_ASSUM_TAC (CONV_RULE (DEPTH_CONV pairLib.GEN_BETA_CONV)) >>
  asm_simp_tac (srw_ss()) [MAP]
QED

Finalise entry_registration_source_accumulator

(* Empty-prefix interface. Initial resources remain explicit hypotheses. *)
Theorem entry_registration_source_endpoint:
  compile_register_positional_args ce specs 4 st = (cer,registered) /\
  compile_guarded_body cer F nk ut iv stmts rt registered = ((),completed) /\
  ~block_is_terminated registered /\ fn_has_code st completed fn /\
  fn_inst_ids_distinct fn /\ ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  unit_alloca_budget ctx < dimword (:256) /\
  registered.cs_next_var <= limit_st.cs_next_var /\
  alloca_inv initial /\ alloca_frontier_inv ctx fn site initial /\
  alloca_history fn initial /\ fresh_vars_wrt limit_st initial /\
  (!id. st.cs_next_id <= id ==> FLOOKUP initial.vs_allocas id = NONE) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  LIST_REL (\(name,prim,dyn,sz,info) (ty,tv,v,at,av).
    abi_decoder_coherent ce env sf ty tv /\
    info = type_to_abi_dec_info sf ce ty /\
    sz = abi_embedded_static_size ce.ce_struct_fields ty /\ sz = abi_member_head_size at /\
    type_memory_bytes ce ty = type_memory_size tv /\
    (prim ==> ?c. info = DecPrimWord c) /\ (dyn /\ ~prim <=> is_dynamic at) /\
    value_has_type tv v /\ vyper_to_abi env ty v = SOME av /\
    at = vyper_to_abi_type env ty /\ type_memory_size tv < dimword (:256)) specs values /\
  LIST_REL (\(name,prim,dyn,sz,info) (ty,tv,v,at,av).
    ?loc. FLOOKUP ce.ce_vars name = SOME loc /\
      var_location_memory_size loc = SOME (type_memory_size tv)) specs values /\
  ALL_DISTINCT (MAP (\(name,prim,dyn,sz,info). name) specs) /\
  has_types (MAP (\(ty,tv,v,at,av). at) values) (MAP (\(ty,tv,v,at,av). av) values) /\
  bs = enc (Tuple (MAP (\(ty,tv,v,at,av). at) values))
    (ListV (MAP (\(ty,tv,v,at,av). av) values)) /\
  mem_bytes_at 4 (LENGTH bs) (abi_decode_source CALLDATALOAD initial) = bs /\
  4 + LENGTH bs < dimword (:256) ==>
  ?out outputs.
    alloca_inv out /\ alloca_frontier_inv ctx fn site out /\
    alloca_history fn out /\ fresh_vars_wrt limit_st out /\
    (!id. registered.cs_next_id <= id ==> FLOOKUP out.vs_allocas id = NONE) /\
    ~out.vs_halted /\ out.vs_current_bb = registered.cs_current_bb /\
    out.vs_inst_idx = LENGTH registered.cs_current_insts /\
    entry_decoder_obs initial out /\
    (abi_alloca_history (fn_insts fn) initial ==> abi_alloca_history (fn_insts fn) out) /\
    ((!fuel. mem_safe_run fuel ctx fn out) ==> !fuel. mem_safe_run fuel ctx fn initial) /\
    (!fuel r. run_from fuel ctx fn out = r /\ (!err. r <> Error err) ==>
      ?fuel'. run_from fuel' ctx fn initial = r /\
        (mem_safe_run fuel ctx fn out ==> mem_safe_run fuel' ctx fn initial)) /\
    LIST_REL (\(name,tv,v) (dst,p,id).
      FLOOKUP cer.ce_vars name = SOME (PtrVar dst (type_memory_size tv)) /\
      (?vname ins. dst = Var vname /\ MEM ins (fn_insts fn) /\
        ins.inst_opcode = ALLOCA /\ ins.inst_outputs = [vname] /\ ins.inst_id = id) /\
      id < registered.cs_next_id /\ abi_decoder_operand_live registered.cs_next_var dst /\
      FLOOKUP out.vs_allocas id = SOME (p,type_memory_size tv) /\
      eval_operand dst out = SOME (n2w p) /\
      val_wf tv v /\ val_in_memory tv v p out.vs_memory)
      (MAP (\((name,prim,dyn,sz,info),(ty,tv,v,at,av)). (name,tv,v))
        (ZIP (specs,values))) outputs /\
    ALL_DISTINCT (MAP (\(dst,p,id). id) outputs)
Proof
  strip_tac >>
  mp_tac (SIMP_RULE bool_ss [LET_THM] entry_registration_source_accumulator) >>
  disch_then (qspecl_then [`specs`,`values`,`ce`,`st`] mp_tac) >>
  disch_then (qspec_then `initial` mp_tac) >>
  disch_then (qspecl_then [`[]`,`[]`,`[]`,`[]`] mp_tac) >>
  simp[] >> strip_tac >> qexistsl_tac [`out`,`added`] >> simp[]
QED

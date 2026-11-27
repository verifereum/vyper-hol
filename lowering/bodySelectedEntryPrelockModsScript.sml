(* The real INVOKE entry leads to a single reached prelock triple. *)
Theory bodySelectedEntryPrelockMods
Ancestors
  bodySelectedCaptureReserveMods bodySelectedMaterializePrelockMods
  fragGasFocus frameActivationSeparation venomExecProps venomExecSemantics
  fragExec fragGasOriginPtr bodyFullPostsMods bodyInvSplit bodyPtrDefs
  intCallCallee compileVyper exprLoweringProps loweringStateRelDefs
  vyperStorageFootprint vyperFiniteStoragePreservation vyperState
  venomState venomInst finite_map list pred_set words

Theorem prelock_decode_setup[local]:
  gas_invoke_entry (ctx,func) t callee entered /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  decode_invoke inst = SOME (lbl,arg_ops) /\ eval_operands arg_ops t = SOME argv /\
  fn_entry_label callee = SOME lbl /\ entry.cs_current_bb = lbl ==>
  ?setup first phi_state.
    setup_callee callee argv t = SOME setup /\
    setup.vs_current_bb = entry.cs_current_bb /\ setup.vs_inst_idx = 0 /\
    lookup_block setup.vs_current_bb callee.fn_blocks = SOME first /\
    eval_phis setup first.bb_instructions = OK phi_state /\
    entered = phi_state with vs_inst_idx := phi_prefix_length first.bb_instructions
Proof
  simp[gas_invoke_entry_def] >> strip_tac >> gvs[] >>
  drule_then strip_assume_tac setup_callee_props >> gvs[]
QED

Theorem prelock_reserve_setup_frame[local]:
  setup_callee callee argv t = SOME setup /\
  u = setup with <|vs_vars := u.vs_vars; vs_inst_idx := k|> /\
  u.vs_inst_idx = k ==>
  u = t with <|vs_vars := u.vs_vars; vs_params := u.vs_params;
               vs_current_bb := u.vs_current_bb; vs_inst_idx := u.vs_inst_idx;
               vs_prev_bb := u.vs_prev_bb; vs_halted := u.vs_halted;
               vs_allocas := u.vs_allocas; vs_call_entry_fmp := u.vs_call_entry_fmp;
               vs_return_pc_token := u.vs_return_pc_token|>
Proof
  simp[setup_callee_def, AllCaseEqs()] >> strip_tac >>
  qpat_assum `u = _` (pure_once_rewrite_tac o single) >>
  qpat_x_assum `_ = setup` (SUBST_ALL_TAC o SYM) >>
  simp[NoAsms,venom_state_component_equality]
QED

Theorem selected_entry_prelock_run_mods:
  gas_invoke_entry (ctx,func) t callee entered /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  decode_invoke inst = SOME (lbl,arg_ops) /\ eval_operands arg_ops t = SOME argv /\
  fn_entry_label callee = SOME lbl /\ entry.cs_current_bb = lbl /\
  entry.cs_current_insts = [] /\
  compile_internal_entry_prefix ce params has_rb entry = ((ce1,caps,pc),capture) /\
  (if ctor /\ 0 < ilen then comp_bind (compile_fixed_region_with_id ilen)
      (\ar. comp_return (SOME (SND ar).buf_operand))
    else comp_return NONE) capture = (imm,reserved) /\
  materialize_internal_params ce1 caps reserved = (ce2,materialized) /\
  (case rt of NONE => comp_return ()
   | SOME ty => if 0 < ce.ce_returns_count then
       comp_ignore_bind (compile_alloc_buffer (type_memory_bytes ce ty))
         (comp_return ()) else comp_return ()) materialized = ((),prologue) /\
  body_ce = ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|> /\
  fn_has_code entry capture callee /\ fn_has_code capture reserved callee /\
  fn_has_code reserved materialized callee /\ fn_has_code materialized prologue callee /\
  fn_inst_ids_distinct callee /\
  (!bb. MEM bb callee.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  p = cx with stk updated_by CONS key /\
  d = (if has_rb then SOME (HD argv,type_memory_size rtv) else NONE) /\
  (!setup. setup_callee callee argv t = SOME setup ==> fmp_room ctx callee setup) /\
  alloca_room ctx callee entered /\ lo <= t.vs_alloca_next /\
  (!fn inst u. frag_reachable ctx callee entered fn inst u ==> dalloca_fmp_headroom inst u) /\
  t.vs_alloca_next + internal_stack_size ce params < dimword (:256) /\
  es1.scopes = [penv] /\
  (!n e. FLOOKUP penv n = SOME e ==> value_has_type e.type e.value) /\
  (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
     internal_args_rel ce params penv (if has_rb then 1 else 0) argv t.vs_alloca_next mem) /\
  (!i off sz. i < LENGTH params /\ ~SND (EL i params) /\
     FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc off sz) ==>
     ?b bsz. op_prov G (EL ((if has_rb then 1 else 0) + i) arg_ops) = SOME (b,bsz) /\
       b <= w2n (EL ((if has_rb then 1 else 0) + i) argv) /\
       w2n (EL ((if has_rb then 1 else 0) + i) argv) + sz <= b + bsz) /\
  (has_rb ==> ?base len. op_prov G (HD arg_ops) = SOME (base,len) /\
     base <= w2n (HD argv) /\ w2n (HD argv) + type_memory_size rtv <= base + len /\
     base + len <= t.vs_alloca_next /\ lo <= base) /\
  (has_rb ==> ?off sz. ce.ce_return_buf = SOME (MemLoc off sz)) /\
  (~has_rb ==> ce.ce_return_buf = NONE) /\
  (ce.ce_is_ctor ==> IS_SOME (FLOOKUP t.vs_labels "runtime_begin")) /\
  ce.ce_imm_alloca = NONE /\
  (!n off sz. FLOOKUP ce.ce_vars n = SOME (MemLoc off sz) ==> MEM n (MAP FST params)) /\
  (!n op sz. FLOOKUP ce.ce_vars n <> SOME (PtrVar op sz)) /\
  ce.ce_modules = cenv.ce_modules /\ ce.ce_module_vars = cenv.ce_module_vars /\
  (!H. valid_horizon p st0 H es1.storage_trace ==>
     ghost_inv_at_mods (DF H) lo dc cenv cx ec G tn t) /\
  (!H. valid_horizon cx st0 H es1.storage_trace ==>
     state_rel H callee ce cx (es1 with scopes := []) t) /\
  (!H. valid_horizon p st0 H es1.storage_trace ==> storage_well_formed_on p es1 (FST H)) /\
  immutables_rel_mods ce cx.txn.target ce.ce_is_ctor es1 t /\
  ALOOKUP ce.ce_modules ce.ce_module = SOME tops /\
  (ce.ce_is_ctor ==> !src m n tv v off.
     ALOOKUP ce.ce_modules src = SOME m /\
     FLOOKUP ce.ce_module_vars (src,n) = SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP es1.immutables cx.txn.target of
                NONE => FEMPTY | SOME imms => get_source_immutables src imms) n = SOME (tv,v) ==>
     off + type_memory_size tv <= lo) /\
  immutable_alloca_sep_mods func cenv p old t /\
  cenv.ce_is_ctor = ce1.ce_is_ctor /\ cenv.ce_module_var_type = ce1.ce_module_var_type /\
  old.immutables = es1.immutables /\
  (!i off sz. i < LENGTH params /\ ~SND (EL i params) /\
    FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc off sz) ==>
    ?inst base len. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      FLOOKUP t.vs_allocas inst.inst_id = SOME (base,len) /\
      base <= w2n (EL ((if has_rb then 1 else 0) + i) argv) /\
      w2n (EL ((if has_rb then 1 else 0) + i) argv) + sz <= base + len) /\
  (has_rb ==> !i off sz. i < LENGTH params /\ ~SND (EL i params) /\
     FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc off sz) ==>
     loweringStateRelDefs$regions_disjoint (w2n (HD argv)) (type_memory_size rtv)
       (w2n (EL (1 + i) argv)) sz) ==>
  ?at_pro Gpro tnpro.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,callee,MAP (op_prov G) arg_ops)
        (entered,FEMPTY,tn with t_var := FEMPTY) [] (OK at_pro,Gpro,tnpro)) /\
    ~at_pro.vs_halted /\ at_pro.vs_current_bb = prologue.cs_current_bb /\
    at_pro.vs_inst_idx = LENGTH prologue.cs_current_insts /\
    ~block_is_terminated prologue /\ fresh_vars_wrt prologue at_pro /\
    local_ptrs_reserved body_ce prologue /\ ret_pc_ok body_ce prologue at_pro /\
    (!q sz. body_ce.ce_return_buf = SOME (PtrVar (Var q) sz) ==> not_fresh_at prologue q) /\
    (!q sz. body_ce.ce_return_pc = SOME (PtrVar (Var q) sz) ==> not_fresh_at prologue q) /\
    return_buf_frame d body_ce prologue at_pro /\ return_buf_sep d body_ce es1 at_pro /\
    alloca_history callee at_pro /\ allocas_from lo at_pro /\
    t.vs_alloca_next <= at_pro.vs_alloca_next /\ allocas_from t.vs_alloca_next at_pro /\
    alloca_room ctx callee at_pro /\ fmp_room ctx callee at_pro /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp at_pro) /\
    (!fn inst u. frag_reachable ctx callee at_pro fn inst u ==> dalloca_fmp_headroom inst u) /\
    (!H. valid_horizon p st0 H es1.storage_trace ==>
       stmt_state_rel H ctx callee body_ce p es1 at_pro /\
       immutable_frame_mods callee body_ce p es1 at_pro /\
       storage_well_formed_on p es1 (FST H) /\ ghost_inv_at_mods (DF H) lo d body_ce p es1 Gpro tnpro at_pro) /\
    at_pro.vs_accounts = t.vs_accounts /\ at_pro.vs_transient = t.vs_transient /\
    at_pro.vs_call_ctx = t.vs_call_ctx /\ at_pro.vs_tx_ctx = t.vs_tx_ctx /\
    at_pro.vs_block_ctx = t.vs_block_ctx /\
    (!b sz. b + sz <= t.vs_alloca_next ==>
      mem_bytes_at b sz at_pro.vs_memory = mem_bytes_at b sz t.vs_memory) /\
    (!i. i < t.vs_alloca_next ==> (i IN tnpro.t_mem <=> i IN tn.t_mem)) /\
    tnpro.t_stor = tn.t_stor /\ tnpro.t_trans = tn.t_trans /\ tnpro.t_imm = tn.t_imm
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac prelock_decode_setup >>
  `fmp_room ctx callee setup` by (first_assum irule >> first_assum ACCEPT_TAC) >>
  qabbrev_tac `Ds = {DF H | valid_horizon p st0 H es1.storage_trace}` >>
  `!D. D IN Ds ==> ghost_inv_at_mods D lo dc cenv cx ec G tn t` by
    (simp[Abbr `Ds`, PULL_EXISTS] >> rpt strip_tac >> first_assum irule >>
     first_assum ACCEPT_TAC) >>
  `(has_rb ==> ?b sz. op_prov G (HD arg_ops) = SOME (b,sz) /\
     b <= w2n (HD argv) /\ w2n (HD argv) + type_memory_size rtv <= b + sz /\
     b + sz <= t.vs_alloca_next)` by
    (disch_tac >> qpat_assum `has_rb ==> ?b sz. _ /\ _ /\ _ /\ _ /\ lo <= b`
       (drule_then (qx_choose_then `rb_base` (qx_choose_then `rb_len` strip_assume_tac))) >>
     qexistsl_tac [`rb_base`,`rb_len`] >> simp[]) >>
  mp_tac (Q.INST [`caller` |-> `cenv`, `es` |-> `es1`, `cx'` |-> `p`]
    selected_capture_reserve_run_mods) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `u` (qx_choose_then `J` (qx_choose_then `N`
    (qx_choose_then `x` (qx_choose_then `mr` (map_every assume_tac o CONJUNCTS)))))) >>
  drule_all_then assume_tac prelock_reserve_setup_frame >>
  drule_then strip_assume_tac setup_callee_allocation_frame >>
  `entered.vs_allocas = FEMPTY /\ entered.vs_alloca_next = t.vs_alloca_next /\
   entered.vs_inst_idx = 0` by
    (qpat_assum `entered = setup` (pure_once_rewrite_tac o single) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `internal_args_rel ce1 params penv (if has_rb then 1 else 0) argv
     t.vs_alloca_next u.vs_memory` by
    (first_assum irule >> simp[NoAsms,mem_agree_outside_def]) >>
  (Q.SUBGOAL_THEN `imm = NONE \/ ?q. imm = SOME (Var q) /\ lookup_var q u = SOME 0w /\
       ~not_fresh_at capture q /\ not_fresh_at reserved q` assume_tac
   >- (qpat_x_assum `(if _ then ?q. imm = _ /\ _ else imm = NONE)` mp_tac >>
       Cases_on `ctor /\ 0 < ilen` >> asm_simp_tac bool_ss []
       >- (disch_then (qx_choose_then `iq` strip_assume_tac) >>
           disj2_tac >> qexists_tac `iq` >> asm_rewrite_tac[]) >>
       disch_then (irule_at Any))) >>
  `!H. valid_horizon p st0 H es1.storage_trace ==>
    ghost_inv_at_mods (DF H) lo d (ce1 with ce_imm_alloca := imm) p es1 J N u` by
    (rpt strip_tac >> qpat_assum `d = _` (pure_once_rewrite_tac o single) >>
     first_assum irule >> simp[NoAsms, Abbr `Ds`, PULL_EXISTS] >>
     qexists_tac `H` >> asm_rewrite_tac[]) >>
  mp_tac (Q.INST [`s` |-> `u`, `caller` |-> `func`,
    `idx` |-> `if has_rb then 1 else 0`] selected_materialize_prelock_run_mods) >>
  (impl_tac >- (
    rpt (first_assum ACCEPT_TAC ORELSE REFL_TAC ORELSE conj_tac)
    >- (qpat_assum `d = _` (pure_once_rewrite_tac o single) >> first_assum ACCEPT_TAC)
    >- (gen_tac >> disch_tac >>
        qpat_assum `!i. i < LENGTH params ==> ?q. _ /\ not_fresh_at reserved q /\ _`
          (drule_then (qx_choose_then `cq` strip_assume_tac)) >>
        qexists_tac `cq` >> rpt conj_tac >> first_assum ACCEPT_TAC)
    >- (sym_tac >> first_assum ACCEPT_TAC)
    >- (sym_tac >> first_assum ACCEPT_TAC)
    >- asm_rewrite_tac[]
    >- asm_rewrite_tac[]
    >- (qpat_assum `!n b sz. mr n = SOME (b,sz) <=> _`
          (fn th => simp_tac bool_ss [th])) >>
    qpat_assum `ce1.ce_vars = ce.ce_vars` (pure_once_rewrite_tac o single) >>
    first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `at_pro` (qx_choose_then `Gpro`
    (qx_choose_then `tnpro` (map_every assume_tac o CONJUNCTS)))) >>
  qexistsl_tac [`at_pro`,`Gpro`,`tnpro`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

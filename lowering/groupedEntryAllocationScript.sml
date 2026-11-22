Theory groupedEntryAllocation
Ancestors
  entryReachBodyFmp exprLoweringProps abiAllocationHistory
  groupedKeywordAllocas abiBuiltinAllocation moduleLowering context emitHelperProps
  compileEnv venomInstIdsProps list pair allocaFrontierBound allocaFrontierRoom
  selectedAcceptedFold defaultConcreteRegistrationDefs ptrDiscipline
  fragGasOriginPtr fragExec venomInst venomInstProofs1 venomExecProofs
  venomExecSemantics venomState loweringStateRelDefs context allocaRemapSSA

Theorem grouped_entry_edge_abi_history[local]:
  gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG)
    (s,G,tn) marks (OK t,J,tz) /\ abi_alloca_history (fn_insts fn) s ==>
  abi_alloca_history (fn_insts fn) t
Proof
  strip_tac >> drule gas_origin_ptr_edge_common_fuel >> strip_tac >>
  `MEM inst (fn_insts fn)` by
    (irule mem_fn_insts_intro >> qexists_tac `bb` >>
     fs[get_instruction_def] >> metis_tac[lookup_block_MEM, listTheory.EL_MEM]) >>
  Cases_on `middle` >> gvs[exit_result_def] >>
  rename1 `step_inst fuel ctx inst s = OK step_state` >>
  `abi_alloca_history (fn_insts fn) step_state` by
    metis_tac[abi_alloca_history_step_inst] >>
  irule abi_alloca_history_frame >> qexists_tac `step_state` >> simp[] >>
  metis_tac[eval_phis_preserves_alloca_fields]
QED

Theorem grouped_entry_path_abi_history:
  gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) marks (OK t,J,tz) /\
  abi_alloca_history (fn_insts fn) s ==> abi_alloca_history (fn_insts fn) t
Proof
  qsuff_tac
    `!cx st marks out. gas_origin_ptr_path cx st marks out ==>
      case (cx,st,out) of
        ((D,lo,explicit,ctx,fn,PG),(s,G,tn),(r,J,tz)) =>
          !t. r = OK t /\ abi_alloca_history (fn_insts fn) s ==>
          abi_alloca_history (fn_insts fn) t`
  >- (strip_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      first_x_assum drule >> simp[]) >>
  ho_match_mp_tac gas_origin_ptr_path_ind >>
  simp[exit_result_def] >> rpt strip_tac >> gvs[] >>
  metis_tac[grouped_entry_edge_abi_history]
QED

Theorem grouped_default_registration_resources:
  selected_registration_resources ctx fn site 0 st s /\
  alloca_history fn s /\ abi_alloca_history (fn_insts fn) s /\
  tn.t_mem = {} /\ tn.t_stor = {} /\ tn.t_trans = {} /\ tn.t_imm = {} /\
  unit_alloca_budget ctx < dimword (:256) /\
  s.vs_fmp = s.vs_initial_fmp /\
  (ctx_has_dalloca ctx ==> unit_alloca_budget ctx <= w2n s.vs_initial_fmp /\
    w2n s.vs_initial_fmp < 2 ** 254) ==>
  default_registration_resources ctx fn site 0 st s tn
Proof
  simp_tac bool_ss [default_registration_resources_def, selected_registration_resources_def,
    alloca_frontier_inv_from_shift_def, arithmeticTheory.SUB_0, venom_state_fn_updates] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  simp[] >> conj_tac
  >- (irule deploy_ctor_frontier_alloca_room >> qexistsl_tac [`0`,`site`] >>
      simp[alloca_frontier_inv_from_shift_def, venom_state_fn_updates]) >>
  mp_tac (SPEC_ALL entry_frontier_fmp_room) >> asm_rewrite_tac[]
QED

Theorem grouped_keyword_allocations_distinct:
  !specs ce sa vars sb.
    compile_create_kwarg_allocas ce specs sa = (vars,sb) ==>
    ALL_DISTINCT (MAP (\(_,op,_,_). op) vars) /\
    !name op ty e. MEM (name,op,ty,e) vars ==>
      ?n. sa.cs_next_var <= n /\ op = Var (STRING #"%" (toString n))
Proof
  Induct >- simp[compile_create_kwarg_allocas_def, comp_return_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[compile_create_kwarg_allocas_def, comp_bind_def, comp_return_def] >>
  Cases_on `compile_alloc_buffer (type_memory_bytes ce h1) sa` >>
  Cases_on `compile_create_kwarg_allocas ce specs r` >>
  disch_then (map_every assume_tac o CONJUNCTS) >> gvs[] >>
  drule abi_builtin_alloc_buffer_shape >>
  disch_then (strip_assume_tac o MATCH_MP emitted_insts_emit_op o cj 2) >>
  qpat_assum `!ce sa vars sb. _` (drule_then strip_assume_tac) >>
  simp[] >> conj_tac
  >- (simp[MEM_MAP, pairTheory.EXISTS_PROD] >> rpt strip_tac >>
      first_x_assum (drule_then strip_assume_tac) >>
      fs[] >> metis_tac[fresh_var_distinct, arithmeticTheory.NOT_SUC_LESS_EQ]) >>
  rpt gen_tac >> disch_then (DISJ_CASES_THEN strip_assume_tac)
  >- (gvs[] >> qexists_tac `sa.cs_next_var` >> simp[]) >>
  first_x_assum (drule_then strip_assume_tac) >>
  qexists_tac `n` >> simp[] >> decide_tac
QED

val keyword_allocation = ``\ce st s G tn fn (name,op,ty,e) (id,q,b,tv).
  op = Var q /\ type_memory_bytes ce ty = type_memory_size tv /\
  not_fresh_at st q /\ lookup_var q s = SOME (n2w b) /\
  MEM (mk_inst id ALLOCA [Lit (n2w (type_memory_size tv))] [q]) (fn_insts fn) /\
  FLOOKUP s.vs_allocas id = SOME (b,type_memory_size tv) /\
  b + type_memory_size tv < dimword (:256) /\ id < st.cs_next_id /\
  ptr_covers G tn q s (type_memory_size tv)``;

Theorem grouped_keyword_allocation_slots:
  !vars tvs.
    LIST_REL (\(_,_,ty,_) tv. type_memory_bytes ce ty = type_memory_size tv) vars tvs /\
    ALL_DISTINCT (MAP (\(_,op,_,_). op) vars) /\
    fn_inst_ids_distinct fn /\
    (!name op ty e. MEM (name,op,ty,e) vars ==>
      ?id q b. op = Var q /\ not_fresh_at st q /\ lookup_var q s = SOME (n2w b) /\
        MEM (mk_inst id ALLOCA [Lit (n2w (type_memory_bytes ce ty))] [q]) (fn_insts fn) /\
        FLOOKUP s.vs_allocas id = SOME (b,type_memory_bytes ce ty) /\
        b + type_memory_bytes ce ty < dimword (:256) /\ id < st.cs_next_id /\
        ptr_covers G tn q s (type_memory_bytes ce ty)) ==>
    ?slots. ALL_DISTINCT (MAP FST slots) /\
      MAP (\(_,_,_,tv). tv) slots = tvs /\
      LIST_REL (^keyword_allocation ce st s G tn fn) vars slots
Proof
  Induct >- simp[] >>
  qx_gen_tac `arg` >> PairCases_on `arg` >> Cases_on `tvs` >- simp[] >>
  simp_tac (srw_ss()) [listTheory.LIST_REL_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!name op ty e. _`
    (qspecl_then [`arg0`,`arg1`,`arg2`,`arg3`] mp_tac) >>
  impl_tac >- simp[] >>
  disch_then (qx_choosel_then [`id`,`q`,`b`] strip_assume_tac) >>
  first_x_assum (qspec_then `t` mp_tac) >>
  impl_tac
  >- (asm_rewrite_tac[] >> rpt gen_tac >> strip_tac >>
      qpat_assum `!name op ty e. _`
        (qspecl_then [`name`,`op`,`ty`,`e`] mp_tac) >> simp[]) >>
  disch_then (qx_choose_then `slots` strip_assume_tac) >>
  gvs[] >> qexists_tac `(id,q,b,h)::slots` >> simp[] >>
  simp[MEM_MAP, MEM_EL] >> rpt strip_tac >>
  qpat_assum `LIST_REL _ _ slots` (strip_assume_tac o REWRITE_RULE [LIST_REL_EL_EQN]) >>
  rename1 `i < LENGTH slots` >>
  `i < LENGTH vars` by decide_tac >>
  `?name op ty e. EL i vars = (name,op,ty,e)` by metis_tac[pairTheory.PAIR] >>
  `?j p b' tv. EL i slots = (j,p,b',tv)` by metis_tac[pairTheory.PAIR] >>
  first_x_assum (qspec_then `i` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `EL i vars = _` (fn var_eq =>
    qpat_assum `EL i slots = _` (fn slot_eq =>
      pure_rewrite_tac [var_eq,slot_eq,pairTheory.UNCURRY,pairTheory.FST,pairTheory.SND])) >>
  disch_then (map_every assume_tac o CONJUNCTS o SIMP_RULE (srw_ss()) []) >>
  `j = id` by fs[] >>
  `p = q` by
    (mp_tac (Q.SPECL [`fn`,`mk_inst id ALLOCA [Lit (n2w (type_memory_size h))] [q]`,
        `mk_inst j ALLOCA [Lit (n2w (type_memory_size tv))] [p]`] fn_inst_ids_distinct_inj) >>
     impl_tac
     >- (conj_tac >- first_assum ACCEPT_TAC >> conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >- first_assum ACCEPT_TAC >>
         pure_rewrite_tac[mk_inst_def,instruction_accessors, instruction_accfupds, combinTheory.K_THM] >>
         qpat_assum `j = id` (ACCEPT_TAC o SYM)) >>
     disch_then (mp_tac o AP_TERM ``instruction_inst_outputs``) >>
     POP_ASSUM_LIST (K all_tac) >> asm_simp_tac bool_ss [mk_inst_def, instruction_accessors, instruction_accfupds, combinTheory.K_THM, listTheory.CONS_11]) >>
  qpat_assum `~MEM (Var q) _` (match_mp_tac o NOT_ELIM) >>
  simp_tac bool_ss [MEM_MAP] >>
  qexists_tac `(name,Var q,ty,e)` >>
  simp_tac bool_ss [pairTheory.UNCURRY, pairTheory.FST, pairTheory.SND, MEM_EL] >>
  qexists_tac `i` >> asm_rewrite_tac[]
QED

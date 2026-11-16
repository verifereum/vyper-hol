Theory calldataRegistrationTerminalBindings
Ancestors
  list entryDecodeProps entryArgPtrs vyperTypeBindArguments memoryValueEncoding
  loweringStateRelDefs venomMemDefs bodyPtrDefs localPtrsProps

Theorem registration_indexed_terminal_local_ptrs:
  bind_arguments tenv args vals = SOME envb /\
  ALL_DISTINCT (MAP FST args) /\
  LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) (MAP SND args) tvs /\
  LENGTH vals = LENGTH args /\
  (!k. ~MEM k (MAP FST args) ==> FLOOKUP cf.ce_vars k = NONE) /\
  alloca_inv t /\
  (!j. j < LENGTH args ==> ?aid q p n inst.
    MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [q] /\ inst.inst_id = aid /\
    aid < last.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (p,n) /\
    p+n < dimword(:256) /\
    FLOOKUP cf.ce_vars (FST (EL j args)) = SOME (PtrVar (Var q) n) /\
    lookup_var q t = SOME (n2w p) /\ n = type_memory_size (EL j tvs) /\
    ptr_covers Gend tnt q t n /\ val_wf (EL j tvs) (EL j vals) /\
    val_footprint (EL j tvs) (EL j vals) <= n /\
    (!mem. mem_agree_outside tnt.t_mem t.vs_memory mem ==>
      val_in_memory (EL j tvs) (EL j vals) p mem)) /\
  local_ptrs_reserved cf last /\ fn_inst_ids_distinct fn ==>
  local_ptrs_rel fn cf [envb] t
Proof
  strip_tac >> rewrite_tac[local_ptrs_rel_def] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
    `FLOOKUP envb name = SOME entry` by
      gvs[vyperStateTheory.lookup_scopes_def, AllCaseEqs()] >>
    drule_all bind_arguments_scope_lookup >> strip_tac >>
    `?j. j < LENGTH args /\ EL j args = (name,typ)` by metis_tac[MEM_EL] >>
    drule_all bind_arguments_lookup_index >> strip_tac >>
    qpat_assum `LIST_REL (\ty tv. evaluate_type _ ty = SOME tv) _ _`
      (mp_tac o SRULE [LIST_REL_EL_EQN]) >> strip_tac >>
    `evaluate_type tenv (SND (EL j args)) = SOME (EL j tvs)` by
      metis_tac[EL_MAP] >>
    qpat_x_assum `!j. j < LENGTH args ==> ?aid q p n inst. _`
      (qspec_then `j` mp_tac) >> simp[] >> strip_tac >> gvs[] >>
    `p' + type_memory_size (EL j tvs) <= t.vs_alloca_next` by
      metis_tac[alloca_inv_def, alloca_next_valid_def] >>
    `p' < dimword(:256)` by decide_tac >>
    simp[] >> conj_tac >- metis_tac[local_backed_def] >>
    irule val_in_memory_memory_value_rel >> conj_tac
    >- (drule bind_arguments_word_arg >> disch_then (qspec_then `j` mp_tac) >>
        simp[] >> metis_tac[]) >>
    first_x_assum irule >> simp[mem_agree_outside_def]) >>
  `!name b sz. local_region cf [envb] t name b sz ==>
    ?q inst. FLOOKUP cf.ce_vars name = SOME (PtrVar (Var q) sz) /\
      MEM inst (fn_insts fn) /\ inst.inst_outputs = [q] /\
      FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz)` by
    (rpt gen_tac >> simp[local_region_def] >> strip_tac >>
     `FLOOKUP envb name = SOME entry` by
       gvs[vyperStateTheory.lookup_scopes_def, AllCaseEqs()] >>
     drule_all bind_arguments_scope_lookup >> strip_tac >>
     `?j. j < LENGTH args /\ EL j args = (name,typ)` by metis_tac[MEM_EL] >>
     qpat_x_assum `!j. j < LENGTH args ==> ?aid q p n inst. _`
       (qspec_then `j` mp_tac) >> simp[] >> strip_tac >> gvs[] >>
     `p' < dimword(:256)` by decide_tac >> simp[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!name b sz. local_region _ _ _ _ _ _ ==> _`
    (qspecl_then [`n1`, `b1`, `sz1`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_assum `!name b sz. local_region _ _ _ _ _ _ ==> _`
    (qspecl_then [`n2`, `b2`, `sz2`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `q <> q'` by metis_tac[local_ptrs_reserved_def] >>
  `inst.inst_id <> inst'.inst_id` by
    (strip_tac >> `inst = inst'` by
       metis_tac[fn_inst_ids_distinct_inj] >> gvs[]) >>
  gvs[alloca_inv_def, allocas_non_overlapping_def] >>
  metis_tac[loweringStateRelDefsTheory.regions_disjoint_def]
QED

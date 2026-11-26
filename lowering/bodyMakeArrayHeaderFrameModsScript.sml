(* The deterministic length-word write preserves the linked frame at each horizon. *)
Theory bodyMakeArrayHeaderFrameMods
Ancestors
  bodyPtrMakeArrayCopyStep wordLoadStorePtr ghostPcTransportPtr
  bodyFullPostsMods bodyFullShadowBodyInv bodyInvSplit bodyPtrDefs
  exprSimAlloc exprLoweringProps loweringSlice stateRelProj loweringStateRelDefs
  ptrDiscipline venomState venomMemDefs venomMemProps valueEncodingProps
  vyperStorageTrace words arithmetic

val _ = Parse.hide "base";

Theorem make_array_header_frame_mods:
  stmt_state_rel H ctx func ce cx es s /\
  immutable_frame_mods func ce cx es s /\
  storage_well_formed_on cx es (FST H) /\
  ghost_inv_at_mods (DF H) lo d ce cx es G tn s /\
  MEM ai (fn_insts func) /\ ai.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas ai.inst_id = SOME (base,cap) /\
  lookup_var q s = SOME (n2w base) /\ ptr_covers G tn q s cap /\
  lo <= base /\ 32 <= cap /\ base + cap < dimword (:256) /\
  base + cap <= s.vs_alloca_next /\
  (!name b n. local_region ce es.scopes s name b n ==>
     loweringStateRelDefs$regions_disjoint base cap b n) /\
  ins = mk_inst id MSTORE [Var q; Lit (n2w len)] [] /\
  raw = mstore base (n2w len) s /\ t = raw with vs_inst_idx := pc /\
  g = step_prov PG G ins raw /\ tt = step_taint ins s raw tn ==>
  stmt_state_rel H ctx func ce cx es t /\
  immutable_frame_mods func ce cx es t /\
  storage_well_formed_on cx es (FST H) /\
  ghost_inv_at_mods (DF H) lo d ce cx es g tt t
Proof
  strip_tac >>
  `base < dimword (:256)` by decide_tac >>
  `!name b n. local_region ce es.scopes s name b n ==>
     b + n <= base \/ base + 32 <= b` by
    (rpt strip_tac >> qpat_assum `!name b n. _ ==> regions_disjoint _ _ b n`
       (drule_then mp_tac) >> simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  conj_tac
  >- (simp[stmt_state_rel_inst_idx] >> irule literal_mstore_state_rel >>
      reverse conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`base`,`ai`,`cap`] >> simp[] >> rpt strip_tac >>
      qpat_assum `!name b n. _ ==> regions_disjoint _ _ b n` (drule_then mp_tac) >>
      simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  conj_tac >- suspend "immutables" >>
  conj_tac >- first_assum ACCEPT_TAC >>
  suspend "ghost"
QED

Resume make_array_header_frame_mods[immutables]:
  qpat_assum `immutable_frame_mods _ _ _ _ s` mp_tac >>
  rewrite_tac[immutable_frame_mods_def, immutables_rel_mods_def,
              immutable_alloca_sep_mods_def] >> strip_tac >>
  simp[immutable_frame_mods_def, immutables_rel_mods_def, immutable_alloca_sep_mods_def] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qabbrev_tac `cs = ce with ce_module := src` >>
      `immutables_rel cs cx.txn.target cs.ce_module cs.ce_is_ctor es
         (mstore base (n2w len) s)` by
        (irule immutables_rel_mstore_alloca >> reverse conj_tac
         >- (qpat_assum `!src tops. _ ==> immutables_rel _ _ _ _ _ _`
               (drule_then (mp_tac o REWRITE_RULE[immutables_rel_def])) >>
             simp[Abbr `cs`, immutables_rel_def]) >>
         qexistsl_tac [`base`,`func`,`ai`,`cap`] >> simp[Abbr `cs`] >>
         qpat_assum `!src tops. _ ==> immutable_alloca_sep _ _ _ _ _`
           (drule_then ACCEPT_TAC)) >>
      qpat_x_assum `immutables_rel cs _ _ _ _ _` mp_tac >>
      simp[Abbr `cs`, immutables_rel_def]) >>
  rpt gen_tac >> strip_tac >>
  irule immutable_alloca_sep_fields >> qexistsl_tac [`s`,`es`] >>
  simp[local_region_def, lookup_var_def, mstore_def] >> metis_tac[]
QED

Resume make_array_header_frame_mods[ghost]:
  `eval_operand (Lit (n2w len)) s = SOME (n2w len)` by simp[eval_operand_def] >>
  `w2n (n2w base : bytes32) = base` by
    (pure_rewrite_tac[w2n_n2w] >> irule LESS_MOD >> first_assum ACCEPT_TAC) >>
  drule_all mstore_raw_ghost_frame >>
  disch_then (qspecl_then [`tn`,`id`,`PG`,`G`] mp_tac) >>
  qpat_assum `w2n (n2w base : bytes32) = base` (fn th => pure_rewrite_tac[th]) >>
  strip_tac >>
  `g = G /\ tt.t_var = tn.t_var /\ tt.t_stor = tn.t_stor /\
   tt.t_trans = tn.t_trans /\ tt.t_imm = tn.t_imm /\
   tt.t_mem = tn.t_mem DIFF {i | base <= i /\ i < base + 32}` by
    fs[w2n_n2w, LESS_MOD, op_taint_def] >>
  `ghost_inv_at (DF H) 0 d ce cx es G tn s` by
    (qpat_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ s`
       (strip_assume_tac o REWRITE_RULE[ghost_inv_at_mods_def,allocas_from_def]) >>
     simp[ghost_inv_at_def,allocas_from_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ghost_inv_at (DF H) 0 d ce cx es G tt t` by
    (simp[ghost_inv_at_inst_idx] >> irule ghost_inv_at_mstore_clean >> simp[] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >-
       (qexists_tac `func` >>
        drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >> first_assum ACCEPT_TAC) >>
     qexists_tac `tn` >> simp[op_taint_def]) >>
  `mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo s.vs_memory` by
    (simp[] >> irule mstore_mem_bytes_at_disjoint >> simp[]) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by
    simp[mstore_def] >>
  qpat_x_assum `t = raw with vs_inst_idx := pc` kall_tac >>
  qpat_x_assum `tt = step_taint _ _ _ _` kall_tac >>
  qpat_assum `ghost_inv_at _ 0 _ _ _ _ _ _ t`
    (strip_assume_tac o REWRITE_RULE[ghost_inv_at_def]) >>
  qpat_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ s`
    (strip_assume_tac o REWRITE_RULE[ghost_inv_at_mods_def]) >>
  qpat_x_assum `g = step_prov _ _ _ _` kall_tac >>
  qpat_x_assum `g = G` SUBST_ALL_TAC >>
  rewrite_tac[ghost_inv_at_mods_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (rpt strip_tac >>
     `i IN tn.t_mem` by
       (qpat_assum `tt.t_mem = _` (fn th =>
          qpat_assum `i IN tt.t_mem`
            (strip_assume_tac o REWRITE_RULE[th,pred_setTheory.IN_DIFF])) >>
        first_assum ACCEPT_TAC) >>
     qpat_assum `!i. _ ==> imm_section_dead_mods _ _ i` (drule_all_then mp_tac) >> simp[]) >>
  conj_tac >-
    (qpat_assum `tt.t_var = tn.t_var` (fn th => pure_rewrite_tac[op_taint_def,th]) >>
     qpat_assum `!x. _ ==> FLOOKUP G x = NONE /\ _`
       (ACCEPT_TAC o REWRITE_RULE[op_taint_def])) >>
  conj_tac >-
    (qpat_assum `t.vs_allocas = s.vs_allocas`
       (fn th => pure_rewrite_tac[allocas_from_def,th]) >>
     qpat_assum `allocas_from lo s` (ACCEPT_TAC o REWRITE_RULE[allocas_from_def])) >>
  simp[]
QED

Finalise make_array_header_frame_mods

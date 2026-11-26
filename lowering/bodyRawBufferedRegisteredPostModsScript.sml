(* Transport at the fixed result endpoint; no execution or ghost witness
   is selected here. Each (id,p,n) identifies a write within a live row. *)
Theory bodyRawBufferedRegisteredPostMods
Ancestors
  bodyFullPostsMods bodyFullShadowBodyInv bodyInvSplit
  bodyMethodIdScratchFrameMods bodyPtrBytestringBuiltinsWindowGhost
  allocationGrowth allocaSiteResource localPtrsProps stateRelProj
  exprLoweringProps exprSimProps loweringSlice loweringPosts loweringStateRelDefs
  bodyPtrDefs ptrDiscipline compileEnv context venomState venomInst venomMemDefs
  valueEncodingDefs finite_map alist list pair arithmetic

Theorem registered_growth_rows[local]:
  allocation_growth s u /\ FLOOKUP u.vs_allocas id = SOME (p,n) ==>
  FLOOKUP s.vs_allocas id = SOME (p,n) \/ s.vs_alloca_next <= p
Proof
  strip_tac >> Cases_on `FLOOKUP s.vs_allocas id`
  >- (disj2_tac >> drule_all_then ACCEPT_TAC allocation_growth_new) >>
  drule_all allocation_growth_old >> simp[]
QED

Theorem registered_result_windows[local]:
  local_ptrs_rel func ce es.scopes u /\ alloca_inv u /\ fn_inst_ids_distinct func /\
  allocation_growth s u /\ allocas_from lo u /\
  (!aid p n. MEM (aid,p,n) writes ==>
    ?cap inst x. FLOOKUP u.vs_allocas aid = SOME (p,cap) /\ n <= cap /\
      MEM inst (fn_insts func) /\ inst.inst_id = aid /\ inst.inst_opcode = ALLOCA /\
      inst.inst_outputs = [x] /\ not_local_ptr ce es.scopes x /\ sf.cs_next_id <= aid) /\
  (!b k. (!aid p n. MEM (aid,p,n) writes ==>
       venomMemDefs$regions_disjoint (b,k) (p,n)) ==>
     mem_bytes_at b k u.vs_memory = mem_bytes_at b k s.vs_memory /\
     (!i. b <= i /\ i < b+k /\ i IN tnf.t_mem ==> i IN tn.t_mem)) ==>
  (mem_bytes_at 0 lo u.vs_memory = mem_bytes_at 0 lo s.vs_memory /\
   (!i. i < lo /\ i IN tnf.t_mem ==> i IN tn.t_mem)) /\
  (!name b k. local_region ce es.scopes u name b k ==>
     mem_bytes_at b k u.vs_memory = mem_bytes_at b k s.vs_memory /\
     (!i. b <= i /\ i < b+k /\ i IN tnf.t_mem ==> i IN tn.t_mem)) /\
  (!id b k. FLOOKUP s.vs_allocas id = SOME (b,k) /\ id < sf.cs_next_id ==>
     mem_bytes_at b k u.vs_memory = mem_bytes_at b k s.vs_memory /\
     (!i. b <= i /\ i < b+k /\ i IN tnf.t_mem ==> i IN tn.t_mem))
Proof
  strip_tac >> conj_tac
  >- (qpat_assum `!b k. _ ==> mem_bytes_at b k u.vs_memory = _ /\ _`
        (qspecl_then [`0`,`lo`] mp_tac) >>
      impl_tac >-
        (rpt gen_tac >> disch_tac >>
         qpat_assum `!aid p n. MEM (aid,p,n) writes ==> _` (drule_then strip_assume_tac) >>
         qpat_assum `allocas_from lo u`
           (drule_then (fn th => simp[th, venomMemDefsTheory.regions_disjoint_def]) o
            REWRITE_RULE[allocas_from_def])) >>
      simp[]) >>
  conj_tac
  >- (rpt gen_tac >> disch_tac >> first_assum irule >> rpt gen_tac >> disch_tac >>
      qpat_assum `!aid p n. MEM (aid,p,n) writes ==> _` (drule_then strip_assume_tac) >>
      `loweringStateRelDefs$regions_disjoint p cap b k` by
        (irule local_ptrs_rel_alloca_disjoint >> metis_tac[]) >>
      fs[loweringStateRelDefsTheory.regions_disjoint_def,
         venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  rpt gen_tac >> strip_tac >> first_assum irule >> rpt gen_tac >> disch_tac >>
  qpat_assum `!aid p n. MEM (aid,p,n) writes ==> _` (drule_then strip_assume_tac) >>
  `FLOOKUP u.vs_allocas id = SOME (b,k)` by drule_all_then ACCEPT_TAC allocation_growth_old >>
  `id <> aid` by decide_tac >>
  drule_all alloca_site_registered_disjoint >>
  simp[venomMemDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem registered_result_immutable[local]:
  immutable_frame_mods func ce cx es s /\
  allocation_growth s u /\
  (!name b k. local_region ce es.scopes u name b k ==> local_region ce es.scopes s name b k) /\
  u.vs_data_section = s.vs_data_section /\ LENGTH s.vs_memory <= LENGTH u.vs_memory /\
  (!aid p n. MEM (aid,p,n) writes ==>
    ?cap inst. FLOOKUP u.vs_allocas aid = SOME (p,cap) /\ n <= cap /\
      MEM inst (fn_insts func) /\ inst.inst_id = aid /\ inst.inst_opcode = ALLOCA) /\
  (!b k. (!aid p n. MEM (aid,p,n) writes ==>
       venomMemDefs$regions_disjoint (b,k) (p,n)) ==>
     mem_bytes_at b k u.vs_memory = mem_bytes_at b k s.vs_memory) ==>
  immutable_frame_mods func ce cx es u
Proof
  simp[immutable_frame_mods_def, immutable_alloca_sep_mods_def, immutables_rel_mods_def] >>
  strip_tac >>
  `!src m id b n. local_region (ce with ce_module := src) es.scopes m id b n =
     local_region ce es.scopes m id b n` by simp[local_region_def] >>
  `!src tops. ALOOKUP ce.ce_modules src = SOME tops ==>
    immutable_alloca_sep func (ce with ce_module := src) cx es u` by
    (rpt gen_tac >> disch_tac >> irule immutable_alloca_sep_frame >>
     qexistsl_tac [`s`,`es`] >> simp[] >> rpt conj_tac
     >- (rpt gen_tac >> strip_tac >> disj1_tac >> qexists_tac `id` >> first_assum drule >> simp[])
     >- (rpt strip_tac >> drule_all_then ACCEPT_TAC registered_growth_rows)
     >- (drule_then ACCEPT_TAC allocation_growth_next) >>
     qpat_assum `!src tops. _ ==> immutable_alloca_sep _ _ _ _ s` (drule_then ACCEPT_TAC)) >>
  asm_rewrite_tac[] >> rpt gen_tac >> disch_tac >>
  irule immutables_rel_mem_agree >> qexists_tac `s` >> simp[] >>
  disch_tac >> rpt gen_tac >> strip_tac >>
  qpat_assum `!b k. _ ==> mem_bytes_at b k u.vs_memory = _` irule >>
  rpt gen_tac >> disch_tac >>
  qpat_assum `!aid p n. MEM (aid,p,n) writes ==> _` (drule_then strip_assume_tac) >>
  qpat_assum `!src tops. _ ==> immutable_alloca_sep _ _ _ _ u`
    (drule_then (strip_assume_tac o SIMP_RULE (srw_ss()) [immutable_alloca_sep_def])) >>
  qpat_assum `ce.ce_is_ctor ==> !name tv v off. _`
    (drule_then (drule_all_then strip_assume_tac)) >>
  qpat_assum `!inst b sz. _ ==> loweringStateRelDefs$regions_disjoint _ _ b sz`
    (qspecl_then [`inst`,`p`,`cap`] mp_tac) >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def,
       venomMemDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem registered_result_ghost[local]:
  ghost_inv_at_mods D lo dep ce cx es G tn s /\
  local_ptrs_rel func ce es.scopes s /\ local_ptrs_reserved ce sf /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sf x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sf x) /\
  (!x w. not_fresh_at sf x /\ lookup_var x s = SOME w ==> lookup_var x u = SOME w) /\
  (!x. not_fresh_at sf x ==> FLOOKUP Gf x = FLOOKUP G x /\
       op_taint tnf (Var x) = op_taint tn (Var x)) /\
  (!name p n. local_region ce es.scopes s name p n ==>
    mem_bytes_at p n u.vs_memory = mem_bytes_at p n s.vs_memory /\
    (!i. p <= i /\ i < p+n /\ i IN tnf.t_mem ==> i IN tn.t_mem)) /\
  mem_bytes_at 0 lo u.vs_memory = mem_bytes_at 0 lo s.vs_memory /\
  (!i. i < lo /\ i IN tnf.t_mem ==> i IN tn.t_mem) /\
  stor_taint_ok_at D tnf u /\ allocas_from lo u /\ lo <= u.vs_alloca_next ==>
  ghost_inv_at_mods D lo dep ce cx es Gf tnf u
Proof
  strip_tac >> drule_then assume_tac method_id_ghost_at_zero >>
  `ghost_inv_at D 0 dep ce cx es Gf tnf u` by
    (irule ghost_inv_at_local_window_transport >>
     qpat_assum `ghost_inv_at D 0 dep ce cx es G tn s` (irule_at Any) >>
     qpat_assum `local_ptrs_rel func ce es.scopes s` (irule_at Any) >>
     qpat_assum `local_ptrs_reserved ce sf` (irule_at Any) >>
     asm_rewrite_tac[] >> simp[allocas_from_def, mem_bytes_at_def]) >>
  qpat_x_assum `ghost_inv_at D 0 _ _ _ _ _ _ u`
    (strip_assume_tac o REWRITE_RULE[ghost_inv_at_def]) >>
  qpat_x_assum `ghost_inv_at_mods D lo _ _ _ _ _ _ s`
    (strip_assume_tac o REWRITE_RULE[ghost_inv_at_mods_def]) >>
  rewrite_tac[ghost_inv_at_mods_def] >> rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac
  >- (rpt strip_tac >> asm_rewrite_tac[] >>
      qpat_assum `!i. i < lo /\ i IN tn.t_mem ==> _` irule >> simp[]) >>
  conj_tac
  >- (gen_tac >> strip_tac >>
      drule_all_then assume_tac local_ptrs_reserved_imm_base >>
      qpat_assum `!x. not_fresh_at sf x ==> _` (drule_then strip_assume_tac) >>
      qpat_assum `!x. lo <> 0 /\ ce.ce_imm_alloca = SOME (Var x) ==> _`
        (drule_all_then strip_assume_tac) >> asm_rewrite_tac[]) >>
  asm_rewrite_tac[]
QED

Theorem raw_buffered_registered_post_mods:
  stmt_state_rel H ctx func ce cx es s /\
  immutable_frame_mods func ce cx es s /\ ghost_inv_at_mods D lo dep ce cx es G tn s /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sf /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sf x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sf x) /\
  (!x w. not_fresh_at sf x /\ lookup_var x s = SOME w ==> lookup_var x u = SOME w) /\
  (!x. not_fresh_at sf x ==> FLOOKUP Gf x = FLOOKUP G x /\
       op_taint tnf (Var x) = op_taint tn (Var x)) /\
  allocation_growth s u /\ LENGTH s.vs_memory <= LENGTH u.vs_memory /\
  u.vs_data_section = s.vs_data_section /\ u.vs_call_ctx = s.vs_call_ctx /\
  u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
  u.vs_immutables = s.vs_immutables /\
  tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
  (!aid p n. MEM (aid,p,n) writes ==>
    ?cap inst x. FLOOKUP u.vs_allocas aid = SOME (p,cap) /\ n <= cap /\
      MEM inst (fn_insts func) /\ inst.inst_id = aid /\ inst.inst_opcode = ALLOCA /\
      inst.inst_outputs = [x] /\ not_local_ptr ce es.scopes x /\ sf.cs_next_id <= aid) /\
  (!b k. (!aid p n. MEM (aid,p,n) writes ==>
       venomMemDefs$regions_disjoint (b,k) (p,n)) ==>
     mem_bytes_at b k u.vs_memory = mem_bytes_at b k s.vs_memory /\
     (!i. b <= i /\ i < b+k /\ i IN tnf.t_mem ==> i IN tn.t_mem)) /\
  vv_post H ctx func ce cx e es0 sf sb s0 es (Value v)
    (LocatedValue ty (mk_ptr result LocMemory)) u ==>
  vv_post_mods H ctx func ce cx e es0 sf sb s0 es (Value v)
    (LocatedValue ty (mk_ptr result LocMemory)) u /\
  ghost_inv_at_mods D lo dep ce cx es Gf tnf u
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `stmt_state_rel _ _ _ _ _ _ s`
    (strip_assume_tac o MATCH_MP stmt_state_rel_local_ptrs_alloca) >>
  `stmt_state_rel H ctx func ce cx es u` by fs[vv_post_def] >>
  qpat_assum `stmt_state_rel _ _ _ _ _ _ u`
    (strip_assume_tac o MATCH_MP stmt_state_rel_local_ptrs_alloca) >>
  `lo <= s.vs_alloca_next /\ allocas_from lo s /\ stor_taint_ok_at D tn s` by
    fs[ghost_inv_at_mods_def] >>
  `lo <= u.vs_alloca_next /\ allocas_from lo u` by
    (conj_tac >- (drule allocation_growth_next >> decide_tac) >>
     simp[allocas_from_def] >> rpt strip_tac >>
     drule_all_then strip_assume_tac registered_growth_rows
     >- (qpat_assum `allocas_from lo s`
           (drule_then ACCEPT_TAC o REWRITE_RULE[allocas_from_def])) >>
     decide_tac) >>
  drule_all_then strip_assume_tac registered_result_windows >>
  `!name b k. local_region ce es.scopes s name b k ==>
     local_region ce es.scopes u name b k` by
    (rpt strip_tac >> irule local_region_frame_fwd >>
     qexistsl_tac [`s`,`sf`,`es.scopes`] >> asm_rewrite_tac[]) >>
  `!name b k. local_region ce es.scopes u name b k ==>
     local_region ce es.scopes s name b k` by
    (rpt strip_tac >> irule local_region_frame >>
     conj_tac >- (qexists_tac `func` >> first_assum ACCEPT_TAC) >>
     qexistsl_tac [`sf`,`es.scopes`,`u`] >> asm_rewrite_tac[]) >>
  conj_tac
  >- (`immutable_frame_mods func ce cx es u` by
        (irule registered_result_immutable >> qexistsl_tac [`s`,`writes`] >>
         asm_rewrite_tac[] >> conj_tac
         >- (rpt strip_tac >>
             qpat_assum `!aid p n. MEM (aid,p,n) writes ==> _` (drule_then strip_assume_tac) >>
             qexistsl_tac [`cap`,`inst`] >> asm_rewrite_tac[]) >>
         rpt strip_tac >> first_x_assum (drule_then strip_assume_tac) >>
         first_assum ACCEPT_TAC) >>
      qhdtm_assum `vv_post` (mp_tac o REWRITE_RULE[vv_post_def]) >>
      simp[vv_post_mods_def, vv_holds_mods_def, vv_place_ptr_mods_def, mk_ptr_def,
           AC CONJ_ASSOC CONJ_COMM] >>
      strip_tac >> first_assum ACCEPT_TAC) >>
  `stor_taint_ok_at D tnf u` by fs[stor_taint_ok_at_def] >>
  irule registered_result_ghost >>
  qpat_assum `ghost_inv_at_mods D lo dep ce cx es G tn s` (irule_at Any) >>
  qpat_assum `local_ptrs_rel func ce es.scopes s` (irule_at Any) >>
  qpat_assum `local_ptrs_reserved ce sf` (irule_at Any) >>
  asm_rewrite_tac[] >> rpt strip_tac >>
  qpat_assum `!name b k. local_region ce es.scopes s name b k ==> _` (drule_then assume_tac) >>
  qpat_assum `!name b k. local_region ce es.scopes u name b k ==> _ /\ _`
    (drule_then strip_assume_tac) >> simp[]
QED

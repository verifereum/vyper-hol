(* The destination is allocated before unwrapping the captured default.
   The linked value, including its qualified immutable source, is retained
   at the endpoint of the very same allocation edge. *)
Theory bodyExtKeywordDefaultAllocMods
Ancestors
  bodyFullAllocaFresh bodyFullPostsMods bodyECAddAllocFrameMods
  bodyFullHashKeccakFixed[qualified,ignore_grammar]
  exprSimIfExpWidenedAdapter exprSimCopy exprSimVVFrame exprSimProps
  abiCallerAllocation abiCallerLocalScratch stateRelProj
  fragGasOriginPtr vyperStorageFootprint loweringPosts freshWrites
  loweringStateRelDefs bodyPtrDefs ptrDiscipline compileEnv context
  venomState venomExecSemantics finite_map words

Theorem default_alloc_holds[local]:
  vv_holds_mods ce cx ty tv vv ee s /\ u.vs_memory = s.vs_memory /\
  contract_storage u = contract_storage s /\
  contract_transient u = contract_transient s /\
  eval_operand (vv_operand vv) u = eval_operand (vv_operand vv) s ==>
  vv_holds_mods ce cx ty tv vv ee u
Proof
  Cases_on `vv`
  >- (simp[vv_holds_mods_def] >> metis_tac[vv_holds_vars_frame]) >>
  rename1 `LocatedValue tag p` >> Cases_on `p.ptr_location = LocCode`
  >- (simp[vv_operand_def, vv_holds_mods_def, immutable_holds_mods_def] >>
      strip_tac >> simp[] >> qexistsl [`src`,`tops`] >> simp[] >>
      drule immutable_holds_memory_cong >> disch_then (fn th => simp[th])) >>
  simp[vv_holds_mods_def] >> metis_tac[vv_holds_vars_frame]
QED

Theorem default_alloc_place[local]:
  vv_place_ptr_mods ce cx ee s tv vv /\
  eval_operand (vv_operand vv) u = eval_operand (vv_operand vv) s /\
  (!id x n w. FLOOKUP ce.ce_vars id = SOME (PtrVar (Var x) n) /\
              lookup_var x s = SOME w ==> lookup_var x u = SOME w) ==>
  vv_place_ptr_mods ce cx ee u tv vv
Proof
  strip_tac >>
  `!ce'. ce'.ce_vars = ce.ce_vars /\ vv_place_ptr ce' cx ee s tv vv ==>
         vv_place_ptr ce' cx ee u tv vv` by
    (rpt strip_tac >> irule vv_place_ptr_vars_frame >> qexists `s` >>
     simp[] >> first_assum ACCEPT_TAC) >>
  Cases_on `tv`
  >- (Cases_on `vv` >> fs[vv_place_ptr_mods_def] >> metis_tac[]) >>
  TRY (rename1 `PlaceR pl` >> Cases_on `pl` >> Cases_on `vv` >>
       fs[vv_place_ptr_mods_def] >> metis_tac[]) >>
  Cases_on `vv` >> fs[vv_place_ptr_mods_def] >> metis_tac[]
QED

Theorem default_alloc_vv[local]:
  vv_post_mods H ctx func ce cx e es sa sm s0 ee tv vv s /\
  stmt_state_rel H ctx func ce cx ee u /\ immutable_frame_mods func ce cx ee u /\
  u.vs_memory = s.vs_memory /\ contract_storage u = contract_storage s /\
  contract_transient u = contract_transient s /\
  eval_operand (vv_operand vv) u = eval_operand (vv_operand vv) s /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
  (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
  (!id b n. local_region ce ee.scopes u id b n <=> local_region ce ee.scopes s id b n) /\
  (!id x n w. FLOOKUP ce.ce_vars id = SOME (PtrVar (Var x) n) /\
    lookup_var x s = SOME w ==> lookup_var x u = SOME w) ==>
  vv_post_mods H ctx func ce cx e es sa sm s0 ee tv vv u
Proof
  strip_tac >> fs[vv_post_mods_def] >> rpt conj_tac
  >- (irule default_alloc_holds >> qexists `s` >> simp[])
  >- (irule vv_at_alloc_mono_frame >> qexistsl [`s`,`sm`] >> simp[])
  >- (irule default_alloc_place >> qexists `s` >> simp[] >> first_assum ACCEPT_TAC)
  >- (strip_tac >> irule vv_own_alloc_mono_frame >> qexistsl [`s`,`sm`] >> simp[])
  >- (Cases_on `vv` >> fs[vv_storage_live_def, vv_operand_def])
  >- metis_tac[]
  >- (irule locals_kept_mem_tail >> qexists `s` >> simp[]) >>
  strip_tac >> irule pure_frame_mem_tail >> qexists `s` >> simp[]
QED

Theorem default_alloc_caller_kept[local]:
  stmt_state_rel H0 ctx func cenv cx es s0 /\
  ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
  sa.cs_next_var <= sm.cs_next_var /\ lo <= s.vs_alloca_next /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  (!x. not_fresh_at sm x ==> FLOOKUP Ga x = FLOOKUP G x /\
                           op_taint ta (Var x) = op_taint tn (Var x)) /\
  (!i. i IN ta.t_mem <=> i IN tn.t_mem \/ (s.vs_alloca_next <= i /\ i < stop)) ==>
  ghost_kept_at lo cenv es sa Gi ti s0 Ga ta
Proof
  strip_tac >> drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  `!aid b len. FLOOKUP s0.vs_allocas aid = SOME (b,len) ==>
      b + len <= s.vs_alloca_next` by
    (rpt strip_tac >> irule arithmeticTheory.LESS_EQ_TRANS >>
     qexists `s0.vs_alloca_next` >> simp[] >> irule abi_caller_allocation_end >>
     simp[] >> qexistsl [`len`,`aid`,`b`] >> simp[]) >>
  `!name b len. local_region cenv es.scopes s0 name b len ==>
      b + len <= s.vs_alloca_next` by
    (rpt strip_tac >> irule arithmeticTheory.LESS_EQ_TRANS >>
     qexists `s0.vs_alloca_next` >> simp[] >> irule abi_caller_local_end >>
     qexistsl [`cenv`,`func`,`name`,`es.scopes`] >> simp[]) >>
  irule alloc_buffer_ghost_kept_at >> qexistsl [`G`,`stop`,`s`,`tn`] >> simp[] >>
  metis_tac[not_fresh_at_mono]
QED

Theorem ext_kw_default_alloc_mods:
  compile_alloc_buffer n sm = (buf,sn) /\ fn_has_code sm sn func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sm /\
  n < dimword (:256) /\ sa.cs_next_var <= sm.cs_next_var /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     vv_post_mods H ctx func cenv cx e es sa sm s0 ee tv vv s /\
     ghost_inv_at_mods (DF H) lo d cenv cx ee G tn s) /\
  stmt_state_rel H0 ctx func cenv cx es s0 /\
  ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  alloca_history func s /\ allocas_from lo s /\
  lo <= s.vs_alloca_next /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?q w u Ga ta.
    buf.buf_operand = Var q /\ not_fresh_at sn q /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
           (s,G,tn) [] (OK u,Ga,ta)) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       vv_post_mods H ctx func cenv cx e es sa sm s0 ee tv vv u /\
       ghost_inv_at_mods (DF H) lo d cenv cx ee Ga ta u) /\
    ghost_kept_at lo cenv es sa Gi ti s0 Ga ta /\
    ~u.vs_halted /\ u.vs_current_bb = sn.cs_current_bb /\
    u.vs_inst_idx = LENGTH sn.cs_current_insts /\
    u with <| vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
              vs_alloca_next := s.vs_alloca_next;
              vs_inst_idx := s.vs_inst_idx |> = s /\
    u.vs_memory = s.vs_memory /\
    alloca_history func u /\ allocas_from lo u /\
    s.vs_alloca_next <= u.vs_alloca_next /\
    s0.vs_alloca_next <= u.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    lookup_var q u = SOME w /\ ptr_covers Ga ta q u n /\
    FLOOKUP u.vs_allocas sm.cs_next_id = SOME (w2n w,n) /\
    FLOOKUP Ga q = SOME (w2n w,n) /\
    w2n w + n < dimword (:256) /\ w2n w + n <= u.vs_alloca_next /\
    (!aid ent. FLOOKUP s.vs_allocas aid = SOME ent ==>
               FLOOKUP u.vs_allocas aid = SOME ent) /\
    (!aid b len. aid < sm.cs_next_id /\
                 FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
                 regions_disjoint (w2n w) n b len) /\
    (!name b len. local_region cenv ee.scopes u name b len ==>
                  regions_disjoint (w2n w) n b len) /\
    ta.t_stor = tn.t_stor /\ ta.t_trans = tn.t_trans /\ ta.t_imm = tn.t_imm /\
    (!i. i IN ta.t_mem <=>
         i IN tn.t_mem \/ (s.vs_alloca_next <= i /\ i < w2n w + n)) /\
    (!x. not_fresh_at sm x ==>
         lookup_var x u = lookup_var x s /\ FLOOKUP Ga x = FLOOKUP G x /\
         op_taint ta (Var x) = op_taint tn (Var x)) /\
    eval_operand (vv_operand vv) u = eval_operand (vv_operand vv) s /\
    op_prov Ga (vv_operand vv) = op_prov G (vv_operand vv) /\
    op_taint ta (vv_operand vv) = op_taint tn (vv_operand vv) /\
    (!i. i < s.vs_alloca_next ==> (i IN ta.t_mem <=> i IN tn.t_mem))
Proof
  strip_tac >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace)
                  ctx func cenv cx ee s` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> _`
      (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
     impl_tac >- fs[storage_trace_domain_def] >> simp[vv_post_mods_def]) >>
  drule_then assume_tac bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp >>
  drule_all (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``]
    alloc_buffer_origin_ptr_path_with_raw_endpoint) >>
  disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`]
    (qx_choosel_then [`q`,`w`,`u`,`Ga`,`ta`,`raw`] strip_assume_tac)) >>
  `u.vs_halted = s.vs_halted /\ u.vs_memory = s.vs_memory /\
   contract_storage u = contract_storage s /\
   contract_transient u = contract_transient s` by
    (qpat_assum `u with <| vs_vars := _; vs_allocas := _;
       vs_alloca_next := _; vs_inst_idx := _ |> = s` (SUBST1_TAC o SYM) >>
     simp[contract_storage_def, contract_transient_def]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by metis_tac[not_fresh_at_mono] >>
  `eval_operand (vv_operand vv) u = eval_operand (vv_operand vv) s /\
   op_prov Ga (vv_operand vv) = op_prov G (vv_operand vv) /\
   op_taint ta (vv_operand vv) = op_taint tn (vv_operand vv)` by
    (Cases_on `vv_operand vv` >> simp[eval_operand_def, op_prov_def, op_taint_def] >>
     qpat_assum `u with <| vs_vars := _; vs_allocas := _;
       vs_alloca_next := _; vs_inst_idx := _ |> = s` (SUBST1_TAC o SYM) >> simp[]) >>
  `!id b k. local_region cenv ee.scopes u id b k <=>
            local_region cenv ee.scopes s id b k` by
    (rpt gen_tac >> irule copy_buffer_local_region_frame >> qexists `sm` >> simp[]) >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace)
                  ctx func cenv cx ee u` by
    (qpat_assum `!K. stmt_state_rel K ctx func cenv cx ee s ==> _`
      (qspec_then `storage_trace_horizon ee.storage_trace` (drule_then ACCEPT_TAC))) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp u)` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ ee u`
       (mp_tac o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) >>
     simp[]) >>
  `ghost_kept_at lo cenv es sa Gi ti s0 Ga ta` by
    (irule default_alloc_caller_kept >>
     (conj_tac >- goal_assum (drule_at Any)) >>
     qexistsl [`G`,`s`,`sm`,`w2n w + n`,`tn`] >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     vv_post_mods H ctx func cenv cx e es sa sm s0 ee tv vv u /\
     ghost_inv_at_mods (DF H) lo d cenv cx ee Ga ta u` by suspend "linked_post" >>
  qpat_x_assum `u = raw with vs_inst_idx := _` kall_tac >>
  qpat_x_assum `!id b k. local_region _ _ u id b k <=> _` kall_tac >>
  `s0.vs_alloca_next <= u.vs_alloca_next` by decide_tac >>
  `!i. i < s.vs_alloca_next ==> (i IN ta.t_mem <=> i IN tn.t_mem)` by
    (gen_tac >> simp[] >> decide_tac) >>
  qexistsl [`q`,`w`,`u`,`Ga`,`ta`] >> simp[] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume ext_kw_default_alloc_mods[linked_post]:
  qx_gen_tac `H` >> disch_tac >>
  qpat_assum `!K. valid_horizon _ _ K _ ==> _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  `stmt_state_rel H ctx func cenv cx ee s /\ immutable_frame_mods func cenv cx ee s` by
    fs[vv_post_mods_def] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
    (rpt strip_tac >> qpat_assum `!x. not_fresh_at sa x ==> _` irule >> metis_tac[]) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
    (rpt strip_tac >> qpat_assum `!x. not_fresh_at sa x ==> _` irule >> metis_tac[]) >>
  `immutable_frame_mods func cenv cx ee u /\ ghost_inv_at_mods (DF H) lo d cenv cx ee Ga ta u` by
    (drule_all bodyECAddAllocFrameModsTheory.ecadd_alloc_frame_mods >> simp[] >>
     rpt strip_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `u = raw with vs_inst_idx := _` kall_tac >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s` by
    (rpt strip_tac >> `not_fresh_at sm x` by simp[] >> simp[]) >>
  `!id x n w. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var x) n) /\
      lookup_var x s = SOME w ==> lookup_var x u = SOME w` by
    (rpt strip_tac >>
     `not_fresh_at sm x` by
       (qpat_x_assum `local_ptrs_reserved _ _` (strip_assume_tac o REWRITE_RULE[local_ptrs_reserved_def]) >>
        qpat_assum `!n1 n2 p sz1 sz2. _ ==> _ /\ _` (drule_then mp_tac) >>
        simp[]) >> simp[]) >>
  simp[] >> irule default_alloc_vv >> simp[] >> qexists `s` >> simp[] >>
  first_assum ACCEPT_TAC
QED

Finalise ext_kw_default_alloc_mods

(* The selected callee's optional entry scratch, at the unit's actual floor. *)
Theory bodySelectedEntryScratchMods
Ancestors
  bodyFullShadowBodyInv bodyFullAllocaFresh exprLoweringProps
  abiBufferAllocationCode compileAllocaProvenance loweringHalt
  allocationPtr allocaHistory venomMemProofs venomExecSemantics
  fragGasOriginPtrLoop fragGasOriginPtr exprPtrUnwrapAllocation
  emitHelperProps fragExecMem fragGasSeqPtr instMemFrontier memSafeRun
  localPtrsProps loweringStateRelDefs bodyPtrDefs ptrDiscipline
  venomState venomInst finite_map words

Theorem entry_scratch_alloc[local]:
  compile_alloc_buffer n sa = (buf,sb) /\ fn_has_code sa sb func /\
  alloca_room ctx func s /\ fmp_room ctx func s /\
  sa.cs_next_id NOTIN FDOM s.vs_allocas /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  alloca_inv s /\ fn_inst_ids_distinct func /\
  (!i w b sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
    i.inst_operands = [Lit w] /\ FLOOKUP s.vs_allocas i.inst_id = SOME (b,sz) ==>
    sz = w2n w) ==>
  ?u G' tn'.
    alloca_inv u /\
    (!i w b sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
      i.inst_operands = [Lit w] /\ FLOOKUP u.vs_allocas i.inst_id = SOME (b,sz) ==>
      sz = w2n w) /\
    u with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
             vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx|> = s /\
    allocas_from lo u /\ s.vs_alloca_next <= u.vs_alloca_next /\
    alloca_room ctx func u /\ fmp_room ctx func u /\ ~u.vs_halted /\
    u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (fresh_vars_wrt sa s ==> fresh_vars_wrt sb u) /\
    (!aid r. FLOOKUP s.vs_allocas aid = SOME r ==> FLOOKUP u.vs_allocas aid = SOME r) /\
    (!aid b sz. FLOOKUP u.vs_allocas aid = SOME (b,sz) /\
        FLOOKUP s.vs_allocas aid = NONE ==> s.vs_alloca_next <= b) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x u = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!i. i IN tn'.t_mem <=>
         i IN tn.t_mem \/ (s.vs_alloca_next <= i /\ i < u.vs_alloca_next)) /\
    !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,G',tn')
Proof
  strip_tac >> drule_then strip_assume_tac compile_alloc_buffer_code >>
  qabbrev_tac `out = STRING #"%" (toString sa.cs_next_var)` >>
  qabbrev_tac `w = (n2w n : 256 word)` >>
  qabbrev_tac `ins = mk_inst sa.cs_next_id ALLOCA [Lit w] [out]` >>
  `MEM ins (fn_insts func)` by
    (irule fn_has_code_current_member >>
     goal_assum (drule_at Any) >> simp[Abbr `ins`, Abbr `out`, Abbr `w`]) >>
  `s.vs_alloca_next + w2n w < dimword (:256) /\
   alloca_room ctx func (s with <|vs_allocas := s.vs_allocas |+
     (sa.cs_next_id,(s.vs_alloca_next,w2n w)); vs_alloca_next := s.vs_alloca_next + w2n w|>)` by
    (qspecl_then [`func`,`s`,`ins`,`w`,`ctx`] mp_tac alloca_room_fresh >>
     `ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit w] /\
      ins.inst_id = sa.cs_next_id` by simp[Abbr `ins`, mk_inst_def] >> simp[]) >>
  qabbrev_tac `t = update_var out (n2w s.vs_alloca_next) (s with <|
     vs_allocas := s.vs_allocas |+ (sa.cs_next_id,(s.vs_alloca_next,w2n w));
     vs_alloca_next := s.vs_alloca_next + w2n w|>)` >>
  `step_inst_base ins s = OK t` by
    (simp[Abbr `t`, Abbr `ins`, GSYM n2w_w2n] >>
     qspecl_then [`sa.cs_next_id`, `w2n w`, `out`, `s`] mp_tac step_alloca_fresh >>
     simp[FLOOKUP_DEF, w2n_lt]) >>
  qabbrev_tac `u = t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `exec_alloca ins s w = OK t` by
    simp[Abbr `ins`, Abbr `t`, mk_inst_def, exec_alloca_def, FLOOKUP_DEF] >>
  `fmp_room ctx func t` by
    (irule fmp_room_exec_alloca >> goal_assum (drule_at Any) >>
     simp[Abbr `ins`, mk_inst_def]) >>
  `fmp_room ctx func u` by
    (qspecl_then [`ctx`,`func`,`t`,`u`] mp_tac fmp_room_fields_cong >> simp[Abbr `u`]) >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
     (OK u,step_prov PG G ins t,step_taint ins s t tn)` by
    (`emitted_insts sa sb = [ins]` by simp[Abbr `ins`, Abbr `out`, Abbr `w`] >>
     rpt gen_tac >>
     `ptr_inst_ok D lo 0 ctx func G tn ins s` by
       (simp[Abbr `ins`] >> irule unwrap_alloc_ptr_check >>
        simp[] >> simp[Abbr `t`, update_var_def]) >>
     simp[NoAsms, Abbr `u`] >>
     irule emitted_origin_ptr_path >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexists_tac `sa` >>
     simp[inst_extends_def, run_inst_seq_def, run_inst_seq_mem_ok_last, inst_seq_ptr_def] >>
     simp[Abbr `ins`, mk_inst_def, is_terminator_def,
          below_frontier_no_ranges, inst_dload_in_section_def] >>
     rpt strip_tac >> Cases_on `pre` >> gvs[]) >>
  `step_prov PG G ins t = G |+ (out,(s.vs_alloca_next,w2n w)) /\
   step_taint ins s t tn = tn with <| t_mem := tn.t_mem UNION
       {i | s.vs_alloca_next <= i /\ i < s.vs_alloca_next + w2n w};
       t_var := tn.t_var |+ (out,{}) |>` by
    (qspecl_then [`sa.cs_next_id`, `w2n w`, `out`, `s`, `t`, `PG`, `G`, `tn`]
       mp_tac fresh_alloca_ghost >>
     simp[w2n_lt, FLOOKUP_DEF, Abbr `ins`]) >>
  `alloca_inv t` by metis_tac[history_base_alloca_inv] >>
  `alloca_inv u` by simp[Abbr `u`, alloca_inv_set_inst_idx] >>
  `!i v b sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
    i.inst_operands = [Lit v] /\ FLOOKUP u.vs_allocas i.inst_id = SOME (b,sz) ==>
    sz = w2n v` by
    (simp[NoAsms, Abbr `u`, Abbr `t`, update_var_def, FLOOKUP_UPDATE] >>
     rpt gen_tac >> Cases_on `i.inst_id = sa.cs_next_id` >> simp[] >> strip_tac
     >- (`i = ins` by
           (irule fn_inst_ids_distinct_inj >> conj_tac >- simp[Abbr `ins`, mk_inst_def] >>
            qexists_tac `func` >> simp[]) >> gvs[Abbr `ins`, mk_inst_def]) >>
     qpat_assum `!i w b sz. _ ==> sz = w2n w` irule >>
     goal_assum (drule_at Any) >> simp[]) >>
  qexistsl_tac [`u`,`step_prov PG G ins t`,`step_taint ins s t tn`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  simp[Abbr `u`, Abbr `t`, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
       venom_state_component_equality, op_taint_def] >>
  TRY (irule alloca_room_fields >> goal_assum (drule_at Any) >> simp[] >> NO_TAC)
  >- (fs[allocas_from_def, FLOOKUP_UPDATE, AllCaseEqs()] >> metis_tac[])
  >- (rpt strip_tac >> simp[fresh_vars_wrt_def, Abbr `out`] >> fs[fresh_vars_wrt_def])
  >- (fs[FLOOKUP_DEF] >> rw[] >> gvs[])
  >- (rw[] >> gvs[AllCaseEqs()]) >>
  rpt strip_tac >> `x <> out` by fs[Abbr `out`,not_fresh_at_def] >> simp[]
QED

(* Layout-independent clauses come from the existing allocation transport at
   floor zero. The actual linked floor and immutable mask are kept separately. *)
Theorem entry_scratch_ghost[local]:
  ghost_inv_at_mods D lo d cenv cx es G tn s /\
  local_ptrs_rel func cenv es.scopes s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==>
       lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x)) /\
  t with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
           vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx|> = s /\
  allocas_from lo t /\ s.vs_alloca_next <= t.vs_alloca_next /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
  (!i. i IN tn'.t_mem <=>
       i IN tn.t_mem \/ (s.vs_alloca_next <= i /\ i < t.vs_alloca_next)) ==>
  ghost_inv_at_mods D lo d cenv cx es G' tn' t
Proof
  strip_tac >>
  `ghost_inv_at D 0 d cenv cx es G tn s` by
    (qpat_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [ghost_inv_at_mods_def]) >>
     pure_rewrite_tac[ghost_inv_at_def] >> rpt conj_tac >>
     (first_assum ACCEPT_TAC ORELSE simp[allocas_from_def])) >>
  `ghost_inv_at D 0 d cenv cx es G' tn' t` by
    (irule alloc_buffer_ghost_inv_at_locals >> conj_tac
     >- simp[allocas_from_def] >>
     qexistsl_tac [`G`,`t.vs_alloca_next`,`func`,`s`,`sa`,`tn`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `ghost_inv_at _ _ _ _ _ _ G' _ _`
    (strip_assume_tac o SRULE [ghost_inv_at_def]) >>
  qpat_x_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ghost_inv_at_mods_def]) >>
  `t.vs_memory = s.vs_memory` by
    (qpat_assum `_ with <|vs_vars := _; vs_allocas := _;
                          vs_alloca_next := _; vs_inst_idx := _|> = s`
       (SUBST1_TAC o SYM) >> simp[]) >>
  pure_rewrite_tac[ghost_inv_at_mods_def] >> rpt conj_tac >>
  TRY (first_assum ACCEPT_TAC >> NO_TAC)
  >- (rpt strip_tac >>
      `i IN tn.t_mem` by
        (qpat_assum `!i. i IN tn'.t_mem <=> _` (qspec_then `i` mp_tac) >>
         `i < s.vs_alloca_next` by decide_tac >> simp[]) >>
      qpat_assum `t.vs_memory = s.vs_memory` (pure_rewrite_tac o single) >>
      qpat_assum `!i. i < lo /\ _ ==> imm_section_dead_mods _ _ i` irule >> simp[])
  >- (rpt strip_tac >>
      `not_fresh_at sa x` by fs[local_ptrs_reserved_def] >>
      qpat_assum `!x. not_fresh_at sa x ==> _` (drule_then strip_assume_tac) >>
      qpat_assum `!x. lo <> 0 /\ _ ==> _` (drule_all_then strip_assume_tac) >>
      simp[]) >>
  decide_tac
QED

Theorem selected_entry_scratch_run_mods:
  (sb = sa \/
   (sa.cs_next_id NOTIN FDOM s.vs_allocas /\ fn_inst_ids_distinct func /\
    fn_has_code sa sb func /\ ?n buf. compile_alloc_buffer n sa = (buf,sb))) /\
  alloca_room ctx func s /\ fmp_room ctx func s /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ alloca_inv s /\
  (!i w b sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
    i.inst_operands = [Lit w] /\ FLOOKUP s.vs_allocas i.inst_id = SOME (b,sz) ==>
    sz = w2n w) /\
  local_ptrs_rel func cenv es.scopes s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
       ghost_inv_at_mods (DF H) lo d cenv cx es G tn s) ==>
  ?u G' tn'.
    alloca_inv u /\
    (!i w b sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
      i.inst_operands = [Lit w] /\ FLOOKUP u.vs_allocas i.inst_id = SOME (b,sz) ==>
      sz = w2n w) /\
    u with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
             vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx|> = s /\
    allocas_from lo u /\ s.vs_alloca_next <= u.vs_alloca_next /\ lo <= u.vs_alloca_next /\
    alloca_room ctx func u /\ fmp_room ctx func u /\ ~u.vs_halted /\
    u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (fresh_vars_wrt sa s ==> fresh_vars_wrt sb u) /\
    (!aid r. FLOOKUP s.vs_allocas aid = SOME r ==> FLOOKUP u.vs_allocas aid = SOME r) /\
    (!aid b sz. FLOOKUP u.vs_allocas aid = SOME (b,sz) /\
        FLOOKUP s.vs_allocas aid = NONE ==> s.vs_alloca_next <= b) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x u = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!i. i IN tn'.t_mem <=>
         i IN tn.t_mem \/ (s.vs_alloca_next <= i /\ i < u.vs_alloca_next)) /\
    (sb = sa ==> u = s /\ G' = G /\ tn' = tn) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
         ghost_inv_at_mods (DF H) lo d cenv cx es G' tn' u) /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,G',tn')
Proof
  strip_tac
  >- (qexistsl_tac [`s`,`G`,`tn`] >>
      simp[venom_state_component_equality, gas_origin_ptr_path_rules] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      rpt gen_tac >> strip_tac >>
      qpat_assum `FLOOKUP s.vs_allocas _ = SOME _` mp_tac >>
      qpat_assum `FLOOKUP s.vs_allocas _ = NONE` (rewrite_tac o single) >> simp[NoAsms]) >>
  drule_all entry_scratch_alloc >>
  disch_then (qspecl_then [`tn`,`PG`,`G`] strip_assume_tac) >>
  `sb <> sa` by
    (drule compile_alloc_buffer_code >> strip_tac >> CCONTR_TAC >> gvs[]) >>
  `lo <= u.vs_alloca_next` by decide_tac >>
  qexistsl_tac [`u`,`G'`,`tn'`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  simp[]
  >- (rpt strip_tac >> irule entry_scratch_ghost >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`G`,`func`,`s`,`sa`,`tn`] >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> _` irule >> first_assum ACCEPT_TAC) >>
  first_assum MATCH_ACCEPT_TAC
QED

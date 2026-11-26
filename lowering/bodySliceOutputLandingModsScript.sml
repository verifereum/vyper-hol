(* The two-instruction output-buffer cut of an ordinary Slice. *)
Theory bodySliceOutputLandingMods
Ancestors
  bodyFullBuiltinBytestringBuffer bodyFullAllocaFresh bodyFullHashKeccakFixed
  revertReasonPrefixPtr bodyPtrBytestringBuiltinsBuffer
  abiBuiltinAllocation exprSimAlloc fragExec
  fragGasOriginPtrLoop emitHelperProps exprLoweringProps freshWrites allocaHistory
  loweringHalt ptrDiscipline bodyPtrDefs loweringStateRelDefs venomExecSemantics
  venomState venomInst finite_map words list
Libs horizonTypeLib

Theorem slice_literal_alloca_class[local]:
  step_inst_base (mk_inst id ALLOCA [Lit arg] [out]) s = OK raw /\
  FLOOKUP raw.vs_allocas aid = SOME (b,len) ==>
  FLOOKUP s.vs_allocas aid = SOME (b,len) \/ s.vs_alloca_next <= b
Proof
  strip_tac >> Cases_on `FLOOKUP s.vs_allocas id` >>
  gvs[step_inst_base_opcode_eqs, mk_inst_def, eval_operand_def,
      exec_alloca_def, AllCaseEqs(), update_var_def, FLOOKUP_UPDATE] >>
  gvs[AllCaseEqs()]
QED

Theorem slice_run_single[local]:
  run_inst_seq [inst] s = step_inst_base inst s
Proof
  Cases_on `step_inst_base inst s` >> simp[run_inst_seq_def]
QED

Theorem slice_offset_history[local]:
  emit_op ADD [Var r; Lit 32w] sm = (Var p,sd) /\
  fn_has_code sm sd func /\ sd.cs_current_bb = sm.cs_current_bb /\
  u.vs_current_bb = sm.cs_current_bb /\
  u.vs_inst_idx = LENGTH sm.cs_current_insts /\
  LENGTH sd.cs_current_insts = LENGTH sm.cs_current_insts + 1 /\
  alloca_history func u ==>
  alloca_history func (update_var p w u with vs_inst_idx := LENGTH sd.cs_current_insts)
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  drule_all fn_has_code_same_block >>
  disch_then (qx_choose_then `bb` strip_assume_tac) >>
  qpat_x_assum `!i. i < _ ==> _` (qspec_then `0` mp_tac) >>
  simp[] >> strip_tac >>
  irule alloca_history_frame >>
  qexists_tac `u with vs_inst_idx := SUC u.vs_inst_idx` >>
  simp[update_var_def] >>
  `alloca_history func (u with vs_inst_idx := SUC u.vs_inst_idx)` by
    (irule history_nonalloca_advance >> simp[] >>
     qexistsl_tac [`bb`, `mk_inst sm.cs_next_id ADD [Var r;Lit 32w]
                         [STRING #"%" (toString sm.cs_next_var)]`] >>
     simp[mk_inst_def]) >>
  gvs[]
QED

Theorem slice_local_region_idx[local]:
  local_region ce scopes (s with vs_inst_idx := j) name b len <=>
  local_region ce scopes s name b len
Proof
  simp[local_region_def,lookup_var_def]
QED

Theorem slice_output_landing_mods:
  compile_slice_out_buf N sc = ((out,data),sd) /\
  fn_has_code sc sd func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sc /\ 32 <= N /\ N < dimword (:256) /\
  stmt_state_rel H ctx func cenv cx es zb /\ alloca_history func zb /\
  allocas_from lo zb /\ lo <= zb.vs_alloca_next /\
  ~zb.vs_halted /\ zb.vs_current_bb = sc.cs_current_bb /\
  zb.vs_inst_idx = LENGTH sc.cs_current_insts ==>
  ?root dst w v G2 tn2.
    out = Var root /\ data = Var dst /\
    not_fresh_at sd root /\ not_fresh_at sd dst /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (zb,G,tn) []
       (OK v,G2,tn2)) /\
    v.vs_current_bb = sd.cs_current_bb /\
    v.vs_inst_idx = LENGTH sd.cs_current_insts /\ ~v.vs_halted /\
    v with <| vs_vars := zb.vs_vars; vs_allocas := zb.vs_allocas;
              vs_alloca_next := zb.vs_alloca_next;
              vs_inst_idx := zb.vs_inst_idx |> = zb /\
    (!H':(bool # bytes32 # type_value) list # num list.
      stmt_state_rel H' ctx func cenv cx es zb ==>
      stmt_state_rel H' ctx func cenv cx es v) /\
    alloca_history func v /\ allocas_from lo v /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp v) /\
    zb.vs_alloca_next <= v.vs_alloca_next /\
    lookup_var root v = SOME w /\ lookup_var dst v = SOME (w+32w) /\
    ptr_covers G2 tn2 root v N /\ ptr_covers G2 tn2 dst v (N-32) /\
    FLOOKUP v.vs_allocas sc.cs_next_id = SOME (w2n w,N) /\
    w2n w + N < dimword (:256) /\ w2n w + N <= v.vs_alloca_next /\
    (!aid e. FLOOKUP zb.vs_allocas aid = SOME e ==>
             FLOOKUP v.vs_allocas aid = SOME e) /\
    (!aid b len. FLOOKUP v.vs_allocas aid = SOME (b,len) ==>
                 FLOOKUP zb.vs_allocas aid = SOME (b,len) \/ zb.vs_alloca_next <= b) /\
    (!aid b len. aid < sc.cs_next_id /\
                 FLOOKUP zb.vs_allocas aid = SOME (b,len) ==>
                 regions_disjoint (w2n w) N b len) /\
    (!name b len. local_region cenv es.scopes v name b len ==>
                  regions_disjoint (w2n w) N b len) /\
    tn2.t_stor = tn.t_stor /\ tn2.t_trans = tn.t_trans /\
    tn2.t_imm = tn.t_imm /\
    (!i. i IN tn2.t_mem <=>
         i IN tn.t_mem \/ (zb.vs_alloca_next <= i /\ i < w2n w + N)) /\
    (!x. not_fresh_at sc x ==>
       lookup_var x v = lookup_var x zb /\ FLOOKUP G2 x = FLOOKUP G x /\
       op_taint tn2 (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  drule compile_slice_out_buf_compiler_parts >>
  disch_then (qx_choosel_then [`buf`,`sm`,`r`,`p`] strip_assume_tac) >>
  drule_all fn_has_code_split >> strip_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp zb` by
    (first_assum (ACCEPT_TAC o MATCH_MP stmt_state_rel_allocas_below_fmp)) >>
  drule_all (horizonTypeLib.at_horizon alloc_buffer_origin_ptr_path_with_raw_endpoint) >>
  disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`]
    (qx_choosel_then [`q`,`w`,`u`,`G1`,`tn1`,`raw`] strip_assume_tac)) >>
  `q = r` by gvs[] >> qpat_x_assum `q = r` SUBST_ALL_TAC >>
  `~u.vs_halted` by
    (qpat_assum `u with <|vs_vars := _; vs_allocas := _;
                           vs_alloca_next := _; vs_inst_idx := _|> = zb`
       (mp_tac o Q.AP_TERM `\st. st.vs_halted`) >> simp[]) >>
  `w2n w + 32 < dimword (:256)` by decide_tac >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  qpat_assum `emit_op ALLOCA _ _ = _` (mp_tac o MATCH_MP emitted_insts_emit_op) >>
  strip_tac >>
  `step_inst_base (mk_inst sc.cs_next_id ALLOCA [Lit (n2w N)] [r]) zb = OK raw` by
    (`r = STRING #"%" (toString sc.cs_next_var)` by fs[] >>
     qpat_x_assum `run_inst_seq (emitted_insts sc sm) zb = OK raw` mp_tac >>
     simp[slice_run_single]) >>
  `!aid b len. FLOOKUP u.vs_allocas aid = SOME (b,len) ==>
     FLOOKUP zb.vs_allocas aid = SOME (b,len) \/ zb.vs_alloca_next <= b` by
    (qpat_assum `u = raw with vs_inst_idx := _` SUBST1_TAC >>
     simp[] >> rpt strip_tac >> drule_all slice_literal_alloca_class >> simp[]) >>
  `stmt_state_rel H ctx func cenv cx es u` by
    (drule_all exprSimAllocTheory.buffer_alloc_code >> strip_tac >>
     drule_all exprSimAllocTheory.literal_alloc_buffer_run >>
     disch_then (qx_choosel_then [`raw'`,`w'`] strip_assume_tac) >>
     `raw' = raw` by metis_tac[optionTheory.SOME_11,exec_result_11] >>
     gvs[stmt_state_rel_inst_idx]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (first_assum (ACCEPT_TAC o MATCH_MP stmt_state_rel_allocas_below_fmp)) >>
  drule_all bytestring_data_offset_full_run >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`v`,`G2`,`tn2`] strip_assume_tac)) >>
  qpat_assum `emit_op ADD _ _ = _` (mp_tac o MATCH_MP emitted_insts_emit_op) >>
  strip_tac >>
  `!x. not_fresh_at sc x ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sc` >> simp[]) >>
  `p = STRING #"%" (toString sm.cs_next_var)` by fs[] >>
  `~not_fresh_at sm p` by
    (simp[not_fresh_at_def] >> qexists_tac `sm.cs_next_var` >> simp[]) >>
  `not_local_ptr cenv es.scopes p` by
    (fs[not_local_ptr_def, local_ptrs_reserved_def] >> metis_tac[]) >>
  `alloca_history func v` by
    (qpat_assum `v = _` SUBST1_TAC >> irule slice_offset_history >>
     simp[] >> qexistsl_tac [`r`,`sm`] >> simp[]) >>
  `v with <| vs_vars := zb.vs_vars; vs_allocas := zb.vs_allocas;
              vs_alloca_next := zb.vs_alloca_next;
              vs_inst_idx := zb.vs_inst_idx |> = zb` by
    (qpat_assum `v = _` SUBST1_TAC >>
     qpat_assum `u with <|vs_vars := _; vs_allocas := _;
                           vs_alloca_next := _; vs_inst_idx := _|> = zb` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[update_var_def,venom_state_component_equality]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (zb,G,tn) []
         (OK v,G2,tn2)` by
    (gen_tac >> irule gas_origin_ptr_path_trans >>
     qexistsl_tac [`G1`,`u`,`tn1`] >>
     conj_tac
     >- qpat_assum `!D. gas_origin_ptr_path _ (zb,G,tn) _ _`
          (qspec_then `D` ACCEPT_TAC)
     >> qpat_assum `!D. gas_origin_ptr_path _ (u,G1,tn1) _ _`
          (qspec_then `D` ACCEPT_TAC)) >>
  `not_fresh_at sd r` by
    (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sm` >> simp[]) >>
  `not_fresh_at sd p` by simp[not_fresh_at_def] >>
  `!H':(bool # bytes32 # type_value) list # num list.
      stmt_state_rel H' ctx func cenv cx es zb ==>
      stmt_state_rel H' ctx func cenv cx es v` by
    (rpt strip_tac >> qpat_assum `v = _` SUBST1_TAC >>
     pure_rewrite_tac [stmt_state_rel_inst_idx] >>
     irule stmt_state_rel_update_var >> conj_tac
     >- first_assum ACCEPT_TAC
     >> first_x_assum irule >> first_assum ACCEPT_TAC) >>
  `v.vs_allocas = u.vs_allocas /\ v.vs_alloca_next = u.vs_alloca_next /\
    (allocas_from lo v <=> allocas_from lo u) /\
    (allocas_below_fmp v <=> allocas_below_fmp u) /\
    (!name b len. local_region cenv es.scopes v name b len <=>
                  local_region cenv es.scopes u name b len)` by
    (qpat_assum `v = _` SUBST1_TAC >>
     qpat_assum `not_local_ptr cenv es.scopes p` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[allocas_from_def,allocas_below_fmp_def,slice_local_region_idx,
          local_region_update_nonlocal,update_var_def]) >>
  `!x. not_fresh_at sc x ==>
       lookup_var x v = lookup_var x zb /\ FLOOKUP G2 x = FLOOKUP G x /\
       op_taint tn2 (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >>
     `not_fresh_at sm x` by simp[] >>
     qpat_assum `!x. not_fresh_at sm x ==> _` (qspec_then `x` mp_tac) >>
     qpat_assum `!x. not_fresh_at sc x ==> lookup_var x u = _ /\ _`
       (qspec_then `x` mp_tac) >>
     simp[] >> metis_tac[]) >>
  qpat_x_assum `u = raw with vs_inst_idx := _` kall_tac >>
  qpat_x_assum `v = update_var _ _ _ with vs_inst_idx := _` kall_tac >>
  qpat_x_assum `tn1 = step_taint _ _ _ _` kall_tac >>
  qexistsl_tac [`r`,`p`,`w`,`v`,`G2`,`tn2`] >>
  asm_simp_tac bool_ss [] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theory bodyCreateDispatchAdoptMods
Ancestors
  bodyFullCreateHeld bodyFullPostsMods bodyFullShadowBodyInv
  bodyForRangeScalarFrameMods gasOutcomeFullPostMods
  bodyFullRawCallCallOrigin bodyFullUnwrapRun lowerDloadPtrCreateInterfaces
  ptrDisciplineTaintProps bodyPtrMakeArrayEmission externalEntryShape
  fragGasOriginPtr fragExec loweringShapeDefs
  venomExecSemantics builtinCreate wordArgsPtr compileEnv bodyPtrDefs
  venomInst venomState contextCodegenRel ptrSafeRun ptrDiscipline
  memSafeRun unitTransformDefs memLocDefs finite_map pred_set
  loweringStateRelDefs codegenRel vyperStorageFootprint exprLoweringProps
  vyperInterpreter vyperCreate vyperState loweringPosts exprSimDefs
  exprSimOperands exprSimMemDefs allocaHistory stateRelProj vyperTypeSystem
  bodyInvSplit convertScalarBytes vyperValue

Theorem consume_dispatch_code[local]:
  compile_create_dispatch codep len amount sop rof sm = (result,sb) /\
  fn_has_code sm sb func /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?mid out bb.
    compile_check_create_result (Var out) rof mid = (result,sb) /\
    fn_has_code mid sb func /\ ~not_fresh_at sm out /\
    s.vs_current_bb = mid.cs_current_bb /\
    SUC s.vs_inst_idx = LENGTH mid.cs_current_insts /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst sm.cs_next_id (if IS_SOME sop then CREATE2 else CREATE)
        ([amount;codep;len] ++ (case sop of NONE => [] | SOME p => [p])) [out])
Proof
  `(case sop of NONE => emit_op CREATE [amount;codep;len]
      | SOME p => emit_op CREATE2 [amount;codep;len;p]) =
    emit_op (if IS_SOME sop then CREATE2 else CREATE)
       ([amount;codep;len] ++ (case sop of NONE => [] | SOME p => [p]))` by
    (Cases_on `sop` >> simp[]) >>
  simp[compile_create_dispatch_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_check_create_result optmp rof mid = (result,sb)` >>
  `cs_extends sm mid` by
    (irule (REWRITE_RULE [fragExecTheory.cs_appends_def]
       (cj 2 fragExecTheory.cs_appends_emit_helpers)) >>
     goal_assum (drule_at Any)) >>
  `cs_extends mid sb` by
    (qspecl_then [`optmp`,`rof`,`mid`] mp_tac
       externalEntryShapeTheory.compile_check_create_result_labels >> simp[]) >>
  drule_all fragExecTheory.fn_has_code_split >> strip_tac >>
  drule_all bodyPtrMakeArrayEmissionTheory.emit_op_fetch_boundary >>
  strip_tac >> qexistsl [`mid`,`tmp`,`bb`] >> simp[] >> metis_tac[]
QED

(* The CREATE instruction reads initcode and adopts world state but does not
   write caller memory. The following cut does not require a singleton ghost. *)
Theorem consume_dispatch_edge[local]:
  ((inst.inst_opcode = CREATE /\ inst.inst_operands = [amount;bufop;len]) \/
   (inst.inst_opcode = CREATE2 /\ inst.inst_operands = [amount;bufop;len;salt] /\
    (?sw. eval_operand salt s = SOME sw))) /\
  eval_operand amount s = SOME value /\
  eval_operand bufop s = SOME off /\ eval_operand len s = SOME sz /\
  (sz <> 0w ==> ?p. bufop = Var p /\ ptr_covers G tn p s (w2n sz)) /\
  (sz <> 0w ==> w2n off + w2n sz <= s.vs_alloca_next \/
    (ctx_has_dalloca ctx /\ w2n s.vs_initial_fmp <= w2n off /\
     w2n off + w2n sz <= w2n s.vs_fmp)) /\
  EVERY (\op. op_taint tn op = {}) inst.inst_operands /\
  (!j. w2n off <= j /\ j < w2n off + w2n sz ==> j NOTIN tn.t_mem) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  stor_taint_ok_at D tn s /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\ step_inst_base inst s = OK u ==>
  gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G inst u, step_taint inst s u tn)
Proof
  strip_tac >>
  `source_memory_read_ranges inst s = [(w2n off,w2n sz)] /\
   source_memory_write_ranges inst s = [] /\
   mem_read_ops inst = SOME <|iao_ofst := bufop; iao_size := SOME len;
                              iao_max_size := SOME len|>` by
    simp[source_memory_read_ranges_def, source_memory_write_ranges_def,
         memory_range_of_operands_def, mem_read_ops_def] >>
  `access_ok lo G func inst s` by
    (simp[access_ok_def] >> rpt strip_tac >>
     `sz <> 0w` by fs[] >>
     qpat_assum `sz <> 0w ==> ?p. _` drule >> strip_tac >>
     gvs[ptr_covers_def, eval_operand_def] >> metis_tac[]) >>
  `taint_ok func tn inst s` by
    (irule ptrDisciplineTaintPropsTheory.taint_ok_clean_step >> simp[]) >>
  `ptr_inst_ok D lo 0 ctx func G tn inst s` by
    (gvs[ptr_inst_ok_def, stor_taint_ok_at_def, step_inst_non_invoke] >>
     metis_tac[]) >>
  `inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> GAS /\
   ~is_terminator inst.inst_opcode` by simp[is_terminator_def] >>
  `mem_safe_step 0 ctx inst s` by
    (Cases_on `sz = 0w` >>
     simp[mem_safe_step_non_invoke, inst_mem_below_frontier_def,
          inst_mem_below_frontiers_def, wordsTheory.w2n_eq_0] >> metis_tac[]) >>
  irule bodyFullRawCallCallOriginTheory.non_gas_mem_safe_origin_ptr_edge >> simp[]
QED

Theorem consume_linked_ghost_frame[local]:
  ghost_inv_at_mods D lo d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==>
       lookup_var x z = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
       op_taint tf (Var x) = op_taint tn (Var x)) /\
  es'.scopes = es.scopes /\ z.vs_memory = s.vs_memory /\
  z.vs_allocas = s.vs_allocas /\ z.vs_alloca_next = s.vs_alloca_next /\
  tf.t_mem = tn.t_mem /\ stor_taint_ok_at D tf z ==>
  ghost_inv_at_mods D lo d cenv cx es' Gf tf z
Proof
  strip_tac >>
  `!p sz. not_fresh_at sa p /\ ptr_covers G tn p s sz ==>
          ptr_covers Gf tf p z sz` by (rw[ptr_covers_def] >> metis_tac[]) >>
  fs[ghost_inv_at_mods_def, allocas_from_def] >>
  rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
      first_x_assum drule_all >> metis_tac[])
  >- (Cases_on `d` >> gvs[return_buf_ptr_def] >>
      rename1 `return_buf_ptr (SOME rb)` >> PairCases_on `rb` >>
      gvs[return_buf_ptr_def] >> metis_tac[]) >>
  rpt strip_tac >> gvs[local_ptrs_reserved_def] >> metis_tac[]
QED

(* World adoption clears the backend taint. Extract the unchanged caller
   fields and the output register facts directly from the stepped state. *)
Theorem consume_dispatch_fields[local]:
  ((inst.inst_opcode = CREATE /\ inst.inst_operands = [amount;bufop;len]) \/
   (inst.inst_opcode = CREATE2 /\ inst.inst_operands = [amount;bufop;len;salt] /\
    (?sw. eval_operand salt s = SOME sw))) /\
  inst.inst_outputs = [out] /\ step_inst_base inst s = OK raw /\ consume_create_outcome rq s = (result,t) /\
  raw = update_var out result t ==>
  let z = raw with vs_inst_idx := SUC s.vs_inst_idx in
  let Gf = step_prov PG G inst raw in
  let tf = step_taint inst s raw tn in
        z.vs_memory = s.vs_memory /\ z.vs_data_section = s.vs_data_section /\
    z.vs_immutables = s.vs_immutables /\
    z.vs_allocas = s.vs_allocas /\ z.vs_alloca_next = s.vs_alloca_next /\
    z.vs_current_bb = s.vs_current_bb /\ z.vs_inst_idx = SUC s.vs_inst_idx /\
    z.vs_initial_fmp = s.vs_initial_fmp /\ z.vs_fmp = s.vs_fmp /\
    z.vs_halted = s.vs_halted /\ z.vs_returndata = t.vs_returndata /\
    lookup_var out z = SOME result /\ FLOOKUP Gf out = NONE /\
    op_taint tf (Var out) = {} /\ tf.t_stor = {} /\ tf.t_trans = {} /\
    tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\
    (!x. x <> out ==> lookup_var x z = lookup_var x s /\
         FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  qabbrev_tac `z = raw with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `Gf = step_prov PG G inst raw` >>
  qabbrev_tac `tf = step_taint inst s raw tn` >>
  `MEM inst.inst_opcode [CREATE;CREATE2] /\ inst.inst_opcode <> INVOKE` by
    (qpat_assum `_ \/ _` strip_assume_tac >> simp[]) >>
  `step_inst 0 ctx inst s = OK raw` by simp[step_inst_non_invoke] >>
  `out_taint tn inst s = {}` by
    (qpat_assum `_ \/ _` strip_assume_tac >> simp[out_taint_def]) >>
  `tf = tn with <|t_var := tn.t_var |+ (out,{}); t_stor := {}; t_trans := {}|>` by
    (drule_all lowerDloadPtrCreateInterfacesTheory.dload_create_step_taint >>
     simp[Abbr `tf`, set_var_taint_def]) >>
  `Gf = DRESTRICT G (COMPL {out})` by
    gvs[Abbr `Gf`, step_prov_def, out_prov_def, set_prov_def] >>
  `t.vs_memory = s.vs_memory /\ t.vs_data_section = s.vs_data_section /\
   t.vs_immutables = s.vs_immutables /\ t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
   t.vs_current_bb = s.vs_current_bb /\ t.vs_initial_fmp = s.vs_initial_fmp /\
   t.vs_fmp = s.vs_fmp /\ t.vs_halted = s.vs_halted /\ t.vs_vars = s.vs_vars` by
    (qpat_x_assum `consume_create_outcome rq s = _`
       (once_rewrite_tac o single o
        MATCH_MP lowerDloadPtrCreateInterfacesTheory.dload_consume_create_state) >>
     simp[NoAsms]) >>
  simp[Abbr `z`, update_var_def, lookup_var_def, op_taint_def,
       finite_mapTheory.FLOOKUP_DRESTRICT, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem consume_control_frame[local]:
  let z = if rof then jump_to lbl u else u in
  (immutable_frame_mods func cenv cx (es with gas_obs := gs) z <=>
   immutable_frame_mods func cenv cx es u) /\
  (ghost_inv_at_mods D lo d cenv cx (es with gas_obs := gs) G tn z <=>
   ghost_inv_at_mods D lo d cenv cx es G tn u)
Proof
  Cases_on `rof` >>
  simp[LET_THM, immutable_frame_mods_def, immutables_rel_mods_def,
       immutable_alloca_sep_mods_def, immutables_rel_def, immutable_alloca_sep_def,
       jump_to_def, local_region_def, lookup_var_def,
       ghost_inv_at_mods_def, ptr_covers_def, stor_taint_ok_at_def, allocas_from_def] >>
  Cases_on `d` >- simp[return_buf_ptr_def] >>
  PairCases_on `x` >> simp[return_buf_ptr_def, ptr_covers_def, lookup_var_def]
QED

Theorem consume_prepend[local]:
  gas_origin_ptr_edge config start [] (OK mid,Gm,tm) /\
  gas_origin_ptr_path config (mid,Gm,tm) [] endpoint ==>
  gas_origin_ptr_path config start [] endpoint
Proof
  PairCases_on `config` >> PairCases_on `start` >> PairCases_on `endpoint` >>
  strip_tac >>
  irule (REWRITE_RULE [listTheory.APPEND]
    (Q.INST [`left` |-> `[]`,`right` |-> `[]`]
      (SPEC_ALL (cj 2 fragGasOriginPtrTheory.gas_origin_ptr_path_rules)))) >>
  goal_assum (drule_at Any) >> first_assum ACCEPT_TAC
QED

Theorem create_dispatch_consume_mods:
  compile_create_dispatch codep len amount sop rof sm = (result,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sm x) /\
  (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sm x) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee s /\
    immutable_frame_mods func cenv cx ee s /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee G tn s) /\
  wb_frame cenv es ee sa s0 s /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  outcomes_accounts_typed ee.outcomes /\
  eval_operand codep s = SOME pv /\ eval_operand len s = SOME sz /\
  (sz <> 0w ==> ?p. codep = Var p /\ ptr_covers G tn p s (w2n sz)) /\
  (sz <> 0w ==> w2n pv + w2n sz <= s.vs_alloca_next \/
    (ctx_has_dalloca ctx /\ w2n s.vs_initial_fmp <= w2n pv /\
     w2n pv + w2n sz <= w2n s.vs_fmp)) /\
  read_memory (w2n pv) (w2n sz) s = initcode /\
  (!i. w2n pv <= i /\ i < w2n pv + w2n sz ==> i NOTIN tn.t_mem) /\
  op_taint tn codep = {} /\ op_taint tn len = {} /\
  eval_operand amount s = SOME aw /\ op_taint tn amount = {} /\
  (case sop of NONE => sw = NONE | SOME op =>
     ?w. sw = SOME w /\ eval_operand op s = SOME w /\ op_taint tn op = {}) /\
  post_value_type cenv e = BaseT AddressT /\ expr_has_effect e /\
  (!tail. source (ee with gas_obs := tail) =
    if w2n sz > 2 * max_code_size then
      (INR (Error (RuntimeError "create initcode too large")),ee with gas_obs := tail)
    else
      bind (ignore_bind (check_not_static cx)
        (create_oracle_result sw (w2n aw) initcode rof))
        (read_result cx) (ee with gas_obs := tail)) /\
  w2n sz <= 2 * max_code_size /\ ~cx.txn.is_static /\ s.vs_outcomes <> [] ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0 source (ee,s,G,tn)
    (\H res ee' G' tn' t. ?v. res = INL v /\
      expr_post_mods H ctx func cenv cx e es sa sb s0 ee' v result t /\
      expr_store_bound cx (BaseT AddressT) v result t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee' G' tn' t /\
      ptr_val_ok cx (BaseT AddressT) v result G' tn' t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn')
    (\H res ee' gt r. expr_exit res r /\ halt_exit H cx ee' res r /\
       (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all consume_dispatch_code >> strip_tac >>
  qabbrev_tac `inst = mk_inst sm.cs_next_id (if IS_SOME sop then CREATE2 else CREATE)
    ([amount;codep;len] ++ (case sop of NONE => [] | SOME p => [p])) [out]` >>
  `inst.inst_outputs = [out] /\ EVERY (\op. op_taint tn op = {}) inst.inst_operands` by
    (Cases_on `sop` >> gvs[Abbr `inst`,mk_inst_def]) >>
  Q.SUBGOAL_THEN
   `((inst.inst_opcode = CREATE /\ inst.inst_operands = [amount;codep;len]) \/
    (inst.inst_opcode = CREATE2 /\ inst.inst_operands = [amount;codep;len;THE sop] /\
       ?w. eval_operand (THE sop) s = SOME w))` ASSUME_TAC
  >- (Cases_on `sop` >> gvs[Abbr `inst`,mk_inst_def]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  `ee.outcomes = SOME s.vs_outcomes /\ s.vs_call_ctx.cc_static = cx.txn.is_static /\
   alloca_inv s` by
    (qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _` (drule_then strip_assume_tac) >>
     fs[stmt_state_rel_def,state_rel_def,call_ctx_rel_def]) >>
  `step_inst_base inst s = exec_create inst s aw pv sz sw` by
    (Cases_on `sop` >> gvs[Abbr `inst`,mk_inst_def,step_inst_base_opcode_eqs,eval_operands_def]) >>
  Cases_on `s.vs_outcomes` >- fs[] >>
  rename1 `ee.outcomes = SOME (oc::rest)` >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
         stmt_state_rel H ctx func cenv cx ee s /\ storage_well_formed_on cx ee (FST H)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _` (drule_then strip_assume_tac) >> simp[]) >>
  drule_all (SIMP_RULE bool_ss [] (Q.INST [`value` |-> `w2n w`, `salt` |-> `sw`] create_paired_adoption)) >>
  disch_then (qspecl_then [`aw`,`sw`,`rof`]
    (qx_choose_then `ef` (qx_choose_then `adopted` (map_every assume_tac o CONJUNCTS)))) >>
  suspend "adopt"
QED

Resume create_dispatch_consume_mods[adopt]:
  qabbrev_tac `addr = if oc.co_success then oc.co_created else 0w` >>
  qabbrev_tac `raw = update_var out (w2w addr) adopted` >>
  `step_inst_base inst s = OK raw` by simp[] >>
  qabbrev_tac `u = raw with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `Gu = step_prov PG G inst raw` >>
  qabbrev_tac `tu = step_taint inst s raw tn` >>
  `raw = update_var out (w2w addr) adopted` by simp[Abbr `raw`] >>
  drule_all consume_dispatch_fields >>
  disch_then (qspecl_then [`tn`,`PG`,`G`] mp_tac) >>
  simp_tac bool_ss [LET_THM] >>
  map_every (fn q => qpat_assum q (fn th =>
    once_rewrite_tac [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]))
    [`Abbrev (u = _)`,`Abbrev (Gu = _)`,`Abbrev (tu = _)`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  suspend "origin"
QED

Resume create_dispatch_consume_mods[origin]:
  `!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s /\
        FLOOKUP Gu x = FLOOKUP G x /\ op_taint tu (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> `x <> out` by metis_tac[] >> simp[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
        FLOOKUP Gu x = FLOOKUP G x /\ op_taint tu (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> `not_fresh_at sm x` by metis_tac[not_fresh_at_mono] >> simp[]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gu tu` by
    (irule bodyFullUnwrapRunTheory.ghost_kept_at_clean_suffix >>
     qexistsl [`G`,`tn`] >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_edge (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gu,tu) /\
    ghost_inv_at_mods (DF H) lo d cenv cx ef Gu tu u /\
    immutable_frame_mods func cenv cx ef u` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _ /\ _ /\ _ /\ _`
       (drule_then strip_assume_tac) >>
     `allocas_from lo s /\ stor_taint_ok_at (DF H) tn s` by
       (qpat_assum `ghost_inv_at_mods _ _ _ _ _ ee G tn s` mp_tac >>
        simp_tac bool_ss [ghost_inv_at_mods_def] >> strip_tac >> simp[]) >>
     conj_tac
     >- (simp[NoAsms, Abbr `u`, Abbr `Gu`, Abbr `tu`] >> irule consume_dispatch_edge >>
         qpat_assum `inst.inst_opcode = CREATE /\ _ \/ _` (irule_at Any) >>
         qpat_assum `get_instruction _ _ = SOME inst` (irule_at Any) >>
         qpat_assum `eval_operand amount s = SOME aw` (irule_at Any) >>
         qpat_assum `eval_operand codep s = SOME pv` (irule_at Any) >>
         qpat_assum `eval_operand len s = SOME sz` (irule_at Any) >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
     `stor_taint_ok_at (DF H) tu u` by
       (qpat_assum `stor_taint_ok_at _ tn s`
          (strip_assume_tac o REWRITE_RULE [stor_taint_ok_at_def]) >>
        simp[stor_taint_ok_at_def, EMPTY_SUBSET]) >>
     conj_tac
     >- (irule consume_linked_ghost_frame >>
         qpat_assum `ghost_inv_at_mods _ _ _ _ _ ee G tn s` (irule_at Any) >>
         qpat_assum `local_ptrs_reserved cenv sm` (irule_at Any) >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
     irule immutable_frame_mods_exterior_frame >>
     qpat_assum `immutable_frame_mods _ _ _ ee s` (irule_at Any) >>
     qpat_assum `local_ptrs_reserved cenv sm` (irule_at Any) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
     rpt strip_tac >> qpat_assum `!x. not_fresh_at sm x ==> _` drule >> simp[]) >>
  suspend "check"
QED

Resume create_dispatch_consume_mods[check]:
  `allocas_from lo u /\ lo <= u.vs_alloca_next` by
    (qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> gas_origin_ptr_edge _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `ghost_inv_at_mods _ _ _ _ _ ef Gu tu u` mp_tac >>
     simp[NoAsms, ghost_inv_at_mods_def] >> strip_tac >> simp[]) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
   (ctx_has_dalloca ctx ==> u.vs_alloca_next + pending_alloca_size func u <= w2n u.vs_initial_fmp)` by
    (conj_tac
     >- (simp[allocas_below_fmp_def] >>
         qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s`
           (ACCEPT_TAC o REWRITE_RULE [allocas_below_fmp_def])) >>
     `pending_alloca_size func u = pending_alloca_size func s` by simp[pending_alloca_size_def] >>
     qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> stmt_state_rel _ _ _ _ _ ee s /\ _`
       (drule_then strip_assume_tac) >>
     drule stmt_state_rel_fmp_room >> simp[fmp_room_def] >> decide_tac) >>
  `eval_operand (Var out) u = SOME (w2w addr)` by simp[eval_operand_def] >>
  `u.vs_current_bb = mid.cs_current_bb /\ u.vs_inst_idx = LENGTH mid.cs_current_insts /\
   ~u.vs_halted` by simp[] >>
  `(rof /\ (w2w addr:bytes32) = 0w ==>
     lo <= u.vs_alloca_next /\ LENGTH u.vs_returndata < dimword (:256) /\
     (ctx_has_dalloca ctx ==> u.vs_alloca_next + pending_alloca_size func u <= w2n u.vs_initial_fmp))`
    by (strip_tac >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
        qpat_assum `u.vs_returndata = _` (once_rewrite_tac o single) >>
        qpat_assum `adopted.vs_returndata = _` (once_rewrite_tac o single) >>
        first_assum ACCEPT_TAC) >>
  `((w2w (addr:address):bytes32) = 0w) = (addr = 0w)` by
    (pure_once_rewrite_tac[GSYM wordsTheory.w2n_eq_0] >>
     simp_tac (bool_ss ++ wordsLib.SIZES_ss ++ numSimps.ARITH_ss) [wordsTheory.w2n_w2w]) >>
  drule_all create_check_result_path >>
  disch_then (qspecl_then [`explicit`,`PG`,`Gu`] mp_tac) >>
  Cases_on `rof /\ addr = 0w` >> simp_tac bool_ss [] >> simp[]
  >- suspend "revert" >>
  suspend "land"
QED

Resume create_dispatch_consume_mods[revert]:
  strip_tac >>
  `!tail. source (ee with gas_obs := tail) =
    (INR (Error (RevertData oc.co_returnData)),ef with gas_obs := tail)` by
    (gen_tac >> qpat_assum `!tail. source _ = _` (fn th => once_rewrite_tac[th]) >>
     simp[bind_def,ignore_bind_def,check_not_static_def,check_def,assert_def,return_def] >>
     qpat_x_assum `rof /\ addr = 0w` strip_assume_tac >>
     qpat_assum `!tail. create_oracle_result _ _ _ _ _ = _`
       (qspec_then `tail` (fn th =>
          qpat_assum `rof:bool` (fn hr => qpat_assum `addr = 0w` (fn hz =>
            once_rewrite_tac [REWRITE_RULE [hr,hz] th])))) >>
     simp[NoAsms]) >>
  irule gas_outcome_full_mods_exit >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`Gf`,`ef`,`Abort Revert_abort t`,`INR (Error (RevertData oc.co_returnData))`,`tf`] >>
  simp[exit_result_def,expr_exit_def,halt_exit_def, IgnAsm `ef.storage_trace = _`] >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H ef.storage_trace ==> _` (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> gas_origin_ptr_edge _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  irule consume_prepend >> goal_assum (drule_at Any) >> first_assum MATCH_ACCEPT_TAC
QED

Resume create_dispatch_consume_mods[land]:
  qmatch_goalsub_abbrev_tac `eval_operand result z = _` >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!tail. source (ee with gas_obs := tail) = (INL (AddressV addr),ef with gas_obs := tail)` by
    (gen_tac >> qpat_assum `!tail. source _ = _` (fn th => once_rewrite_tac[th]) >>
     simp[bind_def,ignore_bind_def,check_not_static_def,check_def,assert_def,return_def] >>
     `~(addr = 0w /\ rof)` by metis_tac[] >>
     qpat_assum `!tail. create_oracle_result _ _ _ _ _ = _`
       (qspec_then `tail` (fn th => qpat_assum `~(addr = 0w /\ rof)` (fn h =>
          once_rewrite_tac [REWRITE_RULE [h] th]))) >> simp[read_result_def,return_def]) >>
  irule gas_outcome_full_mods_pure >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`Gu`,`ef`,`INL (AddressV addr)`,`z`,`tu`] >>
  simp[IgnAsm `ef.storage_trace = _`] >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H ef.storage_trace ==> _` (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> gas_origin_ptr_edge _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  conj_tac >- (irule consume_prepend >> goal_assum (drule_at Any) >> first_assum MATCH_ACCEPT_TAC) >>
  `alloca_history func u` by
    (`~is_terminator inst.inst_opcode` by
       (qpat_assum `inst.inst_opcode = CREATE /\ _ \/ _` strip_assume_tac >> simp[is_terminator_def]) >>
     drule_all alloca_history_base_step >>
     simp[NoAsms, Abbr `u`] >>
     qpat_assum `~is_terminator inst.inst_opcode` (fn th => rewrite_tac[th])) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
  >- suspend "expr_post"
  >- simp[expr_store_bound_word,is_word_type_def]
  >- (Cases_on `rof` >> simp[Abbr `z`] >>
      irule alloca_history_jump >> simp[jump_to_def] >> qexists `u` >> simp[])
  >- (Cases_on `rof` >> simp[NoAsms, Abbr `z`,allocas_below_fmp_def,jump_to_def] >>
      qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp u`
        (ACCEPT_TAC o REWRITE_RULE [allocas_below_fmp_def]))
  >- (Cases_on `rof` >> simp[Abbr `z`,jump_to_def])
  >- (simp[NoAsms, Abbr `z`, SIMP_RULE bool_ss [LET_THM] consume_control_frame] >>
      first_assum ACCEPT_TAC) >>
  irule ptr_val_ok_word >> simp[is_word_type_def,op_prov_def]
QED

Resume create_dispatch_consume_mods[expr_post]:
  rewrite_tac[expr_post_mods_def] >> reverse conj_tac
  >- (simp[NoAsms, Abbr `z`, SIMP_RULE bool_ss [LET_THM] consume_control_frame] >>
      first_assum ACCEPT_TAC) >>
  `stmt_state_rel H ctx func cenv cx ef adopted` by
    (qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> request_agree _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `not_local_ptr cenv ef.scopes out` by
    (irule fresh_not_local_ptr >> qexists `sm` >> simp[]) >>
  `stmt_state_rel H ctx func cenv cx ef raw` by
    (qpat_assum `raw = _` (once_rewrite_tac o single) >>
     irule stmt_state_rel_update_var >> simp[]) >>
  `stmt_state_rel H ctx func cenv cx (ef with gas_obs := []) z` by
    (simp[NoAsms, Abbr `z`, Abbr `u`] >> Cases_on `rof` >>
     rewrite_tac[stmt_state_rel_jump_to,stmt_state_rel_inst_idx,
                 stmt_state_rel_start_gas_obs] >> first_assum ACCEPT_TAC) >>
  `storage_well_formed_on cx (ef with gas_obs := []) (FST H)` by
    (irule (iffRL storage_well_formed_on_backends) >> qexists `ef` >> simp[]) >>
  `z.vs_allocas = s.vs_allocas /\ z.vs_memory = s.vs_memory` by
    (Cases_on `rof` >> simp[Abbr `z`,jump_to_def]) >>
  `!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s` by
    (rpt strip_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> _` (drule_then strip_assume_tac) >>
     Cases_on `rof` >> simp[NoAsms, Abbr `z`,jump_to_def,lookup_var_def] >>
     qpat_assum `lookup_var x u = lookup_var x s`
       (ACCEPT_TAC o REWRITE_RULE [lookup_var_def])) >>
  `eval_operand (Var out) z = SOME (w2w addr)` by
    (qpat_assum `result = Var out` (once_rewrite_tac o single o SYM) >>
     first_assum ACCEPT_TAC) >>
  qpat_x_assum `wb_frame cenv es ee sa s0 s` mp_tac >>
  simp[expr_post_def,wb_frame_def,expr_val_rel_def,expr_val_at_def,
       expr_val_own_def,is_word_type_def,evaluate_type_def,scalar_typed_address_word,
       locals_kept_def,popped_kept_def] >>
  strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
Finalise create_dispatch_consume_mods

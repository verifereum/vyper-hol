(* The real materialization interval, with the linked ghost at unit floor. *)
Theory bodyMaterializeParamsFullMods
Ancestors
  bodyMaterializeBorrowGhostMods bodyMaterializeStackStepMods
  bodyMaterializeStackGhostMods ghostPcTransportPtr bodyFullUnwrapRun
  instSeqComposePtr fragExecMem unitTransformDefs ASCIInumbers
  bodyFullShadowBodyInv bodyPtrDefs ptrDiscipline venomState venomExecSemantics
  intCallCallee loweringStateRelDefs loweringShapeDefs words finite_map list
  venomInst exprLoweringProps fragExec fragGasSeqPtr

Theorem materialize_ghost_inst_idx[local]:
  ghost_inv_at_mods D lo d ce cx es G tn (s with vs_inst_idx := k) <=>
  ghost_inv_at_mods D lo d ce cx es G tn s
Proof
  Cases_on `d` >>
  simp[ghost_inv_at_mods_def, return_buf_ptr_def, stor_taint_ok_at_def,
       allocas_from_def, lookup_var_def] >>
  PairCases_on `x` >> simp[return_buf_ptr_def, lookup_var_def]
QED

Theorem materialize_fmp_inst_idx[local]:
  (allocas_below_fmp (s with vs_inst_idx := k) <=> allocas_below_fmp s) /\
  pending_alloca_size func (s with vs_inst_idx := k) = pending_alloca_size func s
Proof
  simp[allocas_below_fmp_def, pending_alloca_size_def]
QED

Theorem materialize_alloca_insert_keeps[local]:
  (!id r. FLOOKUP old id = SOME r ==> FLOOKUP curr id = SOME r) /\
  FLOOKUP curr key = NONE ==>
  !id r. FLOOKUP old id = SOME r ==>
         FLOOKUP (curr |+ (key,new)) id = SOME r
Proof
  strip_tac >> rpt gen_tac >> disch_tac >>
  first_x_assum drule >> Cases_on `id = key` >> simp[FLOOKUP_UPDATE]
QED

Theorem materialize_params_full_mods:
  !caps cenv st cenv' st' func env s f0 mr ctx lo d cx es PG G tn Ds explicit.
    materialize_internal_params cenv caps st = (cenv',st') /\
    fn_has_code st st' func /\
    (!i. MEM i (DROP (LENGTH st.cs_current_insts) st'.cs_current_insts) ==>
         MEM i (fn_insts func)) /\
    fn_inst_ids_distinct func /\ ALL_DISTINCT (MAP FST caps) /\
    mat_pending cenv env st s f0 mr caps /\
    (!n1 n2 b1 sz1 b2 sz2.
       n1 <> n2 /\ mr n1 = SOME (b1,sz1) /\ mr n2 = SOME (b2,sz2) ==>
       regions_disjoint b1 sz1 b2 sz2) /\
    mat_inv func cenv env st s f0 mr /\
    s.vs_alloca_next + internal_stack_size cenv (MAP (\c. (FST c,FST (SND c))) caps)
      < dimword (:256) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
      s.vs_alloca_next + pending_alloca_size func s <= w2n s.vs_initial_fmp) /\
    lo <= f0 /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts /\ es.scopes = [env] /\
    (!nm entry. FLOOKUP env nm = SOME entry ==>
       value_has_type entry.type entry.value) /\
    (!nm p sz. FLOOKUP cenv.ce_vars nm = SOME (PtrVar (Var p) sz) ==>
       not_fresh_at st p) /\
    (!x. cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at st x) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
       not_fresh_at st x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
       not_fresh_at st x) /\
    (!D. D IN Ds ==> ghost_inv_at_mods D lo d cenv cx es G tn s) /\
    EVERY (\c. op_taint tn (SND (SND c)) = {} /\
      (!p off sz entry.
         ~FST (SND c) /\ SND (SND c) = Var p /\
         FLOOKUP cenv.ce_vars (FST c) = SOME (MemLoc off sz) /\
         FLOOKUP env (FST c) = SOME entry ==>
         ptr_covers G tn p s sz /\
         !w mem. lookup_var p s = SOME w /\
           mem_agree_outside tn.t_mem s.vs_memory mem ==>
           val_in_memory entry.type entry.value (w2n w) mem)) caps ==>
    ?mat_state at_mat G' tn' code.
      st'.cs_current_bb = st.cs_current_bb /\
      st'.cs_current_insts = st.cs_current_insts ++ code /\
      run_inst_seq (DROP (LENGTH st.cs_current_insts) st'.cs_current_insts) s = OK mat_state /\
      mat_inv func cenv' env st' mat_state f0 mr /\ mat_frame st s mat_state /\
      at_mat = mat_state with vs_inst_idx := LENGTH st'.cs_current_insts /\
      ~at_mat.vs_halted /\ at_mat.vs_current_bb = st'.cs_current_bb /\
      at_mat.vs_inst_idx = LENGTH st'.cs_current_insts /\
      at_mat.vs_alloca_next = s.vs_alloca_next +
        internal_stack_size cenv (MAP (\c. (FST c,FST (SND c))) caps) /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp at_mat /\
         at_mat.vs_alloca_next + pending_alloca_size func at_mat <= w2n at_mat.vs_initial_fmp) /\
      (!aid r. FLOOKUP s.vs_allocas aid = SOME r ==> FLOOKUP at_mat.vs_allocas aid = SOME r) /\
      (!aid b sz. FLOOKUP at_mat.vs_allocas aid = SOME (b,sz) /\
                  FLOOKUP s.vs_allocas aid = NONE ==> s.vs_alloca_next <= b) /\
      (!x. not_fresh_at st x ==> FLOOKUP G' x = FLOOKUP G x /\
                                  FLOOKUP tn'.t_var x = FLOOKUP tn.t_var x) /\
      tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
      (!j. j < s.vs_alloca_next ==> (j IN tn'.t_mem <=> j IN tn.t_mem)) /\
      (!nm p sz. FLOOKUP cenv'.ce_vars nm = SOME (PtrVar (Var p) sz) ==>
         not_fresh_at st' p) /\
      (!x. cenv'.ce_imm_alloca = SOME (Var x) ==> not_fresh_at st' x) /\
      (!x sz. cenv'.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st' x) /\
      (!x sz. cenv'.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st' x) /\
      (!D. D IN Ds ==> ghost_inv_at_mods D lo d cenv' cx es G' tn' at_mat) /\
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK at_mat,G',tn'))
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `P = \ce cs todo us.
    ?code J qt.
      cs.cs_current_bb = st.cs_current_bb /\
      cs.cs_current_insts = st.cs_current_insts ++ code /\
      run_inst_seq code s = OK us /\ run_inst_seq_mem_ok code s /\
      EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
                 ~is_terminator i.inst_opcode /\ i.inst_opcode <> DALLOCA) code /\
      (!D k. inst_seq_ptr D lo ctx func PG G tn code
        (s with vs_inst_idx := k) J qt) /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp us /\
        us.vs_alloca_next + pending_alloca_size func us <= w2n us.vs_initial_fmp) /\
      st.cs_next_var <= cs.cs_next_var /\ s.vs_alloca_next <= us.vs_alloca_next /\
      (!aid r. FLOOKUP s.vs_allocas aid = SOME r ==> FLOOKUP us.vs_allocas aid = SOME r) /\
      (!aid b sz. FLOOKUP us.vs_allocas aid = SOME (b,sz) /\
                  FLOOKUP s.vs_allocas aid = NONE ==> s.vs_alloca_next <= b) /\
      (!x. not_fresh_at st x ==> FLOOKUP J x = FLOOKUP G x /\
                                FLOOKUP qt.t_var x = FLOOKUP tn.t_var x) /\
      qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
      (!j. j < s.vs_alloca_next ==> (j IN qt.t_mem <=> j IN tn.t_mem)) /\
      (!D. D IN Ds ==> ghost_inv_at_mods D lo d ce cx es J qt us) /\
      (!nm p sz. FLOOKUP ce.ce_vars nm = SOME (PtrVar (Var p) sz) ==>
         not_fresh_at cs p) /\
      (!x. ce.ce_imm_alloca = SOME (Var x) ==> not_fresh_at cs x) /\
      (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
         not_fresh_at cs x) /\
      (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
         not_fresh_at cs x) /\
      EVERY (\c. op_taint qt (SND (SND c)) = {} /\
        (!p off sz entry.
           ~FST (SND c) /\ SND (SND c) = Var p /\
           FLOOKUP ce.ce_vars (FST c) = SOME (MemLoc off sz) /\
           FLOOKUP env (FST c) = SOME entry ==>
           ptr_covers J qt p us sz /\
           !w mem. lookup_var p us = SOME w /\
             mem_agree_outside qt.t_mem us.vs_memory mem ==>
             val_in_memory entry.type entry.value (w2n w) mem)) todo` >>
  `P cenv st caps s` by
    (simp[Abbr `P`] >> qexistsl_tac [`G`, `tn`] >>
     simp[run_inst_seq_def, run_inst_seq_mem_ok_def, inst_seq_ptr_def] >>
     rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE (rpt strip_tac >> fs[]))) >>
  mp_tac (Q.SPECL [`caps`, `cenv`, `st`, `cenv'`, `st'`, `func`, `env`,
    `s`, `f0`, `mr`, `P`] materialize_run_invariant) >>
  (impl_tac >- (simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
                 conj_tac >- suspend "borrow" >> suspend "stack")) >>
  strip_tac >> suspend "finish"
QED

Resume materialize_params_full_mods[borrow]:
  map_every qx_gen_tac [`ce`, `cs`, `us`, `nm`, `p`, `tail`, `off`, `sz`] >>
  strip_tac >>
  qpat_x_assum `P ce cs _ us` mp_tac >> simp[Abbr `P`] >>
  disch_then (qx_choose_then `code` (qx_choose_then `J`
    (qx_choose_then `qt` strip_assume_tac))) >>
  qpat_assum `mat_pending ce env cs us f0 mr ((nm,F,Var p)::tail)`
    (mp_tac o REWRITE_RULE [mat_pending_def, listTheory.EVERY_DEF]) >>
  simp[] >> strip_tac >>
  rename1 `FLOOKUP env nm = SOME entry` >>
  qpat_assum `!e. FLOOKUP env nm = SOME e ==> _`
    (qspec_then `entry` (drule_then strip_assume_tac)) >>
  qexistsl_tac [`J`, `qt`] >>
  simp[NoAsms] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (gen_tac >> strip_tac >>
      qpat_assum `!D. D IN Ds ==> ghost_inv_at_mods D lo d ce cx es J qt us`
        (drule_then assume_tac) >>
      irule materialize_borrow_ghost_bind_mods >>
      conj_tac >- (qexistsl_tac [`entry`, `env`] >> simp[]) >>
      simp[])
  >- (map_every qx_gen_tac [`key`, `q`, `span`] >>
      Cases_on `key = nm` >> simp[FLOOKUP_UPDATE] >> rpt strip_tac >> gvs[] >>
      qpat_assum `!n q span. FLOOKUP ce.ce_vars n = _ ==> _` drule >> simp[])
  >> irule (SIMP_RULE (srw_ss()) [] materialize_borrow_pending_tail_mods) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume materialize_params_full_mods[stack]:
  map_every qx_gen_tac [`ce`, `cs`, `us`, `mid`, `ut`, `nm`, `p`, `tail`, `off`, `sz`] >>
  strip_tac >>
  qpat_x_assum `P ce cs _ us` mp_tac >> simp[Abbr `P`] >>
  disch_then (qx_choose_then `code` (qx_choose_then `J`
    (qx_choose_then `qt` strip_assume_tac))) >>
  suspend "stack_step"
QED

Resume materialize_params_full_mods[stack_step]:
  `us.vs_alloca_next + sz < dimword (:256)` by decide_tac >>
  drule_all (BETA_RULE (PURE_REWRITE_RULE [LET_THM] materialize_stack_step_frame_mods)) >>
  disch_then (qspecl_then [`PG`, `J`] (qx_choose_then `u` (qx_choose_then `w`
    (qx_choose_then `J2` (qx_choose_then `qt2` strip_assume_tac))))) >>
  qabbrev_tac `dst = STRING #"%" (toString cs.cs_next_var)` >>
  qabbrev_tac `a = mk_inst cs.cs_next_id ALLOCA [Lit (n2w sz)] [dst]` >>
  qabbrev_tac `i = mk_inst (cs.cs_next_id + 1) MSTORE [Var dst; Var p] []` >>
  qexistsl_tac [`code ++ [a;i]`, `J2`, `qt2`] >>
  suspend "stack_fields"
QED

Resume materialize_params_full_mods[stack_fields]:
  conj_tac >- simp[] >>
  conj_tac >- simp[APPEND_ASSOC] >>
  conj_tac >- (drule run_inst_seq_append >> simp[]) >>
  conj_tac >- (irule run_inst_seq_mem_ok_append >> simp[]) >>
  conj_tac >- simp[EVERY_APPEND, Abbr `a`, Abbr `i`, mk_inst_def, is_terminator_def] >>
  conj_tac >- suspend "stack_path" >>
  conj_tac
  >- (strip_tac >>
      qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp ut /\ _`
        (drule_then strip_assume_tac) >>
      conj_tac >- first_assum ACCEPT_TAC >> decide_tac) >>
  conj_tac >- decide_tac >>
  conj_tac >- decide_tac >>
  `FLOOKUP us.vs_allocas cs.cs_next_id = NONE` by
    (qpat_assum `mat_inv func ce env cs us f0 mr`
       (strip_assume_tac o REWRITE_RULE [mat_inv_def]) >>
     simp[FLOOKUP_DEF] >> strip_tac >>
     qpat_assum `!aid. aid IN FDOM us.vs_allocas ==> _` drule >> decide_tac) >>
  conj_tac >- suspend "stack_old_allocas" >>
  conj_tac >- suspend "stack_new_allocas" >>
  conj_tac >- suspend "stack_ghost_frame" >>
  conj_tac >- simp[] >> conj_tac >- simp[] >> conj_tac >- simp[] >>
  conj_tac
  >- (gen_tac >> disch_tac >>
      `j < us.vs_alloca_next` by decide_tac >> simp[]) >>
  conj_tac >- suspend "stack_bind" >> suspend "stack_tail"
QED

Resume materialize_params_full_mods[stack_path]:
  gen_tac >> irule inst_seq_ptr_uniform_append >>
  conj_tac >- (qexistsl_tac [`J`, `us`, `qt`] >> simp[]) >>
  qpat_assum `EVERY _ code`
    (assume_tac o SIMP_RULE std_ss [EVERY_MEM]) >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  qpat_assum `!j. MEM j code ==> _` (drule_then strip_assume_tac) >>
  first_assum ACCEPT_TAC
QED

Resume materialize_params_full_mods[stack_old_allocas]:
  qpat_assum `ut.vs_allocas = _` (pure_once_rewrite_tac o single) >>
  rpt strip_tac >> irule materialize_alloca_insert_keeps >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac `s.vs_allocas` >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume materialize_params_full_mods[stack_new_allocas]:
  rpt gen_tac >>
  qpat_assum `ut.vs_allocas = _` (pure_once_rewrite_tac o single) >>
  Cases_on `aid = cs.cs_next_id` >> simp[FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[] >>
  (decide_tac ORELSE
   qpat_assum `!aid b sz. FLOOKUP us.vs_allocas aid = SOME (b,sz) /\ _ ==> _`
     (drule_all_then ACCEPT_TAC))
QED

Resume materialize_params_full_mods[stack_ghost_frame]:
  gen_tac >> strip_tac >>
  `not_fresh_at cs x` by
    (irule loweringShapeDefsTheory.not_fresh_at_mono >> qexists_tac `st` >> simp[]) >>
  `x <> dst` by
    (qpat_assum `not_fresh_at cs x`
       (qspec_then `cs.cs_next_var` mp_tac o REWRITE_RULE [not_fresh_at_def]) >>
     simp[Abbr `dst`]) >>
  qpat_assum `!x. not_fresh_at st x ==> _` (drule_then strip_assume_tac) >>
  qpat_assum `J2 = J |+ _` (pure_once_rewrite_tac o single) >>
  qpat_assum `qt2.t_var = _` (pure_once_rewrite_tac o single) >>
  simp[FLOOKUP_UPDATE]
QED

Resume materialize_params_full_mods[stack_bind]:
  gen_tac >> strip_tac >>
  qpat_assum `!D. D IN Ds ==> ghost_inv_at_mods D lo d ce cx es J qt us`
    (drule_then assume_tac) >>
  qunabbrev_tac `a` >> qunabbrev_tac `i` >>
  irule materialize_stack_ghost_bind_mods >>
  conj_tac >- (qexists_tac `off` >> first_assum ACCEPT_TAC) >>
  goal_assum (drule_at (Pat `mat_pending _ _ _ _ _ _ (_::_)`)) >>
  goal_assum (drule_at (Pat `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `mat_inv _ (_ with ce_vars updated_by _) _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `step_inst_base _ _ = OK _`)) >>
  goal_assum (drule_at (Pat `lookup_var _ _ = SOME _`)) >>
  goal_assum (drule_at (Pat `_ = step_prov _ _ _ _`)) >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[Abbr `dst`] ORELSE decide_tac)
QED

Resume materialize_params_full_mods[stack_tail]:
  `!q. not_fresh_at cs q ==> not_fresh_at mid q` by
    (rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
     qexists_tac `cs` >> simp[]) >>
  `not_fresh_at mid dst` by
    (simp[not_fresh_at_def, Abbr `dst`, ASCIInumbersTheory.toString_inj] >>
     rpt strip_tac >> decide_tac) >>
  conj_tac
  >- (map_every qx_gen_tac [`key`, `q`, `span`] >>
      Cases_on `key = nm` >> simp[FLOOKUP_UPDATE] >> rpt strip_tac >> gvs[] >>
      qpat_assum `!n q span. FLOOKUP ce.ce_vars n = _ ==> _` drule >> simp[]) >>
  conj_tac >- (rpt strip_tac >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> metis_tac[]) >>
  `mat_pending ce env cs us f0 mr tail` by
    (qpat_assum `mat_pending ce env cs us f0 mr ((nm,T,Var p)::tail)`
       (mp_tac o REWRITE_RULE [mat_pending_def, EVERY_DEF]) >>
     simp[mat_pending_def]) >>
  `f0 <= us.vs_alloca_next` by
    (qpat_assum `mat_inv func ce env cs us f0 mr`
       (strip_assume_tac o REWRITE_RULE [mat_inv_def]) >>
     first_assum ACCEPT_TAC) >>
  irule materialize_stack_pending_tail_mods >>
  conj_tac >- (qexists_tac `p` >> simp[]) >>
  goal_assum (drule_at (Pat `mat_pending _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `EVERY _ _`)) >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[Abbr `dst`])
QED

Resume materialize_params_full_mods[finish]:
  qpat_x_assum `P cenv' st' [] t` mp_tac >> simp[Abbr `P`] >>
  disch_then (qx_choose_then `code` (qx_choose_then `J`
    (qx_choose_then `qt` strip_assume_tac))) >>
  suspend "exit_fields"
QED

Resume materialize_params_full_mods[exit_fields]:
  `~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb` by
    (qpat_assum `mat_frame st s t`
       (mp_tac o REWRITE_RULE [mat_frame_def]) >>
     strip_tac >> qpat_assum `t = _` SUBST1_TAC >> simp[]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
        (OK (t with vs_inst_idx := LENGTH st'.cs_current_insts),J,qt)` by
    suspend "exit_path" >>
  qexistsl_tac [`J`, `qt`, `code`] >>
  simp[materialize_ghost_inst_idx, materialize_fmp_inst_idx] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume materialize_params_full_mods[exit_path]:
  gen_tac >> irule bodyFullUnwrapRunTheory.emitted_origin_ptr_path >>
  conj_tac >- first_assum ACCEPT_TAC >> qexistsl_tac [`code`, `st`] >>
  qpat_assum `EVERY _ code`
    (assume_tac o SIMP_RULE std_ss [EVERY_MEM]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (rpt strip_tac >>
      `MEM i code` by simp[MEM_APPEND] >>
      qpat_assum `!j. MEM j code ==> _` (drule_then strip_assume_tac) >>
      simp[dalloca_no_wrap_def])
  >- (simp[EVERY_MEM] >> rpt strip_tac >>
      qpat_assum `!j. MEM j code ==> _` (drule_then strip_assume_tac) >>
      first_assum ACCEPT_TAC)
  >> `s with vs_inst_idx := s.vs_inst_idx = s` by (Cases_on `s` >> simp[]) >>
  qpat_assum `!D k. inst_seq_ptr D lo ctx func PG G tn code _ J qt`
    (qspecl_then [`D`, `s.vs_inst_idx`] mp_tac) >>
  pop_assum (pure_once_rewrite_tac o single) >> simp[]
QED

Finalise materialize_params_full_mods

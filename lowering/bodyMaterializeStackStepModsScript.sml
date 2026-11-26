(* The actual ALLOCA/MSTORE pair of stack parameter materialization. *)
Theory bodyMaterializeStackStepMods
Ancestors
  intCallMaterializeFull intCallCallee allocationPtr bodyPtrMakeArrayCopyStep
  exprLoweringProps loweringHalt ptrDiscipline fragExec finite_map venomState
  venomExecSemantics venomInst loweringStateRelDefs words

Theorem stack_pair_fmp[local]:
  FLOOKUP s.vs_allocas id = NONE /\ n < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [dst]) s = OK u /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [dst]) (fn_insts fn) /\
  allocas_below_fmp s /\
  s.vs_alloca_next + pending_alloca_size fn s <= w2n s.vs_initial_fmp ==>
  allocas_below_fmp (mstore s.vs_alloca_next w u) /\
  (mstore s.vs_alloca_next w u).vs_alloca_next +
    pending_alloca_size fn (mstore s.vs_alloca_next w u) <=
    w2n (mstore s.vs_alloca_next w u).vs_initial_fmp
Proof
  strip_tac >>
  qpat_assum `step_inst_base _ s = OK u`
    (assume_tac o SRULE [step_inst_base_opcode_eqs, mk_inst_def, eval_operand_def]) >>
  `u.vs_alloca_next + pending_alloca_size fn u <= w2n s.vs_initial_fmp` by
    (`u.vs_alloca_next + pending_alloca_size fn u <=
      s.vs_alloca_next + pending_alloca_size fn s` by
       (irule exec_alloca_static_charge >>
        goal_assum (drule_at Any) >> fs[mk_inst_def] >> first_assum ACCEPT_TAC) >>
     decide_tac) >>
  drule_all step_alloca_fresh >>
  disch_then (qspec_then `dst` assume_tac) >> gvs[] >>
  fs[allocas_below_fmp_def, mstore_def, update_var_def, pending_alloca_size_def] >>
  rpt strip_tac >> gvs[FLOOKUP_UPDATE, AllCaseEqs()] >>
  (decide_tac ORELSE first_x_assum drule >> simp[])
QED

Theorem stack_pair_ghost[local]:
  FLOOKUP s.vs_allocas id = NONE /\ s.vs_alloca_next + n < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [dst]) s = OK u /\
  lookup_var dst u = SOME (n2w s.vs_alloca_next) /\
  lookup_var p u = SOME w /\ dst <> p /\ op_taint qt (Var p) = {} ==>
  let a = mk_inst id ALLOCA [Lit (n2w n)] [dst];
      i = mk_inst (id + 1) MSTORE [Var dst; Var p] [];
      t = mstore s.vs_alloca_next w u;
      J2 = step_prov PG (step_prov PG J a u) i t;
      qt2 = step_taint i u t (step_taint a s u qt)
  in
    J2 = J |+ (dst,(s.vs_alloca_next,n)) /\
    qt2.t_var = qt.t_var |+ (dst,{}) /\
    qt2.t_stor = qt.t_stor /\ qt2.t_trans = qt.t_trans /\
    qt2.t_imm = qt.t_imm /\
    (!j. j < s.vs_alloca_next ==> (j IN qt2.t_mem <=> j IN qt.t_mem))
Proof
  strip_tac >>
  `n < dimword (:256) /\ s.vs_alloca_next < dimword (:256)` by decide_tac >>
  drule_all fresh_alloca_ghost >>
  disch_then (qspecl_then [`PG`, `J`, `qt`] strip_assume_tac) >>
  `eval_operand (Var p) u = SOME w` by simp[eval_operand_def] >>
  qpat_x_assum `lookup_var p u = SOME w` kall_tac >>
  drule_all mstore_raw_ghost_frame >>
  disch_then (qspecl_then [`step_taint (mk_inst id ALLOCA [Lit (n2w n)] [dst]) s u qt`,
    `id + 1`, `PG`, `step_prov PG J (mk_inst id ALLOCA [Lit (n2w n)] [dst]) u`] mp_tac) >>
  simp[LET_THM, w2n_n2w, op_taint_def, FLOOKUP_UPDATE] >>
  strip_tac >> rpt strip_tac >> simp[] >> decide_tac
QED

Theorem materialize_stack_step_frame_mods:
  !ce cs us ut nm p tail off sz f0 mr env lo ctx func PG J qt.
    let dst = STRING #"%" (toString cs.cs_next_var);
        a = mk_inst cs.cs_next_id ALLOCA [Lit (n2w sz)] [dst];
        i = mk_inst (cs.cs_next_id + 1) MSTORE [Var dst; Var p] []
    in
      mat_inv func ce env cs us f0 mr /\
      mat_pending ce env cs us f0 mr ((nm,T,Var p)::tail) /\
      FLOOKUP ce.ce_vars nm = SOME (MemLoc off sz) /\
      MEM a (fn_insts func) /\ us.vs_alloca_next + sz < dimword (:256) /\
      run_inst_seq [a;i] us = OK ut /\ mat_frame cs us ut /\
      op_taint qt (Var p) = {} /\ lo <= f0 /\
      (ctx_has_dalloca ctx ==>
         allocas_below_fmp us /\
         us.vs_alloca_next + pending_alloca_size func us <= w2n us.vs_initial_fmp) ==>
      ?u w J2 qt2.
        step_inst_base a us = OK u /\ step_inst_base i u = OK ut /\
        lookup_var p us = SOME w /\ ut = mstore us.vs_alloca_next w u /\
        u = update_var dst (n2w us.vs_alloca_next)
              (us with <|vs_allocas := us.vs_allocas |+
                   (cs.cs_next_id,(us.vs_alloca_next,sz));
                 vs_alloca_next := us.vs_alloca_next + sz|>) /\
        ut.vs_allocas = us.vs_allocas |+ (cs.cs_next_id,(us.vs_alloca_next,sz)) /\
        ut.vs_alloca_next = us.vs_alloca_next + sz /\
        J2 = step_prov PG (step_prov PG J a u) i ut /\
        qt2 = step_taint i u ut (step_taint a us u qt) /\
        run_inst_seq_mem_ok [a;i] us /\
        (!D k. inst_seq_ptr D lo ctx func PG J qt [a;i]
          (us with vs_inst_idx := k) J2 qt2) /\
        J2 = J |+ (dst,(us.vs_alloca_next,sz)) /\
        qt2.t_var = qt.t_var |+ (dst,{}) /\
        qt2.t_stor = qt.t_stor /\ qt2.t_trans = qt.t_trans /\ qt2.t_imm = qt.t_imm /\
        (!j. j < us.vs_alloca_next ==> (j IN qt2.t_mem <=> j IN qt.t_mem)) /\
        (ctx_has_dalloca ctx ==>
          allocas_below_fmp ut /\
          ut.vs_alloca_next + pending_alloca_size func ut <= w2n ut.vs_initial_fmp) /\
        mat_frame cs us ut
Proof
  rpt gen_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  qpat_assum `mat_inv _ _ _ _ _ _ _` (strip_assume_tac o REWRITE_RULE[mat_inv_def]) >>
  qpat_x_assum `mat_pending _ _ _ _ _ _ _`
    (strip_assume_tac o SRULE [mat_pending_def, listTheory.EVERY_DEF]) >>
  gvs[] >> rename1 `lookup_var p us = SOME w` >>
  `FLOOKUP us.vs_allocas cs.cs_next_id = NONE` by
    (simp[FLOOKUP_DEF] >> metis_tac[prim_recTheory.LESS_REFL]) >>
  `allocas_from lo us /\ lo <= us.vs_alloca_next` by
    (simp[allocas_from_def] >> rpt strip_tac >>
     (decide_tac ORELSE
      qpat_assum `!aid b sz. FLOOKUP _ aid = SOME (b,sz) ==> _` drule >> decide_tac)) >>
  qabbrev_tac `dst = STRING #"%" (toString cs.cs_next_var)` >>
  `dst <> p` by (fs[Abbr `dst`, not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `sz < dimword (:256) /\ us.vs_alloca_next < dimword (:256)` by decide_tac >>
  qabbrev_tac `u = update_var dst (n2w us.vs_alloca_next)
    (us with <|vs_allocas := us.vs_allocas |+
      (cs.cs_next_id,(us.vs_alloca_next,sz));
      vs_alloca_next := sz + us.vs_alloca_next|>)` >>
  `step_inst_base (mk_inst cs.cs_next_id ALLOCA [Lit (n2w sz)] [dst]) us = OK u` by
    simp[step_alloca_fresh, Abbr `u`] >>
  rename1 `lookup_var p us = SOME w` >>
  `lookup_var dst u = SOME (n2w us.vs_alloca_next) /\ lookup_var p u = SOME w` by
    fs[Abbr `u`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `step_inst_base (mk_inst (cs.cs_next_id + 1) MSTORE [Var dst; Var p] []) u =
    OK (mstore us.vs_alloca_next w u)` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def,
         eval_operand_def, w2n_n2w] >>
  `ut = mstore us.vs_alloca_next w u` by fs[run_inst_seq_def] >>
  `step_inst_base (mk_inst (cs.cs_next_id + 1) MSTORE [Var dst; Var p] []) u = OK ut` by
    fs[] >>
  `ut.vs_allocas = us.vs_allocas |+ (cs.cs_next_id,(us.vs_alloca_next,sz)) /\
   ut.vs_alloca_next = sz + us.vs_alloca_next` by
    simp[Abbr `u`, mstore_def, update_var_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp ut /\
    ut.vs_alloca_next + pending_alloca_size func ut <= w2n ut.vs_initial_fmp` by
    (strip_tac >>
     qpat_assum `ctx_has_dalloca ctx ==> _` (drule_then strip_assume_tac) >>
     qpat_assum `ut = mstore _ _ _` SUBST1_TAC >>
     drule_all stack_pair_fmp >> disch_then (qspec_then `w` ACCEPT_TAC)) >>
  simp[] >> conj_tac
  >- (irule materialize_stack_seq_mem >>
      goal_assum (drule_at Any) >> simp[]) >>
  conj_tac
  >- (rpt gen_tac >> irule materialize_stack_seq_ptr_cursors >> simp[]) >>
  match_mp_tac (GEN_ALL (SIMP_RULE std_ss [LET_THM] stack_pair_ghost)) >> simp[]
QED

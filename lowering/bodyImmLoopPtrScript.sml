(* Counted pointer-safe immutable array rounds. *)
Theory bodyImmLoopPtr
Ancestors
  bodyImmConditionPtr bodyImmPreparePtr bodyImmCopyPtr forPtrRounds
  forPtrArrayInvariant forPtrArrayFinish forPtrRangeRound forPtrRoundCleanup
  forPtrControl forPtrRangePrepare forPtrScope gasSummaryComposePtr
  whitelistForIterImmLoop whitelistForIterImmFrag bodyImmRestorePtr
  stmtSimForArrayLoop stmtSimProps exprLoweringProps exprSimWordArgs
  loweringPosts loweringStateRelDefs bodyPtrDefs stmtFragPtr compileEnv context
  emitHelper emitHelperProps stmtLoweringMono stmtSimDeclCompose
  venomInst venomState venomExecSemantics fragExec ptrDiscipline
  finite_map words list arithmetic rich_list vyperInterpreter vyperState
Libs monadsyntax

Theorem immutable_code_loop_outcome_ptr:
  dyn = (case bd of Dynamic _ => T | Fixed _ => F) /\
  (if dyn then
     compile_imm_load_word cenv.ce_is_ctor cenv.ce_imm_alloca (Lit (n2w off))
   else return (Lit (n2w (bound_length bd)))) st = (lvo,st1) /\
  p = STRING #"%" (toString st1.cs_next_var) /\
  idx = STRING #"%" (toString (st1.cs_next_var + 1)) /\
  dv = STRING #"%" (toString (st1.cs_next_var + (if dyn then 4 else 2))) /\
  ov = STRING #"%" (toString (st1.cs_next_var + (if dyn then 5 else 3))) /\
  ep = STRING #"%" (toString (st1.cs_next_var + (if dyn then 7 else 4))) /\
  h = st1.cs_next_id + (if dyn then 9 else 6) /\
  nv = STRING #"%" (toString sj.cs_next_var) /\
  toto = Var (STRING #"%" (toString (st1.cs_next_var + (if dyn then 6 else 3)))) /\
  entry = fresh_label_output "iter_entry" st1.cs_next_label /\
  cond = fresh_label_output "iter_cond" (st1.cs_next_label + 1) /\
  bod = fresh_label_output "iter_body" (st1.cs_next_label + 2) /\
  incr = fresh_label_output "iter_incr" (st1.cs_next_label + 3) /\
  exit = fresh_label_output "iter_exit" (st1.cs_next_label + 4) /\
  declare_local cenv id et st1 = (bc, st1 with cs_next_var := st1.cs_next_var + 1) /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) (type_memory_bytes cenv et)) /\
  sa.cs_current_bb = bod /\
  sa.cs_current_insts =
    [mk_inst h MUL [Var idx; Lit (n2w (elem_size_in_location cenv LocCode et))] [ov]] ++
    (if dyn then [mk_inst (h + 1) ADD [Lit 32w; Var ov]
      [STRING #"%" (toString (st1.cs_next_var + 6))]] else []) ++
    [mk_inst (h + (if dyn then 2 else 1)) ADD [Lit (n2w off); toto] [ep]] /\
  sa.cs_next_var = st1.cs_next_var + (if dyn then 8 else 5) /\
  sa.cs_next_id = h + (if dyn then 3 else 2) /\
  sa.cs_next_label = st1.cs_next_label + 5 /\
  compile_iter_elem_copy cenv (Var ep) (Var p)
    (elem_size_in_location cenv LocCode et) LocCode F et et sa = ((),sb0) /\
  same_blocks sa sb0 /\ sb0.cs_current_bb = bod /\
  sb0.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb0 /\
  ~block_is_terminated sb0 /\ sa.cs_next_var <= sb0.cs_next_var /\
  compile_stmts bc (InLoop exit incr) ty stmts sb0 = ((),sb1) /\
  emit_jmp_if_not_terminated incr sb1 = ((),sj) /\
  sj.cs_next_var = sb1.cs_next_var /\
  (~block_is_terminated sb1 ==>
    sj.cs_blocks = sb1.cs_blocks /\ sj.cs_current_bb = sb1.cs_current_bb /\
    sj.cs_current_insts = sb1.cs_current_insts ++
      [mk_inst sb1.cs_next_id JMP [Label incr] []]) /\
  cs_extends st st1 /\ cs_extends st1 sa /\ cs_extends sa sb0 /\
  cs_extends sb0 sb1 /\ cs_extends sb1 sj /\ cs_extends sj st' /\
  fn_has_code st1 sa func /\ fn_has_code sa sb0 func /\
  fn_has_code sb0 sb1 func /\ fn_has_code sb1 sj func /\ fn_has_code sj st' func /\
  lookup_block st1.cs_current_bb func.fn_blocks =
    SOME <|bb_label := st1.cs_current_bb; bb_instructions := st1.cs_current_insts ++
      [mk_inst st1.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv et))] [p];
       mk_inst (st1.cs_next_id + 1) JMP [Label entry] []]|> /\
  lookup_block entry func.fn_blocks =
    SOME <|bb_label := entry; bb_instructions :=
      [mk_inst (st1.cs_next_id + 2) ASSIGN [Lit 0w] [idx]] ++
      (if dyn then
        [mk_inst (st1.cs_next_id + 3) GT [lvo; Lit (n2w (bound_length bd))]
           [STRING #"%" (toString (st1.cs_next_var + 2))];
         mk_inst (st1.cs_next_id + 4) ISZERO
           [Var (STRING #"%" (toString (st1.cs_next_var + 2)))]
           [STRING #"%" (toString (st1.cs_next_var + 3))];
         mk_inst (st1.cs_next_id + 5) ASSERT
           [Var (STRING #"%" (toString (st1.cs_next_var + 3)))] []] else []) ++
      [mk_inst (h - 3) JMP [Label cond] []]|> /\
  lookup_block cond func.fn_blocks =
    SOME <|bb_label := cond; bb_instructions :=
      [mk_inst (h - 2) EQ [Var idx; lvo] [dv];
       mk_inst (h - 1) JNZ [Var dv; Label exit; Label bod] []]|> /\
  lookup_block incr func.fn_blocks =
    SOME <|bb_label := incr; bb_instructions :=
      [mk_inst sj.cs_next_id ADD [Var idx; Lit 1w] [nv];
       mk_inst (sj.cs_next_id + 1) ASSIGN [Var nv] [idx];
       mk_inst (sj.cs_next_id + 2) JMP [Label cond] []]|> /\
  st'.cs_current_bb = exit /\ st'.cs_current_insts = [] /\
  cenv.ce_alloca_locals /\ FLOOKUP cenv.ce_vars id = NONE /\
  local_ptrs_reserved cenv st1 /\ fn_inst_ids_distinct func /\
  evaluate_type (get_tenv cx) et = SOME tv /\
  elem_size_in_location cenv LocCode et = type_memory_size tv /\
  type_memory_bytes cenv et = type_memory_size tv /\
  0 < type_memory_size tv /\ type_memory_bytes cenv et + 64 < dimword (:256) /\
  LENGTH vs < dimword (:256) /\ copy_old_operand st1 lvo /\
  ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) \/
     cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  (!ei t j. P ei /\ stmt_state_rel ctx func cenv cx ei t /\ j < LENGTH vs ==>
    immutable_holds cenv cx et (Value (EL j vs))
      (n2w off + n2w ((if dyn then 32 else 0) + j * type_memory_size tv)) ei t) /\
  (!st0 bc sd ex inc ei j.
    declare_local cenv id et st0 = (bc,sd) /\ P ei /\
    lookup_scopes id ei.scopes = NONE /\ j < LENGTH vs ==>
    stmt_frag_ptr d ctx PG func cx (InLoop ex inc) RetQ bc
      (stmts_env bc (InLoop ex inc) ty stmts) (eval_stmts cx stmts)
      (ei with <|scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tv; value := EL j vs; popped := []|>)) :: ei.scopes;
        gas_obs := []|>)) /\
  (!ei j gs r es2. P ei /\ lookup_scopes id ei.scopes = NONE /\ j < LENGTH vs /\
    eval_stmts cx stmts (ei with <|scopes := (FEMPTY |+ (id,
      <|assignable := F; type := tv; value := EL j vs; popped := []|>)) :: ei.scopes;
      gas_obs := gs|>) = (r,es2) ==>
    (!ex inc. stmt_res_ok (InLoop ex inc) r) /\
    ?sc rest. es2.scopes = sc :: rest /\
      (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
      ((r = INL () \/ r = INR ContinueException) ==>
        P (es2 with scopes := rest) /\ lookup_scopes id rest = NONE)) ==>
  !k es s dst G tn. k <= LENGTH vs /\
    array_loop_inv ctx func cenv cx P vs id idx (Lit (n2w off)) (n2w off)
      p dst (type_memory_bytes cenv et)
      (mk_inst st1.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv et))] [p])
      cond st k es s /\
    ghost_inv d cenv cx es G tn s /\
    ptr_covers G tn p s (type_memory_bytes cenv et) /\
    FLOOKUP G idx = NONE /\ op_taint tn (Var idx) = {} /\
    eval_operand lvo s = SOME (n2w (LENGTH vs)) /\
    op_prov G lvo = NONE /\ op_taint tn lvo = {} /\
    (!x v. not_fresh_at st x /\ lookup_var x orig = SOME v ==>
      lookup_var x s = SOME v) /\
    (!x. not_fresh_at st x ==> FLOOKUP G x = FLOOKUP G0 x /\
      op_taint tn (Var x) = op_taint tn0 (Var x)) /\
    gas_admissible (eval_for cx tv id stmts (MAP Value (DROP k vs)))
      (stmt_res_ok lctx) es ==>
    gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
      (eval_for cx tv id stmts (MAP Value (DROP k vs))) (es,s,G,tn)
      (\res ee H tm t. res = INL () /\
        for_array_done_ptr ctx func cenv cx exit st orig G0 tn0 d ee H tm t)
      (\res ee gt r. ?ex. res = INR ex /\
        !tail. stmt_exit_ptr RetQ (ee with gas_obs := tail) (INR ex) gt r)

Proof
  strip_tac >>
  `sb0.cs_next_var <= sb1.cs_next_var` by
    (mp_tac (cj 2 compile_stmt_cs_mono) >> simp[cs_mono_def] >>
     disch_then drule >> simp[]) >>
  `sa.cs_next_var <= sj.cs_next_var` by decide_tac >>
  qabbrev_tac `tot = STRING #"%" (toString (st1.cs_next_var + 6))` >>
  `tot = STRING #"%" (toString (st1.cs_next_var + 6))` by simp[Abbr `tot`] >>
  drule_all immutable_register_frame >> strip_tac >>
  drule_all immutable_allocation_ready >> strip_tac >>
  `st.cs_next_var <= st1.cs_next_var` by
    (qpat_x_assum `(if dyn then _ else _) st = (lvo,st1)` mp_tac >>
     qpat_x_assum `~cenv.ce_is_ctor` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >> Cases_on `dyn` >>
     simp[contextTheory.compile_imm_load_word_def, comp_return_def,
       emit_op_def, fresh_var_def, fresh_id_def, emit_def,
       comp_bind_def, comp_ignore_bind_def] >> rpt strip_tac >> gvs[]) >>
  `!x. not_fresh_at st x ==> not_fresh_at st1 x` by
    (qpat_x_assum `st.cs_next_var <= st1.cs_next_var` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[not_fresh_at_def] >>
     metis_tac[LESS_LESS_EQ_TRANS]) >>
  rpt gen_tac >>
  `!k es s G tn. k <= LENGTH vs /\
    (array_loop_inv ctx func cenv cx P vs id idx (Lit (n2w off)) (n2w off)
      p dst (type_memory_bytes cenv et)
      (mk_inst st1.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv et))] [p])
      cond st k es s /\
    ghost_inv d cenv cx es G tn s /\
    ptr_covers G tn p s (type_memory_bytes cenv et) /\
    FLOOKUP G idx = NONE /\ op_taint tn (Var idx) = {} /\
    eval_operand lvo s = SOME (n2w (LENGTH vs)) /\
    op_prov G lvo = NONE /\ op_taint tn lvo = {} /\
    (!x v. not_fresh_at st x /\ lookup_var x orig = SOME v ==>
      lookup_var x s = SOME v) /\
    (!x. not_fresh_at st x ==> FLOOKUP G x = FLOOKUP G0 x /\
      op_taint tn (Var x) = op_taint tn0 (Var x))) /\
    gas_admissible (eval_for cx tv id stmts (MAP Value (DROP k vs)))
      (stmt_res_ok lctx) es ==>
    gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
      (eval_for cx tv id stmts (MAP Value (DROP k vs))) (es,s,G,tn)
      (\res ee H tm t. res = INL () /\
        for_array_done_ptr ctx func cenv cx exit st orig G0 tn0 d ee H tm t)
      (\res ee gt r. ?ex. res = INR ex /\
        !tail. stmt_exit_ptr RetQ (ee with gas_obs := tail) (INR ex) gt r)` suffices_by
    (disch_then (qspecl_then [`k`,`es`,`s`,`G`,`tn`] mp_tac) >> simp[]) >>
  ho_match_mp_tac eval_for_rounds_ptr >> conj_tac
  >- suspend "round" >>
  suspend "terminal"
QED

Resume immutable_code_loop_outcome_ptr[round]:
  rpt gen_tac >> strip_tac >>
  `k <> LENGTH vs` by decide_tac >>
  qpat_assum `!scs. not_local_ptr cenv scs p /\ _`
    (qspec_then `es.scopes` strip_assume_tac) >>
  `dv <> idx /\ dv <> p` by
    (qpat_assum `ALL_DISTINCT [p;idx;dv;ov;ep;nv]` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[ALL_DISTINCT] >> metis_tac[]) >>
  `(!x. lvo = Var x ==> x <> dv) /\
   (!x. not_fresh_at st x ==> x <> dv) /\
   (!z. cenv.ce_return_buf <> SOME (PtrVar (Var dv) z))` by
    (qpat_assum `copy_old_operand st1 lvo` mp_tac >>
     qpat_assum `!x. not_fresh_at st1 x ==> _` mp_tac >>
     qpat_assum `!x. not_fresh_at st x ==> not_fresh_at st1 x` mp_tac >>
     qpat_assum `!x sz. cenv.ce_return_buf = _ \/ cenv.ce_return_pc = _ ==> _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[exprSimCopyTheory.copy_old_operand_def, MEM] >> metis_tac[]) >>
  drule_all (Q.INST [`D` |-> `cx_dead cx`, `PG` |-> `PG`]
    immutable_condition_ptr) >>
  disch_then (qspec_then `PG` mp_tac) >> simp[] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr _ _ _ _ _ _ _ s _ Gc tc (OK live)` >>
  `?bb. lookup_block sb0.cs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX sb0.cs_current_insts bb.bb_instructions` by
    (irule fn_has_code_start >> qexists_tac `sb1` >> simp[]) >>
  `MEM (mk_inst st1.cs_next_id ALLOCA
    [Lit (n2w (type_memory_bytes cenv et))] [p]) (fn_insts func)` by
    (irule lookup_block_fn_insts >>
     qpat_assum `lookup_block st1.cs_current_bb _ = _` (irule_at Any) >> simp[]) >>
  mp_tac (Q.INST [`s` |-> `live`, `G` |-> `Gc`, `tn` |-> `tc`,
    `D` |-> `cx_dead cx`] immutable_body_entry_ptr_from_copy) >>
  impl_tac >- (conj_tac
    >- (rpt gen_tac >> MATCH_ACCEPT_TAC immutable_iter_copy_ptr) >>
    rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
      (qexists_tac `bb` >> conj_tac >> first_assum ACCEPT_TAC),
      (asm_rewrite_tac[] >> simp[Abbr `tot`,Abbr `live`,Abbr `Gc`,Abbr `tc`])]) >>
  disch_then (qx_choose_then `body0` (qx_choose_then `B0`
    (qx_choose_then `tB0` strip_assume_tac))) >>
  suspend "callback"
QED

Resume immutable_code_loop_outcome_ptr[callback]:
  qmatch_goalsub_abbrev_tac `gas_outcome_ptr _ _ _ _ _ _ RoundPost RoundExit` >>
  `P es /\ lookup_scopes id es.scopes = NONE` by
    (qhdtm_assum `array_loop_inv` mp_tac >> rpt (pop_assum kall_tac) >>
     simp[array_loop_inv_def]) >>
  qabbrev_tac `eb = es with <|scopes := (FEMPTY |+ (id,
    <|assignable := F; type := tv; value := EL k vs; popped := []|>))::es.scopes;
    gas_obs := []|>` >>
  `?bc'. stmts_env bc (InLoop exit incr) ty stmts sb0=(bc',sb1)` by
    (qpat_assum `compile_stmts bc (InLoop exit incr) ty stmts sb0=((),sb1)` mp_tac >>
     rpt (pop_assum kall_tac) >> rewrite_tac[compile_stmts_env] >>
     Cases_on `stmts_env bc (InLoop exit incr) ty stmts sb0` >> simp[]) >>
  `cenv_top_ext cenv bc eb.scopes` by
    (simp[Abbr `eb`] >> irule cenv_top_ext_declare_local >>
     qpat_assum `declare_local _ _ _ _ = _` (irule_at Any) >> simp[]) >>
  `bc.ce_return_buf=cenv.ce_return_buf /\ bc.ce_is_ctor=cenv.ce_is_ctor` by
    (qpat_assum `cenv_top_ext cenv bc eb.scopes` mp_tac >>
     rpt (pop_assum kall_tac) >> rewrite_tac[cenv_top_ext_def] >> strip_tac >>
     qpat_x_assum `_ with <|ce_vars := _; ce_var_type := _; ce_dynarray_capacity := _|> = _`
       (fn th => mp_tac(AP_TERM ``\c. (c.ce_return_buf,c.ce_is_ctor)`` th)) >> simp[]) >>
  `stmt_frag_ptr d ctx PG func cx (InLoop exit incr) RetQ bc
    (stmts_env bc (InLoop exit incr) ty stmts) (eval_stmts cx stmts) eb` by
    (qpat_assum `!st0 bc sd ex inc ei j. _`
       (qspecl_then [`st1`,`bc`,`st1 with cs_next_var:=st1.cs_next_var+1`,
         `exit`,`incr`,`es`,`k`] mp_tac) >> simp[Abbr `eb`]) >>
  `gas_admissible (eval_stmts cx stmts) (stmt_res_ok (InLoop exit incr)) eb` by
    (simp[gasContextTheory.gas_admissible_def,Abbr `eb`,evaluation_state_fn_updates] >>
     rpt strip_tac >> qpat_assum `!ei j gs r es2. _` drule_all >> simp[]) >>
  `not_fresh_at sb0 p /\ not_fresh_at sb0 idx /\
   (!x. lvo=Var x ==> not_fresh_at sb0 x) /\
   (!x z. bc.ce_return_buf=SOME(PtrVar(Var x)z) ==> not_fresh_at sb0 x)` by
    (rpt strip_tac >> metis_tac[not_fresh_at_mono]) >>
  `eb=(es with scopes:=(FEMPTY |+ (id,
    <|assignable:=F;type:=tv;value:=EL k vs;popped:=[]|>))::es.scopes)
      with gas_obs:=[]` by simp[Abbr `eb`] >>
  `stmt_state_rel ctx func bc cx eb body0 /\ ghost_inv d bc cx eb B0 tB0 body0` by
    (qpat_assum `eb=(_ with gas_obs:=[])` (fn th => pure_rewrite_tac[th]) >>
     pure_rewrite_tac[stmt_state_rel_gas_obs,ghost_inv_gas_obs] >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `local_ptrs_reserved bc sb0` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> asm_rewrite_tac[]) >>
  mp_tac (Q.INST [`es` |-> `eb`,`s0` |-> `body0`, `G0` |-> `B0`,
    `tn0` |-> `tB0`, `counter` |-> `n2w k`, `len` |-> `n2w(LENGTH (vs:value list))`,
    `sz` |-> `type_memory_bytes cenv et`]
    immutable_body_callback_ptr) >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    asm_rewrite_tac[]]) >>
  strip_tac >>
  dxrule for_outcome_source_evidence_ptr >> strip_tac >>
  qabbrev_tac `CleanPost = \(res:unit+exception) ee H tm t. RoundPost
    (case res of INL u => INL F | INR ex =>
      if ex=BreakException then INL T else if ex=ContinueException then INL F
      else INR ex) (ee with scopes:=TL ee.scopes) H tm t` >>
  `gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG (eval_stmts cx stmts)
    (eb,body0,B0,tB0) CleanPost
    (\res ee gt r. !tail. stmt_exit_ptr RetQ (ee with gas_obs:=tail) res gt r)` by
    (irule for_outcome_zero_suffix_ptr >> goal_assum(drule_at Any) >>
     rpt gen_tac >> simp_tac bool_ss [] >> strip_tac >> suspend "finish") >>
  suspend "assembly"
QED

Resume immutable_code_loop_outcome_ptr[finish]:
  rename1 `stmt_lands (InLoop exit incr) sb1 res u` >>
  rename1 `ghost_inv d c3 cx ee H tm u` >>
  qpat_assum `eb=(_ with gas_obs:=[])` (fn reset =>
    qpat_assum `eval_stmts cx stmts (eb with gas_obs:=obs) = (res,ee)`
      (assume_tac o SIMP_RULE (srw_ss()) [reset,evaluation_state_fupdcanon])) >>
  qpat_assum `!ei j gs r es2. _ ==> _`
    (qspecl_then [`es`,`k`,`obs`,`res`,`ee`] mp_tac) >>
  impl_tac >- asm_rewrite_tac[evaluation_state_fupdcanon] >> strip_tac >>
  `stmt_state_rel ctx func cenv cx (ee with scopes:=rest) u` by
    (mp_tac (Q.SPECL [`ctx`,`func`,`cenv`,`bc`,`c3`,`cx`,
       `eb with gas_obs:=obs`,`stmts`,`res`,`ee`,`u`,`sc`,`rest`]
       array_body_scope_projection) >>
     impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
       pure_rewrite_tac[evaluation_state_accfupds] >> first_assum ACCEPT_TAC]) >>
     disch_then ACCEPT_TAC) >>
  `ghost_inv d cenv cx (ee with scopes:=rest) H tm u` by
    (mp_tac (Q.INST [`ei` |-> `eb with gas_obs:=obs`, `r` |-> `res`,
       `G` |-> `H`, `tn` |-> `tm`, `s` |-> `u`] ghost_inv_body_scope_projection) >>
     impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
       pure_rewrite_tac[evaluation_state_accfupds] >> first_assum ACCEPT_TAC]) >>
     disch_then ACCEPT_TAC) >>
  `!x v. not_fresh_at st x /\ lookup_var x orig=SOME v ==>
      lookup_var x live=SOME v` by
    (qunabbrev_tac `live` >>
     qpat_assum `!x v. _ ==> lookup_var x (update_var _ _ s)=SOME v` mp_tac >>
     rpt(pop_assum kall_tac) >> simp[lookup_var_def,jump_to_def]) >>
  `(!x v. not_fresh_at st x /\ lookup_var x orig=SOME v ==>
      lookup_var x u=SOME v) /\
   (!x. not_fresh_at st x ==> FLOOKUP H x=FLOOKUP G0 x /\
      op_taint tm (Var x)=op_taint tn0 (Var x))` by
    (qpat_assum `st.cs_next_var <=
       (sa with cs_next_var:=st1.cs_next_var+2).cs_next_var` mp_tac >>
     qpat_assum `(sa with cs_next_var:=st1.cs_next_var+2).cs_next_var <=
       sb0.cs_next_var` mp_tac >>
     qpat_assum `!x v. not_fresh_at st x /\ lookup_var x orig=SOME v ==>
       lookup_var x live=SOME v` mp_tac >>
     qpat_assum `!x. not_fresh_at st x ==> FLOOKUP Gc x=FLOOKUP G0 x /\ _` mp_tac >>
     qpat_assum `!x. not_fresh_at (sa with cs_next_var:=st1.cs_next_var+2) x ==>
       lookup_var x body0=lookup_var x live /\ _` mp_tac >>
     qpat_assum `!x w. not_fresh_at sb0 x /\ lookup_var x body0=SOME w ==>
       lookup_var x u=SOME w` mp_tac >>
     qpat_assum `!x. not_fresh_at sb0 x ==> FLOOKUP H x=FLOOKUP B0 x /\ _` mp_tac >>
     rpt(pop_assum kall_tac) >> rpt strip_tac >> metis_tac[not_fresh_at_mono]) >>
  `ret_pc_ok cenv st u` by
    (qpat_assum `ret_pc_ok bc sb0 body0` mp_tac >>
     qpat_assum `bc.ce_return_pc=cenv.ce_return_pc` mp_tac >>
     qpat_assum `!x w. not_fresh_at sb0 x /\ lookup_var x body0=SOME w ==>
       lookup_var x u=SOME w` mp_tac >>
     qpat_assum `!x sz. cenv.ce_return_buf = _ \/ cenv.ce_return_pc = _ ==> _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[ret_pc_ok_def] >> metis_tac[]) >>
  qabbrev_tac `land=if res=INL() then jump_to incr u else u` >>
  `gas_path_ptr (cx_dead cx) 0 ctx func PG H tm u 0 H tm (OK land) /\
   land.vs_inst_idx=0 /\
   (res=INR BreakException ==> u.vs_current_bb=exit) /\
   (res<>INR BreakException ==> land.vs_current_bb=incr)` by
    (qpat_x_assum `exit=fresh_label_output _ _` kall_tac >>
     qpat_x_assum `incr=fresh_label_output _ _` kall_tac >>
     simp[Abbr `land`] >> irule forPtrRangeLandingTheory.for_body_lands_path_ptr >>
     simp[] >> qexistsl_tac [`sb1`,`sj`] >> simp[]) >>
  `stmt_state_rel ctx func cenv cx (ee with scopes:=rest) land /\
   ghost_inv d cenv cx (ee with scopes:=rest) H tm land /\
   ptr_covers H tm p land (type_memory_bytes cenv et) /\
   ~land.vs_halted = ~u.vs_halted /\ land.vs_allocas=u.vs_allocas /\
   (!x. lookup_var x land=lookup_var x u)` by
    (mp_tac (Q.INST [`es` |-> `ee with scopes:=rest`, `s` |-> `u`,
       `G` |-> `H`, `tn` |-> `tm`, `sz` |-> `type_memory_bytes cenv et`,
       `t` |-> `land`, `incr_lbl` |-> `incr`, `res` |-> `res:unit+exception`]
       (INST_TYPE [alpha |-> ``:exception``]
         forPtrRangeLandingTheory.for_body_landing_transport)) >>
     impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
       simp_tac bool_ss [Abbr `land`]]) >> disch_then ACCEPT_TAC) >>
  `(!x v. not_fresh_at st x /\ lookup_var x orig=SOME v ==>
      lookup_var x land=SOME v)` by metis_tac[] >>
  Cases_on `res=INR BreakException`
  >- (qpat_x_assum `res=INR BreakException` SUBST_ALL_TAC >>
      RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) []) >>
      qpat_x_assum `u=land` SUBST_ALL_TAC >>
      qexistsl_tac [`H`,`tm`,`land`] >>
      simp[Abbr `CleanPost`,Abbr `RoundPost`,for_array_done_ptr_def]) >>
  suspend "backedge"
QED

Resume immutable_code_loop_outcome_ptr[backedge]:
  `land.vs_current_bb=incr /\ ~land.vs_halted` by
    (qpat_assum `res<>INR BreakException ==> land.vs_current_bb=incr` mp_tac >>
     qpat_assum `res<>INR BreakException` mp_tac >>
     qpat_assum `~land.vs_halted = ~u.vs_halted` mp_tac >>
     qpat_assum `~u.vs_halted` mp_tac >>
     rpt(pop_assum kall_tac) >> simp[]) >>
  qpat_assum `!scs. not_local_ptr cenv scs p /\ _`
    (qspec_then `rest` strip_assume_tac) >>
  Q.SUBGOAL_THEN `res=INL() \/ res=INR ContinueException` ASSUME_TAC
  >- (qhdtm_assum `stmt_lands` mp_tac >>
      qpat_assum `res<>INR BreakException` mp_tac >>
      rpt(pop_assum kall_tac) >> simp[stmt_lands_def] >> metis_tac[]) >>
  `P (ee with scopes:=rest) /\ lookup_scopes id rest=NONE` by
    (qpat_assum `res=INL() \/ res=INR ContinueException ==> _` irule >>
     asm_rewrite_tac[]) >>
  `p<>idx /\ p<>nv /\ idx<>nv` by
    (qpat_assum `ALL_DISTINCT [p;idx;dv;ov;ep;nv]` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[ALL_DISTINCT] >> metis_tac[]) >>
  `(!x. not_fresh_at st x ==> x<>idx /\ x<>nv) /\
   (!x. lvo=Var x ==> x<>idx /\ x<>nv) /\
   (!z. cenv.ce_return_buf<>SOME(PtrVar(Var idx)z)) /\
   (!z. cenv.ce_return_buf<>SOME(PtrVar(Var nv)z))` by
    (qpat_assum `copy_old_operand st1 lvo` mp_tac >>
     qpat_assum `!x. not_fresh_at st1 x ==> _` mp_tac >>
     qpat_assum `!x. not_fresh_at st x ==> not_fresh_at st1 x` mp_tac >>
     qpat_assum `!x sz. cenv.ce_return_buf = _ \/ cenv.ce_return_pc = _ ==> _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[exprSimCopyTheory.copy_old_operand_def,MEM] >> metis_tac[]) >>
  `lookup_var p land=SOME dst /\ lookup_var idx land=SOME(n2w k) /\
   FLOOKUP land.vs_allocas (mk_inst st1.cs_next_id ALLOCA
     [Lit(n2w(type_memory_bytes cenv et))][p]).inst_id=
     SOME(w2n dst,type_memory_bytes cenv et) /\
   FLOOKUP H idx=NONE /\ op_taint tm (Var idx)={}` by
    (simp[] >> metis_tac[not_fresh_at_mono]) >>
  `ret_pc_ok cenv st land` by
    (Cases_on `res=INL()` >> simp[Abbr `land`,ret_pc_ok_jump_to]) >>
  `eval_operand lvo land=SOME(n2w(LENGTH vs)) /\
   op_prov H lvo=NONE /\ op_taint tm lvo={}` by
    (qpat_assum `eval_operand lvo u=SOME _` mp_tac >>
     qpat_assum `op_prov H lvo=NONE` mp_tac >>
     qpat_assum `op_taint tm lvo={}` mp_tac >>
     qpat_assum `!x. lookup_var x land=lookup_var x u` mp_tac >>
     qunabbrev_tac `land` >> rpt(pop_assum kall_tac) >>
     Cases_on `lvo` >> Cases_on `res=INL()` >>
     simp[eval_operand_def,jump_to_def,lookup_var_def]) >>
  qabbrev_tac `fin=jump_to cond (update_var idx (n2w(SUC k))
    (update_var nv (n2w(SUC k)) land))` >>
  qabbrev_tac `hf=DRESTRICT(DRESTRICT H(COMPL{nv}))(COMPL{idx})` >>
  qabbrev_tac `tf=tm with t_var:=(tm.t_var |+ (nv,{})) |+ (idx,{})` >>
  `gas_path_ptr (cx_dead cx) 0 ctx func PG H tm land 0 hf tf (OK fin)` by
    (simp_tac bool_ss [Abbr `fin`,Abbr `hf`,Abbr `tf`] >>
     mp_tac (Q.INST [`i1` |-> `sj.cs_next_id`,
       `i2` |-> `sj.cs_next_id+1`,`i3` |-> `sj.cs_next_id+2`,
       `s` |-> `land`,`G` |-> `H`,`tn` |-> `tm`,`D` |-> `cx_dead cx`,
       `idx` |-> `idx`,`nv` |-> `nv`,`k` |-> `k`,
       `incr_lbl` |-> `incr`,`cond_lbl` |-> `cond`]
       for_array_increment_block_path_ptr) >>
     impl_tac >- (rpt conj_tac >>
       FIRST [first_assum ACCEPT_TAC,asm_rewrite_tac[]]) >>
     disch_then ACCEPT_TAC) >>
  `stmt_state_rel ctx func cenv cx (ee with scopes:=rest) fin /\
   ghost_inv d cenv cx (ee with scopes:=rest) hf tf fin` by
    (simp_tac bool_ss [Abbr `fin`,Abbr `hf`,Abbr `tf`] >>
     mp_tac (Q.INST [`es` |-> `ee with scopes:=rest`,`s` |-> `land`,
       `G` |-> `H`,`tn` |-> `tm`,`cv` |-> `idx`,`nv` |-> `nv`,
       `lbl` |-> `cond`,`w` |-> `n2w(SUC k)`]
       forPtrRangeBackedgeTheory.for_backedge_state_ghost_transport) >>
     impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
       simp_tac bool_ss [evaluation_state_accfupds,combinTheory.K_THM] >> first_assum ACCEPT_TAC]) >>
     disch_then ACCEPT_TAC) >>
  `ptr_covers hf tf p fin (type_memory_bytes cenv et) /\
   fin.vs_allocas=land.vs_allocas /\ fin.vs_inst_idx=0 /\
   fin.vs_current_bb=cond /\ fin.vs_halted=land.vs_halted /\
   (!nm lo z. local_region cenv rest fin nm lo z <=>
              local_region cenv rest land nm lo z) /\
   (!x. x<>idx /\ x<>nv ==> lookup_var x fin=lookup_var x land /\
     FLOOKUP hf x=FLOOKUP H x /\ op_taint tf (Var x)=op_taint tm (Var x))` by
    (mp_tac (Q.INST [`sf` |-> `fin`,`Gf` |-> `hf`,`tf` |-> `tf`,
       `s` |-> `land`,`G` |-> `H`,`tn` |-> `tm`,`cv` |-> `idx`,
       `nv` |-> `nv`,`lbl` |-> `cond`,`w` |-> `n2w(SUC k)`,
       `scopes` |-> `rest`,`sz` |-> `type_memory_bytes cenv et`]
       forPtrRangeBackedgeTheory.for_backedge_reserved_frame) >>
     impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
       simp_tac bool_ss [Abbr `fin`,Abbr `hf`,Abbr `tf`]]) >>
     disch_then ACCEPT_TAC) >>
  `(!x v. not_fresh_at st x /\ lookup_var x orig=SOME v ==>
      lookup_var x fin=SOME v) /\
   (!x. not_fresh_at st x ==> FLOOKUP hf x=FLOOKUP G0 x /\
     op_taint tf (Var x)=op_taint tn0 (Var x))` by
    (irule forPtrRangeBackedgeTheory.for_backedge_old_frame >>
     qexistsl_tac [`H`,`idx`,`cond`,`nv`,`land`,`tm`,`n2w(SUC k)`] >>
     simp[Abbr `fin`,Abbr `hf`,Abbr `tf`]) >>
  `ret_pc_ok cenv st fin` by
    (irule ret_pc_ok_frame >> qexistsl_tac [`cenv`,`land`,`st`] >>
     simp[] >> rpt strip_tac >> metis_tac[]) >>
  `array_loop_inv ctx func cenv cx P (vs:value list) id idx (Lit(n2w off))(n2w off)
    p dst (type_memory_bytes cenv et)
    (mk_inst st1.cs_next_id ALLOCA [Lit(n2w(type_memory_bytes cenv et))][p])
    cond st (SUC k) (ee with scopes:=rest) fin` by
    (simp[array_loop_inv_def,eval_operand_def] >>
     simp[Abbr `fin`,lookup_var_def,update_var_def,jump_to_def,FLOOKUP_UPDATE] >>
     metis_tac[]) >>
  `FLOOKUP hf idx=NONE /\ op_taint tf (Var idx)={} /\
   eval_operand lvo fin=SOME(n2w(LENGTH vs)) /\
   op_prov hf lvo=NONE /\ op_taint tf lvo={}` by
    (qpat_assum `eval_operand lvo land=SOME _` mp_tac >>
     qpat_assum `op_prov H lvo=NONE` mp_tac >>
     qpat_assum `op_taint tm lvo={}` mp_tac >>
     qpat_assum `!x. lvo=Var x ==> x<>idx /\ x<>nv` mp_tac >>
     qunabbrev_tac `fin` >> qunabbrev_tac `hf` >> qunabbrev_tac `tf` >>
     rpt(pop_assum kall_tac) >> Cases_on `lvo` >>
     simp[eval_operand_def,lookup_var_def,update_var_def,jump_to_def,
       op_prov_def,op_taint_def,FLOOKUP_UPDATE,FLOOKUP_DRESTRICT]) >>
  qexistsl_tac [`hf`,`tf`,`fin`] >>
  conj_tac >- (drule_all fragGasPathPtrTheory.gas_path_ptr_then >> simp[]) >>
  qpat_assum `res=INL() \/ res=INR ContinueException`
    (DISJ_CASES_THEN (fn th =>
      simp_tac (srw_ss()) [Abbr `CleanPost`,Abbr `RoundPost`,th])) >>
  qpat_assum `ee.scopes=sc::rest` (fn th => simp_tac (srw_ss()) [th]) >>
  qpat_assum `p=STRING _ _` (fn pth =>
    qpat_assum `idx=STRING _ _` (fn ith =>
      qpat_assum `cond=fresh_label_output _ _` (fn cth =>
        qpat_assum `type_memory_bytes cenv et=type_memory_size tv` (fn zth =>
          pure_rewrite_tac[GSYM pth,GSYM ith,GSYM cth,GSYM zth])))) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume immutable_code_loop_outcome_ptr[assembly]:
  `gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (finally (try (do eval_stmts cx stmts; return F od) handle_loop_exception) pop_scope)
    (eb,body0,B0,tB0) RoundPost RoundExit` by
    (mp_tac (Q.INST [`es` |-> `eb`,`s` |-> `body0`,
       `G0` |-> `B0`,`tn0` |-> `tB0`,`Q` |-> `CleanPost`,
       `R` |-> `\res ee gt r. !tail. stmt_exit_ptr RetQ
          (ee with gas_obs:=tail) res gt r`,
       `Q'` |-> `RoundPost`,`R'` |-> `RoundExit`,
       `D` |-> `cx_dead cx`,`tops` |-> `cx_tops cx`]
       for_body_cleanup_outcome_ptr) >>
     impl_tac >- (conj_tac >- simp[Abbr `eb`] >>
       conj_tac >- first_assum ACCEPT_TAC >>
       conj_tac >- simp[Abbr `CleanPost`] >>
       rpt gen_tac >> simp_tac bool_ss [] >> strip_tac >>
       drule (Q.INST [`rest` |-> `TL ee.scopes`] for_body_exit_cleanup_ptr) >>
       strip_tac >> qunabbrev_tac `RoundExit` >>
       qpat_x_assum `res=INR ex` mp_tac >>
       qpat_x_assum `ex<>BreakException` mp_tac >>
       qpat_x_assum `ex<>ContinueException` mp_tac >>
       qpat_x_assum `!tail. stmt_exit_ptr RetQ _ (INR ex) gt r` mp_tac >>
       rpt(pop_assum kall_tac) >> simp[]) >>
     disch_then ACCEPT_TAC) >>
  `gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG
    (push_scope_with_var id tv (EL k vs)) (es,s,G,tn) [] (INL())
    (es with scopes := (FEMPTY |+ (id,
      <|assignable:=F;type:=tv;value:=EL k vs;popped:=[]|>))::es.scopes)
    B0 tB0 (OK body0)` by
    (drule_all fragGasPathPtrTheory.gas_path_ptr_then >>
     rpt(pop_assum kall_tac) >>
     simp[gas_marked_exec_ptr_def,push_scope_with_var_def,return_def,
       evaluation_state_component_equality,combinTheory.o_DEF]) >>
  once_rewrite_tac[ignore_bind_def] >>
  irule gas_outcome_ptr_bind_normal >>
  goal_assum(drule_at(Pat `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _`)) >>
  reverse conj_tac >- (BETA_TAC >>
    qpat_assum `eb=(_ with gas_obs:=[])` (fn th => pure_rewrite_tac[GSYM th]) >>
    first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  qhdtm_assum `gas_marked_exec` mp_tac >>
  qhdtm_assum `gas_exempt_cert` mp_tac >> rpt(pop_assum kall_tac) >>
  rewrite_tac[ignore_bind_def,bind_assoc] >> rpt strip_tac >>
  irule (cj 2 gasExemptCertTheory.gas_exempt_cert_rules) >> goal_assum(drule_at Any) >>
  fs[ignore_bind_def,evaluation_state_fupdcanon]
QED

Resume immutable_code_loop_outcome_ptr[terminal]:
  rpt gen_tac >> strip_tac >>
  `dv <> idx /\ dv <> p` by
    (qpat_assum `ALL_DISTINCT [p;idx;dv;ov;ep;nv]` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[ALL_DISTINCT] >> metis_tac[]) >>
  `(!x. lvo = Var x ==> x <> dv) /\
   (!x. not_fresh_at st x ==> x <> dv) /\
   (!z. cenv.ce_return_buf <> SOME (PtrVar (Var dv) z))` by
    (qpat_assum `copy_old_operand st1 lvo` mp_tac >>
     qpat_assum `!x. not_fresh_at st1 x ==> _` mp_tac >>
     qpat_assum `!x. not_fresh_at st x ==> not_fresh_at st1 x` mp_tac >>
     qpat_assum `!x sz. cenv.ce_return_buf = _ \/ cenv.ce_return_pc = _ ==> _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[exprSimCopyTheory.copy_old_operand_def, MEM] >> metis_tac[]) >>
  qpat_assum `!scs. not_local_ptr cenv scs p /\ _`
    (qspec_then `es.scopes` strip_assume_tac) >>
  drule_all (Q.INST [`D` |-> `cx_dead cx`] immutable_condition_ptr) >>
  disch_then (qspec_then `PG` (strip_assume_tac o SIMP_RULE bool_ss [])) >>
  qpat_assum
    `array_loop_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ exit st _ es (jump_to exit _)`
    mp_tac >> pure_rewrite_tac[array_loop_inv_def] >> strip_tac >>
  qexistsl_tac
    [`jump_to exit (update_var dv (bool_to_word T) s)`,
     `DRESTRICT G (COMPL {dv})`, `tn with t_var := tn.t_var |+ (dv,{})`] >>
  pure_rewrite_tac
    [for_array_done_ptr_def, stmt_state_rel_gas_obs, ghost_inv_gas_obs] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise immutable_code_loop_outcome_ptr

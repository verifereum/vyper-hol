Theory lowerDloadExternalCallEffects
Ancestors
  lowerDloadExternalBoundary lowerDloadSafetyUpdates lowerDloadSafetyKernel
  venomExecSemantics venomCallOracleDefs venomState ptrDiscipline
  finite_map pred_set list words arithmetic

Theorem ld_exec_ext_call_effect:
  ld_memory lo A tn s t /\ ld_nonghost tn s t /\
  (!a u v z. FLOOKUP A a = SOME (u,v,z) ==> lo <= u /\ lo <= v) /\
  (!a k u v z b c sz.
    FLOOKUP A a = SOME (u,v,z) /\ FLOOKUP A k = SOME (b,c,sz) /\
    a <> k /\ 0 < z /\ 0 < sz ==>
    (u+z <= b \/ b+sz <= u) /\ (v+z <= c \/ c+sz <= v)) /\
  (inst.inst_opcode = CALL \/ inst.inst_opcode = STATICCALL) /\
  (inst.inst_opcode = CALL ==> st = s.vs_call_ctx.cc_static) /\
  (inst.inst_opcode = STATICCALL ==> st) /\
  read_memory (w2n ao) (w2n az) s = read_memory (w2n at) (w2n az) t /\
  exec_ext_call inst t gt addr value at az rt rz st = OK ts /\
  (w2n rz = 0 \/ (w2n ro = w2n rt /\ w2n ro + w2n rz <= lo) \/
   (?k b c sz delta. FLOOKUP A k = SOME (b,c,sz) /\
     w2n ro = b+delta /\ w2n rt = c+delta /\ delta + w2n rz <= sz)) ==>
  ?ss w out tn'.
    exec_ext_call inst s gs addr value ao az ro rz st = OK ss /\
    inst.inst_outputs = [out] /\
    FLOOKUP ss.vs_vars out = SOME w /\ FLOOKUP ts.vs_vars out = SOME w /\
    tn' = tn with <|
      t_mem := tn.t_mem DIFF {w2n ro+j | j < LENGTH (TAKE (w2n rz) ss.vs_returndata)};
      t_stor := adopt_reset inst (~s.vs_call_ctx.cc_static /\ ss.vs_requests <> s.vs_requests /\
        ss.vs_outcomes <> s.vs_outcomes /\ (HD s.vs_outcomes).co_success) tn.t_stor;
      t_trans := adopt_reset inst (~s.vs_call_ctx.cc_static /\ ss.vs_requests <> s.vs_requests /\
        ss.vs_outcomes <> s.vs_outcomes /\ (HD s.vs_outcomes).co_success) tn.t_trans |> /\
    ld_memory lo A tn' ss ts /\ ld_nonghost tn' ss ts /\
    ss.vs_allocas = s.vs_allocas /\ ts.vs_allocas = t.vs_allocas /\
    ss.vs_alloca_next = s.vs_alloca_next /\ ts.vs_alloca_next = t.vs_alloca_next /\
    ss.vs_current_bb = s.vs_current_bb /\ ts.vs_current_bb = t.vs_current_bb /\
    ss.vs_prev_bb = s.vs_prev_bb /\ ts.vs_prev_bb = t.vs_prev_bb /\
    ss.vs_inst_idx = s.vs_inst_idx /\ ts.vs_inst_idx = t.vs_inst_idx
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >> (
  qabbrev_tac `rq = venom_call_request s addr value ao az st` >>
  qabbrev_tac `rq' = venom_call_request t addr value at az st` >>
  Cases_on `consume_call_outcome rq (w2n ro) (w2n rz) s` >>
  Cases_on `consume_call_outcome rq' (w2n rt) (w2n rz) t` >>
  rename1 `consume_call_outcome rq (w2n ro) (w2n rz) s = (w,ss0)` >>
  rename1 `consume_call_outcome rq' (w2n rt) (w2n rz) t = (w',ts0)` >>
  qunabbrev_tac `rq'` >>
  qpat_x_assum `exec_ext_call _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  pure_rewrite_tac[exec_ext_call_def] >>
  simp[Excl "consume_call_outcome_eq"] >>
  Cases_on `inst.inst_outputs` >- simp[] >>
  rename1 `inst.inst_outputs = out::outs` >>
  Cases_on `outs` >> simp[] >>
  disch_then (SUBST_ALL_TAC o SYM) >>
  qabbrev_tac `mask = tn with <|
    t_mem := tn.t_mem DIFF {w2n ro+j | j < LENGTH (TAKE (w2n rz) ss0.vs_returndata)};
    t_stor := adopt_reset inst (~s.vs_call_ctx.cc_static /\ ss0.vs_requests <> s.vs_requests /\
      ss0.vs_outcomes <> s.vs_outcomes /\ (HD s.vs_outcomes).co_success) tn.t_stor;
    t_trans := adopt_reset inst (~s.vs_call_ctx.cc_static /\ ss0.vs_requests <> s.vs_requests /\
      ss0.vs_outcomes <> s.vs_outcomes /\ (HD s.vs_outcomes).co_success) tn.t_trans |>` >>
  `s.vs_call_ctx = t.vs_call_ctx` by metis_tac[ld_nonghost_def] >>
  `w = w' /\ ld_memory lo A mask ss0 ts0 /\ ld_nonghost mask ss0 ts0 /\
   ss0.vs_allocas = s.vs_allocas /\ ts0.vs_allocas = t.vs_allocas /\
   ss0.vs_alloca_next = s.vs_alloca_next /\ ts0.vs_alloca_next = t.vs_alloca_next /\
   ss0.vs_current_bb = s.vs_current_bb /\ ts0.vs_current_bb = t.vs_current_bb /\
   ss0.vs_prev_bb = s.vs_prev_bb /\ ts0.vs_prev_bb = t.vs_prev_bb /\
   ss0.vs_inst_idx = s.vs_inst_idx /\ ts0.vs_inst_idx = t.vs_inst_idx` by
    (irule ld_consume_call_effect >>
     conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
     qpat_assum `consume_call_outcome rq _ _ s = _` (irule_at Any) >>
     qpat_assum `consume_call_outcome _ _ _ t = _` (irule_at Any) >>
     qexistsl_tac [`TAKE (w2n rz) ss0.vs_returndata`, `tn`, `inst`] >>
     simp[Abbr `mask`, Abbr `rq`, venom_call_request_def] >>
     `LENGTH (TAKE (w2n rz) ss0.vs_returndata) <= w2n rz` by
       (simp[LENGTH_TAKE_EQ]) >>
     qpat_x_assum `w2n rz = 0 \/ _` strip_assume_tac
     >- gvs[]
     >- (disj2_tac >> disj1_tac >> decide_tac) >>
     disj2_tac >> disj2_tac >>
     qexistsl_tac [`k`, `b`, `c`, `sz`, `delta`] >> simp[] >> decide_tac) >>
  `ld_memory lo A (mask with t_var := mask.t_var)
     (update_var out w ss0) (update_var out w' ts0)` by
    (irule ld_memory_update_var >> simp[]) >>
  `ld_nonghost (mask with t_var := mask.t_var)
     (update_var out w ss0) (update_var out w' ts0)` by
    (irule ld_nonghost_update_var >> simp[]) >>
  qexists_tac `w` >> qunabbrev_tac `mask` >>
  gvs[Excl "consume_call_outcome_eq", update_var_def, FLOOKUP_UPDATE, ADD_COMM])
QED

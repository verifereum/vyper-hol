(* Checked allocation-prefix boundaries, including reused allocation sites. *)
Theory revertReasonPrefixPtr
Ancestors
  revertReasonLayout allocationPtr typedCopyPtr fragExec fragGasSeqPtr ghostPcTransportPtr
  loweringSlice exprLoweringProps bodyPtrDefs fragExecPtr venomExecSemantics venomInst venomState
  ptrDiscipline finite_map words arithmetic exprSimAlloc localPtrsProps compileEnv instIdxIndep
  normalizationAllocPtr decoderGhostFramePtr loweringPosts

Theorem alloca_store_offset_alloca_checks:
  stmt_state_rel ctx func cenv cx es s /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
  32 <= n /\ n < dimword(:256) /\ ~ctx_has_dalloca ctx /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 ==>
  ?Gf tnf.
    inst_seq_ptr D 0 ctx func PG G tn
      [mk_inst id ALLOCA [Lit (n2w n)] [out];
       mk_inst (id+1) MSTORE [Var out; Lit value] [];
       mk_inst (id+2) ADD [Var out; Lit off] [p];
       mk_inst (id+3) ALLOCA [Lit sz] [q]] s Gf tnf
Proof
  strip_tac >>
  qmatch_goalsub_abbrev_tac `inst_seq_ptr _ _ _ _ _ _ _ [i;j;k;l] _ _ _` >>
  `ptr_covers (step_prov PG G i s1)
      (step_taint i s s1 tn) out s1 n` by
    (unabbrev_all_tac >> irule alloca_step_ptr_covers >> metis_tac[]) >>
  `ptr_covers (step_prov PG G i s1)
      (step_taint i s s1 tn) out s1 32` by
    (gvs[ptr_covers_def] >> metis_tac[LESS_EQ_TRANS]) >>
  simp[Once inst_seq_ptr_def, Abbr `i`, ptr_inst_ok_alloca] >>
  simp[Once inst_seq_ptr_def] >>
  qmatch_goalsub_abbrev_tac `ptr_inst_ok _ _ _ _ _ g1 t1 _ _` >>
  `ptr_inst_ok D 0 0 ctx func g1 t1 j
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)` by
    (simp[Abbr `j`] >> irule ptr_inst_ok_mstore >>
     simp[op_taint_def, Abbr `g1`, Abbr `t1`]) >>
  `?a. lookup_var out s1 = SOME a /\ op_taint t1 (Var out) = {}` by
    gvs[ptr_covers_def, eval_operand_def] >>
  `step_inst_base j (s1 with vs_inst_idx := SUC s.vs_inst_idx) =
     OK ((mstore (w2n a) value s1) with vs_inst_idx := SUC s.vs_inst_idx)` by
    (simp[Abbr `j`] >> PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def, exec_write2_def, eval_operand_def, mstore_def]) >>
  simp[] >>
  qmatch_goalsub_abbrev_tac `inst_seq_ptr _ _ _ _ _ g2 t2 _ s2 _ _` >>
  `op_taint t2 (Var out) = {}` by
    (simp[Abbr `t2`, Abbr `j`, op_taint_def, mstore_ghost_frame,
          eval_operand_def] >> gvs[op_taint_def]) >>
  simp[Once inst_seq_ptr_def] >>
  `ptr_inst_ok D 0 0 ctx func g2 t2 k s2` by
    (simp[Abbr `k`] >> irule ptr_inst_ok_copy_len_binop >>
     simp[op_taint_def] >> gvs[op_taint_def]) >>
  Cases_on `step_inst_base k s2` >> simp[] >>
  simp[inst_seq_ptr_def, Abbr `l`, ptr_inst_ok_alloca] >>
  Cases_on `step_inst_base (mk_inst (id+3) ALLOCA [Lit sz] [q])
    (v with vs_inst_idx := SUC s2.vs_inst_idx)` >> simp[]

QED

Theorem revert_reason_prefix_path_ptr:
  stmt_state_rel ctx func cenv cx es s /\
  MEM (mk_inst id ALLOCA [Lit (n2w (64+ms))]
    [STRING #"%" (toString v)]) (fn_insts func) /\
  64+ms < dimword(:256) /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (revert_reason_prefix id v ms)
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  run_inst_seq (revert_reason_prefix id v ms) s = OK t ==>
  ?Gf tnf. gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf
    (OK (t with vs_inst_idx := s.vs_inst_idx + 4))
Proof
  strip_tac >>
  `?s1. step_inst_base (mk_inst id ALLOCA [Lit (n2w (64+ms))]
     [STRING #"%" (toString v)]) s = OK s1` by
    (qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
     simp[revert_reason_prefix_def, Once run_inst_seq_def, AllCaseEqs()] >>
     metis_tac[]) >>
  `?Gf tnf. inst_seq_ptr D 0 ctx func PG G tn
      (revert_reason_prefix id v ms) s Gf tnf` by
    (simp[revert_reason_prefix_def] >>
     irule alloca_store_offset_alloca_checks >>
     gvs[ADD_COMM] >> metis_tac[]) >>
  qexistsl_tac [`Gf`, `tnf`] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (revert_reason_prefix id v ms)` by
    simp[revert_reason_prefix_def, mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_path_ptr >>
  simp[revert_reason_prefix_def, mk_inst_def]
QED

Theorem stmt_state_rel_mstore_alloca:
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [p] /\ not_local_ptr cenv es.scopes p /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
  b <= a /\ a+32 <= b+sz ==>
  stmt_state_rel ctx func cenv cx es (mstore a w s)
Proof
  strip_tac >> irule literal_mstore_state_rel >> simp[] >>
  qexistsl_tac [`b`, `inst`, `sz`] >> simp[] >>
  rpt strip_tac >>
  `regions_disjoint b sz lb lsz` by
    (irule local_ptrs_rel_alloca_disjoint >>
     gvs[stmt_state_rel_def, state_rel_def] >> metis_tac[]) >>
  gvs[regions_disjoint_def]
QED

Theorem alloca_mstore_literal_state_rel:
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
  not_local_ptr cenv es.scopes out /\ 32 <= n /\ n < dimword(:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 ==>
  ?b. lookup_var out s1 = SOME (n2w b) /\ b+n < dimword(:256) /\
      stmt_state_rel ctx func cenv cx es (mstore b value s1)
Proof
  strip_tac >>
  `exec_alloca (mk_inst id ALLOCA [Lit (n2w n)] [out]) s (n2w n:bytes32) = OK s1` by
    (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
     PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def] >> strip_tac >> first_x_assum ACCEPT_TAC) >>
  `stmt_state_rel ctx func cenv cx es s1` by
    (drule_at (Pat `exec_alloca _ _ _ = _`) stmt_state_rel_exec_alloca >>
     gvs[mk_inst_def] >> metis_tac[]) >>
  drule_all alloca_step_site >> strip_tac >>
  qexists_tac `b` >> conj_tac >- gvs[eval_operand_def] >>
  simp[] >> irule stmt_state_rel_mstore_alloca >> simp[] >>
  qexistsl_tac [`b`, `mk_inst id ALLOCA [Lit (n2w n)] [out]`, `out`, `n`] >>
  simp[mk_inst_def]
QED


Theorem alloca_store_offset_alloca_state_rel:
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
  MEM (mk_inst (id+3) ALLOCA [Lit sz] [q]) (fn_insts func) /\
  not_local_ptr cenv es.scopes out /\ not_local_ptr cenv es.scopes p /\
  not_local_ptr cenv es.scopes q /\ 32 <= n /\ n < dimword(:256) /\
  run_inst_seq
    [mk_inst id ALLOCA [Lit (n2w n)] [out];
     mk_inst (id+1) MSTORE [Var out; Lit value] [];
     mk_inst (id+2) ADD [Var out; Lit off] [p];
     mk_inst (id+3) ALLOCA [Lit sz] [q]] s = OK t ==>
  stmt_state_rel ctx func cenv cx es t
Proof
  strip_tac >>
  Cases_on `step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s` >>
  gvs[Once run_inst_seq_def] >>
  rename1 `step_inst_base _ s = OK s1` >>
  drule_all alloca_mstore_literal_state_rel >>
  disch_then (qspec_then `value` strip_assume_tac) >>
  `step_inst_base (mk_inst (id+1) MSTORE [Var out; Lit value] []) s1 =
    OK (mstore b value s1)` by
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def, exec_write2_def, eval_operand_def, w2n_n2w]) >>
  qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
  simp[Once run_inst_seq_def] >>
  qmatch_goalsub_abbrev_tac `run_inst_seq _ s2` >>
  `step_inst_base (mk_inst (id+2) ADD [Var out; Lit off] [p]) s2 =
     OK (update_var p (n2w b + off) s2)` by
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def, exec_pure2_def, eval_operand_def,
          Abbr `s2`, mstore_def, lookup_var_def]) >>
  `stmt_state_rel ctx func cenv cx es (update_var p (n2w b+off) s2)` by
    (irule stmt_state_rel_update_var >> simp[Abbr `s2`]) >>
  simp[Once run_inst_seq_def] >>
  qmatch_goalsub_abbrev_tac `run_inst_seq _ s3` >>
  simp[Once run_inst_seq_def, run_inst_seq_def] >>
  Cases_on `step_inst_base (mk_inst (id+3) ALLOCA [Lit sz] [q]) s3` >>
  simp[] >> strip_tac >> gvs[] >>
  qpat_x_assum `step_inst_base _ s3 = _` mp_tac >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  simp[mk_inst_def] >> strip_tac >>
  drule_at (Pat `exec_alloca _ _ _ = _`) stmt_state_rel_exec_alloca >>
  gvs[mk_inst_def] >> metis_tac[]
QED

Theorem revert_reason_prefix_state_rel:
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  MEM (mk_inst id ALLOCA [Lit (n2w (64+ms))]
    [STRING #"%" (toString v)]) (fn_insts func) /\
  MEM (mk_inst (id+3) ALLOCA [Lit (n2w ms)]
    [STRING #"%" (toString (v+2))]) (fn_insts func) /\
  (!k. k < 3 ==> not_local_ptr cenv es.scopes (STRING #"%" (toString (v+k)))) /\
  64+ms < dimword(:256) /\
  run_inst_seq (revert_reason_prefix id v ms) s = OK t ==>
  stmt_state_rel ctx func cenv cx es t
Proof
  strip_tac >>
  fs[revert_reason_prefix_def] >>
  drule_at (Pat `run_inst_seq _ _ = _`) alloca_store_offset_alloca_state_rel >>
  simp[] >>
  `not_local_ptr cenv es.scopes (STRING #"%" (toString v)) /\
   not_local_ptr cenv es.scopes (STRING #"%" (toString (v+1))) /\
   not_local_ptr cenv es.scopes (STRING #"%" (toString (v+2)))` by
    (qpat_x_assum `!k. _` mp_tac >>
     disch_then (fn th => map_every (fn k => qspec_then k assume_tac th)
       [`0`, `1`, `2`]) >> gvs[ADD_COMM]) >>
  simp[] >> disch_then irule >> simp[]
QED

(* Operational inversion is independent of the opcode and is shared by
   the source, coverage, and ghost frames of this four-instruction prefix. *)
Theorem run_inst_seq_four_endpoint:
  run_inst_seq [i;j;k;l] s = OK t ==>
  ?s1 s2 s3.
    step_inst_base i s = OK s1 /\
    step_inst_base j s1 = OK s2 /\
    step_inst_base k s2 = OK s3 /\
    step_inst_base l s3 = OK t
Proof
  simp[run_inst_seq_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem store_offset_endpoint:
  lookup_var out s1 = SOME a /\
  step_inst_base (mk_inst id MSTORE [Var out; Lit value] []) s1 = OK s2 /\
  step_inst_base (mk_inst id2 ADD [Var out; Lit off] [p]) s2 = OK s3 ==>
  s2 = mstore (w2n a) value s1 /\
  s3 = update_var p (a+off) s2
Proof
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  simp[mk_inst_def, exec_write2_def, exec_pure2_def, eval_operand_def] >>
  strip_tac >> gvs[mstore_def, lookup_var_def]
QED

Theorem inst_seq_ptr_four_endpoint:
  step_inst_base i s = OK s1 /\
  step_inst_base j s1 = OK s2 /\
  step_inst_base k s2 = OK s3 /\
  step_inst_base l s3 = OK t /\
  ~is_terminator j.inst_opcode /\ ~is_terminator k.inst_opcode /\
  ~is_terminator l.inst_opcode /\
  G1 = step_prov PG G i s1 /\ tn1 = step_taint i s s1 tn /\
  G2 = step_prov PG G1 j s2 /\ tn2 = step_taint j s1 s2 tn1 /\
  G3 = step_prov PG G2 k s3 /\ tn3 = step_taint k s2 s3 tn2 /\
  G4 = step_prov PG G3 l t /\ tn4 = step_taint l s3 t tn3 /\
  inst_seq_ptr D lo ctx func PG G tn [i;j;k;l] s Gf tnf ==>
  Gf = G4 /\ tnf = tn4
Proof
  strip_tac >>
  gvs[inst_seq_ptr_def, step_inst_inst_idx_indep, exec_result_map_def]
QED

Theorem alloca_store_offset_state_rel:
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
  not_local_ptr cenv es.scopes out /\ not_local_ptr cenv es.scopes p /\
  32 <= n /\ n < dimword(:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 /\
  step_inst_base (mk_inst (id+1) MSTORE [Var out; Lit value] []) s1 = OK s2 /\
  step_inst_base (mk_inst (id+2) ADD [Var out; Lit off] [p]) s2 = OK s3 ==>
  stmt_state_rel ctx func cenv cx es s3
Proof
  strip_tac >> drule_all alloca_mstore_literal_state_rel >>
  disch_then (qspec_then `value` strip_assume_tac) >>
  drule_all store_offset_endpoint >> strip_tac >> gvs[] >>
  irule stmt_state_rel_update_var >> simp[]
QED

Theorem alloca_store_offset_ptr_covers:
  stmt_state_rel ctx func cenv cx es s /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
  n < dimword(:256) /\ out <> p /\ off + m <= n /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 /\
  step_inst_base (mk_inst (id+1) MSTORE [Var out; Lit value] []) s1 = OK s2 /\
  step_inst_base (mk_inst (id+2) ADD [Var out; Lit (n2w off)] [p]) s2 = OK s3 /\
  G1 = step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) s1 /\
  tn1 = step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn /\
  G2 = step_prov PG G1 (mk_inst (id+1) MSTORE [Var out; Lit value] []) s2 /\
  tn2 = step_taint (mk_inst (id+1) MSTORE [Var out; Lit value] []) s1 s2 tn1 /\
  G3 = step_prov PG G2 (mk_inst (id+2) ADD [Var out; Lit (n2w off)] [p]) s3 /\
  tn3 = step_taint (mk_inst (id+2) ADD [Var out; Lit (n2w off)] [p]) s2 s3 tn2 ==>
  ptr_covers G3 tn3 out s3 n /\ ptr_covers G3 tn3 p s3 m
Proof
  strip_tac >>
  `ptr_covers G1 tn1 out s1 n` by
    (gvs[] >> irule alloca_step_ptr_covers >> metis_tac[]) >>
  drule_all alloca_step_site >> strip_tac >>
  `lookup_var out s1 = SOME (n2w b)` by gvs[eval_operand_def] >>
  drule_all store_offset_endpoint >> strip_tac >> gvs[] >>
  `b + off < dimword(:256) /\ b < dimword(:256) /\ off < dimword(:256)` by decide_tac >>
  gvs[lookup_var_def] >>
  simp[ptr_covers_def, step_prov_def, set_prov_def, out_prov_def,
       first_prov_def, op_prov_def, mk_inst_def, FLOOKUP_UPDATE,
       FLOOKUP_DRESTRICT, op_taint_def, step_taint_def, out_taint_def,
       set_var_taint_def, mstore_def, update_var_def, lookup_var_def,
       eval_operand_def, w2n_add_2, w2n_n2w, LESS_MOD] >> decide_tac
QED

Theorem alloca_store_offset_alloca_ptr_covers:
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
  MEM (mk_inst (id+3) ALLOCA [Lit (n2w sz)] [q]) (fn_insts func) /\
  not_local_ptr cenv es.scopes out /\ not_local_ptr cenv es.scopes p /\
  32 <= n /\ n < dimword(:256) /\ sz < dimword(:256) /\
  out <> p /\ out <> q /\ p <> q /\ off+m <= n /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 /\
  step_inst_base (mk_inst (id+1) MSTORE [Var out; Lit value] []) s1 = OK s2 /\
  step_inst_base (mk_inst (id+2) ADD [Var out; Lit (n2w off)] [p]) s2 = OK s3 /\
  step_inst_base (mk_inst (id+3) ALLOCA [Lit (n2w sz)] [q]) s3 = OK t /\
  G1 = step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) s1 /\
  tn1 = step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn /\
  G2 = step_prov PG G1 (mk_inst (id+1) MSTORE [Var out; Lit value] []) s2 /\
  tn2 = step_taint (mk_inst (id+1) MSTORE [Var out; Lit value] []) s1 s2 tn1 /\
  G3 = step_prov PG G2 (mk_inst (id+2) ADD [Var out; Lit (n2w off)] [p]) s3 /\
  tn3 = step_taint (mk_inst (id+2) ADD [Var out; Lit (n2w off)] [p]) s2 s3 tn2 /\
  G4 = step_prov PG G3 (mk_inst (id+3) ALLOCA [Lit (n2w sz)] [q]) t /\
  tn4 = step_taint (mk_inst (id+3) ALLOCA [Lit (n2w sz)] [q]) s3 t tn3 ==>
  ptr_covers G4 tn4 out t n /\ ptr_covers G4 tn4 p t m /\
  ptr_covers G4 tn4 q t sz
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx es s3` by
    (irule alloca_store_offset_state_rel >> metis_tac[]) >>
  drule_all alloca_store_offset_ptr_covers >> strip_tac >>
  conj_tac >-
    (gvs[] >> irule alloca_step_old_ptr_covers >> metis_tac[]) >>
  conj_tac >-
    (gvs[] >> irule alloca_step_old_ptr_covers >> metis_tac[]) >>
  gvs[] >> irule alloca_step_ptr_covers >> metis_tac[]
QED

Theorem alloca_store_offset_alloca_run_covers:
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
  MEM (mk_inst (id+3) ALLOCA [Lit (n2w sz)] [q]) (fn_insts func) /\
  not_local_ptr cenv es.scopes out /\ not_local_ptr cenv es.scopes p /\
  32 <= n /\ n < dimword(:256) /\ sz < dimword(:256) /\
  out <> p /\ out <> q /\ p <> q /\ off+m <= n /\
  run_inst_seq
    [mk_inst id ALLOCA [Lit (n2w n)] [out];
     mk_inst (id+1) MSTORE [Var out; Lit value] [];
     mk_inst (id+2) ADD [Var out; Lit (n2w off)] [p];
     mk_inst (id+3) ALLOCA [Lit (n2w sz)] [q]] s = OK t /\
  inst_seq_ptr D lo ctx func PG G tn
    [mk_inst id ALLOCA [Lit (n2w n)] [out];
     mk_inst (id+1) MSTORE [Var out; Lit value] [];
     mk_inst (id+2) ADD [Var out; Lit (n2w off)] [p];
     mk_inst (id+3) ALLOCA [Lit (n2w sz)] [q]] s Gf tnf ==>
  ptr_covers Gf tnf out t n /\ ptr_covers Gf tnf p t m /\
  ptr_covers Gf tnf q t sz
Proof
  strip_tac >>
  qmatch_asmsub_abbrev_tac `run_inst_seq [i;j;k;l] s` >>
  drule run_inst_seq_four_endpoint >> strip_tac >>
  qabbrev_tac `G1 = step_prov PG G i s1` >>
  qabbrev_tac `tn1 = step_taint i s s1 tn` >>
  qabbrev_tac `G2 = step_prov PG G1 j s2` >>
  qabbrev_tac `tn2 = step_taint j s1 s2 tn1` >>
  qabbrev_tac `G3 = step_prov PG G2 k s3` >>
  qabbrev_tac `tn3 = step_taint k s2 s3 tn2` >>
  qabbrev_tac `G4 = step_prov PG G3 l t` >>
  qabbrev_tac `tn4 = step_taint l s3 t tn3` >>
  `~is_terminator j.inst_opcode /\ ~is_terminator k.inst_opcode /\
   ~is_terminator l.inst_opcode` by
    simp[Abbr `j`, Abbr `k`, Abbr `l`, mk_inst_def, is_terminator_def] >>
  `Gf = G4 /\ tnf = tn4` by
    (irule inst_seq_ptr_four_endpoint >>
     goal_assum (drule_at Any) >>
     simp[Abbr `G1`, Abbr `tn1`, Abbr `G2`, Abbr `tn2`,
          Abbr `G3`, Abbr `tn3`, Abbr `G4`, Abbr `tn4`] >>
     metis_tac[]) >>
  fs[Abbr `i`, Abbr `j`, Abbr `k`, Abbr `l`] >>
  map_every (fn pat => qpat_assum pat
    (assume_tac o REWRITE_RULE[markerTheory.Abbrev_def]))
    [`Abbrev (G1 = _)`, `Abbrev (tn1 = _)`,
     `Abbrev (G2 = _)`, `Abbrev (tn2 = _)`,
     `Abbrev (G3 = _)`, `Abbrev (tn3 = _)`,
     `Abbrev (G4 = _)`, `Abbrev (tn4 = _)`] >>
  `off+m <= n` by decide_tac >>
  drule_all alloca_store_offset_alloca_ptr_covers >> simp[]
QED

Theorem revert_reason_prefix_covers:
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  MEM (mk_inst id ALLOCA [Lit (n2w (64+ms))]
    [STRING #"%" (toString v)]) (fn_insts func) /\
  MEM (mk_inst (id+3) ALLOCA [Lit (n2w ms)]
    [STRING #"%" (toString (v+2))]) (fn_insts func) /\
  (!k. k < 2 ==> not_local_ptr cenv es.scopes (STRING #"%" (toString (v+k)))) /\
  64+ms < dimword(:256) /\
  run_inst_seq (revert_reason_prefix id v ms) s = OK t /\
  inst_seq_ptr D lo ctx func PG G tn (revert_reason_prefix id v ms) s Gf tnf ==>
  ptr_covers Gf tnf (STRING #"%" (toString v)) t (64+ms) /\
  ptr_covers Gf tnf (STRING #"%" (toString (v+1))) t (32+ms) /\
  ptr_covers Gf tnf (STRING #"%" (toString (v+2))) t ms
Proof
  strip_tac >> fs[revert_reason_prefix_def] >>
  drule_at (Pat `run_inst_seq _ _ = _`) alloca_store_offset_alloca_run_covers >>
  simp[ASCIInumbersTheory.toString_11] >>
  `not_local_ptr cenv es.scopes (STRING #"%" (toString v)) /\
   not_local_ptr cenv es.scopes (STRING #"%" (toString (v+1)))` by
    (qpat_x_assum `!k. _` mp_tac >>
     disch_then (fn th => map_every (fn k => qspec_then k assume_tac th)
       [`0`, `1`]) >> gvs[ADD_COMM]) >>
  disch_then irule >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem alloca_step_ptr_mem_ok:
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  expr_val_at cenv cx t sa sb es v op s /\ ~is_word_type t /\
  ptr_mem_ok cx t v op G tn s /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
  not_local_ptr cenv es.scopes out /\
  (id < sa.cs_next_id \/ sb.cs_next_id <= id) /\ n < dimword(:256) /\
  (!p. op = Var p ==> p <> out) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 ==>
  ptr_mem_ok cx t v op
    (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) s1)
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn) s1
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `eval_operand op s1 = eval_operand op s` by
    (irule alloca_step_operand_preserved >> metis_tac[]) >>
  drule_all alloca_step_site >> strip_tac >>
  simp[ptr_mem_ok_def] >> rpt gen_tac >> strip_tac >>
  `eval_operand op s = SOME w` by metis_tac[] >>
  `val_wf tv v` by (fs[expr_val_at_def] >> metis_tac[]) >>
  qpat_x_assum `ptr_mem_ok _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[ptr_mem_ok_def] >>
  disch_then (qspecl_then [`tv`, `w`] mp_tac) >> simp[] >> strip_tac >>
  conj_tac >-
    (rpt strip_tac >> irule alloca_step_expr_robust_preserved >>
     simp[] >> metis_tac[]) >>
  strip_tac >>
  first_x_assum (drule_then strip_assume_tac) >>
  qexistsl_tac [`x`, `b'`, `sz`] >> simp[] >>
  `x <> out` by metis_tac[] >>
  simp[step_prov_other_output, mk_inst_def]
QED

Theorem alloca_step_ptr_val_ok:
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  expr_val_at cenv cx t sa sb es v op s /\ ptr_val_ok cx t v op G tn s /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
  not_local_ptr cenv es.scopes out /\
  (id < sa.cs_next_id \/ sb.cs_next_id <= id) /\ n < dimword(:256) /\
  (!p. op = Var p ==> p <> out) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 ==>
  ptr_val_ok cx t v op
    (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) s1)
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn) s1
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `ptr_val_ok _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[ptr_val_ok_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >> conj_tac >-
    (Cases_on `op` >> gvs[] >>
     simp[step_taint_other_output, mk_inst_def, op_taint_def]) >>
  strip_tac >> irule alloca_step_ptr_mem_ok >> simp[] >> metis_tac[]
QED

(* Checked allocation-prefix boundaries, including reused allocation sites. *)
Theory revertReasonPrefixPtr
Ancestors
  wordLoadStorePtr revertReasonLayout allocationPtr typedCopyPtr fragExec fragGasSeqPtr ghostPcTransportPtr
  loweringSlice exprLoweringProps bodyPtrDefs fragExecPtr venomExecSemantics venomInst venomState
  ptrDiscipline finite_map words arithmetic exprSimAlloc localPtrsProps compileEnv instIdxIndep
  normalizationAllocPtr decoderGhostFramePtr loweringPosts
  robustCopyTransportPtr emitHelperProps valueEncodingProps

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
    (simp[Abbr `j`] >> simp[step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def, eval_operand_def, mstore_def]) >>
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
     simp[step_inst_base_opcode_eqs, mk_inst_def] >> strip_tac >> first_x_assum ACCEPT_TAC) >>
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
    (simp[step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def, eval_operand_def, w2n_n2w]) >>
  qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
  simp[Once run_inst_seq_def] >>
  qmatch_goalsub_abbrev_tac `run_inst_seq _ s2` >>
  `step_inst_base (mk_inst (id+2) ADD [Var out; Lit off] [p]) s2 =
     OK (update_var p (n2w b + off) s2)` by
    (simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def, eval_operand_def,
          Abbr `s2`, mstore_def, lookup_var_def]) >>
  `stmt_state_rel ctx func cenv cx es (update_var p (n2w b+off) s2)` by
    (irule stmt_state_rel_update_var >> simp[Abbr `s2`]) >>
  simp[Once run_inst_seq_def] >>
  qmatch_goalsub_abbrev_tac `run_inst_seq _ s3` >>
  simp[Once run_inst_seq_def, run_inst_seq_def] >>
  Cases_on `step_inst_base (mk_inst (id+3) ALLOCA [Lit sz] [q]) s3` >>
  simp[] >> strip_tac >> gvs[] >>
  qpat_x_assum `step_inst_base _ s3 = _` mp_tac >>
  simp[step_inst_base_opcode_eqs, mk_inst_def] >> strip_tac >>
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
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def, exec_pure2_def, eval_operand_def] >>
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
  conj_tac
  >- (simp[ptr_covers_def, step_prov_def, set_prov_def, out_prov_def,
       first_prov_def, op_prov_def, mk_inst_def, FLOOKUP_UPDATE,
       FLOOKUP_DRESTRICT, op_taint_def, step_taint_def, out_taint_def,
       set_var_taint_def, mstore_def, update_var_def, lookup_var_def,
       eval_operand_def, w2n_add_2, w2n_n2w, LESS_MOD] >> decide_tac) >>
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
  conj_tac >-
    (strip_tac >> Cases_on `op` >> gvs[] >>
     fs[step_prov_other_output, mk_inst_def, op_prov_def]) >>
  strip_tac >> irule alloca_step_ptr_mem_ok >> simp[] >> metis_tac[]
QED

Theorem mstore_literal_ptr_mem_ok:
  ptr_mem_ok cx t v op G tn s /\
  lookup_var dst s = SOME a /\
  (!tv w. evaluate_type (get_tenv cx) t = SOME tv /\
    eval_operand op s = SOME w ==>
    val_wf tv v /\
    (!i. w2n w <= i /\ i < w2n w + val_footprint tv v ==>
      ~(w2n a <= i /\ i < w2n a + 32))) ==>
  ptr_mem_ok cx t v op
    (step_prov PG G (mk_inst id MSTORE [Var dst; Lit value] [])
      (mstore (w2n a) value s))
    (step_taint (mk_inst id MSTORE [Var dst; Lit value] []) s
      (mstore (w2n a) value s) tn) (mstore (w2n a) value s)
Proof
  strip_tac >>
  `eval_operand (Lit value) s = SOME value /\
   op_taint tn (Lit value) = {}` by simp[eval_operand_def, op_taint_def] >>
  drule_all mstore_ghost_frame >> strip_tac >>
  simp[ptr_mem_ok_def, eval_operand_mstore] >> rpt gen_tac >> strip_tac >>
  first_assum (drule_then strip_assume_tac) >>
  qpat_x_assum `ptr_mem_ok _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[ptr_mem_ok_def] >>
  disch_then (qspecl_then [`tv`, `w`] mp_tac) >> simp[] >> strip_tac >>
  `val_wf tv v` by metis_tac[] >>
  rpt strip_tac >> irule robust_val_in_memory_exterior_frame >>
  conj_tac >- simp[] >>
  qexistsl_tac [`s.vs_memory`, `(mstore (w2n a) value s).vs_memory`,
    `tn.t_mem`, `tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a + 32}`,
    `{i | w2n a <= i /\ i < w2n a + 32}`] >>
  simp[] >> rpt strip_tac >>
  irule mstore_mem_bytes_at_disjoint >> decide_tac
QED

Theorem mstore_literal_ptr_val_ok:
  ptr_val_ok cx t v op G tn s /\ lookup_var dst s = SOME a /\
  (!tv w. evaluate_type (get_tenv cx) t = SOME tv /\
    eval_operand op s = SOME w ==>
    val_wf tv v /\
    (!i. w2n w <= i /\ i < w2n w + val_footprint tv v ==>
      ~(w2n a <= i /\ i < w2n a + 32))) ==>
  ptr_val_ok cx t v op
    (step_prov PG G (mk_inst id MSTORE [Var dst; Lit value] [])
      (mstore (w2n a) value s))
    (step_taint (mk_inst id MSTORE [Var dst; Lit value] []) s
      (mstore (w2n a) value s) tn) (mstore (w2n a) value s)
Proof
  strip_tac >>
  `eval_operand (Lit value) s = SOME value /\
   op_taint tn (Lit value) = {}` by simp[eval_operand_def, op_taint_def] >>
  drule_all mstore_ghost_frame >> strip_tac >>
  qpat_x_assum `ptr_val_ok _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[ptr_val_ok_def] >> strip_tac >> conj_tac >-
    (Cases_on `op` >> gvs[op_taint_def]) >>
  conj_tac >- (strip_tac >> simp[]) >>
  strip_tac >> irule mstore_literal_ptr_mem_ok >> simp[] >> metis_tac[]
QED

Theorem alloca_step_expr_store_disjoint:
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  expr_val_at cenv cx t sa sb es v op s /\ ~is_word_type t /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
  not_local_ptr cenv es.scopes out /\
  (id < sa.cs_next_id \/ sb.cs_next_id <= id) /\
  32 <= n /\ n < dimword(:256) /\
  (!p. op = Var p ==> p <> out) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 /\
  lookup_var out s1 = SOME a ==>
  !tv w. evaluate_type (get_tenv cx) t = SOME tv /\
    eval_operand op s1 = SOME w ==>
    val_wf tv v /\
    (!i. w2n w <= i /\ i < w2n w + val_footprint tv v ==>
      ~(w2n a <= i /\ i < w2n a + 32))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `eval_operand op s1 = eval_operand op s` by
    (irule alloca_step_operand_preserved >> metis_tac[]) >>
  drule_all alloca_step_site >> strip_tac >>
  `a = n2w b` by gvs[eval_operand_def] >>
  `w2n a = b` by (gvs[] >> simp[]) >>
  rpt gen_tac >> strip_tac >> conj_tac >-
    (fs[expr_val_at_def] >> metis_tac[]) >>
  rpt strip_tac >>
  `~(b <= i /\ i < b+n)` by
    (irule alloca_step_expr_disjoint >> simp[] >> metis_tac[]) >>
  decide_tac
QED

Theorem ptr_mem_ok_step_frame:
  ptr_mem_ok cx ty v op G tn s /\
  (!x. op = Var x ==> ~MEM x inst.inst_outputs) /\
  eval_operand op t = eval_operand op s /\ t.vs_memory = s.vs_memory /\
  (step_taint inst s t tn).t_mem = tn.t_mem ==>
  ptr_mem_ok cx ty v op (step_prov PG G inst t) (step_taint inst s t tn) t
Proof
  strip_tac >> simp[ptr_mem_ok_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `ptr_mem_ok _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[ptr_mem_ok_def] >>
  disch_then (qspecl_then [`tv`, `w`] mp_tac) >> simp[] >> strip_tac >>
  simp[] >> strip_tac >>
  qpat_x_assum `val_footprint _ _ <> 0 ==> _` (drule_then strip_assume_tac) >>
  qexistsl_tac [`x`, `b`, `sz`] >> simp[step_prov_other_output]
QED

Theorem ptr_val_ok_step_frame:
  ptr_val_ok cx ty v op G tn s /\
  (!x. op = Var x ==> ~MEM x inst.inst_outputs) /\
  eval_operand op t = eval_operand op s /\ t.vs_memory = s.vs_memory /\
  (step_taint inst s t tn).t_mem = tn.t_mem ==>
  ptr_val_ok cx ty v op (step_prov PG G inst t) (step_taint inst s t tn) t
Proof
  strip_tac >> fs[ptr_val_ok_def] >> conj_tac >-
    (Cases_on `op` >> gvs[op_taint_def, step_taint_other_output]) >>
  conj_tac >-
    (strip_tac >> Cases_on `op` >>
     gvs[op_prov_def, step_prov_other_output]) >>
  strip_tac >>
  irule ptr_mem_ok_step_frame >> simp[]
QED

Theorem add_step_ptr_val_ok:
  ptr_val_ok cx ty v op G tn s /\
  (!x. op = Var x ==> x <> out) ==>
  ptr_val_ok cx ty v op
    (step_prov PG G (mk_inst id ADD [left; right] [out]) (update_var out w s))
    (step_taint (mk_inst id ADD [left; right] [out]) s (update_var out w s) tn)
    (update_var out w s)
Proof
  strip_tac >> irule ptr_val_ok_step_frame >> simp[mk_inst_def] >>
  conj_tac >-
    metis_tac[copy_len_binop_ghost_frame, mk_inst_def] >>
  simp[update_var_def] >> Cases_on `op` >> gvs[eval_operand_def] >>
  simp[lookup_var_def, FLOOKUP_UPDATE, update_var_def] >> metis_tac[]
QED

Theorem ptr_vv_ok_nonmemory_frame:
  ptr_vv_ok cx ty tv (LocatedValue ty' p) es G tn s /\
  p.ptr_location <> LocMemory /\
  op_taint tnf p.ptr_operand = op_taint tn p.ptr_operand /\
  eval_operand p.ptr_operand t = eval_operand p.ptr_operand s /\
  tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
  (t.vs_accounts t.vs_call_ctx.cc_address).storage =
    (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
  t.vs_transient t.vs_call_ctx.cc_address =
    s.vs_transient s.vs_call_ctx.cc_address /\
  op_prov Gf p.ptr_operand = op_prov G p.ptr_operand ==>
  ptr_vv_ok cx ty tv (LocatedValue ty' p) es Gf tnf t
Proof
  simp[ptr_vv_ok_def]
QED

Theorem alloca_mstore_literal_ptr_val_ok:
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  expr_val_at cenv cx ty sa sb es v op s /\ ~is_word_type ty /\
  ptr_val_ok cx ty v op G tn s /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
  not_local_ptr cenv es.scopes out /\
  (id < sa.cs_next_id \/ sb.cs_next_id <= id) /\
  32 <= n /\ n < dimword(:256) /\
  (!p. op = Var p ==> p <> out) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 /\
  lookup_var out s1 = SOME a /\
  G1 = step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) s1 /\
  tn1 = step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn ==>
  ptr_val_ok cx ty v op
    (step_prov PG G1 (mk_inst (id+1) MSTORE [Var out; Lit value] [])
      (mstore (w2n a) value s1))
    (step_taint (mk_inst (id+1) MSTORE [Var out; Lit value] []) s1
      (mstore (w2n a) value s1) tn1) (mstore (w2n a) value s1)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ptr_val_ok cx ty v op G1 tn1 s1` by
    (qpat_x_assum `G1 = _` SUBST_ALL_TAC >>
     qpat_x_assum `tn1 = _` SUBST_ALL_TAC >>
     irule alloca_step_ptr_val_ok >> simp[] >> metis_tac[]) >>
  irule mstore_literal_ptr_val_ok >> simp[] >>
  metis_tac[alloca_step_expr_store_disjoint]
QED

Theorem alloca_step_data_frame:
  step_inst_base (mk_inst id ALLOCA [Lit sz] [out]) s = OK t ==>
  t.vs_memory = s.vs_memory /\ t.vs_accounts = s.vs_accounts /\
  t.vs_transient = s.vs_transient /\ t.vs_call_ctx = s.vs_call_ctx
Proof
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_alloca_def] >>
  Cases_on `FLOOKUP s.vs_allocas id` >> simp[] >-
    (strip_tac >> gvs[update_var_def]) >>
  PairCases_on `x` >> simp[] >> strip_tac >> gvs[update_var_def]
QED

Theorem alloca_step_ptr_vv_nonmemory:
  ptr_vv_ok cx ty tv (LocatedValue ty' p) es G tn s /\
  p.ptr_location <> LocMemory /\
  (!x. p.ptr_operand = Var x ==> x <> out) /\
  step_inst_base (mk_inst id ALLOCA [Lit sz] [out]) s = OK t ==>
  ptr_vv_ok cx ty tv (LocatedValue ty' p) es
    (step_prov PG G (mk_inst id ALLOCA [Lit sz] [out]) t)
    (step_taint (mk_inst id ALLOCA [Lit sz] [out]) s t tn) t
Proof
  strip_tac >>
  drule alloca_step_data_frame >> strip_tac >>
  `op_taint (step_taint (mk_inst id ALLOCA [Lit sz] [out]) s t tn)
     p.ptr_operand = op_taint tn p.ptr_operand` by
    (Cases_on `p.ptr_operand` >> gvs[op_taint_def, step_taint_other_output,
      mk_inst_def]) >>
  `eval_operand p.ptr_operand t = eval_operand p.ptr_operand s` by
    (irule alloca_step_operand_preserved >>
     qexistsl_tac [`id`, `w2n sz`, `out`] >> simp[] >> metis_tac[]) >>
  `op_prov (step_prov PG G (mk_inst id ALLOCA [Lit sz] [out]) t)
     p.ptr_operand = op_prov G p.ptr_operand` by
    (Cases_on `p.ptr_operand` >>
     gvs[op_prov_def, step_prov_def, set_prov_def, mk_inst_def] >>
     rpt CASE_TAC >> gvs[FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]) >>
  `(step_taint (mk_inst id ALLOCA [Lit sz] [out]) s t tn).t_stor = tn.t_stor /\
   (step_taint (mk_inst id ALLOCA [Lit sz] [out]) s t tn).t_trans =
     tn.t_trans` by simp[step_taint_nonmemory_frame, mk_inst_def] >>
  drule_then irule ptr_vv_ok_nonmemory_frame >> fs[]
QED

Theorem local_region_update_nonlocal:
  not_local_ptr cenv scopes out ==>
  (local_region cenv scopes (update_var out w s) name b sz <=>
   local_region cenv scopes s name b sz)
Proof
  simp[local_region_def, not_local_ptr_def, lookup_var_def, update_var_def,
    FLOOKUP_UPDATE] >> rpt strip_tac >> eq_tac >> strip_tac >>
  qexistsl_tac [`entry`, `p`, `w'`] >> simp[] >> metis_tac[]
QED

Theorem expr_val_at_update_nonlocal:
  expr_val_at cenv cx ty sa sb es v op s /\
  not_local_ptr cenv es.scopes out /\
  (!x. op = Var x ==> x <> out) ==>
  expr_val_at cenv cx ty sa sb es v op (update_var out w s)
Proof
  strip_tac >>
  `eval_operand op (update_var out w s) = eval_operand op s` by
    (Cases_on `op` >> gvs[eval_operand_def, lookup_var_def, update_var_def,
      FLOOKUP_UPDATE] >> metis_tac[]) >>
  fs[expr_val_at_def] >>
  simp[update_var_def, GSYM update_var_def, local_region_update_nonlocal] >>
  metis_tac[local_region_update_nonlocal]
QED

Theorem expr_val_at_allocation_frame:
  expr_val_at cenv cx ty sa sb es v op s /\
  eval_operand op t = eval_operand op s /\
  (!aid. sa.cs_next_id <= aid /\ aid < sb.cs_next_id ==>
    FLOOKUP t.vs_allocas aid = FLOOKUP s.vs_allocas aid) /\
  (!name b sz. local_region cenv es.scopes t name b sz <=>
    local_region cenv es.scopes s name b sz) ==>
  expr_val_at cenv cx ty sa sb es v op t
Proof
  rw[expr_val_at_def] >>
  first_x_assum (drule_all_then strip_assume_tac) >> gvs[] >>
  metis_tac[]
QED

Theorem alloca_step_expr_val_at:
  expr_val_at cenv cx ty sa sb es v op s /\
  not_local_ptr cenv es.scopes out /\
  (id < sa.cs_next_id \/ sb.cs_next_id <= id) /\
  (!x. op = Var x ==> x <> out) /\
  step_inst_base (mk_inst id ALLOCA [Lit sz] [out]) s = OK t ==>
  expr_val_at cenv cx ty sa sb es v op t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `eval_operand op t = eval_operand op s` by
    (irule alloca_step_operand_preserved >>
     qexistsl_tac [`id`, `w2n sz`, `out`] >> simp[] >> metis_tac[]) >>
  irule expr_val_at_allocation_frame >> qexists_tac `s` >> simp[] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_alloca_def] >>
  Cases_on `FLOOKUP s.vs_allocas id` >> simp[] >-
    (strip_tac >> gnvs[] >> conj_tac >-
       (simp[local_region_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
        fs[not_local_ptr_def] >> metis_tac[]) >>
     simp[update_var_def, FLOOKUP_UPDATE] >> rpt strip_tac >>
     `aid <> id` by decide_tac >> simp[]) >>
  PairCases_on `x` >> simp[] >> strip_tac >> gnvs[] >>
  simp[update_var_def, GSYM update_var_def, local_region_update_nonlocal]
QED

Theorem expr_val_at_mstore:
  expr_val_at cenv cx ty sa sb es v op (mstore a value s) <=>
  expr_val_at cenv cx ty sa sb es v op s
Proof
  simp[expr_val_at_def, eval_operand_mstore, local_region_def,
    lookup_var_mstore, mstore_def]
QED

Theorem alloca_store_offset_expr_frames:
  expr_val_at cenv cx ty sa sb es v op s /\
  not_local_ptr cenv es.scopes out /\ not_local_ptr cenv es.scopes p /\
  (id < sa.cs_next_id \/ sb.cs_next_id <= id) /\
  (!x. op = Var x ==> x <> out /\ x <> p) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 /\
  step_inst_base (mk_inst (id+1) MSTORE [Var out; Lit value] []) s1 = OK s2 /\
  step_inst_base (mk_inst (id+2) ADD [Var out; Lit off] [p]) s2 = OK s3 /\
  lookup_var out s1 = SOME a ==>
  expr_val_at cenv cx ty sa sb es v op s3
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_val_at cenv cx ty sa sb es v op s1` by
    (irule alloca_step_expr_val_at >> simp[] >> metis_tac[]) >>
  drule_all store_offset_endpoint >> strip_tac >>
  qpat_x_assum `s3 = _` SUBST_ALL_TAC >>
  irule expr_val_at_update_nonlocal >> simp[expr_val_at_mstore] >> metis_tac[]
QED

Theorem alloca_store_offset_ptr_val_ok:
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  expr_val_at cenv cx ty sa sb es v op s /\ ~is_word_type ty /\
  ptr_val_ok cx ty v op G tn s /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
  not_local_ptr cenv es.scopes out /\
  (id < sa.cs_next_id \/ sb.cs_next_id <= id) /\
  32 <= n /\ n < dimword(:256) /\
  (!x. op = Var x ==> x <> out /\ x <> p) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 /\
  step_inst_base (mk_inst (id+1) MSTORE [Var out; Lit value] []) s1 = OK s2 /\
  step_inst_base (mk_inst (id+2) ADD [Var out; Lit off] [p]) s2 = OK s3 /\
  G1 = step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) s1 /\
  tn1 = step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn /\
  G2 = step_prov PG G1 (mk_inst (id+1) MSTORE [Var out; Lit value] []) s2 /\
  tn2 = step_taint (mk_inst (id+1) MSTORE [Var out; Lit value] []) s1 s2 tn1 ==>
  ptr_val_ok cx ty v op
    (step_prov PG G2 (mk_inst (id+2) ADD [Var out; Lit off] [p]) s3)
    (step_taint (mk_inst (id+2) ADD [Var out; Lit off] [p]) s2 s3 tn2) s3
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all alloca_step_site >> strip_tac >>
  `lookup_var out s1 = SOME (n2w b)` by gvs[eval_operand_def] >>
  drule_all store_offset_endpoint >> strip_tac >>
  `ptr_val_ok cx ty v op G2 tn2 s2` by
    (qpat_x_assum `G2 = _` SUBST_ALL_TAC >>
     qpat_x_assum `tn2 = _` SUBST_ALL_TAC >>
     qpat_x_assum `s2 = _` SUBST_ALL_TAC >>
     irule alloca_mstore_literal_ptr_val_ok >> simp[] >> metis_tac[]) >>
  qpat_x_assum `s3 = _` SUBST_ALL_TAC >>
  irule add_step_ptr_val_ok >> metis_tac[]
QED

Theorem alloca_store_offset_alloca_ptr_val_ok:
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  expr_val_at cenv cx ty sa sb es v op s /\ ~is_word_type ty /\
  ptr_val_ok cx ty v op G tn s /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
  MEM (mk_inst (id+3) ALLOCA [Lit (n2w sz)] [q]) (fn_insts func) /\
  not_local_ptr cenv es.scopes out /\ not_local_ptr cenv es.scopes p /\
  not_local_ptr cenv es.scopes q /\
  (id < sa.cs_next_id \/ sb.cs_next_id <= id) /\
  (id+3 < sa.cs_next_id \/ sb.cs_next_id <= id+3) /\
  32 <= n /\ n < dimword(:256) /\ sz < dimword(:256) /\
  (!x. op = Var x ==> x <> out /\ x <> p /\ x <> q) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 /\
  step_inst_base (mk_inst (id+1) MSTORE [Var out; Lit value] []) s1 = OK s2 /\
  step_inst_base (mk_inst (id+2) ADD [Var out; Lit off] [p]) s2 = OK s3 /\
  step_inst_base (mk_inst (id+3) ALLOCA [Lit (n2w sz)] [q]) s3 = OK t /\
  G1 = step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) s1 /\
  tn1 = step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn /\
  G2 = step_prov PG G1 (mk_inst (id+1) MSTORE [Var out; Lit value] []) s2 /\
  tn2 = step_taint (mk_inst (id+1) MSTORE [Var out; Lit value] []) s1 s2 tn1 /\
  G3 = step_prov PG G2 (mk_inst (id+2) ADD [Var out; Lit off] [p]) s3 /\
  tn3 = step_taint (mk_inst (id+2) ADD [Var out; Lit off] [p]) s2 s3 tn2 ==>
  ptr_val_ok cx ty v op
    (step_prov PG G3 (mk_inst (id+3) ALLOCA [Lit (n2w sz)] [q]) t)
    (step_taint (mk_inst (id+3) ALLOCA [Lit (n2w sz)] [q]) s3 t tn3) t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `stmt_state_rel ctx func cenv cx es s3` by
    (irule alloca_store_offset_state_rel >> simp[] >> metis_tac[]) >>
  `ptr_val_ok cx ty v op G3 tn3 s3` by
    (qpat_x_assum `G3 = _` SUBST_ALL_TAC >>
     qpat_x_assum `tn3 = _` SUBST_ALL_TAC >>
     irule alloca_store_offset_ptr_val_ok >> simp[] >> metis_tac[]) >>
  `?b. FLOOKUP s1.vs_allocas id = SOME (b,n) /\
       b+n < dimword(:256) /\ eval_operand (Var out) s1 = SOME (n2w b)` by
    (irule alloca_step_site >> metis_tac[]) >>
  `lookup_var out s1 = SOME (n2w b)` by gvs[eval_operand_def] >>
  `expr_val_at cenv cx ty sa sb es v op s3` by
    (irule alloca_store_offset_expr_frames >> simp[] >> metis_tac[]) >>
  irule alloca_step_ptr_val_ok >> simp[] >> metis_tac[]
QED

Theorem alloca_store_offset_alloca_run_ptr_val_ok:
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  expr_val_at cenv cx ty sa sb es v op s /\ ~is_word_type ty /\
  ptr_val_ok cx ty v op G tn s /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
  MEM (mk_inst (id+3) ALLOCA [Lit (n2w sz)] [q]) (fn_insts func) /\
  not_local_ptr cenv es.scopes out /\ not_local_ptr cenv es.scopes p /\
  not_local_ptr cenv es.scopes q /\
  (id < sa.cs_next_id \/ sb.cs_next_id <= id) /\
  (id+3 < sa.cs_next_id \/ sb.cs_next_id <= id+3) /\
  32 <= n /\ n < dimword(:256) /\ sz < dimword(:256) /\
  (!x. op = Var x ==> x <> out /\ x <> p /\ x <> q) /\
  run_inst_seq
    [mk_inst id ALLOCA [Lit (n2w n)] [out];
     mk_inst (id+1) MSTORE [Var out; Lit value] [];
     mk_inst (id+2) ADD [Var out; Lit off] [p];
     mk_inst (id+3) ALLOCA [Lit (n2w sz)] [q]] s = OK t /\
  inst_seq_ptr D lo ctx func PG G tn
    [mk_inst id ALLOCA [Lit (n2w n)] [out];
     mk_inst (id+1) MSTORE [Var out; Lit value] [];
     mk_inst (id+2) ADD [Var out; Lit off] [p];
     mk_inst (id+3) ALLOCA [Lit (n2w sz)] [q]] s Gf tnf ==>
  ptr_val_ok cx ty v op Gf tnf t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
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
          Abbr `G3`, Abbr `tn3`, Abbr `G4`, Abbr `tn4`] >> metis_tac[]) >>
  qpat_x_assum `Gf = _` SUBST_ALL_TAC >>
  qpat_x_assum `tnf = _` SUBST_ALL_TAC >>
  fs[Abbr `i`, Abbr `j`, Abbr `k`, Abbr `l`] >>
  map_every (fn pat => qpat_assum pat
    (assume_tac o REWRITE_RULE[markerTheory.Abbrev_def]))
    [`Abbrev (G1 = _)`, `Abbrev (tn1 = _)`,
     `Abbrev (G2 = _)`, `Abbrev (tn2 = _)`,
     `Abbrev (G3 = _)`, `Abbrev (tn3 = _)`] >>
  qpat_x_assum `Abbrev (G4 = _)`
    (SUBST_ALL_TAC o REWRITE_RULE[markerTheory.Abbrev_def]) >>
  qpat_x_assum `Abbrev (tn4 = _)`
    (SUBST_ALL_TAC o REWRITE_RULE[markerTheory.Abbrev_def]) >>
  irule alloca_store_offset_alloca_ptr_val_ok >> metis_tac[]
QED

Theorem revert_reason_prefix_ptr_val_ok:
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  expr_val_at cenv cx ty sa sb es v op s /\ ~is_word_type ty /\
  ptr_val_ok cx ty v op G tn s /\
  MEM (mk_inst id ALLOCA [Lit (n2w (64+ms))]
    [STRING #"%" (toString vn)]) (fn_insts func) /\
  MEM (mk_inst (id+3) ALLOCA [Lit (n2w ms)]
    [STRING #"%" (toString (vn+2))]) (fn_insts func) /\
  (!k. k < 3 ==> not_local_ptr cenv es.scopes (STRING #"%" (toString (vn+k)))) /\
  (id+3 < sa.cs_next_id \/ sb.cs_next_id <= id) /\
  64+ms < dimword(:256) /\
  (!x k. op = Var x /\ k < 3 ==> x <> STRING #"%" (toString (vn+k))) /\
  run_inst_seq (revert_reason_prefix id vn ms) s = OK t /\
  inst_seq_ptr D lo ctx func PG G tn (revert_reason_prefix id vn ms) s Gf tnf ==>
  ptr_val_ok cx ty v op Gf tnf t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  fs[revert_reason_prefix_def] >>
  `not_local_ptr cenv es.scopes (STRING #"%" (toString vn)) /\
   not_local_ptr cenv es.scopes (STRING #"%" (toString (vn+1))) /\
   not_local_ptr cenv es.scopes (STRING #"%" (toString (vn+2)))` by
    (qpat_x_assum `!k. k < 3 ==> _` mp_tac >>
     disch_then (fn th => map_every (fn k => qspec_then k assume_tac th)
       [`0`, `1`, `2`]) >> gvs[ADD_COMM]) >>
  `ms < dimword(:256) /\ 32 <= ms+64 /\
   (id < sa.cs_next_id \/ sb.cs_next_id <= id) /\
   (id+3 < sa.cs_next_id \/ sb.cs_next_id <= id+3)` by decide_tac >>
  `!x. op = Var x ==> x <> STRING #"%" (toString vn) /\
    x <> STRING #"%" (toString (vn+1)) /\
    x <> STRING #"%" (toString (vn+2))` by
    (qpat_x_assum `!k. op = _ ==> _` mp_tac >>
     disch_then (fn th => map_every (fn k => qspec_then k assume_tac th)
       [`0`, `1`, `2`]) >> gvs[ADD_COMM] >> metis_tac[]) >>
  irule alloca_store_offset_alloca_run_ptr_val_ok >>
  qpat_assum `run_inst_seq _ _ = OK _` (irule_at Any) >>
  simp[] >> metis_tac[]
QED

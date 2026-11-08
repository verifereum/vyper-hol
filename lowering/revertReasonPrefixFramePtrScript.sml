(* Shared observational effects of the checked encoder prefix. *)
Theory revertReasonPrefixFramePtr
Ancestors revertReasonPrefixPtr ghostObservationPtr decoderGhostFramePtr bodyPtrDefs
  allocationPtr loweringHalt typedCopyPtr ptrDiscipline instIdxIndep
  exprLoweringProps venomInstProps list
  allocaSiteResource localPtrsProps exprSimProps stmtSimLogSuffixFrame
  fragGasSeqPtr revertReasonLayout context venomInst venomExecSemantics venomState finite_map

Theorem inst_seq_ptr_other_output_frame:
  !is D lo ctx func PG G tn s Gf tnf x.
    inst_seq_ptr D lo ctx func PG G tn is s Gf tnf /\
    EVERY (\i. ~MEM x i.inst_outputs) is ==>
    FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tnf (Var x) = op_taint tn (Var x)
Proof
  Induct >> simp[inst_seq_ptr_def] >> rpt gen_tac >>
  Cases_on `step_inst_base h s` >> simp[] >> strip_tac >>
  gvs[] >> first_x_assum drule >>
  simp[step_prov_other_output, step_taint_other_output]
QED

Theorem inst_seq_ptr_nonmemory_taint_frame:
  !is D lo ctx func PG G tn s Gf tnf.
    inst_seq_ptr D lo ctx func PG G tn is s Gf tnf /\
    EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> SSTORE /\
      i.inst_opcode <> TSTORE /\ i.inst_opcode <> ISTORE) is ==>
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    tnf.t_imm = tn.t_imm
Proof
  Induct >> simp[inst_seq_ptr_def] >> rpt gen_tac >>
  Cases_on `step_inst_base h s` >> simp[] >> strip_tac >>
  gvs[] >> first_x_assum drule >>
  simp[step_taint_nonmemory_frame]
QED

Theorem revert_reason_prefix_ghost_observations:
  inst_seq_ptr D lo ctx func PG G tn (revert_reason_prefix id vn ms) s Gf tnf ==>
  (!x. (!k. k < 3 ==> x <> STRING #"%" (toString (vn+k))) ==>
    FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tnf (Var x) = op_taint tn (Var x)) /\
  tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
  tnf.t_imm = tn.t_imm
Proof
  strip_tac >> conj_tac >-
    (gen_tac >> disch_tac >> irule inst_seq_ptr_other_output_frame >>
     goal_assum (drule_at Any) >>
     simp[revert_reason_prefix_def, mk_inst_def] >>
     qpat_x_assum `!k. _` mp_tac >>
     disch_then (fn th => map_every (fn k => qspec_then k assume_tac th)
       [`0`, `1`, `2`]) >> gvs[arithmeticTheory.ADD_COMM]) >>
  irule inst_seq_ptr_nonmemory_taint_frame >>
  goal_assum (drule_at Any) >>
  simp[revert_reason_prefix_def, mk_inst_def]
QED

Theorem alloca_store_add_data_frame:
  step_inst_base (mk_inst id ALLOCA [Lit sz] [out]) s = OK t \/
  step_inst_base (mk_inst id MSTORE [Var out; Lit value] []) s = OK t \/
  step_inst_base (mk_inst id ADD [left; right] [out]) s = OK t ==>
  t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
  t.vs_call_ctx = s.vs_call_ctx
Proof
  strip_tac >- metis_tac[alloca_step_data_frame] >-
    (fs[step_inst_base_def, mk_inst_def, exec_write2_def, AllCaseEqs()] >>
     gvs[mstore_def]) >>
  fs[step_inst_base_def, mk_inst_def, exec_pure2_def, AllCaseEqs()] >>
  gvs[update_var_def]
QED

Theorem revert_reason_prefix_data_frame:
  run_inst_seq (revert_reason_prefix id vn ms) s = OK t ==>
  t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
  t.vs_call_ctx = s.vs_call_ctx
Proof
  simp[revert_reason_prefix_def] >> strip_tac >>
  drule run_inst_seq_four_endpoint >> strip_tac >>
  metis_tac[alloca_store_add_data_frame]
QED

Theorem alloca_store_add_lookup_frame:
  x <> out /\
  (step_inst_base (mk_inst id ALLOCA [Lit sz] [out]) s = OK t \/
   step_inst_base (mk_inst id MSTORE [Var dst; Lit value] []) s = OK t \/
   step_inst_base (mk_inst id ADD [left; right] [out]) s = OK t) ==>
  lookup_var x t = lookup_var x s
Proof
  strip_tac >-
    (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
     simp[step_inst_base_def, mk_inst_def, exec_alloca_def] >>
     Cases_on `FLOOKUP s.vs_allocas id` >> simp[] >-
       (strip_tac >> gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
     PairCases_on `x'` >> simp[] >> strip_tac >>
     gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >-
    (fs[step_inst_base_def, mk_inst_def, exec_write2_def, AllCaseEqs()] >>
     gvs[lookup_var_def, mstore_def]) >>
  fs[step_inst_base_def, mk_inst_def, exec_pure2_def, AllCaseEqs()] >>
  gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem revert_reason_prefix_lookup_frame:
  run_inst_seq (revert_reason_prefix id vn ms) s = OK t /\
  (!k. k < 3 ==> x <> STRING #"%" (toString (vn+k))) ==>
  lookup_var x t = lookup_var x s
Proof
  strip_tac >>
  `x <> STRING #"%" (toString vn) /\
   x <> STRING #"%" (toString (vn+1)) /\
   x <> STRING #"%" (toString (vn+2))` by
    (qpat_x_assum `!k. _` mp_tac >>
     disch_then (fn th => map_every (fn k => qspec_then k assume_tac th)
       [`0`, `1`, `2`]) >> gvs[arithmeticTheory.ADD_COMM]) >>
  fs[revert_reason_prefix_def] >>
  drule run_inst_seq_four_endpoint >> strip_tac >>
  metis_tac[alloca_store_add_lookup_frame]
QED

Theorem alloca_step_memory_taint_bound:
  n < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK t /\
  FLOOKUP t.vs_allocas id = SOME (b,n) ==>
  (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s t tn).t_mem
    SUBSET tn.t_mem UNION {i | b <= i /\ i < b+n}
Proof
  strip_tac >> Cases_on `FLOOKUP s.vs_allocas id` >-
    (drule_all fresh_alloca_ghost >>
     disch_then (qspecl_then [`[]`, `FEMPTY`, `tn`] strip_assume_tac) >>
     drule step_alloca_fresh >> disch_then (qspec_then `n` mp_tac) >>
     simp[] >> disch_then (qspec_then `out` assume_tac) >>
     gvs[update_var_def, FLOOKUP_UPDATE]) >>
  rename1 `FLOOKUP s.vs_allocas id = SOME site` >> PairCases_on `site` >>
  fs[step_inst_base_def, mk_inst_def, exec_alloca_def] >>
  gvs[update_var_def, FLOOKUP_UPDATE] >>
  drule reused_alloca_memory_taint >>
  disch_then (qspecl_then [`out`, `tn`] mp_tac) >>
  simp[mk_inst_def, update_var_def]
QED

Theorem mstore_literal_memory_taint_bound:
  step_inst_base (mk_inst id MSTORE [Var dst; Lit value] []) s = OK t ==>
  (step_taint (mk_inst id MSTORE [Var dst; Lit value] []) s t tn).t_mem
    SUBSET tn.t_mem
Proof
  simp[step_inst_base_def, mk_inst_def, exec_write2_def,
       eval_operand_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  `eval_operand (Lit value) s = SOME value /\ op_taint tn (Lit value) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all (cj 5 mstore_ghost_frame) >> simp[mk_inst_def]
QED

Theorem add_step_memory_taint_frame:
  step_inst_base (mk_inst id ADD [left; right] [out]) s = OK t ==>
  (step_taint (mk_inst id ADD [left; right] [out]) s t tn).t_mem = tn.t_mem
Proof
  simp[step_inst_base_def, mk_inst_def, exec_pure2_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  simp[step_taint_def, mem_taint_def, step_writes_def,
       codegenRelTheory.source_memory_write_ranges_def, written_taint_def,
       new_site_bytes_def, update_var_def, range_bytes_def, FLOOKUP_DEF] >>
  SET_TAC[]
QED

Theorem alloca_store_offset_alloca_memory_taint_bound:
  n < dimword (:256) /\ sz < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 /\
  step_inst_base (mk_inst (id+1) MSTORE [Var out; Lit value] []) s1 = OK s2 /\
  step_inst_base (mk_inst (id+2) ADD [Var out; Lit off] [p]) s2 = OK s3 /\
  step_inst_base (mk_inst (id+3) ALLOCA [Lit (n2w sz)] [q]) s3 = OK t /\
  FLOOKUP s1.vs_allocas id = SOME (b,n) /\
  FLOOKUP t.vs_allocas (id+3) = SOME (c,sz) /\
  inst_seq_ptr D lo ctx func PG G tn
    [mk_inst id ALLOCA [Lit (n2w n)] [out];
     mk_inst (id+1) MSTORE [Var out; Lit value] [];
     mk_inst (id+2) ADD [Var out; Lit off] [p];
     mk_inst (id+3) ALLOCA [Lit (n2w sz)] [q]] s Gf tnf ==>
  tnf.t_mem SUBSET tn.t_mem UNION
    {i | b <= i /\ i < b+n} UNION {i | c <= i /\ i < c+sz}
Proof
  strip_tac >>
  qmatch_asmsub_abbrev_tac `inst_seq_ptr D lo ctx func PG G tn [i;j;k;l] s Gf tnf` >>
  qabbrev_tac `tn1 = step_taint i s s1 tn` >>
  qabbrev_tac `tn2 = step_taint j s1 s2 tn1` >>
  qabbrev_tac `tn3 = step_taint k s2 s3 tn2` >>
  qabbrev_tac `tn4 = step_taint l s3 t tn3` >>
  qabbrev_tac `G1 = step_prov PG G i s1` >>
  qabbrev_tac `G2 = step_prov PG G1 j s2` >>
  qabbrev_tac `G3 = step_prov PG G2 k s3` >>
  qabbrev_tac `G4 = step_prov PG G3 l t` >>
  `~is_terminator j.inst_opcode /\ ~is_terminator k.inst_opcode /\
   ~is_terminator l.inst_opcode` by
    simp[Abbr `j`, Abbr `k`, Abbr `l`, mk_inst_def, is_terminator_def] >>
  `Gf = G4 /\ tnf = tn4` by
    (irule inst_seq_ptr_four_endpoint >> goal_assum (drule_at Any) >>
     simp[Abbr `G1`, Abbr `G2`, Abbr `G3`, Abbr `G4`,
          Abbr `tn1`, Abbr `tn2`, Abbr `tn3`, Abbr `tn4`] >>
     metis_tac[]) >>
  `tn1.t_mem SUBSET tn.t_mem UNION {i | b <= i /\ i < b+n}` by
    (simp[Abbr `tn1`, Abbr `i`] >>
     irule alloca_step_memory_taint_bound >> goal_assum (drule_at Any) >> simp[]) >>
  `tn2.t_mem SUBSET tn1.t_mem` by
    (simp[Abbr `tn2`, Abbr `j`] >>
     irule mstore_literal_memory_taint_bound >> goal_assum (drule_at Any)) >>
  `tn3.t_mem = tn2.t_mem` by
    (simp[Abbr `tn3`, Abbr `k`] >>
     irule add_step_memory_taint_frame >> goal_assum (drule_at Any)) >>
  `tn4.t_mem SUBSET tn3.t_mem UNION {i | c <= i /\ i < c+sz}` by
    (simp[NoAsms, Abbr `tn4`, Abbr `l`] >>
     irule alloca_step_memory_taint_bound >> goal_assum (drule_at Any) >> simp[]) >>
  gvs[] >>
  map_every (fn pat => qpat_x_assum pat mp_tac)
    [`tn4.t_mem SUBSET _`, `tn2.t_mem SUBSET _`, `tn1.t_mem SUBSET _`] >>
  POP_ASSUM_LIST (K all_tac) >> SET_TAC[]
QED

Theorem alloca_store_offset_alloca_memory_frame:
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 /\
  step_inst_base (mk_inst (id+1) MSTORE [Var out; Lit value] []) s1 = OK s2 /\
  step_inst_base (mk_inst (id+2) ADD [Var out; Lit off] [p]) s2 = OK s3 /\
  step_inst_base (mk_inst (id+3) ALLOCA [Lit (n2w sz)] [q]) s3 = OK t /\
  lookup_var out s1 = SOME a /\ 32 <= n /\
  ~(w2n a <= i /\ i < w2n a+n) ==>
  mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory
Proof
  strip_tac >>
  `s1.vs_memory = s.vs_memory /\ t.vs_memory = s3.vs_memory` by
    metis_tac[alloca_step_data_frame] >>
  drule_all store_offset_endpoint >> strip_tac >> gvs[update_var_def] >>
  qpat_x_assum `s1.vs_memory = s.vs_memory` (SUBST1_TAC o SYM) >>
  irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >> decide_tac
QED

Theorem alloca_store_offset_alloca_run_memory_effects:
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
  MEM (mk_inst (id+3) ALLOCA [Lit (n2w sz)] [q]) (fn_insts func) /\
  not_local_ptr cenv es.scopes out /\ not_local_ptr cenv es.scopes p /\
  32 <= n /\ n < dimword (:256) /\ sz < dimword (:256) /\
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
  ?b c. b+n < dimword (:256) /\ c+sz < dimword (:256) /\
    FLOOKUP t.vs_allocas id = SOME (b,n) /\
    FLOOKUP t.vs_allocas (id+3) = SOME (c,sz) /\
    (!i. i NOTIN ({i | b <= i /\ i < b+n} UNION {i | c <= i /\ i < c+sz}) ==>
      mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
    tnf.t_mem SUBSET tn.t_mem UNION
      {i | b <= i /\ i < b+n} UNION {i | c <= i /\ i < c+sz}
Proof
  strip_tac >> drule run_inst_seq_four_endpoint >> strip_tac >>
  drule_all alloca_step_site >> strip_tac >>
  `lookup_var out s1 = SOME (n2w b)` by gvs[eval_operand_def] >>
  `stmt_state_rel ctx func cenv cx es s3` by
    (irule alloca_store_offset_state_rel >> metis_tac[]) >>
  `?c. FLOOKUP t.vs_allocas (id+3) = SOME (c,sz) /\
    c+sz < dimword (:256) /\ eval_operand (Var q) t = SOME (n2w c)` by
    (irule alloca_step_site >> metis_tac[]) >>
  `FLOOKUP t.vs_allocas id = SOME (b,n)` by
    (drule_all store_offset_endpoint >> strip_tac >>
     `s3.vs_allocas = s1.vs_allocas` by simp[update_var_def, mstore_def] >>
     qpat_x_assum `step_inst_base _ s3 = OK t` mp_tac >>
     simp[step_inst_base_def, mk_inst_def, exec_alloca_def, AllCaseEqs()] >>
     strip_tac >> simp[update_var_def, FLOOKUP_UPDATE] >>
     gvs[update_var_def, FLOOKUP_UPDATE]) >>
  qexistsl_tac [`b`, `c`] >> simp[] >> conj_tac >-
    (rpt strip_tac >> irule alloca_store_offset_alloca_memory_frame >>
     goal_assum (drule_at Any) >>
     simp[wordsTheory.w2n_n2w] >> gvs[pred_setTheory.IN_UNION] >>
     metis_tac[wordsTheory.w2n_n2w, arithmeticTheory.LESS_ADD]) >>
  irule alloca_store_offset_alloca_memory_taint_bound >> metis_tac[]
QED

Theorem revert_reason_prefix_memory_effects:
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  MEM (mk_inst id ALLOCA [Lit (n2w (64+ms))]
    [STRING #"%" (toString v)]) (fn_insts func) /\
  MEM (mk_inst (id+3) ALLOCA [Lit (n2w ms)]
    [STRING #"%" (toString (v+2))]) (fn_insts func) /\
  (!k. k < 2 ==> not_local_ptr cenv es.scopes (STRING #"%" (toString (v+k)))) /\
  64+ms < dimword (:256) /\
  run_inst_seq (revert_reason_prefix id v ms) s = OK t /\
  inst_seq_ptr D lo ctx func PG G tn (revert_reason_prefix id v ms) s Gf tnf ==>
  ?b c. b+(64+ms) < dimword (:256) /\ c+ms < dimword (:256) /\
    FLOOKUP t.vs_allocas id = SOME (b,64+ms) /\
    FLOOKUP t.vs_allocas (id+3) = SOME (c,ms) /\
    (!i. i NOTIN ({i | b <= i /\ i < b+(64+ms)} UNION {i | c <= i /\ i < c+ms}) ==>
      mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
    (!i. i NOTIN ({i | b <= i /\ i < b+(64+ms)} UNION {i | c <= i /\ i < c+ms}) /\
      i IN tnf.t_mem ==> i IN tn.t_mem)
Proof
  strip_tac >> fs[revert_reason_prefix_def] >>
  `not_local_ptr cenv es.scopes (STRING #"%" (toString v)) /\
   not_local_ptr cenv es.scopes (STRING #"%" (toString (v+1)))` by
    (qpat_x_assum `!k. _` mp_tac >>
     disch_then (fn th => map_every (fn k => qspec_then k assume_tac th)
       [`0`, `1`]) >> gvs[arithmeticTheory.ADD_COMM]) >>
  `32 <= ms+64 /\ ms < dimword (:256)` by decide_tac >>
  drule_at (Pat `run_inst_seq _ _ = _`) alloca_store_offset_alloca_run_memory_effects >>
  disch_then drule_all >>
  strip_tac >> qexistsl_tac [`b`, `c`] >> simp[] >>
  qpat_x_assum `_ SUBSET _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> SET_TAC[]
QED

Theorem revert_reason_prefix_allocation_frame:
  run_inst_seq (revert_reason_prefix id v ms) s = OK t ==>
  !aid site. FLOOKUP s.vs_allocas aid = SOME site ==>
    FLOOKUP t.vs_allocas aid = SOME site
Proof
  strip_tac >> drule log_run_old_allocas >>
  simp[revert_reason_prefix_def, mk_inst_def]
QED

Theorem revert_reason_prefix_local_region_frame:
  run_inst_seq (revert_reason_prefix id v ms) s = OK t /\
  (!k. k < 3 ==> not_local_ptr cenv scopes (STRING #"%" (toString (v+k)))) /\
  local_region cenv scopes s name b sz ==>
  local_region cenv scopes t name b sz
Proof
  simp[compileEnvTheory.local_region_def] >> strip_tac >>
  `lookup_var p t = lookup_var p s` by
    (irule revert_reason_prefix_lookup_frame >>
     goal_assum (drule_at Any) >> rpt strip_tac >>
     fs[compileEnvTheory.not_local_ptr_def] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem revert_reason_prefix_local_exterior:
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  MEM (mk_inst id ALLOCA [Lit (n2w (64+ms))]
    [STRING #"%" (toString v)]) (fn_insts func) /\
  MEM (mk_inst (id+3) ALLOCA [Lit (n2w ms)]
    [STRING #"%" (toString (v+2))]) (fn_insts func) /\
  (!k. k < 3 ==> not_local_ptr cenv es.scopes (STRING #"%" (toString (v+k)))) /\
  64+ms < dimword (:256) /\
  run_inst_seq (revert_reason_prefix id v ms) s = OK t /\
  FLOOKUP t.vs_allocas id = SOME (b,64+ms) /\
  FLOOKUP t.vs_allocas (id+3) = SOME (c,ms) /\
  local_region cenv es.scopes s name a sz /\ a <= i /\ i < a+sz ==>
  i NOTIN ({i | b <= i /\ i < b+(64+ms)} UNION {i | c <= i /\ i < c+ms})
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx es t` by
    (irule revert_reason_prefix_state_rel >> metis_tac[]) >>
  `local_region cenv es.scopes t name a sz` by
    (irule revert_reason_prefix_local_region_frame >> metis_tac[]) >>
  `not_local_ptr cenv es.scopes (STRING #"%" (toString v)) /\
   not_local_ptr cenv es.scopes (STRING #"%" (toString (v+2)))` by
    (qpat_x_assum `!k. _` mp_tac >>
     disch_then (fn th => map_every (fn k => qspec_then k assume_tac th)
       [`0`, `2`]) >> gvs[arithmeticTheory.ADD_COMM]) >>
  `alloca_inv t /\ local_ptrs_rel func cenv es.scopes t` by
    fs[exprLoweringPropsTheory.stmt_state_rel_def, compileEnvTheory.state_rel_def] >>
  `regions_disjoint b (64+ms) a sz` by
    (irule local_ptrs_rel_alloca_disjoint >>
     qexistsl_tac [`cenv`, `func`,
       `mk_inst id ALLOCA [Lit (n2w (64+ms))] [STRING #"%" (toString v)]`] >>
     simp[mk_inst_def] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  `regions_disjoint c ms a sz` by
    (irule local_ptrs_rel_alloca_disjoint >>
     qexistsl_tac [`cenv`, `func`,
       `mk_inst (id+3) ALLOCA [Lit (n2w ms)] [STRING #"%" (toString (v+2))]`] >>
     simp[mk_inst_def] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  fs[compileEnvTheory.regions_disjoint_def] >> decide_tac
QED

Theorem revert_reason_prefix_old_allocation_exterior:
  alloca_inv t /\ sa.cs_next_id <= id /\
  (!aid site. FLOOKUP s0.vs_allocas aid = SOME site ==>
    FLOOKUP s.vs_allocas aid = SOME site) /\
  run_inst_seq (revert_reason_prefix id v ms) s = OK t /\
  FLOOKUP t.vs_allocas id = SOME (b,64+ms) /\
  FLOOKUP t.vs_allocas (id+3) = SOME (c,ms) /\
  FLOOKUP s0.vs_allocas aid = SOME (a,sz) /\ aid < sa.cs_next_id /\
  a <= i /\ i < a+sz ==>
  i NOTIN ({i | b <= i /\ i < b+(64+ms)} UNION {i | c <= i /\ i < c+ms})
Proof
  strip_tac >>
  `FLOOKUP t.vs_allocas aid = SOME (a,sz)` by
    (drule revert_reason_prefix_allocation_frame >>
     disch_then irule >> metis_tac[]) >>
  `aid <> id /\ aid <> id+3` by decide_tac >>
  `venomMemDefs$regions_disjoint (a,sz) (b,64+ms)` by
    (irule alloca_site_registered_disjoint >> metis_tac[]) >>
  `venomMemDefs$regions_disjoint (a,sz) (c,ms)` by
    (irule alloca_site_registered_disjoint >> metis_tac[]) >>
  fs[venomMemDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem revert_reason_prefix_labels_frame:
  run_inst_seq (revert_reason_prefix id vn ms) s = OK t ==>
  t.vs_labels = s.vs_labels
Proof
  strip_tac >>
  drule_at (Pos hd)
    (Q.ISPEC `\s:venom_state. s.vs_labels` run_inst_seq_preserves_field) >>
  simp[] >> disch_then irule >> rpt strip_tac >>
  fs[revert_reason_prefix_def, MEM, mk_inst_def] >>
  irule venomInstPropsTheory.step_preserves_labels >>
  qexistsl [`ARB`, `0`, `i`] >>
  simp[step_inst_non_invoke, is_terminator_def]
QED

Theorem revert_reason_prefix_ptr_vv_nonmemory:
  ptr_vv_ok cx ty tv (LocatedValue ty' p) es G tn s /\
  p.ptr_location <> LocMemory /\
  (!k. k < 3 ==> p.ptr_operand <> Var (STRING #"%" (toString (v+k)))) /\
  run_inst_seq (revert_reason_prefix id v ms) s = OK t /\
  inst_seq_ptr D lo ctx func PG G tn (revert_reason_prefix id v ms) s Gf tnf ==>
  ptr_vv_ok cx ty tv (LocatedValue ty' p) es Gf tnf t
Proof
  strip_tac >> drule revert_reason_prefix_ghost_observations >> strip_tac >>
  drule revert_reason_prefix_data_frame >> strip_tac >>
  `op_taint tnf p.ptr_operand = op_taint tn p.ptr_operand /\
   eval_operand p.ptr_operand t = eval_operand p.ptr_operand s` by
    (drule revert_reason_prefix_labels_frame >> strip_tac >>
     Cases_on `p.ptr_operand` >> simp[op_taint_def, eval_operand_def] >>
     `!k. k < 3 ==> s' <> STRING #"%" (toString (v+k))` by metis_tac[] >>
     conj_tac >- (first_x_assum drule >> simp[op_taint_def]) >>
     irule revert_reason_prefix_lookup_frame >> metis_tac[]) >>
  `op_prov Gf p.ptr_operand = op_prov G p.ptr_operand` by
    (Cases_on `p.ptr_operand` >> simp[op_prov_def] >>
     `!k. k < 3 ==> s' <> STRING #"%" (toString (v+k))` by metis_tac[] >>
     metis_tac[]) >>
  irule ptr_vv_ok_nonmemory_frame >> metis_tac[]
QED

Theorem revert_reason_prefix_old_ptr_covers:
  ptr_covers G tn x s sz /\
  (!k. k < 3 ==> x <> STRING #"%" (toString (v+k))) /\
  run_inst_seq (revert_reason_prefix id v ms) s = OK t /\
  inst_seq_ptr D lo ctx func PG G tn (revert_reason_prefix id v ms) s Gf tnf ==>
  ptr_covers Gf tnf x t sz
Proof
  strip_tac >> drule revert_reason_prefix_ghost_observations >> strip_tac >>
  drule_all revert_reason_prefix_lookup_frame >> strip_tac >>
  first_x_assum drule >> fs[ptr_covers_def]
QED

Theorem revert_reason_prefix_return_frame:
  ghost_inv d cenv cx es G tn s /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) \/
     cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
     !k. k < 3 ==> x <> STRING #"%" (toString (v+k))) /\
  run_inst_seq (revert_reason_prefix id v ms) s = OK t /\
  inst_seq_ptr D lo ctx func PG G tn (revert_reason_prefix id v ms) s Gf tnf ==>
  return_buf_ptr d cenv Gf tnf t /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
    op_taint tnf (Var x) = {}) /\ stor_taint_ok cx tnf t
Proof
  strip_tac >> drule revert_reason_prefix_ghost_observations >> strip_tac >>
  drule revert_reason_prefix_data_frame >> strip_tac >>
  conj_tac >-
    (Cases_on `d` >> simp[return_buf_ptr_def] >> PairCases_on `x` >>
     fs[ghost_inv_def, return_buf_ptr_def] >>
     conj_tac >-
       (`lookup_var x t = lookup_var x s` by
          (irule revert_reason_prefix_lookup_frame >>
           metis_tac[arithmeticTheory.ADD_COMM]) >> simp[]) >>
     irule revert_reason_prefix_old_ptr_covers >>
     metis_tac[arithmeticTheory.ADD_COMM]) >>
  fs[ghost_inv_def, stor_taint_ok_def] >> metis_tac[]
QED

Theorem revert_reason_prefix_ghost_inv:
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  MEM (mk_inst id ALLOCA [Lit (n2w (64+ms))]
    [STRING #"%" (toString v)]) (fn_insts func) /\
  MEM (mk_inst (id+3) ALLOCA [Lit (n2w ms)]
    [STRING #"%" (toString (v+2))]) (fn_insts func) /\
  (!k. k < 3 ==> not_local_ptr cenv es.scopes (STRING #"%" (toString (v+k)))) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) \/
     cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
     !k. k < 3 ==> x <> STRING #"%" (toString (v+k))) /\
  64+ms < dimword (:256) /\ ghost_inv d cenv cx es G tn s /\
  run_inst_seq (revert_reason_prefix id v ms) s = OK t /\
  inst_seq_ptr D lo ctx func PG G tn (revert_reason_prefix id v ms) s Gf tnf ==>
  ghost_inv d cenv cx es Gf tnf t
Proof
  strip_tac >>
  `!k. k < 2 ==> not_local_ptr cenv es.scopes (STRING #"%" (toString (v+k)))`
    by (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  drule_all revert_reason_prefix_memory_effects >> strip_tac >>
  drule_all revert_reason_prefix_return_frame >> strip_tac >>
  irule ghost_inv_exterior_frame >> simp[] >>
  qexistsl_tac [`G`, `{i | b <= i /\ i < b+(64+ms)} UNION {i | c <= i /\ i < c+ms}`,
    `s`, `tn`] >> simp[] >> rpt gen_tac >> strip_tac >>
  `!k. k < 3 ==> p <> STRING #"%" (toString (v+k))` by
    (fs[compileEnvTheory.not_local_ptr_def] >> metis_tac[]) >>
  `lookup_var p t = lookup_var p s` by
    (irule revert_reason_prefix_lookup_frame >> metis_tac[]) >>
  `local_ptrs_rel func cenv es.scopes s` by
    fs[stmt_state_rel_def, compileEnvTheory.state_rel_def] >>
  `?w. lookup_var p s = SOME w /\ type_memory_size entry.type <= sz /\
       val_wf entry.type entry.value` by
    (fs[compileEnvTheory.local_ptrs_rel_def] >> metis_tac[]) >>
  simp[] >> conj_tac >-
    (irule revert_reason_prefix_old_ptr_covers >> fs[ghost_inv_def] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  `val_footprint entry.type entry.value <= sz` by
    metis_tac[val_footprint_le, arithmeticTheory.LESS_EQ_TRANS] >>
  `local_region cenv es.scopes s name (w2n w) sz` by
    (simp[compileEnvTheory.local_region_def] >> metis_tac[]) >>
  `i NOTIN ({i | b <= i /\ i < b+(64+ms)} UNION {i | c <= i /\ i < c+ms})` by
    (irule revert_reason_prefix_local_exterior >> simp[] >>
     goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
     simp[] >> goal_assum (drule_at (Pat `run_inst_seq _ _ = _`)) >>
     fs[arithmeticTheory.ADD_COMM] >> metis_tac[]) >>
  fs[]
QED

Theorem revert_reason_prefix_ghost_kept:
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  MEM (mk_inst id ALLOCA [Lit (n2w (64+ms))]
    [STRING #"%" (toString v)]) (fn_insts func) /\
  MEM (mk_inst (id+3) ALLOCA [Lit (n2w ms)]
    [STRING #"%" (toString (v+2))]) (fn_insts func) /\
  (!k. k < 3 ==> not_local_ptr cenv es.scopes (STRING #"%" (toString (v+k)))) /\
  64+ms < dimword (:256) /\ sa.cs_next_id <= id /\ sa.cs_next_var <= v /\
  local_ptrs_reserved cenv sa /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x s = SOME w) /\
  (!aid site. FLOOKUP s0.vs_allocas aid = SOME site ==> FLOOKUP s.vs_allocas aid = SOME site) /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  run_inst_seq (revert_reason_prefix id v ms) s = OK t /\
  inst_seq_ptr D lo ctx func PG G tn (revert_reason_prefix id v ms) s Gf tnf ==>
  ghost_kept cenv es sa G0 tn0 s0 Gf tnf
Proof
  strip_tac >>
  `!k. k < 2 ==> not_local_ptr cenv es.scopes (STRING #"%" (toString (v+k)))`
    by (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  drule_all revert_reason_prefix_memory_effects >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es t` by
    (irule revert_reason_prefix_state_rel >> metis_tac[]) >>
  `alloca_inv t` by fs[stmt_state_rel_def, compileEnvTheory.state_rel_def] >>
  irule ghost_kept_exterior_frame >>
  qexistsl_tac [`G`, `{i | b <= i /\ i < b+(64+ms)} UNION {i | c <= i /\ i < c+ms}`, `tn`] >>
  simp[] >> conj_tac >-
    (drule revert_reason_prefix_ghost_observations >> strip_tac >>
     gen_tac >> disch_tac >> first_x_assum irule >>
     fs[compileEnvTheory.not_fresh_at_def] >> rpt strip_tac >>
     first_x_assum irule >> decide_tac) >>
  conj_tac >- suspend "initial_locals" >> suspend "old_allocations"
QED

Resume revert_reason_prefix_ghost_kept[old_allocations]:
  rpt gen_tac >> strip_tac >>
  `i NOTIN ({i | b <= i /\ i < b+(64+ms)} UNION {i | c <= i /\ i < c+ms})` by
    (irule revert_reason_prefix_old_allocation_exterior >> simp[] >>
     goal_assum (drule_at (Pat `FLOOKUP s0.vs_allocas _ = _`)) >>
     simp[] >> goal_assum (drule_at (Pat `run_inst_seq _ _ = _`)) >>
     fs[arithmeticTheory.ADD_COMM] >> metis_tac[]) >> fs[]
QED

Resume revert_reason_prefix_ghost_kept[initial_locals]:
  rpt gen_tac >> strip_tac >>
  `local_region cenv es.scopes s n b' sz` by
    (irule local_region_frame_fwd >> metis_tac[]) >>
  `i NOTIN ({i | b <= i /\ i < b+(64+ms)} UNION {i | c <= i /\ i < c+ms})` by
    (irule revert_reason_prefix_local_exterior >> simp[] >>
     goal_assum (drule_at (Pat `local_region _ _ s _ _ _`)) >>
     simp[] >> goal_assum (drule_at (Pat `run_inst_seq _ _ = _`)) >>
     fs[arithmeticTheory.ADD_COMM] >> metis_tac[]) >> fs[]
QED

Finalise revert_reason_prefix_ghost_kept

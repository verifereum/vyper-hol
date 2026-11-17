Theory abiBytesEncoderCopyGhost
Ancestors
  abiBytestringCode abiEncoderRounding emitHelperProps exprLoweringProps
  fragGasSeqPtr bodyPtrDefs ptrCoverage ptrSafetyTransport
  ghostPcTransportPtr instIdxIndep
  ptrSafeRun ptrDiscipline venomInstProofs venomExecSemantics
  venomMemDefs venomState venomInst words list arithmetic finite_map

Theorem bytes_encoder_copy_ghosts:
  LENGTH N = 9 /\ ALL_DISTINCT N /\ src NOTIN set N /\ dst NOTIN set N /\
  eval_operand (Var src) a = SOME p /\ eval_operand (Var dst) a = SOME q /\
  eval_operand (Var (EL 0 N)) a = SOME (n2w n) /\
  op_taint tn (Var (EL 0 N)) = {} /\
  eval_operand (Var (EL 3 N)) a = SOME (n2w (w2n q + contractABI$ceil32 n)) /\
  ptr_covers G tn (EL 3 N) a 32 /\
  w2n p + 32 + n <= a.vs_alloca_next /\
  w2n p + 32 + n < dimword (:256) /\
  w2n q + 32 + contractABI$ceil32 n <= a.vs_alloca_next /\
  w2n q + 32 + contractABI$ceil32 n < dimword (:256) /\
  regions_disjoint (w2n p,32+n) (w2n q,32+contractABI$ceil32 n) /\
  ptr_covers G tn src a (32+n) /\
  ptr_covers G tn dst a (32+contractABI$ceil32 n) /\
  (!i. w2n p <= i /\ i < w2n p + 32 + n ==> i NOTIN tn.t_mem) /\
  ~ctx_has_dalloca ctx /\ allocas_from lo a /\
  run_inst_seq (TAKE 3 (DROP 4 (bytestring_encoder_insts id N (Var dst) (Var src)))) a = OK b ==>
  ?H tm.
    (!D k. inst_seq_ptr D lo ctx func PG G tn
      (TAKE 3 (DROP 4 (bytestring_encoder_insts id N (Var dst) (Var src))))
      (a with vs_inst_idx := k) H tm) /\
    ptr_covers H tm dst b (32+contractABI$ceil32 n) /\
    (!i. w2n q <= i /\ i < w2n q + 32 + contractABI$ceil32 n ==> i NOTIN tm.t_mem) /\
    (!i. i < w2n q \/ w2n q + 32 + contractABI$ceil32 n <= i ==>
      (i IN tm.t_mem <=> i IN tn.t_mem)) /\
    eval_operand (Var src) b = SOME p /\ eval_operand (Var dst) b = SOME q /\
    eval_operand (Var (EL 0 N)) b = SOME (n2w n) /\
    op_taint tm (Var (EL 0 N)) = {} /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    b.vs_allocas = a.vs_allocas /\ b.vs_alloca_next = a.vs_alloca_next /\
    (!x. x <> EL 4 N ==>
      lookup_var x b = lookup_var x a /\ FLOOKUP H x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x))
Proof
  rpt strip_tac >>
  `?v0 v1 v2 v3 v4 v5 v6 v7 v8. N = [v0;v1;v2;v3;v4;v5;v6;v7;v8]` by
    (gvs[LENGTH_EQ_NUM_compute] >> metis_tac[]) >>
  gvs[bytestring_encoder_insts_def] >>
  `n <= contractABI$ceil32 n /\ contractABI$ceil32 n < n+32` by
    metis_tac[abi_encoder_ceil32_bounds] >>
  `32+n < dimword (:256) /\ w2n q + contractABI$ceil32 n < dimword (:256)` by decide_tac >>
  `step_inst_base (mk_inst (id+4) MSTORE [Var v3; Lit 0w] []) a =
    OK (mstore (w2n q + contractABI$ceil32 n) 0w a)` by
    (drule step_MSTORE >> simp[w2n_n2w, eval_operand_def]) >>
  qabbrev_tac `a1 = mstore (w2n q + contractABI$ceil32 n) 0w a` >>
  `step_inst_base (mk_inst (id+5) ADD [Lit 32w; Var v0] [v4]) a1 =
    OK (update_var v4 (n2w (32+n)) a1)` by
    (rewrite_tac[GSYM word_add_n2w] >> irule step_ADD >>
     simp[Abbr `a1`, mstore_def, write_memory_with_expansion_def,
       eval_operand_def, lookup_var_def] >> gvs[eval_operand_def, lookup_var_def]) >>
  qabbrev_tac `a2 = update_var v4 (n2w (32+n)) a1` >>
  `eval_operand (Var dst) a2 = SOME q /\
   eval_operand (Var src) a2 = SOME p /\
   eval_operand (Var v4) a2 = SOME (n2w (32+n))` by
    (simp[Abbr `a2`, Abbr `a1`, mstore_def, write_memory_with_expansion_def,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     gvs[eval_operand_def, lookup_var_def]) >>
  `step_inst_base (mk_inst (id+6) MCOPY [Var dst; Var src; Var v4] []) a2 =
    OK (mcopy (w2n q) (w2n p) (32+n) a2)` by
    (simp[step_inst_base_def, w2n_n2w]) >>
  qabbrev_tac `a3 = mcopy (w2n q) (w2n p) (32+n) a2` >>
  `b = a3` by gvs[run_inst_seq_def] >>
  qabbrev_tac `i0 = mk_inst (id+4) MSTORE [Var v3; Lit 0w] []` >>
  qabbrev_tac `i1 = mk_inst (id+5) ADD [Lit 32w; Var v0] [v4]` >>
  qabbrev_tac `i2 = mk_inst (id+6) MCOPY [Var dst; Var src; Var v4] []` >>
  qabbrev_tac `G1 = step_prov PG G i0 a1` >>
  qabbrev_tac `G2 = step_prov PG G1 i1 a2` >>
  qabbrev_tac `G3 = step_prov PG G2 i2 a3` >>
  qabbrev_tac `tn1 = step_taint i0 a a1 tn` >>
  qabbrev_tac `tn2 = step_taint i1 a1 a2 tn1` >>
  qabbrev_tac `tn3 = step_taint i2 a2 a3 tn2` >>
  `tn1 = tn with t_mem := tn.t_mem DIFF
    {i | w2n q + contractABI$ceil32 n <= i /\ i < w2n q + contractABI$ceil32 n + 32}` by
    (simp[Abbr `tn1`, Abbr `i0`, Abbr `a1`, step_taint_def, mem_taint_def,
      new_site_bytes_def, step_writes_def, written_taint_def, out_taint_def,
      set_var_taint_def, adopt_reset_def, store_taint_def, imm_taint_def,
      codegenRelTheory.source_memory_write_ranges_def, memLocDefsTheory.mem_write_ops_def,
      range_bytes_def, mstore_def, write_memory_with_expansion_def, mk_inst_def,
      eval_operand_def, FLOOKUP_DEF, op_taint_def, w2n_n2w,
      codegenRelTheory.fixed_source_write_range_def, DRESTRICT_UNIV,
      taint_component_equality, pred_setTheory.EXTENSION, SF CONJ_ss] >> decide_tac) >>
  `tn2 = tn1 with t_var := tn1.t_var |+ (v4,{})` by
    (simp[Abbr `tn2`, Abbr `i1`, Abbr `a2`, step_taint_def, mem_taint_def,
      new_site_bytes_def, step_writes_def, written_taint_def, out_taint_def,
      set_var_taint_def, adopt_reset_def, store_taint_def, imm_taint_def,
      codegenRelTheory.source_memory_write_ranges_def, memLocDefsTheory.mem_write_ops_def,
      range_bytes_def, update_var_def, mk_inst_def, eval_operand_def,
      FLOOKUP_DEF, taint_component_equality, pred_setTheory.EXTENSION, SF CONJ_ss]) >>
  `written_taint tn2 i2 a2 = {}` by
    (simp[written_taint_def, Abbr `i2`, w2n_n2w, pred_setTheory.EXTENSION] >>
     rpt strip_tac >> gvs[] >>
     Cases_on `i < n+32` >> simp[] >>
     `i + w2n p NOTIN tn.t_mem` by (first_x_assum irule >> decide_tac) >> simp[]) >>
  `tn3 = tn2 with t_mem := tn2.t_mem DIFF
    {i | w2n q <= i /\ i < w2n q+32+n}` by
    (simp[Abbr `tn3`, Abbr `i2`, Abbr `a3`, step_taint_def, mem_taint_def,
      new_site_bytes_def, step_writes_def, set_var_taint_def, out_taint_def,
      adopt_reset_def, store_taint_def, imm_taint_def, mcopy_def,
      write_memory_with_expansion_def, codegenRelTheory.source_memory_write_ranges_def,
      codegenRelTheory.sized_source_write_range_def, memLocDefsTheory.mem_write_ops_def,
      range_bytes_def, mk_inst_def, DRESTRICT_UNIV, w2n_n2w, FLOOKUP_DEF,
      taint_component_equality, pred_setTheory.EXTENSION, SF CONJ_ss] >> decide_tac) >>
  `G1 = G /\ G2 = set_prov G [v4] (FLOOKUP G v0) /\ G3 = G2` by
    (Cases_on `FLOOKUP G v0` >>
     simp[Abbr `G1`, Abbr `G2`, Abbr `G3`, Abbr `i0`, Abbr `i1`, Abbr `i2`,
      step_prov_def, out_prov_def, set_prov_def, first_prov_def, op_prov_def,
      mk_inst_def, DRESTRICT_UNIV]) >>
  `!x. x <> v4 ==> lookup_var x a3 = lookup_var x a` by
    (simp[Abbr `a3`, mcopy_def, write_memory_with_expansion_def, lookup_var_def] >>
     simp[Abbr `a2`, update_var_def, FLOOKUP_UPDATE] >>
     simp[Abbr `a1`, mstore_def, write_memory_with_expansion_def]) >>
  `a3.vs_allocas = a.vs_allocas /\ a3.vs_alloca_next = a.vs_alloca_next` by
    (simp[Abbr `a3`, mcopy_def, write_memory_with_expansion_def] >>
     simp[Abbr `a2`, update_var_def] >>
     simp[Abbr `a1`, mstore_def, write_memory_with_expansion_def]) >>
  qexistsl_tac [`G3`, `tn3`] >>
  reverse conj_tac >-
    (Cases_on `FLOOKUP G v0` >> simp[set_prov_def] >>
     simp[ptr_covers_def, op_taint_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
     simp[eval_operand_def] >>
     gvs[ptr_covers_def, eval_operand_def, lookup_var_def, op_taint_def] >>
     rpt strip_tac >> simp[] >> decide_tac) >>
  `~is_terminator i0.inst_opcode /\ ~is_terminator i1.inst_opcode /\
   ~is_terminator i2.inst_opcode` by
    simp[Abbr `i0`, Abbr `i1`, Abbr `i2`, mk_inst_def, is_terminator_def] >>
  `!D k. ptr_inst_ok D lo 0 ctx func G tn i0 (a with vs_inst_idx := k)` by
    (simp[Abbr `i0`, ptr_inst_ok_def, step_inst_non_invoke,
       step_inst_inst_idx_indep, exec_result_map_def] >>
     simp[access_ok_def, taint_ok_def,
       codegenRelTheory.source_memory_write_ranges_def,
       codegenRelTheory.fixed_source_write_range_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       memLocDefsTheory.mem_write_ops_def, memLocDefsTheory.mem_read_ops_def,
       mk_inst_def, op_taint_def, eval_operand_def, w2n_n2w] >>
     gvs[ptr_covers_def, eval_operand_def, op_taint_def, Abbr `a1`, mstore_def,
       write_memory_with_expansion_def] >>
     rpt strip_tac >> gvs[allocas_from_def] >> metis_tac[]) >>
  `a2.vs_requests = a1.vs_requests /\ a3.vs_requests = a2.vs_requests /\
   a1.vs_allocas = a.vs_allocas /\ a2.vs_allocas = a.vs_allocas` by
    (simp[Abbr `a3`, mcopy_def, write_memory_with_expansion_def] >>
     simp[Abbr `a2`, update_var_def] >>
     simp[Abbr `a1`, mstore_def, write_memory_with_expansion_def]) >>
  `(?base cap. FLOOKUP G src = SOME (base,cap) /\
      base <= w2n p /\ w2n p + (32+n) <= base+cap) /\
   (?base cap. FLOOKUP G dst = SOME (base,cap) /\
      base <= w2n q /\ w2n q + (32+n) <= base+cap)` by
    (conj_tac >-
       (qpat_x_assum `ptr_covers G tn src a _` mp_tac >>
        simp[ptr_covers_def] >> rpt strip_tac >>
        gvs[eval_operand_def] >> metis_tac[]) >>
     qpat_x_assum `ptr_covers G tn dst a _` mp_tac >>
     simp[ptr_covers_def] >> rpt strip_tac >>
     gvs[eval_operand_def] >>
     mp_tac (Q.INST [`cnt` |-> `n`] abi_encoder_ceil32_bounds) >> decide_tac) >>
  `FLOOKUP G2 src = FLOOKUP G src /\ FLOOKUP G2 dst = FLOOKUP G dst` by
    (Cases_on `FLOOKUP G v0` >>
     simp[set_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]) >>
  `op_taint tn1 (Var v0) = {} /\ op_taint tn2 (Var src) = {} /\
   op_taint tn2 (Var dst) = {} /\ op_taint tn2 (Var v4) = {}` by
    (simp[op_taint_def, FLOOKUP_UPDATE] >>
     gvs[ptr_covers_def, op_taint_def]) >>
  `!k. access_ok lo G1 func i1 (a1 with vs_inst_idx := k) /\
       access_ok lo G2 func i2 (a2 with vs_inst_idx := k)` by
    (simp[Abbr `i1`, Abbr `i2`, access_ok_def,
       codegenRelTheory.source_memory_write_ranges_def,
       codegenRelTheory.sized_source_write_range_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       memLocDefsTheory.mem_write_ops_def, memLocDefsTheory.mem_read_ops_def,
       mk_inst_def, eval_operand_def, w2n_n2w] >>
     rpt strip_tac >> gvs[eval_operand_def] >> metis_tac[]) >>
  `!k. taint_ok func tn1 i1 (a1 with vs_inst_idx := k) /\
       taint_ok func tn2 i2 (a2 with vs_inst_idx := k)` by
    (simp[Abbr `i1`, Abbr `i2`, taint_ok_def, mk_inst_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       memLocDefsTheory.mem_read_ops_def] >>
     rpt strip_tac >> gvs[] >> Cases_on `op` >>
     gvs[op_taint_def] >> Cases_on `s = v4` >> gvs[] >>
     spose_not_then strip_assume_tac >> gvs[] >> metis_tac[]) >>
  `!D k. ptr_inst_ok D lo 0 ctx func G1 tn1 i1 (a1 with vs_inst_idx := k) /\
    ptr_inst_ok D lo 0 ctx func G2 tn2 i2 (a2 with vs_inst_idx := k)` by
    (`i1.inst_opcode = ADD /\ i2.inst_opcode = MCOPY` by
       simp[Abbr `i1`, Abbr `i2`, mk_inst_def] >>
     simp[ptr_inst_ok_def, step_inst_non_invoke, step_inst_inst_idx_indep,
       exec_result_map_def] >>
     gvs[Abbr `i1`, Abbr `i2`, mk_inst_def, allocas_from_def] >>
     rpt strip_tac >> metis_tac[]) >>
  qpat_x_assum `G1 = G` kall_tac >>
  qpat_x_assum `G2 = set_prov _ _ _` kall_tac >>
  qpat_x_assum `G3 = G2` kall_tac >>
  qpat_x_assum `tn1 = tn with t_mem := _` kall_tac >>
  qpat_x_assum `tn2 = tn1 with t_var := _` kall_tac >>
  qpat_x_assum `tn3 = tn2 with t_mem := _` kall_tac >>
  simp[inst_seq_ptr_def, step_inst_inst_idx_indep, exec_result_map_def,
    Abbr `G3`, Abbr `G2`, Abbr `G1`, Abbr `tn3`, Abbr `tn2`, Abbr `tn1`]
QED

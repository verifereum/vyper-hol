Theory abiBytesEncoderPrefixGhost
Ancestors
  abiBytestringCode abiEncoderRounding emitHelperProps exprLoweringProps
  fragGasSeqPtr bodyPtrDefs ptrCoverage ptrSafetyTransport
  ghostPcTransportPtr instIdxIndep
  ptrSafeRun ptrDiscipline venomInstProofs venomExecSemantics
  venomMemDefs venomState venomInst words list arithmetic finite_map

Theorem bytes_encoder_prefix_ghosts:
  LENGTH N = 9 /\ ALL_DISTINCT N /\ src NOTIN set N /\ dst NOTIN set N /\
  eval_operand (Var src) a = SOME p /\ eval_operand (Var dst) a = SOME q /\
  mload (w2n p) a = n2w n /\
  w2n p + 32 + n <= a.vs_alloca_next /\
  w2n p + 32 + n < dimword (:256) /\
  w2n q + 32 + contractABI$ceil32 n <= a.vs_alloca_next /\
  w2n q + 32 + contractABI$ceil32 n < dimword (:256) /\
  ptr_covers G tn src a (32+n) /\
  ptr_covers G tn dst a (32+contractABI$ceil32 n) /\
  (!i. w2n p <= i /\ i < w2n p + 32 + n ==> i NOTIN tn.t_mem) /\
  ~ctx_has_dalloca ctx /\ allocas_from lo a /\
  run_inst_seq (TAKE 4 (bytestring_encoder_insts id N (Var dst) (Var src))) a = OK b ==>
  ?H tm.
    (!D. inst_seq_ptr D lo ctx func PG G tn
      (TAKE 4 (bytestring_encoder_insts id N (Var dst) (Var src))) a H tm) /\
    eval_operand (Var (EL 0 N)) b = SOME (n2w n) /\
    op_taint tm (Var (EL 0 N)) = {} /\
    eval_operand (Var (EL 3 N)) b = SOME (n2w (w2n q + contractABI$ceil32 n)) /\
    ptr_covers H tm (EL 3 N) b 32 /\
    eval_operand (Var src) b = SOME p /\ eval_operand (Var dst) b = SOME q /\
    ptr_covers H tm src b (32+n) /\
    ptr_covers H tm dst b (32+contractABI$ceil32 n) /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    b.vs_allocas = a.vs_allocas /\ b.vs_alloca_next = a.vs_alloca_next /\
    (!x. x NOTIN set (TAKE 4 N) ==>
      lookup_var x b = lookup_var x a /\ FLOOKUP H x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x))
Proof
  rpt strip_tac >>
  `?v0 v1 v2 v3 v4 v5 v6 v7 v8. N = [v0;v1;v2;v3;v4;v5;v6;v7;v8]` by
    (gvs[LENGTH_EQ_NUM_compute] >> metis_tac[]) >>
  gvs[bytestring_encoder_insts_def] >>
  `n + 31 < dimword (:256)` by decide_tac >>
  `step_inst_base (mk_inst id MLOAD [Var src] [v0]) a =
    OK (update_var v0 (n2w n) a)` by metis_tac[step_MLOAD] >>
  qabbrev_tac `a1 = update_var v0 (n2w n) a` >>
  `step_inst_base (mk_inst (id+1) ADD [Lit 31w; Var v0] [v1]) a1 =
    OK (update_var v1 (31w + n2w n) a1)` by
    (irule step_ADD >> simp[Abbr `a1`, eval_operand_def, lookup_var_update_var]) >>
  qabbrev_tac `a2 = update_var v1 (31w + n2w n) a1` >>
  `step_inst_base (mk_inst (id+2) AND
      [Lit 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w;
       Var v1] [v2]) a2 =
    OK (update_var v2 (n2w (contractABI$ceil32 n)) a2)` by
    (`step_inst_base (mk_inst (id+2) AND
       [Lit 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w;
        Var v1] [v2]) a2 = OK (update_var v2
        (0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w &&
         (31w + n2w n)) a2)` by
       (irule step_AND >> simp[Abbr `a2`, eval_operand_def, lookup_var_update_var]) >>
     gvs[abi_encoder_round_ceil32]) >>
  qabbrev_tac `a3 = update_var v2 (n2w (contractABI$ceil32 n)) a2` >>
  `step_inst_base (mk_inst (id+3) ADD [Var dst; Var v2] [v3]) a3 =
    OK (update_var v3 (q + n2w (contractABI$ceil32 n)) a3)` by
    (irule step_ADD >>
     simp[Abbr `a3`, Abbr `a2`, Abbr `a1`,
       eval_operand_def, lookup_var_update_var] >> gvs[eval_operand_def]) >>
  qabbrev_tac `a4 = update_var v3 (q + n2w (contractABI$ceil32 n)) a3` >>
  `b = a4` by (gvs[run_inst_seq_def]) >>
  qabbrev_tac `i0 = mk_inst id MLOAD [Var src] [v0]` >>
  qabbrev_tac `i1 = mk_inst (id+1) ADD [Lit 31w; Var v0] [v1]` >>
  qabbrev_tac `i2 = mk_inst (id+2) AND
    [Lit 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w;
     Var v1] [v2]` >>
  qabbrev_tac `i3 = mk_inst (id+3) ADD [Var dst; Var v2] [v3]` >>
  qabbrev_tac `G1 = step_prov PG G i0 a1` >>
  qabbrev_tac `G2 = step_prov PG G1 i1 a2` >>
  qabbrev_tac `G3 = step_prov PG G2 i2 a3` >>
  qabbrev_tac `G4 = step_prov PG G3 i3 a4` >>
  qabbrev_tac `tn1 = step_taint i0 a a1 tn` >>
  qabbrev_tac `tn2 = step_taint i1 a1 a2 tn1` >>
  qabbrev_tac `tn3 = step_taint i2 a2 a3 tn2` >>
  qabbrev_tac `tn4 = step_taint i3 a3 a4 tn3` >>
  `mem_word_taint tn.t_mem (w2n p) = {}` by
    (simp[mem_word_taint_def, pred_setTheory.EXTENSION] >>
     gen_tac >> Cases_on `x < 32` >> simp[] >> first_x_assum irule >> simp[]) >>
  `tn1 = tn with t_var := tn.t_var |+ (v0,{})` by
    (simp[Abbr `tn1`, Abbr `i0`, Abbr `a1`,
       step_taint_def, mem_taint_def, new_site_bytes_def, step_writes_def,
       written_taint_def, out_taint_def, set_var_taint_def, adopt_reset_def,
       store_taint_def, imm_taint_def, codegenRelTheory.source_memory_write_ranges_def,
       memLocDefsTheory.mem_write_ops_def, range_bytes_def, update_var_def, mk_inst_def,
       eval_operand_def, FLOOKUP_DEF, taint_component_equality, pred_setTheory.EXTENSION, SF CONJ_ss]) >>
  `tn2 = tn1 with t_var := tn1.t_var |+ (v1,{})` by
    (simp[Abbr `tn2`, Abbr `i1`, Abbr `a2`,
       step_taint_def, mem_taint_def, new_site_bytes_def, step_writes_def,
       written_taint_def, out_taint_def, set_var_taint_def, adopt_reset_def,
       store_taint_def, imm_taint_def, codegenRelTheory.source_memory_write_ranges_def,
       memLocDefsTheory.mem_write_ops_def, range_bytes_def, update_var_def, mk_inst_def,
       eval_operand_def, FLOOKUP_DEF, taint_component_equality, pred_setTheory.EXTENSION, SF CONJ_ss]) >>
  `tn3 = tn2 with t_var := tn2.t_var |+ (v2,{})` by
    (simp[Abbr `tn3`, Abbr `i2`, Abbr `a3`,
       step_taint_def, mem_taint_def, new_site_bytes_def, step_writes_def,
       written_taint_def, out_taint_def, set_var_taint_def, adopt_reset_def,
       store_taint_def, imm_taint_def, codegenRelTheory.source_memory_write_ranges_def,
       memLocDefsTheory.mem_write_ops_def, range_bytes_def, update_var_def, mk_inst_def,
       eval_operand_def, FLOOKUP_DEF, taint_component_equality, pred_setTheory.EXTENSION, SF CONJ_ss]) >>
  `tn4 = tn3 with t_var := tn3.t_var |+ (v3,{})` by
    (Cases_on `lookup_var dst a3` >>
     simp[Abbr `tn4`, Abbr `i3`, Abbr `a4`,
       step_taint_def, mem_taint_def, new_site_bytes_def, step_writes_def,
       written_taint_def, out_taint_def, set_var_taint_def, adopt_reset_def,
       store_taint_def, imm_taint_def, codegenRelTheory.source_memory_write_ranges_def,
       memLocDefsTheory.mem_write_ops_def, range_bytes_def, update_var_def, mk_inst_def,
       eval_operand_def, FLOOKUP_DEF, taint_component_equality, pred_setTheory.EXTENSION, SF CONJ_ss]) >>
  `?dbase dsz. FLOOKUP G dst = SOME (dbase,dsz) /\
    dbase <= w2n q /\ w2n q + 32 + contractABI$ceil32 n <= dbase + dsz` by
    (qpat_x_assum `ptr_covers G tn dst a _` mp_tac >>
     simp[ptr_covers_def] >> strip_tac >> gvs[eval_operand_def] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `G1 = DRESTRICT G (COMPL {v0})` by
    simp[Abbr `G1`, Abbr `i0`, step_prov_def, out_prov_def, set_prov_def, mk_inst_def] >>
  `G2 = DRESTRICT G1 (COMPL {v1})` by
    simp[Abbr `G2`, Abbr `i1`, step_prov_def, out_prov_def, set_prov_def,
      first_prov_def, op_prov_def, mk_inst_def, FLOOKUP_DRESTRICT] >>
  `G3 = DRESTRICT G2 (COMPL {v2})` by
    simp[Abbr `G3`, Abbr `i2`, step_prov_def, out_prov_def, set_prov_def, mk_inst_def] >>
  `G4 = G3 |+ (v3,(dbase,dsz))` by
    simp[Abbr `G4`, Abbr `i3`, step_prov_def, out_prov_def, set_prov_def,
      first_prov_def, op_prov_def, mk_inst_def, FLOOKUP_DRESTRICT] >>
  qexistsl_tac [`G4`, `tn4`] >>
  reverse conj_tac >-
    (simp[Abbr `a4`, Abbr `a3`, Abbr `a2`, Abbr `a1`,
       eval_operand_def, lookup_var_update_var, update_var_def, lookup_var_def,
       op_taint_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT,
       ptr_covers_def, GSYM word_add_n2w, ADD_COMM] >>
     gvs[ptr_covers_def, eval_operand_def, lookup_var_def, op_taint_def,
       GSYM word_add_n2w, w2n_n2w, WORD_ADD_COMM] >>
     `contractABI$ceil32 n < dimword (:256)` by decide_tac >>
     `w2n q + w2n (n2w (contractABI$ceil32 n):bytes32) < dimword (:256)` by
       (simp[w2n_n2w] >> decide_tac) >>
     drule w2n_add_2 >> simp[w2n_n2w] >> decide_tac) >>
  `~is_terminator i0.inst_opcode /\ ~is_terminator i1.inst_opcode /\
   ~is_terminator i2.inst_opcode /\ ~is_terminator i3.inst_opcode` by
    simp[Abbr `i0`, Abbr `i1`, Abbr `i2`, Abbr `i3`, mk_inst_def, is_terminator_def] >>
  `!D. ptr_inst_ok D lo 0 ctx func G tn i0 a` by
    (simp[Abbr `i0`, ptr_inst_ok_def, access_ok_def, taint_ok_def,
       codegenRelTheory.source_memory_write_ranges_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       memLocDefsTheory.mem_write_ops_def, memLocDefsTheory.mem_read_ops_def,
       mk_inst_def, step_inst_non_invoke] >>
     qpat_x_assum `ptr_covers G tn src a _` mp_tac >>
     simp[ptr_covers_def, eval_operand_def] >> rpt strip_tac >>
     gvs[eval_operand_def, Abbr `a1`, update_var_def] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `!D k. ptr_inst_ok D lo 0 ctx func G1 tn1 i1 (a1 with vs_inst_idx := k) /\
    ptr_inst_ok D lo 0 ctx func G2 tn2 i2 (a2 with vs_inst_idx := k) /\
    ptr_inst_ok D lo 0 ctx func G3 tn3 i3 (a3 with vs_inst_idx := k)` by
    (`i1.inst_opcode = ADD /\ i2.inst_opcode = AND /\ i3.inst_opcode = ADD` by
       simp[Abbr `i1`, Abbr `i2`, Abbr `i3`, mk_inst_def] >>
     simp[ptr_inst_ok_def, step_inst_non_invoke, step_inst_inst_idx_indep,
       exec_result_map_def] >>
     rw[Abbr `i1`, Abbr `i2`, Abbr `i3`,
       access_ok_def, taint_ok_def,
       codegenRelTheory.source_memory_write_ranges_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       memLocDefsTheory.mem_write_ops_def, memLocDefsTheory.mem_read_ops_def,
       mk_inst_def, step_inst_non_invoke, op_taint_def, FLOOKUP_UPDATE,
       allocas_from_def, Abbr `a4`, Abbr `a3`, Abbr `a2`, Abbr `a1`, update_var_def] >>
     (gvs[allocas_from_def, ptr_covers_def, op_taint_def]
       >>~- ([`_ \/ _`], Cases_on `op` >> gvs[] >>
         rename1 `u <> dst /\ u <> v2 \/ _` >>
         Cases_on `u = dst` >> gvs[] >> Cases_on `u = v2` >> gvs[])) >>
     metis_tac[]) >>
  qpat_x_assum `G1 = DRESTRICT _ _` kall_tac >>
  qpat_x_assum `G2 = DRESTRICT _ _` kall_tac >>
  qpat_x_assum `G3 = DRESTRICT _ _` kall_tac >>
  qpat_x_assum `G4 = _ |+ _` kall_tac >>
  qpat_x_assum `tn1 = tn with t_var := _` kall_tac >>
  qpat_x_assum `tn2 = tn1 with t_var := _` kall_tac >>
  qpat_x_assum `tn3 = tn2 with t_var := _` kall_tac >>
  qpat_x_assum `tn4 = tn3 with t_var := _` kall_tac >>
  simp[inst_seq_ptr_def, step_inst_inst_idx_indep, exec_result_map_def,
    Abbr `G4`, Abbr `G3`, Abbr `G2`, Abbr `G1`,
    Abbr `tn4`, Abbr `tn3`, Abbr `tn2`, Abbr `tn1`]
QED

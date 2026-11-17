(* Pointer assertinsts for the resolved 32-byte memory Append suffix. *)
Theory appendMemoryPtr
Ancestors
  fragGasSeqPtr ghostPcTransportPtr
  exprPtrCtorImmStore exprPtrUnwrapCopyEdges exprPtrUnwrapScalarEdges
  exprPtrUnwrapFrames typedCopyLoopHeaderPtr wordLoadStorePtr
  bodyPtrBopScalarStep bodyPtrBopAssert ptrSafetyTransport
  bodyPtrBopInLoadOutput bodyPtrMakeArrayMloadFrame
  bodyPtrDefs ptrSafeRun ptrDiscipline codegenRel contextCodegenRel
  exprLowering exprLoweringProps emitHelper emitHelperProps compileEnv loweringStateRelDefs
  instIdxIndep instSeqComposePtr decoderGhostFramePtr
  exprPtrUnwrapOffsetSegment exprPtrUnwrapStoreSegment bodyPtrPopScalarTransfer
  venomExecSemantics venomInst venomState finite_map list rich_list words

Theorem append_memory_success_prefix[local]:
  lv <> ov /\ p <> lv /\ p <> ov /\
  lookup_var p s = SOME bp /\ ptr_covers G tn p s (32*(1+cap)) /\
  (!i. w2n bp <= i /\ i < w2n bp+32 ==> i NOTIN tn.t_mem) /\
  cap < dimword (:256) /\ L = w2n (mload (w2n bp) s) /\ L < cap /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  ?H tm t.
    run_inst_seq [mk_inst id MLOAD [Var p] [lv];
      mk_inst (id+1) LT [Var lv; Lit (n2w cap)] [ov];
      mk_inst (id+2) ASSERT [Var ov] []] s = OK t /\
    (!k. inst_seq_ptr D lo ctx fn PG G tn
      [mk_inst id MLOAD [Var p] [lv];
       mk_inst (id+1) LT [Var lv; Lit (n2w cap)] [ov];
       mk_inst (id+2) ASSERT [Var ov] []]
      (s with vs_inst_idx := k) H tm) /\
    t = update_var ov 1w (update_var lv (mload (w2n bp) s) s) /\
    ptr_covers H tm p t (32*(1+cap)) /\
    lookup_var lv t = SOME (n2w L) /\ op_prov H (Var lv) = NONE /\
    op_taint tm (Var lv) = {} /\ allocas_from lo t /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!x. x <> lv /\ x <> ov ==>
      FLOOKUP H x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  qabbrev_tac `load = mk_inst id MLOAD [Var p] [lv]` >>
  qabbrev_tac `test = mk_inst (id+1) LT [Var lv; Lit (n2w cap)] [ov]` >>
  qabbrev_tac `assertinst = mk_inst (id+2) ASSERT [Var ov] []` >>
  qabbrev_tac `s1 = update_var lv (mload (w2n bp) s) s` >>
  qabbrev_tac `s2 = update_var ov 1w s1` >>
  qabbrev_tac `G1 = step_prov PG G load s1` >>
  qabbrev_tac `tn1 = step_taint load s s1 tn` >>
  qabbrev_tac `G2 = step_prov PG G1 test s2` >>
  qabbrev_tac `tn2 = step_taint test s1 s2 tn1` >>
  `step_inst_base load s = OK s1 /\
   step_inst_base test s1 = OK s2 /\ step_inst_base assertinst s2 = OK s2` by
    simp[Abbr `load`, Abbr `test`, Abbr `assertinst`, Abbr `s1`, Abbr `s2`,
         step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def,
         exec_pure2_def, eval_operand_def, lookup_var_def, update_var_def,
         FLOOKUP_UPDATE, bool_to_word_def, w2n_n2w, arithmeticTheory.LESS_MOD] >>
  `ptr_covers G tn p s 32` by
    (gvs[ptr_covers_def] >> goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
  `op_taint tn1 (Var lv) = {}` by
    (simp[Abbr `tn1`, Abbr `load`, Abbr `s1`] >>
     irule (cj 1 mload_ghost_clean) >> simp[eval_operand_def] >> metis_tac[]) >>
  `op_prov G1 (Var lv) = NONE` by
    simp[Abbr `G1`, Abbr `load`, op_prov_def, scalar_load_output_prov] >>
  `G2 = DRESTRICT G1 (COMPL {ov}) /\
   tn2 = tn1 with t_var := tn1.t_var |+ (ov,{})` by
    (simp[Abbr `G2`, Abbr `tn2`, Abbr `test`] >> conj_tac
     >- (irule (cj 1 typed_copy_loop_arith_ghost_clean) >>
         simp[] >> qexists_tac `s2` >> simp[]) >>
     irule (cj 2 typed_copy_loop_arith_ghost_clean) >>
     simp[Abbr `s2`, update_var_def]) >>
  qexistsl_tac [`G2`, `tn2`, `s2`] >>
  conj_tac >- simp[run_inst_seq_def] >>
  conj_tac >- suspend "assertinsts" >> suspend "frame"
QED

Resume append_memory_success_prefix[assertinsts]:
  `!k. ptr_inst_ok D lo 0 ctx fn G tn load (s with vs_inst_idx := k)` by
    (gen_tac >> simp[Abbr `load`] >> irule ptr_inst_ok_mload_lo >>
     simp[allocas_from_def]) >>
  `!k. ptr_inst_ok D lo 0 ctx fn G1 tn1 test (s1 with vs_inst_idx := k)` by
    (gen_tac >> irule ptr_inst_ok_lower_bound_transport >>
     conj_tac >- simp[allocas_from_def, Abbr `s1`, update_var_def] >>
     qexists_tac `0` >> simp[] >>
     simp[Abbr `test`] >> irule bop_scalar_ptr_inst_ok >>
     simp[step_inst_inst_idx_indep, mk_inst_def, is_terminator_def,
          exec_result_map_def, GSYM mk_inst_def] >>
     gvs[op_taint_def, op_prov_def]) >>
  `op_taint tn2 (Var ov) = {}` by simp[op_taint_def, FLOOKUP_UPDATE] >>
  `!k. ptr_inst_ok D lo 0 ctx fn G2 tn2 assertinst (s2 with vs_inst_idx := k)` by
    (gen_tac >> irule ptr_inst_ok_lower_bound_transport >>
     conj_tac >- simp[allocas_from_def, Abbr `s1`, Abbr `s2`, update_var_def] >>
     qexists_tac `0` >>
     simp[Abbr `s2`, Abbr `s1`, allocas_from_def, update_var_def] >>
     simp[Abbr `assertinst`] >> irule bop_assert_ptr_inst_ok >>
     simp[op_taint_def, FLOOKUP_UPDATE]) >>
  `~is_terminator load.inst_opcode /\ ~is_terminator test.inst_opcode /\
   ~is_terminator assertinst.inst_opcode` by
    simp[Abbr `load`, Abbr `test`, Abbr `assertinst`, mk_inst_def, is_terminator_def] >>
  `!H tm u. step_prov PG H assertinst u = H /\
      step_taint assertinst u u tm = tm` by
    simp[Abbr `assertinst`, bop_assert_ghost] >>
  gen_tac >> pure_rewrite_tac[inst_seq_ptr_def] >>
  simp[step_inst_inst_idx_indep, exec_result_map_def,
       GSYM copy_update_inst_idx, Abbr `G1`, Abbr `tn1`,
       Abbr `G2`, Abbr `tn2`] >> metis_tac[]
QED

Resume append_memory_success_prefix[frame]:
  `ptr_covers G1 tn1 p s1 (32*(1+cap))` by
    (simp[Abbr `G1`, Abbr `tn1`, Abbr `load`, Abbr `s1`] >>
     irule mload_preserves_ptr_covers >> simp[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  `ptr_covers G2 tn2 p s2 (32*(1+cap))` by
    (gvs[ptr_covers_def, Abbr `s2`, lookup_var_def, update_var_def,
         FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_prov_def, op_taint_def] >>
     goal_assum (drule_at Any) >> simp[]) >>
  simp[Abbr `s2`, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       Abbr `s1`, allocas_from_def, op_prov_def, op_taint_def,
       FLOOKUP_DRESTRICT] >>
  simp[GSYM op_prov_def, GSYM op_taint_def] >>
  simp[Abbr `G1`, Abbr `tn1`, Abbr `load`, mload_ghost_frame] >>
  rpt strip_tac >>
  simp[op_taint_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  simp[SRULE[op_taint_def] mload_ghost_frame] >>
  gvs[op_prov_def, op_taint_def]
QED

Finalise append_memory_success_prefix[local]

Theorem append_memory_success_tail[local]:
  ALL_DISTINCT [p;lv;dv;offv;ep;nv] /\
  vop <> Var dv /\ vop <> Var offv /\ vop <> Var ep /\ vop <> Var nv /\
  lookup_var p s = SOME bp /\ lookup_var lv s = SOME (n2w L) /\
  op_prov G (Var lv) = NONE /\ op_taint tn (Var lv) = {} /\
  eval_operand vop s = SOME w /\ op_taint tn vop = {} /\
  ptr_covers G tn p s (32*(1+cap)) /\ L < cap /\
  w2n bp+32*(1+cap) <= dimword (:256) /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  ?H tm t.
    run_inst_seq [mk_inst id ADD [Var p;Lit 32w] [dv];
      mk_inst (id+1) MUL [Var lv;Lit 32w] [offv];
      mk_inst (id+2) ADD [Var dv;Var offv] [ep];
      mk_inst (id+3) MSTORE [Var ep;vop] [];
      mk_inst (id+4) ADD [Var lv;Lit 1w] [nv];
      mk_inst (id+5) MSTORE [Var p;Var nv] []] s = OK t /\
    (!k. inst_seq_ptr D lo ctx fn PG G tn
      [mk_inst id ADD [Var p;Lit 32w] [dv];
       mk_inst (id+1) MUL [Var lv;Lit 32w] [offv];
       mk_inst (id+2) ADD [Var dv;Var offv] [ep];
       mk_inst (id+3) MSTORE [Var ep;vop] [];
       mk_inst (id+4) ADD [Var lv;Lit 1w] [nv];
       mk_inst (id+5) MSTORE [Var p;Var nv] []]
      (s with vs_inst_idx := k) H tm) /\
    tm.t_mem = (tn.t_mem DIFF
      {i | w2n bp+32*(1+L) <= i /\ i < w2n bp+32*(1+L)+32}) DIFF
      {i | w2n bp <= i /\ i < w2n bp+32} /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!x. x <> dv /\ x <> offv /\ x <> ep /\ x <> nv ==>
      FLOOKUP H x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `p <> dv` by gvs[ALL_DISTINCT] >>
  `32 < 32*(1+cap) /\ 32+32*cap <= 32*(1+cap) /\
   w2n bp+32 < dimword (:256)` by decide_tac >>
  `?G1 tn1 s1.
    run_inst_seq [mk_inst id ADD [Var p;Lit 32w] [dv]] s = OK s1 /\
    inst_seq_ptr D lo ctx fn PG G tn [mk_inst id ADD [Var p;Lit 32w] [dv]] s G1 tn1 /\
    s1 = update_var dv (bp+32w) s /\ ptr_covers G1 tn1 dv s1 (32*cap) /\
    tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
    tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
    (!x. x <> dv ==> FLOOKUP G1 x = FLOOKUP G x /\
      op_taint tn1 (Var x) = op_taint tn (Var x)) /\
    allocas_from lo s1 /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s1) /\
    (!x c. x <> dv /\ ptr_covers G tn x s c ==> ptr_covers G1 tn1 x s1 c)` by
    (irule copy_offset_segment >> simp[eval_operand_def, op_taint_def] >>
     qexists_tac `32*(1+cap)` >> gvs[]) >>
  `step_inst_base (mk_inst id ADD [Var p;Lit 32w] [dv]) s = OK s1` by
    (gvs[run_inst_seq_def] >> gvs[AllCaseEqs()]) >>
  `!k. ptr_inst_ok D lo 0 ctx fn G tn (mk_inst id ADD [Var p;Lit 32w] [dv])
      (s with vs_inst_idx := k)` by
    (gen_tac >> irule ptr_inst_ok_copy_arith >>
     gvs[ptr_covers_def, op_taint_def, allocas_from_def] >> metis_tac[]) >>
  `!k. inst_seq_ptr D lo ctx fn PG G tn [mk_inst id ADD [Var p;Lit 32w] [dv]]
      (s with vs_inst_idx := k) G1 tn1` by
    (qpat_x_assum `inst_seq_ptr _ _ _ _ _ _ _ _ s _ _` mp_tac >>
     simp[inst_seq_ptr_def] >> strip_tac >> gen_tac >>
     `~is_terminator (mk_inst id ADD [Var p;Lit 32w] [dv]).inst_opcode` by
       simp[mk_inst_def, is_terminator_def] >>
     simp[step_inst_inst_idx_indep, exec_result_map_def] >> gvs[exec_result_map_def]) >>
  qabbrev_tac `mulinst = mk_inst (id+1) MUL [Var lv;Lit 32w] [offv]` >>
  qabbrev_tac `s2 = update_var offv (n2w L * 32w) s1` >>
  qabbrev_tac `G2 = step_prov PG G1 mulinst s2` >>
  qabbrev_tac `tn2 = step_taint mulinst s1 s2 tn1` >>
  `lookup_var lv s1 = SOME (n2w L) /\ op_prov G1 (Var lv) = NONE /\
   op_taint tn1 (Var lv) = {}` by
    (gvs[ALL_DISTINCT, lookup_var_def, update_var_def, op_prov_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  `step_inst_base mulinst s1 = OK s2` by
    (simp[Abbr `mulinst`, Abbr `s2`, step_inst_base_opcode_eqs, mk_inst_def,
          exec_pure2_def, eval_operand_def] >> gvs[]) >>
  `G2 = DRESTRICT G1 (COMPL {offv}) /\
   tn2 = tn1 with t_var := tn1.t_var |+ (offv,{})` by
    (simp[Abbr `G2`, Abbr `tn2`, Abbr `mulinst`] >> conj_tac
     >- (irule (cj 1 typed_copy_loop_arith_ghost_clean) >>
         simp[] >> conj_tac
         >- (qexists_tac `tn1` >> rpt strip_tac >> gvs[op_taint_def]) >>
         qexists_tac `s2` >> simp[]) >>
     irule (cj 2 typed_copy_loop_arith_ghost_clean) >>
     simp[Abbr `s2`, update_var_def] >> rpt strip_tac >> gvs[op_taint_def]) >>
  `!k. ptr_inst_ok D lo 0 ctx fn G1 tn1 mulinst (s1 with vs_inst_idx := k)` by
    (gen_tac >> irule ptr_inst_ok_lower_bound_transport >>
     conj_tac >- simp[allocas_from_def] >>
     qexists_tac `0` >> simp[] >>
     simp[Abbr `mulinst`] >> irule bop_scalar_ptr_inst_ok >>
     `~is_terminator (mk_inst (id+1) MUL [Var lv;Lit 32w] [offv]).inst_opcode` by
       simp[mk_inst_def, is_terminator_def] >>
     simp[step_inst_inst_idx_indep, exec_result_map_def] >>
     gvs[op_taint_def, op_prov_def, exec_result_map_def]) >>
  `!k. inst_seq_ptr D lo ctx fn PG G1 tn1 [mulinst]
      (s1 with vs_inst_idx := k) G2 tn2` by
    (gen_tac >>
     `~is_terminator mulinst.inst_opcode` by
       simp[Abbr `mulinst`, mk_inst_def, is_terminator_def] >>
     simp[inst_seq_ptr_def, step_inst_inst_idx_indep, exec_result_map_def,
          Abbr `G2`, Abbr `tn2`] >> gvs[]) >>
  `dv <> offv` by gvs[ALL_DISTINCT] >>
  `lookup_var dv s2 = SOME (bp+32w)` by
    simp[Abbr `s2`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `eval_operand (Var offv) s2 = SOME (n2w (32*L))` by
    (simp[Abbr `s2`, eval_operand_def, lookup_var_def, update_var_def,
          FLOOKUP_UPDATE] >> pure_rewrite_tac[GSYM word_mul_n2w] >> simp[WORD_MULT_COMM]) >>
  `op_taint tn2 (Var offv) = {}` by simp[op_taint_def, FLOOKUP_UPDATE] >>
  `allocas_from lo s2` by simp[Abbr `s2`, allocas_from_def, update_var_def] >>
  `ptr_covers G2 tn2 dv s2 (32*cap)` by
    (gvs[ptr_covers_def, Abbr `s2`, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
         FLOOKUP_DRESTRICT, op_prov_def, op_taint_def] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `w2n (bp+32w) = w2n bp+32` by
    simp[word_add_def, w2n_n2w, arithmeticTheory.LESS_MOD] >>
  `32*L < 32*cap /\ 32*L+32 <= 32*cap /\
   w2n (bp+32w)+32*L < dimword (:256) /\ dv <> ep` by
    (gvs[ALL_DISTINCT] >> decide_tac) >>
  `?G3 tn3 s3.
    run_inst_seq [mk_inst (id+2) ADD [Var dv;Var offv] [ep]] s2 = OK s3 /\
    inst_seq_ptr D lo ctx fn PG G2 tn2 [mk_inst (id+2) ADD [Var dv;Var offv] [ep]] s2 G3 tn3 /\
    s3 = update_var ep ((bp+32w)+n2w (32*L)) s2 /\ ptr_covers G3 tn3 ep s3 32 /\
    tn3.t_mem = tn2.t_mem /\ tn3.t_stor = tn2.t_stor /\
    tn3.t_trans = tn2.t_trans /\ tn3.t_imm = tn2.t_imm /\
    (!x. x <> ep ==> FLOOKUP G3 x = FLOOKUP G2 x /\
      op_taint tn3 (Var x) = op_taint tn2 (Var x)) /\
    allocas_from lo s3 /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s3) /\
    (!x c. x <> ep /\ ptr_covers G2 tn2 x s2 c ==> ptr_covers G3 tn3 x s3 c)` by
    (irule copy_offset_segment >> simp[] >> qexists_tac `32*cap` >> simp[] >> metis_tac[]) >>
  `!k. inst_seq_ptr D lo ctx fn PG G2 tn2
    [mk_inst (id+2) ADD [Var dv;Var offv] [ep]]
    (s2 with vs_inst_idx := k) G3 tn3` by suspend "element_add_uniform" >>
  `eval_operand (Var ep) s3 = SOME (bp+32w+n2w (32*L))` by
    simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `eval_operand vop s3 = SOME w /\ op_taint tn3 vop = {}` by
    (Cases_on `vop` >>
     gvs[eval_operand_def, lookup_var_def, update_var_def, Abbr `s2`,
         FLOOKUP_UPDATE, op_taint_def] >> metis_tac[]) >>
  drule_all (copy_store_segment |> Q.INST [`id` |-> `id+3`, `v` |-> `vop`]) >>
  disch_then (qspecl_then [`id`,`fn`,`PG`,`D`]
    (qx_choosel_then [`G4`,`tn4`,`s4`] strip_assume_tac)) >>
  `!k. inst_seq_ptr D lo ctx fn PG G3 tn3
     [mk_inst (id+3) MSTORE [Var ep;vop] []]
     (s3 with vs_inst_idx := k) G4 tn4` by suspend "element_store_uniform" >>
  `lookup_var lv s4 = SOME (n2w L) /\ op_prov G4 (Var lv) = NONE /\
   op_taint tn4 (Var lv) = {}` by
    (gvs[ALL_DISTINCT, Abbr `s2`, lookup_var_def, update_var_def,
         mstore_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_prov_def,
         op_taint_def] >> metis_tac[]) >>
  qabbrev_tac `incinst = mk_inst (id+4) ADD [Var lv;Lit 1w] [nv]` >>
  qabbrev_tac `s5 = update_var nv (n2w L+1w) s4` >>
  qabbrev_tac `G5 = step_prov PG G4 incinst s5` >>
  qabbrev_tac `tn5 = step_taint incinst s4 s5 tn4` >>
  `step_inst_base incinst s4 = OK s5` by
    (simp[Abbr `incinst`, Abbr `s5`, step_inst_base_opcode_eqs, mk_inst_def,
          exec_pure2_def, eval_operand_def] >> gvs[]) >>
  `G5 = DRESTRICT G4 (COMPL {nv}) /\
   tn5 = tn4 with t_var := tn4.t_var |+ (nv,{})` by suspend "increment_ghost" >>
  `!k. inst_seq_ptr D lo ctx fn PG G4 tn4 [incinst]
      (s4 with vs_inst_idx := k) G5 tn5` by suspend "increment_uniform" >>
  `ptr_covers G1 tn1 p s1 (32*(1+cap))` by (gvs[ALL_DISTINCT] >> metis_tac[]) >>
  `ptr_covers G2 tn2 p s2 (32*(1+cap))` by
    (gvs[ptr_covers_def, Abbr `s2`, lookup_var_def, update_var_def,
         FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_taint_def, ALL_DISTINCT] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `ptr_covers G3 tn3 p s3 (32*(1+cap))` by (gvs[ALL_DISTINCT] >> metis_tac[]) >>
  `ptr_covers G4 tn4 p s4 (32*(1+cap))` by metis_tac[] >>
  `ptr_covers G5 tn5 p s5 32` by
    (gvs[ptr_covers_def, Abbr `s5`, lookup_var_def, update_var_def,
         FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_taint_def, ALL_DISTINCT] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `eval_operand (Var p) s5 = SOME bp /\
   eval_operand (Var nv) s5 = SOME (n2w L+1w) /\
   op_taint tn5 (Var nv) = {} /\ allocas_from lo s5` by
    (simp[Abbr `s5`, Abbr `s2`, eval_operand_def, lookup_var_def,
         update_var_def, mstore_def, FLOOKUP_UPDATE, op_taint_def,
         allocas_from_def] >> gvs[ALL_DISTINCT] >>
     metis_tac[lookup_var_def, allocas_from_def]) >>
  mp_tac (copy_store_segment |> SPEC_ALL |> Q.INST
    [`G` |-> `G5`, `tn` |-> `tn5`, `root` |-> `p`, `s` |-> `s5`,
     `addr` |-> `bp`, `v` |-> `Var nv`, `value` |-> `n2w L+1w`,
     `id` |-> `id+5`]) >>
  impl_tac >- simp[] >>
  disch_then (qx_choosel_then [`G6`,`tn6`,`s6`] strip_assume_tac) >>
  `!k. inst_seq_ptr D lo ctx fn PG G5 tn5
     [mk_inst (id+5) MSTORE [Var p;Var nv] []]
     (s5 with vs_inst_idx := k) G6 tn6` by suspend "header_store_uniform" >>
  qexistsl [`G6`,`tn6`,`s6`] >>
  conj_tac >- suspend "tail_run" >>
  conj_tac >- suspend "tail_uniform" >>
  conj_tac >- suspend "tail_memory" >>
  suspend "tail_frame"
QED

Resume append_memory_success_tail[increment_ghost]:
  simp[Abbr `G5`, Abbr `tn5`, Abbr `incinst`, Abbr `s5`] >>
  irule pop_scalar_binary_ghost >> simp[op_prov_def, op_taint_def]
QED

Resume append_memory_success_tail[increment_uniform]:
  `!k. ptr_inst_ok D lo 0 ctx fn G4 tn4 incinst (s4 with vs_inst_idx := k)` by
    (gen_tac >> irule ptr_inst_ok_lower_bound_transport >>
     conj_tac >- simp[allocas_from_def] >> qexists_tac `0` >> simp[] >>
     simp[Abbr `incinst`] >> irule bop_scalar_ptr_inst_ok >>
     `~is_terminator (mk_inst (id+4) ADD [Var lv;Lit 1w] [nv]).inst_opcode` by
       simp[mk_inst_def, is_terminator_def] >>
     simp[step_inst_inst_idx_indep, exec_result_map_def] >>
     gvs[op_taint_def, op_prov_def, exec_result_map_def]) >>
  gen_tac >>
  `~is_terminator incinst.inst_opcode` by
    simp[Abbr `incinst`, mk_inst_def, is_terminator_def] >>
  simp[inst_seq_ptr_def, step_inst_inst_idx_indep, exec_result_map_def,
       Abbr `G5`, Abbr `tn5`] >> gvs[]
QED

Resume append_memory_success_tail[element_add_uniform]:
  `!k. ptr_inst_ok D lo 0 ctx fn G2 tn2
      (mk_inst (id+2) ADD [Var dv;Var offv] [ep])
      (s2 with vs_inst_idx := k)` by
    (gen_tac >> irule ptr_inst_ok_copy_arith >>
     gvs[ptr_covers_def, op_taint_def, allocas_from_def] >> metis_tac[]) >>
  `step_inst_base (mk_inst (id+2) ADD [Var dv;Var offv] [ep]) s2 = OK s3` by
    (gvs[run_inst_seq_def] >> gvs[AllCaseEqs()]) >>
  qpat_x_assum `inst_seq_ptr _ _ _ _ _ _ _ _ s2 _ _` mp_tac >>
  simp[inst_seq_ptr_def] >> strip_tac >> gen_tac >>
  `~is_terminator (mk_inst (id+2) ADD [Var dv;Var offv] [ep]).inst_opcode` by
    simp[mk_inst_def, is_terminator_def] >>
  simp[step_inst_inst_idx_indep, exec_result_map_def] >> gvs[exec_result_map_def]
QED

Resume append_memory_success_tail[element_store_uniform]:
  `!k. ptr_inst_ok D lo 0 ctx fn G3 tn3
    (mk_inst (id+3) MSTORE [Var ep;vop] []) (s3 with vs_inst_idx := k)` by
    (gen_tac >> irule ptr_inst_ok_mstore_tainted >>
     gvs[ptr_covers_def, lookup_var_def, allocas_from_def] >> metis_tac[]) >>
  `step_inst_base (mk_inst (id+3) MSTORE [Var ep;vop] []) s3 = OK s4` by
    (gvs[run_inst_seq_def] >> gvs[AllCaseEqs()]) >>
  qpat_x_assum `inst_seq_ptr _ _ _ _ _ _ _ _ s3 _ _` mp_tac >>
  simp[inst_seq_ptr_def] >> strip_tac >> gen_tac >>
  `~is_terminator (mk_inst (id+3) MSTORE [Var ep;vop] []).inst_opcode` by
    simp[mk_inst_def, is_terminator_def] >>
  simp[step_inst_inst_idx_indep, exec_result_map_def] >> gvs[exec_result_map_def]
QED

Resume append_memory_success_tail[header_store_uniform]:
  `!k. ptr_inst_ok D lo 0 ctx fn G5 tn5
    (mk_inst (id+5) MSTORE [Var p;Var nv] []) (s5 with vs_inst_idx := k)` by
    (gen_tac >> irule ptr_inst_ok_mstore_tainted >>
     gvs[ptr_covers_def, lookup_var_def, allocas_from_def] >> metis_tac[]) >>
  `step_inst_base (mk_inst (id+5) MSTORE [Var p;Var nv] []) s5 = OK s6` by
    (gvs[run_inst_seq_def] >> gvs[AllCaseEqs()]) >>
  qpat_x_assum `inst_seq_ptr _ _ _ _ _ _ _ _ s5 _ _` mp_tac >>
  simp[inst_seq_ptr_def] >> strip_tac >> gen_tac >>
  `~is_terminator (mk_inst (id+5) MSTORE [Var p;Var nv] []).inst_opcode` by
    simp[mk_inst_def, is_terminator_def] >>
  simp[step_inst_inst_idx_indep, exec_result_map_def] >> gvs[exec_result_map_def]
QED

Resume append_memory_success_tail[tail_run]:
  gvs[run_inst_seq_def] >> gvs[AllCaseEqs()]
QED

Resume append_memory_success_tail[tail_memory]:
  `w2n (bp+32w+n2w (32*L)) = w2n bp+32*(1+L)` by
    (simp[word_add_def, w2n_n2w, arithmeticTheory.LESS_MOD] >> decide_tac) >>
  simp[op_taint_def]
QED

Resume append_memory_success_tail[tail_frame]:
  simp[] >> rpt strip_tac >>
  gvs[FLOOKUP_DRESTRICT, op_taint_def, FLOOKUP_UPDATE] >> metis_tac[]
QED

Resume append_memory_success_tail[tail_uniform]:
  irule (inst_seq_ptr_uniform_append |> Q.INST
    [`xs` |-> `[mk_inst id ADD [Var p;Lit 32w] [dv]]`]
    |> SIMP_RULE (srw_ss()) []) >>
  conj_tac >- simp[is_terminator_def] >>
  qexistsl [`G1`,`s1`,`tn1`] >>
  conj_tac >- metis_tac[] >>
  reverse conj_tac >- metis_tac[] >>
  irule (inst_seq_ptr_uniform_append |> Q.INST [`xs` |-> `[mulinst]`]
    |> SIMP_RULE (srw_ss()) []) >>
  conj_tac >- simp[Abbr `mulinst`, mk_inst_def, is_terminator_def] >>
  qexistsl [`G2`,`s2`,`tn2`] >>
  conj_tac >- metis_tac[] >>
  reverse conj_tac >- simp[run_inst_seq_def] >>
  irule (inst_seq_ptr_uniform_append |> Q.INST
    [`xs` |-> `[mk_inst (id+2) ADD [Var dv;Var offv] [ep]]`]
    |> SIMP_RULE (srw_ss()) []) >>
  conj_tac >- simp[is_terminator_def] >>
  qexistsl [`G3`,`s3`,`tn3`] >>
  conj_tac >- metis_tac[] >>
  reverse conj_tac >- metis_tac[] >>
  irule (inst_seq_ptr_uniform_append |> Q.INST
    [`xs` |-> `[mk_inst (id+3) MSTORE [Var ep;vop] []]`]
    |> SIMP_RULE (srw_ss()) []) >>
  conj_tac >- simp[is_terminator_def] >>
  qexistsl [`G4`,`s4`,`tn4`] >>
  conj_tac >- metis_tac[] >>
  reverse conj_tac >- metis_tac[] >>
  irule (inst_seq_ptr_uniform_append |> Q.INST [`xs` |-> `[incinst]`]
    |> SIMP_RULE (srw_ss()) []) >>
  conj_tac >- simp[Abbr `incinst`, mk_inst_def, is_terminator_def] >>
  qexistsl [`G5`,`s5`,`tn5`] >>
  conj_tac >- metis_tac[] >>
  reverse conj_tac >- simp[run_inst_seq_def] >>
  metis_tac[]
QED

Finalise append_memory_success_tail[local]

Theorem append_memory_word_ptr:
  compile_dynarray_append ce (Var p) vop 32 32 dt vt cap T LocMemory sa = ((),sf) /\
  not_fresh_at sa p /\
  (!x. vop = Var x ==> not_fresh_at sa x) /\
  lookup_var p s = SOME bp /\ eval_operand vop s = SOME w /\
  ptr_covers G tn p s (32*(1+cap)) /\
  (!i. w2n bp <= i /\ i < w2n bp+32 ==> i NOTIN tn.t_mem) /\
  op_taint tn vop = {} /\ cap < dimword (:256) /\
  w2n bp+32*(1+cap) <= dimword (:256) /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  ?Gf tnf.
    (!k. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sf)
      (s with vs_inst_idx := k) Gf tnf) /\
    tnf.t_mem SUBSET tn.t_mem /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    tnf.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tnf (Var x) = op_taint tn (Var x)) /\
    tnf.t_mem =
      (if w2n (mload (w2n bp) s) < cap then
        (tn.t_mem DIFF
          {i | w2n bp+32*(1+w2n (mload (w2n bp) s)) <= i /\
               i < w2n bp+32*(1+w2n (mload (w2n bp) s))+32}) DIFF
          {i | w2n bp <= i /\ i < w2n bp+32}
       else tn.t_mem)
Proof
  strip_tac >>
  `!n. sa.cs_next_var <= n ==>
    p <> STRING #"%" (toString n) /\
    vop <> Var (STRING #"%" (toString n))` by
    metis_tac[not_fresh_at_def] >>
  qpat_x_assum `compile_dynarray_append _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_dynarray_append_def, contextTheory.compile_ptr_load_def,
       contextTheory.compile_ptr_store_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_id_def,
       fresh_var_def, emit_def] >> strip_tac >> gvs[] >>
  simp_tac (srw_ss()) [emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  Cases_on `w2n (mload (w2n bp) s) < cap`
  >- suspend "success" >> suspend "full"
QED

Resume append_memory_word_ptr[full]:
  qabbrev_tac `lenvar = STRING #"%" (toString sa.cs_next_var)` >>
  qabbrev_tac `okvar = STRING #"%" (toString (sa.cs_next_var+1))` >>
  qabbrev_tac `load = mk_inst sa.cs_next_id MLOAD [Var p] [lenvar]` >>
  qabbrev_tac `test = mk_inst (sa.cs_next_id+1) LT
    [Var lenvar; Lit (n2w cap)] [okvar]` >>
  qabbrev_tac `s1 = update_var lenvar (mload (w2n bp) s) s` >>
  qabbrev_tac `s2 = update_var okvar 0w s1` >>
  qabbrev_tac `G1 = step_prov PG G load s1` >>
  qabbrev_tac `tn1 = step_taint load s s1 tn` >>
  qabbrev_tac `G2 = step_prov PG G1 test s2` >>
  qabbrev_tac `tn2 = step_taint test s1 s2 tn1` >>
  qexistsl_tac [`G2`, `tn2`] >>
  conj_tac >- suspend "full_path" >> suspend "full_frame"
QED

Resume append_memory_word_ptr[full_path]:
  `p <> lenvar /\ p <> okvar /\ lenvar <> okvar` by
    (simp[Abbr `lenvar`, Abbr `okvar`] >>
     metis_tac[fresh_var_neq, DECIDE ``n <= n+1``]) >>
  `ptr_covers G tn p s 32` by
    (gvs[ptr_covers_def] >> goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
  `op_taint tn1 (Var lenvar) = {}` by
    (simp[Abbr `tn1`, Abbr `load`, Abbr `s1`] >>
     irule (cj 1 mload_ghost_clean) >> simp[eval_operand_def] >> metis_tac[]) >>
  `ptr_covers G1 tn1 p s1 32` by
    (simp[Abbr `G1`, Abbr `tn1`, Abbr `load`, Abbr `s1`] >>
     irule mload_preserves_ptr_covers >> simp[]) >>
  `op_taint tn2 (Var okvar) = {}` by
    (simp[Abbr `tn2`, Abbr `test`, Abbr `s2`,
          typed_copy_loop_arith_ghost_clean, update_var_def,
          op_taint_def, FLOOKUP_UPDATE]) >>
  `step_inst_base load s = OK s1 /\
   step_inst_base test s1 = OK s2` by
    simp[Abbr `load`, Abbr `test`, Abbr `s1`, Abbr `s2`,
         step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def,
         exec_pure2_def, eval_operand_def, lookup_var_def, update_var_def,
         FLOOKUP_UPDATE, bool_to_word_def, w2n_n2w, arithmeticTheory.LESS_MOD] >>
  `op_prov G1 (Var lenvar) = NONE` by
    (simp[Abbr `G1`, Abbr `load`, op_prov_def, scalar_load_output_prov]) >>
  `!k. ptr_inst_ok D lo 0 ctx fn G tn load (s with vs_inst_idx := k)` by
    (gen_tac >> simp[Abbr `load`] >> irule ptr_inst_ok_mload_lo >>
     simp[allocas_from_def]) >>
  `!k. ptr_inst_ok D lo 0 ctx fn G1 tn1 test (s1 with vs_inst_idx := k)` by
    (gen_tac >> irule ptr_inst_ok_lower_bound_transport >>
     conj_tac >- simp[allocas_from_def, Abbr `s1`, Abbr `s2`, update_var_def] >>
     qexists_tac `0` >>
     simp[] >>
     simp[Abbr `test`] >> irule bop_scalar_ptr_inst_ok >>
     simp[step_inst_inst_idx_indep, mk_inst_def, is_terminator_def,
          exec_result_map_def, GSYM mk_inst_def] >>
     gvs[op_taint_def, op_prov_def]) >>
  `!k. ptr_inst_ok D lo 0 ctx fn G2 tn2
    (mk_inst (sa.cs_next_id+2) ASSERT [Var okvar] [])
    (s2 with vs_inst_idx := k)` by
    (gen_tac >> irule ptr_inst_ok_lower_bound_transport >>
     conj_tac >- simp[allocas_from_def, Abbr `s1`, Abbr `s2`, update_var_def] >>
     qexists_tac `0` >>
     simp[Abbr `s2`, Abbr `s1`, allocas_from_def, update_var_def] >>
     irule bop_assert_ptr_inst_ok >> simp[]) >>
  `~is_terminator load.inst_opcode /\ ~is_terminator test.inst_opcode /\
   ~is_terminator (mk_inst (sa.cs_next_id+2) ASSERT [Var okvar] []).inst_opcode` by
    simp[Abbr `load`, Abbr `test`, mk_inst_def, is_terminator_def] >>
  `step_inst_base (mk_inst (sa.cs_next_id+2) ASSERT [Var okvar] []) s2 =
    Abort Revert_abort (revert_state (set_returndata [] s2))` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, Abbr `s2`,
         eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  gen_tac >>
  pure_rewrite_tac[APPEND, inst_seq_ptr_def] >>
  simp[step_inst_inst_idx_indep, exec_result_map_def,
       GSYM copy_update_inst_idx, Abbr `G1`, Abbr `tn1`,
       Abbr `G2`, Abbr `tn2`]
QED

Resume append_memory_word_ptr[full_frame]:
  `!x. not_fresh_at sa x ==> x <> lenvar /\ x <> okvar` by
    (gen_tac >> simp[not_fresh_at_def, Abbr `lenvar`, Abbr `okvar`] >>
     strip_tac >> conj_tac >> first_x_assum irule >> simp[]) >>

  `G2 = DRESTRICT G1 (COMPL {okvar}) /\
   tn2 = tn1 with t_var := tn1.t_var |+ (okvar,{})` by
    (simp[Abbr `G2`, Abbr `tn2`, Abbr `test`] >>
     conj_tac
     >- (irule (cj 1 typed_copy_loop_arith_ghost_clean) >>
         simp[] >> qexists_tac `s2` >> simp[]) >>
     irule (cj 2 typed_copy_loop_arith_ghost_clean) >>
     simp[Abbr `s2`, update_var_def]) >>
  simp[Abbr `G1`, Abbr `tn1`, Abbr `load`, Abbr `s1`,
       mload_ghost_frame] >>
  rpt strip_tac >>
  `x <> lenvar /\ x <> okvar` by metis_tac[] >>
  simp[op_taint_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  simp[SRULE[op_taint_def] mload_ghost_frame]
QED

Resume append_memory_word_ptr[success]:
  qabbrev_tac `lv = STRING #"%" (toString sa.cs_next_var)` >>
  qabbrev_tac `ov = STRING #"%" (toString (sa.cs_next_var+1))` >>
  qabbrev_tac `dv = STRING #"%" (toString (sa.cs_next_var+2))` >>
  qabbrev_tac `offv = STRING #"%" (toString (sa.cs_next_var+3))` >>
  qabbrev_tac `ep = STRING #"%" (toString (sa.cs_next_var+4))` >>
  qabbrev_tac `nv = STRING #"%" (toString (sa.cs_next_var+5))` >>
  `ALL_DISTINCT [p;lv;ov;dv;offv;ep;nv] /\
   vop <> Var lv /\ vop <> Var ov /\ vop <> Var dv /\
   vop <> Var offv /\ vop <> Var ep /\ vop <> Var nv` by
    (simp[ALL_DISTINCT, Abbr `lv`, Abbr `ov`, Abbr `dv`, Abbr `offv`,
          Abbr `ep`, Abbr `nv`] >> metis_tac[DECIDE ``!n:num. n <= n+1 /\ n <= n+2 /\ n <= n+3 /\ n <= n+4 /\ n <= n+5``]) >>
  `cap < dimword (:256)` by decide_tac >>
  mp_tac (append_memory_success_prefix |> SPEC_ALL |> Q.INST
    [`id` |-> `sa.cs_next_id`, `L` |-> `w2n (mload (w2n bp) s)`]) >>
  impl_tac >- gvs[ALL_DISTINCT] >>
  disch_then (qx_choosel_then [`H`,`tm`,`t`] strip_assume_tac) >>
  `lookup_var p t = SOME bp /\ eval_operand vop t = SOME w /\
   op_taint tm vop = {}` by
    (conj_tac >- gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE, ALL_DISTINCT] >>
     Cases_on `vop` >> gvs[eval_operand_def, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE, op_taint_def] >> metis_tac[op_taint_def]) >>
  mp_tac (append_memory_success_tail |> SPEC_ALL |> Q.INST
    [`G` |-> `H`, `tn` |-> `tm`, `s` |-> `t`, `id` |-> `sa.cs_next_id+3`,
     `L` |-> `w2n (mload (w2n bp) s)`]) >>
  impl_tac >- gvs[ALL_DISTINCT] >>
  disch_then (qx_choosel_then [`Hf`,`tmf`,`tf`] strip_assume_tac) >>
  qexistsl [`Hf`,`tmf`] >>
  conj_tac >- suspend "success_uniform" >>
  suspend "success_frame"
QED

Resume append_memory_word_ptr[success_uniform]:
  pure_rewrite_tac[APPEND] >>
  irule (inst_seq_ptr_uniform_append |> Q.INST
    [`xs` |-> `[mk_inst sa.cs_next_id MLOAD [Var p] [lv];
      mk_inst (sa.cs_next_id+1) LT [Var lv;Lit (n2w cap)] [ov];
      mk_inst (sa.cs_next_id+2) ASSERT [Var ov] []]`]
    |> SIMP_RULE (srw_ss()) []) >>
  simp_tac (srw_ss()) [is_terminator_def] >>
  qexistsl [`H`,`t`,`tm`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `!k. inst_seq_ptr _ _ _ _ _ H tm _ _ Hf tmf` mp_tac >>
  simp[NoAsms]
QED

Resume append_memory_word_ptr[success_frame]:
  `!x. not_fresh_at sa x ==>
    x <> lv /\ x <> ov /\ x <> dv /\ x <> offv /\ x <> ep /\ x <> nv` by
    (gen_tac >> simp[not_fresh_at_def, Abbr `lv`, Abbr `ov`, Abbr `dv`,
       Abbr `offv`, Abbr `ep`, Abbr `nv`] >> strip_tac >>
     rpt conj_tac >> first_x_assum irule >> simp[]) >>
  simp[] >> SET_TAC[]
QED

Finalise append_memory_word_ptr

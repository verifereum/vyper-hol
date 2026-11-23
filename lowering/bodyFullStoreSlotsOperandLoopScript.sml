Theory bodyFullStoreSlotsOperandLoop
Ancestors
  fragGasOriginPtrLoop fragGasCopyLoop fragGasOriginPtrDead placeStoreCopyPath stmtSimStoreCopy
  fragGasCopySeqLiftProps
  bodyMemAssignTopCopyPaths bodyMemAssignTopCopyLoop
  decoderGhostFramePtr bodyFullStoreSlotsRetired
  fragGasSeqPtr fragGasSeqPtrContext fragGasOriginPtr ptrSafeRun ptrDiscipline
  instMemFrontier fragExecMem memSafeRun fragExec
  venomInstProofs venomExecSemantics venomState venomInst
  finite_map pred_set list words arithmetic
  emitHelperProps fragGasSeq fragGasSeqAbort venomMemProps codegenRel contextCodegenRel exprLoweringProps
Libs
  stepInstBaseLib

val _ = hide "count";

Theorem copy_scalar_eq_origin_ptr[local]:
  isPREFIX [mk_inst id EQ [Var cv;count] [tv]]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  eval_operand (Var cv) s = SOME a /\ eval_operand count s = SOME b /\
  op_taint tn (Var cv) = {} /\ op_taint tn count = {} /\
  FLOOKUP G cv = NONE /\ op_prov G count = NONE /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\ ~s.vs_halted ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (update_var tv (bool_to_word (a = b)) s with
           vs_inst_idx := s.vs_inst_idx + 1),
     step_prov PG G (mk_inst id EQ [Var cv;count] [tv])
       (update_var tv (bool_to_word (a = b)) s),
     step_taint (mk_inst id EQ [Var cv;count] [tv]) s
       (update_var tv (bool_to_word (a = b)) s) tn)
Proof
  strip_tac >>
  `step_inst_base (mk_inst id EQ [Var cv;count] [tv]) s =
     OK (update_var tv (bool_to_word (a = b)) s)` by
    (irule step_EQ >> simp[]) >>
  `ptr_inst_ok D 0 0 ctx func G tn
     (mk_inst id EQ [Var cv;count] [tv]) s` by
    (simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
          mk_inst_def, source_memory_write_ranges_def,
          source_memory_read_ranges_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke, update_var_def] >>
     Cases_on `count` >> gvs[op_prov_def, FLOOKUP_DEF] >>
     rpt strip_tac >> Cases_on `op` >> gvs[op_taint_def] >> metis_tac[]) >>
  `run_inst_seq_mem_ok [mk_inst id EQ [Var cv;count] [tv]] s` by
    (simp[run_inst_seq_mem_ok_last, inst_dload_in_section_def, mk_inst_def] >>
     irule below_frontier_no_ranges >> simp[]) >>
  `inst_seq_ptr D 0 ctx func PG G tn
    [mk_inst id EQ [Var cv;count] [tv]] s
    (step_prov PG G (mk_inst id EQ [Var cv;count] [tv])
      (update_var tv (bool_to_word (a = b)) s))
    (step_taint (mk_inst id EQ [Var cv;count] [tv]) s
      (update_var tv (bool_to_word (a = b)) s) tn)` by
    simp[inst_seq_ptr_def] >>
  `run_inst_seq [mk_inst id EQ [Var cv;count] [tv]] s =
     OK (update_var tv (bool_to_word (a = b)) s)` by
    simp[run_inst_seq_def] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
              i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS)
     [mk_inst id EQ [Var cv;count] [tv]]` by
    simp[mk_inst_def, is_terminator_def] >>
  `(ctx_has_dalloca ctx ==>
    !pre i post u. [mk_inst id EQ [Var cv;count] [tv]] = pre ++ i::post /\
      run_inst_seq pre s = OK u ==> unitTransformDefs$dalloca_no_wrap i u)` by
    (rpt strip_tac >> irule memSafeRunTheory.dalloca_no_wrap_non_dalloca >>
     `MEM i [mk_inst id EQ [Var cv;count] [tv]]` by metis_tac[MEM_APPEND, MEM] >>
     gvs[mk_inst_def]) >>
  drule_all_then (qspec_then `explicit` mp_tac) run_inst_seq_origin_ptr_lift >>
  simp[run_inst_seq_def, mk_inst_def, is_terminator_def]
QED

Theorem copy_operand_header_origin_ptr[local]:
  isPREFIX [mk_inst id EQ [Var cv;count] [tv];
    mk_inst (id+1) JNZ [Var tv;Label exit;Label body_lbl] []]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  eval_operand (Var cv) s = SOME a /\ eval_operand count s = SOME b /\
  op_taint tn (Var cv) = {} /\ op_taint tn count = {} /\
  FLOOKUP G cv = NONE /\ op_prov G count = NONE /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\ ~s.vs_halted ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (jump_to (if a = b then exit else body_lbl)
          (update_var tv (bool_to_word (a = b)) s with
             vs_inst_idx := s.vs_inst_idx + 1)),
     step_prov PG G (mk_inst id EQ [Var cv;count] [tv])
       (update_var tv (bool_to_word (a = b)) s),
     step_taint (mk_inst id EQ [Var cv;count] [tv]) s
       (update_var tv (bool_to_word (a = b)) s) tn)
Proof
  strip_tac >>
  `isPREFIX [mk_inst id EQ [Var cv;count] [tv]]
    (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `isPREFIX (_::_::_) _` mp_tac >>
     Cases_on `DROP s.vs_inst_idx bb.bb_instructions` >> simp[]) >>
  drule_all copy_scalar_eq_origin_ptr >>
  disch_then (qspecl_then [`explicit`,`PG`,`D`] assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_origin_ptr_path _ _ [] (OK t,G1,tn1)` >>
  `~t.vs_halted /\ allocas_from lo t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    t.vs_current_bb = s.vs_current_bb /\
    t.vs_inst_idx = s.vs_inst_idx + 1 /\
    lookup_var tv t = SOME (bool_to_word (a = b))` by
    (simp[Abbr `t`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
     gvs[allocas_from_def, allocas_below_fmp_def, update_var_def] >> metis_tac[]) >>
  `op_taint tn1 (Var tv) = {}` by
    simp[Abbr `tn1`, step_taint_def, set_var_taint_def,
         out_taint_def, mk_inst_def, op_taint_def, FLOOKUP_UPDATE,
         eval_operand_def] >>
  `get_instruction bb t.vs_inst_idx =
     SOME (mk_inst (id+1) JNZ [Var tv;Label exit;Label body_lbl] [])` by
    (qpat_assum `isPREFIX (_::_::_) _` mp_tac >>
     disch_then (strip_assume_tac o MATCH_MP instruction_prefix_cursor) >>
     qpat_x_assum `isPREFIX [_] _` mp_tac >>
     disch_then (strip_assume_tac o MATCH_MP instruction_prefix_cursor) >>
     gvs[ADD1]) >>
  `step_inst_base (mk_inst (id+1) JNZ [Var tv;Label exit;Label body_lbl] []) t =
     OK (jump_to (if a = b then exit else body_lbl) t)` by
    (Cases_on `a = b` >>
     simp[step_inst_base_def, mk_inst_def, eval_operand_def, bool_to_word_def]) >>
  `ptr_inst_ok D 0 0 ctx func G1 tn1
    (mk_inst (id+1) JNZ [Var tv;Label exit;Label body_lbl] []) t` by
    (simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
          mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke, jump_to_def] >>
     rpt strip_tac >> Cases_on `op` >> gvs[op_taint_def]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G1,tn1) []
     (OK (jump_to (if a = b then exit else body_lbl) t),G1,tn1)` by
    (irule copy_jump_origin_ptr >> simp[] >>
     qexists_tac `mk_inst (id+1) JNZ [Var tv;Label exit;Label body_lbl] []` >>
     gvs[mk_inst_def]) >>
  metis_tac[gas_origin_ptr_path_trans]
QED

Theorem copy_body_scalar_counter[local]:
  ALL_DISTINCT [cv;mv;sv;vv;dv;nv] /\ FLOOKUP G cv = NONE /\
  inst_seq_ptr D lo ctx fn PG G tn
    [mk_inst id MUL [Var cv;Lit 32w] [mv];
     mk_inst (id+1) ADD [Var x;Var mv] [sv];
     mk_inst (id+2) MLOAD [Var sv] [vv];
     mk_inst (id+3) ADD [dst;Var cv] [dv];
     mk_inst (id+4) (if loc = LocStorage then SSTORE else TSTORE)
       [Var dv;Var vv] [];
     mk_inst (id+5) ADD [Var cv;Lit 1w] [nv];
     mk_inst (id+6) ASSIGN [Var nv] [cv]] s Gf tnf ==>
  FLOOKUP Gf cv = NONE
Proof
  strip_tac >>
  ntac 7
    (qpat_x_assum `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Once inst_seq_ptr_def] >>
     qmatch_goalsub_abbrev_tac `step_inst_base inst state` >>
     Cases_on `step_inst_base inst state` >> simp[] >> strip_tac >>
     gvs[Abbr `inst`, Abbr `state`,
         decoderGhostFramePtrTheory.step_prov_other_output, mk_inst_def]) >>
  rpt (qpat_x_assum `ptr_inst_ok _ _ _ _ _ _ _ _ _` kall_tac) >>
  rpt (qpat_x_assum `step_inst_base _ _ = _` kall_tac) >>
  gvs[inst_seq_ptr_def] >>
  irule scalar_forward_output_provenance_none >> simp[op_prov_def] >>
  irule scalar_forward_output_provenance_none >> simp[op_prov_def] >>
  rpt strip_tac >> gvs[op_prov_def,
    decoderGhostFramePtrTheory.step_prov_other_output]
QED

Theorem copy_two_instruction_prefix[local]:
  isPREFIX [a;b] (DROP n bb.bb_instructions) ==>
  isPREFIX [a] (DROP n bb.bb_instructions) /\
  get_instruction bb (n+1) = SOME b
Proof
  strip_tac >> conj_tac >-
    (qpat_x_assum `isPREFIX _ _` mp_tac >>
     Cases_on `DROP n bb.bb_instructions` >> simp[]) >>
  drule instruction_prefix_cursor >> strip_tac >>
  drule instruction_prefix_cursor >> simp[ADD1]
QED

Theorem memory_copy_loop_zero_origin_ptr_uniform:
 !src dst count F sa u sb func loc ctx lo s G tn explicit PG.
  compile_word_copy_loop_op src dst count LocMemory loc F sa = (u,sb) /\
  fn_has_code sa sb func /\ (loc = LocStorage \/ loc = LocTransient) /\
  eval_operand count s = SOME 0w /\ op_taint tn count = {} /\
  op_prov G count = NONE /\ (!y. count = Var y ==> not_fresh_at sa y) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tnf)) /\
    store_copy_normalize s t = s /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!y. not_fresh_at sa y ==> lookup_var y t = lookup_var y s /\
      FLOOKUP Gf y = FLOOKUP G y /\ op_taint tnf (Var y) = op_taint tn (Var y)) /\
    tnf.t_mem = tn.t_mem /\ tnf.t_imm = tn.t_imm /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all place_store_runtime_copy_code >> strip_tac >>
  `cv <> tv /\ (!y. not_fresh_at sa y ==> y <> cv /\ y <> tv)` by
    (gvs[] >> metis_tac[]) >>
  `isPREFIX [mk_inst id0 ASSIGN [Lit 0w] [cv]]
    (DROP s.vs_inst_idx bb0.bb_instructions) /\
   get_instruction bb0 (s.vs_inst_idx+1) =
     SOME (mk_inst (id0+1) JMP [Label hdr] [])` by
    (qpat_assum `isPREFIX [mk_inst _ ASSIGN _ _; _] _`
       (strip_assume_tac o MATCH_MP copy_two_instruction_prefix) >>
     gvs[Excl "isPREFIX"]) >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb0` by simp[] >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp s)` by simp[] >>
  drule_all copy_init_origin_ptr >>
  disch_then (qspecl_then [`<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |>`,`explicit`,`PG`,`G`,`tn`] assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_origin_ptr_path _ _ [] (OK q,Gq,tq)` >>
  `eval_operand (Var cv) q = SOME 0w /\ op_taint tq (Var cv) = {} /\
   FLOOKUP Gq cv = NONE /\ eval_operand count q = SOME 0w /\
   op_taint tq count = {} /\ op_prov Gq count = NONE /\
   allocas_from lo q /\ ~q.vs_halted /\ q.vs_current_bb = hdr /\ q.vs_inst_idx = 0` by
    (simp[Abbr `q`, Abbr `Gq`, Abbr `tq`, jump_to_def, update_var_def,
      eval_operand_def, lookup_var_def, step_prov_def, set_prov_def, out_prov_def,
      first_prov_def, FLOOKUP_DRESTRICT, step_taint_def, set_var_taint_def,
      out_taint_def, mk_inst_def, op_taint_def, FLOOKUP_UPDATE] >>
     Cases_on `count` >>
     gvs[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE, op_prov_def,
         op_taint_def, FLOOKUP_DRESTRICT, allocas_from_def] >> metis_tac[]) >>
  `isPREFIX [mk_inst idh EQ [Var cv;count] [tv];
      mk_inst (idh+1) JNZ [Var tv;Label exit;Label body_lbl] []]
     (DROP q.vs_inst_idx bbh.bb_instructions)` by simp[Excl "isPREFIX"] >>
  `lookup_block q.vs_current_bb func.fn_blocks = SOME bbh` by simp[] >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp q)` by
    (gvs[Abbr `q`, jump_to_def, update_var_def, allocas_below_fmp_def] >> metis_tac[]) >>
  drule_all copy_operand_header_origin_ptr >>
  disch_then (qspecl_then [`explicit`,`PG`,`<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |>`] assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_origin_ptr_path _ (q,Gq,tq) [] (OK t,Gf,tnf)` >>
  qexistsl_tac [`t`,`Gf`,`tnf`] >>
  conj_tac >- (gen_tac >> irule gas_origin_ptr_path_from_no_dead >>
    metis_tac[gas_origin_ptr_path_trans]) >>
  simp[Abbr `t`, Abbr `q`, store_copy_normalize_def, jump_to_def,
       update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  conj_tac >-
    (qpat_x_assum `s.vs_current_bb = sa.cs_current_bb` (fn th => rewrite_tac[GSYM th]) >> simp[]) >>
  conj_tac >-
    (rpt strip_tac >>
     simp[Abbr `Gf`, Abbr `Gq`, Abbr `tnf`, Abbr `tq`,
       decoderGhostFramePtrTheory.step_prov_other_output,
       decoderGhostFramePtrTheory.step_taint_other_output, mk_inst_def]) >>
  simp[Abbr `tnf`, Abbr `tq`,
    copy_register_taint_frame,
    exprSimPtrTopLevelStorageCopyTheory.toplevel_copy_register_taint_frame,
    mk_inst_def, jump_to_def, update_var_def]
QED

Theorem copy_operand_header_frame[local]:
  isPREFIX [mk_inst id EQ [Var cv;count] [tv];
    mk_inst (id+1) JNZ [Var tv;Label exit;Label body_lbl] []]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  eval_operand (Var cv) s = SOME a /\ eval_operand count s = SOME b /\
  op_taint tn (Var cv) = {} /\ op_taint tn count = {} /\
  FLOOKUP G cv = NONE /\ op_prov G count = NONE /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\ ~s.vs_halted ==>
  ?t Gf tnf.
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf) /\
    t = jump_to (if a = b then exit else body_lbl)
      (update_var tv (bool_to_word (a = b)) s with vs_inst_idx := s.vs_inst_idx + 1) /\
    (!y. y <> tv ==> FLOOKUP Gf y = FLOOKUP G y /\
      op_taint tnf (Var y) = op_taint tn (Var y)) /\
    tnf.t_mem = tn.t_mem /\ tnf.t_imm = tn.t_imm /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans
Proof
  strip_tac >> drule_all copy_operand_header_origin_ptr >>
  disch_then (qspecl_then [`explicit`,`PG`,`D`] assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_origin_ptr_path _ _ [] (OK t,Gf,tnf)` >>
  qexistsl_tac [`t`,`Gf`,`tnf`] >> simp[] >>
  conj_tac >- (rpt strip_tac >> simp[Abbr `Gf`, Abbr `tnf`,
    decoderGhostFramePtrTheory.step_prov_other_output,
    decoderGhostFramePtrTheory.step_taint_other_output, mk_inst_def]) >>
  simp[Abbr `tnf`, copy_register_taint_frame, mk_inst_def, update_var_def]
QED

Theorem copy_operand_body_runtime[local]:
  code = [mk_inst id MUL [Var cv;Lit 32w] [mv];
    mk_inst (id+1) ADD [src;Var mv] [sv];
    mk_inst (id+2) MLOAD [Var sv] [vv];
    mk_inst (id+3) ADD [dst;Var cv] [dv];
    mk_inst (id+4) (if loc = LocStorage then SSTORE else TSTORE) [Var dv;Var vv] [];
    mk_inst (id+5) ADD [Var cv;Lit 1w] [nv];
    mk_inst (id+6) ASSIGN [Var nv] [cv]] /\
  (loc = LocStorage \/ loc = LocTransient) /\
  store_copy_frame sa loc b k sbase i s /\
  eval_operand src sbase = SOME b /\ eval_operand dst sbase = SOME k /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME b /\ eval_operand (Var cv) s = SOME (n2w i) /\
  ALL_DISTINCT [cv;mv;sv;vv;dv;nv] /\
  (!x. not_fresh_at sa x ==> ~MEM x [cv;mv;sv;vv;dv;nv]) /\
  ~sbase.vs_call_ctx.cc_static /\ w2n b + 32*(i+1) <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (code ++ [mk_inst (id+7) JMP [Label hdr] []])
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  inst_seq_ptr D 0 ctx func PG G tn code s Gf tnf ==>
  ?t. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf) /\
    store_copy_frame sa loc b k sbase (i+1) t /\
    eval_operand (Var cv) t = SOME (n2w (i+1)) /\ allocas_from lo t /\
    ~t.vs_halted /\ t.vs_current_bb = hdr /\ t.vs_inst_idx = 0
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> drule_all topcopy_body_run >>
  disch_then (qspec_then `id` strip_assume_tac) >>
  `!x. src = Var x ==> ~MEM x [cv;mv;sv;vv;dv;nv]` by metis_tac[] >>
  `run_inst_seq_mem_ok code s` by
    (simp[] >> irule body_mem_storage_iteration_mem_ok_modular >> metis_tac[]) >>
  `isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by
    (irule isPREFIX_TRANS >> goal_assum (drule_at Any) >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
      i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) code` by
    (simp[] >> Cases_on `loc = LocStorage` >> simp[mk_inst_def, is_terminator_def]) >>
  `run_inst_seq code s = OK t` by simp[] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
      ~is_alloca_op i.inst_opcode /\ i.inst_opcode <> SETFMP /\
      i.inst_opcode <> DALLOCA) code` by
    (simp[] >> Cases_on `loc = LocStorage` >>
     simp[mk_inst_def, is_terminator_def, is_alloca_op_def]) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp t)` by
    metis_tac[run_inst_seq_allocas_below_fmp] >>
  `(ctx_has_dalloca ctx ==>
    !pre i post u. code = pre ++ i::post /\ run_inst_seq pre s = OK u ==>
      unitTransformDefs$dalloca_no_wrap i u)` by
    (rpt strip_tac >> irule memSafeRunTheory.dalloca_no_wrap_non_dalloca >>
     rename1 `ins.inst_opcode <> DALLOCA` >>
     `MEM ins code` by metis_tac[MEM_APPEND, MEM] >>
     qpat_x_assum `EVERY (\j. _ /\ _ /\ _ /\ _ /\ j.inst_opcode <> DALLOCA) code` mp_tac >>
     simp[EVERY_MEM] >> metis_tac[]) >>
  drule_all_then (qspec_then `explicit` strip_assume_tac) run_inst_seq_origin_ptr_lift >>
  qmatch_asmsub_abbrev_tac `gas_origin_ptr_path _ _ [] (OK t1,Gf,tnf)` >>
  `get_instruction bb t1.vs_inst_idx = SOME (mk_inst (id+7) JMP [Label hdr] [])` by
    (qpat_x_assum `isPREFIX (_ ++ [_]) _` mp_tac >> simp[Excl "isPREFIX"] >>
     strip_tac >> ntac 7 (dxrule instruction_prefix_cursor >> strip_tac) >>
     drule instruction_prefix_cursor >> simp[Abbr `t1`, ADD1]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t1,Gf,tnf) []
     (OK (jump_to hdr t1),Gf,tnf)` by
    (irule jmp_origin_ptr_path >>
     gvs[Abbr `t1`, allocas_from_def, allocas_below_fmp_def, Excl "isPREFIX"] >>
     metis_tac[]) >>
  qexists_tac `jump_to hdr t1` >>
  conj_tac >- metis_tac[gas_origin_ptr_path_trans] >>
  simp[Abbr `t1`, jump_to_def, eval_operand_def, lookup_var_def,
    allocas_from_def, GSYM ADD1] >>
  metis_tac[eval_operand_def, lookup_var_def, allocas_from_def]
QED

Theorem copy_operand_body_step[local]:
  code = [mk_inst id MUL [Var cv;Lit 32w] [mv];
    mk_inst (id+1) ADD [Var x;Var mv] [sv]; mk_inst (id+2) MLOAD [Var sv] [vv];
    mk_inst (id+3) ADD [dst;Var cv] [dv];
    mk_inst (id+4) (if loc = LocStorage then SSTORE else TSTORE) [Var dv;Var vv] [];
    mk_inst (id+5) ADD [Var cv;Lit 1w] [nv]; mk_inst (id+6) ASSIGN [Var nv] [cv]] /\
  (loc = LocStorage \/ loc = LocTransient) /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ALL_DISTINCT [cv;mv;sv;vv;dv;nv] /\ ~MEM x [cv;mv;sv;vv;dv;nv] /\
  (!y. dst = Var y ==> ~MEM y [cv;mv;sv;vv;dv;nv]) /\
  store_copy_frame sa loc b k sbase i s /\
  eval_operand (Var x) sbase = SOME b /\ eval_operand dst sbase = SOME k /\
  (!y. Var x = Var y \/ dst = Var y ==> not_fresh_at sa y) /\
  (!y. not_fresh_at sa y ==> ~MEM y [cv;mv;sv;vv;dv;nv]) /\
  ~sbase.vs_call_ctx.cc_static /\
  ptr_covers G tn x s (32*n) /\ lookup_var x s = SOME b /\
  eval_operand dst s = SOME k /\ op_taint tn dst = {} /\
  eval_operand (Var cv) s = SOME (n2w i) /\ op_taint tn (Var cv) = {} /\
  FLOOKUP G cv = NONE /\ i < n /\ w2n b + 32*n < dimword(:256) /\
  ~s.vs_call_ctx.cc_static /\ w2n b + 32*(i+1) <= s.vs_alloca_next /\
  allocas_from lo s /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (code ++ [mk_inst (id+7) JMP [Label hdr] []])
    (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t Gf tnf.
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf) /\
    store_copy_frame sa loc b k sbase (i+1) t /\
    eval_operand (Var cv) t = SOME (n2w (i+1)) /\ allocas_from lo t /\
    ~t.vs_halted /\ t.vs_current_bb = hdr /\ t.vs_inst_idx = 0 /\
    FLOOKUP Gf cv = NONE /\ op_taint tnf (Var cv) = {} /\
    (!y. ~MEM y [cv;mv;sv;vv;dv;nv] ==> FLOOKUP Gf y = FLOOKUP G y /\
      op_taint tnf (Var y) = op_taint tn (Var y)) /\
    tnf.t_mem = tn.t_mem /\ tnf.t_imm = tn.t_imm /\
    (if loc = LocStorage then tnf.t_trans = tn.t_trans else tnf.t_stor = tn.t_stor) /\
    toplevel_copy_source_taint loc tnf = key_update (toplevel_copy_source_taint loc tn)
      (k + n2w i) (mem_word_taint tn.t_mem (w2n b + 32*i))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp s)` by simp[] >>
  drule_all memory_copy_body_ptr >>
  disch_then (qspecl_then [`id`,`D`,`func`,`PG`] strip_assume_tac) >>
  `FLOOKUP Gf cv = NONE` by (drule_all copy_body_scalar_counter >> simp[]) >>
  `inst_seq_ptr D 0 ctx func PG G tn code s Gf tnf` by simp[] >>
  `eval_operand (Var x) s = SOME b` by simp[eval_operand_def] >>
  drule_all copy_operand_body_runtime >>
  disch_then (qspec_then `explicit` strip_assume_tac) >>
  qexistsl_tac [`t`,`Gf`,`tnf`] >> simp[]
QED

Theorem store_copy_frame_allocas_below_fmp:
  store_copy_frame sa loc b k sbase i q ==>
  (allocas_below_fmp q <=> allocas_below_fmp sbase)
Proof
  `!js a. allocas_below_fmp
      (FOLDL (\t j. (if loc = LocStorage then sstore else tstore)
        (k + n2w j) (mload (w2n (b + n2w j * 32w)) sbase) t) a js) =
      allocas_below_fmp a` by
    (Induct >> simp[] >> rpt gen_tac >>
     Cases_on `loc = LocStorage` >>
     simp[sstore_def, tstore_def, allocas_below_fmp_def]) >>
  strip_tac >> fs[store_copy_frame_def] >>
  qpat_x_assum `store_copy_normalize _ _ = _`
    (mp_tac o Q.AP_TERM `\q. allocas_below_fmp q`) >>
  simp[store_copy_prefix_def] >>
  simp[store_copy_normalize_def, allocas_below_fmp_def]
QED

Theorem memory_copy_loop_operand_origin_ptr_uniform:
 !x dst n count F sa u sb func loc ctx lo s G tn b k explicit PG.
  compile_word_copy_loop_op (Var x) dst count LocMemory loc F sa = (u,sb) /\
  fn_has_code sa sb func /\ (loc = LocStorage \/ loc = LocTransient) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\ ~s.vs_call_ctx.cc_static /\
  not_fresh_at sa x /\ (!y. dst = Var y ==> not_fresh_at sa y) /\
  lookup_var x s = SOME b /\ ptr_covers G tn x s (32*n) /\
  eval_operand dst s = SOME k /\ op_taint tn dst = {} /\
  eval_operand count s = SOME (n2w n) /\ op_taint tn count = {} /\
  op_prov G count = NONE /\ (!y. count = Var y ==> not_fresh_at sa y) /\
  n < dimword(:256) /\ w2n b + 32*n < dimword(:256) /\
  w2n b + 32*n <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf)) /\
    store_copy_frame sa loc b k s n t /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!y. not_fresh_at sa y ==> FLOOKUP Gf y = FLOOKUP G y /\
      op_taint tnf (Var y) = op_taint tn (Var y)) /\
    tnf.t_mem = tn.t_mem /\ tnf.t_imm = tn.t_imm /\
    (if loc = LocStorage then tnf.t_trans = tn.t_trans else tnf.t_stor = tn.t_stor) /\
    toplevel_copy_source_taint loc tnf SUBSET
      (toplevel_copy_source_taint loc tn DIFF {(k + n2w i, j) | (i,j) | i < n}) UNION
      {(k + n2w i, j) | (i,j) | i < n /\ j < 32 /\ w2n b + 32*i + j IN tn.t_mem}
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all place_store_runtime_copy_code >> strip_tac >>
  `!y. not_fresh_at sa y ==> ~MEM y [cv;mv;sv;vv;dv;nv] /\ y <> tv` by
    (gvs[] >> metis_tac[]) >>
  `cv <> tv /\ ALL_DISTINCT [cv;mv;sv;vv;dv;nv]` by gvs[] >>
  qabbrev_tac `D0 = <|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>` >>
  qabbrev_tac `Inv = \j Gj tj q.
    store_copy_frame sa loc b k s j q /\ allocas_from lo q /\
    eval_operand (Var cv) q = SOME (n2w j) /\ op_taint tj (Var cv) = {} /\
    FLOOKUP Gj cv = NONE /\ eval_operand count q = SOME (n2w n) /\
    op_taint tj count = {} /\ op_prov Gj count = NONE /\
    (!y. not_fresh_at sa y ==> FLOOKUP Gj y = FLOOKUP G y /\
      op_taint tj (Var y) = op_taint tn (Var y)) /\
    tj.t_mem = tn.t_mem /\ tj.t_imm = tn.t_imm /\
    (if loc = LocStorage then tj.t_trans = tn.t_trans else tj.t_stor = tn.t_stor) /\
    toplevel_copy_source_taint loc tj SUBSET
      (toplevel_copy_source_taint loc tn DIFF {(k + n2w i,jj) | (i,jj) | i < j}) UNION
      {(k + n2w i,jj) | (i,jj) | i < j /\ jj < 32 /\ w2n b + 32*i + jj IN tn.t_mem}` >>
  `!j Gj tj q. j <= n /\ Inv j Gj tj q /\ ~q.vs_halted /\
      q.vs_current_bb = hdr /\ q.vs_inst_idx = 0 ==>
    ?r Gr tr. gas_origin_ptr_path (D0,lo,explicit,ctx,func,PG) (q,Gj,tj) [] (OK r,Gr,tr) /\
      Inv j Gr tr r /\ ~r.vs_halted /\ r.vs_inst_idx = 0 /\
      r.vs_current_bb = (if j = n then exit else body_lbl)` by suspend "header" >>
  `!j Gj tj q. j < n /\ Inv j Gj tj q /\ ~q.vs_halted /\
      q.vs_current_bb = body_lbl /\ q.vs_inst_idx = 0 ==>
    ?r Gr tr. gas_origin_ptr_path (D0,lo,explicit,ctx,func,PG) (q,Gj,tj) [] (OK r,Gr,tr) /\
      Inv (j+1) Gr tr r /\ ~r.vs_halted /\ r.vs_current_bb = hdr /\ r.vs_inst_idx = 0`
    by suspend "body" >>
  `?q Gq tq. gas_origin_ptr_path (D0,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK q,Gq,tq) /\
     Inv 0 Gq tq q /\ ~q.vs_halted /\ q.vs_current_bb = hdr /\ q.vs_inst_idx = 0`
    by suspend "init" >>
  suspend "finish"
QED

Resume memory_copy_loop_operand_origin_ptr_uniform[header]:
  qunabbrev_tac `Inv` >> BETA_TAC >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `isPREFIX [mk_inst idh EQ [Var cv;count] [tv];
     mk_inst (idh+1) JNZ [Var tv;Label exit;Label body_lbl] []]
     (DROP q.vs_inst_idx bbh.bb_instructions)` by simp[Excl "isPREFIX"] >>
  `lookup_block q.vs_current_bb func.fn_blocks = SOME bbh` by simp[] >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp q)` by
    metis_tac[store_copy_frame_allocas_below_fmp] >>
  drule_all copy_operand_header_frame >>
  disch_then (qspecl_then [`explicit`,`PG`,`D0`] strip_assume_tac) >>
  `j < dimword(:256)` by decide_tac >>
  `(n2w j : bytes32) = n2w n <=> j = n` by simp[n2w_11] >>
  `store_copy_frame sa loc b k s j t` by
    (simp[] >> irule topcopy_frame_update >> metis_tac[]) >>
  `eval_operand (Var cv) t = SOME (n2w j) /\
   eval_operand count t = SOME (n2w n)` by
    (simp[jump_to_def, update_var_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
     Cases_on `count` >> gvs[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  `op_taint tnf count = {} /\ op_prov Gf count = NONE` by
    (Cases_on `count` >> gvs[op_taint_def, op_prov_def] >> metis_tac[]) >>
  qexistsl_tac [`t`,`Gf`,`tnf`] >>
  simp[exprSimPtrTopLevelStorageCopyTheory.toplevel_copy_source_taint_def, jump_to_def, update_var_def] >>
  conj_tac >- (gvs[allocas_from_def] >> metis_tac[]) >>
  qpat_x_assum `toplevel_copy_source_taint loc tj SUBSET _` mp_tac >>
  simp[exprSimPtrTopLevelStorageCopyTheory.toplevel_copy_source_taint_def]
QED

Resume memory_copy_loop_operand_origin_ptr_uniform[body]:
  qpat_x_assum `!j Gj tj q. j <= n /\ _ ==> _` kall_tac >>
  qunabbrev_tac `Inv` >> BETA_TAC >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `eval_operand (Var x) s = SOME b` by simp[eval_operand_def] >>
  `!y. Var x = Var y \/ dst = Var y ==> not_fresh_at sa y` by
    (rpt strip_tac >> gvs[]) >>
  `!y. not_fresh_at sa y ==> ~MEM y [cv;mv;sv;vv;dv;nv]` by metis_tac[] >>
  `~MEM x [cv;mv;sv;vv;dv;nv] /\
   (!y. dst = Var y ==> ~MEM y [cv;mv;sv;vv;dv;nv])` by metis_tac[] >>
  `lookup_var x q = SOME b` by
    (gvs[store_copy_frame_def] >> metis_tac[]) >>
  `eval_operand dst q = SOME k` by (irule topcopy_frame_operand >> metis_tac[]) >>
  `~q.vs_call_ctx.cc_static` by metis_tac[topcopy_frame_call_ctx] >>
  `w2n b + 32*(j+1) <= q.vs_alloca_next` by
    (irule topcopy_frame_index_bound >> metis_tac[]) >>
  `ptr_covers Gj tj x q (32*n)` by metis_tac[ptr_covers_frame] >>
  `op_taint tj dst = {}` by (Cases_on `dst` >> gvs[op_taint_def] >> metis_tac[]) >>
  `lookup_block q.vs_current_bb func.fn_blocks = SOME bbb` by simp[] >>
  qabbrev_tac `code = [mk_inst idb MUL [Var cv;Lit 32w] [mv];
    mk_inst (idb+1) ADD [Var x;Var mv] [sv]; mk_inst (idb+2) MLOAD [Var sv] [vv];
    mk_inst (idb+3) ADD [dst;Var cv] [dv];
    mk_inst (idb+4) (if loc = LocStorage then SSTORE else TSTORE) [Var dv;Var vv] [];
    mk_inst (idb+5) ADD [Var cv;Lit 1w] [nv]; mk_inst (idb+6) ASSIGN [Var nv] [cv]]` >>
  `isPREFIX (code ++ [mk_inst (idb+7) JMP [Label hdr] []])
    (DROP q.vs_inst_idx bbb.bb_instructions)` by simp[Abbr `code`, Excl "isPREFIX"] >>
  `code = [mk_inst idb MUL [Var cv;Lit 32w] [mv];
    mk_inst (idb+1) ADD [Var x;Var mv] [sv]; mk_inst (idb+2) MLOAD [Var sv] [vv];
    mk_inst (idb+3) ADD [dst;Var cv] [dv];
    mk_inst (idb+4) (if loc = LocStorage then SSTORE else TSTORE) [Var dv;Var vv] [];
    mk_inst (idb+5) ADD [Var cv;Lit 1w] [nv]; mk_inst (idb+6) ASSIGN [Var nv] [cv]]` by simp[Abbr `code`] >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp q)` by
    metis_tac[store_copy_frame_allocas_below_fmp] >>
  drule_all copy_operand_body_step >>
  disch_then (qspecl_then [`explicit`,`PG`,`D0`] strip_assume_tac) >>
  `eval_operand count t = SOME (n2w n)` by
    (irule topcopy_frame_operand >> metis_tac[]) >>
  `op_taint tnf count = {} /\ op_prov Gf count = NONE` by
    (Cases_on `count` >> simp[op_taint_def, op_prov_def] >>
     fs[op_taint_def, op_prov_def, Excl "isPREFIX"] >> metis_tac[]) >>
  qexistsl_tac [`t`,`Gf`,`tnf`] >> simp[] >>
  reverse conj_tac
  >- (drule copy_store_taint_bound_step >> simp[]) >>
  qpat_x_assum `if loc = LocStorage then tj.t_trans = _ else _` mp_tac >>
  qpat_x_assum `if loc = LocStorage then tnf.t_trans = _ else _` mp_tac >>
  Cases_on `loc = LocStorage` >> simp[]
QED

Resume memory_copy_loop_operand_origin_ptr_uniform[init]:
  qpat_x_assum `!j Gj tj q. j <= n /\ _ ==> _` kall_tac >>
  qpat_x_assum `!j Gj tj q. j < n /\ _ ==> _` kall_tac >>
  `isPREFIX [mk_inst id0 ASSIGN [Lit 0w] [cv]]
    (DROP s.vs_inst_idx bb0.bb_instructions) /\
   get_instruction bb0 (s.vs_inst_idx+1) =
     SOME (mk_inst (id0+1) JMP [Label hdr] [])` by
    (qpat_assum `isPREFIX [mk_inst _ ASSIGN _ _; _] _`
       (strip_assume_tac o MATCH_MP copy_two_instruction_prefix) >>
     gvs[Excl "isPREFIX"]) >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb0` by simp[] >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp s)` by simp[] >>
  drule_all copy_init_origin_ptr >>
  disch_then (qspecl_then [`D0`,`explicit`,`PG`,`G`,`tn`] assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_origin_ptr_path _ _ [] (OK q,Gq,tq)` >>
  `eval_operand (Var cv) q = SOME 0w /\ op_taint tq (Var cv) = {} /\
   FLOOKUP Gq cv = NONE /\ eval_operand count q = SOME (n2w n) /\
   op_taint tq count = {} /\ op_prov Gq count = NONE /\
   allocas_from lo q /\ ~q.vs_halted /\ q.vs_current_bb = hdr /\ q.vs_inst_idx = 0` by
    (simp[Abbr `q`, Abbr `Gq`, Abbr `tq`, jump_to_def, update_var_def,
      eval_operand_def, lookup_var_def, step_prov_def, set_prov_def, out_prov_def,
      first_prov_def, FLOOKUP_DRESTRICT, step_taint_def, set_var_taint_def,
      out_taint_def, mk_inst_def, op_taint_def, FLOOKUP_UPDATE] >>
     Cases_on `count` >>
     gvs[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE, op_prov_def,
         op_taint_def, FLOOKUP_DRESTRICT, allocas_from_def] >> metis_tac[]) >>
  qexistsl_tac [`q`,`Gq`,`tq`] >> simp[Abbr `Inv`] >>
  conj_tac >-
    (simp[Abbr `q`] >> irule topcopy_frame_update >> simp[] >>
     qpat_x_assum `!x. not_fresh_at sa x ==> ~MEM x _` (qspec_then `cv` mp_tac) >> simp[]) >>
  conj_tac >-
    (rpt strip_tac >>
     `y <> cv` by
       (qpat_x_assum `!x. not_fresh_at sa x ==> ~MEM x _` (qspec_then `y` mp_tac) >> simp[]) >>
     simp[Abbr `Gq`, Abbr `tq`,
      decoderGhostFramePtrTheory.step_prov_other_output,
      decoderGhostFramePtrTheory.step_taint_other_output, mk_inst_def]) >>
  simp[Abbr `tq`, copy_register_taint_frame,
    exprSimPtrTopLevelStorageCopyTheory.toplevel_copy_register_taint_frame,
    exprSimPtrTopLevelStorageCopyTheory.toplevel_copy_source_taint_def,
    mk_inst_def, update_var_def]
QED

Resume memory_copy_loop_operand_origin_ptr_uniform[finish]:
  `?t Gf tnf.
    gas_origin_ptr_path (D0,lo,explicit,ctx,func,PG) (q,Gq,tq) [] (OK t,Gf,tnf) /\
    Inv n Gf tnf t /\ ~t.vs_halted /\ t.vs_current_bb = exit /\ t.vs_inst_idx = 0` by
    (irule copy_loop_iterate_origin_ptr >>
     simp[] >> conj_tac >-
       (qexists_tac `body_lbl` >> simp[]) >>
     qexistsl_tac [`0`,`n`] >> simp[]) >>
  qexistsl_tac [`t`,`Gf`,`tnf`] >>
  conj_tac >- (gen_tac >> irule gas_origin_ptr_path_from_no_dead >>
    fs[Abbr `D0`] >>
    metis_tac[gas_origin_ptr_path_trans]) >>
  qpat_x_assum `Inv n Gf tnf t` mp_tac >> simp[Abbr `Inv`]
QED

Finalise memory_copy_loop_operand_origin_ptr_uniform

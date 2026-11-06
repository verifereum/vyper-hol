(* Runtime immutable-copy layout and counted pointer boundaries. *)
Theory exprSimPtrTopLevelImmutableCopy
Ancestors
  exprSimPtrTopLevelCopy immutableCopyExecution compileEnv emitHelper
  fragGasSeqPtr context exprLoweringProps emitHelperProps venomInst list
  bodyPtrDefs typedCopyPtr ptrDiscipline ptrSafeRun venomState words
  venomExecSemantics exprSimCopy finite_map pred_set memLocDefs codegenRel
  fragExec exprSimStorageCopy ghostPcTransportPtr instSeqComposePtr instIdxIndep

Theorem toplevel_immutable_copy_one_layout:
  compile_imm_copy_to_memory F imm src dst (SUC 0) 0 sa = ((),sb) ==>
  emitted_insts sa sb =
    [mk_inst sa.cs_next_id DLOAD [src]
       [STRING #"%" (toString sa.cs_next_var)];
     mk_inst (sa.cs_next_id+1) MSTORE
       [dst; Var (STRING #"%" (toString sa.cs_next_var))] []]
Proof
  simp[compile_imm_copy_to_memory_def, compile_lit_byte_offset_def,
       compile_imm_load_word_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def] >> rpt strip_tac >> gvs[] >>
  simp[emitted_insts_def, DROP_APPEND]
QED

Theorem toplevel_immutable_copy_one_counted:
  compile_imm_copy_to_memory F imm src dst (SUC 0) 0 sa = ((),sb) /\
  inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gf tnf /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  run_inst_seq (emitted_insts sa sb) s = OK r ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf
    (OK (r with vs_inst_idx := s.vs_inst_idx + 2))
Proof
  strip_tac >> drule toplevel_immutable_copy_one_layout >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb) /\
   LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb)) = 0 /\
   LENGTH (emitted_insts sa sb) = 2` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_path_ptr >> simp[]
QED

Theorem toplevel_immutable_offset_coverage:
  ptr_covers G tn root s capacity /\ lookup_var root s = SOME a /\
  off+len <= capacity /\ w2n a+capacity < dimword (:256) ==>
  ptr_covers
    (step_prov PG G (mk_inst id ADD [Var root; Lit (n2w off)] [out])
      (update_var out (a+n2w off) s))
    (step_taint (mk_inst id ADD [Var root; Lit (n2w off)] [out]) s
      (update_var out (a+n2w off) s) tn)
    out (update_var out (a+n2w off) s) len
Proof
  strip_tac >> gvs[ptr_covers_def] >>
  simp[step_prov_def, set_prov_def, out_prov_def, first_prov_def,
       op_prov_def, mk_inst_def, finite_mapTheory.FLOOKUP_UPDATE,
       lookup_var_def, update_var_def] >>
  conj_tac
  >- (simp[step_taint_def, set_var_taint_def, out_taint_def, op_taint_def,
           mk_inst_def, finite_mapTheory.FLOOKUP_UPDATE] >>
      Cases_on `eval_operand (Var root) s` >> simp[]) >>
  `w2n (a+n2w off) = w2n a+off` by
    (Cases_on `a` >> gvs[wordsTheory.word_add_n2w] >> decide_tac) >>
  simp[] >> decide_tac
QED

Theorem toplevel_immutable_byte_offset_ptr:
  compile_lit_byte_offset (Var root) off sa = (Var dst,sb) /\
  ptr_covers G tn root s capacity /\ lookup_var root s = SOME a /\
  off+len <= capacity /\ w2n a+capacity < dimword (:256) /\
  ~ctx_has_dalloca ctx ==>
  ?t Gf tnf.
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gf tnf /\
    ptr_covers Gf tnf dst t len
Proof
  Cases_on `off = 0`
  >- (simp[compile_lit_byte_offset_def, comp_return_def] >>
      rpt strip_tac >> gvs[] >> qexistsl_tac [`s`,`G`,`tn`] >>
      simp[emitted_insts_def, run_inst_seq_def, inst_seq_ptr_def] >>
      gvs[ptr_covers_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS,
                                    arithmeticTheory.LESS_EQ_MONO_ADD_EQ]) >>
  simp[compile_lit_byte_offset_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def,
       emit_def] >> rpt strip_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac `mk_inst id ADD _ [out]` >>
  simp[emitted_insts_def, DROP_APPEND] >>
  qexists_tac `update_var out (a+n2w off) s` >>
  qexists_tac `step_prov PG G (mk_inst id ADD [Var root; Lit (n2w off)] [out])
    (update_var out (a+n2w off) s)` >>
  qexists_tac `step_taint (mk_inst id ADD [Var root; Lit (n2w off)] [out]) s
    (update_var out (a+n2w off) s) tn` >>
  `step_inst_base (mk_inst id ADD [Var root; Lit (n2w off)] [out]) s =
     OK (update_var out (a+n2w off) s)` by
    simp[mk_inst_def, step_inst_base_opcode_eqs, exec_pure2_def,
         eval_operand_def] >>
  conj_tac >- simp[run_inst_seq_def] >>
  conj_tac
  >- (simp[inst_seq_ptr_def] >> irule ptr_inst_ok_copy_len_binop >>
      gvs[ptr_covers_def, op_taint_def]) >>
  irule toplevel_immutable_offset_coverage >> simp[] >>
  qexists_tac `capacity` >> simp[]
QED

(* Proof-only joint frame for a suffix of the immutable copy. *)
Definition immutable_copy_ghost_frame_def:
  immutable_copy_ghost_frame sa s G tn sb t H tm off nb b <=>
    copy_runtime_frame sa s sb t /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP H x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x)) /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\
    tm.t_imm = tn.t_imm /\
    tm.t_mem = tn.t_mem DIFF
      {q | w2n b+off <= q /\ q < w2n b+off+nb}
End

Theorem immutable_copy_ghost_frame_refl:
  immutable_copy_ghost_frame sa s G tn sa s G tn off 0 b
Proof
  simp[immutable_copy_ghost_frame_def, copy_runtime_frame_refl,
       pred_setTheory.EXTENSION]
QED

Theorem immutable_copy_ghost_frame_trans:
  immutable_copy_ghost_frame sa s G tn sb t H tm off m b /\
  immutable_copy_ghost_frame sb t H tm sc u J tu (off+m) n b ==>
  immutable_copy_ghost_frame sa s G tn sc u J tu off (m+n) b
Proof
  simp[immutable_copy_ghost_frame_def] >> rpt strip_tac
  >- metis_tac[copy_runtime_frame_trans]
  >- (gvs[copy_runtime_frame_def] >>
      `not_fresh_at sb x` by
        (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
      metis_tac[])
  >- (gvs[copy_runtime_frame_def] >>
      `not_fresh_at sb x` by
        (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
      metis_tac[]) >>
  simp[pred_setTheory.EXTENSION] >> gen_tac >> eq_tac >>
  simp[] >> decide_tac
QED

Theorem toplevel_immutable_covers_pc:
  ptr_covers G tn root (s with vs_inst_idx := pc) nb <=>
  ptr_covers G tn root s nb
Proof
  simp[ptr_covers_def, lookup_var_def]
QED

Theorem toplevel_immutable_dload_ghost_frame:
  !PG G tn s id src tmp w.
    op_taint (step_taint (mk_inst id DLOAD [src] [tmp]) s
      (update_var tmp w s) tn) (Var tmp) = {} /\
    (step_taint (mk_inst id DLOAD [src] [tmp]) s
      (update_var tmp w s) tn).t_mem = tn.t_mem /\
    (step_taint (mk_inst id DLOAD [src] [tmp]) s
      (update_var tmp w s) tn).t_stor = tn.t_stor /\
    (step_taint (mk_inst id DLOAD [src] [tmp]) s
      (update_var tmp w s) tn).t_trans = tn.t_trans /\
    (step_taint (mk_inst id DLOAD [src] [tmp]) s
      (update_var tmp w s) tn).t_imm = tn.t_imm /\
    (!p. p <> tmp ==>
      FLOOKUP (step_prov PG G (mk_inst id DLOAD [src] [tmp])
        (update_var tmp w s)) p = FLOOKUP G p /\
      op_taint (step_taint (mk_inst id DLOAD [src] [tmp]) s
        (update_var tmp w s) tn) (Var p) = op_taint tn (Var p))
Proof
  rpt gen_tac >>
  `new_site_bytes s (update_var tmp w s) = {}` by
    simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF,
         pred_setTheory.EXTENSION, SF CONJ_ss] >>
  Cases_on `eval_operand src s` >>
  simp[step_prov_def, set_prov_def, out_prov_def, step_taint_def,
       mk_inst_def, set_var_taint_def, out_taint_def, op_taint_def,
       store_taint_def, adopt_reset_def, imm_taint_def, mem_taint_def,
       step_writes_def, source_memory_write_ranges_def, written_taint_def,
       range_bytes_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]
QED

Theorem toplevel_immutable_mstore_ghost_frame:
  lookup_var dst s = SOME a /\ eval_operand value s = SOME w /\
  op_taint tn value = {} ==>
  step_prov PG G (mk_inst id MSTORE [Var dst; value] [])
    (mstore (w2n a) w s) = G /\
  (step_taint (mk_inst id MSTORE [Var dst; value] []) s
    (mstore (w2n a) w s) tn) =
    (tn with t_mem := tn.t_mem DIFF {q | w2n a <= q /\ q < w2n a+32})
Proof
  strip_tac >> drule_all mstore_ghost_frame >> strip_tac >>
  simp[] >>
  simp[ptrDisciplineTheory.taint_component_equality] >>
  simp[step_taint_def, mk_inst_def, set_var_taint_def, imm_taint_def,
       mem_taint_def, step_writes_def, source_memory_write_ranges_def,
       fixed_source_write_range_def, eval_operand_def, written_taint_def,
       range_bytes_def, new_site_bytes_def, mstore_def, FLOOKUP_DEF,
       pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem toplevel_immutable_add_ghost_frame:
  (step_taint (mk_inst id ADD [left;right] [tmp]) s
    (update_var tmp w s) tn).t_imm = tn.t_imm
Proof
  simp[step_taint_def, mk_inst_def, imm_taint_def]
QED

Theorem toplevel_immutable_offset_frame:
  compile_lit_byte_offset op off sa = (r,sb) /\
  copy_old_operand sa op /\ eval_operand op s = SOME a /\
  op_taint tn op = {} /\ ~ctx_has_dalloca ctx ==>
  ?t H tm.
    (!pc. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
       (s with vs_inst_idx := pc) H tm) /\
    immutable_copy_ghost_frame sa s G tn sb t H tm 0 0 0w /\
    eval_operand r t = SOME (a+n2w off) /\ op_taint tm r = {} /\
    copy_old_operand sb r
Proof
  strip_tac >> drule_all copy_runtime_offset >> strip_tac >>
  Cases_on `off = 0`
  >- (gvs[compile_lit_byte_offset_def, comp_return_def] >>
      qexistsl_tac [`s`,`G`,`tn`] >>
      simp[emitted_insts_def, inst_seq_ptr_def,
           immutable_copy_ghost_frame_refl, wordsTheory.WORD_ADD_0]) >>
  Cases_on `op`
  >- (gvs[compile_lit_byte_offset_def, comp_return_def,
           eval_operand_def, op_taint_def] >>
      qexistsl_tac [`s`,`G`,`tn`] >>
      simp[emitted_insts_def, inst_seq_ptr_def,
           immutable_copy_ghost_frame_refl, eval_operand_def,
           op_taint_def, copy_old_operand_def]) >>
  (gvs[compile_lit_byte_offset_def, emit_op_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def,
      emit_def] >>
  qmatch_asmsub_abbrev_tac `mk_inst id ADD [left;_] [out]` >>
  `step_inst_base (mk_inst id ADD [left; Lit (n2w off)] [out]) s =
     OK (update_var out (a+n2w off) s)` by
    simp[mk_inst_def, step_inst_base_opcode_eqs, exec_pure2_def,
         eval_operand_def, Abbr `left`] >>
  `s' = update_var out (a+n2w off) s` by
    (gvs[copy_runtime_frame_def, emitted_insts_def, DROP_APPEND,
         run_inst_seq_def]) >>
  qexists_tac `s'` >>
  qexists_tac `step_prov PG G (mk_inst id ADD [left; Lit (n2w off)] [out]) s'` >>
  qexists_tac `step_taint (mk_inst id ADD [left; Lit (n2w off)] [out]) s s' tn` >>
  conj_tac
  >- (simp[emitted_insts_def, DROP_APPEND, inst_seq_ptr_def] >>
      gen_tac >> conj_tac
      >- (irule ptr_inst_ok_copy_len_binop >> simp[op_taint_def, Abbr `left`]) >>
      `~is_terminator (mk_inst id ADD [left; Lit (n2w off)] [out]).inst_opcode` by
        simp[mk_inst_def, is_terminator_def] >>
      simp[step_inst_inst_idx_indep, exec_result_map_def]) >>
  simp[immutable_copy_ghost_frame_def] >>
  `!x. not_fresh_at sa x ==> x <> out` by
    (simp[Abbr `out`, not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  gvs[] >> simp[copy_len_binop_ghost_frame,
                 toplevel_immutable_add_ghost_frame] >>
  rpt strip_tac >> `x <> out` by metis_tac[] >>
  simp[copy_len_binop_ghost_frame])
QED

Theorem toplevel_immutable_load_frame:
  compile_imm_load_word F imm op sa = (r,sb) /\
  copy_old_operand sa op /\ eval_operand op s = SOME a /\
  op_taint tn op = {} /\ ~ctx_has_dalloca ctx ==>
  ?t H tm.
    (!pc. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
       (s with vs_inst_idx := pc) H tm) /\
    immutable_copy_ghost_frame sa s G tn sb t H tm 0 0 0w /\
    eval_operand r t = SOME (immutable_copy_read F a s) /\
    op_taint tm r = {} /\ copy_old_operand sb r
Proof
  strip_tac >> drule_all copy_runtime_load >> strip_tac >>
  gvs[compile_imm_load_word_def, emit_op_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def,
      emit_def] >>
  qmatch_asmsub_abbrev_tac `mk_inst id DLOAD _ [out]` >>
  qmatch_asmsub_abbrev_tac `eval_operand (Var out) s' = SOME w` >>
  `step_inst_base (mk_inst id DLOAD [op] [out]) s =
     OK (update_var out w s)` by
    simp[mk_inst_def, step_inst_base_opcode_eqs, exec_read1_def,
         Abbr `w`, immutable_copy_read_def] >>
  `s' = update_var out w s` by
    gvs[copy_runtime_frame_def, emitted_insts_def, DROP_APPEND, run_inst_seq_def] >>
  qexists_tac `s'` >>
  qexists_tac `step_prov PG G (mk_inst id DLOAD [op] [out]) s'` >>
  qexists_tac `step_taint (mk_inst id DLOAD [op] [out]) s s' tn` >>
  conj_tac
  >- (simp[emitted_insts_def, DROP_APPEND, inst_seq_ptr_def] >>
      gen_tac >> conj_tac
      >- (irule toplevel_ptr_inst_ok_load >> simp[]) >>
      `~is_terminator (mk_inst id DLOAD [op] [out]).inst_opcode` by
        simp[mk_inst_def, is_terminator_def] >>
      simp[step_inst_inst_idx_indep, exec_result_map_def]) >>
  simp[immutable_copy_ghost_frame_def] >>
  `!x. not_fresh_at sa x ==> x <> out` by
    (simp[Abbr `out`, not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  gvs[] >> simp[toplevel_immutable_dload_ghost_frame] >>
  rpt strip_tac >> `x <> out` by metis_tac[] >>
  simp[toplevel_immutable_dload_ghost_frame]
QED

Theorem toplevel_immutable_store_frame:
  emit_void MSTORE [Var dst;value] sa = ((),sb) /\
  copy_old_operand sa (Var dst) /\ copy_old_operand sa value /\
  lookup_var dst s = SOME a /\ eval_operand value s = SOME w /\
  op_taint tn value = {} /\ ptr_covers G tn dst s 32 /\
  w2n a = w2n b+off /\ ~ctx_has_dalloca ctx ==>
  (!pc. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
    (s with vs_inst_idx := pc) G
    (tn with t_mem := tn.t_mem DIFF {q | w2n a <= q /\ q < w2n a+32})) /\
  immutable_copy_ghost_frame sa s G tn sb (mstore (w2n a) w s) G
    (tn with t_mem := tn.t_mem DIFF {q | w2n a <= q /\ q < w2n a+32})
    off 32 b
Proof
  strip_tac >>
  `copy_runtime_frame sa s sb (mstore (w2n a) w s)` by
    (irule copy_runtime_store >> qexistsl_tac [`Var dst`,`value`] >>
     simp[eval_operand_def]) >>
  drule_all toplevel_immutable_mstore_ghost_frame >> strip_tac >>
  conj_tac
  >- (qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
      simp[emit_void_def, comp_bind_def, comp_ignore_bind_def,
           comp_return_def, fresh_id_def, emit_def] >> strip_tac >> gvs[] >>
      simp[emitted_insts_def, DROP_APPEND, inst_seq_ptr_def] >>
      `step_inst_base (mk_inst sa.cs_next_id MSTORE [Var dst;value] []) s =
         OK (mstore (w2n a) w s)` by
        simp[mk_inst_def, step_inst_base_opcode_eqs, exec_write2_def,
             eval_operand_def] >>
      `~is_terminator (mk_inst sa.cs_next_id MSTORE [Var dst;value] []).inst_opcode` by
        simp[mk_inst_def, is_terminator_def] >>
      simp[step_inst_inst_idx_indep, exec_result_map_def] >>
      gen_tac >> irule toplevel_ptr_inst_ok_mstore >> simp[]) >>
  simp[immutable_copy_ghost_frame_def, op_taint_def]
QED

Theorem immutable_copy_ghost_frame_covers:
  immutable_copy_ghost_frame sa s G tn sb t H tm off nb b /\
  not_fresh_at sa root /\ ptr_covers G tn root s capacity ==>
  ptr_covers H tm root t capacity
Proof
  simp[immutable_copy_ghost_frame_def, copy_runtime_frame_def,
       ptr_covers_def] >> metis_tac[]
QED

Theorem immutable_copy_ghost_frame_operand:
  immutable_copy_ghost_frame sa s G tn sb t H tm off nb b /\
  copy_old_operand sa op ==>
  eval_operand op t = eval_operand op s /\ op_taint tm op = op_taint tn op
Proof
  strip_tac >> conj_tac
  >- metis_tac[immutable_copy_ghost_frame_def, copy_runtime_frame_operand] >>
  Cases_on `op` >> gvs[op_taint_def, copy_old_operand_def,
                         immutable_copy_ghost_frame_def]
QED

Theorem immutable_copy_ghost_frame_zero_offset:
  immutable_copy_ghost_frame sa s G tn sb t H tm off 0 b <=>
  immutable_copy_ghost_frame sa s G tn sb t H tm 0 0 0w
Proof
  simp[immutable_copy_ghost_frame_def, pred_setTheory.EXTENSION]
QED

Theorem immutable_copy_ghost_frame_pc:
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb) /\
  immutable_copy_ghost_frame sa s G tn sb t H tm off nb b ==>
  immutable_copy_ghost_frame sa (s with vs_inst_idx := pc) G tn
    sb (t with vs_inst_idx := pc) H tm off nb b
Proof
  simp[immutable_copy_ghost_frame_def, copy_runtime_frame_def] >>
  rpt strip_tac >>
  gvs[run_inst_seq_inst_idx, exec_result_map_def, copy_static_def,
      lookup_var_def]
QED

Theorem toplevel_immutable_destination_frame:
  compile_lit_byte_offset (Var root) off sa = (r,sb) /\
  not_fresh_at sa root /\ lookup_var root s = SOME b /\
  ptr_covers G tn root s capacity /\ off+32 <= capacity /\
  w2n b+capacity < dimword (:256) /\ ~ctx_has_dalloca ctx ==>
  ?dst t H tm.
    r = Var dst /\
    (!pc. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := pc) H tm) /\
    immutable_copy_ghost_frame sa s G tn sb t H tm 0 0 0w /\
    lookup_var dst t = SOME (b+n2w off) /\
    ptr_covers H tm dst t 32 /\ copy_old_operand sb (Var dst)
Proof
  strip_tac >>
  `copy_old_operand sa (Var root) /\ eval_operand (Var root) s = SOME b /\
   op_taint tn (Var root) = {}` by
    gvs[copy_old_operand_def, eval_operand_def, ptr_covers_def, op_taint_def] >>
  drule_all toplevel_immutable_offset_frame >>
  disch_then (qspecl_then [`fn`,`PG`,`G`,`D`] strip_assume_tac) >>
  Cases_on `off = 0`
  >- (gvs[compile_lit_byte_offset_def, comp_return_def] >>
      qexistsl_tac [`t`,`H`,`tm`] >> simp[] >>
      conj_tac >- gvs[eval_operand_def] >>
      `ptr_covers H tm root t capacity` by
        metis_tac[immutable_copy_ghost_frame_covers] >>
      gvs[ptr_covers_def] >> decide_tac) >>
  gvs[compile_lit_byte_offset_def, emit_op_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def,
      emit_def] >>
  rename1 `eval_operand (Var dst) t = SOME _` >>
  qexistsl_tac [`t`,`H`,`tm`] >> simp[] >>
  conj_tac >- gvs[eval_operand_def] >>
  qpat_x_assum `!pc. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _` (qspec_then `s.vs_inst_idx` mp_tac) >>
  gvs[emitted_insts_def, DROP_APPEND, inst_seq_ptr_def] >>
  `step_inst_base (mk_inst sa.cs_next_id ADD [Var root;Lit (n2w off)] [dst]) s =
   OK (update_var dst (b+n2w off) s)` by
    simp[mk_inst_def, step_inst_base_opcode_eqs, exec_pure2_def, eval_operand_def] >>
  simp[] >> strip_tac >>
  `t = update_var dst (b+n2w off) s` by
    gvs[immutable_copy_ghost_frame_def, copy_runtime_frame_def,
        emitted_insts_def, DROP_APPEND, run_inst_seq_def] >>
  gvs[] >> irule toplevel_immutable_offset_coverage >> simp[] >>
  qexists_tac `capacity` >> simp[]
QED

Theorem toplevel_immutable_frame_append:
  immutable_copy_ghost_frame sa s G tn sm t H tm 0 0 0w /\
  immutable_copy_ghost_frame sm t H tm sb u J tu off nb b /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sm) /\
  (!pc. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sm)
     (s with vs_inst_idx := pc) H tm) /\
  (!pc. inst_seq_ptr D 0 ctx fn PG H tm (emitted_insts sm sb)
     (t with vs_inst_idx := pc) J tu) ==>
  immutable_copy_ghost_frame sa s G tn sb u J tu off nb b /\
  (!pc. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
     (s with vs_inst_idx := pc) J tu)
Proof
  strip_tac >> conj_tac
  >- (irule (immutable_copy_ghost_frame_trans |> Q.INST [`m` |-> `0`] |> SRULE []) >>
      qexistsl_tac [`H`,`sm`,`t`,`tm`] >>
      metis_tac[immutable_copy_ghost_frame_zero_offset]) >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> gvs[immutable_copy_ghost_frame_def,
                                      copy_runtime_frame_def]) >>
  simp[] >> irule inst_seq_ptr_uniform_append >>
  metis_tac[immutable_copy_ghost_frame_def, copy_runtime_frame_def]
QED

Theorem toplevel_immutable_offset_nonterminators:
  compile_lit_byte_offset op off sa = (r,sb) ==>
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)
Proof
  strip_tac >> drule code_offset_insts >>
  simp[listTheory.EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >> gvs[is_terminator_def]
QED

Theorem toplevel_immutable_load_nonterminators:
  compile_imm_load_word F imm op sa = (r,sb) ==>
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)
Proof
  simp[compile_imm_load_word_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def,
       emit_def] >> rpt strip_tac >> gvs[] >>
  simp[emitted_insts_def, DROP_APPEND, mk_inst_def, is_terminator_def]
QED

Theorem toplevel_immutable_one_frame:
  immutable_copy_one F imm src (Var root) off sa = ((),sb) /\
  copy_old_operand sa src /\ not_fresh_at sa root /\
  eval_operand src s = SOME a /\ lookup_var root s = SOME b /\
  op_taint tn src = {} /\ ptr_covers G tn root s capacity /\
  off+32 <= capacity /\ w2n b+capacity < dimword (:256) /\
  ~ctx_has_dalloca ctx ==>
  ?t H tm.
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    (!pc. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := pc) H tm) /\
    ptr_covers H tm root t capacity /\
    immutable_copy_ghost_frame sa s G tn sb t H tm off 32 b
Proof
  simp[immutable_copy_one_def, immutable_comp_bind_cases] >> strip_tac >>
  drule_all toplevel_immutable_offset_frame >>
  disch_then (qspecl_then [`fn`,`PG`,`G`,`D`] strip_assume_tac) >>
  rename1 `compile_lit_byte_offset src off sa = (sop,s1)` >>
  rename1 `immutable_copy_ghost_frame sa s G tn s1 t1 G1 tn1 _ _ _` >>
  drule_all toplevel_immutable_load_frame >>
  disch_then (qspecl_then [`fn`,`PG`,`G1`,`D`] strip_assume_tac) >>
  rename1 `compile_imm_load_word F imm sop s1 = (value,s2)` >>
  rename1 `immutable_copy_ghost_frame s1 t1 G1 tn1 s2 t2 G2 tn2 _ _ _` >>
  `immutable_copy_ghost_frame sa s G tn s2 t2 G2 tn2 0 0 0w /\
   (!pc. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa s2)
     (s with vs_inst_idx := pc) G2 tn2)` by
    (irule toplevel_immutable_frame_append >>
     qexistsl_tac [`G1`,`s1`,`t1`,`tn1`] >> simp[] >>
     metis_tac[toplevel_immutable_offset_nonterminators]) >>
  `not_fresh_at s2 root /\ lookup_var root t2 = SOME b /\
   ptr_covers G2 tn2 root t2 capacity` by
    (conj_tac
     >- (gvs[immutable_copy_ghost_frame_def, copy_runtime_frame_def,
             not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
     conj_tac
     >- (drule_at Any immutable_copy_ghost_frame_operand >>
         disch_then (qspec_then `Var root` mp_tac) >>
         simp[copy_old_operand_def, eval_operand_def]) >>
     metis_tac[immutable_copy_ghost_frame_covers]) >>
  `w2n b+capacity < dimword (:256)` by decide_tac >>
  drule_all toplevel_immutable_destination_frame >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  gvs[] >> suspend "store_and_compose"
QED

Resume toplevel_immutable_one_frame[store_and_compose]:
  rename1 `immutable_copy_ghost_frame s2 t2 G2 tn2 s3 t3 G3 tn3 0 0 0w` >>
  `copy_old_operand s3 value` by
    metis_tac[copy_old_operand_mono, immutable_copy_ghost_frame_def,
              copy_runtime_frame_def] >>
  `eval_operand value t3 = SOME (immutable_copy_read F (a+n2w off) t1) /\
   op_taint tn3 value = {}` by
    metis_tac[immutable_copy_ghost_frame_operand] >>
  `w2n (b+n2w off) = w2n b+off` by
    (Cases_on `b` >> gvs[wordsTheory.word_add_n2w] >> decide_tac) >>
  drule_all toplevel_immutable_store_frame >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `immutable_copy_ghost_frame s3 t3 G3 tn3 sb t4 G3 tn4 off 32 b` >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts s2 s3)` by
    metis_tac[toplevel_immutable_offset_nonterminators] >>
  `immutable_copy_ghost_frame s2 t2 G2 tn2 sb t4 G3 tn4 off 32 b /\
   (!pc. inst_seq_ptr D 0 ctx fn PG G2 tn2 (emitted_insts s2 sb)
     (t2 with vs_inst_idx := pc) G3 tn4)` by
    (irule toplevel_immutable_frame_append >>
     qexistsl_tac [`G3`,`s3`,`t3`,`tn3`] >> simp[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts s1 s2)` by
    metis_tac[toplevel_immutable_load_nonterminators] >>
  `immutable_copy_ghost_frame s1 t1 G1 tn1 sb t4 G3 tn4 off 32 b /\
   (!pc. inst_seq_ptr D 0 ctx fn PG G1 tn1 (emitted_insts s1 sb)
     (t1 with vs_inst_idx := pc) G3 tn4)` by
    (irule toplevel_immutable_frame_append >>
     qexistsl_tac [`G2`,`s2`,`t2`,`tn2`] >> simp[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa s1)` by
    metis_tac[toplevel_immutable_offset_nonterminators] >>
  `immutable_copy_ghost_frame sa s G tn sb t4 G3 tn4 off 32 b /\
   (!pc. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
     (s with vs_inst_idx := pc) G3 tn4)` by
    (irule toplevel_immutable_frame_append >>
     qexistsl_tac [`G1`,`s1`,`t1`,`tn1`] >> simp[]) >>
  qexistsl_tac [`t4`,`G3`,`tn4`] >> simp[] >>
  conj_tac
  >- gvs[immutable_copy_ghost_frame_def, copy_runtime_frame_def] >>
  metis_tac[immutable_copy_ghost_frame_covers]
QED

Finalise toplevel_immutable_one_frame

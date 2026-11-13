Theory bodyPtrIfExpRuntimeOne
Ancestors bodyPtrIfExpRuntimeCompiler bodyPtrIfExpRuntimeOffset
  bodyPtrIfExpMaterializeWord exprSimCopy exprSimStorageCopy fragExec
  instIdxIndep venomState emitHelper context compileEnv loweringStateRelDefs venomExecSemantics
  venomInst exprSimPtrProps fragGasPathPtr immutableCopyExecution
  exprLoweringProps emitHelperProps bodyPtrIfExpScalarLoad finite_map
  bodyPtrDefs ptrDiscipline words arithmetic pred_set ghostPcTransportPtr

(* Fixed-run frames commute with restoring a straight-line cursor. *)
Theorem ifexp_runtime_frame_cursor:
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts ca cb) /\
  copy_runtime_frame ca s cb t ==>
  copy_runtime_frame ca (s with vs_inst_idx := k) cb
    (t with vs_inst_idx := k)
Proof
  simp[copy_runtime_frame_def] >> strip_tac >>
  simp[run_inst_seq_inst_idx, exec_result_map_def,
       copy_static_def, lookup_var_def] >>
  gvs[copy_static_def, lookup_var_def]
QED

Theorem ifexp_runtime_frame_then:
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts cb cc) /\
  copy_runtime_frame ca s cb (r with vs_inst_idx := s.vs_inst_idx) /\
  copy_runtime_frame cb r cc (t with vs_inst_idx := r.vs_inst_idx) ==>
  copy_runtime_frame ca s cc (t with vs_inst_idx := s.vs_inst_idx)
Proof
  strip_tac >>
  drule_all ifexp_runtime_frame_cursor >>
  disch_then (qspec_then `s.vs_inst_idx` mp_tac) >>
  simp[] >> strip_tac >>
  drule_all copy_runtime_frame_trans >> simp[]
QED

Theorem ifexp_runtime_store_path:
  emit_void MSTORE [Var p;value] ca = ((),cb) /\
  fn_has_code ca cb fn /\ ptr_covers G tn p s 32 /\
  eval_operand (Var p) s = SOME a /\ eval_operand value s = SOME w /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = ca.cs_current_bb /\
  s.vs_inst_idx = LENGTH ca.cs_current_insts ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst ca.cs_next_id MSTORE [Var p;value] [])
      (mstore (w2n a) w s))
    (step_taint (mk_inst ca.cs_next_id MSTORE [Var p;value] []) s
      (mstore (w2n a) w s) tn)
    (OK (mstore (w2n a) w s with vs_inst_idx := LENGTH cb.cs_current_insts))
Proof
  strip_tac >>
  `cb.cs_current_bb = ca.cs_current_bb /\
   cb.cs_current_insts = ca.cs_current_insts ++
     [mk_inst ca.cs_next_id MSTORE [Var p;value] []]` by
    gvs[emit_void_def, comp_bind_def, comp_ignore_bind_def,
        fresh_id_def, emit_def, comp_return_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
    SOME (mk_inst ca.cs_next_id MSTORE [Var p;value] [])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `step_inst_base (mk_inst ca.cs_next_id MSTORE [Var p;value] []) s =
    OK (mstore (w2n a) w s)` by
    (pure_once_rewrite_tac[step_inst_base_def] >>
     pure_rewrite_tac[instruction_accessors, instruction_accfupds, opcode_case_def,
                      mk_inst_def, combinTheory.K_THM] >>
     simp[exec_write2_def]) >>
  `LENGTH cb.cs_current_insts = SUC s.vs_inst_idx` by simp[] >>
  simp[] >>
  qpat_x_assum `s.vs_inst_idx = _` (fn th => rewrite_tac[GSYM th]) >>
  irule gas_path_ptr_one_step >>
  simp[mk_inst_def, is_terminator_def, mstore_def, write_memory_with_expansion_def] >>
  simp[GSYM mk_inst_def] >> irule ifexp_materialize_mstore_check >> simp[]
QED

Theorem ifexp_runtime_load_frame:
  emit_op DLOAD [arg] ca = (value,cb) /\
  copy_old_operand ca arg /\ eval_operand arg s = SOME a ==>
  ?out. value = Var out /\
    copy_runtime_frame ca s cb
      (update_var out (immutable_copy_read F a s) s) /\
    copy_old_operand cb value
Proof
  strip_tac >>
  `compile_imm_load_word F imm arg ca = (value,cb)` by
    simp[compile_imm_load_word_def] >>
  drule_all copy_runtime_load >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  qexists_tac `STRING #"%" (toString ca.cs_next_var)` >> simp[] >>
  qpat_x_assum `copy_runtime_frame _ _ _ _` mp_tac >>
  simp[copy_runtime_frame_def, run_inst_seq_def, mk_inst_def,
       step_inst_base_opcode_eqs, exec_read1_def, immutable_copy_read_def] >>
  strip_tac >> gvs[]
QED

Theorem ifexp_runtime_load_step:
  eval_operand arg s = SOME a ==>
  step_inst_base (mk_inst id DLOAD [arg] [out]) s =
    OK (update_var out (immutable_copy_read F a s) s)
Proof
  simp[mk_inst_def, step_inst_base_opcode_eqs, exec_read1_def,
       immutable_copy_read_def]
QED

Theorem ifexp_runtime_load_path:
  emit_op DLOAD [arg] ca = (value,cb) /\ copy_old_operand ca arg /\
  eval_operand arg s = SOME a /\ op_taint tn arg = {} /\
  fn_has_code ca cb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = ca.cs_current_bb /\
  s.vs_inst_idx = LENGTH ca.cs_current_insts ==>
  ?t H tt out.
    value = Var out /\
    t = (update_var out (immutable_copy_read F a s) s with
      vs_inst_idx := LENGTH cb.cs_current_insts) /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tt (OK t) /\
    copy_runtime_frame ca s cb (t with vs_inst_idx := s.vs_inst_idx) /\
    copy_old_operand cb value /\
    op_prov H value = NONE /\ op_taint tt value = {} /\
    t.vs_current_bb = cb.cs_current_bb /\ ~t.vs_halted /\
    tt.t_mem = tn.t_mem /\ tt.t_stor = tn.t_stor /\
    tt.t_trans = tn.t_trans /\ tt.t_imm = tn.t_imm /\
    (!x. not_fresh_at ca x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint tt (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  drule_all ifexp_runtime_load_frame >> strip_tac >>
  `step_inst_base
    (mk_inst ca.cs_next_id DLOAD [arg] [STRING #"%" (toString ca.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString ca.cs_next_var))
       (immutable_copy_read F a s) s)` by
    (irule ifexp_runtime_load_step >> simp[]) >>
  drule_all (ifexp_emit_scalar_load_ptr_path |> SPEC_ALL |>
    Q.INST [`opc` |-> `DLOAD`] |> SRULE []) >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  `cb.cs_current_bb = ca.cs_current_bb /\
   LENGTH cb.cs_current_insts = SUC s.vs_inst_idx` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def]) >>
  goal_assum (drule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  qexists_tac `out` >>
  simp[update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  qpat_x_assum `s.vs_inst_idx = _` (fn th => rewrite_tac[GSYM th]) >>
  gvs[update_var_def] >> metis_tac[]
QED

Theorem ifexp_runtime_read_path:
  compile_lit_byte_offset src off ca = (arg,cb) /\
  emit_op DLOAD [arg] cb = (value,cc) /\
  fn_has_code ca cb fn /\ fn_has_code cb cc fn /\
  copy_old_operand ca src /\ eval_operand src s = SOME a /\
  op_taint tn src = {} /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = ca.cs_current_bb /\
  s.vs_inst_idx = LENGTH ca.cs_current_insts ==>
  ?t H tt.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tt (OK t) /\
    copy_runtime_frame ca s cc (t with vs_inst_idx := s.vs_inst_idx) /\
    eval_operand value t = SOME (immutable_copy_read F (a+n2w off) s) /\
    copy_old_operand cc value /\ op_prov H value = NONE /\ op_taint tt value = {} /\
    t.vs_current_bb = cc.cs_current_bb /\
    t.vs_inst_idx = LENGTH cc.cs_current_insts /\ ~t.vs_halted /\
    t.vs_memory = s.vs_memory /\ tt.t_mem = tn.t_mem /\ tt.t_stor = tn.t_stor /\
    tt.t_trans = tn.t_trans /\ tt.t_imm = tn.t_imm /\
    (!x. not_fresh_at ca x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint tt (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  drule_all ifexp_runtime_offset_path >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK r)` >>
  `copy_old_operand cb arg` by
    (drule_all copy_runtime_offset >> strip_tac >> simp[]) >>
  `r.vs_data_section = s.vs_data_section` by
    (qpat_x_assum `copy_runtime_frame ca s cb _` mp_tac >>
     simp[copy_runtime_frame_def] >> strip_tac >>
     qpat_x_assum `copy_static _ = _` (mp_tac o AP_TERM ``\z:venom_state. z.vs_data_section``) >>
     simp[copy_static_def]) >>
  drule_all ifexp_runtime_load_path >>
  disch_then (qspecl_then [`PG`, `G1`, `D`] strip_assume_tac) >>
  suspend "read_finish"
QED

Resume ifexp_runtime_read_path[read_finish]:
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts cb cc)` by
    (drule emitted_insts_emit_op >> simp[mk_inst_def, is_terminator_def]) >>
  `copy_runtime_frame ca s cc (t with vs_inst_idx := s.vs_inst_idx)` by
    (irule ifexp_runtime_frame_then >> metis_tac[]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 H tt (OK t)` by
    (drule_all gas_path_ptr_then >> simp[]) >>
  `ca.cs_next_var <= cb.cs_next_var` by
    gvs[copy_runtime_frame_def] >>
  qexistsl_tac [`t`, `H`, `tt`] >>
  simp[] >>
  conj_tac >- simp[eval_operand_def, lookup_var_def, update_var_def,
                  FLOOKUP_UPDATE, immutable_copy_read_def] >>
  conj_tac >- simp[update_var_def] >>
  qx_gen_tac `x` >> disch_tac >>
  `not_fresh_at cb x` by
    (simp[not_fresh_at_def] >> rpt strip_tac >>
     qpat_x_assum `not_fresh_at ca x` mp_tac >>
     simp[not_fresh_at_def] >>
     disch_then (qspec_then `n` mp_tac) >> simp[]) >>
  metis_tac[]
QED

Finalise ifexp_runtime_read_path

Theorem ifexp_runtime_write_path:
  compile_lit_byte_offset (Var root) off ca = (addr,cb) /\
  emit_void MSTORE [addr;value] cb = ((),cc) /\
  fn_has_code ca cb fn /\ fn_has_code cb cc fn /\
  copy_old_operand ca (Var root) /\ copy_old_operand ca value /\
  lookup_var root s = SOME d /\ eval_operand value s = SOME w /\
  op_taint tn value = {} /\ ptr_covers G tn root s capacity /\
  off+32 <= capacity /\ w2n d+capacity < dimword (:256) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = ca.cs_current_bb /\
  s.vs_inst_idx = LENGTH ca.cs_current_insts ==>
  ?t H tt r J tr p.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tt (OK t) /\
    copy_runtime_frame ca s cc (t with vs_inst_idx := s.vs_inst_idx) /\
    t.vs_memory = (mstore (w2n (d+n2w off)) w s).vs_memory /\
    t.vs_current_bb = cc.cs_current_bb /\
    t.vs_inst_idx = LENGTH cc.cs_current_insts /\ ~t.vs_halted /\
    ptr_covers H tt root t capacity /\
    tt.t_mem = tn.t_mem DIFF {i | w2n d+off <= i /\ i < w2n d+off+32} /\
    tt.t_stor = tn.t_stor /\ tt.t_trans = tn.t_trans /\ tt.t_imm = tn.t_imm /\
    (!x. not_fresh_at ca x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint tt (Var x) = op_taint tn (Var x)) /\
    addr = Var p /\ eval_operand addr r = SOME (d+n2w off) /\
    eval_operand value r = SOME w /\ op_taint tr value = {} /\
    t = (mstore (w2n (d+n2w off)) w r with vs_inst_idx := LENGTH cc.cs_current_insts) /\
    H = step_prov PG J (mk_inst cb.cs_next_id MSTORE [addr;value] [])
      (mstore (w2n (d+n2w off)) w r) /\
    tt = step_taint (mk_inst cb.cs_next_id MSTORE [addr;value] []) r
      (mstore (w2n (d+n2w off)) w r) tr /\
    copy_runtime_frame ca s cb (r with vs_inst_idx := s.vs_inst_idx) /\
    r.vs_memory = s.vs_memory /\ tr.t_mem = tn.t_mem /\
    tr.t_stor = tn.t_stor /\ tr.t_trans = tn.t_trans /\ tr.t_imm = tn.t_imm /\
    (!x. not_fresh_at ca x ==> lookup_var x r = lookup_var x s /\
      FLOOKUP J x = FLOOKUP G x /\ op_taint tr (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `eval_operand (Var root) s = SOME d /\ op_taint tn (Var root) = {}` by
    gvs[eval_operand_def, ptr_covers_def] >>
  drule_all ifexp_runtime_offset_path >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx fn PG G tn s 0 J tr (OK r)` >>
  `copy_old_operand cb addr` by
    (drule_all copy_runtime_offset >> strip_tac >> simp[]) >>
  `copy_old_operand cb value` by
    (irule copy_old_operand_mono >> qexists_tac `ca` >>
     gvs[copy_runtime_frame_def]) >>
  `eval_operand value r = SOME w` by
    (drule_all copy_runtime_frame_operand >> simp[]) >>
  `op_taint tr value = {}` by
    (Cases_on `value` >> gvs[copy_old_operand_def, op_taint_def] >> metis_tac[]) >>
  `w2n d+off < dimword (:256)` by decide_tac >>
  `?p. addr = Var p /\ ptr_covers J tr p r 32` by
    (drule_all ifexp_runtime_offset_covers >> simp[]) >>
  suspend "write_store"
QED

Resume ifexp_runtime_write_path[write_store]:
  gvs[] >>
  drule_all ifexp_runtime_store_path >>
  disch_then (qspecl_then [`PG`, `D`] assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx fn PG J tr r 0 H tt (OK t)` >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 H tt (OK t)` by
    (drule_all gas_path_ptr_then >> simp[]) >>
  `copy_runtime_frame cb r cc (mstore (w2n (d+n2w off)) w r)` by
    (irule copy_runtime_store >> simp[] >> metis_tac[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts cb cc)` by
    (drule emitted_insts_emit_void >> simp[mk_inst_def, is_terminator_def]) >>
  `t with vs_inst_idx := r.vs_inst_idx = mstore (w2n (d+n2w off)) w r` by
    (simp[Abbr `t`, mstore_def, write_memory_with_expansion_def] >>
     qpat_x_assum `r.vs_inst_idx = _` (fn th => rewrite_tac[GSYM th]) >> simp[]) >>
  `copy_runtime_frame ca s cc (t with vs_inst_idx := s.vs_inst_idx)` by
    (irule ifexp_runtime_frame_then >> qexistsl_tac [`cb`, `r`] >>
     asm_rewrite_tac[]) >>
  qexistsl_tac [`r`, `J`, `tr`] >>
  simp[Abbr `t`, Abbr `H`, Abbr `tt`, ifexp_materialize_mstore_ghost] >>
  suspend "write_post"
QED

Resume ifexp_runtime_write_path[write_post]:
  gvs[] >>
  conj_tac >- simp[mstore_def, write_memory_with_expansion_def] >>
  conj_tac >-
    (drule emit_void_same_blocks >> simp[same_blocks_def, mstore_def,
                                         write_memory_with_expansion_def]) >>
  `!x. op_taint
    (step_taint (mk_inst cb.cs_next_id MSTORE [Var p;value] []) r
      (mstore (w2n (d+n2w off)) w r) tr) (Var x) = op_taint tr (Var x)` by
    simp[op_taint_def, ifexp_materialize_mstore_ghost] >>
  conj_tac >-
    (gvs[ptr_covers_def, copy_old_operand_def] >>
     qpat_x_assum `!p. not_fresh_at ca p ==> _` (qspec_then `root` mp_tac) >>
     simp[lookup_var_def, mstore_def, write_memory_with_expansion_def] >>
     metis_tac[]) >>
  conj_tac >-
    (`w2n (d+n2w off) = w2n d+off` by
       (simp[w2n_add_2] >> decide_tac) >>
     simp[ifexp_materialize_mstore_taint, EXTENSION] >> decide_tac) >>
  simp[lookup_var_def, mstore_def, write_memory_with_expansion_def] >>
  rpt strip_tac >>
  qpat_x_assum `!p. not_fresh_at ca p ==> _` (qspec_then `x` mp_tac) >>
  simp[lookup_var_def]
QED

Finalise ifexp_runtime_write_path

Theorem ifexp_runtime_offset_nonterm[local]:
  compile_lit_byte_offset (Var root) off ca = (addr,cb) ==>
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts ca cb)
Proof
  Cases_on `off = 0` >>
  simp[compile_lit_byte_offset_def, comp_return_def] >> rpt strip_tac >>
  gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
      fresh_id_def, emit_def, comp_return_def, emitted_insts_def,
      DROP_PREFIX, mk_inst_def, is_terminator_def]
QED

Theorem ifexp_runtime_write_nonterm[local]:
  compile_lit_byte_offset (Var root) off ca = (addr,cb) /\
  emit_void MSTORE [addr;value] cb = ((),cc) ==>
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts ca cc)
Proof
  Cases_on `off = 0` >>
  simp[compile_lit_byte_offset_def, comp_return_def] >>
  rpt strip_tac >>
  gvs[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
      fresh_var_def, fresh_id_def, emit_def, comp_return_def,
      emitted_insts_def, mk_inst_def, is_terminator_def,
      DROP_PREFIX] >>
  pure_once_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
  simp[DROP_PREFIX, mk_inst_def, is_terminator_def]
QED

Theorem ifexp_runtime_one_path:
  immutable_copy_one F imm src (Var root) off ca = ((),cb) /\
  fn_has_code ca cb fn /\ copy_old_operand ca src /\
  copy_old_operand ca (Var root) /\ eval_operand src s = SOME a /\
  lookup_var root s = SOME d /\ op_taint tn src = {} /\
  ptr_covers G tn root s capacity /\ off+32 <= capacity /\
  w2n d+capacity < dimword (:256) /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = ca.cs_current_bb /\
  s.vs_inst_idx = LENGTH ca.cs_current_insts ==>
  ?t H tt.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tt (OK t) /\
    copy_runtime_frame ca s cb (t with vs_inst_idx := s.vs_inst_idx) /\
    t.vs_memory = (immutable_word_transfer F F a d off s).vs_memory /\
    t.vs_current_bb = cb.cs_current_bb /\
    t.vs_inst_idx = LENGTH cb.cs_current_insts /\ ~t.vs_halted /\
    ptr_covers H tt root t capacity /\
    eval_operand src t = SOME a /\ op_taint tt src = {} /\
    tt.t_mem = tn.t_mem DIFF {i | w2n d+off <= i /\ i < w2n d+off+32} /\
    tt.t_stor = tn.t_stor /\ tt.t_trans = tn.t_trans /\ tt.t_imm = tn.t_imm /\
    (!x. not_fresh_at ca x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint tt (Var x) = op_taint tn (Var x)) /\
    ?cc addr value r J tr.
      emit_void MSTORE [addr;value] cc = ((),cb) /\
      eval_operand addr r = SOME (d+n2w off) /\
      eval_operand value r = SOME (immutable_copy_read F (a+n2w off) s) /\
      op_taint tr value = {} /\
      t = (mstore (w2n (d+n2w off)) (immutable_copy_read F (a+n2w off) s) r
        with vs_inst_idx := LENGTH cb.cs_current_insts) /\
      H = step_prov PG J (mk_inst cc.cs_next_id MSTORE [addr;value] [])
        (mstore (w2n (d+n2w off)) (immutable_copy_read F (a+n2w off) s) r) /\
      tt = step_taint (mk_inst cc.cs_next_id MSTORE [addr;value] []) r
        (mstore (w2n (d+n2w off)) (immutable_copy_read F (a+n2w off) s) r) tr /\
      copy_runtime_frame ca s cc (r with vs_inst_idx := s.vs_inst_idx) /\
      r.vs_memory = s.vs_memory /\ tr.t_mem = tn.t_mem /\
      tr.t_stor = tn.t_stor /\ tr.t_trans = tn.t_trans /\ tr.t_imm = tn.t_imm /\
      (!x. not_fresh_at ca x ==> lookup_var x r = lookup_var x s /\
        FLOOKUP J x = FLOOKUP G x /\ op_taint tr (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all ifexp_runtime_one_parts >> strip_tac >>
  drule_all ifexp_runtime_read_path >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx fn PG G tn s 0 J tr (OK r)` >>
  `not_fresh_at ca root` by gvs[copy_old_operand_def] >>
  `lookup_var root r = SOME d /\ ptr_covers J tr root r capacity` by
    (qpat_x_assum `!x. not_fresh_at ca x ==> _` (qspec_then `root` mp_tac) >>
     simp[] >> strip_tac >> gvs[ptr_covers_def]) >>
  `copy_old_operand cb' (Var root)` by
    (irule copy_old_operand_mono >> qexists_tac `ca` >>
     gvs[copy_runtime_frame_def]) >>
  suspend "one_write"
QED

Resume ifexp_runtime_one_path[one_write]:
  drule_all ifexp_runtime_write_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx fn PG J tr r 0 H tt (OK t)` >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 H tt (OK t)` by
    (drule_all gas_path_ptr_then >> simp[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts cb' cb)` by
    metis_tac[ifexp_runtime_write_nonterm] >>
  suspend "one_finish"
QED

Resume ifexp_runtime_one_path[one_finish]:
  `copy_runtime_frame ca s cb (t with vs_inst_idx := s.vs_inst_idx)` by
    (irule ifexp_runtime_frame_then >> qexistsl_tac [`cb'`, `r`] >> simp[]) >>
  `t.vs_memory = (immutable_word_transfer F F a d off s).vs_memory` by
    (`eval_operand (Var root) s = SOME d` by simp[eval_operand_def] >>
     drule_all copy_runtime_one >> strip_tac >>
     gvs[copy_runtime_frame_def]) >>
  suspend "one_post"
QED

Resume ifexp_runtime_one_path[one_post]:
  `ca.cs_next_var <= cb'.cs_next_var` by gvs[copy_runtime_frame_def] >>
  `!x. not_fresh_at ca x ==> lookup_var x t = lookup_var x s /\
    FLOOKUP H x = FLOOKUP G x /\ op_taint tt (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >>
     `not_fresh_at cb' x` by
       (simp[not_fresh_at_def] >> rpt strip_tac >>
        qpat_x_assum `not_fresh_at ca x` mp_tac >> simp[not_fresh_at_def] >>
        disch_then (qspec_then `n` mp_tac) >> simp[]) >>
     metis_tac[]) >>
  `eval_operand src t = SOME a` by
    (qpat_assum `copy_runtime_frame ca s cb _`
       (mp_then Any mp_tac copy_runtime_frame_operand) >>
     disch_then (qspec_then `src` mp_tac) >> simp[]) >>
  `op_taint tt src = {}` by
    (Cases_on `src` >> gvs[op_taint_def, copy_old_operand_def] >> metis_tac[]) >>
  qexistsl_tac [`t`, `H`, `tt`] >> simp[] >>
  qexistsl_tac [`cc`, `dop`, `value`, `r''`, `J'`, `tr'`] >> simp[] >>
  conj_tac >-
    (`EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts cb' cc)` by
       metis_tac[ifexp_runtime_offset_nonterm] >>
     qpat_x_assum `s.vs_inst_idx = _` (fn th => rewrite_tac[GSYM th]) >>
     irule ifexp_runtime_frame_then >> qexistsl_tac [`cb'`, `r`] >> simp[]) >>
  rpt strip_tac >>
  `not_fresh_at cb' x` by
    (simp[not_fresh_at_def] >> rpt strip_tac >>
     qpat_x_assum `not_fresh_at ca x` mp_tac >> simp[not_fresh_at_def] >>
     disch_then (qspec_then `n` mp_tac) >> simp[]) >>
  metis_tac[]
QED

Finalise ifexp_runtime_one_path

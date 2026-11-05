(* Completed storage-copy suffix interfaces. *)
Theory exprSimPtrTopLevelStoragePost
Ancestors
  exprSimPtrTopLevelStorageCopy exprSimStorageCopy typedCopyPtr
  exprLoweringProps exprSimPtrTopLevelCopy venomExecSemantics venomInst gasCount fragGasSeqPtr
  rich_list codegenRel decoderGhostFramePtr bodyPtrDefs ptrDiscipline venomState finite_map pred_set list words

Theorem toplevel_copy_loop_post_effects:
  compile_word_copy_loop src (Var dst) n loc LocMemory F sa = (u,sb) /\
  fn_has_code sa sb fn /\ (loc = LocStorage \/ loc = LocTransient) /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa dst /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  lookup_var dst s = SOME (n2w b) /\ ptr_covers G tn dst s cap /\
  32*n <= cap /\ n < 2**256 /\ b+cap < 2**256 /\
  b+cap <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tnf. gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK t) /\
    copy_prefix loc a b n s n t /\ copy_static t = copy_static s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)) /\
    ptr_covers Gf tnf dst t cap /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    tnf.t_mem SUBSET toplevel_copy_taint_bound loc a b tn n /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `ptr_covers G tn dst s (32*n)` by
    (gvs[ptr_covers_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `b+32*n < 2**256 /\ b+32*n <= s.vs_alloca_next` by decide_tac >>
  drule_all toplevel_copy_compiled_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  drule toplevel_copy_inv_content >>
  simp[storage_copy_inv_def, storage_copy_frame_def] >> strip_tac >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> metis_tac[toplevel_copy_inv_ghost_frame]) >>
  `ptr_covers Gf tnf dst t cap` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  qexistsl_tac [`t`, `Gf`, `tnf`] >>
  simp[] >>
  metis_tac[copy_prefix_def, toplevel_copy_inv_storage_taint,
    toplevel_copy_inv_transient_taint, toplevel_copy_inv_immutable_taint,
    toplevel_copy_inv_memory_taint]
QED

Theorem toplevel_copy_word_path:
  (loc = LocStorage \/ loc = LocTransient) /\ ~ctx_has_dalloca ctx /\
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  lookup_var dst s = SOME (n2w b) /\ ptr_covers G tn dst s cap /\
  32 <= cap /\ b+cap < 2**256 /\ tmp <> dst /\
  i = mk_inst id (if loc = LocStorage then SLOAD else TLOAD) [src] [tmp] /\
  j = mk_inst (id+1) MSTORE [Var dst;Var tmp] [] /\
  u = update_var tmp (copy_runtime_word loc s a) s /\
  u1 = u with vs_inst_idx := SUC s.vs_inst_idx /\
  t = mstore b (copy_runtime_word loc s a) u1 /\
  G1 = step_prov PG G i u /\ tn1 = step_taint i s u tn /\
  Gf = step_prov PG G1 j t /\ tnf = step_taint j u1 t tn1 /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX [i;j] (DROP s.vs_inst_idx bb.bb_instructions) ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf
    (OK (t with vs_inst_idx := s.vs_inst_idx+2))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `b < dimword (:256)` by gvs[dimword_def] >>
  `step_inst_base i s = OK u` by
    (Cases_on `loc = LocStorage` >>
     simp[copy_runtime_word_def, step_inst_base_def, mk_inst_def,
       exec_read1_def] >> gvs[]) >>
  `eval_operand (Var dst) u1 = SOME (n2w b) /\
   eval_operand (Var tmp) u1 = SOME (copy_runtime_word loc s a)` by
    (simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     gvs[lookup_var_def]) >>
  `step_inst_base j u1 = OK t` by
    (simp[step_inst_base_def, mk_inst_def, exec_write2_def, eval_operands_def,
      eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     gvs[lookup_var_def]) >>
  `ptr_covers G tn dst s 32` by
    (gvs[ptr_covers_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `run_inst_seq [i;j] s = OK (t with vs_inst_idx := s.vs_inst_idx)` by
    (simp[run_inst_seq_def] >>
     simp[step_inst_base_def, mk_inst_def, exec_write2_def,
       eval_operands_def, eval_operand_def, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE] >> gvs[lookup_var_def, mstore_def]) >>
  `inst_seq_ptr D 0 ctx fn PG G tn [i;j] s Gf tnf` by
    (irule toplevel_load_store_seq_ptr >>
     simp[] >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `EVERY (\k. k.inst_opcode <> INVOKE /\ ~is_terminator k.inst_opcode) [i;j] /\
   LENGTH (FILTER (\k. k.inst_opcode = GAS) [i;j]) = 0` by
    (Cases_on `loc = LocStorage` >> simp[mk_inst_def, is_terminator_def]) >>
  drule_all run_inst_seq_gas_path_ptr >> simp[]
QED

Theorem toplevel_copy_word_content:
  t = mstore b (copy_runtime_word loc s a)
    (update_var tmp (copy_runtime_word loc s a) s with vs_inst_idx := ix) ==>
  copy_prefix loc a b 1 s 1 t /\ copy_static t = copy_static s
Proof
  strip_tac >>
  qabbrev_tac `q = update_var tmp (copy_runtime_word loc s a) s with vs_inst_idx := ix` >>
  `copy_static q = copy_static s` by
    simp[Abbr `q`, copy_static_def, update_var_def] >>
  `copy_prefix loc a b 1 s 0 q` by
    simp[Abbr `q`, copy_prefix_def, copy_static_def, update_var_def] >>
  drule copy_prefix_extend >> simp[WORD_ADD_0, copy_static_mstore]
QED

Theorem toplevel_copy_word_frame:
  (loc = LocStorage \/ loc = LocTransient) /\ x <> tmp /\
  i = mk_inst id (if loc = LocStorage then SLOAD else TLOAD) [src] [tmp] /\
  j = mk_inst (id+1) MSTORE [Var dst;Var tmp] [] /\
  u = update_var tmp w s /\ u1 = u with vs_inst_idx := ix /\
  t = mstore b w u1 /\ r = t with vs_inst_idx := iy /\
  G1 = step_prov PG G i u /\ tn1 = step_taint i s u tn /\
  Gf = step_prov PG G1 j t /\ tnf = step_taint j u1 t tn1 ==>
  lookup_var x r = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
  op_taint tnf (Var x) = op_taint tn (Var x) /\
  tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm
Proof
  strip_tac >>
  simp[lookup_var_def, mstore_def, update_var_def, FLOOKUP_UPDATE] >>
  simp[step_prov_def, out_prov_def, set_prov_def, mk_inst_def,
    FLOOKUP_DRESTRICT, step_taint_other_output] >>
  Cases_on `loc = LocStorage` >>
  simp[step_taint_def, store_taint_def, imm_taint_def, adopt_reset_def, mk_inst_def,
    set_var_taint_def, op_taint_def, FLOOKUP_UPDATE]
QED

Theorem toplevel_copy_word_memory_taint:
  (loc = LocStorage \/ loc = LocTransient) /\ eval_operand src s = SOME a /\
  lookup_var dst s = SOME (n2w b) /\ tmp <> dst /\ b < dimword (:256) /\
  i = mk_inst id (if loc = LocStorage then SLOAD else TLOAD) [src] [tmp] /\
  j = mk_inst (id+1) MSTORE [Var dst;Var tmp] [] /\
  u = update_var tmp w s /\ u1 = u with vs_inst_idx := ix /\ t = mstore b w u1 /\
  tn1 = step_taint i s u tn /\ tnf = step_taint j u1 t tn1 ==>
  tnf.t_mem SUBSET toplevel_copy_taint_bound loc a b tn 1
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `u.vs_allocas = s.vs_allocas /\ u.vs_fmp = s.vs_fmp` by
    simp[update_var_def] >>
  `MEM i.inst_opcode [ADD;MUL;ASSIGN;SLOAD;TLOAD]` by
    (Cases_on `loc = LocStorage` >> simp[mk_inst_def]) >>
  `tn1.t_mem = tn.t_mem` by metis_tac[toplevel_copy_register_taint_frame] >>
  `op_taint tn1 (Var tmp) = key_taint
     (if loc = LocStorage then tn.t_stor else tn.t_trans) a` by
    (Cases_on `loc = LocStorage` >>
     simp[step_taint_def, op_taint_def, out_taint_def, set_var_taint_def,
       mk_inst_def, FLOOKUP_UPDATE]) >>
  `eval_operand (Var dst) u1 = SOME (n2w b) /\
   eval_operand (Var tmp) u1 = SOME w` by
    (simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     gvs[lookup_var_def]) >>
  `new_site_bytes u1 t = {}` by
    (simp[new_site_bytes_def, mstore_def, EXTENSION, FLOOKUP_DEF] >> metis_tac[]) >>
  `range_bytes (step_writes j u1 t) = toplevel_copy_word_region b 0` by
    (simp[step_writes_def, source_memory_write_ranges_def,
      codegenRelTheory.fixed_source_write_range_def, mk_inst_def,
      range_bytes_def, toplevel_copy_word_region_def, EXTENSION] >>
     gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     decide_tac) >>
  `tnf.t_mem = (tn.t_mem DIFF toplevel_copy_word_region b 0) UNION
    toplevel_copy_word_taint loc a b tn 0` by
    (qpat_x_assum `j = _` SUBST_ALL_TAC >>
     `w2n (n2w b:256 word) = b+32*0` by simp[] >>
     drule_all toplevel_copy_mstore_taint >>
     disch_then (qspec_then `tn1` assume_tac) >>
     qpat_x_assum `tn1 = _` kall_tac >>
     gvs[toplevel_copy_word_taint_def, toplevel_copy_source_taint_def,
       key_taint_def, WORD_ADD_0] >> SET_TAC[]) >>
  `tn.t_mem SUBSET toplevel_copy_taint_bound loc a b tn 0` by simp[] >>
  drule_all toplevel_copy_store_taint_bound >> simp[]
QED

Theorem toplevel_copy_word_compiled_post_effects:
  do v <- emit_op (if loc = LocStorage then SLOAD else TLOAD) [src];
     emit_void MSTORE [Var dst;v] od sa = (out,sb) /\
  fn_has_code sa sb fn /\ (loc = LocStorage \/ loc = LocTransient) /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa dst /\
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  lookup_var dst s = SOME (n2w b) /\ ptr_covers G tn dst s cap /\
  32 <= cap /\ b+cap < 2**256 /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?r Gf tnf. gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK r) /\
    copy_prefix loc a b 1 s 1 r /\ copy_static r = copy_static s /\
    (!x. not_fresh_at sa x ==> lookup_var x r = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)) /\
    ptr_covers Gf tnf dst r cap /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    tnf.t_mem SUBSET toplevel_copy_taint_bound loc a b tn 1 /\
    ~r.vs_halted /\ r.vs_current_bb = sb.cs_current_bb /\
    r.vs_inst_idx = LENGTH sb.cs_current_insts /\
    LENGTH s.vs_memory <= LENGTH r.vs_memory
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule storage_copy_word_layout >> strip_tac >>
  qmatch_asmsub_abbrev_tac `emitted_insts sa sb =
    [mk_inst sa.cs_next_id opc [src] [tmp];
     mk_inst (sa.cs_next_id+1) MSTORE [Var dst;Var tmp] []]` >>
  qabbrev_tac `i = mk_inst sa.cs_next_id opc [src] [tmp]` >>
  qabbrev_tac `j = mk_inst (sa.cs_next_id+1) MSTORE [Var dst;Var tmp] []` >>
  qabbrev_tac `u = update_var tmp (copy_runtime_word loc s a) s` >>
  qabbrev_tac `u1 = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `t = mstore b (copy_runtime_word loc s a) u1` >>
  qabbrev_tac `r = t with vs_inst_idx := s.vs_inst_idx+2` >>
  qabbrev_tac `G1 = step_prov PG G i u` >>
  qabbrev_tac `tn1 = step_taint i s u tn` >>
  qabbrev_tac `Gf = step_prov PG G1 j t` >>
  qabbrev_tac `tnf = step_taint j u1 t tn1` >>
  `tmp <> dst` by metis_tac[] >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX [i;j] (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[fragExecTheory.fn_has_code_def, same_blocks_def, emitted_insts_def,
      IS_PREFIX_APPEND] >>
     qpat_x_assum `DROP _ _ = [i;j]` mp_tac >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
     disch_then SUBST1_TAC >> simp[]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK r)` by
    (qunabbrev_tac `r` >> irule toplevel_copy_word_path >>
     simp[] >> rpt (goal_assum (drule_at Any)) >>
     simp[Abbr `Gf`, Abbr `tnf`, Abbr `G1`, Abbr `tn1`, Abbr `i`, Abbr `j`,
       Abbr `opc`, Abbr `u`, Abbr `u1`, Abbr `t`] >>
     qexists_tac `sa.cs_next_id` >> gvs[]) >>
  suspend "post"
QED
Resume toplevel_copy_word_compiled_post_effects[post]:
  `!x. x <> tmp ==> lookup_var x r = lookup_var x s /\
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm` by
    (gen_tac >> disch_tac >>
     `i = mk_inst sa.cs_next_id (if loc = LocStorage then SLOAD else TLOAD) [src] [tmp]` by
       simp[Abbr `i`, Abbr `opc`] >>
     rule_assum_tac (PURE_REWRITE_RULE[markerTheory.Abbrev_def]) >>
     drule_all toplevel_copy_word_frame >> simp[]) >>
  `copy_prefix loc a b 1 s 1 r /\ copy_static r = copy_static s` by
    (irule toplevel_copy_word_content >>
     qexistsl_tac [`s.vs_inst_idx+2`, `tmp`] >>
     simp[Abbr `r`, Abbr `t`, Abbr `u1`, Abbr `u`, mstore_def]) >>
  `ptr_covers Gf tnf dst r cap` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  `b < dimword (:256)` by gvs[dimword_def] >>
  `tnf.t_mem SUBSET toplevel_copy_taint_bound loc a b tn 1` by
    (`i = mk_inst sa.cs_next_id (if loc = LocStorage then SLOAD else TLOAD) [src] [tmp]` by
       simp[Abbr `i`, Abbr `opc`] >>
     rule_assum_tac (PURE_REWRITE_RULE[markerTheory.Abbrev_def]) >>
     drule_all toplevel_copy_word_memory_taint >> simp[]) >>
  `LENGTH s.vs_memory <= LENGTH r.vs_memory` by
    simp[Abbr `r`, Abbr `t`, Abbr `u1`, Abbr `u`,
      venomMemPropsTheory.LENGTH_mstore_eq, update_var_def] >>
  qexistsl_tac [`r`, `Gf`, `tnf`] >> simp[] >>
  `tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm` by
    metis_tac[] >>
  simp[] >>
  simp[Abbr `r`, Abbr `t`, Abbr `u1`, Abbr `u`, mstore_def,
    update_var_def, same_blocks_def] >>
  qpat_x_assum `emitted_insts sa sb = _` mp_tac >>
  qpat_x_assum `isPREFIX sa.cs_current_insts sb.cs_current_insts` mp_tac >>
  qpat_x_assum `same_blocks sa sb` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp[same_blocks_def, emitted_insts_def, IS_PREFIX_APPEND] >>
  rpt strip_tac >> gvs[DROP_LENGTH_APPEND]
QED
Finalise toplevel_copy_word_compiled_post_effects

Theorem toplevel_copy_suffix_post_effects:
  (if n = 1 then
     do v <- emit_op (if loc = LocStorage then SLOAD else TLOAD) [src];
        emit_void MSTORE [Var dst;v] od
   else do compile_word_copy_loop src (Var dst) n loc LocMemory F;
           return () od) sa = (out,sb) /\
  fn_has_code sa sb fn /\ (loc = LocStorage \/ loc = LocTransient) /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa dst /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  lookup_var dst s = SOME (n2w b) /\ ptr_covers G tn dst s cap /\
  32*n <= cap /\ n < 2**256 /\ b+cap < 2**256 /\
  b+cap <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tnf. gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK t) /\
    copy_prefix loc a b n s n t /\ copy_static t = copy_static s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)) /\
    ptr_covers Gf tnf dst t cap /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    tnf.t_mem SUBSET toplevel_copy_taint_bound loc a b tn n /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `n = 1`
  >- (qpat_x_assum `n = 1` SUBST_ALL_TAC >> gnvs[] >>
      irule toplevel_copy_word_compiled_post_effects >>
      rpt (goal_assum (drule_at Any)) >> simp[] >>
      qexists_tac `src` >> simp[]) >>
  gnvs[] >>
  Cases_on `compile_word_copy_loop src (Var dst) n loc LocMemory F sa` >>
  gnvs[compileEnvTheory.comp_ignore_bind_def, compileEnvTheory.comp_bind_def,
    compileEnvTheory.comp_return_def] >>
  irule toplevel_copy_loop_post_effects >>
  rpt (goal_assum (drule_at Any)) >> simp[] >>
  qexists_tac `src` >> simp[]
QED

Theorem toplevel_copy_loop_post:
  compile_word_copy_loop src (Var dst) n loc LocMemory F sa = (u,sb) /\
  fn_has_code sa sb fn /\ (loc = LocStorage \/ loc = LocTransient) /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa dst /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  lookup_var dst s = SOME (n2w b) /\ ptr_covers G tn dst s cap /\
  32*n <= cap /\ n < 2**256 /\ b+cap < 2**256 /\
  b+cap <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tnf. gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK t) /\
    copy_prefix loc a b n s n t /\ copy_static t = copy_static s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)) /\
    ptr_covers Gf tnf dst t cap /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    tnf.t_mem SUBSET toplevel_copy_taint_bound loc a b tn n /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> drule_all toplevel_copy_loop_post_effects >> metis_tac[]
QED

Theorem toplevel_copy_word_compiled_post:
  do v <- emit_op (if loc = LocStorage then SLOAD else TLOAD) [src];
     emit_void MSTORE [Var dst;v] od sa = (out,sb) /\
  fn_has_code sa sb fn /\ (loc = LocStorage \/ loc = LocTransient) /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa dst /\
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  lookup_var dst s = SOME (n2w b) /\ ptr_covers G tn dst s cap /\
  32 <= cap /\ b+cap < 2**256 /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?r Gf tnf. gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK r) /\
    copy_prefix loc a b 1 s 1 r /\ copy_static r = copy_static s /\
    (!x. not_fresh_at sa x ==> lookup_var x r = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)) /\
    ptr_covers Gf tnf dst r cap /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    tnf.t_mem SUBSET toplevel_copy_taint_bound loc a b tn 1 /\
    ~r.vs_halted /\ r.vs_current_bb = sb.cs_current_bb /\
    r.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> drule_all toplevel_copy_word_compiled_post_effects >> metis_tac[]
QED

Theorem toplevel_copy_suffix_post:
  (if n = 1 then
     do v <- emit_op (if loc = LocStorage then SLOAD else TLOAD) [src];
        emit_void MSTORE [Var dst;v] od
   else do compile_word_copy_loop src (Var dst) n loc LocMemory F;
           return () od) sa = (out,sb) /\
  fn_has_code sa sb fn /\ (loc = LocStorage \/ loc = LocTransient) /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa dst /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  lookup_var dst s = SOME (n2w b) /\ ptr_covers G tn dst s cap /\
  32*n <= cap /\ n < 2**256 /\ b+cap < 2**256 /\
  b+cap <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tnf. gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK t) /\
    copy_prefix loc a b n s n t /\ copy_static t = copy_static s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)) /\
    ptr_covers Gf tnf dst t cap /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    tnf.t_mem SUBSET toplevel_copy_taint_bound loc a b tn n /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> drule_all toplevel_copy_suffix_post_effects >> metis_tac[]
QED

Theory bodyPtrPrecompileBuiltinsRecoveryFrame
Ancestors bodyPtrPrecompileBuiltinsCompletePrefixes
          bodyPtrPrecompileBuiltinsRecoveryRun
          bodyPtrPrecompileBuiltinsCompilerStages
          bodyPtrPrecompileBuiltinsRunAllocation
          bodyPtrPrecompileBuiltinsPrefixFrames
          bodyPtrDefs compileEnv exprLoweringProps venomState finite_map pred_set list

Theorem recovery_payload_ranges:
  emit_void MSTORE [buf; h] sa = ((),sb) /\
  (do dst <- emit_op ADD [buf; Lit 32w];
      emit_void MSTORE [dst; v] od) sb = ((),sc) /\
  (do dst <- emit_op ADD [buf; Lit 64w];
      emit_void MSTORE [dst; r] od) sc = ((),sd) /\
  (do dst <- emit_op ADD [buf; Lit 96w];
      emit_void MSTORE [dst; q] od) sd = ((),sp) ==>
  emitted_insts sa sp = emitted_insts sa sb ++ emitted_insts sb sc ++
    emitted_insts sc sd ++ emitted_insts sd sp
Proof
  strip_tac >>
  imp_res_tac direct_store_compiler_shape >>
  imp_res_tac offset_store_compiler_shape >>
  imp_res_tac compiler_append_trans >> simp[APPEND_ASSOC] >> metis_tac[]
QED

Theorem recovery_prefix_ghost_kept:
  compile_alloc_buffer 128 sf = (ib,sa) /\
  compile_alloc_buffer 32 sp = (ob,sm) /\
  run_inst_seq (emitted_insts sf sa) s0 = OK s1 /\
  run_inst_seq (emitted_insts sp sm) s2 = OK s3 /\
  stmt_state_rel ctx fn cenv cx es s0 /\
  stmt_state_rel ctx fn cenv cx es s2 /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sf /\ local_ptrs_reserved cenv sp /\
  local_ptrs_rel fn cenv es.scopes s0 /\ local_ptrs_rel fn cenv es.scopes s2 /\
  MEM (mk_inst sf.cs_next_id ALLOCA [Lit 128w]
    [STRING #"%" (toString sf.cs_next_var)]) (fn_insts fn) /\
  s2.vs_allocas = s1.vs_allocas /\
  (!p. not_fresh_at sf p ==> lookup_var p s2 = lookup_var p s0) /\
  (!p. not_fresh_at sf p ==> FLOOKUP Gf p = FLOOKUP G p /\
    op_taint tnf (Var p) = op_taint tn (Var p)) /\
  tnf.t_mem = (((tn.t_mem UNION new_site_bytes s0 s1) DIFF writes1)
    UNION new_site_bytes s2 s3) DIFF writes2 ==>
  ghost_kept cenv es sf G tn s0 Gf tnf
Proof
  strip_tac >>
  `128 < dimword(:256)` by simp[wordsTheory.dimword_def] >>
  qpat_assum `stmt_state_rel ctx fn cenv cx es s0`
    (mp_then Any (drule_all_then strip_assume_tac)
      exprSimLiteralBufferTheory.alloc_buffer_frame_run) >>
  gvs[] >>
  `alloca_next_valid s0 /\ alloca_next_valid s2` by
    gvs[stmt_state_rel_def, venomMemDefsTheory.alloca_inv_def] >>
  `!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
    off <= i /\ i < off + sz ==>
    i NOTIN new_site_bytes s0 s1 /\ i NOTIN new_site_bytes s2 s3` by
    (rpt gen_tac >> strip_tac >>
     `FLOOKUP s2.vs_allocas aid = SOME (off,sz)` by metis_tac[] >>
     conj_tac
     >- (irule emitted_allocation_old_region_exterior >>
         simp[] >> conj_tac
         >- (qexistsl [`aid`,`sz`,`off`] >> simp[]) >>
         qexistsl [`ib`,`128`,`sf`,`sa`] >> simp[]) >>
     irule emitted_allocation_old_region_exterior >> simp[] >> conj_tac
     >- (qexistsl [`aid`,`sz`,`off`] >> simp[]) >>
     qexistsl [`ob`,`32`,`sp`,`sm`] >> simp[]) >>
  `!n b sz i. local_region cenv es.scopes s0 n b sz /\
    b <= i /\ i < b + sz ==>
    i NOTIN new_site_bytes s0 s1 /\ i NOTIN new_site_bytes s2 s3` by
    (rpt gen_tac >> strip_tac >>
     `local_region cenv es.scopes s2 n b sz` by
       (irule exprSimPropsTheory.local_region_frame_fwd >>
        goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
     qpat_assum `run_inst_seq (emitted_insts sf sa) s0 = OK s1`
       (mp_then Any (drule_all_then strip_assume_tac) emitted_allocation_step) >>
     qpat_assum `run_inst_seq (emitted_insts sp sm) s2 = OK s3`
       (mp_then Any (drule_all_then strip_assume_tac) emitted_allocation_step) >>
     conj_tac
     >- (qpat_assum `step_inst_base _ s0 = OK s1`
           (mp_then Any mp_tac local_region_allocation_growth_disjoint) >>
         simp[venomInstTheory.mk_inst_def] >> disch_then drule_all >>
         simp[DISJOINT_ALT] >> metis_tac[]) >>
     qpat_assum `step_inst_base _ s2 = OK s3`
       (mp_then Any mp_tac local_region_allocation_growth_disjoint) >>
     simp[venomInstTheory.mk_inst_def] >> disch_then drule_all >>
     simp[DISJOINT_ALT] >> metis_tac[]) >>
  simp[ghost_kept_def] >> rpt conj_tac >> rpt strip_tac >>
  gvs[IN_DIFF, IN_UNION] >> metis_tac[]
QED

Theorem recovery_prefix_ghost_inv:
  compile_alloc_buffer 128 sf = (ib,sa) /\
  compile_alloc_buffer 32 sp = (ob,sm) /\
  run_inst_seq (emitted_insts sf sa) s0 = OK s1 /\
  run_inst_seq (emitted_insts sp sm) s2 = OK s3 /\
  stmt_state_rel ctx fn cenv cx es s0 /\
  stmt_state_rel ctx fn cenv cx es s2 /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sf /\ local_ptrs_reserved cenv sp /\
  local_ptrs_rel fn cenv es.scopes s0 /\ local_ptrs_rel fn cenv es.scopes s2 /\
  MEM (mk_inst sf.cs_next_id ALLOCA [Lit 128w]
    [STRING #"%" (toString sf.cs_next_var)]) (fn_insts fn) /\
  MEM (mk_inst sp.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString sp.cs_next_var)]) (fn_insts fn) /\
  eval_operand ib.buf_operand s1 = SOME b /\
  eval_operand ob.buf_operand s3 = SOME c /\
  ghost_inv d cenv cx es G tn s0 /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sf p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sf p) /\
  (!p. not_fresh_at sf p ==> lookup_var p s2 = lookup_var p s0) /\
  (!p. not_fresh_at sf p ==> lookup_var p s4 = lookup_var p s0 /\
    FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p)) /\
  (!i. ~(w2n b <= i /\ i < w2n b + 128) /\
       ~(w2n c <= i /\ i < w2n c + 32) ==>
    mem_bytes_at i 1 s4.vs_memory = mem_bytes_at i 1 s0.vs_memory) /\
  tnf.t_mem = (((tn.t_mem UNION new_site_bytes s0 s1) DIFF
    {i | w2n b <= i /\ i < w2n b + 128}) UNION new_site_bytes s2 s3) DIFF
    {i | w2n c <= i /\ i < w2n c + 32} /\
  EVERY (\i. i.inst_opcode = ALLOCA \/ i.inst_opcode = ADD \/
    i.inst_opcode = MLOAD \/ i.inst_opcode = MSTORE) code /\
  run_inst_seq code s0 = OK s4 /\
  (!k. inst_seq_ptr D 0 ctx fn PG G tn code
    (s0 with vs_inst_idx := k) Gf tnf) ==>
  ghost_inv d cenv cx es Gf tnf s4
Proof
  strip_tac >>
  `128 < dimword(:256) /\ 32 < dimword(:256)` by
    simp[wordsTheory.dimword_def] >>
  `!name entry p sz w.
    lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
    lookup_var p s0 = SOME w ==>
    val_wf entry.type entry.value /\
    (!i. w2n w <= i /\ i < w2n w + val_footprint entry.type entry.value ==>
      i NOTIN (new_site_bytes s0 s1 UNION new_site_bytes s2 s3 UNION
        {j | w2n b <= j /\ j < w2n b + 128} UNION
        {j | w2n c <= j /\ j < w2n c + 32}))` by
    (mp_tac (Q.INST [`insz` |-> `128`, `outsz` |-> `32`, `zero_len` |-> `32`]
       complete_prefix_scope_exterior |>
       SIMP_RULE (srw_ss()) [wordsTheory.dimword_def]) >> simp[]) >>
  drule_all staging_prefix_nonmemory_frames >> strip_tac >>
  irule complete_prefix_ghost_frame >>
  qexistsl [`G`,`new_site_bytes s0 s1`,`new_site_bytes s2 s3`,`s0`,`tn`,
    `{i | w2n b <= i /\ i < w2n b + 128}`,
    `{i | w2n c <= i /\ i < w2n c + 32}`] >>
  simp[IN_UNION] >> conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sf p` by (gvs[local_ptrs_reserved_def] >> metis_tac[]) >>
      qpat_assum `!p. not_fresh_at sf p ==> _ /\ _ /\ _`
        (qspec_then `p` mp_tac) >> simp[]) >>
  rpt strip_tac >>
  qpat_assum `!name entry p sz w. _` (drule_all_then strip_assume_tac) >>
  gvs[IN_UNION] >> metis_tac[]
QED

Theorem recovery_prefix_framed:
  compile_alloc_buffer 128 sf = (ib,sa) /\ ib.buf_operand = Var bufroot /\
  emit_void MSTORE [Var bufroot; h] sa = ((),sb) /\
  (do dst <- emit_op ADD [Var bufroot; Lit 32w];
      emit_void MSTORE [dst; v] od) sb = ((),sc) /\
  (do dst <- emit_op ADD [Var bufroot; Lit 64w];
      emit_void MSTORE [dst; r] od) sc = ((),sd) /\
  (do dst <- emit_op ADD [Var bufroot; Lit 96w];
      emit_void MSTORE [dst; q] od) sd = ((),sp) /\
  compile_alloc_buffer 32 sp = (ob,sm) /\ ob.buf_operand = Var out /\
  emit_void MSTORE [Var out; Lit 0w] sm = ((),sz) /\
  run_inst_seq (emitted_insts sf sa) s0 = OK s1 /\
  run_inst_seq (emitted_insts sa sp) s1 = OK s2 /\
  run_inst_seq (emitted_insts sp sm) s2 = OK s3 /\
  run_inst_seq (emitted_insts sm sz) s3 = OK s4 /\
  stmt_state_rel ctx fn cenv cx es s0 /\ stmt_state_rel ctx fn cenv cx es s2 /\
  fn_inst_ids_distinct fn /\ ~ctx_has_dalloca ctx /\
  local_ptrs_reserved cenv sf /\ local_ptrs_reserved cenv sp /\
  local_ptrs_rel fn cenv es.scopes s0 /\ local_ptrs_rel fn cenv es.scopes s2 /\
  MEM (mk_inst sf.cs_next_id ALLOCA [Lit 128w]
    [STRING #"%" (toString sf.cs_next_var)]) (fn_insts fn) /\
  MEM (mk_inst sp.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString sp.cs_next_var)]) (fn_insts fn) /\
  ghost_inv d cenv cx es G tn s0 /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sf p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sf p) /\
  eval_operand h s0 = SOME wh /\ eval_operand v s0 = SOME wv /\
  eval_operand r s0 = SOME wr /\ eval_operand q s0 = SOME wq /\
  EVERY (\x. op_taint tn x = {} /\ (!l. x <> Label l) /\
    (!p. x = Var p ==> not_fresh_at sf p)) [h;v;r;q] /\
  eval_operand ib.buf_operand s1 = SOME b /\ w2n b + 128 < dimword(:256) /\
  eval_operand ob.buf_operand s3 = SOME c /\ w2n c + 32 < dimword(:256) /\
  s2.vs_allocas = s1.vs_allocas /\
  (!p. not_fresh_at sf p ==> lookup_var p s2 = lookup_var p s0) ==>
  ?Gf tnf.
    (!k. inst_seq_ptr D 0 ctx fn PG G tn
      (emitted_insts sf sa ++ emitted_insts sa sp ++
       emitted_insts sp sm ++ emitted_insts sm sz)
      (s0 with vs_inst_idx := k) Gf tnf) /\
    ptr_covers Gf tnf bufroot s4 128 /\ ptr_covers Gf tnf out s4 32 /\
    lookup_var bufroot s4 = SOME b /\ lookup_var out s4 = SOME c /\
    (!i. w2n b <= i /\ i < w2n b + 128 ==> i NOTIN tnf.t_mem) /\
    (!i. w2n c <= i /\ i < w2n c + 32 ==> i NOTIN tnf.t_mem) /\
    ghost_inv d cenv cx es Gf tnf s4 /\ ghost_kept cenv es sf G tn s0 Gf tnf
Proof
  strip_tac >>
  `emitted_insts sa sp = emitted_insts sa sb ++ emitted_insts sb sc ++
    emitted_insts sc sd ++ emitted_insts sd sp` by
    (irule recovery_payload_ranges >> qexistsl [`Var bufroot`,`h`,`q`,`r`,`v`] >> simp[]) >>
  `128 < dimword(:256)` by simp[wordsTheory.dimword_def] >>
  qpat_assum `stmt_state_rel ctx fn cenv cx es s0`
    (mp_then Any (drule_all_then strip_assume_tac)
      exprSimLiteralBufferTheory.alloc_buffer_frame_run) >> gvs[] >>
  `alloca_next_valid s2` by
    gvs[stmt_state_rel_def, venomMemDefsTheory.alloca_inv_def] >>
  `!i. w2n b <= i /\ i < w2n b + 128 ==> i NOTIN new_site_bytes s2 s3` by
    (rpt gen_tac >> strip_tac >>
     irule emitted_allocation_old_region_exterior >> simp[] >> conj_tac
     >- (qexistsl [`sf.cs_next_id`,`128`,`w2n b`] >> simp[]) >>
     qexistsl [`ob`,`32`,`sp`,`sm`] >> simp[]) >>
  mp_tac recovery_complete_prefix_checked >> simp[] >>
  disch_then (qx_choose_then `Gf` (qx_choose_then `tnf` strip_assume_tac)) >>
  suspend "frame"
QED

Resume recovery_prefix_framed[frame]:
  qmatch_asmsub_abbrev_tac `inst_seq_ptr D 0 ctx fn PG G tn code _ Gf tnf` >>
  `run_inst_seq code s0 = OK s4` by
    (simp[Abbr `code`] >>
     qpat_assum `run_inst_seq (emitted_insts sf sa) s0 = OK s1` mp_tac >>
     qpat_assum `run_inst_seq _ s1 = OK s2` mp_tac >>
     qpat_assum `run_inst_seq (emitted_insts sp sm) s2 = OK s3` mp_tac >>
     qpat_assum `run_inst_seq (emitted_insts sm sz) s3 = OK s4` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     rpt strip_tac >>
     `run_inst_seq (emitted_insts sf sa ++
       ((emitted_insts sa sb ++ emitted_insts sb sc ++
         emitted_insts sc sd ++ emitted_insts sd sp) ++
        (emitted_insts sp sm ++ emitted_insts sm sz))) s0 = OK s4`
       suffices_by simp[APPEND_ASSOC] >>
     imp_res_tac run_inst_seq_append >> asm_rewrite_tac[]) >>
  `EVERY (\i. i.inst_opcode = ALLOCA \/ i.inst_opcode = ADD \/
    i.inst_opcode = MLOAD \/ i.inst_opcode = MSTORE) code` by
    simp[Abbr `code`] >>
  `ghost_inv d cenv cx es Gf tnf s4` by
    (mp_tac recovery_prefix_ghost_inv >> simp[] >>
     (impl_tac >- (rpt strip_tac >> first_x_assum irule >> simp[])) >> simp[]) >>
  `ghost_kept cenv es sf G tn s0 Gf tnf` by
    (mp_tac (Q.INST [
       `writes1` |-> `{i | w2n (b:256 word) <= i /\ i < w2n b + 128}`,
       `writes2` |-> `{i | w2n (c:256 word) <= i /\ i < w2n c + 32}`]
       (INST_TYPE [alpha |-> ``:num # num``] recovery_prefix_ghost_kept)) >>
     simp[] >> (impl_tac >- (rpt strip_tac >> first_x_assum drule >> simp[])) >> simp[]) >>
  qexistsl [`Gf`,`tnf`] >> simp[Abbr `code`]
QED

Finalise recovery_prefix_framed

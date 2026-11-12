Theory bodyPtrPrecompileBuiltinsArithmeticPrefix
Ancestors bodyPtrPrecompileBuiltinsArithmeticRun
          bodyPtrPrecompileBuiltinsCompletePrefixes
          bodyPtrPrecompileBuiltinsRunAllocation
          bodyPtrPrecompileBuiltinsPrefixFrames
          bodyPtrDefs compileEnv loweringStateRelDefs exprLoweringProps venomState finite_map pred_set list

(* Arithmetic leaves the output allocation uninitialized. Only the input
   range is cleared from memory taint before the precompile call. *)
Theorem arithmetic_prefix_ghost_inv:
  compile_alloc_buffer insz sf = (ib,sa) /\
  compile_alloc_buffer 64 sp = (ob,sm) /\
  run_inst_seq (emitted_insts sf sa) s0 = OK s1 /\
  run_inst_seq (emitted_insts sp sm) s2 = OK s3 /\
  stmt_state_rel ctx fn cenv cx es s0 /\
  stmt_state_rel ctx fn cenv cx es s2 /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sf /\ local_ptrs_reserved cenv sp /\
  local_ptrs_rel fn cenv es.scopes s0 /\ local_ptrs_rel fn cenv es.scopes s2 /\
  insz < dimword(:256) /\
  MEM (mk_inst sf.cs_next_id ALLOCA [Lit (n2w insz)]
    [STRING #"%" (toString sf.cs_next_var)]) (fn_insts fn) /\
  MEM (mk_inst sp.cs_next_id ALLOCA [Lit 64w]
    [STRING #"%" (toString sp.cs_next_var)]) (fn_insts fn) /\
  eval_operand ib.buf_operand s1 = SOME b /\
  eval_operand ob.buf_operand s3 = SOME c /\
  ghost_inv d cenv cx es G tn s0 /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sf p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sf p) /\
  (!p. not_fresh_at sf p ==> lookup_var p s2 = lookup_var p s0) /\
  (!p. not_fresh_at sf p ==> lookup_var p s3 = lookup_var p s0 /\
    FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p)) /\
  (!i. ~(w2n b <= i /\ i < w2n b + insz) ==>
    mem_bytes_at i 1 s3.vs_memory = mem_bytes_at i 1 s0.vs_memory) /\
  tnf.t_mem = ((tn.t_mem UNION new_site_bytes s0 s1) DIFF
    {i | w2n b <= i /\ i < w2n b + insz}) UNION new_site_bytes s2 s3 /\
  EVERY (\i. i.inst_opcode = ALLOCA \/ i.inst_opcode = ADD \/
    i.inst_opcode = MLOAD \/ i.inst_opcode = MSTORE) code /\
  run_inst_seq code s0 = OK s3 /\
  (!k. inst_seq_ptr D 0 ctx fn PG G tn code
    (s0 with vs_inst_idx := k) Gf tnf) ==>
  ghost_inv d cenv cx es Gf tnf s3
Proof
  strip_tac >>
  `!name entry p sz w.
    lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
    lookup_var p s0 = SOME w ==>
    val_wf entry.type entry.value /\
    (!i. w2n w <= i /\ i < w2n w + val_footprint entry.type entry.value ==>
      i NOTIN (new_site_bytes s0 s1 UNION new_site_bytes s2 s3 UNION
        {j | w2n b <= j /\ j < w2n b + insz}))` by
    (mp_tac (Q.INST [`outsz` |-> `64`, `zero_len` |-> `0`]
       complete_prefix_scope_exterior |>
       SIMP_RULE (srw_ss()) []) >> simp[wordsTheory.dimword_def] >>
     fs[wordsTheory.dimword_def]) >>
  drule_all staging_prefix_nonmemory_frames >> strip_tac >>
  irule complete_prefix_ghost_frame >>
  qexistsl [`G`,`new_site_bytes s0 s1`,`new_site_bytes s2 s3`,`s0`,`tn`,
    `{i | w2n b <= i /\ i < w2n b + insz}`,`{} `] >>
  simp[IN_UNION] >> conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sf p` by (gvs[local_ptrs_reserved_def] >> metis_tac[]) >>
      qpat_assum `!p. not_fresh_at sf p ==> _ /\ _ /\ _`
        (qspec_then `p` mp_tac) >> simp[]) >>
  rpt strip_tac >>
  qpat_assum `!name entry p sz w. _` (drule_all_then strip_assume_tac) >>
  gvs[IN_UNION] >> metis_tac[]
QED

Theorem allocated_prefix_ghost_kept:
  compile_alloc_buffer insz sf = (ib,sa) /\
  compile_alloc_buffer outsz sp = (ob,sm) /\
  run_inst_seq (emitted_insts sf sa) s0 = OK s1 /\
  run_inst_seq (emitted_insts sp sm) s2 = OK s3 /\
  stmt_state_rel ctx fn cenv cx es s0 /\
  stmt_state_rel ctx fn cenv cx es s2 /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sf /\ local_ptrs_reserved cenv sp /\
  local_ptrs_rel fn cenv es.scopes s0 /\ local_ptrs_rel fn cenv es.scopes s2 /\
  insz < dimword(:256) /\
  MEM (mk_inst sf.cs_next_id ALLOCA [Lit (n2w insz)]
    [STRING #"%" (toString sf.cs_next_var)]) (fn_insts fn) /\
  s2.vs_allocas = s1.vs_allocas /\
  (!p. not_fresh_at sf p ==> lookup_var p s2 = lookup_var p s0) /\
  (!p. not_fresh_at sf p ==> FLOOKUP Gf p = FLOOKUP G p /\
    op_taint tnf (Var p) = op_taint tn (Var p)) /\
  tnf.t_mem SUBSET (tn.t_mem UNION new_site_bytes s0 s1 UNION new_site_bytes s2 s3) ==>
  ghost_kept cenv es sf G tn s0 Gf tnf
Proof
  strip_tac >>
  qpat_assum `stmt_state_rel ctx fn cenv cx es s0`
    (mp_then Any (drule_all_then strip_assume_tac)
      exprSimLiteralBufferTheory.alloc_buffer_frame_run) >> gvs[] >>
  `alloca_next_valid s0 /\ alloca_next_valid s2` by
    gvs[stmt_state_rel_def, venomMemDefsTheory.alloca_inv_def] >>
  `!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
    off <= i /\ i < off + sz ==>
    i NOTIN new_site_bytes s0 s1 /\ i NOTIN new_site_bytes s2 s3` by
    (rpt gen_tac >> strip_tac >>
     `FLOOKUP s2.vs_allocas aid = SOME (off,sz)` by metis_tac[] >>
     conj_tac
     >- (irule emitted_allocation_old_region_exterior >> simp[] >> conj_tac
         >- (qexistsl [`aid`,`sz`,`off`] >> simp[]) >>
         qexistsl [`ib`,`insz`,`sf`,`sa`] >> simp[]) >>
     irule emitted_allocation_old_region_exterior >> simp[] >> conj_tac
     >- (qexistsl [`aid`,`sz`,`off`] >> simp[]) >>
     qexistsl [`ob`,`outsz`,`sp`,`sm`] >> simp[]) >>
  suspend "locals"
QED

Resume allocated_prefix_ghost_kept[locals]:
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
  gvs[SUBSET_DEF, IN_UNION] >> metis_tac[]
QED
Finalise allocated_prefix_ghost_kept

Theorem ecmul_prefix_framed:
  compile_alloc_buffer 96 sf = (ib,sa) /\ ib.buf_operand = Var bufroot /\
  (do src <- emit_op ADD [Var root; Lit 0w]; value <- emit_op MLOAD [src];
      dst <- emit_op ADD [Var bufroot; Lit 0w]; emit_void MSTORE [dst; value] od)
    sa = ((),sb) /\
  (do src <- emit_op ADD [Var root; Lit 32w]; value <- emit_op MLOAD [src];
      dst <- emit_op ADD [Var bufroot; Lit 32w]; emit_void MSTORE [dst; value] od)
    sb = ((),sc) /\
  (do dst <- emit_op ADD [Var bufroot; Lit 64w];
      emit_void MSTORE [dst; scalar] od) sc = ((),sp) /\
  compile_alloc_buffer 64 sp = (ob,sm) /\
  run_inst_seq (emitted_insts sf sa) s0 = OK s1 /\
  run_inst_seq (emitted_insts sa sb ++ emitted_insts sb sc ++ emitted_insts sc sp)
    s1 = OK s2 /\
  run_inst_seq (emitted_insts sp sm) s2 = OK s3 /\
  stmt_state_rel ctx fn cenv cx es s0 /\ stmt_state_rel ctx fn cenv cx es s2 /\
  fn_inst_ids_distinct fn /\ ~ctx_has_dalloca ctx /\
  local_ptrs_reserved cenv sf /\ local_ptrs_reserved cenv sp /\
  local_ptrs_rel fn cenv es.scopes s0 /\ local_ptrs_rel fn cenv es.scopes s2 /\
  MEM (mk_inst sf.cs_next_id ALLOCA [Lit 96w]
    [STRING #"%" (toString sf.cs_next_var)]) (fn_insts fn) /\
  MEM (mk_inst sp.cs_next_id ALLOCA [Lit 64w]
    [STRING #"%" (toString sp.cs_next_var)]) (fn_insts fn) /\
  ghost_inv d cenv cx es G tn s0 /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sf p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sf p) /\
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo sf es v (Var root) s0 /\
  ptr_covers G tn root s0 64 /\ lookup_var root s0 = SOME a /\
  w2n a + 64 < dimword(:256) /\
  (!i. w2n a <= i /\ i < w2n a + 64 ==> i NOTIN tn.t_mem) /\
  eval_operand scalar s0 = SOME w /\ op_taint tn scalar = {} /\
  (!l. scalar <> Label l) /\ (!p. scalar = Var p ==> not_fresh_at sf p) /\
  not_fresh_at sf root /\ eval_operand ib.buf_operand s1 = SOME b /\
  eval_operand ob.buf_operand s3 = SOME c /\ w2n b + 96 < dimword(:256) /\
  s2.vs_allocas = s1.vs_allocas /\
  (!p. not_fresh_at sf p ==> lookup_var p s2 = lookup_var p s0) ==>
  ?out Gf tnf.
    ob.buf_operand = Var out /\
    (!k. inst_seq_ptr D 0 ctx fn PG G tn
      (emitted_insts sf sa ++
       (emitted_insts sa sb ++ emitted_insts sb sc ++ emitted_insts sc sp) ++
       emitted_insts sp sm) (s0 with vs_inst_idx := k) Gf tnf) /\
    EVERY (\i. i.inst_opcode = ALLOCA \/ i.inst_opcode = ADD \/
      i.inst_opcode = MLOAD \/ i.inst_opcode = MSTORE)
      (emitted_insts sf sa ++ emitted_insts sa sb ++ emitted_insts sb sc ++
       emitted_insts sc sp ++ emitted_insts sp sm) /\
    ptr_covers Gf tnf bufroot s3 96 /\ ptr_covers Gf tnf out s3 64 /\
    lookup_var bufroot s3 = SOME b /\
    (!i. w2n b <= i /\ i < w2n b + 96 ==> i NOTIN tnf.t_mem) /\
    tnf.t_mem = ((tn.t_mem UNION new_site_bytes s0 s1) DIFF
      {i | w2n b <= i /\ i < w2n b + 96}) UNION new_site_bytes s2 s3 /\
    (!p. not_fresh_at sf p ==> lookup_var p s3 = lookup_var p s0 /\
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p)) /\
    ghost_inv d cenv cx es Gf tnf s3 /\ ghost_kept cenv es sf G tn s0 Gf tnf
Proof
  strip_tac >>
  `96 < dimword(:256)` by simp[wordsTheory.dimword_def] >>
  `!i. w2n a <= i /\ i < w2n a + 64 ==> i NOTIN new_site_bytes s0 s1` by
    (rpt strip_tac >>
     `eval_operand (Var root) s0 = SOME a` by simp[venomStateTheory.eval_operand_def] >>
     qpat_assum `compile_alloc_buffer 96 sf = _`
       (mp_then Any mp_tac emitted_allocation_point_exterior) >>
     disch_then drule_all >> simp[]) >>
  qpat_assum `stmt_state_rel ctx fn cenv cx es s0`
    (mp_then Any (drule_all_then strip_assume_tac)
      exprSimLiteralBufferTheory.alloc_buffer_frame_run) >> gvs[] >>
  `alloca_next_valid s2` by
    gvs[stmt_state_rel_def, venomMemDefsTheory.alloca_inv_def] >>
  `!i. w2n b <= i /\ i < w2n b + 96 ==> i NOTIN new_site_bytes s2 s3` by
    (rpt gen_tac >> strip_tac >>
     irule emitted_allocation_old_region_exterior >> simp[] >> conj_tac
     >- (qexistsl [`sf.cs_next_id`,`96`,`w2n b`] >> simp[]) >>
     qexistsl [`ob`,`64`,`sp`,`sm`] >> simp[]) >>
  mp_tac ecmul_complete_prefix_checked >> simp[] >>
  disch_then (qx_choose_then `out` (qx_choose_then `Gf`
    (qx_choose_then `tnf` strip_assume_tac))) >>
  suspend "frame"
QED

Resume ecmul_prefix_framed[frame]:
  qmatch_asmsub_abbrev_tac `inst_seq_ptr D 0 ctx fn PG G tn code _ Gf tnf` >>
  `run_inst_seq code s0 = OK s3` by
    (simp[Abbr `code`] >>
     qpat_assum `run_inst_seq (emitted_insts sf sa) s0 = OK s1` mp_tac >>
     qpat_assum `run_inst_seq _ s1 = OK s2` mp_tac >>
     qpat_assum `run_inst_seq (emitted_insts sp sm) s2 = OK s3` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     `run_inst_seq (emitted_insts sf sa ++
       ((emitted_insts sa sb ++ emitted_insts sb sc ++ emitted_insts sc sp) ++
         emitted_insts sp sm)) s0 = OK s3` suffices_by simp[listTheory.APPEND_ASSOC] >>
     imp_res_tac exprLoweringPropsTheory.run_inst_seq_append >> asm_rewrite_tac[]) >>
  `EVERY (\i. i.inst_opcode = ALLOCA \/ i.inst_opcode = ADD \/
    i.inst_opcode = MLOAD \/ i.inst_opcode = MSTORE) code` by
    simp[Abbr `code`] >>
  `ghost_inv d cenv cx es Gf tnf s3` by
    (mp_tac (Q.INST [`insz` |-> `96`] arithmetic_prefix_ghost_inv) >> simp[] >>
     (impl_tac >- (rpt strip_tac >> first_x_assum irule >> simp[])) >> simp[]) >>
  `tnf.t_mem SUBSET (tn.t_mem UNION new_site_bytes s0 s1 UNION new_site_bytes s2 s3)` by
    (gvs[SUBSET_DEF, IN_UNION, IN_DIFF] >> metis_tac[]) >>
  `ghost_kept cenv es sf G tn s0 Gf tnf` by
    (mp_tac (Q.INST [`insz` |-> `96`, `outsz` |-> `64`]
       (INST_TYPE [alpha |-> ``:num # num``] allocated_prefix_ghost_kept)) >> simp[] >>
     (impl_tac >- (rpt strip_tac >> first_x_assum drule >> simp[])) >> simp[]) >>
  qexistsl [`out`,`Gf`,`tnf`] >> simp[Abbr `code`]
QED
Finalise ecmul_prefix_framed

Theorem ecadd_prefix_framed:
  compile_alloc_buffer 128 sf = (ib,sa) /\ ib.buf_operand = Var bufroot /\
  (do src <- emit_op ADD [Var root1; Lit 0w]; value <- emit_op MLOAD [src];
      dst <- emit_op ADD [Var bufroot; Lit 0w]; emit_void MSTORE [dst; value] od)
    sa = ((),sb) /\
  (do src <- emit_op ADD [Var root1; Lit 32w]; value <- emit_op MLOAD [src];
      dst <- emit_op ADD [Var bufroot; Lit 32w]; emit_void MSTORE [dst; value] od)
    sb = ((),sc) /\
  (do src <- emit_op ADD [Var root2; Lit 0w]; value <- emit_op MLOAD [src];
      dst <- emit_op ADD [Var bufroot; Lit 64w]; emit_void MSTORE [dst; value] od)
    sc = ((),sd) /\
  (do src <- emit_op ADD [Var root2; Lit 32w]; value <- emit_op MLOAD [src];
      dst <- emit_op ADD [Var bufroot; Lit 96w]; emit_void MSTORE [dst; value] od)
    sd = ((),sp) /\
  compile_alloc_buffer 64 sp = (ob,sm) /\
  run_inst_seq (emitted_insts sf sa) s0 = OK s1 /\
  run_inst_seq (emitted_insts sa sb ++ emitted_insts sb sc ++
    emitted_insts sc sd ++ emitted_insts sd sp) s1 = OK s2 /\
  run_inst_seq (emitted_insts sp sm) s2 = OK s3 /\
  stmt_state_rel ctx fn cenv cx es s0 /\ stmt_state_rel ctx fn cenv cx es s2 /\
  fn_inst_ids_distinct fn /\ ~ctx_has_dalloca ctx /\
  local_ptrs_reserved cenv sf /\ local_ptrs_reserved cenv sp /\
  local_ptrs_rel fn cenv es.scopes s0 /\ local_ptrs_rel fn cenv es.scopes s2 /\
  MEM (mk_inst sf.cs_next_id ALLOCA [Lit 128w]
    [STRING #"%" (toString sf.cs_next_var)]) (fn_insts fn) /\
  MEM (mk_inst sp.cs_next_id ALLOCA [Lit 64w]
    [STRING #"%" (toString sp.cs_next_var)]) (fn_insts fn) /\
  ghost_inv d cenv cx es G tn s0 /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sf p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sf p) /\
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo sf es vp (Var root1) s0 /\
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo sf es vq (Var root2) s0 /\
  ptr_covers G tn root1 s0 64 /\ lookup_var root1 s0 = SOME a1 /\
  ptr_covers G tn root2 s0 64 /\ lookup_var root2 s0 = SOME a2 /\
  w2n a1 + 64 < dimword(:256) /\ w2n a2 + 64 < dimword(:256) /\
  (!i. w2n a1 <= i /\ i < w2n a1 + 64 ==> i NOTIN tn.t_mem) /\
  (!i. w2n a2 <= i /\ i < w2n a2 + 64 ==> i NOTIN tn.t_mem) /\
  not_fresh_at sf root1 /\ not_fresh_at sf root2 /\
  eval_operand ib.buf_operand s1 = SOME b /\
  eval_operand ob.buf_operand s3 = SOME c /\ w2n b + 128 < dimword(:256) /\
  s2.vs_allocas = s1.vs_allocas /\
  (!p. not_fresh_at sf p ==> lookup_var p s2 = lookup_var p s0) ==>
  ?out Gf tnf.
    ob.buf_operand = Var out /\
    (!k. inst_seq_ptr D 0 ctx fn PG G tn
      (emitted_insts sf sa ++
       (emitted_insts sa sb ++ emitted_insts sb sc ++ emitted_insts sc sd ++
        emitted_insts sd sp) ++ emitted_insts sp sm)
      (s0 with vs_inst_idx := k) Gf tnf) /\
    EVERY (\i. i.inst_opcode = ALLOCA \/ i.inst_opcode = ADD \/
      i.inst_opcode = MLOAD \/ i.inst_opcode = MSTORE)
      (emitted_insts sf sa ++ emitted_insts sa sb ++ emitted_insts sb sc ++
       emitted_insts sc sd ++ emitted_insts sd sp ++ emitted_insts sp sm) /\
    ptr_covers Gf tnf bufroot s3 128 /\ ptr_covers Gf tnf out s3 64 /\
    lookup_var bufroot s3 = SOME b /\
    (!i. w2n b <= i /\ i < w2n b + 128 ==> i NOTIN tnf.t_mem) /\
    tnf.t_mem = ((tn.t_mem UNION new_site_bytes s0 s1) DIFF
      {i | w2n b <= i /\ i < w2n b + 128}) UNION new_site_bytes s2 s3 /\
    (!p. not_fresh_at sf p ==> lookup_var p s3 = lookup_var p s0 /\
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p)) /\
    ghost_inv d cenv cx es Gf tnf s3 /\ ghost_kept cenv es sf G tn s0 Gf tnf
Proof
  strip_tac >>
  `128 < dimword(:256)` by simp[wordsTheory.dimword_def] >>
  `!i. w2n a1 <= i /\ i < w2n a1 + 64 ==> i NOTIN new_site_bytes s0 s1` by
    (rpt strip_tac >>
     `eval_operand (Var root1) s0 = SOME a1` by simp[venomStateTheory.eval_operand_def] >>
     qpat_assum `expr_val_at _ _ _ _ _ _ vp (Var root1) s0`
       (mp_then Any mp_tac emitted_allocation_point_exterior) >>
     disch_then drule_all >> simp[]) >>
  `!i. w2n a2 <= i /\ i < w2n a2 + 64 ==> i NOTIN new_site_bytes s0 s1` by
    (rpt strip_tac >>
     `eval_operand (Var root2) s0 = SOME a2` by simp[venomStateTheory.eval_operand_def] >>
     qpat_assum `expr_val_at _ _ _ _ _ _ vq (Var root2) s0`
       (mp_then Any mp_tac emitted_allocation_point_exterior) >>
     disch_then drule_all >> simp[]) >>
  qpat_assum `stmt_state_rel ctx fn cenv cx es s0`
    (mp_then Any (drule_all_then strip_assume_tac)
      exprSimLiteralBufferTheory.alloc_buffer_frame_run) >> gvs[] >>
  `alloca_next_valid s2` by
    gvs[stmt_state_rel_def, venomMemDefsTheory.alloca_inv_def] >>
  `!i. w2n b <= i /\ i < w2n b + 128 ==> i NOTIN new_site_bytes s2 s3` by
    (rpt gen_tac >> strip_tac >>
     irule emitted_allocation_old_region_exterior >> simp[] >> conj_tac
     >- (qexistsl [`sf.cs_next_id`,`128`,`w2n b`] >> simp[]) >>
     qexistsl [`ob`,`64`,`sp`,`sm`] >> simp[]) >>
  mp_tac ecadd_complete_prefix_checked >> simp[] >>
  disch_then (qx_choose_then `out` (qx_choose_then `Gf`
    (qx_choose_then `tnf` strip_assume_tac))) >>
  suspend "frame"
QED

Resume ecadd_prefix_framed[frame]:
  qmatch_asmsub_abbrev_tac `inst_seq_ptr D 0 ctx fn PG G tn code _ Gf tnf` >>
  `run_inst_seq code s0 = OK s3` by
    (simp[Abbr `code`] >>
     qpat_assum `run_inst_seq (emitted_insts sf sa) s0 = OK s1` mp_tac >>
     qpat_assum `run_inst_seq _ s1 = OK s2` mp_tac >>
     qpat_assum `run_inst_seq (emitted_insts sp sm) s2 = OK s3` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     `run_inst_seq (emitted_insts sf sa ++
       ((emitted_insts sa sb ++ emitted_insts sb sc ++ emitted_insts sc sd ++
         emitted_insts sd sp) ++ emitted_insts sp sm)) s0 = OK s3`
       suffices_by simp[listTheory.APPEND_ASSOC] >>
     imp_res_tac exprLoweringPropsTheory.run_inst_seq_append >> asm_rewrite_tac[]) >>
  `EVERY (\i. i.inst_opcode = ALLOCA \/ i.inst_opcode = ADD \/
    i.inst_opcode = MLOAD \/ i.inst_opcode = MSTORE) code` by
    simp[Abbr `code`] >>
  `ghost_inv d cenv cx es Gf tnf s3` by
    (mp_tac (Q.INST [`insz` |-> `128`] arithmetic_prefix_ghost_inv) >> simp[] >>
     (impl_tac >- (rpt strip_tac >> first_x_assum irule >> simp[])) >> simp[]) >>
  `tnf.t_mem SUBSET (tn.t_mem UNION new_site_bytes s0 s1 UNION new_site_bytes s2 s3)` by
    (gvs[SUBSET_DEF, IN_UNION, IN_DIFF] >> metis_tac[]) >>
  `ghost_kept cenv es sf G tn s0 Gf tnf` by
    (mp_tac (Q.INST [`insz` |-> `128`, `outsz` |-> `64`]
       (INST_TYPE [alpha |-> ``:num # num``] allocated_prefix_ghost_kept)) >> simp[] >>
     (impl_tac >- (rpt strip_tac >> first_x_assum drule >> simp[])) >> simp[]) >>
  qexistsl [`out`,`Gf`,`tnf`] >> simp[Abbr `code`]
QED
Finalise ecadd_prefix_framed

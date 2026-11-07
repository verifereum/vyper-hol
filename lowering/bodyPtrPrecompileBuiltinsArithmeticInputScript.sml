Theory bodyPtrPrecompileBuiltinsArithmeticInput
Ancestors bodyPtrPrecompileBuiltinsArithmeticPrefix bodyPtrPrecompileBuiltinsArithmeticRun
          bodyPtrPrecompileBuiltinsCompilerStages bodyPtrPrecompileBuiltinsBoundary
          bodyPtrPrecompileBuiltinsRecoveryResidual
          exprSimProps exprSimDefs exprSimWordArgs bodyPtrDefs
          compileEnv emitHelper exprLoweringProps freshWrites list

(* Regroup compiler operations without expanding compiler records. *)
Theorem point_transfer_group:
  (do src <- emit_op ADD [point; Lit 0w]; value <- emit_op MLOAD [src];
      dst <- emit_op ADD [buf; Lit off]; emit_void MSTORE [dst; value] od)
    sa = ((),sb) /\
  (do src <- emit_op ADD [point; Lit 32w]; value <- emit_op MLOAD [src];
      dst <- emit_op ADD [buf; Lit (off+32w)]; emit_void MSTORE [dst; value] od)
    sb = ((),sc) ==>
  (do src <- emit_op ADD [point; Lit 0w]; value <- emit_op MLOAD [src];
      dst <- emit_op ADD [buf; Lit off]; emit_void MSTORE [dst; value];
      src <- emit_op ADD [point; Lit 32w]; value <- emit_op MLOAD [src];
      dst <- emit_op ADD [buf; Lit (off+32w)]; emit_void MSTORE [dst; value] od)
    sa = ((),sc)
Proof
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem ecmul_framed_input:
  compile_ecmul_point point scalar sf = (res,sb) /\
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sf /\ ~ctx_has_dalloca ctx /\
  (!i. MEM i (emitted_insts sf sb) ==> MEM i (fn_insts fn)) /\
  ghost_inv d cenv cx es G tn s /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sf p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sf p) /\
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo sf es v point s /\
  ptr_val_ok cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) v point G tn s /\
  value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v /\
  eval_operand point s = SOME a /\ w2n a + 64 < dimword(:256) /\
  eval_operand scalar s = SOME w /\ op_taint tn scalar = {} /\
  (!l. scalar <> Label l) /\
  (!p. MEM (Var p) [point;scalar] ==> not_fresh_at sf p) ==>
  ?sz src dst t Gf tnf b c aid.
    (do gas <- emit_op GAS [];
        success <- emit_op STATICCALL
          [gas; Lit 7w; Var src; Lit 96w; Var dst; Lit 64w];
        emit_void ASSERT [success]; return (Var dst) od) sz = (res,sb) /\
    emitted_insts sf sb = emitted_insts sf sz ++ emitted_insts sz sb /\
    run_inst_seq (emitted_insts sf sz) s = OK t /\
    EVERY (\i. i.inst_opcode = ALLOCA \/ i.inst_opcode = ADD \/
      i.inst_opcode = MLOAD \/ i.inst_opcode = MSTORE) (emitted_insts sf sz) /\
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sf sz)
      (s with vs_inst_idx := k) Gf tnf) /\
    not_fresh_at sz src /\ not_fresh_at sz dst /\
    sf.cs_next_var <= sz.cs_next_var /\ sf.cs_next_id <= sz.cs_next_id /\
    local_ptrs_reserved cenv sz /\
    lookup_var src t = SOME b /\ lookup_var dst t = SOME c /\
    FLOOKUP t.vs_allocas aid = SOME (w2n c,64) /\
    sf.cs_next_id <= aid /\ aid < sb.cs_next_id /\
    ptr_covers Gf tnf src t 96 /\ ptr_covers Gf tnf dst t 64 /\
    (!i. w2n b <= i /\ i < w2n b + 96 ==> i NOTIN tnf.t_mem) /\
    mem_bytes_at (w2n b) 96 t.vs_memory =
      word_to_bytes (mload (w2n a) s) T ++
      word_to_bytes (mload (w2n a+32) s) T ++ word_to_bytes w T /\
    stmt_state_rel ctx fn cenv cx es t /\ wb_frame cenv es sf s t /\
    ghost_inv d cenv cx es Gf tnf t /\ ghost_kept cenv es sf G tn s Gf tnf /\
    (!name lo len. local_region cenv es.scopes t name lo len ==>
       regions_disjoint (w2n c) 64 lo len) /\
    (!aid lo len. aid < sf.cs_next_id /\
       FLOOKUP t.vs_allocas aid = SOME (lo,len) ==>
       regions_disjoint (w2n c) 64 lo len) /\
    (cenv.ce_is_ctor ==> !name tv iv off.
       FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
       FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
         | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,iv) ==>
       regions_disjoint (w2n c) 64 off (type_memory_size tv))
Proof
  strip_tac >> drule_all ec_point_read_ready >> strip_tac >> gvs[] >>
  drule ecmul_compiler_stages >> strip_tac >>
  `sa.cs_next_var <= sp.cs_next_var` by simp[] >>
  drule_all allocated_stage_frame >> strip_tac >>
  `!x. scalar = Var x ==> not_fresh_at sf x` by metis_tac[MEM] >>
  `not_fresh_at sf p` by metis_tac[MEM] >>
  ` (do src <- emit_op ADD [Var p; Lit 0w]; value <- emit_op MLOAD [src];
        dst <- emit_op ADD [ib.buf_operand; Lit 0w]; emit_void MSTORE [dst; value];
        src <- emit_op ADD [Var p; Lit 32w]; value <- emit_op MLOAD [src];
        dst <- emit_op ADD [ib.buf_operand; Lit 32w]; emit_void MSTORE [dst; value] od)
      sa = ((),s2)` by
    (qpat_assum `_ sa = ((),s1)` (mp_then Any mp_tac point_transfer_group) >>
     simp[wordsTheory.WORD_ADD_0] >> disch_then (qspec_then `s2` mp_tac) >>
     gvs[]) >>
  `!x. MEM (Var x) [Var p;scalar] ==> not_fresh_at sf x` by
    (simp[] >> metis_tac[]) >>
  `w2n a + 64 < dimword(:256)` by fs[wordsTheory.dimword_def] >>
  drule_all ecmul_prefix_runtime >> strip_tac >>
  suspend "checked"
QED

Resume ecmul_framed_input[checked]:
  `local_ptrs_rel fn cenv es.scopes s /\
   local_ptrs_rel fn cenv es.scopes s2'` by
    fs[stmt_state_rel_def, state_rel_def] >>
  imp_res_tac word_transfer_compiler_shape >>
  imp_res_tac offset_store_compiler_shape >>
  `emitted_insts sa s2 = emitted_insts sa s1 ++ emitted_insts s1 s2` by
    (irule emitted_insts_append >> simp[]) >>
  `run_inst_seq (emitted_insts sa s1 ++ emitted_insts s1 s2 ++ emitted_insts s2 sp)
    s1' = OK s2'` by
    (qpat_x_assum `run_inst_seq (emitted_insts sa s2 ++ _) _ = _` mp_tac >>
     asm_rewrite_tac[listTheory.APPEND_ASSOC]) >>
  `lookup_var p s = SOME a` by gvs[venomStateTheory.eval_operand_def] >>
  qpat_assum `ib.buf_operand = _` (fn ei =>
    map_every (fn pat => qpat_assum pat
      (fn th => assume_tac (REWRITE_RULE [ei] th)))
      [`_ sa = ((),s1)`, `_ s1 = ((),s2)`, `_ s2 = ((),sp)`]) >>
  drule_all ecmul_prefix_framed >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  suspend "pack"
QED

Resume ecmul_framed_input[pack]:
  `emitted_insts sa sp = emitted_insts sa s2 ++ emitted_insts s2 sp` by
    (irule emitted_insts_append >> simp[]) >>
  `emitted_insts sa sp = emitted_insts sa s1 ++ emitted_insts s1 s2 ++
    emitted_insts s2 sp` by simp[listTheory.APPEND_ASSOC] >>
  `run_inst_seq (emitted_insts sf sm) s = OK s3` by
    (`run_inst_seq (emitted_insts sf sa ++
        ((emitted_insts sa s2 ++ emitted_insts s2 sp) ++ emitted_insts sp sm)) s = OK s3`
       suffices_by simp[listTheory.APPEND_ASSOC] >>
     qpat_assum `run_inst_seq (emitted_insts sf sa) s = _` mp_tac >>
     qpat_assum `run_inst_seq (emitted_insts sa s2 ++ _) _ = _` mp_tac >>
     qpat_assum `run_inst_seq (emitted_insts sp sm) _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     imp_res_tac run_inst_seq_append >> asm_rewrite_tac[]) >>
  `s3.vs_memory = s2'.vs_memory` by
    (drule_all emitted_allocation_memory >> simp[]) >>
  qpat_assum `compile_alloc_buffer 64 sp = _`
    (mp_then Any strip_assume_tac loweringHaltTheory.compile_alloc_buffer_parts) >>
  `sp.cs_next_id < sb.cs_next_id` by decide_tac >>
  qexistsl [`sm`,`x`,`x'`,`s3`,`Gf`,`tnf`,`b`,`c`,`sp.cs_next_id`] >>
  gvs[venomStateTheory.eval_operand_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
Finalise ecmul_framed_input

Theorem ecadd_framed_input:
  compile_ecadd_points point other sf = (res,sb) /\
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sf /\ ~ctx_has_dalloca ctx /\
  (!i. MEM i (emitted_insts sf sb) ==> MEM i (fn_insts fn)) /\
  ghost_inv d cenv cx es G tn s /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sf p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sf p) /\
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo sf es vp point s /\
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo sf es vq other s /\
  ptr_val_ok cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) vp point G tn s /\
  ptr_val_ok cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) vq other G tn s /\
  value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) vp /\
  value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) vq /\
  eval_operand point s = SOME a1 /\ w2n a1 + 64 < dimword(:256) /\
  eval_operand other s = SOME a2 /\ w2n a2 + 64 < dimword(:256) /\
  (!p. MEM (Var p) [point;other] ==> not_fresh_at sf p) ==>
  ?sz src dst t Gf tnf b c aid.
    (do gas <- emit_op GAS [];
        success <- emit_op STATICCALL
          [gas; Lit 6w; Var src; Lit 128w; Var dst; Lit 64w];
        emit_void ASSERT [success]; return (Var dst) od) sz = (res,sb) /\
    emitted_insts sf sb = emitted_insts sf sz ++ emitted_insts sz sb /\
    run_inst_seq (emitted_insts sf sz) s = OK t /\
    EVERY (\i. i.inst_opcode = ALLOCA \/ i.inst_opcode = ADD \/
      i.inst_opcode = MLOAD \/ i.inst_opcode = MSTORE) (emitted_insts sf sz) /\
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sf sz)
      (s with vs_inst_idx := k) Gf tnf) /\
    not_fresh_at sz src /\ not_fresh_at sz dst /\
    sf.cs_next_var <= sz.cs_next_var /\ sf.cs_next_id <= sz.cs_next_id /\
    local_ptrs_reserved cenv sz /\
    lookup_var src t = SOME b /\ lookup_var dst t = SOME c /\
    FLOOKUP t.vs_allocas aid = SOME (w2n c,64) /\
    sf.cs_next_id <= aid /\ aid < sb.cs_next_id /\
    ptr_covers Gf tnf src t 128 /\ ptr_covers Gf tnf dst t 64 /\
    (!i. w2n b <= i /\ i < w2n b + 128 ==> i NOTIN tnf.t_mem) /\
    mem_bytes_at (w2n b) 128 t.vs_memory =
      word_to_bytes (mload (w2n a1) s) T ++ word_to_bytes (mload (w2n a1+32) s) T ++
      word_to_bytes (mload (w2n a2) s) T ++ word_to_bytes (mload (w2n a2+32) s) T /\
    stmt_state_rel ctx fn cenv cx es t /\ wb_frame cenv es sf s t /\
    ghost_inv d cenv cx es Gf tnf t /\ ghost_kept cenv es sf G tn s Gf tnf /\
    (!name lo len. local_region cenv es.scopes t name lo len ==>
       regions_disjoint (w2n c) 64 lo len) /\
    (!aid lo len. aid < sf.cs_next_id /\
       FLOOKUP t.vs_allocas aid = SOME (lo,len) ==>
       regions_disjoint (w2n c) 64 lo len) /\
    (cenv.ce_is_ctor ==> !name tv iv off.
       FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
       FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
         | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,iv) ==>
       regions_disjoint (w2n c) 64 off (type_memory_size tv))
Proof
  strip_tac >>
  qpat_assum `ptr_val_ok _ _ vp _ _ _ _`
    (mp_then Any (drule_all_then strip_assume_tac) ec_point_read_ready) >>
  qpat_assum `ptr_val_ok _ _ vq _ _ _ _`
    (mp_then Any (drule_all_then strip_assume_tac) ec_point_read_ready) >> gvs[] >>
  drule ecadd_compiler_stages >> strip_tac >>
  `sa.cs_next_var <= sp.cs_next_var` by simp[] >>
  drule_all allocated_stage_frame >> strip_tac >>
  suspend "runtime"
QED

Resume ecadd_framed_input[runtime]:
  ` (do src <- emit_op ADD [Var p; Lit 0w]; value <- emit_op MLOAD [src];
        dst <- emit_op ADD [ib.buf_operand; Lit 0w]; emit_void MSTORE [dst; value];
        src <- emit_op ADD [Var p; Lit 32w]; value <- emit_op MLOAD [src];
        dst <- emit_op ADD [ib.buf_operand; Lit 32w]; emit_void MSTORE [dst; value] od)
      sa = ((),s2)` by
    (qpat_assum `_ sa = ((),s1)` (mp_then Any mp_tac point_transfer_group) >>
     simp[wordsTheory.WORD_ADD_0] >> disch_then (qspec_then `s2` mp_tac) >> gvs[]) >>
  ` (do src <- emit_op ADD [Var p'; Lit 0w]; value <- emit_op MLOAD [src];
        dst <- emit_op ADD [ib.buf_operand; Lit 64w]; emit_void MSTORE [dst; value];
        src <- emit_op ADD [Var p'; Lit 32w]; value <- emit_op MLOAD [src];
        dst <- emit_op ADD [ib.buf_operand; Lit 96w]; emit_void MSTORE [dst; value] od)
      s2 = ((),sp)` by
    (qpat_assum `_ s2 = ((),s3)` (mp_then Any mp_tac point_transfer_group) >>
     simp[wordsTheory.word_add_n2w] >>
     disch_then (qspec_then `sp` mp_tac) >> gvs[]) >>
  `!x. MEM (Var x) [Var p;Var p'] ==> not_fresh_at sf x` by
    (simp[] >> metis_tac[]) >>
  `w2n a1 + 64 < dimword(:256)` by fs[wordsTheory.dimword_def] >>
  `w2n a2 + 64 < dimword(:256)` by fs[wordsTheory.dimword_def] >>
  drule_all ecadd_prefix_runtime >> strip_tac >>
  suspend "checked"
QED

Resume ecadd_framed_input[checked]:
  `local_ptrs_rel fn cenv es.scopes s /\
   local_ptrs_rel fn cenv es.scopes s2'` by
    fs[stmt_state_rel_def, state_rel_def] >>
  imp_res_tac word_transfer_compiler_shape >>
  `emitted_insts sa s2 = emitted_insts sa s1 ++ emitted_insts s1 s2` by
    (irule emitted_insts_append >> simp[]) >>
  `emitted_insts s2 sp = emitted_insts s2 s3 ++ emitted_insts s3 sp` by
    (irule emitted_insts_append >> simp[]) >>
  `run_inst_seq (emitted_insts sa s1 ++ emitted_insts s1 s2 ++
    emitted_insts s2 s3 ++ emitted_insts s3 sp) s1' = OK s2'` by
    (qpat_x_assum `run_inst_seq (emitted_insts sa s2 ++ _) _ = _` mp_tac >>
     asm_rewrite_tac[listTheory.APPEND_ASSOC]) >>
  `lookup_var p s = SOME a1 /\ lookup_var p' s = SOME a2` by
    gvs[venomStateTheory.eval_operand_def] >>
  `not_fresh_at sf p /\ not_fresh_at sf p'` by metis_tac[] >>
  qpat_assum `ib.buf_operand = _` (fn ei =>
    map_every (fn pat => qpat_assum pat
      (fn th => assume_tac (REWRITE_RULE [ei] th)))
      [`_ sa = ((),s1)`, `_ s1 = ((),s2)`, `_ s2 = ((),s3)`, `_ s3 = ((),sp)`]) >>
  drule_all ecadd_prefix_framed >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  suspend "pack"
QED

Resume ecadd_framed_input[pack]:
  `emitted_insts sa sp = emitted_insts sa s2 ++ emitted_insts s2 sp` by
    (irule emitted_insts_append >> simp[]) >>
  `emitted_insts sa sp = emitted_insts sa s1 ++ emitted_insts s1 s2 ++
    emitted_insts s2 s3 ++ emitted_insts s3 sp` by simp[listTheory.APPEND_ASSOC] >>
  `run_inst_seq (emitted_insts sf sm) s = OK s3'` by
    (`run_inst_seq (emitted_insts sf sa ++
        ((emitted_insts sa s2 ++ emitted_insts s2 sp) ++ emitted_insts sp sm)) s = OK s3'`
       suffices_by simp[listTheory.APPEND_ASSOC] >>
     qpat_assum `run_inst_seq (emitted_insts sf sa) s = _` mp_tac >>
     qpat_assum `run_inst_seq (emitted_insts sa s2 ++ _) _ = _` mp_tac >>
     qpat_assum `run_inst_seq (emitted_insts sp sm) _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     imp_res_tac run_inst_seq_append >> asm_rewrite_tac[]) >>
  `s3'.vs_memory = s2'.vs_memory` by
    (drule_all emitted_allocation_memory >> simp[]) >>
  qpat_assum `compile_alloc_buffer 64 sp = _`
    (mp_then Any strip_assume_tac loweringHaltTheory.compile_alloc_buffer_parts) >>
  `sp.cs_next_id < sb.cs_next_id` by decide_tac >>
  qexistsl [`sm`,`x`,`x'`,`s3'`,`Gf`,`tnf`,`b`,`c`,`sp.cs_next_id`] >>
  gvs[venomStateTheory.eval_operand_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
Finalise ecadd_framed_input

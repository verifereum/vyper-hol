(* A single stage execution carries both its gas path and snapshot owner. *)
Theory tuplePlaceStage
Ancestors
  tuplePlacePrefixCert tupleStageProps exprLoweringProps localPtrsProps
  compileEnv loweringStateRelDefs loweringSlice fragExec valueEncoding vyperValue list finite_map
  exprLowering stmtSimDeclPath exprSimBufferStore fragGasPath fragGasSeq fragGasMode venomMemDefs
  venomInstProofs venomInst venomState venomExecSemantics emitHelper
  valueEncodingProofs valueEncodingProps valueCopy loweringHalt stmtLowering
  context loweringPosts stmtSimProps
Libs
  monadsyntax

Theorem tuple_place_mcopy_path[local]:
  !ctx func cenv cx es sa sb s inst p dw sw src sz tv v.
    emit_void MCOPY [Var p; src; Lit (n2w sz)] sa = ((), sb) /\
    lookup_var p s = SOME dw /\ eval_operand src s = SOME sw /\
    sz < dimword (:256) /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
    not_local_ptr cenv es.scopes p /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n dw, sz) /\
    val_in_memory tv v (w2n sw) s.vs_memory /\ val_wf tv v /\
    val_footprint tv v <= sz /\ fn_has_code sa sb func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. stmt_state_rel ctx func cenv cx es t /\
      val_in_memory tv v (w2n dw) t.vs_memory /\
      (!q. lookup_var q t = lookup_var q s) /\ t.vs_allocas = s.vs_allocas /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      gas_marked_path F ctx func s 0 (OK t) /\
      (!a len. a + len <= w2n dw \/ w2n dw + sz <= a ==>
        mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory)
Proof
  rpt strip_tac >>
  `stmt_state_rel ctx func cenv cx es (mcopy (w2n dw) (w2n sw) sz s)` by
    (irule stmt_state_rel_mcopy_alloca >> simp[] >>
     qexistsl [`sz`, `inst`, `p`] >> simp[]) >>
  `val_in_memory tv v (w2n dw) (mcopy (w2n dw) (w2n sw) sz s).vs_memory` by
    (irule mcopy_val_in_memory >> simp[]) >>
  `gas_marked_path F ctx func s 0
     (OK (mcopy (w2n dw) (w2n sw) sz s with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule emit_inst_zero_marked_path >> simp[] >>
     qexistsl [`[Var p; src; Lit (n2w sz)]`, `MCOPY`, `[]`, `sa`, `sb`] >>
     gvs[emit_void_def, emit_inst_def, is_terminator_def] >>
     simp[stepInstBaseLib.simp_opcode_clause ``MCOPY``, mk_inst_def,
          eval_operand_def, wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD]) >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts)` by
    gvs[emit_void_def, emit_inst_def, comp_bind_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  qexists `mcopy (w2n dw) (w2n sw) sz s with vs_inst_idx := SUC s.vs_inst_idx` >>
  simp[stmt_state_rel_inst_idx] >>
  rpt conj_tac
  >- simp[mcopy_def, write_memory_with_expansion_def, LET_THM, lookup_var_def]
  >- simp[mcopy_def, write_memory_with_expansion_def, LET_THM] >>
  rpt strip_tac >> irule valueCopyTheory.mem_bytes_at_mcopy_disjoint >> decide_tac
QED

Theorem tuple_place_stage_path:
  !ctx func cenv cx es sa sb staged op s sw sz tv v.
    (do buf <- compile_alloc_buffer sz;
        emit_void MCOPY [buf.buf_operand; op; Lit (n2w sz)];
        comp_return buf.buf_operand od) sa = (staged,sb) /\
    fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\
    (!x. op = Var x ==> not_fresh_at sa x) /\
    eval_operand op s = SOME sw /\
    val_in_memory tv v (w2n sw) s.vs_memory /\ val_wf tv v /\
    val_footprint tv v <= sz /\ sz < dimword (:256) /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t w. eval_operand staged t = SOME w /\
      FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
      val_in_memory tv v (w2n w) t.vs_memory /\
      stmt_state_rel ctx func cenv cx es t /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
        FLOOKUP t.vs_allocas aid = SOME entry) /\
      (!x. staged = Var x ==> not_fresh_at sb x) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      gas_marked_path F ctx func s 0 (OK t) /\
      (!n lb lsz. local_region cenv es.scopes t n lb lsz ==>
        w2n w + sz <= lb \/ lb + lsz <= w2n w) /\
      alloca_frame cenv es sa s cenv es t
Proof
  rpt strip_tac >> drule_all tuple_stage_copy_parts >>
  disch_then (qx_choosel_then [`sx`, `sm`, `p`] strip_assume_tac) >>
  `MEM (mk_inst sx.cs_next_id ALLOCA [Lit (n2w sz)] [p]) (fn_insts func)` by
    (irule emit_inst_fn_member >> qexists `sm` >> simp[]) >>
  `not_local_ptr cenv es.scopes p` by
    (gvs[local_ptrs_reserved_def, not_local_ptr_def] >> metis_tac[]) >>
  `op <> Var p` by metis_tac[] >>
  `s.vs_current_bb = sx.cs_current_bb /\
   s.vs_inst_idx = LENGTH sx.cs_current_insts` by simp[] >>
  drule_all annassign_alloca_operand_framed_path >>
  disch_then (qx_choosel_then [`s1`, `w`] strip_assume_tac) >>
  `eval_operand op s1 = SOME sw` by metis_tac[] >>
  `val_in_memory tv v (w2n sw) s1.vs_memory` by simp[] >>
  `?t. stmt_state_rel ctx func cenv cx es t /\
      val_in_memory tv v (w2n w) t.vs_memory /\
      (!q. lookup_var q t = lookup_var q s1) /\ t.vs_allocas = s1.vs_allocas /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      gas_marked_path F ctx func s1 0 (OK t) /\
      (!a len. a + len <= w2n w \/ w2n w + sz <= a ==>
        mem_bytes_at a len t.vs_memory = mem_bytes_at a len s1.vs_memory)` by
    (irule tuple_place_mcopy_path >> simp[] >>
     qexists `mk_inst sx.cs_next_id ALLOCA [Lit (n2w sz)] [p]` >>
     goal_assum (drule_at (Pat `emit_void _ _ _ = _`)) >> gvs[mk_inst_def]) >>
  `gas_marked_path F ctx func s (0 + 0) (OK t)` by
    (irule gas_marked_path_then >> qexists `s1` >> simp[]) >>
  `!n lb lsz. local_region cenv es.scopes t n lb lsz ==>
        w2n w + sz <= lb \/ lb + lsz <= w2n w` by
    (rpt strip_tac >>
     `alloca_inv t /\ local_ptrs_rel func cenv es.scopes t` by
       gvs[stmt_state_rel_def, state_rel_def] >>
     qpat_x_assum `sx = _` SUBST_ALL_TAC >>
     drule_at (Pat `MEM _ _`) local_ptrs_rel_alloca_disjoint >>
     simp[mk_inst_def] >>
     disch_then (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
     gvs[] >> simp[loweringStateRelDefsTheory.regions_disjoint_def, arithmeticTheory.ADD_COMM] ) >>
  `alloca_frame cenv es sa s cenv es t` by
    (irule localMemoryStorePathTheory.alloca_frame_owned_copy >>
     `allocas_non_overlapping t` by gvs[stmt_state_rel_def, state_rel_def, alloca_inv_def] >>
     simp[] >> conj_tac
     >- (rpt strip_tac >> `x <> p` by metis_tac[] >> simp[]) >>
     reverse conj_tac >- metis_tac[] >>
     qexistsl [`w2n w`, `sx.cs_next_id`, `sz`] >>
     gvs[arithmeticTheory.ADD_COMM] >> metis_tac[]) >>
  qexistsl [`t`, `w`] >> simp[eval_operand_def] >>
  conj_tac >- gvs[] >>
  conj_tac >- (rpt strip_tac >> `x <> p` by metis_tac[] >> simp[]) >>
  gvs[] >> rpt strip_tac >> first_x_assum drule >> simp[]
QED

Theorem tuple_place_stage_snapshot_path:
  !ctx func cenv cx es sa sb staged op s sw ltvs v lo tys ltys.
    (do buf <- compile_alloc_buffer (type_memory_size_list ltvs);
        emit_void MCOPY [buf.buf_operand; op; Lit (n2w (type_memory_size_list ltvs))];
        comp_return buf.buf_operand od) sa = (staged,sb) /\
    fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\
    (!x. op = Var x ==> not_fresh_at sa x) /\
    eval_operand op s = SOME sw /\
    val_in_memory (TupleTV ltvs) v (w2n sw) s.vs_memory /\
    val_wf (TupleTV ltvs) v /\
    val_footprint (TupleTV ltvs) v <= type_memory_size_list ltvs /\
    type_memory_size_list ltvs < dimword (:256) /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\ lo <= sa.cs_next_id ==>
    ?t w. eval_operand staged t = SOME w /\
      FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,type_memory_size_list ltvs) /\
      val_in_memory (TupleTV ltvs) v (w2n w) t.vs_memory /\
      stmt_state_rel ctx func cenv cx es t /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
        FLOOKUP t.vs_allocas aid = SOME entry) /\
      (!x. staged = Var x ==> not_fresh_at sb x) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      gas_marked_path F ctx func s 0 (OK t) /\
      tuple_place_snapshot cenv cx es lo sb.cs_next_id tys ltys ltvs w t /\
      alloca_frame cenv es sa s cenv es t
Proof
  rpt strip_tac >>
  `sa.cs_next_id < sb.cs_next_id` by
    (drule_all tuple_stage_copy_parts >>
     strip_tac >>
     gvs[emit_void_def, emit_inst_def, comp_bind_def, comp_ignore_bind_def,
         comp_return_def, fresh_id_def, emit_def]) >>
  drule_all tuple_place_stage_path >>
  disch_then (qx_choosel_then [`t`, `w`] strip_assume_tac) >>
  qexistsl [`t`, `w`] >> simp[] >>
  irule tuple_place_snapshot_owned >>
  qexistsl [`sa.cs_next_id`, `w2n w`, `type_memory_size_list ltvs`] >>
  gvs[] >> rpt strip_tac >> first_x_assum drule >> simp[]
QED

(* Mapping scratch writes retain their allocation and its local separation. *)
Theory bodyIntCallFamStmtMutationAugTargetMapping
Ancestors
  bodyIntCallFamAggArray bodyIntCallFamStmtMutationLoad exprSimMapKey
  bodyIntCallJointAggCore placeMemoryCopyEffect venomState venomMemProps
  exprLoweringProps intCallFrame compileEnv valueEncodingProps
  stmtSimAugAssignPlaceMemory bodyIntCallJointContract emitHelperProps fragGasMode loweringStateRelDefs

Theorem intcall_scratch_mstore:
  intcall_frame_ok fp /\
  intcall_expr_cont fp ce env es0 sa s0 es si s /\
  emit_void MSTORE [Var p; op] si = ((),sb) /\
  fn_has_code si sb fp.jc_func /\
  lookup_var p s = SOME w /\ eval_operand op s = SOME wd /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,k) /\
  sa.cs_next_id <= inst.inst_id /\
  MEM inst (fn_insts fp.jc_func) /\ inst.inst_opcode = ALLOCA /\
  sa.cs_next_var <= si.cs_next_var /\
  fp.jc_lo <= b /\ b <= w2n w /\ w2n w + 32 <= b+k /\
  (!n a z. local_region ce es.scopes s n a z ==>
     regions_disjoint b k a z) /\
  (!n a z. local_region ce es0.scopes s0 n a z ==>
     regions_disjoint b k a z) ==>
  ?u. intcall_expr_cont fp ce env es0 sa s0 es sb u /\
      gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
      FLOOKUP u.vs_allocas inst.inst_id = SOME (b,k) /\
      (!n a z. local_region ce es.scopes u n a z ==>
         regions_disjoint b k a z) /\
      (!q. eval_operand q u = eval_operand q s) /\
      mem_word_at (w2n w) u.vs_memory = wd /\
      (!a z. regions_disjoint a z (w2n w) 32 ==>
         mem_bytes_at a z u.vs_memory = mem_bytes_at a z s.vs_memory)
Proof
  strip_tac >> drule_all intcall_owned_mstore_landing >> strip_tac >> gvs[] >>
  qexists `mstore (w2n w) wd s with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[] >> conj_tac
  >- metis_tac[typed_copy_effect_path] >>
  conj_tac
  >- (simp[local_region_def, lookup_var_def, mstore_def] >>
      metis_tac[local_region_def, lookup_var_def]) >>
  conj_tac >- simp[mstore_mem_word_at_same] >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def] >>
  metis_tac[mstore_mem_bytes_at_disjoint]
QED

(* Allocate scratch, then initialize its first word from an old operand. *)
Theorem intcall_scratch_entry:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s /\
  compile_alloc_buffer sz sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand; op] sm = ((),sb) /\
  fn_has_code sa sm fp.jc_func /\ fn_has_code sm sb fp.jc_func /\
  fn_inst_ids_distinct fp.jc_func /\ sz < dimword (:256) /\ 32 <= sz /\
  (!x. op = Var x ==> not_fresh_at sa x) /\ eval_operand op s = SOME wd /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u w inst p. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
    intcall_expr_cont fp ce env es sa s es sb u /\
    buf.buf_operand = Var p /\ lookup_var p u = SOME w /\ not_fresh_at sb p /\
    FLOOKUP u.vs_allocas inst.inst_id = SOME (w2n w,sz) /\
    inst.inst_id = sa.cs_next_id /\ inst.inst_opcode = ALLOCA /\
    MEM inst (fn_insts fp.jc_func) /\
    fp.jc_lo <= w2n w /\ w2n w + sz < dimword (:256) /\
    sa.cs_next_id < sb.cs_next_id /\ sa.cs_next_var <= sb.cs_next_var /\
    (!name a z. local_region ce es.scopes u name a z ==>
       regions_disjoint (w2n w) sz a z) /\
    (!name a z. local_region ce es.scopes s name a z ==>
       regions_disjoint (w2n w) sz a z) /\
    mem_word_at (w2n w) u.vs_memory = wd
Proof
  strip_tac >> drule_all intcall_array_root_alloc >> strip_tac >>
  `eval_operand op u = SOME wd` by
    (irule aug_place_saved_operand >> goal_assum (drule_at Any) >>
     fs[intcall_expr_cont_def] >> metis_tac[]) >>
  `lookup_var p u = SOME w` by fs[eval_operand_def] >>
  qpat_x_assum `emit_void _ _ _ = _` mp_tac >> simp[] >> strip_tac >>
  drule_at (Pat `intcall_expr_cont _ _ _ _ _ _ _ _ _`) intcall_scratch_mstore >>
  disch_then (drule_at (Pat `emit_void _ _ _ = _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >>
  simp[] >> (impl_tac >- metis_tac[]) >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  rename1 `mem_word_at (w2n w) landed.vs_memory = wd` >>
  qexistsl [`landed`, `w`, `inst`] >> simp[] >>
  conj_tac >- metis_tac[gas_marked_path_then, arithmeticTheory.ADD] >>
  `eval_operand (Var p) landed = SOME w` by gvs[] >>
  fs[eval_operand_def, not_fresh_at_def] >> metis_tac[]
QED

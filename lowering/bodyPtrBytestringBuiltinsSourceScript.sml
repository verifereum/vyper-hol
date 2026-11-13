(* Source preparation for memory-backed slices. Fixed bytes use a raw
   scratch word, not a dynamic bytestring's length-prefixed representation. *)
Theory bodyPtrBytestringBuiltinsSource
Ancestors
  bodyPtrBytestringBuiltinsBuffer exprSimPtrProps builtinBytes
  emitHelper compileEnv loweringStateRelDefs exprLoweringProps bodyPtrDefs venomState venomInstProofs
  finite_map fragExec freshWrites fragGasPathPtr typedCopyPtr bodyPtrAttributeAdd
  ptrDiscipline venomInst emitHelperProps fragExecPtr valueEncodingProps wordLoadStorePtr

Theorem compile_bytestring_src_parts:
  compile_bytestring_src src sa = ((len,data),sb) ==>
  ?sm. emit_op MLOAD [src] sa = (len,sm) /\
       emit_op ADD [src; Lit 32w] sm = (data,sb)
Proof
  simp[compile_bytestring_src_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >> metis_tac[]
QED

(* A clean length word is scalar, while the source root remains a pointer.
   The explicit loaded value premise is supplied by source representation. *)
Theorem emit_bytestring_length_counted:
  emit_op MLOAD [Var src] sa = (op,sb) /\ fn_has_code sa sb fn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\ not_fresh_at sa src /\
  ptr_covers G tn src s (32+L) /\ lookup_var src s = SOME a /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  mload (w2n a) s = n2w L /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) ==>
  !D PG. ?out G' tn'.
    op = Var out /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
      (OK ((update_var out (n2w L) s) with vs_inst_idx := SUC s.vs_inst_idx)) /\
    op_taint tn' op = {} /\ op_prov G' op = NONE /\
    ptr_covers G' tn' src (update_var out (n2w L) s) (32+L) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> rpt gen_tac >>
  `ptr_covers G tn src s 32` by
    (fs[ptr_covers_def] >> metis_tac[arithmeticTheory.LE_ADD]) >>
  drule_all emit_mload_ptr_path >>
  disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`out`,`G'`,`tn'`] >> gvs[] >>
  conj_tac
  >- (`src <> STRING #"%" (toString sa.cs_next_var)` by metis_tac[] >>
      gvs[ptr_covers_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
      metis_tac[]) >>
  metis_tac[]
QED

Theorem compile_bytestring_src_compiler_parts:
  compile_bytestring_src (Var src) sa = ((len,data),sb) /\
  not_fresh_at sa src ==>
  ?sm l p. emit_op MLOAD [Var src] sa = (Var l,sm) /\
    emit_op ADD [Var src; Lit 32w] sm = (Var p,sb) /\
    len = Var l /\ data = Var p /\ src <> l /\ src <> p /\ l <> p /\
    cs_extends sa sm /\ cs_extends sm sb /\
    sm.cs_current_bb = sa.cs_current_bb /\ sb.cs_current_bb = sm.cs_current_bb /\
    LENGTH sm.cs_current_insts = LENGTH sa.cs_current_insts + 1 /\
    LENGTH sb.cs_current_insts = LENGTH sm.cs_current_insts + 1 /\
    (!x. not_fresh_at sa x ==> x <> l /\ x <> p)
Proof
  strip_tac >> drule compile_bytestring_src_parts >> strip_tac >>
  `cs_extends sa sm /\ cs_extends sm sb` by
    metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  qpat_x_assum `emit_op ADD _ _ = _` mp_tac >>
  qpat_x_assum `emit_op MLOAD _ _ = _` mp_tac >>
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_id_def, fresh_var_def, emit_def] >> rpt strip_tac >>
  gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]
QED

Theorem compile_bytestring_src_counted:
  compile_bytestring_src (Var src) sa = ((len,data),sb) /\
  fn_has_code sa sb fn /\ not_fresh_at sa src /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  ptr_covers G tn src s (32+L) /\ lookup_var src s = SOME a /\
  w2n a + 32 < dimword (:256) /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  mload (w2n a) s = n2w L /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) ==>
  !D PG. ?l p t G2 tn2.
    len = Var l /\ data = Var p /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G2 tn2 (OK t) /\
    eval_operand len t = SOME (n2w L) /\
    op_prov G2 len = NONE /\ op_taint tn2 len = {} /\
    lookup_var p t = SOME (a + 32w) /\
    ptr_covers G2 tn2 p t L /\ ptr_covers G2 tn2 src t (32+L) /\
    t.vs_memory = s.vs_memory /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    tn2.t_mem = tn.t_mem /\ tn2.t_stor = tn.t_stor /\
    tn2.t_trans = tn.t_trans /\ tn2.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\
      FLOOKUP G2 x = FLOOKUP G x /\ op_taint tn2 (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> rpt gen_tac >>
  drule_all compile_bytestring_src_compiler_parts >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all emit_bytestring_length_counted >>
  disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
  `out = l` by gvs[] >> qpat_x_assum `out = l` SUBST_ALL_TAC >>
  qabbrev_tac `u = (update_var l (n2w L) s) with vs_inst_idx := SUC s.vs_inst_idx` >>
  `~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\
   u.vs_inst_idx = LENGTH sm.cs_current_insts /\
   lookup_var src u = SOME a /\ ptr_covers G' tn' src u (32+L)` by
    gvs[Abbr `u`, update_var_def, lookup_var_def, ptr_covers_def, FLOOKUP_UPDATE] >>
  `32 + L <= 32 + L` by simp[] >>
  `eval_operand (Lit 32w) u = SOME (n2w 32) /\ op_taint tn' (Lit 32w) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all emit_pointer_offset_counted_covers >>
  disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
  suspend "compose"
QED

Resume compile_bytestring_src_counted[compose]:
  qmatch_asmsub_abbrev_tac
    `gas_path_ptr_edge D 0 ctx fn PG G' tn' u 0 G2 tn2 (OK t)` >>
  `~t.vs_halted` by simp[Abbr `t`, update_var_def] >>
  `gas_path_ptr D 0 ctx fn PG G' tn' u 0 G2 tn2 (OK t)` by
    (`gas_path_ptr D 0 ctx fn PG G2 tn2 t 0 G2 tn2 (OK t)` by
       simp[gas_path_ptr_rules] >>
     drule_at (Pat `gas_path_ptr_edge _ _ _ _ _ G' _ _ _ _ _ _`)
       (cj 2 gas_path_ptr_rules) >> disch_then drule >> simp[]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 G2 tn2 (OK t)` by
    metis_tac[gas_path_ptr_then, arithmeticTheory.ADD_0] >>
  suspend "frame"
QED

Resume compile_bytestring_src_counted[frame]:
  `ptr_covers G2 tn2 src t (32+L)` by
    (simp_tac pure_ss [Abbr `t`] >> irule attribute_ptr_covers_update >>
     conj_tac >- simp[] >> qexistsl_tac [`G'`,`tn'`] >>
     simp[Abbr `G2`, Abbr `tn2`, copy_len_binop_ghost_frame]) >>
  `!x. x <> p ==> FLOOKUP G2 x = FLOOKUP G' x /\
    op_taint tn2 (Var x) = op_taint tn' (Var x)` by
    simp[Abbr `G2`, Abbr `tn2`, copy_len_binop_ghost_frame] >>
  qexistsl_tac [`l`,`p`,`t`,`G2`,`tn2`] >>
  simp[Abbr `t`, Abbr `u`, update_var_def, lookup_var_def, eval_operand_def,
    FLOOKUP_UPDATE, arithmeticTheory.ADD1, arithmeticTheory.ADD_ASSOC] >>
  conj_tac >- gvs[op_prov_def] >>
  simp[Abbr `tn2`, copy_len_binop_ghost_frame] >>
  simp[step_taint_def, imm_taint_def, mk_inst_def]
QED

Finalise compile_bytestring_src_counted

(* Raw scratch preparation: the store cleans exactly the payload word;
   it does not install a dynamic bytestring length header. *)
Theorem emit_scratch_word_counted:
  emit_void MSTORE [Var dst; value] sa = ((),sb) /\ fn_has_code sa sb fn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\ ptr_covers G tn dst s 32 /\
  lookup_var dst s = SOME a /\ eval_operand value s = SOME w /\
  op_taint tn value = {} /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  !D PG. ?t tn'.
    t = (mstore (w2n a) w s) with vs_inst_idx := SUC s.vs_inst_idx /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G tn' (OK t) /\
    ptr_covers G tn' dst t 32 /\
    (!root cap. ptr_covers G tn root s cap ==> ptr_covers G tn' root t cap) /\
    mem_word_at (w2n a) t.vs_memory = w /\
    (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn'.t_mem) /\
    tn'.t_mem = tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a + 32} /\
    tn'.t_var = tn.t_var /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. lookup_var x t = lookup_var x s) /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted
Proof
  strip_tac >> rpt gen_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id MSTORE [Var dst; value] []]` by
    (qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     simp[emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, emit_def] >> strip_tac >> gvs[]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
    SOME (mk_inst sa.cs_next_id MSTORE [Var dst; value] [])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `step_inst_base (mk_inst sa.cs_next_id MSTORE [Var dst; value] []) s =
    OK (mstore (w2n a) w s)` by
    (irule step_MSTORE >> simp[eval_operand_def]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn
     (mk_inst sa.cs_next_id MSTORE [Var dst; value] []) s` by
    (irule ptr_inst_ok_mstore >> simp[]) >>
  drule_all mstore_ghost_frame >>
  disch_then (qspecl_then [`PG`,`G`,`sa.cs_next_id`] strip_assume_tac) >>
  suspend "scratch_path"
QED

Resume emit_scratch_word_counted[scratch_path]:
  qabbrev_tac `tn' = step_taint (mk_inst sa.cs_next_id MSTORE [Var dst; value] [])
    s (mstore (w2n a) w s) tn` >>
  qabbrev_tac `t = (mstore (w2n a) w s) with vs_inst_idx := SUC s.vs_inst_idx` >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 G tn' (OK t)` by
    (simp_tac pure_ss [Abbr `t`, Abbr `tn'`] >>
     `~(mstore (w2n a) w s).vs_halted` by simp[mstore_def] >>
     `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
     `(mk_inst sa.cs_next_id MSTORE [Var dst; value] []).inst_opcode <> INVOKE /\
      ~is_terminator (mk_inst sa.cs_next_id MSTORE [Var dst; value] []).inst_opcode /\
      (mk_inst sa.cs_next_id MSTORE [Var dst; value] []).inst_opcode <> GAS` by
       simp[mk_inst_def, is_terminator_def] >>
     drule_all gas_path_ptr_one_step >>
     disch_then (qspec_then `PG` mp_tac) >>
     simp[mk_inst_def, is_terminator_def]) >>
  qexistsl_tac [`t`,`tn'`] >>
  simp[Abbr `t`, mstore_mem_word_at_same, lookup_var_def] >>
  conj_tac
  >- gvs[ptr_covers_def, mstore_def, op_taint_def] >>
  conj_tac >- gvs[ptr_covers_def, mstore_def, op_taint_def, lookup_var_def] >>
  simp[Abbr `tn'`, step_taint_def, imm_taint_def, mk_inst_def] >>
  simp[mstore_def]
QED

Finalise emit_scratch_word_counted

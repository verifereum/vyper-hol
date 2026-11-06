(* Checked size-slot and ABI payload boundaries, shared by raise and assert. *)
Theory reasonEncoderTailPtr
Ancestors
  reasonTupleCopyPtr reasonPrefixPtr typedCopyPtr ghostPcTransportPtr
  venomExecSemantics venomState venomInst ptrDiscipline bodyPtrDefs
  emitHelper compileEnv fragExec finite_map words list fragExecPtr fragGasPathPtr

Theorem reason_encoder_mstore_path_ptr:
  emit_void MSTORE [Var dst;value] sa = ((),sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  lookup_var dst s = SOME a /\ eval_operand value s = SOME w /\
  op_taint tn value = {} /\ ptr_covers G tn dst s 32 ==>
  gas_path_ptr D 0 ctx func PG G tn s 0
    (step_prov PG G (mk_inst sa.cs_next_id MSTORE [Var dst;value] [])
      (mstore (w2n a) w s))
    (step_taint (mk_inst sa.cs_next_id MSTORE [Var dst;value] []) s
      (mstore (w2n a) w s) tn)
    (OK (mstore (w2n a) w s with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >> irule reason_encoder_emit_path_ptr >>
  simp[GSYM emit_void_def, is_terminator_def] >> conj_tac
  >- (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
      simp[mk_inst_def, eval_operand_def, exec_write2_def]) >>
  conj_tac
  >- (qexists_tac `sb` >> fs[emit_void_def, emit_inst_def]) >>
  irule ptr_inst_ok_mstore >> simp[]
QED

Theorem reason_encoder_mstore_resources_ptr:
  emit_void MSTORE [Var dst;value] sa = ((),sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  lookup_var dst s = SOME a /\ eval_operand value s = SOME w /\
  op_taint tn value = {} /\ ptr_covers G tn dst s 32 ==>
  ?tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 G tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    sf.vs_memory = (mstore (w2n a) w s).vs_memory /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_data_section = s.vs_data_section /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    mload (w2n a) sf = w /\
    (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tnf.t_mem) /\
    tnf.t_mem = tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a + 32} /\
    (!p. lookup_var p sf = lookup_var p s /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    (!p k. ptr_covers G tn p s k ==> ptr_covers G tnf p sf k)
Proof
  strip_tac >>
  qabbrev_tac `t = mstore (w2n a) w s` >>
  qabbrev_tac `tnf = step_taint
    (mk_inst sa.cs_next_id MSTORE [Var dst;value] []) s t tn` >>
  `step_prov PG G (mk_inst sa.cs_next_id MSTORE [Var dst;value] []) t = G` by
    (drule_all (cj 1 mstore_ghost_frame) >>
     disch_then (qspecl_then [`PG`, `G`, `sa.cs_next_id`] mp_tac) >>
     simp[Abbr `t`]) >>
  `tnf.t_var = tn.t_var /\ tnf.t_stor = tn.t_stor /\
   tnf.t_trans = tn.t_trans /\
   tnf.t_mem = tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a + 32}` by
    (drule_all mstore_ghost_frame >>
     disch_then (qspecl_then [`PG`, `G`, `sa.cs_next_id`] mp_tac) >>
     simp[Abbr `tnf`, Abbr `t`]) >>
  qexistsl_tac [`tnf`, `t with vs_inst_idx := SUC s.vs_inst_idx`] >>
  conj_tac
  >- (drule_all reason_encoder_mstore_path_ptr >>
      disch_then (qspecl_then [`PG`, `D`] mp_tac) >>
      gvs[Abbr `t`, Abbr `tnf`]) >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts)` by
    (gvs[emit_void_def, emit_inst_def, fresh_id_def, emit_def,
         comp_bind_def, comp_ignore_bind_def, comp_return_def]) >>
  `mload (w2n a) (t with vs_inst_idx := SUC s.vs_inst_idx) = w` by
    (`mload (w2n a) (t with vs_inst_idx := SUC s.vs_inst_idx) =
      mload (w2n a) t` by simp[mload_def] >>
     simp[Abbr `t`, venomMemProofsTheory.mload_mstore_same_proof]) >>
  simp[Abbr `t`, mstore_def, write_memory_with_expansion_def,
       lookup_var_def, op_taint_def, ptr_covers_def,
       pred_setTheory.IN_DIFF, pred_setTheory.GSPECIFICATION]
QED

(* Size slots are initialized and later read through this same checked pair.
   The value is any clean scalar, not only the encoder's initial 32. *)
Theorem reason_encoder_store_load_ptr:
  emit_void MSTORE [Var dst;value] sa = ((),sm) /\
  emit_inst MLOAD [Var dst] [out] sm = ((),sb) /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\
  ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  lookup_var dst s = SOME a /\ eval_operand value s = SOME w /\
  op_taint tn value = {} /\ ptr_covers G tn dst s 32 ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var out sf = SOME w /\ op_taint tnf (Var out) = {} /\
    sf.vs_memory = (mstore (w2n a) w s).vs_memory /\
    tnf.t_mem = tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a + 32} /\
    (!p. p <> out ==>
      lookup_var p sf = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule_all reason_encoder_mstore_resources_ptr >>
  disch_then (qspecl_then [`PG`, `D`] (qx_choose_then `tn1`
    (qx_choose_then `s1` strip_assume_tac))) >>
  `lookup_var dst s1 = SOME a /\ ptr_covers G tn1 dst s1 32` by
    metis_tac[] >>
  drule_all reason_copy_mload_resources_ptr >>
  disch_then (qspecl_then [`PG`, `D`] (qx_choose_then `G2`
    (qx_choose_then `tn2` (qx_choose_then `s2` strip_assume_tac)))) >>
  qexistsl_tac [`G2`, `tn2`, `s2`] >> conj_tac
  >- metis_tac[gas_path_ptr_then, arithmeticTheory.ADD_CLAUSES] >>
  simp[] >> rpt strip_tac >> metis_tac[]
QED

(* Both literal and size-slot offsets use this boundary. Only the offset is
   required clean; provenance comes from the first ADD operand. *)
Theorem reason_encoder_offset_path_ptr:
  emit_inst ADD [Var root;offset] [out] sa = ((),sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  lookup_var root s = SOME a /\ eval_operand offset s = SOME d /\
  op_taint tn offset = {} /\ ptr_covers G tn root s capacity /\
  w2n d + k <= capacity /\ w2n a + w2n d < dimword (:256) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var out sf = SOME (a + d) /\ ptr_covers Gf tnf out sf k /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_data_section = s.vs_data_section /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    (!p. p <> out ==>
      lookup_var p sf = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `t = update_var out (a + d) s` >>
  qabbrev_tac `Gf = step_prov PG G
    (mk_inst sa.cs_next_id ADD [Var root;offset] [out]) t` >>
  qabbrev_tac `tnf = step_taint
    (mk_inst sa.cs_next_id ADD [Var root;offset] [out]) s t tn` >>
  qexistsl_tac [`Gf`, `tnf`, `t with vs_inst_idx := SUC s.vs_inst_idx`] >>
  `op_taint tn (Var root) = {}` by fs[ptr_covers_def] >>
  conj_tac
  >- (unabbrev_all_tac >> irule reason_copy_binop_path_ptr >>
      simp[eval_operand_def]) >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts)` by
    (gvs[emit_inst_def, fresh_id_def, emit_def, comp_bind_def,
         comp_ignore_bind_def, comp_return_def]) >>
  simp[Abbr `t`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  conj_tac >- suspend "covers" >> suspend "frame"
QED

Resume reason_encoder_offset_path_ptr[covers]:
  gvs[ptr_covers_def] >>
  simp[Abbr `Gf`, Abbr `tnf`, copy_len_binop_ghost_frame,
       ptr_covers_def, step_prov_def, set_prov_def, out_prov_def,
       first_prov_def, op_prov_def, mk_inst_def, FLOOKUP_UPDATE,
       update_var_def, lookup_var_def, w2n_add_2] >> decide_tac
QED

Resume reason_encoder_offset_path_ptr[frame]:
  simp[Abbr `tnf`, copy_len_binop_ghost_frame] >>
  rpt strip_tac >>
  simp[Abbr `Gf`, step_prov_def, set_prov_def,
       out_prov_def, step_taint_def, set_var_taint_def, mk_inst_def,
       op_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
  Cases_on `first_prov G [Var root;offset]` >> simp[FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]
QED

Finalise reason_encoder_offset_path_ptr

(* The encoder reads its dynamic tuple offset from the size slot, then adds
   that clean scalar to the payload pointer. *)
Theorem reason_encoder_load_offset_ptr:
  emit_inst MLOAD [Var slot] [off] sa = ((),sm) /\
  emit_inst ADD [Var root;Var off] [out] sm = ((),sb) /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\
  ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  lookup_var slot s = SOME addr /\ ptr_covers G tn slot s 32 /\
  (!i. w2n addr <= i /\ i < w2n addr + 32 ==> i NOTIN tn.t_mem) /\
  mload (w2n addr) s = d /\ lookup_var root s = SOME a /\
  ptr_covers G tn root s capacity /\ root <> off /\
  w2n d + k <= capacity /\ w2n a + w2n d < dimword (:256) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var out sf = SOME (a + d) /\ ptr_covers Gf tnf out sf k /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    (!p. p <> off /\ p <> out ==>
      lookup_var p sf = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    (off <> out ==> lookup_var off sf = SOME d /\ op_taint tnf (Var off) = {})
Proof
  strip_tac >> drule_all reason_copy_mload_resources_ptr >>
  disch_then (qspecl_then [`PG`, `D`] (qx_choose_then `G1`
    (qx_choose_then `tn1` (qx_choose_then `s1` strip_assume_tac)))) >>
  `lookup_var root s1 = SOME a /\ ptr_covers G1 tn1 root s1 capacity` by
    (gvs[ptr_covers_def, op_taint_def] >> metis_tac[]) >>
  `eval_operand (Var off) s1 = SOME d` by simp[eval_operand_def] >>
  drule_all reason_encoder_offset_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] (qx_choose_then `G2`
    (qx_choose_then `tn2` (qx_choose_then `s2` strip_assume_tac)))) >>
  qexistsl_tac [`G2`, `tn2`, `s2`] >> conj_tac
  >- metis_tac[gas_path_ptr_then, arithmeticTheory.ADD_CLAUSES] >>
  simp[] >> rpt strip_tac >> metis_tac[]
QED

(* The four pointer-setup instructions after size-slot initialization. *)
Theorem reason_encoder_pointer_setup_ptr:
  emit_inst ADD [Var tuple;Lit 0w] [src] sa = ((),c1) /\
  emit_inst ADD [Var payload;Lit 0w] [head] c1 = ((),c2) /\
  emit_inst MLOAD [Var slot] [off] c2 = ((),c3) /\
  emit_inst ADD [Var payload;Var off] [tail] c3 = ((),sb) /\
  fn_has_code sa c1 func /\ fn_has_code c1 c2 func /\
  fn_has_code c2 c3 func /\ fn_has_code c3 sb func /\
  ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  lookup_var tuple s = SOME a /\ ptr_covers G tn tuple s tuple_capacity /\
  lookup_var payload s = SOME b /\ ptr_covers G tn payload s capacity /\
  lookup_var slot s = SOME addr /\ ptr_covers G tn slot s 32 /\
  (!i. w2n addr <= i /\ i < w2n addr + 32 ==> i NOTIN tn.t_mem) /\
  mload (w2n addr) s = 32w /\ 32 <= capacity /\
  w2n b + 32 < dimword (:256) /\
  (!p. p = payload \/ p = slot ==> p <> src /\ p <> head /\ p <> off) /\
  src <> head /\ src <> off /\ src <> tail /\
  head <> off /\ head <> tail ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var src sf = SOME a /\ ptr_covers Gf tnf src sf tuple_capacity /\
    lookup_var head sf = SOME b /\ ptr_covers Gf tnf head sf capacity /\
    lookup_var tail sf = SOME (b + 32w) /\
    ptr_covers Gf tnf tail sf (capacity - 32) /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    (!p. p <> src /\ p <> head /\ p <> off /\ p <> tail ==>
      lookup_var p sf = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    (off <> tail ==> lookup_var off sf = SOME 32w /\ op_taint tnf (Var off) = {})
Proof
  strip_tac >>
  drule_all (SRULE [eval_operand_def, op_taint_def, w2n_lt]
    (Q.INST [`offset` |-> `Lit 0w`, `d` |-> `0w`,
             `k` |-> `tuple_capacity`, `capacity` |-> `tuple_capacity`]
      reason_encoder_offset_path_ptr)) >>
  disch_then (qspecl_then [`PG`, `D`] (qx_choose_then `G1`
    (qx_choose_then `tn1` (qx_choose_then `s1` strip_assume_tac)))) >>
  `lookup_var payload s1 = SOME b /\ ptr_covers G1 tn1 payload s1 capacity` by
    (gvs[ptr_covers_def, op_taint_def] >> metis_tac[]) >>
  drule_all (SRULE [eval_operand_def, op_taint_def, w2n_lt]
    (Q.INST [`offset` |-> `Lit 0w`, `d` |-> `0w`, `k` |-> `capacity`]
      reason_encoder_offset_path_ptr)) >>
  disch_then (qspecl_then [`PG`, `D`] (qx_choose_then `G2`
    (qx_choose_then `tn2` (qx_choose_then `s2` strip_assume_tac)))) >>
  `lookup_var payload s2 = SOME b /\ ptr_covers G2 tn2 payload s2 capacity /\
   lookup_var slot s2 = SOME addr /\ ptr_covers G2 tn2 slot s2 32 /\
   mload (w2n addr) s2 = 32w /\
   (!i. w2n addr <= i /\ i < w2n addr + 32 ==> i NOTIN tn2.t_mem)` by
    (gvs[ptr_covers_def, mload_def, op_taint_def] >> metis_tac[]) >>
  `payload <> off /\ 32 + (capacity - 32) <= capacity` by
    (conj_tac >- metis_tac[] >> decide_tac) >>
  `w2n (32w : bytes32) = 32` by simp[w2n_n2w, dimword_def] >>
  qpat_assum `w2n (32w : bytes32) = 32` (fn th =>
    drule_all (SRULE [th] (Q.INST
      [`d` |-> `32w`, `k` |-> `capacity - 32`] reason_encoder_load_offset_ptr))) >>
  disch_then (qspecl_then [`PG`, `D`] (qx_choose_then `G3`
    (qx_choose_then `tn3` (qx_choose_then `s3` strip_assume_tac)))) >>
  qexistsl_tac [`G3`, `tn3`, `s3`] >> conj_tac
  >- suspend "path" >> suspend "resources"
QED

Resume reason_encoder_pointer_setup_ptr[path]:
  metis_tac[gas_path_ptr_then, arithmeticTheory.ADD_CLAUSES]
QED

Resume reason_encoder_pointer_setup_ptr[resources]:
  simp[] >> rpt strip_tac >>
  gvs[ptr_covers_def, op_taint_def, WORD_ADD_0] >> metis_tac[]
QED

Finalise reason_encoder_pointer_setup_ptr

(* Length load, rounding and the checked terminating zero word of the tail.
   Bounds are stated on the computed word so callers can use string-size facts. *)
Theorem reason_encoder_tail_zero_ptr:
  emit_inst MLOAD [Var src] [len] sa = ((),c1) /\
  emit_inst ADD [Var len;Lit 31w] [tmp] c1 = ((),c2) /\
  emit_inst AND [Var tmp;Lit (i2w (-32))] [rounded] c2 = ((),c3) /\
  emit_inst ADD [Var tail;Var rounded] [last] c3 = ((),c4) /\
  emit_void MSTORE [Var last;Lit 0w] c4 = ((),sb) /\
  fn_has_code sa c1 func /\ fn_has_code c1 c2 func /\
  fn_has_code c2 c3 func /\ fn_has_code c3 c4 func /\
  fn_has_code c4 sb func /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  lookup_var src s = SOME a /\ ptr_covers G tn src s 32 /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) /\
  mload (w2n a) s = n /\ lookup_var tail s = SOME b /\
  ptr_covers G tn tail s capacity /\
  w2n ((n + 31w) && i2w (-32)) + 32 <= capacity /\
  w2n b + w2n ((n + 31w) && i2w (-32)) < dimword (:256) /\
  tail <> len /\ tail <> tmp /\ tail <> rounded /\
  len <> tmp /\ len <> rounded /\ len <> last ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var len sf = SOME n /\ op_taint tnf (Var len) = {} /\
    sf.vs_memory = (mstore (w2n (b + ((n + 31w) && i2w (-32)))) 0w s).vs_memory /\
    tnf.t_mem = tn.t_mem DIFF
      {i | w2n (b + ((n + 31w) && i2w (-32))) <= i /\
           i < w2n (b + ((n + 31w) && i2w (-32))) + 32} /\
    (!p. p <> len /\ p <> tmp /\ p <> rounded /\ p <> last ==>
      lookup_var p sf = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule_all reason_load_round_ptr >>
  disch_then (qspecl_then [`PG`, `D`] (qx_choose_then `G1`
    (qx_choose_then `tn1` (qx_choose_then `s1` strip_assume_tac)))) >>
  `lookup_var tail s1 = SOME b /\ ptr_covers G1 tn1 tail s1 capacity /\
   eval_operand (Var rounded) s1 = SOME ((n + 31w) && i2w (-32))` by
    (gvs[ptr_covers_def, eval_operand_def] >> metis_tac[]) >>
  drule_all reason_encoder_offset_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] (qx_choose_then `G2`
    (qx_choose_then `tn2` (qx_choose_then `s2` strip_assume_tac)))) >>
  `eval_operand (Lit 0w) s2 = SOME 0w /\ op_taint tn2 (Lit 0w) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all reason_encoder_mstore_resources_ptr >>
  disch_then (qspecl_then [`PG`, `D`] (qx_choose_then `tn3`
    (qx_choose_then `s3` strip_assume_tac))) >>
  qexistsl_tac [`G2`, `tn3`, `s3`] >> conj_tac
  >- suspend "path" >> suspend "resources"
QED

Resume reason_encoder_tail_zero_ptr[path]:
  metis_tac[gas_path_ptr_then, arithmeticTheory.ADD_CLAUSES]
QED

Resume reason_encoder_tail_zero_ptr[resources]:
  gvs[] >> simp[mstore_def, write_memory_with_expansion_def] >>
  rpt strip_tac >> metis_tac[]
QED

Finalise reason_encoder_tail_zero_ptr

(* Counted copy with the actual transported memory taint and live registers.
   Unlike the robust-string tuple interface, this permits an exact byte cnt. *)
Theorem reason_encoder_mcopy_resources_ptr:
  emit_void MCOPY [Var dst;Var src;cnt_op] sa = ((),sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  eval_operand (Var dst) s = SOME b /\ eval_operand (Var src) s = SOME a /\
  eval_operand cnt_op s = SOME n /\ op_taint tn cnt_op = {} /\
  ptr_covers G tn dst s (w2n n) /\ ptr_covers G tn src s (w2n n) ==>
  ?tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 G tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    sf.vs_memory = (mcopy (w2n b) (w2n a) (w2n n) s).vs_memory /\
    tnf.t_mem =
      (tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b + w2n n}) UNION
      {w2n b + i | i < w2n n /\ w2n a + i IN tn.t_mem} /\
    (!p. lookup_var p sf = lookup_var p s /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    (!p k. ptr_covers G tn p s k ==> ptr_covers G tnf p sf k)
Proof
  strip_tac >>
  qabbrev_tac `t = mcopy (w2n b) (w2n a) (w2n n) s` >>
  qabbrev_tac `tnf = step_taint
    (mk_inst sa.cs_next_id MCOPY [Var dst;Var src;cnt_op] []) s t tn` >>
  `step_prov PG G (mk_inst sa.cs_next_id MCOPY [Var dst;Var src;cnt_op] []) t = G` by
    (simp[Abbr `t`] >> irule (cj 1 mcopy_operand_ghost_frame) >> simp[]) >>
  `tnf.t_var = tn.t_var /\
   tnf.t_mem =
      (tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b + w2n n}) UNION
      {w2n b + i | i < w2n n /\ w2n a + i IN tn.t_mem}` by
    (simp[Abbr `tnf`, Abbr `t`] >> conj_tac
     >- (irule (cj 2 mcopy_operand_ghost_frame) >> simp[]) >>
     irule (SRULE [arithmeticTheory.ADD_COMM] (cj 5 mcopy_operand_ghost_frame)) >> simp[]) >>
  qexistsl_tac [`tnf`, `t with vs_inst_idx := SUC s.vs_inst_idx`] >>
  conj_tac
  >- (drule_all reason_mcopy_path_ptr >>
      disch_then (qspecl_then [`PG`, `D`] mp_tac) >>
      gvs[Abbr `t`, Abbr `tnf`]) >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts)` by
    (gvs[emit_void_def, emit_inst_def, fresh_id_def, emit_def,
         comp_bind_def, comp_ignore_bind_def, comp_return_def]) >>
  simp[Abbr `t`, mcopy_def, write_memory_with_expansion_def,
       lookup_var_def, op_taint_def, ptr_covers_def]
QED

(* Exact (not padded) length-word-plus-data copy after zeroing the tail. *)
Theorem reason_encoder_exact_copy_ptr:
  emit_inst ADD [Lit 32w;Var len] [cnt] sa = ((),c1) /\
  emit_void MCOPY [Var dst;Var src;Var cnt] c1 = ((),sb) /\
  fn_has_code sa c1 func /\ fn_has_code c1 sb func /\
  ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  lookup_var len s = SOME n /\ op_taint tn (Var len) = {} /\
  lookup_var dst s = SOME b /\ lookup_var src s = SOME a /\
  ptr_covers G tn dst s (w2n (32w + n)) /\
  ptr_covers G tn src s (w2n (32w + n)) /\
  src <> cnt /\ dst <> cnt /\ len <> cnt ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var len sf = SOME n /\ op_taint tnf (Var len) = {} /\
    sf.vs_memory = (mcopy (w2n b) (w2n a) (w2n (32w + n)) s).vs_memory /\
    tnf.t_mem =
      (tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b + w2n (32w + n)}) UNION
      {w2n b + i | i < w2n (32w + n) /\ w2n a + i IN tn.t_mem} /\
    (!p. p <> cnt ==>
      lookup_var p sf = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `eval_operand (Var len) s = SOME n /\
   eval_operand (Lit 32w) s = SOME 32w /\
   op_taint tn (Lit 32w) = {}` by simp[eval_operand_def, op_taint_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`, `f` |-> `word_add`]
    reason_copy_binop_resources_ptr)) >>
  disch_then (qspecl_then [`PG`, `G`, `D`] (qx_choose_then `G1`
    (qx_choose_then `tn1` (qx_choose_then `s1` strip_assume_tac)))) >>
  `eval_operand (Var dst) s1 = SOME b /\ eval_operand (Var src) s1 = SOME a /\
   eval_operand (Var cnt) s1 = SOME (32w + n) /\
   ptr_covers G1 tn1 dst s1 (w2n (32w + n)) /\
   ptr_covers G1 tn1 src s1 (w2n (32w + n))` by
    (gvs[ptr_covers_def, eval_operand_def] >> metis_tac[]) >>
  drule_all reason_encoder_mcopy_resources_ptr >>
  disch_then (qspecl_then [`PG`, `D`] (qx_choose_then `tn2`
    (qx_choose_then `s2` strip_assume_tac))) >>
  qexistsl_tac [`G1`, `tn2`, `s2`] >> conj_tac
  >- metis_tac[gas_path_ptr_then, arithmeticTheory.ADD_CLAUSES] >>
  gvs[mcopy_def, write_memory_with_expansion_def] >> rpt strip_tac >> metis_tac[]
QED

Theorem reason_encoder_item_length_ptr:
  emit_inst ADD [Var len;Lit 31w] [tmp] sa = ((),c1) /\
  emit_inst AND [Var tmp;Lit (i2w (-32))] [rounded] c1 = ((),c2) /\
  emit_inst ADD [Lit 32w;Var rounded] [item] c2 = ((),sb) /\
  fn_has_code sa c1 func /\ fn_has_code c1 c2 func /\
  fn_has_code c2 sb func /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  lookup_var len s = SOME n /\ op_taint tn (Var len) = {} ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var item sf = SOME (32w + ((n + 31w) && i2w (-32))) /\
    op_taint tnf (Var item) = {} /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    (!p. p <> tmp /\ p <> rounded /\ p <> item ==>
      lookup_var p sf = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule_all reason_round_scalar_ptr >>
  disch_then (qspecl_then [`PG`, `G`, `D`] (qx_choose_then `G1`
    (qx_choose_then `tn1` (qx_choose_then `s1` strip_assume_tac)))) >>
  `eval_operand (Var rounded) s1 = SOME ((n + 31w) && i2w (-32)) /\
   eval_operand (Lit 32w) s1 = SOME 32w /\
   op_taint tn1 (Lit 32w) = {}` by simp[eval_operand_def, op_taint_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`, `f` |-> `word_add`]
    reason_copy_binop_resources_ptr)) >>
  disch_then (qspecl_then [`PG`, `G1`, `D`] (qx_choose_then `G2`
    (qx_choose_then `tn2` (qx_choose_then `s2` strip_assume_tac)))) >>
  qexistsl_tac [`G2`, `tn2`, `s2`] >> conj_tac
  >- metis_tac[gas_path_ptr_then, arithmeticTheory.ADD_CLAUSES] >>
  simp[] >> rpt strip_tac >> metis_tac[]
QED

(* Final ABI head word and size_out-size update/readback, compiler lines 181-184. *)
Theorem reason_encoder_finish_size_ptr:
  emit_void MSTORE [Var head;Var off] sa = ((),c1) /\
  emit_inst ADD [Var off;Var item] [size_out] c1 = ((),c2) /\
  emit_void MSTORE [Var slot;Var size_out] c2 = ((),c3) /\
  emit_inst MLOAD [Var slot] [encoded] c3 = ((),sb) /\
  fn_has_code sa c1 func /\ fn_has_code c1 c2 func /\
  fn_has_code c2 c3 func /\ fn_has_code c3 sb func /\
  ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  lookup_var head s = SOME h /\ ptr_covers G tn head s 32 /\
  lookup_var slot s = SOME a /\ ptr_covers G tn slot s 32 /\
  lookup_var off s = SOME d /\ op_taint tn (Var off) = {} /\
  lookup_var item s = SOME z /\ op_taint tn (Var item) = {} /\
  slot <> size_out ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var encoded sf = SOME (d + z) /\ op_taint tnf (Var encoded) = {} /\
    sf.vs_memory = (mstore (w2n a) (d + z) (mstore (w2n h) d s)).vs_memory /\
    tnf.t_mem = (tn.t_mem DIFF {i | w2n h <= i /\ i < w2n h + 32}) DIFF
      {i | w2n a <= i /\ i < w2n a + 32} /\
    (!p. p <> size_out /\ p <> encoded ==>
      lookup_var p sf = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `eval_operand (Var off) s = SOME d` by simp[eval_operand_def] >>
  drule_all reason_encoder_mstore_resources_ptr >>
  disch_then (qspecl_then [`PG`, `D`] (qx_choose_then `tn1`
    (qx_choose_then `s1` strip_assume_tac))) >>
  `eval_operand (Var off) s1 = SOME d /\ op_taint tn1 (Var off) = {} /\
   eval_operand (Var item) s1 = SOME z /\ op_taint tn1 (Var item) = {}` by
    (simp[eval_operand_def] >> metis_tac[]) >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`, `f` |-> `word_add`]
    reason_copy_binop_resources_ptr)) >>
  disch_then (qspecl_then [`PG`, `G`, `D`] (qx_choose_then `G2`
    (qx_choose_then `tn2` (qx_choose_then `s2` strip_assume_tac)))) >>
  `lookup_var slot s2 = SOME a /\ ptr_covers G2 tn2 slot s2 32 /\
   eval_operand (Var size_out) s2 = SOME (d + z)` by
    (gvs[ptr_covers_def, eval_operand_def] >> metis_tac[]) >>
  drule_all reason_encoder_store_load_ptr >>
  disch_then (qspecl_then [`PG`, `D`] (qx_choose_then `G3`
    (qx_choose_then `tn3` (qx_choose_then `s3` strip_assume_tac)))) >>
  qexistsl_tac [`G3`, `tn3`, `s3`] >> conj_tac
  >- suspend "path" >> suspend "resources"
QED

Resume reason_encoder_finish_size_ptr[path]:
  metis_tac[gas_path_ptr_then, arithmeticTheory.ADD_CLAUSES]
QED

Resume reason_encoder_finish_size_ptr[resources]:
  simp[] >> PURE_ONCE_REWRITE_TAC[mstore_def] >> simp[]
QED

Finalise reason_encoder_finish_size_ptr

(* Once the clean length is captured, the source need not remain robust:
   zeroing and copying may transport arbitrary payload taint. *)
Theorem reason_encoder_tail_copy_ptr:
  emit_inst MLOAD [Var src] [len] sa = ((),c1) /\
  emit_inst ADD [Var len;Lit 31w] [tmp] c1 = ((),c2) /\
  emit_inst AND [Var tmp;Lit (i2w (-32))] [rounded] c2 = ((),c3) /\
  emit_inst ADD [Var tail;Var rounded] [last] c3 = ((),c4) /\
  emit_void MSTORE [Var last;Lit 0w] c4 = ((),c5) /\
  emit_inst ADD [Lit 32w;Var len] [cnt] c5 = ((),c6) /\
  emit_void MCOPY [Var tail;Var src;Var cnt] c6 = ((),sb) /\
  fn_has_code sa c1 func /\ fn_has_code c1 c2 func /\
  fn_has_code c2 c3 func /\ fn_has_code c3 c4 func /\
  fn_has_code c4 c5 func /\ fn_has_code c5 c6 func /\
  fn_has_code c6 sb func /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  lookup_var src s = SOME a /\ ptr_covers G tn src s 32 /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) /\
  mload (w2n a) s = n /\ lookup_var tail s = SOME b /\
  ptr_covers G tn tail s capacity /\
  ptr_covers G tn src s (w2n (32w + n)) /\
  w2n (32w + n) <= capacity /\
  w2n ((n + 31w) && i2w (-32)) + 32 <= capacity /\
  w2n b + w2n ((n + 31w) && i2w (-32)) < dimword (:256) /\
  (!p. MEM p [src;tail] ==> ~MEM p [len;tmp;rounded;last;cnt]) /\
  len <> tmp /\ len <> rounded /\ len <> last /\ len <> cnt ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var len sf = SOME n /\ op_taint tnf (Var len) = {} /\
    (!p. ~MEM p [len;tmp;rounded;last;cnt] ==>
      lookup_var p sf = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `tail <> len /\ tail <> tmp /\ tail <> rounded /\
   tail <> last /\ tail <> cnt /\
   src <> len /\ src <> tmp /\ src <> rounded /\ src <> last /\ src <> cnt` by
    (fs[] >> metis_tac[]) >>
  drule_all reason_encoder_tail_zero_ptr >>
  disch_then (qspecl_then [`PG`, `D`] (qx_choose_then `G1`
    (qx_choose_then `tn1` (qx_choose_then `s1` strip_assume_tac)))) >>
  `lookup_var src s1 = SOME a /\ lookup_var tail s1 = SOME b /\
   ptr_covers G1 tn1 src s1 (w2n (32w + n)) /\
   ptr_covers G1 tn1 tail s1 (w2n (32w + n))` by
    (gvs[ptr_covers_def] >> rpt strip_tac >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  drule_all reason_encoder_exact_copy_ptr >>
  disch_then (qspecl_then [`PG`, `D`] (qx_choose_then `G2`
    (qx_choose_then `tn2` (qx_choose_then `s2` strip_assume_tac)))) >>
  qexistsl_tac [`G2`, `tn2`, `s2`] >> conj_tac
  >- metis_tac[gas_path_ptr_then, arithmeticTheory.ADD_CLAUSES] >>
  simp[] >> rpt strip_tac >> fs[] >> metis_tac[]
QED

Theorem reason_encoder_size_suffix_ptr:
  emit_inst ADD [Var len;Lit 31w] [tmp] sa = ((),c1) /\
  emit_inst AND [Var tmp;Lit (i2w (-32))] [rounded] c1 = ((),c2) /\
  emit_inst ADD [Lit 32w;Var rounded] [item] c2 = ((),c3) /\
  emit_void MSTORE [Var head;Var off] c3 = ((),c4) /\
  emit_inst ADD [Var off;Var item] [size_out] c4 = ((),c5) /\
  emit_void MSTORE [Var slot;Var size_out] c5 = ((),c6) /\
  emit_inst MLOAD [Var slot] [encoded] c6 = ((),sb) /\
  fn_has_code sa c1 func /\ fn_has_code c1 c2 func /\
  fn_has_code c2 c3 func /\ fn_has_code c3 c4 func /\
  fn_has_code c4 c5 func /\ fn_has_code c5 c6 func /\
  fn_has_code c6 sb func /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  lookup_var len s = SOME n /\ op_taint tn (Var len) = {} /\
  lookup_var head s = SOME h /\ ptr_covers G tn head s 32 /\
  lookup_var slot s = SOME a /\ ptr_covers G tn slot s 32 /\
  lookup_var off s = SOME d /\ op_taint tn (Var off) = {} /\
  (!p. MEM p [head;slot;off] ==> ~MEM p [tmp;rounded;item]) /\
  slot <> size_out ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var encoded sf = SOME (d + (32w + ((n + 31w) && i2w (-32)))) /\
    op_taint tnf (Var encoded) = {} /\
    (!p. ~MEM p [tmp;rounded;item;size_out;encoded] ==>
      lookup_var p sf = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule_all reason_encoder_item_length_ptr >>
  disch_then (qspecl_then [`PG`, `G`, `D`] (qx_choose_then `G1`
    (qx_choose_then `tn1` (qx_choose_then `s1` strip_assume_tac)))) >>
  `lookup_var head s1 = SOME h /\ ptr_covers G1 tn1 head s1 32 /\
   lookup_var slot s1 = SOME a /\ ptr_covers G1 tn1 slot s1 32 /\
   lookup_var off s1 = SOME d /\ op_taint tn1 (Var off) = {}` by
    (gvs[ptr_covers_def] >> fs[] >> metis_tac[]) >>
  drule_all reason_encoder_finish_size_ptr >>
  disch_then (qspecl_then [`PG`, `D`] (qx_choose_then `G2`
    (qx_choose_then `tn2` (qx_choose_then `s2` strip_assume_tac)))) >>
  qexistsl_tac [`G2`, `tn2`, `s2`] >> conj_tac
  >- metis_tac[gas_path_ptr_then, arithmeticTheory.ADD_CLAUSES] >>
  simp[] >> rpt strip_tac >> fs[] >> metis_tac[]
QED

(* The initialized pointer setup feeds two independently checked blocks.
   This boundary exports only the scalar and live operands needed by REVERT;
   there is deliberately no cleanliness requirement on the encoded bytes. *)
Theorem reason_encoder_payload_tail_ptr:
  emit_inst MLOAD [Var src] [len] sa = ((),c1) /\
  emit_inst ADD [Var len;Lit 31w] [tmp0] c1 = ((),c2) /\
  emit_inst AND [Var tmp0;Lit (i2w (-32))] [rounded0] c2 = ((),c3) /\
  emit_inst ADD [Var tail;Var rounded0] [last] c3 = ((),c4) /\
  emit_void MSTORE [Var last;Lit 0w] c4 = ((),c5) /\
  emit_inst ADD [Lit 32w;Var len] [cnt] c5 = ((),c6) /\
  emit_void MCOPY [Var tail;Var src;Var cnt] c6 = ((),c7) /\
  emit_inst ADD [Var len;Lit 31w] [tmp1] c7 = ((),c8) /\
  emit_inst AND [Var tmp1;Lit (i2w (-32))] [rounded1] c8 = ((),c9) /\
  emit_inst ADD [Lit 32w;Var rounded1] [item] c9 = ((),c10) /\
  emit_void MSTORE [Var head;Var off] c10 = ((),c11) /\
  emit_inst ADD [Var off;Var item] [size_out] c11 = ((),c12) /\
  emit_void MSTORE [Var slot;Var size_out] c12 = ((),c13) /\
  emit_inst MLOAD [Var slot] [encoded] c13 = ((),sb) /\
  fn_has_code sa c1 func /\ fn_has_code c1 c2 func /\
  fn_has_code c2 c3 func /\ fn_has_code c3 c4 func /\
  fn_has_code c4 c5 func /\ fn_has_code c5 c6 func /\
  fn_has_code c6 c7 func /\ fn_has_code c7 c8 func /\
  fn_has_code c8 c9 func /\ fn_has_code c9 c10 func /\
  fn_has_code c10 c11 func /\ fn_has_code c11 c12 func /\
  fn_has_code c12 c13 func /\ fn_has_code c13 sb func /\
  ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  lookup_var src s = SOME a /\ ptr_covers G tn src s 32 /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) /\
  mload (w2n a) s = n /\ lookup_var tail s = SOME b /\
  ptr_covers G tn tail s capacity /\
  ptr_covers G tn src s (w2n (32w + n)) /\
  w2n (32w + n) <= capacity /\
  w2n ((n + 31w) && i2w (-32)) + 32 <= capacity /\
  w2n b + w2n ((n + 31w) && i2w (-32)) < dimword (:256) /\
  lookup_var head s = SOME h /\ ptr_covers G tn head s 32 /\
  lookup_var slot s = SOME addr /\ ptr_covers G tn slot s 32 /\
  lookup_var off s = SOME d /\ op_taint tn (Var off) = {} /\
  (!p. MEM p [src;tail;head;slot;off] ==>
    ~MEM p [len;tmp0;rounded0;last;cnt;tmp1;rounded1;item]) /\
  len <> tmp0 /\ len <> rounded0 /\ len <> last /\ len <> cnt /\
  slot <> size_out ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var encoded sf = SOME (d + (32w + ((n + 31w) && i2w (-32)))) /\
    op_taint tnf (Var encoded) = {} /\
    (!p. ~MEM p [len;tmp0;rounded0;last;cnt;tmp1;rounded1;item;size_out;encoded] ==>
      lookup_var p sf = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `!p. MEM p [src;tail] ==> ~MEM p [len;tmp0;rounded0;last;cnt]` by
    (fs[] >> metis_tac[]) >>
  drule_all reason_encoder_tail_copy_ptr >>
  disch_then (qspecl_then [`PG`, `D`] (qx_choose_then `G1`
    (qx_choose_then `tn1` (qx_choose_then `s1` strip_assume_tac)))) >>
  `lookup_var head s1 = SOME h /\ ptr_covers G1 tn1 head s1 32 /\
   lookup_var slot s1 = SOME addr /\ ptr_covers G1 tn1 slot s1 32 /\
   lookup_var off s1 = SOME d /\ op_taint tn1 (Var off) = {}` by
    (gvs[ptr_covers_def] >> fs[] >> metis_tac[]) >>
  `!p. MEM p [head;slot;off] ==> ~MEM p [tmp1;rounded1;item]` by
    (fs[] >> metis_tac[]) >>
  drule_all reason_encoder_size_suffix_ptr >>
  disch_then (qspecl_then [`PG`, `D`] (qx_choose_then `G2`
    (qx_choose_then `tn2` (qx_choose_then `s2` strip_assume_tac)))) >>
  qexistsl_tac [`G2`, `tn2`, `s2`] >> conj_tac
  >- metis_tac[gas_path_ptr_then, arithmeticTheory.ADD_CLAUSES] >>
  simp[] >> rpt strip_tac >> fs[] >> metis_tac[]
QED

(* Combine the counted allocation edge with size-slot initialization.
   The allocation resources are supplied by reason_encoder_alloc_buffer_resources;
   they are not re-proved here. *)
Theorem reason_encoder_size_slot_init_ptr:
  compile_alloc_buffer 32 sa = (buf,c1) /\ buf.buf_operand = Var slot /\
  emit_void MSTORE [Var slot;Lit 32w] c1 = ((),sb) /\
  fn_has_code sa c1 func /\ fn_has_code c1 sb func /\
  ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit 32w] [slot]) s = OK t /\
  G1 = step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit 32w] [slot]) t /\
  tn1 = step_taint (mk_inst sa.cs_next_id ALLOCA [Lit 32w] [slot]) s t tn /\
  lookup_var slot t = SOME a /\ ptr_covers G1 tn1 slot t 32 ==>
  ?tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 G1 tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var slot sf = SOME a /\ ptr_covers G1 tnf slot sf 32 /\
    mload (w2n a) sf = 32w /\
    (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tnf.t_mem) /\
    sf.vs_memory = (mstore (w2n a) 32w t).vs_memory /\
    (!p. lookup_var p sf = lookup_var p t /\
      op_taint tnf (Var p) = op_taint tn1 (Var p)) /\
    (!p k. ptr_covers G1 tn1 p t k ==> ptr_covers G1 tnf p sf k)
Proof
  strip_tac >>
  `gas_path_ptr D 0 ctx func PG G tn s 0 G1 tn1
    (OK (t with vs_inst_idx := SUC s.vs_inst_idx))` by
    (drule_all reason_encoder_alloc_path_ptr >> simp[]) >>
  `t.vs_current_bb = s.vs_current_bb /\
   t.vs_inst_idx = s.vs_inst_idx /\ ~t.vs_halted` by
    (qpat_x_assum `step_inst_base _ _ = OK t` mp_tac >>
     PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def, exec_alloca_def] >>
     gvs[AllCaseEqs()] >> rpt strip_tac >>
     gvs[update_var_def]) >>
  `c1.cs_current_bb = sa.cs_current_bb /\
   LENGTH c1.cs_current_insts = SUC (LENGTH sa.cs_current_insts)` by
    (gvs[contextTheory.compile_alloc_buffer_def, emit_op_def, fresh_var_def,
         emit_inst_def, fresh_id_def, emit_def, comp_bind_def,
         comp_ignore_bind_def, comp_return_def]) >>
  qabbrev_tac `s1 = t with vs_inst_idx := SUC s.vs_inst_idx` >>
  `s1.vs_current_bb = c1.cs_current_bb /\
   s1.vs_inst_idx = LENGTH c1.cs_current_insts /\ ~s1.vs_halted /\
   lookup_var slot s1 = SOME a /\ ptr_covers G1 tn1 slot s1 32 /\
   eval_operand (Lit 32w) s1 = SOME 32w /\ op_taint tn1 (Lit 32w) = {}` by
    gvs[Abbr `s1`, lookup_var_def, eval_operand_def, op_taint_def,
        ptr_covers_def] >>
  drule_all reason_encoder_mstore_resources_ptr >>
  disch_then (qspecl_then [`PG`, `D`] (qx_choose_then `tn2`
    (qx_choose_then `s2` strip_assume_tac))) >>
  qexistsl_tac [`tn2`, `s2`] >> conj_tac
  >- (gvs[Abbr `s1`] >> metis_tac[gas_path_ptr_then, arithmeticTheory.ADD_CLAUSES]) >>
  simp[] >> conj_tac
  >- (PURE_ONCE_REWRITE_TAC[mstore_def] >> simp[Abbr `s1`]) >>
  gvs[Abbr `s1`, lookup_var_def, op_taint_def, ptr_covers_def] >>
  rpt strip_tac >> metis_tac[]
QED

(* Initialized size slots feed the shared pointer setup and payload suffix.
   The frame keeps the outer buffer operand live for the final REVERT. *)
Theorem reason_encoder_payload_ptr:
  emit_inst ADD [Var tuple;Lit 0w] [src] sa = ((),p1) /\
  emit_inst ADD [Var payload;Lit 0w] [head] p1 = ((),p2) /\
  emit_inst MLOAD [Var slot] [off] p2 = ((),p3) /\
  emit_inst ADD [Var payload;Var off] [tail] p3 = ((),sm) /\
  emit_inst MLOAD [Var src] [len] sm = ((),c1) /\
  emit_inst ADD [Var len;Lit 31w] [tmp0] c1 = ((),c2) /\
  emit_inst AND [Var tmp0;Lit (i2w (-32))] [rounded0] c2 = ((),c3) /\
  emit_inst ADD [Var tail;Var rounded0] [last] c3 = ((),c4) /\
  emit_void MSTORE [Var last;Lit 0w] c4 = ((),c5) /\
  emit_inst ADD [Lit 32w;Var len] [cnt] c5 = ((),c6) /\
  emit_void MCOPY [Var tail;Var src;Var cnt] c6 = ((),c7) /\
  emit_inst ADD [Var len;Lit 31w] [tmp1] c7 = ((),c8) /\
  emit_inst AND [Var tmp1;Lit (i2w (-32))] [rounded1] c8 = ((),c9) /\
  emit_inst ADD [Lit 32w;Var rounded1] [item] c9 = ((),c10) /\
  emit_void MSTORE [Var head;Var off] c10 = ((),c11) /\
  emit_inst ADD [Var off;Var item] [size_out] c11 = ((),c12) /\
  emit_void MSTORE [Var slot;Var size_out] c12 = ((),c13) /\
  emit_inst MLOAD [Var slot] [encoded] c13 = ((),sb) /\
  fn_has_code sa p1 func /\ fn_has_code p1 p2 func /\
  fn_has_code p2 p3 func /\ fn_has_code p3 sm func /\
  fn_has_code sm c1 func /\ fn_has_code c1 c2 func /\
  fn_has_code c2 c3 func /\ fn_has_code c3 c4 func /\
  fn_has_code c4 c5 func /\ fn_has_code c5 c6 func /\
  fn_has_code c6 c7 func /\ fn_has_code c7 c8 func /\
  fn_has_code c8 c9 func /\ fn_has_code c9 c10 func /\
  fn_has_code c10 c11 func /\ fn_has_code c11 c12 func /\
  fn_has_code c12 c13 func /\ fn_has_code c13 sb func /\
  ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  lookup_var tuple s = SOME a /\ ptr_covers G tn tuple s tuple_capacity /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) /\
  mload (w2n a) s = n /\
  lookup_var payload s = SOME b /\ ptr_covers G tn payload s capacity /\
  lookup_var slot s = SOME addr /\ ptr_covers G tn slot s 32 /\
  (!i. w2n addr <= i /\ i < w2n addr + 32 ==> i NOTIN tn.t_mem) /\
  mload (w2n addr) s = 32w /\ 32 <= capacity /\
  w2n b + 32 < dimword (:256) /\
  w2n (b + 32w) + w2n ((n + 31w) && i2w (-32)) < dimword (:256) /\
  32 <= tuple_capacity /\ w2n (32w + n) <= tuple_capacity /\
  w2n (32w + n) <= capacity - 32 /\
  w2n ((n + 31w) && i2w (-32)) + 32 <= capacity - 32 /\
  (!p. p = payload \/ p = slot ==> p <> src /\ p <> head /\ p <> off) /\
  slot <> tail /\ src <> head /\ src <> off /\ src <> tail /\
  head <> off /\ head <> tail /\ off <> tail /\
  (!p. MEM p [src;tail;head;slot;off] ==>
    ~MEM p [len;tmp0;rounded0;last;cnt;tmp1;rounded1;item]) /\
  len <> tmp0 /\ len <> rounded0 /\ len <> last /\ len <> cnt /\
  slot <> size_out ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var encoded sf = SOME (32w + (32w + ((n + 31w) && i2w (-32)))) /\
    op_taint tnf (Var encoded) = {} /\
    (!p. ~MEM p [src;head;off;tail;len;tmp0;rounded0;last;cnt;
                 tmp1;rounded1;item;size_out;encoded] ==>
      lookup_var p sf = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule_all reason_encoder_pointer_setup_ptr >>
  disch_then (qspecl_then [`PG`, `D`] (qx_choose_then `G1`
    (qx_choose_then `tn1` (qx_choose_then `s1` strip_assume_tac)))) >>
  `lookup_var slot s1 = SOME addr /\ ptr_covers G1 tn1 slot s1 32 /\
   lookup_var off s1 = SOME 32w /\ op_taint tn1 (Var off) = {} /\
   ptr_covers G1 tn1 src s1 32 /\
   ptr_covers G1 tn1 src s1 (w2n (32w + n)) /\
   ptr_covers G1 tn1 head s1 32 /\
   mload (w2n a) s1 = n /\
   (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn1.t_mem)` by
    (gvs[ptr_covers_def, mload_def, op_taint_def] >>
     rpt conj_tac >> metis_tac[arithmeticTheory.LESS_EQ_TRANS,
       arithmeticTheory.SUB_LESS_EQ]) >>
  qpat_assum `emit_inst MLOAD [Var src] [len] sm = _`
    (mp_then Any mp_tac reason_encoder_payload_tail_ptr) >>
  ntac 13 (disch_then drule) >>
  disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `D`] (qx_choose_then `G2`
    (qx_choose_then `tn2` (qx_choose_then `s2` strip_assume_tac)))) >>
  qexistsl_tac [`G2`, `tn2`, `s2`] >> conj_tac
  >- metis_tac[gas_path_ptr_then, arithmeticTheory.ADD_CLAUSES] >>
  simp[] >> rpt strip_tac >> fs[] >> metis_tac[]
QED

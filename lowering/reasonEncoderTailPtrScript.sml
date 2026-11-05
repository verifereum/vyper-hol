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
  `tnf.t_var = tn.t_var /\
   tnf.t_mem = tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a + 32}` by
    (simp[Abbr `tnf`, Abbr `t`] >> conj_tac
     >- (irule (cj 2 mstore_ghost_frame) >> simp[]) >>
     irule (cj 5 mstore_ghost_frame) >> simp[]) >>
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

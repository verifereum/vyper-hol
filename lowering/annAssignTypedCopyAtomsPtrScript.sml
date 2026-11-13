(* Concrete counted copy endpoints retain the ambient declaration frame. *)
Theory annAssignTypedCopyAtomsPtr
Ancestors
  assignBasePtrCopyFrame assignBasePtrCopyPath assignBasePtrBytesPost annAssignPtrLength annAssignPtrStore
  typedMemoryCopy typedCopyPtr fragGasPathPtr bodyPtrDefs context words
  compileEnv valueEncoding valueEncodingDefs venomState venomExecSemantics
  ptrDiscipline emitHelper finite_map venomInst augAssignPtrStore wordLoadStorePtr
  annAssignPtrBytestring

Theorem annassign_copy_memory_counted_ambient_ptr:
  !dst src n sa sb fn s d a G tn D ctx PG tv v.
    n < dimword (:256) /\
    compile_copy_memory (Var dst) (Var src) n sa = ((),sb) /\
    fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
    ~ctx_has_dalloca ctx /\ ptr_covers G tn dst s n /\
    ptr_covers G tn src s n /\
    lookup_var dst s = SOME d /\ lookup_var src s = SOME a /\
    val_wf tv v /\ val_footprint tv v <= n /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
         val_in_memory tv v (w2n a) m) ==>
    ?Gf tf u. gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~u.vs_halted /\
      u.vs_prev_bb = s.vs_prev_bb /\
      typed_copy_state_frame sa (w2n d) n s u /\
      (!m. mem_agree_outside tf.t_mem u.vs_memory m ==>
           val_in_memory tv v (w2n d) m) /\
      tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
      (!p. lookup_var p u = lookup_var p s /\
        FLOOKUP Gf p = FLOOKUP G p /\
        op_taint tf (Var p) = op_taint tn (Var p)) /\
      (!i. ~(w2n d <= i /\ i < w2n d + n) ==>
        mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 s.vs_memory /\
        (i IN tf.t_mem <=> i IN tn.t_mem))
Proof
  rpt gen_tac >> strip_tac >> Cases_on `n = 0`
  >- (gvs[compile_copy_memory_def, comp_return_def] >>
      qexistsl_tac [`G`, `tn`, `s`] >>
      simp[cj 1 gas_path_ptr_rules] >> rpt strip_tac >>
      irule valueCopyTheory.val_in_memory_relocate >> simp[] >>
      qexistsl_tac [`w2n a`, `0`, `m`] >> simp[mem_bytes_at_def]) >>
  `0 < n` by decide_tac >>
  drule_all (SRULE [] assign_base_copy_memory_robust_endpoint_ptr) >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  qpat_assum `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[typed_copy_mcopy_state_frame] >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    (Cases_on `n` >>
     gvs[compile_copy_memory_def, emit_void_def, comp_bind_def,
         comp_ignore_bind_def, fresh_id_def, emit_def, comp_return_def]) >>
  qspecl_then [`PG`, `G`, `tn`, `s`, `sa.cs_next_id`,
    `Var dst`, `Var src`, `Lit (n2w n)`, `a`, `d`, `n2w n`]
    mp_tac mcopy_operand_ghost_frame >>
  simp[eval_operand_def] >> strip_tac >>
  `!i. ~(w2n d <= i /\ i < w2n d + n) ==>
    mem_bytes_at i 1 (mcopy (w2n d) (w2n a) n s).vs_memory =
    mem_bytes_at i 1 s.vs_memory` by
    (rpt strip_tac >> irule valueEncodingProofsTheory.mcopy_mem_bytes_at_disjoint >> decide_tac) >>
  simp[op_taint_def, lookup_var_def, mcopy_def, write_memory_with_expansion_def,
       step_taint_def, mk_inst_def, set_var_taint_def, imm_taint_def] >>
  rpt strip_tac >> gvs[] >> eq_tac >> strip_tac >> gvs[] >> decide_tac

QED

(* The emitted pair is the word branch's implementation interface. *)
Theorem annassign_word_pair_counted_ambient_ptr:
  !D ctx fn PG G tn s sa sm sb src dst out a b.
    emit_op MLOAD [Var src] sa = (Var out,sm) /\
    emit_void MSTORE [Var dst;Var out] sm = ((),sb) /\
    fn_has_code sa sm fn /\ fn_has_code sm sb fn /\
    not_fresh_at sa dst /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    ptr_covers G tn src s 32 /\ ptr_covers G tn dst s 32 /\
    lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
    (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) ==>
    ?Gf tf u. gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~u.vs_halted /\
      u.vs_prev_bb = s.vs_prev_bb /\
      typed_copy_state_frame sa (w2n b) 32 s u /\
      u.vs_memory = (mstore (w2n b) (mload (w2n a) s) s).vs_memory /\
      tf.t_mem = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b + 32} /\
      tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
      (!p. not_fresh_at sa p ==>
        lookup_var p u = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
        op_taint tf (Var p) = op_taint tn (Var p)) /\
      (!i. ~(w2n b <= i /\ i < w2n b + 32) ==>
        mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 s.vs_memory /\
        (i IN tf.t_mem <=> i IN tn.t_mem))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all annassign_emit_mload_clean_path_ptr >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  `ptr_covers Gf tnf dst sf 32 /\ lookup_var dst sf = SOME b` by
    (conj_tac >- (irule annassign_ptr_covers_frame_ptr >>
       goal_assum (drule_at Any) >> simp[]) >> metis_tac[]) >>
  `eval_operand (Var out) sf = SOME (mload (w2n a) s)` by simp[eval_operand_def] >>
  drule_all emit_mstore_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx fn PG Gf tnf sf 0 Gf tf (OK u)` >>
  qexistsl_tac [`Gf`, `tf`, `u`] >> conj_tac
  >- (`gas_path_ptr D 0 ctx fn PG G tn s (0+0) Gf tf (OK u)` by
       (irule gas_path_ptr_then >> goal_assum (drule_at Any) >> simp[]) >> fs[]) >>
  `tf.t_imm = tn.t_imm` by
    simp[step_taint_def, mk_inst_def, set_var_taint_def, imm_taint_def] >>
  `typed_copy_state_frame sa (w2n b) 32 s sf` by
    (simp[typed_copy_state_frame_def, typed_copy_frame_def] >>
     qpat_x_assum `sf with <|vs_vars := _; vs_inst_idx := _|> = s` mp_tac >>
     simp[venom_state_component_equality] >> metis_tac[]) >>
  `typed_copy_state_frame sa (w2n b) 32 s u` by
    (irule typed_copy_state_frame_trans >> qexists_tac `sf` >>
     simp[typed_copy_mstore_state_frame]) >>
  `sf.vs_prev_bb = s.vs_prev_bb` by
    (qpat_x_assum `sf with <|vs_vars := _; vs_inst_idx := _|> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  simp[op_taint_def] >> conj_tac
  >- simp[mstore_def, write_memory_with_expansion_def] >>
  conj_tac >- simp[mstore_def, write_memory_with_expansion_def] >>
  conj_tac >- (rpt strip_tac >>
    qpat_x_assum `!p. not_fresh_at sa p ==> _` (qspec_then `p` mp_tac) >>
    simp[op_taint_def]) >>
  rpt strip_tac >> simp[] >>
  qpat_assum `sf.vs_memory = s.vs_memory`
    (fn th => pure_once_rewrite_tac[GSYM th]) >>
  irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >> decide_tac
QED

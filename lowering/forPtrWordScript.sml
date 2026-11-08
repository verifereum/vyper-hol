(* Finite checked word element copies, independent of block layout. *)
Theory forPtrWord
Ancestors forPtrAdmin typedCopyPtr fragGasSeqPtr ghostPcTransportPtr
  representationCleanPtr wordCopyRobustPtr robustCopyTransportPtr
  venomExecSemantics venomInst venomState finite_map instIdxIndep
  fragExecPtr bodyPtrDefs fragExec exprLoweringProps ptrSafeRun ptrDiscipline
  valueEncodingProps valueEncoding valueEncodingProofs list venomMemProofs
  vyperTyping vyperValue context compileEnv

Theorem for_word_copy_steps:
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\ tmp <> dst ==>
  step_inst_base (mk_inst id MLOAD [Var src] [tmp]) s =
    OK (update_var tmp (mload (w2n a) s) s) /\
  step_inst_base (mk_inst (id+1) MSTORE [Var dst; Var tmp] [])
    (update_var tmp (mload (w2n a) s) s) =
    OK (mstore (w2n b) (mload (w2n a) s)
      (update_var tmp (mload (w2n a) s) s))
Proof
  strip_tac >> conj_tac >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def, exec_write2_def, eval_operand_def,
       update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  gvs[lookup_var_def]
QED

Theorem for_word_copy_checked_seq:
  ptr_covers G tn src s 32 /\ ptr_covers G tn dst s 32 /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\ tmp <> dst /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) /\
  ~ctx_has_dalloca ctx ==>
  ?Gf tnf.
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id MLOAD [Var src] [tmp];
       mk_inst (id+1) MSTORE [Var dst; Var tmp] []] s Gf tnf /\
    Gf = step_prov PG
      (step_prov PG G (mk_inst id MLOAD [Var src] [tmp])
        (update_var tmp (mload (w2n a) s) s))
      (mk_inst (id+1) MSTORE [Var dst; Var tmp] [])
      (mstore (w2n b) (mload (w2n a) s)
        (update_var tmp (mload (w2n a) s) s)) /\
    tnf = step_taint (mk_inst (id+1) MSTORE [Var dst; Var tmp] [])
      (update_var tmp (mload (w2n a) s) s)
      (mstore (w2n b) (mload (w2n a) s)
        (update_var tmp (mload (w2n a) s) s))
      (step_taint (mk_inst id MLOAD [Var src] [tmp]) s
        (update_var tmp (mload (w2n a) s) s) tn)
Proof
  strip_tac >> simp[] >>
  qabbrev_tac `u = update_var tmp (mload (w2n a) s) s` >>
  `step_inst_base (mk_inst id MLOAD [Var src] [tmp]) s = OK u` by
    (simp[Abbr `u`] >> metis_tac[for_word_copy_steps]) >>
  `step_inst_base (mk_inst (id+1) MSTORE [Var dst; Var tmp] [])
      (u with vs_inst_idx := SUC s.vs_inst_idx) =
    OK ((mstore (w2n b) (mload (w2n a) s) u) with
      vs_inst_idx := SUC s.vs_inst_idx)` by
    (simp[step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def, eval_operand_def, Abbr `u`,
          update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
     gvs[lookup_var_def] >> simp[mstore_def]) >>
  simp[inst_seq_ptr_def] >>
  conj_tac >- (irule ptr_inst_ok_mload >> simp[]) >>
  irule ptr_inst_ok_mstore >> simp[] >> conj_tac
  >- (simp[Abbr `u`] >> irule (cj 1 mload_ghost_clean) >>
      simp[eval_operand_def] >> metis_tac[]) >>
  simp[Abbr `u`] >> irule mload_preserves_ptr_covers >> simp[]
QED

Theorem for_word_copy_run:
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\ tmp <> dst ==>
  run_inst_seq [mk_inst id MLOAD [Var src] [tmp];
    mk_inst (id+1) MSTORE [Var dst; Var tmp] []] s =
  OK (mstore (w2n b) (mload (w2n a) s)
    (update_var tmp (mload (w2n a) s) s))
Proof
  strip_tac >>
  `step_inst_base (mk_inst id MLOAD [Var src] [tmp]) s =
    OK (update_var tmp (mload (w2n a) s) s)` by
    metis_tac[for_word_copy_steps] >>
  `step_inst_base (mk_inst (id+1) MSTORE [Var dst; Var tmp] [])
    (update_var tmp (mload (w2n a) s) s) =
    OK (mstore (w2n b) (mload (w2n a) s)
      (update_var tmp (mload (w2n a) s) s))` by
    metis_tac[for_word_copy_steps] >>
  simp[run_inst_seq_def]
QED


Theorem for_word_copy_taint_frame:
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\ tmp <> dst /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) /\
  u = update_var tmp (mload (w2n a) s) s /\
  t = step_taint (mk_inst id MLOAD [Var src] [tmp]) s u tn /\
  tf = step_taint (mk_inst (id+1) MSTORE [Var dst; Var tmp] []) u
       (mstore (w2n b) (mload (w2n a) s) u) t ==>
  tf.t_mem = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b + 32} /\
  tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
  tf.t_var = t.t_var
Proof
  strip_tac >>
  `op_taint t (Var tmp) = {} /\ t.t_mem = tn.t_mem /\
   t.t_stor = tn.t_stor /\ t.t_trans = tn.t_trans` by
    (qpat_x_assum `t = _` (SUBST1_TAC) >>
     qpat_x_assum `u = _` (SUBST1_TAC) >>
     irule mload_ghost_clean >> simp[eval_operand_def]) >>
  `lookup_var dst u = SOME b /\
   eval_operand (Var tmp) u = SOME (mload (w2n a) s)` by
    (gvs[lookup_var_def, eval_operand_def, update_var_def, FLOOKUP_UPDATE]) >>
  drule_all mstore_ghost_frame >> simp[]
QED

Theorem for_word_copy_variable_frame:
  p <> tmp /\
  u = update_var tmp (mload (w2n a) s) s /\
  g = step_prov PG G (mk_inst id MLOAD [Var src] [tmp]) u /\
  t = step_taint (mk_inst id MLOAD [Var src] [tmp]) s u tn /\
  gf = step_prov PG g (mk_inst (id+1) MSTORE [Var dst; Var tmp] [])
       (mstore (w2n b) (mload (w2n a) s) u) /\
  tf = step_taint (mk_inst (id+1) MSTORE [Var dst; Var tmp] []) u
       (mstore (w2n b) (mload (w2n a) s) u) t ==>
  lookup_var p (mstore (w2n b) (mload (w2n a) s) u) = lookup_var p s /\
  FLOOKUP gf p = FLOOKUP G p /\
  op_taint tf (Var p) = op_taint tn (Var p)
Proof
  strip_tac >>
  gvs[step_prov_def, set_prov_def, out_prov_def, step_taint_def,
      set_var_taint_def, op_taint_def, mk_inst_def, update_var_def,
      lookup_var_def, mstore_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]
QED

(* Typed word encodings include right-aligned addresses and left-aligned
   fixed bytes, not just the four arithmetic value constructors. *)
Theorem for_typed_word_in_memory:
  is_word_type ty /\ evaluate_type tenv ty = SOME tv /\
  value_has_type tv v ==>
  (val_in_memory tv v a mem <=>
    mem_word_at a mem = typed_val_to_w256 tv v)
Proof
  Cases_on `ty` >> simp[is_word_type_def, evaluate_type_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  TRY (rename1 `is_word_type (BaseT bt)` >> Cases_on `bt` >>
    gvs[is_word_type_def, evaluate_type_def, AllCaseEqs()]) >>
  TRY (rename1 `is_word_type (BaseT (BytesT bd))` >> Cases_on `bd` >>
    gvs[is_word_type_def, evaluate_type_def, AllCaseEqs()]) >>
  Cases_on `v` >>
  gvs[value_has_type_def, val_in_memory_def, typed_val_to_w256_def]
QED

Theorem for_typed_word_robust_clean:
  is_word_type ty /\ evaluate_type tenv ty = SOME tv /\
  value_has_type tv v /\
  (!mem. mem_agree_outside taints memory mem ==>
    val_in_memory tv v a mem) ==>
  !i. a <= i /\ i < a + 32 ==> i NOTIN taints
Proof
  strip_tac >> gen_tac >> disch_tac >> irule robust_mem_word_at_clean >>
  qexistsl_tac [`a`, `memory`, `typed_val_to_w256 tv v`] >> simp[] >>
  rpt strip_tac >> drule_all for_typed_word_in_memory >>
  metis_tac[]
QED

Theorem for_word_store_robust:
  is_word_type ty /\ evaluate_type tenv ty = SOME tv /\
  value_has_type tv v /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory tv v (w2n (a:256 word)) m) /\
  mem' = (mstore (w2n b) (mload (w2n a) s) s).vs_memory /\
  taints = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b + 32} ==>
  !m. mem_agree_outside taints mem' m ==> val_in_memory tv v (w2n b) m
Proof
  strip_tac >> rpt strip_tac >>
  `mem_bytes_at (w2n b) 32 m = mem_bytes_at (w2n b) 32 mem'` by
    (irule LIST_EQ >> simp[] >> rpt strip_tac >>
     rename1 `j < 32` >>
     `w2n b + j NOTIN taints` by simp[] >>
     `mem_bytes_at (w2n b+j) 1 mem' = mem_bytes_at (w2n b+j) 1 m` by
       (fs[mem_agree_outside_def] >> metis_tac[]) >>
     qpat_x_assum `mem_bytes_at _ 1 _ = mem_bytes_at _ 1 _` mp_tac >>
     simp[LIST_EQ_REWRITE, EL_mem_bytes_at]) >>
  `val_in_memory tv v (w2n a) s.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  `mem_word_at (w2n b) m = mem_word_at (w2n b) mem'` by
    asm_simp_tac bool_ss [mem_word_at_def, GSYM mem_bytes_at_def] >>
  `mem_word_at (w2n b) m = mload (w2n a) s` by
    metis_tac[mstore_mem_word_at_same] >>
  drule_all for_typed_word_in_memory >>
  disch_then (fn th => fs[th]) >>
  fs[mem_word_at_eq_mload]
QED

Theorem for_word_copy_robust_checked:
  ptr_covers G tn src s 32 /\ ptr_covers G tn dst s 32 /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\ tmp <> dst /\
  ~ctx_has_dalloca ctx /\
  is_word_type ty /\ evaluate_type tenv ty = SOME tv /\
  value_has_type tv v /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory tv v (w2n a) m) ==>
  ?Gf tnf sf.
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id MLOAD [Var src] [tmp];
       mk_inst (id+1) MSTORE [Var dst; Var tmp] []] s Gf tnf /\
    run_inst_seq [mk_inst id MLOAD [Var src] [tmp];
       mk_inst (id+1) MSTORE [Var dst; Var tmp] []] s = OK sf /\
    mem_agree_outside {i | w2n b <= i /\ i < w2n b + 32}
      sf.vs_memory s.vs_memory /\
    tnf.t_mem = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b + 32} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. p <> tmp ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
      val_in_memory tv v (w2n b) m)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem` by
    (gen_tac >> disch_tac >> irule for_typed_word_robust_clean >>
     qexistsl_tac [`w2n a`, `s.vs_memory`, `tenv`, `tv`, `ty`, `v`] >> simp[]) >>
  drule_all for_word_copy_checked_seq >>
  disch_then (qspecl_then [`id`, `fn`, `PG`, `D`] strip_assume_tac) >>
  qexistsl [`Gf`, `tnf`,
    `mstore (w2n b) (mload (w2n a) s)
      (update_var tmp (mload (w2n a) s) s)`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `run_inst_seq [mk_inst id MLOAD [Var src] [tmp];
     mk_inst (id+1) MSTORE [Var dst; Var tmp] []] s =
     OK (mstore (w2n b) (mload (w2n a) s)
       (update_var tmp (mload (w2n a) s) s))` by
    metis_tac[for_word_copy_run] >>
  `!w. (mstore (w2n b) w (update_var tmp (mload (w2n a) s) s)).vs_memory =
        (mstore (w2n b) w s).vs_memory` by simp[mstore_def, update_var_def] >>
  `tnf.t_mem = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b + 32} /\
   tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans` by
    metis_tac[for_word_copy_taint_frame] >>
  `!p. p <> tmp ==>
     lookup_var p (mstore (w2n b) (mload (w2n a) s)
       (update_var tmp (mload (w2n a) s) s)) = lookup_var p s /\
     FLOOKUP Gf p = FLOOKUP G p /\
     op_taint tnf (Var p) = op_taint tn (Var p)` by
    metis_tac[for_word_copy_variable_frame] >>
  qpat_x_assum `tnf = _` kall_tac >> qpat_x_assum `Gf = _` kall_tac >>
  simp[mstore_memory_frame] >>
  rpt strip_tac >> irule for_word_store_robust >> simp[] >>
  conj_tac >- (qexistsl_tac [`tenv`, `ty`] >> simp[]) >>
  qexistsl [`a`, `s`, `tn`] >> simp[]
QED

Theorem for_compile_word_copy_checked:
  is_word_type dst_ty /\
  compile_store_memory_typed cenv (Var dst) dst_ty (Var src) src_ty sa =
    ((),sb) /\ not_fresh_at sa dst /\
  ptr_covers G tn src s 32 /\ ptr_covers G tn dst s 32 /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ~ctx_has_dalloca ctx /\
  is_word_type ty /\ evaluate_type tenv ty = SOME tv /\
  value_has_type tv v /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory tv v (w2n a) m) ==>
  ?tmp id Gf tnf sf.
    sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts ++
      [mk_inst id MLOAD [Var src] [tmp];
       mk_inst (id+1) MSTORE [Var dst; Var tmp] []] /\
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id MLOAD [Var src] [tmp];
       mk_inst (id+1) MSTORE [Var dst; Var tmp] []] s Gf tnf /\
    run_inst_seq [mk_inst id MLOAD [Var src] [tmp];
       mk_inst (id+1) MSTORE [Var dst; Var tmp] []] s = OK sf /\
    mem_agree_outside {i | w2n b <= i /\ i < w2n b + 32}
      sf.vs_memory s.vs_memory /\
    tnf.t_mem = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b + 32} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
      val_in_memory tv v (w2n b) m)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all compile_store_word_code >> strip_tac >>
  `tmp <> dst` by metis_tac[] >>
  drule_all for_word_copy_robust_checked >>
  disch_then (qspecl_then [`id`, `fn`, `PG`, `D`] strip_assume_tac) >>
  qexistsl [`tmp`, `id`, `Gf`, `tnf`, `sf`] >>
  simp[APPEND_ASSOC] >> metis_tac[]
QED

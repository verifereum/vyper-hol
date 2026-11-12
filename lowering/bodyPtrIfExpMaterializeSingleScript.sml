Theory bodyPtrIfExpMaterializeSingle
Ancestors
  bodyPtrIfExpMaterializeWord bodyPtrIfExpMaterializeFrame
  context compileEnv loweringStateRelDefs emitHelper fragExec contextCodegenRel codegenRel
  venomExecSemantics venomInst venomState finite_map rich_list
  ptrDiscipline ptrSafeRun bodyPtrDefs bodyPtrIfExpBytesEndpoint

Theorem ifexp_ensure_single_stages:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_ensure_in_memory src loc bytes 1 ctor imm sa = (op,sb) ==>
  ?buf sc.
    compile_alloc_buffer bytes sa = (buf,sc) /\
    (do loaded <- emit_op (if loc = LocStorage then SLOAD else TLOAD) [src];
        emit_void MSTORE [buf.buf_operand;loaded] od) sc = ((),sb) /\
    op = buf.buf_operand
Proof
  strip_tac >> gvs[compile_ensure_in_memory_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> metis_tac[]
QED

Theorem ifexp_materialize_single_layout:
  (do loaded <- emit_op opc [src];
      emit_void MSTORE [Var dst;loaded] od) sc = ((),sn) /\
  fn_has_code sc sn fn ==>
  ?out bb.
    out = STRING #"%" (toString sc.cs_next_var) /\
    (!x. not_fresh_at sc x ==> x <> out) /\
    sn.cs_current_bb = sc.cs_current_bb /\
    LENGTH sn.cs_current_insts = LENGTH sc.cs_current_insts + 2 /\
    lookup_block sc.cs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH sc.cs_current_insts) =
      SOME (mk_inst sc.cs_next_id opc [src] [out]) /\
    get_instruction bb (SUC (LENGTH sc.cs_current_insts)) =
      SOME (mk_inst (SUC sc.cs_next_id) MSTORE [Var dst;Var out] [])
Proof
  strip_tac >>
  `sn.cs_current_bb = sc.cs_current_bb /\
   sn.cs_current_insts = sc.cs_current_insts ++
     [mk_inst sc.cs_next_id opc [src] [STRING #"%" (toString sc.cs_next_var)];
      mk_inst (SUC sc.cs_next_id) MSTORE
        [Var dst;Var (STRING #"%" (toString sc.cs_next_var))] []] /\
   (!x. not_fresh_at sc x ==> x <> STRING #"%" (toString sc.cs_next_var))` by
    (gvs[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_var_def, fresh_id_def, emit_def, not_fresh_at_def, arithmeticTheory.ADD1] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `~not_fresh_at sc (STRING #"%" (toString sc.cs_next_var))` by metis_tac[] >>
  qexistsl_tac [`STRING #"%" (toString sc.cs_next_var)`,`bb`] >> simp[] >>
  conj_tac >- (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  first_x_assum (qspec_then `1` mp_tac) >> simp[arithmeticTheory.ADD1]
QED

Theorem ifexp_materialize_single_path:
  MEM opc [SLOAD;TLOAD] /\
  (do loaded <- emit_op opc [src];
      emit_void MSTORE [Var dst;loaded] od) sc = ((),sn) /\
  fn_has_code sc sn fn /\ not_fresh_at sc dst /\
  ~ctx_has_dalloca ctx /\ eval_operand src s = SOME a /\
  op_taint tn src = {} /\ ptr_covers G tn dst s 32 /\
  lookup_var dst s = SOME p /\ ~s.vs_halted /\
  s.vs_current_bb = sc.cs_current_bb /\
  s.vs_inst_idx = LENGTH sc.cs_current_insts /\
  step_inst_base (mk_inst sc.cs_next_id opc [src]
    [STRING #"%" (toString sc.cs_next_var)]) s =
      OK (update_var (STRING #"%" (toString sc.cs_next_var)) w s) ==>
  ?out s1 u G1 tn1 G2 tn2.
    out = STRING #"%" (toString sc.cs_next_var) /\
    (!x. not_fresh_at sc x ==> x <> out) /\
    s1 = (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx) /\
    u = mstore (w2n p) w s1 /\
    G1 = step_prov PG G (mk_inst sc.cs_next_id opc [src] [out]) (update_var out w s) /\
    tn1 = step_taint (mk_inst sc.cs_next_id opc [src] [out]) s (update_var out w s) tn /\
    G2 = step_prov PG G1 (mk_inst (SUC sc.cs_next_id) MSTORE [Var dst;Var out] []) u /\
    tn2 = step_taint (mk_inst (SUC sc.cs_next_id) MSTORE [Var dst;Var out] []) s1 u tn1 /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G2 tn2
      (OK (u with vs_inst_idx := LENGTH sn.cs_current_insts)) /\
    u.vs_current_bb = sn.cs_current_bb /\ lookup_var dst u = SOME p
Proof
  strip_tac >> drule_all ifexp_materialize_single_layout >> strip_tac >>
  `out <> dst` by metis_tac[] >>
  qabbrev_tac `s1 = update_var out w s with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `u = mstore (w2n p) w s1` >>
  qabbrev_tac `G1 = step_prov PG G (mk_inst sc.cs_next_id opc [src] [out]) (update_var out w s)` >>
  qabbrev_tac `tn1 = step_taint (mk_inst sc.cs_next_id opc [src] [out]) s (update_var out w s) tn` >>
  qabbrev_tac `G2 = step_prov PG G1 (mk_inst (SUC sc.cs_next_id) MSTORE [Var dst;Var out] []) u` >>
  qabbrev_tac `tn2 = step_taint (mk_inst (SUC sc.cs_next_id) MSTORE [Var dst;Var out] []) s1 u tn1` >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 G2 tn2
     (OK (u with vs_inst_idx := SUC s1.vs_inst_idx))` by
    (irule ifexp_materialize_word_path >>
     simp[mk_inst_def] >>
     simp[Abbr `G1`, Abbr `tn1`, Abbr `G2`, Abbr `tn2`, Abbr `u`, Abbr `s1`] >>
     gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE, mk_inst_def] >>
     qexists_tac `w` >> simp[]) >>
  qexistsl_tac [`out`,`s1`,`u`,`G1`,`tn1`,`G2`,`tn2`] >>
  gvs[Abbr `s1`, Abbr `u`, update_var_def, mstore_def,
      write_memory_with_expansion_def, lookup_var_def, FLOOKUP_UPDATE,
      arithmeticTheory.ADD1] >>
  metis_tac[]
QED

Theorem ifexp_materialize_single_effect:
  MEM opc [SLOAD;TLOAD] /\ eval_operand src s = SOME a /\ out <> dst /\
  ptr_covers G tn dst s n /\ lookup_var dst s = SOME p /\
  s1 = (update_var out w s with vs_inst_idx := k) /\
  u = mstore (w2n p) w s1 /\
  G1 = step_prov PG G (mk_inst id opc [src] [out]) (update_var out w s) /\
  tn1 = step_taint (mk_inst id opc [src] [out]) s (update_var out w s) tn /\
  G2 = step_prov PG G1 (mk_inst sid MSTORE [Var dst;Var out] []) u /\
  tn2 = step_taint (mk_inst sid MSTORE [Var dst;Var out] []) s1 u tn1 ==>
  ptr_covers G2 tn2 dst (u with vs_inst_idx := j) n /\
  op_taint tn1 (Var out) SUBSET count 32 /\
  tn2.t_mem = (tn.t_mem DIFF {i | w2n p <= i /\ i < w2n p+32}) UNION
    {w2n p+i | i IN (if opc = SLOAD then key_taint tn.t_stor a
                    else key_taint tn.t_trans a)}
Proof
  strip_tac >>
  `MEM opc [SLOAD;TLOAD;DLOAD]` by gvs[] >>
  `ptr_covers G1 tn1 dst (update_var out w s) n` by
    (gvs[] >> irule ifexp_materialize_load_covers >> simp[] >> metis_tac[]) >>
  `op_taint tn1 (Var out) SUBSET count 32` by
    (gvs[] >> irule ifexp_materialize_load_taint_bound >> simp[] >> metis_tac[]) >>
  `eval_operand (Var dst) s1 = SOME p /\ eval_operand (Var out) s1 = SOME w` by
    gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `G2 = G1 /\ tn2.t_var = tn1.t_var` by
    gvs[ifexp_materialize_mstore_ghost, step_taint_def, set_var_taint_def,
        mk_inst_def, store_taint_def, adopt_reset_def, imm_taint_def, DRESTRICT_UNIV] >>
  conj_tac >-
    (gvs[ptr_covers_def, mstore_def,
         write_memory_with_expansion_def, update_var_def,
         lookup_var_def, FLOOKUP_UPDATE, op_taint_def] >> metis_tac[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `tn2.t_mem = (tn1.t_mem DIFF {i | w2n p <= i /\ i < w2n p+32}) UNION
     {w2n p+i | i IN op_taint tn1 (Var out)}` by
    (qpat_assum `eval_operand (Var dst) s1 = SOME p`
       (mp_then Any mp_tac ifexp_materialize_mstore_taint) >>
     disch_then (qspecl_then [`w`,`Var out`,`tn1`,`sid`] mp_tac) >>
     simp[arithmeticTheory.ADD_COMM]) >>
  `tn1 = tn with t_var := tn.t_var |+ (out,
     if opc = SLOAD then key_taint tn.t_stor a
     else key_taint tn.t_trans a)` by
    (qpat_assum `eval_operand src s = SOME a`
      (mp_then Any mp_tac ifexp_materialize_load_taint) >>
     simp[] >> disch_then (qspecl_then [`w`,`tn`,`out`,`opc`,`id`] mp_tac) >>
     gvs[]) >>
  qpat_x_assum `tn2.t_mem = _` (fn th => pure_rewrite_tac[th]) >>
  qpat_x_assum `tn1 = _ with t_var := _` (fn th => pure_rewrite_tac[th]) >>
  simp[op_taint_def, FLOOKUP_UPDATE, arithmeticTheory.ADD_COMM]
QED

Theorem ifexp_materialize_single_frames:
  MEM opc [SLOAD;TLOAD] /\ eval_operand src s = SOME a /\
  (!x. not_fresh_at sa x ==> x <> out) /\
  ghost_inv d ce cx ee G tn s /\ ghost_kept ce es sa G0 tn0 s0 G tn /\
  local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  s1 = (update_var out w s with vs_inst_idx := k) /\
  eval_operand (Var dst) s1 = SOME p /\
  u = mstore (w2n p) w s1 /\
  G1 = step_prov PG G (mk_inst id opc [src] [out]) (update_var out w s) /\
  tn1 = step_taint (mk_inst id opc [src] [out]) s (update_var out w s) tn /\
  G2 = step_prov PG G1 (mk_inst sid MSTORE [Var dst;Var out] []) u /\
  tn2 = step_taint (mk_inst sid MSTORE [Var dst;Var out] []) s1 u tn1 /\
  (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
    (!name p len. local_region ce es.scopes s0 name p len ==>
      off+sz <= p \/ p+len <= off) ==> off+sz <= w2n p \/ w2n p+32 <= off) /\
  (!name b len. local_region ce es.scopes s0 name b len ==>
    b+len <= w2n p \/ w2n p+32 <= b) /\
  (!name entry b sz v. lookup_scopes name ee.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var b) sz) /\ lookup_var b s1 = SOME v ==>
    val_wf entry.type entry.value /\
    (w2n v+type_memory_size entry.type <= w2n p \/ w2n p+32 <= w2n v)) ==>
  ghost_inv d ce cx ee G2 tn2 (u with vs_inst_idx := j) /\
  ghost_kept ce es sa G0 tn0 s0 G2 tn2
Proof
  strip_tac >>
  `MEM opc [SLOAD;TLOAD;DLOAD]` by gvs[] >>
  `ghost_inv d ce cx ee G1 tn1 (update_var out w s)` by
    (gvs[] >> irule ifexp_materialize_load_inv >> simp[] >> metis_tac[]) >>
  `ghost_inv d ce cx ee G1 tn1 s1` by gvs[] >>
  `ghost_kept ce es sa G0 tn0 s0 G1 tn1` by
    (gvs[] >> irule ifexp_materialize_load_kept >> simp[] >> metis_tac[]) >>
  `op_taint tn1 (Var out) SUBSET count 32` by
    (gvs[] >> irule ifexp_materialize_load_taint_bound >> simp[] >> metis_tac[]) >>
  `eval_operand (Var out) s1 = SOME w` by
    gvs[eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  conj_tac >- suspend "inv" >> suspend "kept"
QED

Resume ifexp_materialize_single_frames[inv]:
  pure_rewrite_tac[ifexp_ghost_inv_inst_idx] >>
  qpat_x_assum `G2 = _` SUBST1_TAC >> qpat_x_assum `tn2 = _` SUBST1_TAC >>
  qpat_x_assum `u = _` SUBST1_TAC >>
  irule ifexp_materialize_store_inv >>
  metis_tac[]
QED

Resume ifexp_materialize_single_frames[kept]:
  qpat_x_assum `G2 = _` SUBST1_TAC >> qpat_x_assum `tn2 = _` SUBST1_TAC >>
  qpat_x_assum `u = _` SUBST1_TAC >>
  irule ifexp_materialize_store_kept >> metis_tac[]
QED

Finalise ifexp_materialize_single_frames

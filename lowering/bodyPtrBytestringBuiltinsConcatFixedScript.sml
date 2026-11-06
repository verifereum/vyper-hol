(* Fixed Concat arm: scalar loads and increments must not acquire provenance. *)
Theory bodyPtrBytestringBuiltinsConcatFixed
Ancestors
  bodyPtrBytestringBuiltinsConcatFrame bodyPtrBytestringBuiltinsAllocation
  typedCopyPtr fragGasSeqPtr fragGasPathPtr
  concatMemory fragExecPtr bodyPtrDefs ptrDiscipline ptrSafeRun
  venomInst venomState venomExecSemantics finite_map words

Theorem concat_offset_load_ghost:
  !PG G tn s id src tmp a.
    eval_operand src s = SOME a /\
    (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) ==>
    op_prov (step_prov PG G (mk_inst id MLOAD [src] [tmp])
      (update_var tmp (mload (w2n a) s) s)) (Var tmp) = NONE /\
    op_taint (step_taint (mk_inst id MLOAD [src] [tmp]) s
      (update_var tmp (mload (w2n a) s) s) tn) (Var tmp) = {} /\
    (step_taint (mk_inst id MLOAD [src] [tmp]) s
      (update_var tmp (mload (w2n a) s) s) tn).t_mem = tn.t_mem /\
    (step_taint (mk_inst id MLOAD [src] [tmp]) s
      (update_var tmp (mload (w2n a) s) s) tn).t_stor = tn.t_stor /\
    (step_taint (mk_inst id MLOAD [src] [tmp]) s
      (update_var tmp (mload (w2n a) s) s) tn).t_trans = tn.t_trans
Proof
  rpt strip_tac
  >- (irule step_prov_out_none >> simp[mk_inst_def] >>
      irule out_prov_other_none >> simp[mk_inst_def]) >>
  drule_all mload_ghost_clean >> simp[]
QED

Theorem concat_offset_add_ghost:
  !PG G tn s id left right tmp w.
    op_prov G left = NONE /\ op_prov G right = NONE ==>
    op_prov (step_prov PG G (mk_inst id ADD [left; right] [tmp])
      (update_var tmp w s)) (Var tmp) = NONE /\
    op_taint (step_taint (mk_inst id ADD [left; right] [tmp]) s
      (update_var tmp w s) tn) (Var tmp) = {} /\
    (step_taint (mk_inst id ADD [left; right] [tmp]) s
      (update_var tmp w s) tn).t_mem = tn.t_mem /\
    (step_taint (mk_inst id ADD [left; right] [tmp]) s
      (update_var tmp w s) tn).t_stor = tn.t_stor /\
    (step_taint (mk_inst id ADD [left; right] [tmp]) s
      (update_var tmp w s) tn).t_trans = tn.t_trans
Proof
  rpt strip_tac
  >- (irule step_prov_out_none >> simp[mk_inst_def] >>
      irule out_prov_arith_none >> simp[mk_inst_def]) >>
  simp[copy_len_binop_ghost_frame]
QED

Theorem concat_offset_load_counted_edge:
  !D ctx fn PG G tn s bb id src tmp a.
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id MLOAD [Var src] [tmp]) /\
    lookup_var src s = SOME a /\ ptr_covers G tn src s 32 ==>
    gas_path_ptr_edge D 0 ctx fn PG G tn s 0
      (step_prov PG G (mk_inst id MLOAD [Var src] [tmp])
        (update_var tmp (mload (w2n a) s) s))
      (step_taint (mk_inst id MLOAD [Var src] [tmp]) s
        (update_var tmp (mload (w2n a) s) s) tn)
      (OK ((update_var tmp (mload (w2n a) s) s) with
        vs_inst_idx := SUC s.vs_inst_idx))
Proof
  rpt strip_tac >>
  `step_inst_base (mk_inst id MLOAD [Var src] [tmp]) s =
    OK (update_var tmp (mload (w2n a) s) s)` by
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def, exec_read1_def, eval_operand_def]) >>
  drule_at (Pat `step_inst_base _ _ = _`) straight_line_ptr_edge >>
  simp[mk_inst_def, is_terminator_def] >> disch_then irule >>
  simp[GSYM mk_inst_def] >> irule ptr_inst_ok_mload >> simp[]
QED

Theorem concat_word_store_counted_edge:
  !D ctx fn PG G tn s bb id dst value a w.
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id MSTORE [Var dst; value] []) /\
    lookup_var dst s = SOME a /\ eval_operand value s = SOME w /\
    op_taint tn value = {} /\ ptr_covers G tn dst s 32 ==>
    gas_path_ptr_edge D 0 ctx fn PG G tn s 0
      (step_prov PG G (mk_inst id MSTORE [Var dst; value] [])
        (mstore (w2n a) w s))
      (step_taint (mk_inst id MSTORE [Var dst; value] []) s
        (mstore (w2n a) w s) tn)
      (OK ((mstore (w2n a) w s) with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  rpt strip_tac >>
  `step_inst_base (mk_inst id MSTORE [Var dst; value] []) s =
    OK (mstore (w2n a) w s)` by
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def, exec_write2_def, eval_operand_def]) >>
  drule_at (Pat `step_inst_base _ _ = _`) straight_line_ptr_edge >>
  simp[mk_inst_def, is_terminator_def] >> disch_then irule >>
  simp[GSYM mk_inst_def] >> irule ptr_inst_ok_mstore >> simp[]
QED

Theorem concat_offset_load_register_frame:
  !PG G tn s id src tmp a q.
    q <> tmp ==>
    lookup_var q (update_var tmp (mload (w2n a) s) s) = lookup_var q s /\
    FLOOKUP (step_prov PG G (mk_inst id MLOAD [src] [tmp])
      (update_var tmp (mload (w2n a) s) s)) q = FLOOKUP G q /\
    op_taint (step_taint (mk_inst id MLOAD [src] [tmp]) s
      (update_var tmp (mload (w2n a) s) s) tn) (Var q) = op_taint tn (Var q)
Proof
  rpt strip_tac >>
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       step_prov_def, set_prov_def, out_prov_def, mk_inst_def,
       FLOOKUP_DRESTRICT, step_taint_def, set_var_taint_def, op_taint_def]
QED

Theorem concat_word_store_preserves_covers:
  !PG G tn s id dst value a w p n.
    lookup_var dst s = SOME a /\ eval_operand value s = SOME w /\
    op_taint tn value = {} /\ ptr_covers G tn p s n ==>
    ptr_covers
      (step_prov PG G (mk_inst id MSTORE [Var dst; value] [])
        (mstore (w2n a) w s))
      (step_taint (mk_inst id MSTORE [Var dst; value] []) s
        (mstore (w2n a) w s) tn)
      p ((mstore (w2n a) w s) with vs_inst_idx := SUC s.vs_inst_idx) n
Proof
  rpt strip_tac >> drule_all mstore_ghost_frame >> strip_tac >>
  gvs[ptr_covers_def, op_taint_def, mstore_def, lookup_var_def]
QED

Theorem concat_add_preserves_covers:
  !PG G tn s id left right tmp w p n.
    p <> tmp /\ ptr_covers G tn p s n ==>
    ptr_covers
      (step_prov PG G (mk_inst id ADD [left; right] [tmp])
        (update_var tmp w s))
      (step_taint (mk_inst id ADD [left; right] [tmp]) s
        (update_var tmp w s) tn)
      p ((update_var tmp w s) with vs_inst_idx := SUC s.vs_inst_idx) n
Proof
  rpt strip_tac >>
  gvs[ptr_covers_def, copy_len_binop_ghost_frame,
      update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

(* The first two actual edges, retaining the loaded scalar as well as the
   full-word destination capability. No erased execution is lifted here. *)
Theorem concat_fixed_address_counted:
  !D ctx fn PG G tn s bb id root off tmp dst a b k cap.
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id MLOAD [Var off] [tmp]) /\
    get_instruction bb (SUC s.vs_inst_idx) =
      SOME (mk_inst (id+1) ADD [Var root; Var tmp] [dst]) /\
    lookup_var off s = SOME b /\ lookup_var root s = SOME a /\
    ptr_covers G tn off s 32 /\ ptr_covers G tn root s cap /\
    mload (w2n b) s = n2w k /\
    (!i. w2n b <= i /\ i < w2n b + 32 ==> i NOTIN tn.t_mem) /\
    k + 32 <= cap /\ w2n a + k < dimword(:256) /\
    root <> tmp /\ tmp <> dst ==>
    ?Gf tnf t.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK t) /\
      lookup_var dst t = SOME (a + n2w k) /\
      lookup_var tmp t = SOME (n2w k) /\
      op_prov Gf (Var tmp) = NONE /\ op_taint tnf (Var tmp) = {} /\
      ptr_covers Gf tnf dst t 32 /\
      t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
      t.vs_inst_idx = s.vs_inst_idx + 2 /\
      t.vs_current_bb = s.vs_current_bb /\ ~t.vs_halted /\
      tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
      tnf.t_trans = tn.t_trans /\
      (!q. q <> tmp /\ q <> dst ==>
        lookup_var q t = lookup_var q s /\
        FLOOKUP Gf q = FLOOKUP G q /\
        op_taint tnf (Var q) = op_taint tn (Var q))
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `u = update_var tmp (n2w k) s` >>
  qabbrev_tac `g1 = step_prov PG G (mk_inst id MLOAD [Var off] [tmp]) u` >>
  qabbrev_tac `tn1 = step_taint (mk_inst id MLOAD [Var off] [tmp]) s u tn` >>
  qabbrev_tac `s1 = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `v = update_var dst (a + n2w k) s1` >>
  qabbrev_tac `g2 = step_prov PG g1
    (mk_inst (id+1) ADD [Var root; Var tmp] [dst]) v` >>
  qabbrev_tac `tn2 = step_taint
    (mk_inst (id+1) ADD [Var root; Var tmp] [dst]) s1 v tn1` >>
  qabbrev_tac `s2 = v with vs_inst_idx := SUC s1.vs_inst_idx` >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0 g1 tn1 (OK s1)` by
    (unabbrev_all_tac >> drule_all concat_offset_load_counted_edge >> simp[]) >>
  `op_prov g1 (Var tmp) = NONE /\ op_taint tn1 (Var tmp) = {} /\
   tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\ tn1.t_trans = tn.t_trans`
    by suspend "load_ghost" >>
  `ptr_covers g1 tn1 root s1 cap /\ lookup_var root s1 = SOME a`
    by suspend "root" >>
  `gas_path_ptr_edge D 0 ctx fn PG g1 tn1 s1 0 g2 tn2 (OK s2)`
    by suspend "add_edge" >>
  qexistsl_tac [`g2`, `tn2`, `s2`] >>
  conj_tac >- suspend "path" >> suspend "endpoint"
QED

Resume concat_fixed_address_counted[load_ghost]:
  `eval_operand (Var off) s = SOME b` by simp[eval_operand_def] >>
  drule_all concat_offset_load_ghost >>
  disch_then (qspecl_then [`PG`, `G`, `id`, `tmp`] mp_tac) >>
  simp[Abbr `g1`, Abbr `tn1`, Abbr `u`]
QED

Resume concat_fixed_address_counted[root]:
  conj_tac
  >- (simp[Abbr `s1`, Abbr `g1`, Abbr `tn1`, Abbr `u`] >>
      qpat_assum `mload _ _ = _` (fn th => pure_rewrite_tac[GSYM th]) >>
      irule mload_preserves_ptr_covers >> simp[]) >>
  simp[Abbr `s1`, Abbr `u`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  gvs[lookup_var_def]
QED

Resume concat_fixed_address_counted[add_edge]:
  simp[Abbr `g2`, Abbr `tn2`, Abbr `s2`, Abbr `v`] >>
  irule pointer_offset_counted_edge >>
  gvs[Abbr `s1`, Abbr `u`, ptr_covers_def, eval_operand_def,
      lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  qexists_tac `bb` >> simp[]
QED

Resume concat_fixed_address_counted[path]:
  `~s2.vs_halted` by
    simp[Abbr `s2`, Abbr `v`, Abbr `s1`, Abbr `u`, update_var_def] >>
  metis_tac[gas_path_ptr_rules, arithmeticTheory.ADD]
QED

Resume concat_fixed_address_counted[endpoint]:
  `ptr_covers g2 tn2 dst s2 32` by
    (qunabbrev_tac `g2` >> qunabbrev_tac `tn2` >>
     qunabbrev_tac `s2` >> qunabbrev_tac `v` >>
     `eval_operand (Var tmp) s1 = SOME (n2w k)` by
       simp[Abbr `s1`, Abbr `u`, eval_operand_def,
            lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     irule pointer_offset_covers >> simp[] >>
     qexists_tac `cap` >> simp[]) >>
  simp[Abbr `s2`, Abbr `v`, Abbr `tn2`, copy_len_binop_ghost_frame,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       Abbr `s1`, Abbr `u`] >>
  conj_tac
  >- (simp[Abbr `g2`, op_prov_def, copy_len_binop_ghost_frame] >>
      gvs[op_prov_def]) >>
  rpt strip_tac >>
  simp[Abbr `g2`, copy_len_binop_ghost_frame, Abbr `g1`,
       step_prov_def, set_prov_def, out_prov_def, mk_inst_def,
       FLOOKUP_DRESTRICT] >>
  simp[Abbr `tn1`, step_taint_def, set_var_taint_def, op_taint_def,
       mk_inst_def, FLOOKUP_UPDATE]
QED

Finalise concat_fixed_address_counted

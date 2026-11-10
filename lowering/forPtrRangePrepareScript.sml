(* Concrete range-header layout adapter. No synthetic compiler transition is
   assumed by the consumer: the witness states below only describe prefixes. *)
Theory forPtrRangePrepare
Ancestors forPtrControl forPtrScalarStore forPtrRangeCallback fragExec
  emitHelperProps venomState venomInst finite_map list ptrDiscipline
  fragGasPathPtr bodyPtrDefs compileEnv loweringStateRelDefs stmtSimDeclStore stmtSimProps
  stmtSimDefs loweringPosts localPtrsProps valueEncodingProps valueEncoding
  venomMemProofs loweringSlice exprLoweringProps vyperState

Theorem for_header_test_path_ptr:
  lookup_block cond_lbl fn.fn_blocks =
    SOME <| bb_label := cond_lbl;
      bb_instructions := [mk_inst j1 EQ [Var cv; Var ev] [dv];
        mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl] []] |> /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = cond_lbl /\ s.vs_inst_idx = 0 /\
  lookup_var cv s = SOME w /\ lookup_var ev s = SOME z /\
  op_taint tn (Var cv) = {} /\ op_taint tn (Var ev) = {} /\
  op_prov G (Var cv) = NONE /\ op_prov G (Var ev) = NONE ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {dv}))
    (tn with t_var := tn.t_var |+ (dv,{}))
    (OK (jump_to (if w = z then exit_lbl else body_lbl)
      (update_var dv (if w = z then 1w else 0w) s)))
Proof
  strip_tac >> irule for_counter_test_path_ptr >> simp[] >>
  qexistsl_tac [`Var ev`, `cv`, `j1`,

    `(ARB:compile_state) with <| cs_blocks := []; cs_current_bb := cond_lbl;
       cs_current_insts := []; cs_next_id := j1 |>`,
    `(ARB:compile_state) with <| cs_blocks := []; cs_current_bb := cond_lbl;
       cs_current_insts := [mk_inst j1 EQ [Var cv; Var ev] [dv];
         mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl] []] |>`,
    `(ARB:compile_state) with <| cs_blocks := []; cs_current_bb := cond_lbl;
       cs_current_insts := [mk_inst j1 EQ [Var cv; Var ev] [dv]];
       cs_next_id := j2 |>`] >>
  simp[fn_has_code_def, emitted_blocks_def, eval_operand_def]
QED

Theorem for_header_store_path_ptr:
  lookup_block cond_lbl fn.fn_blocks =
    SOME <| bb_label := cond_lbl;
      bb_instructions := [mk_inst j1 EQ [Var cv; Var ev] [dv];
        mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl] []] |> /\
  lookup_block body_lbl fn.fn_blocks = SOME bbb /\
  get_instruction bbb 0 = SOME (mk_inst j3 MSTORE [Var p; Var cv] []) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = cond_lbl /\ s.vs_inst_idx = 0 /\
  lookup_var cv s = SOME w /\ lookup_var ev s = SOME z /\
  lookup_var p s = SOME a /\ w <> z /\ dv <> p /\ dv <> cv /\
  ptr_covers G tn p s 32 /\
  op_taint tn (Var cv) = {} /\ op_taint tn (Var ev) = {} /\
  op_prov G (Var cv) = NONE /\ op_prov G (Var ev) = NONE ==>
  ?tf. gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {dv})) tf
    (OK ((mstore (w2n a) w (jump_to body_lbl (update_var dv 0w s)))
      with vs_inst_idx := 1)) /\
    tf.t_var = (tn.t_var |+ (dv,{})) /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    tf.t_mem = tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a+32}
Proof
  strip_tac >> drule_all for_header_test_path_ptr >> simp[] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `OK s1` >>
  `ptr_covers (DRESTRICT G (COMPL {dv}))
     (tn with t_var := tn.t_var |+ (dv,{})) p s1 32` by
    gvs[Abbr `s1`, ptr_covers_def, jump_to_def, update_var_def,
        lookup_var_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE, op_taint_def] >>
  `?tf. gas_path_ptr D 0 ctx fn PG (DRESTRICT G (COMPL {dv}))
     (tn with t_var := tn.t_var |+ (dv,{})) s1 0
     (DRESTRICT G (COMPL {dv})) tf
     (OK ((mstore (w2n a) w s1) with vs_inst_idx := SUC s1.vs_inst_idx)) /\
     tf.t_var = tn.t_var |+ (dv,{}) /\ tf.t_stor = tn.t_stor /\
     tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
     tf.t_mem = tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a+32}` by
    (irule (SRULE [] (Q.INST
       [`tn` |-> `tn with t_var := tn.t_var |+ (dv,{})`]
       scalar_mstore_path_ptr)) >> simp[] >>
     conj_tac >- simp[Abbr `s1`, jump_to_def, update_var_def] >>
     qexistsl_tac [`bbb`, `p`, `j3`, `Var cv`] >>
     gvs[Abbr `s1`, jump_to_def, update_var_def, eval_operand_def,
          lookup_var_def, FLOOKUP_UPDATE, op_taint_def]) >>
  qexists_tac `tf` >> simp[Abbr `s1`] >>
  qpat_x_assum `!PG D. _` (qspecl_then [`PG`, `D`] mp_tac) >>
  disch_then (mp_then Any mp_tac gas_path_ptr_then) >> disch_then drule >>
  simp[jump_to_def]
QED

(* Scalar control results may replace no live local or return-buffer pointer.
   Return-PC taint is safe even if the result replaces that scalar. *)
Theorem for_scalar_overwrite_ghost:
  ghost_inv d cenv cx es G tn s /\
  not_local_ptr cenv es.scopes out /\
  (!sz. cenv.ce_return_buf <> SOME (PtrVar (Var out) sz)) ==>
  ghost_inv d cenv cx es (DRESTRICT G (COMPL {out}))
    (tn with t_var := tn.t_var |+ (out,{})) (update_var out w s)
Proof
  strip_tac >> fs[ghost_inv_def, not_local_ptr_def] >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `p <> out` by metis_tac[] >>
      qpat_x_assum `!name entry p sz. _` drule_all >>
      simp[ptr_covers_def, lookup_var_def, update_var_def,
           op_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE])
  >- (Cases_on `d` >> simp[return_buf_ptr_def] >> PairCases_on `x` >>
      fs[return_buf_ptr_def] >>
      rename1 `cenv.ce_return_buf = SOME (PtrVar (Var rp) slot_size)` >>
      `rp <> out` by metis_tac[] >>
      simp[ptr_covers_def, lookup_var_def, update_var_def,
           op_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
      gvs[ptr_covers_def, lookup_var_def, op_taint_def])
  >- (rpt strip_tac >> Cases_on `out = x`
      >- simp[op_taint_def, FLOOKUP_UPDATE] >>
      qpat_x_assum `!x sz. _` drule >>
      simp[op_taint_def, FLOOKUP_UPDATE]) >>
  fs[stor_taint_ok_def, update_var_def]
QED

Theorem return_buf_fresh_result_separate:
  (!r q. cenv.ce_return_buf = SOME (PtrVar (Var r) q) ==>
     not_fresh_at sa r) /\ ~not_fresh_at sa out ==>
  !r q. cenv.ce_return_buf = SOME (PtrVar (Var r) q) ==> r <> out
Proof
  metis_tac[]
QED

Theorem for_code_return_buf:
  for_code func cenv bc ty stmts id tyv p sz ainst cv ev dv nv
    cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3 sb0 sb1 sj ==>
  bc.ce_return_buf = cenv.ce_return_buf
Proof
  simp[stmtSimForLoopTheory.for_code_def] >> strip_tac >>
  qpat_x_assum `_ = cenv` mp_tac >>
  disch_then (mp_tac o AP_TERM ``\c:compile_env. c.ce_return_buf``) >> simp[]
QED

(* Export the allocation-offd word declaration boundary: unlike the older
   prefix-bound variant, separation comes from the actual ALLOCA record. *)
Theorem for_declare_word_alloca:
  !func cenv cx es s id p sz w inst v tyv sc rest a ctx.
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  es.scopes = sc :: rest /\ lookup_scopes id es.scopes = NONE /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  not_local_ptr cenv es.scopes p /\ lookup_var p s = SOME w /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [p] /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w, sz) /\
  32 <= sz /\ word_value v /\ type_memory_size tyv = 32 ==>
  stmt_state_rel ctx func cenv cx
    (es with scopes :=
      (sc |+ (id,<|assignable := a; type := tyv; value := v; popped := []|>)) :: rest)
    (mstore (w2n w) (val_to_w256 v) s)
Proof
  rpt gen_tac >> strip_tac >>
  `local_ptrs_rel func cenv es.scopes s /\
   immutable_alloca_sep func cenv cx es s /\
   immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es
    (mstore (w2n w) (val_to_w256 v) s)` by
    (irule immutables_rel_mstore_alloca >> simp[] >>
     qexistsl_tac [`w2n w`, `func`, `inst`, `sz`] >> simp[]) >>
  irule stmt_state_rel_declare_memory >> simp[word_value_wf] >>
  qexistsl_tac [`inst`, `s`, `w`] >> simp[word_value_in_memory] >> conj_tac
  >- (rpt strip_tac >>
      `regions_disjoint (w2n w) sz b sz'` by
        (irule local_ptrs_rel_alloca_disjoint >>
         goal_assum (drule_at (Pat `local_ptrs_rel _ _ _ _`)) >>
         goal_assum (drule_at (Pat `MEM _ (fn_insts _)`)) >>
         fs[stmt_state_rel_def] >> metis_tac[]) >>
      irule EQ_SYM >> irule mstore_mem_bytes_at_disjoint >>
      fs[regions_disjoint_def] >> decide_tac) >>
  simp[mstore_def, lookup_var_def, LET_THM] >> metis_tac[]
QED

Theorem for_range_body_prepare_state:
  for_code func cenv bc ty stmts id tyv p sz ainst cv ev dv nv
    cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3 sb0 sb1 sj /\
  stmt_state_rel ctx func cenv cx es s /\ lookup_scopes id es.scopes = NONE /\
  lookup_var p s = SOME a /\
  FLOOKUP s.vs_allocas ainst.inst_id = SOME (w2n a,sz) /\
  not_local_ptr bc (FEMPTY :: es.scopes) p ==>
  stmt_state_rel ctx func bc cx
    (es with scopes := (FEMPTY |+ (id,
      <|assignable := F; type := tyv; value := IntV i; popped := []|>)) :: es.scopes)
    ((mstore (w2n a) (i2w i) (jump_to body_lbl (update_var dv 0w s)))
      with vs_inst_idx := 1)
Proof
  strip_tac >> fs[stmtSimForLoopTheory.for_code_def,
                   compile_env_component_equality] >>
  qmatch_goalsub_abbrev_tac `mstore _ _ s1` >>
  `stmt_state_rel ctx func cenv cx (es with scopes := FEMPTY :: es.scopes) s1` by
    (simp[Abbr `s1`, stmt_state_rel_jump_to, stmt_state_rel_push_scope] >>
     irule stmt_state_rel_update_var >> simp[]) >>
  `stmt_state_rel ctx func bc cx (es with scopes := FEMPTY :: es.scopes) s1` by
    (irule stmt_state_rel_cenv_cong >> qexists_tac `cenv` >> simp[] >>
     rpt strip_tac >> Cases_on `n = id` >> gvs[lookup_scopes_def] >>
     metis_tac[]) >>
  simp[stmt_state_rel_inst_idx] >>
  `i2w i = val_to_w256 (IntV i)` by simp[val_to_w256_def] >>
  pop_assum SUBST1_TAC >>
  irule (SRULE [] (Q.SPECL [`func`, `bc`, `cx`,
    `es with scopes := FEMPTY :: es.scopes`] for_declare_word_alloca)) >>
  simp[lookup_scopes_def, word_value_def] >>
  qexists_tac `ainst` >>
  simp[Abbr `s1`, jump_to_def, update_var_def, lookup_var_def,
       FLOOKUP_UPDATE] >> fs[lookup_var_def]
QED

Theorem for_alloca_scalar_write_separation:
  !ctx func cenv cx es s inst dst off cap len.
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_outputs = [dst] /\
  not_local_ptr cenv es.scopes dst /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (off,cap) /\ len <= cap ==>
  !name entry p sz.
    lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    val_wf entry.type entry.value /\
    !b i. lookup_var p s = SOME b /\
      w2n b <= i /\ i < w2n b + val_footprint entry.type entry.value ==>
      i < off \/ off+len <= i
Proof
  rpt gen_tac >> strip_tac >>
  `local_ptrs_rel func cenv es.scopes s /\ alloca_inv s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  rpt gen_tac >> strip_tac >>
  `?w. lookup_var p s = SOME w /\
       type_memory_size entry.type <= sz /\ val_wf entry.type entry.value` by
    (fs[local_ptrs_rel_def] >> metis_tac[]) >>
  simp[] >> rpt gen_tac >> strip_tac >>
  `regions_disjoint off cap (w2n w) sz` by
    (irule local_ptrs_rel_alloca_disjoint >>
     goal_assum (drule_at (Pat `local_ptrs_rel _ _ _ _`)) >>
     goal_assum (drule_at (Pat `MEM _ (fn_insts _)`)) >>
     simp[local_region_def] >> metis_tac[]) >>
  `val_footprint entry.type entry.value <= type_memory_size entry.type` by
    metis_tac[exprSimPropsTheory.val_footprint_le] >>
  fs[regions_disjoint_def] >> decide_tac
QED

Theorem for_range_body_prepare_ghost:
  for_code func cenv bc ty stmts id tyv p sz ainst cv ev dv nv
    cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3 sb0 sb1 sj /\
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  lookup_scopes id es.scopes = NONE /\ lookup_var p s = SOME a /\
  FLOOKUP s.vs_allocas ainst.inst_id = SOME (w2n a,sz) /\
  not_local_ptr cenv es.scopes p /\
  ptr_covers G tn p s sz /\ lookup_var cv s = SOME (i2w i) /\
  op_taint tn (Var cv) = {} /\
  (!r q. cenv.ce_return_buf = SOME (PtrVar (Var r) q) ==> r <> dv) ==>
  ghost_inv d bc cx
    (es with scopes := (FEMPTY |+ (id,
      <|assignable := F; type := tyv; value := IntV i; popped := []|>)) :: es.scopes)
    (DRESTRICT G (COMPL {dv}))
    (step_taint (mk_inst j3 MSTORE [Var p; Var cv] [])
      (jump_to body_lbl (update_var dv 0w s))
      (mstore (w2n a) (i2w i) (jump_to body_lbl (update_var dv 0w s)))
      (tn with t_var := tn.t_var |+ (dv,{})))
    (mstore (w2n a) (i2w i) (jump_to body_lbl (update_var dv 0w s)))
Proof
  strip_tac >>
  `ghost_inv d cenv cx es (DRESTRICT G (COMPL {dv}))
     (tn with t_var := tn.t_var |+ (dv,{})) (update_var dv 0w s)` by
    (irule for_scalar_overwrite_ghost >> simp[] >>
     fs[stmtSimForLoopTheory.for_code_def] >> metis_tac[]) >>
  qmatch_goalsub_abbrev_tac `mstore _ _ s1` >>
  `ghost_inv d cenv cx es (DRESTRICT G (COMPL {dv}))
     (tn with t_var := tn.t_var |+ (dv,{})) s1` by
    simp[Abbr `s1`, jump_to_def, stmtFragPtrTheory.ghost_inv_jump_to] >>
  `stmt_state_rel ctx func cenv cx es s1` by
    (simp[Abbr `s1`, stmt_state_rel_jump_to] >>
     irule stmt_state_rel_update_var >>
     fs[stmtSimForLoopTheory.for_code_def]) >>
  `i2w i = val_to_w256 (IntV i)` by simp[val_to_w256_def] >>
  pop_assum SUBST1_TAC >>
  irule (SRULE [] (Q.INST
    [`entry` |-> `<|assignable := F; type := tyv; value := IntV i; popped := []|>`]
    scalar_mstore_install_ghost)) >> simp[] >>
  conj_tac
  >- fs[stmtSimForLoopTheory.for_code_def, op_taint_def, FLOOKUP_UPDATE] >>
  conj_tac
  >- fs[stmtSimForLoopTheory.for_code_def, Abbr `s1`, eval_operand_def,
        lookup_var_def, update_var_def, jump_to_def, FLOOKUP_UPDATE,
        val_to_w256_def] >>
  conj_tac
  >- fs[stmtSimForLoopTheory.for_code_def, Abbr `s1`, lookup_var_def,
        update_var_def, jump_to_def, FLOOKUP_UPDATE] >>
  conj_tac
  >- (qexists_tac `sz` >>
      fs[stmtSimForLoopTheory.for_code_def, ptr_covers_def, Abbr `s1`,
         lookup_var_def, update_var_def, jump_to_def, FLOOKUP_DRESTRICT,
         FLOOKUP_UPDATE, op_taint_def]) >>
  qexists_tac `cenv` >> simp[] >> conj_tac
  >- (match_mp_tac for_alloca_scalar_write_separation >>
      qexistsl_tac [`ctx`, `func`, `cx`, `ainst`, `p`, `sz`] >>
      simp[] >> fs[stmtSimForLoopTheory.for_code_def, Abbr `s1`,
        jump_to_def, update_var_def]) >>
  fs[stmtSimForLoopTheory.for_code_def, cenv_top_ext_def] >>
  rpt strip_tac >> `n = id` by metis_tac[] >> gvs[] >> metis_tac[]
QED

Theorem for_range_body_ghost_endpoint:
  ghost_inv d bc cx es (DRESTRICT G (COMPL {dv}))
    (step_taint (mk_inst j3 MSTORE [Var p; Var cv] [])
      (jump_to body_lbl (update_var dv 0w s))
      (mstore (w2n a) w (jump_to body_lbl (update_var dv 0w s)))
      (tn with t_var := tn.t_var |+ (dv,{})))
    (mstore (w2n a) w (jump_to body_lbl (update_var dv 0w s))) /\
  dv <> p /\ dv <> cv /\ lookup_var p s = SOME a /\
  lookup_var cv s = SOME w /\ op_taint tn (Var cv) = {} /\
  tf.t_var = tn.t_var |+ (dv,{}) /\ tf.t_stor = tn.t_stor /\
  tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
  tf.t_mem = tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a+32} ==>
  ghost_inv d bc cx es (DRESTRICT G (COMPL {dv})) tf
    ((mstore (w2n a) w (jump_to body_lbl (update_var dv 0w s)))
      with vs_inst_idx := 1)
Proof
  strip_tac >>
  `step_taint (mk_inst j3 MSTORE [Var p; Var cv] [])
      (jump_to body_lbl (update_var dv 0w s))
      (mstore (w2n a) w (jump_to body_lbl (update_var dv 0w s)))
      (tn with t_var := tn.t_var |+ (dv,{})) = tf` by
    (simp[step_taint_def, mk_inst_def, eval_operand_def, jump_to_def,
          update_var_def, lookup_var_def, FLOOKUP_UPDATE,
          set_var_taint_def, op_taint_def, taint_component_equality,
          imm_taint_def, store_taint_def, adopt_reset_def, mem_taint_def,
          step_writes_def, codegenRelTheory.source_memory_write_ranges_def,
          codegenRelTheory.fixed_source_write_range_def, written_taint_def, range_bytes_def,
          new_site_bytes_def, DRESTRICT_UNIV] >>
     fs[op_taint_def, lookup_var_def, mstore_def, FLOOKUP_DEF,
        pred_setTheory.EXTENSION] >> metis_tac[]) >>
  gvs[] >>
  qmatch_goalsub_abbrev_tac `ghost_inv _ _ _ _ _ _ s2` >>
  `s2 = (mstore (w2n a) w (jump_to body_lbl (update_var dv 0w s))) with
      <|vs_prev_bb := s2.vs_prev_bb; vs_current_bb := s2.vs_current_bb;
        vs_inst_idx := 1|>` by simp[Abbr `s2`, mstore_def, jump_to_def] >>
  pop_assum SUBST1_TAC >> simp[stmtFragPtrTheory.ghost_inv_jump_to]
QED

Theorem for_range_body_prepare_ptr:
  for_code func cenv bc ty stmts id tyv p sz ainst cv ev dv nv
    cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3 sb0 sb1 sj /\
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = cond_lbl /\ s.vs_inst_idx = 0 /\
  lookup_var cv s = SOME (i2w i) /\ lookup_var ev s = SOME z /\ i2w i <> z /\
  lookup_var p s = SOME a /\
  FLOOKUP s.vs_allocas ainst.inst_id = SOME (w2n a,sz) /\ ptr_covers G tn p s sz /\
  op_taint tn (Var cv) = {} /\ op_taint tn (Var ev) = {} /\
  op_prov G (Var cv) = NONE /\ op_prov G (Var ev) = NONE /\
  lookup_scopes id es.scopes = NONE /\ not_local_ptr bc (FEMPTY::es.scopes) p /\
  (!r q. cenv.ce_return_buf = SOME (PtrVar (Var r) q) ==> r <> dv) ==>
  ?s2 G2 tf.
    s2 = ((mstore (w2n a) (i2w i) (jump_to body_lbl (update_var dv 0w s)))
      with vs_inst_idx := 1) /\ G2 = DRESTRICT G (COMPL {dv}) /\
    tf.t_var = tn.t_var |+ (dv,{}) /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    tf.t_mem = tn.t_mem DIFF {j | w2n a <= j /\ j < w2n a+32} /\
    gas_path_ptr D 0 ctx func PG G tn s 0 G2 tf (OK s2) /\
    stmt_state_rel ctx func bc cx
      (es with scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tyv; value := IntV i; popped := []|>))::es.scopes) s2 /\
    ghost_inv d bc cx
      (es with scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tyv; value := IntV i; popped := []|>))::es.scopes)
      G2 tf s2 /\
    s2.vs_current_bb = body_lbl /\ s2.vs_inst_idx = 1 /\ ~s2.vs_halted /\
    s2.vs_allocas = s.vs_allocas /\
    (!v. v <> dv ==> lookup_var v s2 = lookup_var v s) /\
    ptr_covers G2 tf p s2 sz
Proof
  strip_tac >> drule_all for_range_body_prepare_state >> strip_tac >>
  `not_local_ptr cenv es.scopes p` by
    (fs[stmtSimForLoopTheory.for_code_def, not_local_ptr_def,
        lookup_scopes_def, compile_env_component_equality] >>
     rpt strip_tac >> Cases_on `name = id` >> gvs[] >> metis_tac[]) >>
  drule_all for_range_body_prepare_ghost >> strip_tac >>
  qmatch_asmsub_abbrev_tac `ghost_inv d bc cx _ _ _ s2` >>
  `32 <= sz` by fs[stmtSimForLoopTheory.for_code_def] >>
  `ptr_covers G tn p s 32` by (fs[ptr_covers_def] >> metis_tac[]) >>
  `dv <> p /\ dv <> cv` by fs[stmtSimForLoopTheory.for_code_def] >>
  qhdtm_assum `for_code`
    (strip_assume_tac o REWRITE_RULE [stmtSimForLoopTheory.for_code_def]) >>
  drule_all for_header_store_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`s2 with vs_inst_idx := 1`, `DRESTRICT G (COMPL {dv})`, `tf`] >>
  simp[Abbr `s2`] >> conj_tac
  >- (irule for_range_body_ghost_endpoint >> simp[] >> metis_tac[]) >>
  simp[mstore_def, jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  qpat_x_assum `ptr_covers G tn p s sz` mp_tac >>
  qpat_x_assum `tf.t_var = _` mp_tac >> qpat_x_assum `dv <> p` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp[ptr_covers_def, lookup_var_def, op_taint_def,
       FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >> metis_tac[]
QED

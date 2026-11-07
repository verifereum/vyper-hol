(* Source correspondence for the actual post-ADD memory word load. *)
Theory bodyPtrStructLitMemoryRead
Ancestors
  bodyPtrStructLitMemoryUnwrap bodyPtrStructLitSourceFrame
  bodyPtrStructLitFreshGhost exprSimUnwrapProps valueEncodingProps
  loweringPosts exprLoweringProps venomState finite_map bodyPtrDefs
  ptrSafeRun ptrDiscipline venomInst gasSummaryComposePtr typedCopyPtr

Theorem vv_post_memory_word_read:
  vv_post ctx fn cenv cx e es sa sm s0 ee tv (LocatedValue ty p) s /\
  p.ptr_location = LocMemory /\ is_word_type ty ==>
  ty = expr_type e /\
  ?v a. read_result cx tv ee = (INL v,ee) /\
    eval_operand p.ptr_operand s = SOME a /\
    (!tvt. evaluate_type (get_tenv cx) ty = SOME tvt ==>
      mload (w2n a) s = typed_val_to_w256 tvt v)
Proof
  simp[vv_post_def, vv_holds_def] >> rpt strip_tac >>
  gvs[mem_word_at_eq_mload] >> metis_tac[]
QED

Theorem stmt_state_rel_index:
  stmt_state_rel ctx func cenv cx es (s with vs_inst_idx := idx) <=>
  stmt_state_rel ctx func cenv cx es s
Proof
  `(s with <|vs_current_bb := s.vs_current_bb; vs_inst_idx := idx|>) =
   (s with vs_inst_idx := idx)` by simp[venom_state_component_equality] >>
  mp_tac (Q.INST [`lbl` |-> `s.vs_current_bb`] stmt_state_rel_pc) >>
  asm_rewrite_tac[]
QED

Theorem memory_word_load_source_post:
  vv_post ctx fn cenv cx e es sa sm s0 ee tv (LocatedValue ty p) s /\
  p.ptr_location = LocMemory /\ is_word_type ty /\
  eval_operand p.ptr_operand s = SOME a /\
  read_result cx tv ee = (INL v,ee) /\
  sa.cs_next_var <= sm.cs_next_var /\ ~not_fresh_at sm out /\
  not_local_ptr cenv ee.scopes out ==>
  expr_post ctx fn cenv cx e es sa sb s0 ee v (Var out)
    (update_var out (mload (w2n a) s) s with
      vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >>
  drule_all vv_post_memory_word_read >> strip_tac >>
  `vv_post ctx fn cenv cx e es sa sm s0 ee (Value v)
     (LocatedValue ty p) s` by metis_tac[vv_post_read_result] >>
  `stmt_state_rel ctx fn cenv cx ee (update_var out (mload (w2n a) s) s)` by
    (irule stmt_state_rel_update_var >> gvs[vv_post_def]) >>
  `stmt_state_rel ctx fn cenv cx ee
     (update_var out (mload (w2n a) s) s with
       vs_inst_idx := SUC s.vs_inst_idx)` by
    simp[stmt_state_rel_index] >>
  irule expr_post_of_vv_post_load >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (qexists `mload (w2n a) s` >>
    gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  conj_tac >- simp[] >>
  qexistsl [`p`, `s`, `sm`, `ty`] >>
  gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  metis_tac[]
QED

Theorem word_load_endpoint_covers:
  ptr_covers G tn r s sz /\ r <> out ==>
  ptr_covers
    (step_prov PG G (mk_inst id MLOAD [src] [out]) (update_var out w s))
    (step_taint (mk_inst id MLOAD [src] [out]) s (update_var out w s) tn)
    r (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx) sz
Proof
  simp[ptr_covers_def] >> metis_tac[word_load_endpoint_registers]
QED

(* The load address and endpoint are named, but successful source reading is
   derived.  Clean bytes and reservations remain explicit caller obligations. *)
Theorem memory_word_unwrap_continuation:
  vv_post ctx fn cenv cx e es sa sm s0 ee tv (LocatedValue ty p) s /\
  p.ptr_location = LocMemory /\ is_word_type ty /\ p.ptr_operand = Var src /\
  unwrap_value cenv (LocatedValue ty p) sm = (Var out,sb) /\
  fn_has_code sm sb fn /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ptr_covers G tn src s 32 /\ lookup_var src s = SOME a /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) /\
  sa.cs_next_var <= sm.cs_next_var /\ not_local_ptr cenv ee.scopes out /\
  ghost_inv d cenv cx ee G tn s /\
  (!name entry r sz. lookup_scopes name ee.scopes = SOME entry /\
     FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var r) sz) ==> r <> out) /\
  (!r sz. cenv.ce_return_buf = SOME (PtrVar (Var r) sz) ==> r <> out) /\
  (!r sz. cenv.ce_return_pc = SOME (PtrVar (Var r) sz) ==> r <> out) /\
  ghost_kept cenv es sf G0 tn0 initial G tn /\ ~not_fresh_at sf out /\
  G1 = step_prov PG G (mk_inst sm.cs_next_id MLOAD [Var src] [out])
    (update_var out (mload (w2n a) s) s) /\
  tn1 = step_taint (mk_inst sm.cs_next_id MLOAD [Var src] [out]) s
    (update_var out (mload (w2n a) s) s) tn /\
  s1 = (update_var out (mload (w2n a) s) s with
    vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?v. read_result cx tv ee = (INL v,ee) /\
    gas_marked_exec_ptr D (ctx,fn) PG (read_result cx tv)
      (ee,s,G,tn) [] (INL v) ee G1 tn1 (OK s1) /\
    expr_post ctx fn cenv cx e es sa sb s0 ee v (Var out) s1 /\
    ptr_val_ok cx ty v (Var out) G1 tn1 s1 /\
    ghost_inv d cenv cx ee G1 tn1 s1 /\
    ghost_kept cenv es sf G0 tn0 initial G1 tn1 /\
    (!r sz. r <> out /\ ptr_covers G tn r s sz ==>
      ptr_covers G1 tn1 r s1 sz)
Proof
  strip_tac >> drule_all vv_post_memory_word_read >> strip_tac >>
  `eval_operand (Var src) s = SOME a` by simp[eval_operand_def] >>
  gvs[eval_operand_def] >>
  drule_all memory_word_unwrap_code >> strip_tac >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0
     (step_prov PG G (mk_inst sm.cs_next_id MLOAD [Var src] [out])
       (update_var out (mload (w2n a) s) s))
     (step_taint (mk_inst sm.cs_next_id MLOAD [Var src] [out]) s
       (update_var out (mload (w2n a) s) s) tn)
     (OK (update_var out (mload (w2n a) s) s with
       vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule memory_word_unwrap_counted >> metis_tac[]) >>
  qpat_x_assum `s.vs_inst_idx = _` (fn th => rewrite_tac[GSYM th]) >>
  conj_tac >- (irule (cj 1 word_load_marked_read) >> simp[] >>
    conj_tac >- metis_tac[] >>
    qexistsl [`a`, `sm.cs_next_id`, `out`, `Var src`] >>
    simp[eval_operand_def]) >>
  conj_tac >- (irule memory_word_load_source_post >> simp[] >>
    qexistsl [`p`, `sm`, `tv`, `expr_type e`] >> simp[eval_operand_def]) >>
  conj_tac >- (simp[ptr_val_ok_def, mload_output_provenance] >>
    irule (cj 1 mload_ghost_clean) >>
    simp[eval_operand_def] >> metis_tac[]) >>
  conj_tac >- (irule ghost_inv_clean_mload_pc >>
    simp[eval_operand_def] >> metis_tac[]) >>
  conj_tac >- (irule word_load_ghost_kept >>
    simp[eval_operand_def] >> metis_tac[]) >>
  metis_tac[word_load_endpoint_covers]
QED

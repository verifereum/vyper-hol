Theory bodyCreateBlueprintRawOwnedMods
Ancestors
  bodyFullOperandSnapshot[qualified] exprSimWordArgs[qualified]
  wordArgsPtr[qualified] assignTuplePtrCopyLen[qualified]
  valueEncodingProps[qualified] memoryReadProps[qualified]
  bodyPtrDefs ptrDiscipline loweringPosts loweringStateRelDefs
  exprLoweringProps exprLowering context compileEnv freshWrites
  valueEncodingDefs vyperStorageFootprint vyperValue vyperTypeSystem
  venomState venomInst finite_map words

(* The size of the owned allocation is determined by the returned VV tag.
   The two header registers are protected at the later cursor, while the
   payload is protected by the allocation already present before the header. *)
Theorem blueprint_raw_owned_window_mods:
  compile_snapshot_vv ce T vv sm =
    (LocatedValue (vv_type vv) (mk_ptr (Var dst) LocMemory),sd) /\
  ~is_word_type (vv_type vv) /\
  evaluate_type (get_tenv cx) (vv_type vv) = SOME tv /\
  val_wf tv (BytesV bs) /\ val_footprint tv (BytesV bs) <= sz /\
  ptr_val_ok cx (vv_type vv) (BytesV bs) (Var dst) Gu tu u /\
  not_fresh_at sd dst /\ lookup_var dst u = SOME dw /\
  FLOOKUP u.vs_allocas sm.cs_next_id = SOME (w2n dw,sz) /\
  sm.cs_next_id < sd.cs_next_id /\
  (!n b len. local_region ce ee.scopes u n b len ==>
    regions_disjoint (w2n dw) sz b len) /\
  32 + LENGTH bs <= sz /\ w2n dw + 32 < dimword (:256) /\
  w2n dw + sz <= u.vs_alloca_next /\
  u.vs_alloca_next <= h.vs_alloca_next /\ h.vs_alloca_next <= f.vs_alloca_next /\
  mem_bytes_at (w2n dw + 32) (LENGTH bs) u.vs_memory = bs /\
  (!i. w2n dw + 32 <= i /\ i < w2n dw + 32 + LENGTH bs ==> i NOTIN tu.t_mem) /\
  cnt = Var l /\ data = Var q /\
  not_fresh_at sb l /\ not_fresh_at sb q /\
  eval_operand (Var l) h = SOME (n2w (LENGTH bs)) /\
  eval_operand (Var q) h = SOME (n2w (w2n dw + 32)) /\
  op_taint th (Var l) = {} /\ op_prov Gh (Var l) = NONE /\
  ptr_covers Gh th q h (LENGTH bs) /\
  stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func ce cx ee u /\
  local_ptrs_reserved ce sd /\ ci_mono sd sb /\
  wb_frame ce ee ee sd u h /\ ghost_kept_at lo ce ee sd Gu tu u Gh th /\
  wb_frame ce ee ef sb h f /\ ghost_kept_at lo ce ee sb Gh th h Gf tf ==>
  eval_operand cnt f = SOME (n2w (LENGTH bs)) /\
  op_taint tf cnt = {} /\ op_prov Gf cnt = NONE /\
  (cnt <> Lit 0w ==> ?q a. data = Var q /\ lookup_var q f = SOME a /\
    ptr_covers Gf tf q f (LENGTH bs) /\ (bs = [] \/ w2n a + LENGTH bs <= f.vs_alloca_next) /\
    (!i. w2n a <= i /\ i < w2n a + LENGTH bs ==> i NOTIN tf.t_mem) /\
    read_memory (w2n a) (LENGTH bs) f = bs)
Proof
  strip_tac >>
  qpat_x_assum `cnt = Var l` SUBST_ALL_TAC >>
  qpat_x_assum `data = Var q` SUBST_ALL_TAC >>
  `sd.cs_next_var <= sb.cs_next_var /\ sd.cs_next_id <= sb.cs_next_id` by fs[ci_mono_def] >>
  `wb_frame ce ee ef sd u f` by
    (irule (INST_TYPE [``:'a`` |-> ``:256``] exprSimWordArgsTheory.wb_frame_trans) >>
     qpat_assum `wb_frame ce ee ef sb h f` (irule_at Any) >>
     qpat_assum `stmt_state_rel _ ctx func ce cx ee u` (irule_at Any) >> simp[]) >>
  `ghost_kept_at lo ce ee sd Gu tu u Gf tf` by
    (metis_tac[wordArgsPtrTheory.ghost_kept_at_wb_trans]) >>
  `!n b len. local_region ce ee.scopes u n b len ==>
    sz + w2n dw <= b \/ b + len <= w2n dw` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!n b len. _ ==> regions_disjoint _ _ b len` (drule_then mp_tac) >>
     rewrite_tac[regions_disjoint_def] >> decide_tac) >>
  `mem_bytes_at (w2n dw) sz f.vs_memory = mem_bytes_at (w2n dw) sz u.vs_memory` by
    (irule (cj 4 bodyFullOperandSnapshotTheory.compile_snapshot_vv_materialized_frame) >>
     qpat_assum `compile_snapshot_vv ce T vv sm = _` (irule_at Any) >>
     qpat_assum `ptr_val_ok cx _ (BytesV bs) (Var dst) Gu tu u` (irule_at Any) >>
     qpat_assum `ghost_kept_at lo ce ee sd Gu tu u Gf tf` (irule_at Any) >>
     simp[vv_operand_def,mk_ptr_def] >>
     qexistsl [`ef`,`sm.cs_next_id`] >> simp[] >> first_assum ACCEPT_TAC) >>
  `mem_bytes_at (w2n dw + 32) (LENGTH bs) f.vs_memory = bs` by
    (drule_then (qspecl_then [`32`,`LENGTH bs`] mp_tac)
       valueEncodingPropsTheory.mem_bytes_at_translated_window >> simp[]) >>
  `!i. w2n dw + 32 <= i /\ i < w2n dw + 32 + LENGTH bs ==> i NOTIN tf.t_mem` by
    (rpt strip_tac >>
     `w2n dw <= i /\ i < w2n dw + sz` by decide_tac >>
     qpat_assum `ghost_kept_at lo ce ee sd Gu tu u Gf tf`
       (mp_tac o cj 2 o REWRITE_RULE [ghost_kept_at_def]) >>
     disch_then (qspecl_then [`sm.cs_next_id`,`w2n dw`,`sz`,`i`] mp_tac) >>
     simp[] >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `eval_operand (Var l) h = _`
    (assume_tac o REWRITE_RULE [eval_operand_def]) >>
  qpat_x_assum `eval_operand (Var q) h = _`
    (assume_tac o REWRITE_RULE [eval_operand_def]) >>
  `lookup_var l f = SOME (n2w (LENGTH bs)) /\
   lookup_var q f = SOME (n2w (w2n dw + 32))` by
    (conj_tac >> irule exprSimWordArgsTheory.wb_frame_vars >>
     qpat_assum `wb_frame ce ee ef sb h f` (irule_at Any) >> simp[]) >>
  `FLOOKUP Gf l = FLOOKUP Gh l /\ FLOOKUP Gf q = FLOOKUP Gh q /\
   op_taint tf (Var l) = op_taint th (Var l) /\ op_taint tf (Var q) = op_taint th (Var q)` by
    (qpat_assum `ghost_kept_at lo ce ee sb Gh th h Gf tf`
       (mp_tac o cj 1 o REWRITE_RULE [ghost_kept_at_def]) >>
     disch_then (fn thm => mp_tac (Q.SPEC `l` thm) >> mp_tac (Q.SPEC `q` thm)) >> simp[]) >>
  `ptr_covers Gf tf q f (LENGTH bs)` by
    (irule assignTuplePtrCopyLenTheory.ptr_covers_lookup_frame >>
     qpat_assum `ptr_covers Gh th q h (LENGTH bs)` (irule_at Any) >> simp[eval_operand_def]) >>
  `w2n (n2w (w2n dw + 32) : bytes32) = w2n dw + 32` by simp[w2n_n2w] >>
  `w2n dw + 32 + LENGTH bs <= f.vs_alloca_next` by decide_tac >>
  fs[eval_operand_def,op_prov_def,memoryReadPropsTheory.read_memory_eq_mem_bytes_at]
QED

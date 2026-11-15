(* Transport the captured value, with no read of its original source place. *)
Theory bodyMemSnapshotCapturedFrame
Ancestors
  bodyMemSnapshotTargetFrame loweringPosts exprSimProps valueEncodingProofs
  context compileEnv exprLoweringProps vyperState
  valueCopyBytes valueTypingMemoryProps

Theorem snapshot_captured_memory_retag:
  vv_holds ce cx sty raw (LocatedValue lty (mk_ptr op LocMemory)) es s /\
  vv_own ce cx sty sa sb es raw (LocatedValue lty (mk_ptr op LocMemory)) s /\
  read_result cx raw es = (INL v,es) /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) lty = SOME ltv /\
  value_has_type stv v /\ value_has_type ltv v /\
  (sty = lty \/ is_bytestring_type sty /\ is_bytestring_type lty) ==>
  val_wf ltv v /\
  ?w. eval_operand op s = SOME w /\
    val_in_memory ltv v (w2n w) s.vs_memory /\
    vv_own ce cx lty sa sb es (Value v)
      (LocatedValue lty (mk_ptr op LocMemory)) s
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `val_wf ltv v` by metis_tac[value_has_type_memory_wf] >> simp[] >>
  qpat_x_assum `vv_holds _ _ _ _ _ _ _` mp_tac >>
  simp[vv_holds_def, mk_ptr_def] >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `w` strip_assume_tac)) >>
  `val_in_memory stv v (w2n w) s.vs_memory` by metis_tac[] >>
  `val_footprint stv v = val_footprint ltv v` by
    (Cases_on `sty = lty` >- gvs[] >> fs[] >>
     qspecl_then [`get_tenv cx`, `sty`, `lty`, `stv`, `ltv`, `v`]
       mp_tac bytestring_val_footprint_eq >> simp[]) >>
  `val_in_memory ltv v (w2n w) s.vs_memory` by
    (Cases_on `sty = lty` >- gvs[] >> fs[] >>
     qspecl_then [`get_tenv cx`, `sty`, `lty`, `stv`, `ltv`,
       `v`, `w2n w`, `s.vs_memory`] mp_tac
       bytestring_val_in_memory_transfer >> simp[]) >>
  qexists_tac `w` >> simp[] >>
  qpat_x_assum `vv_own _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[vv_own_def, mk_ptr_def, read_result_def, return_def]
QED

Theorem snapshot_captured_memory_target:
  target_post ctx func ce cx es sa sb s0 ee pv vt r z /\
  stmt_state_rel ctx func ce cx es s0 /\ local_ptrs_reserved ce sa /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  (!x. op = Var x ==> not_fresh_at sa x) /\ (!l. op <> Label l) /\
  eval_operand op s0 = SOME w /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  val_wf tv v /\ val_in_memory tv v (w2n w) s0.vs_memory /\
  vv_own ce cx ty origin sa es (Value v)
    (LocatedValue ty (mk_ptr op LocMemory)) s0 ==>
  eval_operand op z = SOME w /\
  val_in_memory tv v (w2n w) z.vs_memory /\
  vv_own ce cx ty origin sb ee (Value v)
    (LocatedValue ty (mk_ptr op LocMemory)) z /\
  vv_at ce cx ty origin sb ee (Value v)
    (LocatedValue ty (mk_ptr op LocMemory)) z
Proof
  strip_tac >> drule_all snapshot_target_operand_frame >> strip_tac >>
  `val_in_memory tv v (w2n w) z.vs_memory /\
   vv_own ce cx ty origin sb ee (Value v)
     (LocatedValue ty (mk_ptr op LocMemory)) z` by
    (Cases_on `val_footprint tv v = 0`
     >- (simp[vv_own_def, mk_ptr_def, read_result_def, return_def] >>
         irule val_in_memory_footprint_agree >> simp[] >>
         qexists_tac `s0.vs_memory` >>
         simp[valueEncodingDefsTheory.mem_bytes_at_def]) >>
     `?aid b sz. FLOOKUP s0.vs_allocas aid = SOME (b,sz) /\
        origin.cs_next_id <= aid /\ aid < sa.cs_next_id /\
        b <= w2n w /\ w2n w + val_footprint tv v <= b + sz /\
        (!n lb len. local_region ce es.scopes s0 n lb len ==>
          b + sz <= lb \/ lb + len <= b)` by
       (qpat_x_assum `vv_own _ _ _ _ _ _ _ _ _` mp_tac >>
        simp[vv_own_def, mk_ptr_def, read_result_def, return_def]) >>
     drule_all snapshot_target_owned_memory_frame >> strip_tac >>
     `!n lb len. local_region ce ee.scopes z n lb len ==>
        b + sz <= lb \/ lb + len <= b` by
       (mp_tac (SPEC_ALL snapshot_target_local_separation) >> simp[] >>
        metis_tac[]) >> simp[] >>
     simp[vv_own_def, mk_ptr_def, read_result_def, return_def] >>
     rpt strip_tac >> gvs[] >>
     qexistsl_tac [`aid`, `b`, `sz`] >> simp[] >>
     metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  simp[] >>
  gvs[vv_at_def, vv_own_def, mk_ptr_def, read_result_def, return_def] >>
  metis_tac[]
QED

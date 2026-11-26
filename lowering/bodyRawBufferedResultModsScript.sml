(* Join the positive raw-call suffixes at their fetched CALL cursor. *)
Theory bodyRawBufferedResultMods
Ancestors
  bodyRawBufferedBytesFrameMods bodyRawBufferedRegisteredPostMods bodyRawBufferedTupleFrameMods
  bodyFullRawCallFinishJoint bodyFullHashKeccakFixed allocationPathGrowth
  freshWrites abiDecodeStaticProps valueEncodingProps
  bodyFullPostsMods bodyFullShadowBodyInv loweringPosts
  exprSimRawCall exprSafeOperand exprLoweringProps ptrDiscipline venomState
  venomMemDefs words arithmetic list

Theorem raw_buffered_header_post_mods[local]:
  stmt_state_rel H ctx func cenv cx es s /\
  immutable_frame_mods func cenv cx es s /\
  ghost_inv_at_mods D lo dep cenv cx es G tn s /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sf /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sf x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sf x) /\
  sf.cs_next_var <= sc.cs_next_var /\
  (!x. not_fresh_at sc x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)) /\
  u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
  LENGTH s.vs_memory <= LENGTH u.vs_memory /\
  u.vs_data_section = s.vs_data_section /\ u.vs_call_ctx = s.vs_call_ctx /\
  u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
  u.vs_immutables = s.vs_immutables /\
  tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
  MEM alloc (fn_insts func) /\ alloc.inst_opcode = ALLOCA /\
  alloc.inst_outputs = [q] /\ not_local_ptr cenv es.scopes q /\
  sf.cs_next_id <= alloc.inst_id /\
  FLOOKUP u.vs_allocas alloc.inst_id = SOME (a,cap) /\ 32 <= cap /\
  u.vs_memory = (mstore a len s).vs_memory /\
  tnf.t_mem = tn.t_mem DIFF {i | a <= i /\ i < a+32} /\
  vv_post H ctx func cenv cx e es0 sf sb s0 es (Value v)
    (LocatedValue ty (mk_ptr result LocMemory)) u ==>
  vv_post_mods H ctx func cenv cx e es0 sf sb s0 es (Value v)
    (LocatedValue ty (mk_ptr result LocMemory)) u /\
  ghost_inv_at_mods D lo dep cenv cx es Gf tnf u
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `allocation_growth s u` by (irule allocation_growth_map_eq >> simp[]) >>
  `!x. not_fresh_at sf x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!x. not_fresh_at sc x ==> _` irule >>
     irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sf` >> simp[]) >>
  match_mp_tac (Q.INST [`writes` |-> `[(alloc.inst_id,a,32)]`]
    raw_buffered_registered_post_mods) >>
  simp[venomMemDefsTheory.regions_disjoint_def] >>
  conj_tac
  >- (qexistsl_tac [`cap`,`alloc`] >> simp[] >>
      qpat_assum `u.vs_allocas = s.vs_allocas` (pure_once_rewrite_tac o single o SYM) >>
      first_assum ACCEPT_TAC) >>
  rpt gen_tac >> disch_tac >>
  Cases_on `k = 0` >- simp[valueEncodingDefsTheory.mem_bytes_at_def] >>
  irule mstore_mem_bytes_at_disjoint >> decide_tac
QED

Theorem raw_buffered_result_path_mods:
  compile_raw_call_finish to_op dp dl gas_op val_op
    call_ty n rev ov op sa = (result,sb) /\
  (case call_ty of
     RegularCall => emit_op CALL [gas_op;to_op;val_op;dp;dl;op;Lit (n2w n)]
   | StaticCall => emit_op STATICCALL [gas_op;to_op;dp;dl;op;Lit (n2w n)]
   | DelegateCall => emit_op DELEGATECALL [gas_op;to_op;dp;dl;op;Lit (n2w n)]) sa = (ok,sc) /\
  0 < n /\ (~rev \/ success) /\
  eval_operand ok s = SOME (if success then 1w else 0w) /\ op_taint tn ok = {} /\
  fn_has_code sc sb func /\ fn_inst_ids_distinct func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size func s <= w2n s.vs_initial_fmp) /\
  allocas_from lo s /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = sc.cs_current_bb /\
  s.vs_inst_idx = LENGTH sc.cs_current_insts /\ LENGTH s.vs_returndata < dimword (:256) /\
  stmt_state_rel (H0:(bool # 256 word # type_value) list # num list) ctx func cenv cx es s /\
  wb_frame cenv es0 es sf s0 s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ghost_kept_at lo cenv es0 sf G0 tn0 s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sf x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sf x) /\
  expr_has_effect e /\ post_value_type cenv e = expr_type e /\
  lowered_value_type cenv e = expr_type e /\
  expr_type e = (if rev then BaseT (BytesT (Dynamic n))
                 else TupleT [BaseT BoolT;BaseT (BytesT (Dynamic n))]) /\
  (?x w alloc q pre (ro:bytes32) old_tn.
     ov = Var x /\ n < dimword (:256) /\ 64 + ((n+31) DIV 32)*32 < dimword (:256) /\
     MEM alloc (fn_insts func) /\ alloc.inst_opcode = ALLOCA /\
     alloc.inst_outputs = [q] /\ not_local_ptr cenv es.scopes q /\
     FLOOKUP s.vs_allocas alloc.inst_id = SOME (w2n w,32 + ((n+31) DIV 32)*32) /\
     local_ptrs_reserved cenv sf /\ local_ptrs_reserved cenv sc /\
     sf.cs_next_var <= sc.cs_next_var /\ sf.cs_next_id <= alloc.inst_id /\
     alloc.inst_id < sc.cs_next_id /\ MAP FDOM es0.scopes = MAP FDOM es.scopes /\
     not_fresh_at sc x /\ lookup_var x s = SOME w /\ ptr_covers G tn x s (32 + ((n+31) DIV 32)*32) /\
     w2n ro = w2n w+32 /\
     s.vs_memory = (write_memory_with_expansion (w2n ro) (TAKE n s.vs_returndata) pre).vs_memory /\
     tn.t_mem = old_tn.t_mem DIFF
       {i | w2n ro <= i /\ i < w2n ro + LENGTH (TAKE n s.vs_returndata)} /\
     (~rev ==> safe_operand sc ok /\ evaluate_type (get_tenv cx) (expr_type e) =
       SOME (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic n))]))) ==>
  let v = if rev then BytesV (TAKE n s.vs_returndata)
          else ArrayV (TupleV [BoolV success;BytesV (TAKE n s.vs_returndata)]);
      vv = LocatedValue (expr_type e) (mk_ptr result LocMemory)
  in
  ?u Gf tnf.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,Gf,tnf)) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func u /\
    s0.vs_alloca_next <= u.vs_alloca_next /\
    ghost_kept_at lo cenv es0 sf G0 tn0 s0 Gf tnf /\
    ptr_vv_ok cx (post_value_type cenv e) (Value v) vv es Gf tnf u /\
    ptr_buf_ok cenv e result Gf u /\
    (!H:(bool # 256 word # type_value) list # num list. !D.
       stmt_state_rel H ctx func cenv cx es s /\ immutable_frame_mods func cenv cx es s /\
       storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods D lo dep cenv cx es G tn s ==>
       vv_post_mods H ctx func cenv cx e es0 sf sb s0 es (Value v) vv u /\
       vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) es (Value v) vv u /\
       vv_own cenv cx (post_value_type cenv e) sf sb es (Value v) vv u /\
       (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
       ghost_inv_at_mods D lo dep cenv cx es Gf tnf u)
Proof
  simp_tac bool_ss [LET_THM] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?x w alloc q pre ro old_tn. _`
    (qx_choose_then `x` (qx_choose_then `w` (qx_choose_then `alloc`
      (qx_choose_then `q` (qx_choose_then `pre` (qx_choose_then `ro`
        (qx_choose_then `old_tn` (map_every assume_tac o CONJUNCTS)))))))) >>
  qpat_x_assum `ov = Var x` SUBST_ALL_TAC >>
  Cases_on `rev` >- suspend "bytes" >>
  suspend "tuple"
QED

Resume raw_buffered_result_path_mods[bytes]:
  `success` by fs[] >>
  `eval_operand ok s = SOME 1w /\ expr_type e = BaseT (BytesT (Dynamic n))` by simp[] >>
  qpat_x_assum `expr_type e = if T then _ else _` kall_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    (disch_tac >> qpat_assum `ctx_has_dalloca ctx ==> _` drule >> simp[]) >>
  drule_all (SIMP_RULE bool_ss []
    (Q.INST [`data` |-> `u.vs_returndata`] raw_call_positive_payload_cut)) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `mem_bytes_at (w2n w+32) (LENGTH (TAKE n s.vs_returndata)) s.vs_memory =
      TAKE n s.vs_returndata` by simp[] >>
  `!i. w2n w+32 <= i /\ i < w2n w+32+LENGTH (TAKE n s.vs_returndata) ==>
       i NOTIN tn.t_mem` by simp[] >>
  pure_rewrite_tac [COND_CLAUSES] >>
  qabbrev_tac `v = BytesV (TAKE n s.vs_returndata)` >>
  qabbrev_tac `vv = LocatedValue (BaseT (BytesT (Dynamic n))) (mk_ptr result LocMemory)` >>
  `v = BytesV (TAKE n s.vs_returndata) /\ vv = LocatedValue (expr_type e) (mk_ptr result LocMemory)` by
    simp[Abbr `v`,Abbr `vv`] >>
  drule_all raw_buffered_bytes_finish_frame >>
  disch_then (qspec_then `PG` (qx_choose_then `u` (qx_choose_then `Gf` (qx_choose_then `tnf`
    (map_every assume_tac o CONJUNCTS))))) >>
  qexistsl_tac [`u`,`Gf`,`tnf`] >>
  asm_rewrite_tac[] >>
  conj_tac
  >- (qhdtm_x_assum `ptr_vv_ok` mp_tac >>
      qpat_assum `post_value_type cenv e = _` (pure_once_rewrite_tac o single) >>
      qpat_assum `expr_type e = _` (pure_once_rewrite_tac o single) >>
      qpat_assum `vv = _` (pure_once_rewrite_tac o single) >>
      asm_rewrite_tac[]) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!H. stmt_state_rel H _ _ _ _ _ s /\ _ ==> _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (qhdtm_assum `vv_post`
       (strip_assume_tac o PURE_REWRITE_RULE [vv_post_def]) >>
     qpat_assum `stmt_state_rel H _ _ _ _ _ u`
       (mp_then Any ACCEPT_TAC stmt_state_rel_allocas_below_fmp)) >>
  `vv_post H ctx func cenv cx e es0 sf sb s0 es (Value v)
     (LocatedValue (expr_type e) (mk_ptr result LocMemory)) u` by
    (qpat_assum `vv = _` (pure_once_rewrite_tac o single o SYM) >> first_assum ACCEPT_TAC) >>
  `vv_post_mods H ctx func cenv cx e es0 sf sb s0 es (Value v)
     (LocatedValue (expr_type e) (mk_ptr result LocMemory)) u /\
   ghost_inv_at_mods D lo dep cenv cx es Gf tnf u` by
    (`32 <= 32 + ((n+31) DIV 32)*32` by decide_tac >>
     drule_all raw_buffered_header_post_mods >> asm_rewrite_tac[]) >>
  map_every (fn c => qhdtm_x_assum c mp_tac) [`vv_store_bound`,`vv_own`,`vv_post_mods`] >>
  map_every (fn pat => qpat_assum pat (pure_once_rewrite_tac o single))
    [`vv = _`,`post_value_type cenv e = _`,`lowered_value_type cenv e = _`,
     `expr_type e = _`,`result = _`,`v = _`] >>
  rpt disch_tac >> asm_rewrite_tac[]
QED

Resume raw_buffered_result_path_mods[tuple]:
  qpat_assum `compile_raw_call_finish _ _ _ _ _ _ _ F _ _ _ = _`
    (mp_then Any mp_tac raw_call_nonrevert_finish_code) >>
  disch_then (qx_choose_then `ok1` (qx_choose_then `sc1`
    (map_every assume_tac o CONJUNCTS))) >>
  `(ok1,sc1) = (ok,sc)` by (Cases_on `call_ty` >> fs[]) >>
  pop_assum (map_every SUBST_ALL_TAC o CONJUNCTS o REWRITE_RULE [pairTheory.PAIR_EQ]) >>
  `safe_operand sc (Var x)` by simp[exprSafeOperandTheory.safe_operand_def] >>
  `expr_type e = TupleT [BaseT BoolT;BaseT (BytesT (Dynamic n))] /\
   safe_operand sc ok /\ evaluate_type (get_tenv cx) (expr_type e) =
     SOME (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic n))])` by simp[] >>
  qpat_x_assum `expr_type e = if F then _ else _` kall_tac >>
  pure_rewrite_tac [COND_CLAUSES] >>
  qabbrev_tac `v = ArrayV (TupleV [BoolV success;BytesV (TAKE n s.vs_returndata)])` >>
  `v = ArrayV (TupleV [BoolV success;BytesV (TAKE n s.vs_returndata)])` by simp[Abbr `v`] >>
  drule_all (SIMP_RULE bool_ss [] (Q.INST
    [`data` |-> `s.vs_returndata`, `vv` |-> `LocatedValue (expr_type e) (mk_ptr result LocMemory)`]
    raw_buffered_tuple_finish_frame_registered)) >>
  disch_then (qspecl_then [`dep`,`PG`] (qx_choose_then `u` (qx_choose_then `Gf`
    (qx_choose_then `tnf` (map_every assume_tac o CONJUNCTS))))) >>
  qpat_x_assum `?i b. _` (qx_choose_then `i` (qx_choose_then `b`
    (map_every assume_tac o CONJUNCTS o CONV_RULE (DEPTH_CONV BETA_CONV) o PURE_REWRITE_RULE [LET_THM]))) >>
  `s0.vs_alloca_next <= u.vs_alloca_next` by
    (drule allocationGrowthTheory.allocation_growth_next >> decide_tac) >>
  qexistsl_tac [`u`,`Gf`,`tnf`] >> asm_rewrite_tac[] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!H. stmt_state_rel H _ _ _ _ _ s /\ _ ==> _` (qspec_then `H` mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (qhdtm_assum `vv_post` (strip_assume_tac o PURE_REWRITE_RULE [vv_post_def]) >>
     qpat_assum `stmt_state_rel H _ _ _ _ _ u`
       (mp_then Any ACCEPT_TAC stmt_state_rel_allocas_below_fmp)) >>
  `vv_post_mods H ctx func cenv cx e es0 sf sb s0 es (Value v)
      (LocatedValue (expr_type e) (mk_ptr result LocMemory)) u /\
   ghost_inv_at_mods D lo dep cenv cx es Gf tnf u` by
    (match_mp_tac (Q.INST [`writes` |->
      `[(alloc.inst_id,w2n w,32);(i.inst_id,b,64+((n+31) DIV 32)*32)]`]
      raw_buffered_registered_post_mods) >> asm_rewrite_tac[]) >>
  map_every (fn c => qhdtm_x_assum c mp_tac) [`vv_store_bound`,`vv_own`,`vv_post_mods`] >>
  map_every (fn pat => qpat_assum pat (pure_once_rewrite_tac o single))
    [`post_value_type cenv e = _`,`lowered_value_type cenv e = _`,`expr_type e = _`,`v = _`] >>
  rpt disch_tac >> asm_rewrite_tac[]
QED

Finalise raw_buffered_result_path_mods

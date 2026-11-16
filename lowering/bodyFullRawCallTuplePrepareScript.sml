(* Conditional assembly of the tuple suffix.  The four closed antecedents are
   discharged by the actual finite and spatial producers at publication. *)
Theory bodyFullRawCallTuplePrepare
Ancestors
  bodyFullRawCallTupleAllocFrame bodyFullAllocGeneric rawCallBufferPtr
  exprSimRawCall exprSimRawCallCalldata fragGasSeqPtr instSeqComposePtr
  loweringStateRelDefs ptrDiscipline venomState bodyPtrDefs
  exprLoweringProps venomMemDefs bodyPtrIfExpAllocFrame

Theorem raw_call_tuple_seq_ghost_cursor_unique:
  !code s G tn G1 tn1 G2 tn2 k.
    EVERY (\i. ~is_terminator i.inst_opcode) code /\
    inst_seq_ptr D1 lo ctx fn PG G tn code s G1 tn1 /\
    inst_seq_ptr D2 lo ctx fn PG G tn code
      (s with vs_inst_idx := k) G2 tn2 ==>
    G1 = G2 /\ tn1 = tn2
Proof
  Induct_on `code` >- simp[inst_seq_ptr_def] >>
  rpt gen_tac >>
  simp[inst_seq_ptr_def] >> strip_tac >>
  Cases_on `step_inst_base h s` >>
  gvs[instIdxIndepTheory.step_inst_inst_idx_indep,
      instIdxIndepTheory.exec_result_map_def] >>
  first_x_assum irule >>
  qexistsl_tac [`step_prov PG G h v`, `SUC k`,
    `v with vs_inst_idx := SUC s.vs_inst_idx`, `step_taint h s v tn`] >>
  simp[]
QED

Theorem raw_call_tuple_suffix_prepared:
  (!z sa s1 cmp n s2 cap s3 sb x s b G tn lo ctx func PG t.
    emit_op RETURNDATASIZE [] sa = (z,s1) /\
    emit_op LT [z;Lit (n2w n)] s1 = (cmp,s2) /\
    compile_select cmp z (Lit (n2w n)) s2 = (cap,s3) /\
    emit_void MSTORE [Var x;cap] s3 = ((),sb) /\
    0 < n /\ n < dimword (:256) /\
    64 + ((n+31) DIV 32)*32 < dimword (:256) /\
    safe_operand sa (Var x) /\ lookup_var x s = SOME (n2w b) /\
    b + (32 + ((n+31) DIV 32)*32) < dimword (:256) /\
    ptr_covers G tn x s (32 + ((n+31) DIV 32)*32) /\
    LENGTH s.vs_returndata < dimword (:256) /\
    mem_bytes_at (b+32) (LENGTH (TAKE n s.vs_returndata)) s.vs_memory =
      TAKE n s.vs_returndata /\
    (!i. b+32 <= i /\ i < b+32+LENGTH (TAKE n s.vs_returndata) ==>
      i NOTIN tn.t_mem) /\
    allocas_from lo s /\ ~ctx_has_dalloca ctx /\
    run_inst_seq (emitted_insts sa sb) s = OK t ==>
    ?Gf tnf.
      (!D. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s Gf tnf) /\
      ptr_covers Gf tnf x t (32 + ((n+31) DIV 32)*32) /\
      (!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
        val_in_memory (BaseTV (BytesT (Dynamic n)))
          (BytesV (TAKE n s.vs_returndata)) b mem) /\
      tnf.t_mem = tn.t_mem DIFF {i | b <= i /\ i < b+32} /\
      tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
      (!v. not_fresh_at sa v ==>
        lookup_var v t = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
        op_taint tnf (Var v) = op_taint tn (Var v)) /\
      (t with vs_vars := s.vs_vars) =
        mstore b (n2w (LENGTH (TAKE n s.vs_returndata))) s) ==>
  (!p ok sa s1 dst s2 x n sb bs a b s G tn success lo ctx func PG t.
    emit_void MSTORE [Var p;ok] sa = ((),s1) /\
    emit_op ADD [Var p;Lit 32w] s1 = (dst,s2) /\
    emit_void MCOPY [dst;Var x;Lit (n2w (32 + ((n+31) DIV 32)*32))]
      s2 = ((),sb) /\
    safe_operand sa (Var p) /\ safe_operand sa (Var x) /\ safe_operand sa ok /\
    0 < n /\ LENGTH bs <= n /\
    64 + ((n+31) DIV 32)*32 < dimword (:256) /\
    a + (32 + ((n+31) DIV 32)*32) < dimword (:256) /\
    b + (64 + ((n+31) DIV 32)*32) < dimword (:256) /\
    lookup_var x s = SOME (n2w a) /\ lookup_var p s = SOME (n2w b) /\
    ptr_covers G tn x s (32 + ((n+31) DIV 32)*32) /\
    ptr_covers G tn p s (64 + ((n+31) DIV 32)*32) /\
    eval_operand ok s = SOME (if success then 1w else 0w) /\ op_taint tn ok = {} /\
    (a+32+LENGTH bs <= b \/ b+32 <= a) /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bs) a mem) /\
    allocas_from lo s /\ ~ctx_has_dalloca ctx /\
    run_inst_seq (emitted_insts sa sb) s = OK t ==>
    let count = 32 + ((n+31) DIV 32)*32;
        dirty = tn.t_mem DIFF {i | b <= i /\ i < b+32}
    in ?Gf tnf.
      (!D. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s Gf tnf) /\
      ptr_covers Gf tnf p t (64 + ((n+31) DIV 32)*32) /\
      (!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
        val_in_memory (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic n))])
          (ArrayV (TupleV [BoolV success;BytesV bs])) b mem) /\
      tnf.t_mem =
        ((dirty DIFF {i | b+32 <= i /\ i < b+32+count}) UNION
          {b+32+i | i < count /\ a+i IN dirty}) /\
      tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
      (!v. not_fresh_at sa v ==>
        lookup_var v t = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
        op_taint tnf (Var v) = op_taint tn (Var v)) /\
      (t with vs_vars := s.vs_vars) =
        mcopy (b+32) a count (mstore b (val_to_w256 (BoolV success)) s)) ==>
  (!H ctx func cenv cx es s inst q b k sf es0 s0 lo.
    stmt_state_rel (H:(bool # 256 word # type_value) list # num list)
      ctx func cenv cx es s /\
    fn_inst_ids_distinct func /\ MEM inst (fn_insts func) /\
    inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [q] /\
    not_local_ptr cenv es.scopes q /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,k) /\
    sf.cs_next_id <= inst.inst_id /\ local_ptrs_reserved cenv sf /\
    MAP FDOM es0.scopes = MAP FDOM es.scopes /\
    (!x. not_fresh_at sf x ==> lookup_var x s = lookup_var x s0) /\
    (!aid row. FLOOKUP s0.vs_allocas aid = SOME row ==>
      FLOOKUP s.vs_allocas aid = SOME row) /\ allocas_from lo s ==>
    lo <= b /\
    (!aid a m. FLOOKUP s.vs_allocas aid = SOME (a,m) /\ aid < inst.inst_id ==>
      a+m <= b \/ b+k <= a) /\
    (!name a m i. local_region cenv es.scopes s name a m /\
      a <= i /\ i < a+m ==> ~(b <= i /\ i < b+k)) /\
    (!aid a m i. FLOOKUP s0.vs_allocas aid = SOME (a,m) /\
      aid < sf.cs_next_id /\ a <= i /\ i < a+m ==> ~(b <= i /\ i < b+k)) /\
    (!name a m i. local_region cenv es0.scopes s0 name a m /\
      a <= i /\ i < a+m ==> ~(b <= i /\ i < b+k))) ==>
  (!H ctx func cenv cx es s sf t Gf G tnf tn R lo s0 es0 G0 tn0 dep.
    stmt_state_rel (H:(bool # 256 word # type_value) list # num list)
      ctx func cenv cx es s /\
    local_ptrs_reserved cenv sf /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sf x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sf x) /\
    (!x. not_fresh_at sf x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tnf (Var x) = op_taint tn (Var x)) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
    t.vs_transient = s.vs_transient /\ t.vs_immutables = s.vs_immutables /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!i. i NOTIN R ==> mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
    (!i. i NOTIN R /\ i IN tnf.t_mem ==> i IN tn.t_mem) /\
    (!i. i < lo ==> i NOTIN R) /\
    (!name a m i. local_region cenv es.scopes s name a m /\
      a <= i /\ i < a+m ==> i NOTIN R) /\
    (!aid a m i. FLOOKUP s0.vs_allocas aid = SOME (a,m) /\
      aid < sf.cs_next_id /\ a <= i /\ i < a+m ==> i NOTIN R) /\
    (!name a m i. local_region cenv es0.scopes s0 name a m /\
      a <= i /\ i < a+m ==> i NOTIN R) /\
    ghost_kept_at lo cenv es0 sf G0 tn0 s0 G tn ==>
    ghost_kept_at lo cenv es0 sf G0 tn0 s0 Gf tnf /\
    (!D. ghost_inv_at D lo dep cenv cx es G tn s ==>
      ghost_inv_at D lo dep cenv cx es Gf tnf t)) ==>
  !n sa result sb cenv e cx H0 ctx func es s es0 sf s0 alloc q w ov ok
    ovx G tn success lo G0 tn0 explicit PG t dep.
  (if n > 0 then
       do z <- emit_op RETURNDATASIZE [];
          cmp <- emit_op LT [z;Lit (n2w n)];
          cap <- compile_select cmp z (Lit (n2w n));
          emit_void MSTORE [ov;cap];
          buf <- compile_alloc_buffer (64 + ((n + 31) DIV 32) * 32);
          emit_void MSTORE [buf.buf_operand;ok];
          dst <- emit_op ADD [buf.buf_operand;Lit 32w];
          emit_void MCOPY [dst;ov;Lit (n2w (32 + ((n + 31) DIV 32) * 32))];
          return buf.buf_operand od
     else return ok) sa = (result,sb) /\
  0 < n /\
  post_value_type cenv e = TupleT [BaseT BoolT;BaseT (BytesT (Dynamic n))] /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) =
    SOME (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic n))]) /\
  type_memory_bytes cenv (lowered_value_type cenv e) <=
    64 + ((n + 31) DIV 32) * 32 /\
  stmt_state_rel (H0 : (bool # 256 word # type_value) list # num list)
    ctx func cenv cx es s /\
  wb_frame cenv es0 es sf s0 s /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  MEM alloc (fn_insts func) /\ alloc.inst_opcode = ALLOCA /\
  alloc.inst_outputs = [q] /\ not_local_ptr cenv es.scopes q /\
  FLOOKUP s.vs_allocas alloc.inst_id =
    SOME (w2n w,32 + ((n + 31) DIV 32) * 32) /\
  local_ptrs_reserved cenv sf /\ local_ptrs_reserved cenv sa /\
  sf.cs_next_var <= sa.cs_next_var /\ sf.cs_next_id <= alloc.inst_id /\
  alloc.inst_id < sa.cs_next_id /\
  MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at sf x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at sf x) /\
  safe_operand sa ov /\ safe_operand sa ok /\
  ov = Var ovx /\
  FLOOKUP G ovx = SOME (w2n w,32 + ((n + 31) DIV 32) * 32) /\
  op_taint tn ov = {} /\ op_taint tn ok = {} /\
  eval_operand ov s = SOME w /\
  eval_operand ok s = SOME (if success then 1w else 0w) /\
  LENGTH s.vs_returndata < dimword (:256) /\
  mem_bytes_at (w2n w + 32) (LENGTH (TAKE n s.vs_returndata)) s.vs_memory =
    TAKE n s.vs_returndata /\
  (!i. w2n w + 32 <= i /\
       i < w2n w + 32 + LENGTH (TAKE n s.vs_returndata) ==>
       i NOTIN tn.t_mem) /\
  64 + ((n + 31) DIV 32) * 32 < dimword (:256) /\
  n < dimword (:256) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ghost_kept_at lo cenv es0 sf G0 tn0 s0 G tn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq_mem_ok (emitted_insts sa sb) s /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?Gf tnf p.
    result = Var p /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
       (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tnf)) /\
    ptr_covers Gf tnf p t (64 + ((n + 31) DIV 32) * 32) /\
    (!tw mem. eval_operand result t = SOME tw /\
       mem_agree_outside tnf.t_mem t.vs_memory mem ==>
       val_in_memory (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic n))])
         (ArrayV (TupleV [BoolV success;BytesV (TAKE n s.vs_returndata)]))
         (w2n tw) mem) /\
    ptr_vv_ok cx (post_value_type cenv e)
      (Value (ArrayV (TupleV [BoolV success;BytesV (TAKE n s.vs_returndata)])))
      (LocatedValue (expr_type e) (mk_ptr result LocMemory)) es Gf tnf
      (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    ptr_buf_ok cenv e result Gf
      (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    ghost_kept_at lo cenv es0 sf G0 tn0 s0 Gf tnf /\
    (!D. ghost_inv_at D lo dep cenv cx es G tn s ==>
       ghost_inv_at D lo dep cenv cx es Gf tnf
         (t with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  disch_then (mk_asm "length") >>
  disch_then (mk_asm "copy") >>
  disch_then (mk_asm "separation") >>
  disch_then (mk_asm "frame") >>
  rpt gen_tac >> strip_tac >>
  drule_all raw_call_nonrevert_suffix_code >> strip_tac >>
  suspend "assemble"
QED

Resume raw_call_tuple_suffix_prepared[assemble]:
  qpat_x_assum `(if _ then _ else _) _ = _` kall_tac >>
  `stmt_state_rel H0 ctx func cenv cx es (s with vs_fmp := s.vs_fmp)` by simp[] >>
  qpat_assum `stmt_state_rel H0 _ _ _ _ _ (s with vs_fmp := _)`
    (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) mp_tac
      raw_call_output_prefix_ready) >>
  disch_then (drule_at (Pat `emit_op RETURNDATASIZE _ _ = _`)) >>
  disch_then (drule_at (Pat `emit_op LT _ _ = _`)) >>
  disch_then (drule_at (Pat `compile_select _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `emit_void MSTORE _ _ = _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >> simp[] >>
  disch_then drule_all >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa s4) s = OK u` >>
  `u with vs_fmp := s.vs_fmp = u` by
    (qpat_assum `u.vs_fmp = _` (SUBST1_TAC o SYM) >> simp[]) >> fs[] >>
  `w2n w + (32 + ((n+31) DIV 32)*32) < dimword (:256)` by
    (fs[stmt_state_rel_def, alloca_inv_def, alloca_next_valid_def,
        alloca_room_def] >> res_tac >> decide_tac) >>
  `ptr_covers G tn ovx s (32 + ((n+31) DIV 32)*32)` by
    (gvs[ptr_covers_def, eval_operand_def]) >>
  gvs[eval_operand_def] >>
  asm "length" (drule_at (Pat `emit_op RETURNDATASIZE _ _ = _`)) >>
  disch_then (drule_at (Pat `emit_op LT _ _ = _`)) >>
  disch_then (drule_at (Pat `compile_select _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `emit_void MSTORE _ _ = _`)) >>
  disch_then (qspecl_then [`s`,`w2n w`] mp_tac) >>
  simp[] >> disch_then drule_all >> strip_tac >>
  suspend "length_frame"
QED

Resume raw_call_tuple_suffix_prepared[length_frame]:
  qpat_x_assum `!func' PG. ?Gf tnf. _`
    (qspecl_then [`func`,`PG`] (qx_choose_then `G1` (qx_choose_then `tn1` strip_assume_tac))) >>
  asm "separation" (fn sep =>
    qpat_assum `stmt_state_rel H0 ctx func cenv cx es s`
      (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) mp_tac sep)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `_.inst_outputs = _`)) >>
  disch_then (qspecl_then [`sf`,`es`,`s`,`lo`] mp_tac) >>
  simp[] >> strip_tac >>
  suspend "length_transport"
QED

Resume raw_call_tuple_suffix_prepared[length_transport]:
  `!x. not_fresh_at sf x ==>
     lookup_var x u = lookup_var x s /\ FLOOKUP G1 x = FLOOKUP G x /\
     op_taint tn1 (Var x) = op_taint tn (Var x)` by
    (gen_tac >> disch_tac >>
     qpat_x_assum `!v. not_fresh_at sa v ==> _` irule >>
     irule loweringShapeDefsTheory.not_fresh_at_mono >>
     qexists_tac `sf` >> simp[]) >>
  qpat_assum `u with vs_vars := _ = _`
    (strip_assume_tac o SRULE [venom_state_component_equality, mstore_def, LET_THM]) >>
  qpat_x_assum `u.vs_memory = _` kall_tac >>
  `u.vs_memory = (mstore (w2n w) (n2w (LENGTH (TAKE n s.vs_returndata))) s).vs_memory` by
    (qpat_assum `u with vs_vars := _ = _`
      (mp_tac o Q.AP_TERM `\v. v.vs_memory`) >> simp[]) >>
  asm "frame" (fn frame =>
    qpat_assum `stmt_state_rel H0 ctx func cenv cx es s`
      (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) mp_tac frame)) >>
  disch_then (drule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`u`,`G1`,`tn1`] mp_tac) >>
  disch_then (qspecl_then [`{i | w2n w <= i /\ i < w2n w + (32*((n+31) DIV 32)+32)}`,`dep`] mp_tac) >>
  simp[] >>
  impl_tac >-
    (conj_tac >-
       (rpt strip_tac >> irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >>
        decide_tac) >>
     conj_tac >-
       (rpt gen_tac >> disch_tac >>
        qpat_x_assum `!name a m i. local_region cenv es.scopes s name a m /\ _ ==> _`
          (qspecl_then [`name`,`a`,`m`,`i`] mp_tac) >>
        simp[]) >>
     conj_tac >-
       (rpt strip_tac >>
        qpat_assum `wb_frame cenv es0 es sf s0 s`
          (strip_assume_tac o REWRITE_RULE [loweringPostsTheory.wb_frame_def]) >>
        qpat_x_assum `!aid a m i. FLOOKUP s.vs_allocas _ = _ /\ _ ==> _`
          (qspecl_then [`aid`,`a`,`m`,`i`] mp_tac) >>
        simp[]) >>
     rpt strip_tac >>
     `local_region cenv es.scopes s name a m` by
       (irule exprSimPropsTheory.local_region_frame_fwd >>
        qexistsl_tac [`s0`,`sf`,`es0.scopes`] >>
        fs[loweringPostsTheory.wb_frame_def]) >>
     metis_tac[]) >>
  strip_tac >> suspend "allocation"
QED

Resume raw_call_tuple_suffix_prepared[allocation]:
  `cs_extends s4 s5` by metis_tac[loweringHaltTheory.compile_alloc_buffer_extends] >>
  `cs_extends s5 s6 /\ cs_extends s6 s7 /\ cs_extends s7 sb` by
    (mp_tac (Q.SPECL [`MSTORE`,`[buf.buf_operand;ok]`,`s5`] exprLoweringPropsTheory.ci_mono_emit_void) >>
     mp_tac (Q.SPECL [`MCOPY`,`[dst;Var ovx;Lit (n2w (32*((n+31) DIV 32)+32))]`,`s7`] exprLoweringPropsTheory.ci_mono_emit_void) >>
     simp[exprLoweringPropsTheory.ci_mono_def] >>
     metis_tac[exprSimAccountsTheory.emit_op_extends_next_var]) >>
  `cs_extends s5 sb` by metis_tac[compileEnvTheory.cs_extends_trans] >>
  `fn_has_code s4 s5 func` by metis_tac[fragExecTheory.fn_has_code_mid] >>
  qpat_assum `stmt_state_rel H0 ctx func cenv cx es u`
    (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) mp_tac
      bodyPtrIfExpAllocCompilerTheory.compile_alloc_buffer_raw_step) >>
  disch_then (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
  disch_then drule_all >> strip_tac >>
  rename1 `step_inst_base (mk_inst s4.cs_next_id ALLOCA _ [out]) u = OK u2` >>
  drule loweringHaltTheory.compile_alloc_buffer_insts >> strip_tac >>
  `emitted_insts s4 s5 =
     [mk_inst s4.cs_next_id ALLOCA [Lit (n2w (32*((n+31) DIV 32)+64))] [out]]` by
    (gvs[exprLoweringPropsTheory.emitted_insts_def, exprLoweringPropsTheory.DROP_PREFIX]) >>
  `inst_extends s5 sb` by
    (imp_res_tac emitHelperPropsTheory.inst_extends_emit_void >>
     imp_res_tac emitHelperPropsTheory.inst_extends_emit_op >>
     metis_tac[emitHelperPropsTheory.inst_extends_trans]) >>
  `inst_extends s4 s5` by gvs[emitHelperPropsTheory.inst_extends_def] >>
  `emitted_insts sa sb = emitted_insts sa s4 ++
      (emitted_insts s4 s5 ++ emitted_insts s5 sb)` by
    (qpat_assum `inst_extends sa s4` mp_tac >>
     qpat_assum `inst_extends s4 sb` mp_tac >>
     qpat_assum `inst_extends s4 s5` mp_tac >>
     qpat_assum `inst_extends s5 sb` mp_tac >>
     rpt (pop_assum kall_tac) >>
     pure_rewrite_tac [emitHelperPropsTheory.inst_extends_def] >>
     metis_tac[exprLoweringPropsTheory.emitted_insts_append]) >>
  `run_inst_seq (emitted_insts s5 sb) u2 = OK t` by
    (qpat_x_assum `run_inst_seq (emitted_insts sa sb) s = OK t` mp_tac >>
     qpat_assum `emitted_insts sa sb = _` (fn th => pure_once_rewrite_tac[th]) >>
     qpat_assum `run_inst_seq (emitted_insts sa s4) s = OK u`
       (mp_then Any (fn th => pure_once_rewrite_tac[th]) run_inst_seq_append) >>
     qpat_assum `emitted_insts s4 s5 = _` (fn th => pure_once_rewrite_tac[th]) >>
     simp[run_inst_seq_def]) >>
  suspend "allocation_frames"
QED

Resume raw_call_tuple_suffix_prepared[allocation_frames]:
  `sf.cs_next_var <= s4.cs_next_var` by
    (fs[exprLoweringPropsTheory.ci_mono_def] >> decide_tac) >>
  `STRING #"%" (toString s4.cs_next_var) = out` by
    (qpat_assum `buf.buf_operand = Var out` mp_tac >> simp[]) >>
  qpat_assum `stmt_state_rel H0 ctx func cenv cx es u`
    (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) mp_tac raw_call_tuple_alloc_kept_at) >>
  disch_then (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
  disch_then (drule_at (Pat `step_inst_base _ _ = _`)) >>
  disch_then (drule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `wb_frame _ _ _ _ _ _`)) >>
  simp[] >> disch_then (qspec_then `PG` assume_tac) >>
  qmatch_asmsub_abbrev_tac `ghost_kept_at lo cenv es0 sf G0 tn0 s0 G2 tn2` >>
  `!D. ghost_inv_at D lo dep cenv cx es G1 tn1 u ==>
       ghost_inv_at D lo dep cenv cx es G2 tn2 u2` by
    (rpt strip_tac >> unabbrev_all_tac >>
     irule bodyFullAllocGenericTheory.compile_alloc_buffer_ghost_frame_at >>
     simp[] >> conj_tac >- (qexists_tac `sf` >> simp[]) >>
     qexistsl_tac [`H0`,`ctx`,`func`] >> simp[]) >>
  suspend "allocation_resources"
QED

Resume raw_call_tuple_suffix_prepared[allocation_resources]:
  `local_ptrs_reserved cenv s4` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     qexists_tac `sa` >> fs[exprLoweringPropsTheory.ci_mono_def]) >>
  qpat_assum `stmt_state_rel H0 ctx func cenv cx es u`
    (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) mp_tac
      bodyPtrIfExpAllocSourceTheory.compile_alloc_buffer_raw_resources) >>
  disch_then (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
  disch_then (drule_at (Pat `step_inst_base _ _ = _`)) >>
  simp[] >> strip_tac >>
  suspend "allocation_covers"
QED

Resume raw_call_tuple_suffix_prepared[allocation_covers]:
  `ovx <> out` by
    (`not_fresh_at sa ovx` by fs[exprSafeOperandTheory.safe_operand_def] >>
     `not_fresh_at s4 ovx` by
       (irule loweringShapeDefsTheory.not_fresh_at_mono >> qexists_tac `sa` >>
        fs[exprLoweringPropsTheory.ci_mono_def]) >>
     metis_tac[loweringStateRelDefsTheory.not_fresh_at_def, arithmeticTheory.LESS_EQ_REFL]) >>
  `ptr_covers G2 tn2 out u2 (32*((n+31) DIV 32)+64)` by
    (qpat_assum `stmt_state_rel H0 ctx func cenv cx es u`
       (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) mp_tac
         allocationPtrTheory.alloca_step_ptr_covers) >>
     disch_then (drule_at (Pat `step_inst_base _ _ = _`)) >>
     simp[] >> disch_then (qspecl_then [`PG`,`G1`,`tn1`] mp_tac) >>
     simp[Abbr `G2`, Abbr `tn2`]) >>
  `ptr_covers G2 tn2 ovx u2 (32*((n+31) DIV 32)+32)` by
    (qpat_assum `stmt_state_rel H0 ctx func cenv cx es u`
       (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) mp_tac
         allocationPtrTheory.alloca_step_old_ptr_covers) >>
     disch_then (drule_at (Pat `step_inst_base _ _ = _`)) >>
     simp[] >> disch_then (qspecl_then [`PG`,`G1`,`tn1`,`ovx`,`32*((n+31) DIV 32)+32`] mp_tac) >>
     simp[Abbr `G2`, Abbr `tn2`]) >>
  qpat_assum `stmt_state_rel H0 ctx func cenv cx es u`
    (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) mp_tac allocationPtrTheory.alloca_step_site) >>
  disch_then (drule_at (Pat `step_inst_base _ _ = _`)) >>
  simp[] >> strip_tac >> rename1 `eval_operand (Var out) u2 = SOME (n2w b)` >>
  suspend "copy_premises"
QED

Resume raw_call_tuple_suffix_prepared[copy_premises]:
  `safe_operand s5 (Var out)` by
    metis_tac[exprSafeOperandTheory.alloc_buffer_safe_operand] >>
  `sa.cs_next_var <= s5.cs_next_var` by
    (drule loweringHaltTheory.compile_alloc_buffer_parts >> strip_tac >>
     fs[exprLoweringPropsTheory.ci_mono_def] >> decide_tac) >>
  `safe_operand s5 (Var ovx) /\ safe_operand s5 ok` by
    (conj_tac >> irule exprSafeOperandTheory.safe_operand_mono >>
     qexists_tac `sa` >> simp[]) >>
  `lookup_var ovx u2 = SOME (n2w (w2n w))` by
    (`not_fresh_at s4 ovx` by
       (irule loweringShapeDefsTheory.not_fresh_at_mono >> qexists_tac `sa` >>
        fs[exprSafeOperandTheory.safe_operand_def, exprLoweringPropsTheory.ci_mono_def]) >>
     metis_tac[wordsTheory.n2w_w2n, eval_operand_def]) >>
  `!mem. mem_agree_outside tn2.t_mem u2.vs_memory mem ==>
      val_in_memory (BaseTV (BytesT (Dynamic n)))
        (BytesV (TAKE n s.vs_returndata)) (w2n w) mem` by
    (`val_wf (BaseTV (BytesT (Dynamic n))) (BytesV (TAKE n s.vs_returndata))` by
       (simp[valueEncodingDefsTheory.val_wf_def, valueEncodingTheory.type_memory_size_def] >>
        irule arithmeticTheory.LESS_EQ_TRANS >> qexists_tac `n` >>
        simp[listTheory.LENGTH_TAKE_EQ, exprSimPropsTheory.le_word_size_mul]) >>
     `!i. w2n w <= i /\ i < w2n w + val_footprint
          (BaseTV (BytesT (Dynamic n))) (BytesV (TAKE n s.vs_returndata)) ==>
          i < u.vs_alloca_next` by
       (rpt strip_tac >>
        `w2n w + (32*((n+31) DIV 32)+32) <= u.vs_alloca_next` by
          (qpat_assum `stmt_state_rel H0 ctx func cenv cx es u`
             (strip_assume_tac o PURE_REWRITE_RULE [stmt_state_rel_def, alloca_inv_def,
                 alloca_next_valid_def]) >>
           qpat_x_assum `!aid base sz. FLOOKUP u.vs_allocas aid = SOME (base,sz) ==> _`
             (qspecl_then [`alloc.inst_id`,`w2n w`,`32*((n+31) DIV 32)+32`] mp_tac) >>
           simp[]) >>
        fs[loweringPostsTheory.val_footprint_def, listTheory.LENGTH_TAKE_EQ] >>
        mp_tac (Q.SPEC `n` exprSimPropsTheory.le_word_size_mul) >>
        simp[vfmConstantsTheory.word_size_def] >> decide_tac) >>
     qunabbrev_tac `tn2` >>
     qpat_assum `step_inst_base (mk_inst _ ALLOCA _ _) u = OK u2`
       (mp_then (Pat `step_inst_base _ _ = _`) mp_tac
         bodyPtrIfExpAllocFrameTheory.alloca_step_robust_below_frontier) >>
     disch_then (qspecl_then [`tn1`, `BaseTV (BytesT (Dynamic n))`,
       `BytesV (TAKE n s.vs_returndata)`, `w2n w`] mp_tac) >> simp[]) >>
  suspend "copy_separation"
QED

Resume raw_call_tuple_suffix_prepared[copy_separation]:
  `allocas_from lo u /\ lo <= u.vs_alloca_next` by
    (fs[ptrDisciplineTheory.allocas_from_def] >> (gvs[ptrDisciplineTheory.allocas_from_def])) >>
  `allocas_from lo u2` by
    (irule frameActivationSeparationTheory.allocas_from_step >>
     qexistsl_tac [`ctx`,`0`,
       `mk_inst s4.cs_next_id ALLOCA [Lit (n2w (32*((n+31) DIV 32)+64))] [out]`,`u`] >>
     simp[venomExecSemanticsTheory.step_inst_non_invoke]) >>
  `not_local_ptr cenv es.scopes out` by
    (qpat_assum `STRING #"%" _ = out` (SUBST1_TAC o SYM) >>
     irule exprLoweringPropsTheory.local_ptrs_reserved_fresh >>
     qexists_tac `s4` >> simp[]) >>
  `sf.cs_next_id <= s4.cs_next_id /\ alloc.inst_id < s4.cs_next_id` by
    (fs[exprLoweringPropsTheory.ci_mono_def] >> decide_tac) >>
  asm "separation" (fn sep =>
    qpat_assum `stmt_state_rel H0 ctx func cenv cx es u2`
      (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) mp_tac sep)) >>
  disch_then (qspec_then
    `mk_inst s4.cs_next_id ALLOCA [Lit (n2w (32*((n+31) DIV 32)+64))] [out]` mp_tac) >>
  simp[venomInstTheory.mk_inst_def] >>
  disch_then (qspecl_then [`sf`,`es`,`u2`,`lo`] mp_tac) >>
  simp[] >> strip_tac >>
  `FLOOKUP u2.vs_allocas alloc.inst_id =
      SOME (w2n w,32*((n+31) DIV 32)+32)` by metis_tac[] >>
  `w2n w + 32 + LENGTH (TAKE n s.vs_returndata) <= b \/ b + 32 <= w2n w` by
    (qpat_x_assum `!aid a m. FLOOKUP u2.vs_allocas aid = SOME (a,m) /\ _ ==> _`
       (qspecl_then [`alloc.inst_id`,`w2n w`,`32*((n+31) DIV 32)+32`] mp_tac) >>
     simp[] >>
     mp_tac (Q.SPEC `n` exprSimPropsTheory.le_word_size_mul) >>
     simp[listTheory.LENGTH_TAKE_EQ, vfmConstantsTheory.word_size_def] >> decide_tac) >>
  suspend "copy_scalar"
QED

Resume raw_call_tuple_suffix_prepared[copy_scalar]:
  markerLib.RESUME_TAC >>
  `!x. ok = Var x ==> not_fresh_at s4 x /\ x <> out` by
    (rpt strip_tac >>
     `not_fresh_at sa x` by fs[exprSafeOperandTheory.safe_operand_def] >>
     `not_fresh_at s4 x` by
       (irule loweringShapeDefsTheory.not_fresh_at_mono >> qexists_tac `sa` >>
        fs[exprLoweringPropsTheory.ci_mono_def]) >>
     metis_tac[loweringStateRelDefsTheory.not_fresh_at_def, arithmeticTheory.LESS_EQ_REFL]) >>
  `eval_operand ok u2 = SOME (if success then 1w else 0w)` by
    (`eval_operand ok u = SOME (if success then 1w else 0w)` by simp[] >>
     qpat_assum `eval_operand ok u = _` mp_tac >>
     qpat_assum `!x. not_fresh_at s4 x ==> lookup_var x u2 = _` mp_tac >>
     qpat_assum `!x. ok = Var x ==> _` mp_tac >>
     qpat_assum `safe_operand sa ok` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     Cases_on `ok` >> fs[eval_operand_def, exprSafeOperandTheory.safe_operand_def] >>
     metis_tac[]) >>
  `op_taint tn1 ok = {}` by
    (qpat_assum `op_taint tn ok = {}` mp_tac >>
     qpat_assum `safe_operand sa ok` mp_tac >>
     qpat_assum `!v. not_fresh_at sa v ==> _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     Cases_on `ok` >> fs[ptrDisciplineTheory.op_taint_def,
       exprSafeOperandTheory.safe_operand_def] >> metis_tac[]) >>
  `!x. ok = Var x ==> x <> out` by metis_tac[] >>
  `op_taint tn2 ok = {}` by
    (drule bodyPtrIfExpAllocSourceTheory.alloca_step_operand_taint >>
     simp[Abbr `tn2`]) >>
  `emit_void MSTORE [Var out;ok] s5 = ((),s6) /\
   emit_op ADD [Var out;Lit 32w] s6 = (dst,s7)` by
    (qpat_assum `buf.buf_operand = Var out` (fn th => rewrite_tac[GSYM th]) >> simp[]) >>
  `32 + (n+31) DIV 32 * 32 = 32*((n+31) DIV 32)+32` by
    metis_tac[arithmeticTheory.ADD_COMM, arithmeticTheory.MULT_COMM] >>
  qpat_assum `32 + (n+31) DIV 32 * 32 = _` (fn eq =>
    qpat_assum `emit_void MCOPY _ s7 = _`
      (mk_asm "copy_code" o PURE_ONCE_REWRITE_RULE [GSYM eq])) >>
  `lookup_var out u2 = SOME (n2w b)` by fs[eval_operand_def] >>
  asm "copy" (fn cp =>
    qpat_assum `emit_void MSTORE [Var out;ok] s5 = _`
      (mp_then (Pat `emit_void MSTORE _ _ = _`) mp_tac cp)) >>
  disch_then (drule_at (Pat `emit_op ADD _ _ = _`)) >>
  disch_then (qspecl_then [`ovx`,`n`,`sb`] mp_tac) >>
  disch_then (fn cp =>
    asm "copy_code" (mp_then (Pat `emit_void MCOPY _ _ = _`) mp_tac cp)) >>
  disch_then (fn th => mk_asm "copy_matched" th >> mp_tac th) >>
  disch_then (qspecl_then [`TAKE n s.vs_returndata`,`w2n w`,`b`,`u2`] mp_tac) >>
  disch_then (qspecl_then [`G2`,`tn2`,`success`] mp_tac) >>
  disch_then (qspecl_then [`lo`,`ctx`] mp_tac) >>
  simp[arithmeticTheory.MULT_COMM, eval_operand_def, listTheory.LENGTH_TAKE_EQ] >>
  disch_then (qspecl_then [`func`,`PG`] mp_tac) >>
  disch_then (qx_choose_then `G3` (qx_choose_then `tn3` strip_assume_tac)) >>
  asm_x "length" kall_tac >> asm_x "copy" kall_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts s5 sb)` by
    (qpat_assum `EVERY _ (emitted_insts sa sb)` mp_tac >>
     qpat_assum `emitted_insts sa sb = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[listTheory.EVERY_APPEND, listTheory.EVERY_MEM] >> metis_tac[]) >>
  `!k D. inst_seq_ptr D lo ctx func PG G2 tn2 (emitted_insts s5 sb)
      (u2 with vs_inst_idx := k) G3 tn3` by
    (rpt gen_tac >>
     asm "copy_matched" (qspecl_then
       [`TAKE n s.vs_returndata`,`w2n w`,`b`,`u2 with vs_inst_idx := k`] mp_tac) >>
     disch_then (qspecl_then [`G2`,`tn2`,`success`] mp_tac) >>
     disch_then (qspecl_then [`lo`,`ctx`] mp_tac) >>
     simp[arithmeticTheory.MULT_COMM, eval_operand_def, lookup_var_def,
       ptrDisciplineTheory.allocas_from_def, listTheory.LENGTH_TAKE_EQ,
       fragExecTheory.run_inst_seq_inst_idx, instIdxIndepTheory.exec_result_map_def] >>
     disch_then (qspecl_then [`func`,`PG`] mp_tac) >>
     (impl_tac >-
       (qpat_assum `lookup_var ovx u2 = _` mp_tac >>
        qpat_assum `lookup_var out u2 = _` mp_tac >>
        qpat_assum `allocas_from lo u2` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >>
        simp[lookup_var_def, ptrDisciplineTheory.allocas_from_def] >> metis_tac[])) >>
     disch_then (qx_choose_then `G4` (qx_choose_then `tn4` strip_assume_tac)) >>
     `G3 = G4 /\ tn3 = tn4` by
       (qpat_assum `!D. inst_seq_ptr D lo ctx func PG G2 tn2 _ u2 G3 tn3`
          (qspec_then `D` mp_tac) >>
        qpat_assum `!D. inst_seq_ptr D lo ctx func PG G2 tn2 _ _ G4 tn4`
          (qspec_then `D` mp_tac) >>
        qpat_assum `EVERY _ (emitted_insts s5 sb)` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
        metis_tac[raw_call_tuple_seq_ghost_cursor_unique]) >>
     metis_tac[]) >>
  asm_x "copy_matched" kall_tac >> suspend "copy_frame"
QED

Resume raw_call_tuple_suffix_prepared[copy_frame]:
  markerLib.RESUME_TAC >>
  `sf.cs_next_var <= s5.cs_next_var` by decide_tac >>
  `!x. not_fresh_at sf x ==>
     lookup_var x t = lookup_var x u2 /\ FLOOKUP G3 x = FLOOKUP G2 x /\
     op_taint tn3 (Var x) = op_taint tn2 (Var x)` by
    (gen_tac >> disch_tac >>
     qpat_x_assum `!v. not_fresh_at s5 v ==> _` irule >>
     irule loweringShapeDefsTheory.not_fresh_at_mono >>
     qexists_tac `sf` >> simp[]) >>
  qpat_assum `t with vs_vars := _ = _`
    (strip_assume_tac o
     SIMP_RULE (srw_ss()) [venomExecSemanticsTheory.mcopy_def,
       write_memory_with_expansion_def, mstore_def, LET_THM] o
     Q.AP_TERM `\v. (v.vs_allocas,v.vs_alloca_next,v.vs_call_ctx,
       v.vs_accounts,v.vs_transient,v.vs_immutables)`) >>
  `t.vs_memory = (mcopy (b+32) (w2n w) (32*((n+31) DIV 32)+32)
       (mstore b (val_to_w256 (BoolV success)) u2)).vs_memory` by
    (qpat_assum `t with vs_vars := _ = _`
      (mp_tac o Q.AP_TERM `\v. v.vs_memory`) >> simp[]) >>
  asm "frame" (fn frame =>
    qpat_assum `stmt_state_rel H0 ctx func cenv cx es u2`
      (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) mp_tac frame)) >>
  disch_then (drule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`t`,`G3`,`tn3`] mp_tac) >>
  disch_then (qspecl_then [`{i | b <= i /\ i < b + (32*((n+31) DIV 32)+64)}`,`dep`] mp_tac) >>
  (impl_tac >- (simp[IgnAsm `t.vs_memory = _`, IgnAsm `u2.vs_memory = _`,
     IgnAsm `u.vs_memory = _`, IgnAsm `tn3.t_mem = _`] >>
    conj_tac >-
      (gen_tac >> disch_tac >>
       qpat_assum `t.vs_memory = _` (fn th => pure_rewrite_tac[th]) >>
       irule EQ_TRANS >>
       qexists_tac `mem_bytes_at i 1 (mstore b (val_to_w256 (BoolV success)) u2).vs_memory` >>
       conj_tac >-
         (irule valueEncodingPropsTheory.mcopy_mem_bytes_at_disjoint >> decide_tac) >>
       irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >> decide_tac) >>
    conj_tac >-
      (qpat_assum `tn3.t_mem = _` (fn th => pure_rewrite_tac[th]) >>
       simp[pred_setTheory.IN_UNION, pred_setTheory.IN_DIFF,
         pred_setTheory.GSPECIFICATION] >> rpt strip_tac >>
       (first_assum ACCEPT_TAC ORELSE decide_tac)) >>
    conj_tac >- metis_tac[] >>
    conj_tac >-
      (rpt strip_tac >>
       `FLOOKUP u2.vs_allocas aid = SOME (a,m)` by
         metis_tac[loweringPostsTheory.wb_frame_def] >> metis_tac[]) >>
    rpt strip_tac >>
    `local_region cenv es.scopes u name a m` by
      (irule exprSimPropsTheory.local_region_frame_fwd >>
       qexistsl_tac [`s0`,`sf`,`es0.scopes`] >>
       fs[loweringPostsTheory.wb_frame_def]) >>
    `local_region cenv es.scopes u2 name a m` by
      (irule exprSimPropsTheory.local_region_frame_fwd >>
       qexistsl_tac [`u`,`s4`,`es.scopes`] >> simp[]) >>
    metis_tac[])) >>
  strip_tac >> suspend "package"
QED

Resume raw_call_tuple_suffix_prepared[package]:
  markerLib.RESUME_TAC >> (
  asm_x "separation" kall_tac >> asm_x "frame" kall_tac >>
  `lookup_var out t = SOME (n2w b)` by
    (qpat_assum `!v. not_fresh_at s5 v ==> _` (qspec_then `out` mp_tac) >>
     fs[exprSafeOperandTheory.safe_operand_def]) >>
  qexistsl_tac [`G3`,`tn3`] >>
  conj_tac >- suspend "origin" >>
  conj_tac >- simp[] >>
  conj_tac >- (rpt strip_tac >> gvs[]) >>
  conj_tac >- suspend "ptr_value" >>
  conj_tac >-
    (qpat_assum `ptr_covers G3 tn3 out t _`
       (strip_assume_tac o PURE_REWRITE_RULE [bodyPtrDefsTheory.ptr_covers_def]) >>
     rename1 `FLOOKUP G3 out = SOME (bb0,cap0)` >>
     simp[bodyPtrDefsTheory.ptr_buf_ok_def, eval_operand_def] >> strip_tac >>
     qexistsl_tac [`bb0`,`cap0`] >> simp[] >> gvs[] >> decide_tac) >>
  conj_tac >- simp[] >>
  simp[ghostPcTransportPtrTheory.ghost_inv_at_inst_idx] >> metis_tac[])
QED

Resume raw_call_tuple_suffix_prepared[ptr_value]:
  markerLib.RESUME_TAC >> (
  qpat_assum `ptr_covers G3 tn3 out t _`
    (strip_assume_tac o PURE_REWRITE_RULE [bodyPtrDefsTheory.ptr_covers_def]) >>
  qpat_x_assum `tn3.t_mem = _` kall_tac >>
  qpat_x_assum `t.vs_memory = _` kall_tac >>
  `b < dimword (:256)` by decide_tac >>
  `w2n (n2w b : bytes32) = b` by simp[wordsTheory.w2n_n2w] >>
  simp[bodyPtrDefsTheory.ptr_vv_ok_def, bodyPtrDefsTheory.ptr_mem_ok_def,
    contextTheory.mk_ptr_def, vyperStateTheory.read_result_def,
    vyperStateTheory.return_def, eval_operand_def] >>
  conj_tac >-
    (rpt strip_tac >> gvs[] >> metis_tac[]) >>
  rpt strip_tac >>
  simp[exprSimPropsTheory.val_store_size_def,
    valueEncodingTheory.type_memory_size_def, vfmConstantsTheory.word_size_def] >>
  gvs[] >> decide_tac)
QED

Resume raw_call_tuple_suffix_prepared[origin]:
  markerLib.RESUME_TAC >>
  `!D k. ptr_inst_ok D lo 0 ctx func G1 tn1
      (mk_inst s4.cs_next_id ALLOCA
        [Lit (n2w (32*((n+31) DIV 32)+64))] [out])
      (u with vs_inst_idx := k)` by
    (qpat_assum `allocas_from lo u` mp_tac >>
     qpat_assum `~ctx_has_dalloca ctx` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     fs[ptrSafeRunTheory.ptr_inst_ok_def, ptrDisciplineTheory.access_ok_def,
       taint_ok_def, op_taint_def, ptrDisciplineTheory.allocas_from_def,
       venomInstTheory.mk_inst_def,
       codegenRelTheory.source_memory_write_ranges_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       venomExecSemanticsTheory.step_inst_non_invoke] >>
     PURE_ONCE_REWRITE_TAC[venomExecSemanticsTheory.step_inst_base_def] >>
     pure_rewrite_tac[venomInstTheory.instruction_accessors,
       venomInstTheory.instruction_accfupds, combinTheory.K_THM,
       venomInstTheory.opcode_case_def] >>
     simp[venomExecSemanticsTheory.exec_alloca_def, AllCaseEqs(), update_var_def] >>
     rpt strip_tac >> gvs[] >> metis_tac[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa s4)` by
    (qpat_assum `EVERY _ (emitted_insts sa sb)` mp_tac >>
     qpat_assum `emitted_insts sa sb = _` (fn th => pure_once_rewrite_tac[th]) >>
     POP_ASSUM_LIST (K all_tac) >> simp[listTheory.EVERY_APPEND, listTheory.EVERY_MEM] >>
     metis_tac[]) >>
  `!D. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s G3 tn3` by
    (gen_tac >>
     qpat_assum `emitted_insts sa sb = _` (fn th => pure_once_rewrite_tac[th]) >>
     irule instSeqComposePtrTheory.inst_seq_ptr_append_ok >>
     conj_tac >- simp[] >>
     qexistsl_tac [`G1`,`u`,`tn1`] >> simp[] >>
     qpat_assum `emitted_insts s4 s5 = _` (fn th => pure_once_rewrite_tac[th]) >>
     simp[inst_seq_ptr_def, instIdxIndepTheory.step_inst_inst_idx_indep,
       instIdxIndepTheory.exec_result_map_def, venomInstTheory.mk_inst_def,
       venomInstTheory.is_terminator_def, Abbr `G2`, Abbr `tn2`] >-
       (qpat_assum `!k D. inst_seq_ptr D lo ctx func PG _ _ _ _ G3 tn3`
          (qspecl_then [`SUC (LENGTH sa.cs_current_insts + LENGTH (emitted_insts sa s4))`,`D`] mp_tac) >>
        metis_tac[venomInstTheory.mk_inst_def])) >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    (qpat_assum `sa.cs_current_insts <<= sb.cs_current_insts` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[exprLoweringPropsTheory.prefix_drop_equiv, emitted_insts_def]) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_assum `fn_has_code sa sb func` mp_tac >>
     qpat_assum `sb.cs_current_insts = sa.cs_current_insts ++ _` mp_tac >>
     qpat_assum `sb.cs_current_bb = sa.cs_current_bb` mp_tac >>
     qpat_assum `s.vs_current_bb = sa.cs_current_bb` mp_tac >>
     qpat_assum `s.vs_inst_idx = LENGTH sa.cs_current_insts` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[fragExecTheory.fn_has_code_def, exprLoweringPropsTheory.prefix_drop_equiv] >>
     rpt strip_tac >> qexists_tac `bb` >> simp[] >>
     qpat_x_assum `bb.bb_instructions = _`
       (fn th => GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) empty_rewrites [th]) >>
     pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC,
       rich_listTheory.DROP_LENGTH_APPEND, rich_listTheory.DROP_DROP_T] >>
     simp[arithmeticTheory.ADD_COMM]) >>
  strip_tac >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (qpat_assum `emit_op RETURNDATASIZE [] sa = _` mp_tac >>
     qpat_assum `emit_op LT _ s1 = _` mp_tac >>
     qpat_assum `compile_select _ _ _ s2 = _` mp_tac >>
     qpat_assum `emit_void MSTORE _ s3 = _` mp_tac >>
     qpat_assum `compile_alloc_buffer _ s4 = _` mp_tac >>
     qpat_assum `emit_void MSTORE _ s5 = _` mp_tac >>
     qpat_assum `emit_op ADD _ s6 = _` mp_tac >>
     qpat_assum `emit_void MCOPY _ s7 = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[builtinSimpleTheory.compile_select_def, contextTheory.compile_alloc_buffer_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
       compileEnvTheory.comp_return_def, compileEnvTheory.fresh_var_def,
       compileEnvTheory.fresh_id_def, compileEnvTheory.emit_def] >>
     rpt strip_tac >>
     map_every (fn pat => qpat_x_assum pat (fn th =>
       rewrite_tac[GSYM th]) >> simp[])
       [`_ = sb`, `_ = s7`, `_ = s6`, `_ = s5`, `_ = s4`,
        `_ = s3`, `_ = s2`, `_ = s1`] >>
     simp[emitted_insts_def] >>
     pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
     simp[venomInstTheory.mk_inst_def]) >>
  `s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts` by
    (qpat_assum `s.vs_inst_idx = LENGTH sa.cs_current_insts` mp_tac >>
     qpat_assum `sb.cs_current_insts = sa.cs_current_insts ++ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  qpat_assum `!D. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s G3 tn3`
    (qspec_then `D` assume_tac) >>
  drule_all fragGasSeqPtrTheory.run_inst_seq_gas_origin_ptr_path >>
  simp[]
QED

Finalise raw_call_tuple_suffix_prepared

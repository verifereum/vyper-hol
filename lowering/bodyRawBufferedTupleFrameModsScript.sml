Theory bodyRawBufferedTupleFrameMods
Ancestors
  bodyFullRawCallTupleLength bodyFullRawCallTupleCopy
  bodyFullRawCallTupleAllocFrame bodyFullRawCallTupleWriteFrame
  exprSimRawCall exprSimRawCallCalldata
  placeMemoryTypedPrimitive venomMemProps venomState venomInst
  venomExecSemantics finite_map words stateRelProj loweringStateRelDefs
  allocaFootprint exprSafeOperand ptrDiscipline fragGasSeqPtr exprLowering
  bodyPtrIfExpAllocCompiler bodyPtrIfExpAllocSource bodyFullHashKeccakFixed
  exprSimProps loweringHalt exprLoweringProps allocationPtr venomMemDefs
  bodyRawTupleAllocCopyEntryMods bodyRawTupleCallerKeptMods
  bodyRawTupleCopyIndexedMods bodyRawTupleOrdinaryEndpointMods
  bodyRawTupleSuffixPathMods bodyFullRawCallFinishJoint allocationPathGrowth
Libs
  monadsyntax

(* The allocation between the header and copy does not write memory. *)
Theorem tuple_write_window[local]:
  u.vs_memory = (mstore a len s).vs_memory /\
  t.vs_memory = (mcopy (b+32) a k (mstore b flag u)).vs_memory ==>
  LENGTH s.vs_memory <= LENGTH t.vs_memory /\
  (!p m. (p+m <= a \/ a+32 <= p) /\ (p+m <= b \/ b+32+k <= p) ==>
     mem_bytes_at p m t.vs_memory = mem_bytes_at p m s.vs_memory)
Proof
  strip_tac >> conj_tac
  >- (irule arithmeticTheory.LESS_EQ_TRANS >> qexists_tac `LENGTH u.vs_memory` >>
      conj_tac >- simp[venomMemPropsTheory.mstore_memory_nondecreasing] >>
      irule arithmeticTheory.LESS_EQ_TRANS >>
      qexists_tac `LENGTH (mstore b flag u).vs_memory` >>
      simp[placeMemoryTypedPrimitiveTheory.mcopy_memory_length,
           venomMemPropsTheory.mstore_memory_nondecreasing]) >>
  rpt gen_tac >> strip_tac >>
  `p+m <= b+32 \/ b+32+k <= p` by decide_tac >>
  `p+m <= b \/ b+32 <= p` by decide_tac >>
  simp[valueEncodingPropsTheory.mcopy_mem_bytes_at_disjoint,
       valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint]
QED

Theorem tuple_copy_taint_window[local]:
  tn1.t_mem = tn.t_mem DIFF {i | a <= i /\ i < a+32} /\
  (!i. ~(b <= i /\ i < b+32+k) /\ i IN tn2.t_mem ==> i IN tn1.t_mem) /\
  tnf.t_mem =
    ((tn2.t_mem DIFF {i | b <= i /\ i < b+32}) DIFF {i | b+32 <= i /\ i < b+32+k}) UNION
    {b+32+i | i | i < k /\ a+i IN (tn2.t_mem DIFF {i | b <= i /\ i < b+32})} ==>
  !i. ~(a <= i /\ i < a+32) /\ ~(b <= i /\ i < b+32+k) /\
      i IN tnf.t_mem ==> i IN tn.t_mem
Proof
  rpt gen_tac >> strip_tac >>
  `!i. i IN tnf.t_mem /\ ~(b <= i /\ i < b+32+k) ==> i IN tn2.t_mem` by
    (gen_tac >> simp[pred_setTheory.IN_UNION,pred_setTheory.IN_DIFF] >>
     rpt strip_tac >> gvs[] >> decide_tac) >>
  rpt strip_tac >>
  `i IN tn2.t_mem` by (first_x_assum irule >> simp[] >> decide_tac) >>
  `i IN tn1.t_mem` by
    (qpat_assum `!i. _ ==> i IN tn1.t_mem` irule >> simp[] >> decide_tac) >>
  qpat_assum `tn1.t_mem = _` (fn th =>
    qpat_x_assum `i IN tn1.t_mem`
      (mp_tac o PURE_REWRITE_RULE [th,pred_setTheory.IN_DIFF])) >>
  tautLib.TAUT_TAC
QED

Theorem tuple_alloca_rows[local]:
  k < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w k)] [p]) s = OK t /\
  FLOOKUP t.vs_allocas id = SOME (b,k) ==>
  t with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
            vs_alloca_next := s.vs_alloca_next |> = s /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  (!aid row. FLOOKUP s.vs_allocas aid = SOME row ==> FLOOKUP t.vs_allocas aid = SOME row) /\
  (!aid off m. FLOOKUP t.vs_allocas aid = SOME (off,m) ==>
     FLOOKUP s.vs_allocas aid = SOME (off,m) \/ s.vs_alloca_next <= off)
Proof
  strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, venomExecSemanticsTheory.exec_alloca_def] >>
  Cases_on `FLOOKUP s.vs_allocas id` >> gvs[LET_THM]
  >- (gvs[update_var_def,FLOOKUP_UPDATE] >> rpt strip_tac >>
      Cases_on `aid = id` >> gvs[FLOOKUP_UPDATE]) >>
  PairCases_on `x` >> simp[update_var_def] >> strip_tac >> gvs[]
QED

(* Execute the header once, retaining the ordinary state and the exact write
   of the ghost-checked length-store fragment. *)
Theorem tuple_header_cut[local]:
  emit_op RETURNDATASIZE [] sa = (z,s1) /\
  emit_op LT [z;Lit (n2w n)] s1 = (cmp,s2) /\
  compile_select cmp z (Lit (n2w n)) s2 = (cap,s3) /\
  emit_void MSTORE [Var x;cap] s3 = ((),s4) /\
  0 < n /\ n < dimword (:256) /\
  64 + ((n+31) DIV 32)*32 < dimword (:256) /\
  safe_operand sa (Var x) /\ lookup_var x s = SOME w /\
  ptr_covers G tn x s (32 + ((n+31) DIV 32)*32) /\
  LENGTH s.vs_returndata < dimword (:256) /\
  mem_bytes_at (w2n w+32) (LENGTH (TAKE n s.vs_returndata)) s.vs_memory =
    TAKE n s.vs_returndata /\
  (!i. w2n w+32 <= i /\ i < w2n w+32+LENGTH (TAKE n s.vs_returndata) ==>
       i NOTIN tn.t_mem) /\
  stmt_state_rel H ctx func cenv cx es s /\ wb_frame cenv es0 es sf s0 s /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sf /\
  sf.cs_next_var <= sa.cs_next_var /\ MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  fn_inst_ids_distinct func /\ MEM alloc (fn_insts func) /\
  alloc.inst_opcode = ALLOCA /\ alloc.inst_outputs = [q] /\
  not_local_ptr cenv es.scopes q /\ sf.cs_next_id <= alloc.inst_id /\
  FLOOKUP s.vs_allocas alloc.inst_id = SOME (w2n w,32 + ((n+31) DIV 32)*32) /\
  allocas_from lo s ==>
  ?u G1 tn1.
    run_inst_seq (emitted_insts sa s4) s = OK u /\
    stmt_state_rel H ctx func cenv cx es u /\ wb_frame cenv es0 es sf s0 u /\
    (!D. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa s4) s G1 tn1) /\
    ptr_covers G1 tn1 x u (32 + ((n+31) DIV 32)*32) /\
    (!mem. mem_agree_outside tn1.t_mem u.vs_memory mem ==>
      val_in_memory (BaseTV (BytesT (Dynamic n)))
        (BytesV (TAKE n s.vs_returndata)) (w2n w) mem) /\
    tn1.t_mem = tn.t_mem DIFF {i | w2n w <= i /\ i < w2n w+32} /\
    tn1.t_stor = tn.t_stor /\ tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
    (!v. not_fresh_at sa v ==>
      lookup_var v u = lookup_var v s /\ FLOOKUP G1 v = FLOOKUP G v /\
      op_taint tn1 (Var v) = op_taint tn (Var v)) /\
    (u with vs_vars := s.vs_vars) =
      mstore (w2n w) (n2w (LENGTH (TAKE n s.vs_returndata))) s
Proof
  strip_tac >>
  `eval_operand (Var x) s = SOME w` by simp[eval_operand_def] >>
  `stmt_state_rel H ctx func cenv cx es (s with vs_fmp := s.vs_fmp)` by simp[] >>
  `w2n w <= w2n w /\ w2n w + 32 <= w2n w + (32 + ((n+31) DIV 32)*32)` by decide_tac >>
  drule_all raw_call_output_prefix_ready >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  `u with vs_fmp := s.vs_fmp = u` by
    (qpat_assum `u.vs_fmp = _` (SUBST1_TAC o SYM) >> simp[]) >>
  `stmt_state_rel H ctx func cenv cx es u` by fs[] >>
  `w2n w + (32 + ((n+31) DIV 32)*32) <= s.vs_alloca_next` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx es s`
       (mp_then Any mp_tac stmt_state_rel_local_ptrs_alloca) >>
     simp[alloca_inv_def,alloca_next_valid_def] >> strip_tac >>
     first_x_assum drule >> simp[]) >>
  `s.vs_alloca_next < dimword (:256)` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx es s`
       (mp_then Any mp_tac stmt_state_rel_alloca_room) >>
     simp[alloca_room_def] >> decide_tac) >>
  `w2n w + (32 + ((n+31) DIV 32)*32) < dimword (:256)` by decide_tac >>
  `lookup_var x s = SOME (n2w (w2n w))` by simp[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    qpat_assum `stmt_state_rel H ctx func cenv cx es s`
      (ACCEPT_TAC o MATCH_MP stmt_state_rel_allocas_below_fmp) >>
  drule_all raw_call_tuple_length_checked >>
  disch_then (qspecl_then [`func`,`PG`] strip_assume_tac) >>
  rename1 `ptr_covers G1 tn1 x u _` >>
  qexistsl_tac [`u`,`G1`,`tn1`] >> simp[]
QED

Theorem raw_buffered_tuple_finish_frame_registered:
  (if n > 0 then
       do z <- emit_op RETURNDATASIZE [];
          cmp <- emit_op LT [z;Lit (n2w n)];
          cap <- compile_select cmp z (Lit (n2w n));
          emit_void MSTORE [Var x;cap];
          buf <- compile_alloc_buffer (64 + ((n + 31) DIV 32) * 32);
          emit_void MSTORE [buf.buf_operand;ok];
          dst <- emit_op ADD [buf.buf_operand;Lit 32w];
          emit_void MCOPY [dst;Var x;Lit (n2w (32 + ((n + 31) DIV 32) * 32))];
          return buf.buf_operand od
     else return ok) sa = (result,sb) /\ 0 < n /\
  stmt_state_rel (H0:(bool # 256 word # type_value) list # num list)
    ctx func cenv cx es s /\ wb_frame cenv es0 es sf s0 s /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  MEM alloc (fn_insts func) /\ alloc.inst_opcode = ALLOCA /\
  alloc.inst_outputs = [q] /\ not_local_ptr cenv es.scopes q /\
  FLOOKUP s.vs_allocas alloc.inst_id = SOME (w2n w,32 + ((n + 31) DIV 32) * 32) /\
  local_ptrs_reserved cenv sf /\ local_ptrs_reserved cenv sa /\
  sf.cs_next_var <= sa.cs_next_var /\ sf.cs_next_id <= alloc.inst_id /\
  alloc.inst_id < sa.cs_next_id /\ MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  safe_operand sa (Var x) /\ safe_operand sa ok /\ lookup_var x s = SOME w /\
  eval_operand ok s = SOME (if success then 1w else 0w) /\
  op_taint tn ok = {} /\ ptr_covers G tn x s (32 + ((n+31) DIV 32) * 32) /\
  s.vs_memory = (write_memory_with_expansion (w2n ro) (TAKE n data) pre).vs_memory /\
  s.vs_returndata = data /\
  tn.t_mem = old_tn.t_mem DIFF {j | w2n ro <= j /\ j < w2n ro + LENGTH (TAKE n data)} /\
  w2n ro = w2n w + 32 /\ LENGTH data < dimword (:256) /\
  64 + ((n + 31) DIV 32) * 32 < dimword (:256) /\ n < dimword (:256) /\
  allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size func s <= w2n s.vs_initial_fmp) /\
  (!v sz. cenv.ce_return_buf = SOME (PtrVar (Var v) sz) ==> not_fresh_at sf v) /\
  (!v sz. cenv.ce_return_pc = SOME (PtrVar (Var v) sz) ==> not_fresh_at sf v) /\
  ghost_kept_at lo cenv es0 sf G0 tn0 s0 G tn /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ alloca_history func s /\
  expr_has_effect e /\ post_value_type cenv e = expr_type e /\
  lowered_value_type cenv e = expr_type e /\
  expr_type e = TupleT [BaseT BoolT;BaseT (BytesT (Dynamic n))] /\
  evaluate_type (get_tenv cx) (expr_type e) =
    SOME (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic n))]) /\
  v = ArrayV (TupleV [BoolV success;BytesV (TAKE n data)]) /\
  vv = LocatedValue (expr_type e) (mk_ptr result LocMemory) ==>
  ?u Gf tnf.
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func u /\
    ghost_kept_at lo cenv es0 sf G0 tn0 s0 Gf tnf /\
    (!D. ghost_inv_at D lo dep cenv cx es G tn s ==>
      ghost_inv_at D lo dep cenv cx es Gf tnf u) /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,Gf,tnf)) /\
    ptr_vv_ok cx (post_value_type cenv e) (Value v)
      (LocatedValue (expr_type e) (mk_ptr result LocMemory)) es Gf tnf u /\
    ptr_buf_ok cenv e result Gf u /\
    (!H:(bool # 256 word # type_value) list # num list.
         stmt_state_rel H ctx func cenv cx es s /\
         storage_well_formed_on cx es (FST H) ==>
      vv_post H ctx func cenv cx e es0 sf sb s0 es (Value v)
        (LocatedValue (expr_type e) (mk_ptr result LocMemory)) u /\
      vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e)
        es (Value v) (LocatedValue (expr_type e) (mk_ptr result LocMemory)) u /\
      vv_own cenv cx (post_value_type cenv e) sf sb es (Value v)
        (LocatedValue (expr_type e) (mk_ptr result LocMemory)) u) /\
    (?i b.
      let writes = [(alloc.inst_id,w2n w,32); (i.inst_id,b,64+((n+31) DIV 32)*32)] in
      (!z wz. not_fresh_at sf z /\ lookup_var z s = SOME wz ==>
        lookup_var z u = SOME wz) /\
      (!z. not_fresh_at sf z ==> FLOOKUP Gf z = FLOOKUP G z /\
        op_taint tnf (Var z) = op_taint tn (Var z)) /\
      allocation_growth s u /\ LENGTH s.vs_memory <= LENGTH u.vs_memory /\
      u.vs_data_section = s.vs_data_section /\ u.vs_call_ctx = s.vs_call_ctx /\
      u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
      u.vs_immutables = s.vs_immutables /\
      tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
      (!aid p k. MEM (aid,p,k) writes ==>
        ?cap inst z. FLOOKUP u.vs_allocas aid = SOME (p,cap) /\ k <= cap /\
          MEM inst (fn_insts func) /\ inst.inst_id = aid /\ inst.inst_opcode = ALLOCA /\
          inst.inst_outputs = [z] /\ not_local_ptr cenv es.scopes z /\ sf.cs_next_id <= aid) /\
      (!off len. (!aid p k. MEM (aid,p,k) writes ==>
          venomMemDefs$regions_disjoint (off,len) (p,k)) ==>
        mem_bytes_at off len u.vs_memory = mem_bytes_at off len s.vs_memory /\
        (!j. off <= j /\ j < off+len /\ j IN tnf.t_mem ==> j IN tn.t_mem)))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all raw_call_positive_payload_cut >> strip_tac >>
  `LENGTH s.vs_returndata < dimword (:256)` by simp[] >>
  `eval_operand (Var x) s = SOME w` by simp[eval_operand_def] >>
  `v = ArrayV (TupleV [BoolV success;BytesV (TAKE n s.vs_returndata)])` by simp[] >>
  drule_all (INST_TYPE [``:α`` |-> ``:256``, ``:β`` |-> ``:256``]
    raw_tuple_ordinary_endpoint) >>
  disch_then (qx_choose_then `t` (CONJUNCTS_THEN2 assume_tac (mk_asm "ordinary"))) >>
  drule_all raw_call_positive_suffix_mem_ok >> strip_tac >>
  drule_all raw_call_nonrevert_suffix_code >> strip_tac >>
  drule_all tuple_header_cut >>
  disch_then (qspec_then `PG` (qx_choose_then `h` (qx_choose_then `G1` (qx_choose_then `tn1` strip_assume_tac)))) >>
  `h.vs_allocas = s.vs_allocas /\ h.vs_alloca_next = s.vs_alloca_next /\
   h.vs_initial_fmp = s.vs_initial_fmp /\ h.vs_inst_idx = s.vs_inst_idx` by
    (qpat_assum `(h with vs_vars := _) = _` (fn th =>
       mp_tac (Q.AP_TERM `\v. (v.vs_allocas,v.vs_alloca_next,v.vs_initial_fmp,v.vs_inst_idx)` th)) >>
     simp[venomStateTheory.mstore_def]) >>
  `allocas_from lo h` by
    (pure_rewrite_tac [allocas_from_def] >>
     qpat_assum `h.vs_allocas = s.vs_allocas` (pure_rewrite_tac o single) >>
     qpat_assum `allocas_from lo s` (ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
  `FLOOKUP h.vs_allocas alloc.inst_id = SOME (w2n w,32 + ((n+31) DIV 32)*32)` by simp[] >>
  `alloca_inv s` by
    (qpat_assum `stmt_state_rel H0 ctx func cenv cx es s`
       (mp_then Any mp_tac stmt_state_rel_local_ptrs_alloca) >> simp[]) >>
  `w2n w + (32 + ((n+31) DIV 32)*32) <= s.vs_alloca_next` by
    (qpat_assum `alloca_inv s` (mp_tac o REWRITE_RULE [alloca_inv_def,alloca_next_valid_def]) >>
     strip_tac >> qpat_assum `!aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) ==> _`
       drule >> simp[]) >>
  `lo <= w2n w` by
    (qpat_assum `allocas_from lo s` (mp_tac o REWRITE_RULE [allocas_from_def]) >>
     strip_tac >> first_x_assum drule >> simp[]) >>
  `lo <= h.vs_alloca_next` by decide_tac >>
  `h.vs_fmp = s.vs_fmp` by
    (qpat_assum `(h with vs_vars := _) = _` (mp_tac o Q.AP_TERM `\v. v.vs_fmp`) >>
     simp[mstore_def]) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp h /\
      h.vs_alloca_next + pending_alloca_size func h <= w2n h.vs_initial_fmp)` by
    (pure_rewrite_tac [allocas_below_fmp_def,pending_alloca_size_def] >>
     map_every (fn pat => qpat_assum pat (pure_rewrite_tac o single))
       [`h.vs_allocas = _`,`h.vs_alloca_next = _`,`h.vs_initial_fmp = _`,`h.vs_fmp = _`] >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s /\ _`
       (ACCEPT_TAC o REWRITE_RULE [allocas_below_fmp_def,pending_alloca_size_def])) >>
  `local_ptrs_reserved cenv s4 /\ safe_operand s4 (Var x) /\ safe_operand s4 ok /\
   sf.cs_next_var <= s4.cs_next_var /\ sf.cs_next_id <= s4.cs_next_id /\ alloc.inst_id < s4.cs_next_id` by
    (qpat_assum `ci_mono sa s4` (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
     conj_tac >- (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
     conj_tac >- (irule safe_operand_mono >> qexists_tac `sa` >> simp[]) >>
     conj_tac >- (irule safe_operand_mono >> qexists_tac `sa` >> simp[]) >>
     decide_tac) >>
  `not_fresh_at sa x` by
    qpat_assum `safe_operand sa (Var x)`
      (ACCEPT_TAC o SIMP_RULE (srw_ss()) [safe_operand_def]) >>
  `lookup_var x h = SOME (n2w (w2n w))` by
    (qpat_assum `!v. not_fresh_at sa v ==> _` drule >> simp[]) >>
  `eval_operand ok h = SOME (if success then 1w else 0w) /\ op_taint tn1 ok = {}` by
    (Cases_on `ok` >> fs[eval_operand_def,op_taint_def,safe_operand_def] >>
     rename1 `lookup_var z h = _` >>
     qpat_assum `!v. not_fresh_at sa v ==> _` (qspec_then `z` mp_tac) >> simp[]) >>
  `cs_extends s4 s5` by (drule compile_alloc_buffer_extends >> simp[]) >>
  `fn_has_code s4 sb func` by (drule_all fragExecTheory.fn_has_code_split >> simp[]) >>
  `cs_extends s5 s6` by
    (qpat_assum `emit_void MSTORE _ s5 = _`
      (ACCEPT_TAC o MATCH_MP fragExecTheory.cs_extends_emit_inst o
        REWRITE_RULE [emitHelperTheory.emit_void_def,GSYM emitHelperTheory.emit_inst_def])) >>
  `cs_extends s6 s7` by (drule exprSimAccountsTheory.emit_op_extends_next_var >> simp[]) >>
  `cs_extends s7 sb` by
    (qpat_assum `emit_void MCOPY _ s7 = _`
      (ACCEPT_TAC o MATCH_MP fragExecTheory.cs_extends_emit_inst o
        REWRITE_RULE [emitHelperTheory.emit_void_def,GSYM emitHelperTheory.emit_inst_def])) >>
  `cs_extends s5 sb` by
    (irule compileEnvTheory.cs_extends_trans >> qexists_tac `s7` >>
     simp[] >> irule compileEnvTheory.cs_extends_trans >> qexists_tac `s6` >> simp[]) >>
  `fn_has_code s4 s5 func` by (drule_all fragExecTheory.fn_has_code_split >> simp[]) >>
  `LENGTH (TAKE n s.vs_returndata) <= n` by simp[listTheory.LENGTH_TAKE_EQ] >>
  `val_wf (BaseTV (BytesT (Dynamic n))) (BytesV (TAKE n s.vs_returndata))` by
    (simp[valueEncodingDefsTheory.val_wf_def,valueEncodingTheory.type_memory_size_def,listTheory.LENGTH_TAKE_EQ] >>
     qspec_then `n` mp_tac valueTypingMemoryPropsTheory.word_size_capacity >>
     simp[vfmConstantsTheory.word_size_def] >> decide_tac) >>
  mp_tac (Q.INST [`u` |-> `h`,`H` |-> `H0`,`aid` |-> `alloc.inst_id`,
                  `a` |-> `w2n (w:256 word)`,`bs` |-> `TAKE n s.vs_returndata`,
                  `L` |-> `32 + ((n+31) DIV 32)*32`,
                  `kbuf` |-> `64 + ((n+31) DIV 32)*32`]
    (INST_TYPE [``:α`` |-> ``:256``] raw_tuple_alloc_copy_entry)) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >>
  disch_then (qx_choose_then `p` (qx_choose_then `r` (qx_choose_then `b` strip_assume_tac))) >>
  qabbrev_tac `i = mk_inst s4.cs_next_id ALLOCA [Lit (n2w (64 + ((n+31) DIV 32)*32))] [p]` >>
  qabbrev_tac `G2 = step_prov PG G1 i r` >>
  qabbrev_tac `tn2 = step_taint i h r tn1` >>
  `inst_extends s4 s5` by
    (drule abiBufferAllocationCodeTheory.compile_alloc_buffer_code >>
     simp[emitHelperPropsTheory.inst_extends_def]) >>
  `s5.cs_blocks = sb.cs_blocks` by
    (qpat_assum `cs_extends sa s4` (strip_assume_tac o REWRITE_RULE [compileEnvTheory.cs_extends_def]) >>
     qpat_assum `cs_extends s4 s5` (strip_assume_tac o REWRITE_RULE [compileEnvTheory.cs_extends_def]) >>
     qpat_assum `cs_extends s5 sb` (strip_assume_tac o REWRITE_RULE [compileEnvTheory.cs_extends_def]) >>
     rename1 `sb.cs_blocks = extra ++ s5.cs_blocks` >>
     map_every (fn pat => qpat_assum pat
       (assume_tac o REWRITE_RULE [listTheory.LENGTH_APPEND] o Q.AP_TERM `LENGTH`))
       [`sb.cs_blocks = extra ++ _`,`s5.cs_blocks = _ ++ _`,
        `s4.cs_blocks = _ ++ _`,`sb.cs_blocks = sa.cs_blocks`] >>
     `LENGTH extra = 0` by decide_tac >>
     fs[]) >>
  `inst_extends s5 sb` by
    (qpat_assum `cs_extends s5 sb` (strip_assume_tac o REWRITE_RULE [compileEnvTheory.cs_extends_def]) >>
     rename1 `sb.cs_blocks = extra ++ s5.cs_blocks` >>
     `extra = []` by
       (qpat_assum `sb.cs_blocks = extra ++ _` (mp_tac o Q.AP_TERM `LENGTH`) >>
        qpat_assum `s5.cs_blocks = sb.cs_blocks` (pure_once_rewrite_tac o single) >>
        simp_tac (srw_ss()) []) >>
     `isPREFIX s5.cs_current_insts sb.cs_current_insts` by
       (qpat_assum `if extra = [] then _ else _` mp_tac >>
        qpat_assum `extra = []` (fn th => simp_tac (srw_ss()) [th])) >>
     drule rich_listTheory.IS_PREFIX_IMP_TAKE >>
     disch_then (fn th => simp[emitHelperPropsTheory.inst_extends_def,emitted_insts_def,Once th,listTheory.TAKE_DROP])) >>
  `emitted_insts sa sb = emitted_insts sa s4 ++ (emitted_insts s4 s5 ++ emitted_insts s5 sb)` by
    (`emitted_insts s4 sb = emitted_insts s4 s5 ++ emitted_insts s5 sb` by
       (irule emitted_insts_append >>
        simp[GSYM emitHelperPropsTheory.inst_extends_def]) >>
     `emitted_insts sa sb = emitted_insts sa s4 ++ emitted_insts s4 sb` by
       (irule emitted_insts_append >>
        simp[GSYM emitHelperPropsTheory.inst_extends_def]) >>
     simp[]) >>
  `run_inst_seq (emitted_insts s5 sb) r = OK t` by
    (qpat_assum `run_inst_seq (emitted_insts sa sb) s = OK t` mp_tac >>
     qpat_assum `emitted_insts sa sb = _` (pure_once_rewrite_tac o single) >>
     qpat_assum `run_inst_seq (emitted_insts sa s4) s = OK h`
       (pure_once_rewrite_tac o single o MATCH_MP run_inst_seq_append) >>
     qpat_assum `run_inst_seq (emitted_insts s4 s5) h = OK r`
       (pure_once_rewrite_tac o single o MATCH_MP run_inst_seq_append) >>
     tautLib.TAUT_TAC) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa s4) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts s5 sb)` by
    (qpat_assum `EVERY (\i. _ /\ _) (emitted_insts sa sb)` mp_tac >>
     qpat_assum `emitted_insts sa sb = _` (pure_once_rewrite_tac o single) >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[listTheory.EVERY_APPEND,listTheory.EVERY_MEM] >> metis_tac[]) >>
  `alloca_inv r` by
    (qpat_assum `stmt_state_rel H0 ctx func cenv cx es r`
       (mp_then Any mp_tac stmt_state_rel_local_ptrs_alloca) >> simp[]) >>
  Q.SUBGOAL_THEN
    `w2n w + (32 + ((n+31) DIV 32)*32) <= b \/ b + (64 + ((n+31) DIV 32)*32) <= w2n w`
    assume_tac
  >- (irule abiCallerAllocationTheory.abi_caller_allocation_separate >>
      qexistsl_tac [`alloc.inst_id`,`r`,`s4.cs_next_id`] >> simp[] >> decide_tac) >>
  `n <= ((n+31) DIV 32)*32` by
    (qspec_then `n` mp_tac valueTypingMemoryPropsTheory.word_size_capacity >>
     simp[vfmConstantsTheory.word_size_def]) >>
  Q.SUBGOAL_THEN `w2n w+32+LENGTH (TAKE n s.vs_returndata) <= b \/ b+32 <= w2n w` assume_tac
  >- decide_tac >>
  `w2n w + (32 + ((n+31) DIV 32)*32) < dimword (:256)` by
    (`s.vs_alloca_next < dimword (:256)` by
       (qpat_assum `stmt_state_rel H0 ctx func cenv cx es s`
          (mp_then Any mp_tac stmt_state_rel_alloca_room) >>
        simp[alloca_room_def] >> decide_tac) >> decide_tac) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp r)` by
    qpat_assum `stmt_state_rel H0 ctx func cenv cx es r`
      (ACCEPT_TAC o MATCH_MP stmt_state_rel_allocas_below_fmp) >>
  qpat_assum `buf.buf_operand = Var p` (fn th =>
    qpat_assum `emit_void MSTORE [buf.buf_operand;ok] s5 = _`
      (assume_tac o PURE_REWRITE_RULE [th]) >>
    qpat_assum `emit_op ADD [buf.buf_operand;Lit 32w] s6 = _`
      (assume_tac o PURE_REWRITE_RULE [th])) >>
  qabbrev_tac `j = s.vs_inst_idx + LENGTH (emitted_insts sa s4) + LENGTH (emitted_insts s4 s5)` >>
  mp_tac (Q.INST [`s1` |-> `s6`,`s2` |-> `s7`,`a` |-> `w2n (w:256 word)`,
                  `bs` |-> `TAKE n s.vs_returndata`] raw_tuple_copy_indexed_effects) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >>
  disch_then (qx_choose_then `Gf` (qx_choose_then `tnf` strip_assume_tac)) >>
  `!D. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s Gf tnf` by
    (gen_tac >> qpat_assum `emitted_insts sa sb = _` (pure_once_rewrite_tac o single) >>
     irule instSeqComposePtrTheory.inst_seq_ptr_append_ok >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`G1`,`h`,`tn1`] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac
     >- (qpat_assum `!D. inst_seq_ptr D _ _ _ _ G tn _ _ _ _` (qspec_then `D` ACCEPT_TAC)) >>
     irule instSeqComposePtrTheory.inst_seq_ptr_append_ok >>
     conj_asm1_tac
     >- (qpat_assum `emitted_insts s4 s5 = [i]` (pure_once_rewrite_tac o single) >>
         simp[Abbr `i`,mk_inst_def,is_terminator_def]) >>
     qexistsl_tac [`G2`,`r with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa s4)`,`tn2`] >>
     conj_tac
     >- (qpat_assum `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts s4 s5)`
           (mp_then Any (pure_rewrite_tac o single) fragExecTheory.run_inst_seq_inst_idx) >>
         qpat_assum `run_inst_seq (emitted_insts s4 s5) h = OK r` (pure_rewrite_tac o single) >>
         simp_tac (srw_ss()) [instIdxIndepTheory.exec_result_map_def]) >>
     conj_tac
     >- (qpat_assum `emitted_insts s4 s5 = [i]` (pure_once_rewrite_tac o single) >>
         qpat_assum `!D j. inst_seq_ptr D _ _ _ _ G1 tn1 _ _ _ _` irule) >>
     qpat_assum `!D. inst_seq_ptr D _ _ _ _ G2 tn2 _ _ _ _` (qspec_then `D` mp_tac) >>
     simp_tac (srw_ss()) [Abbr `j`,arithmeticTheory.ADD_ASSOC]) >>
  mp_tac (Q.INST [`code` |-> `emitted_insts sa sb`,`ov` |-> `Var x`]
    raw_tuple_suffix_path_at_end) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE REFL_TAC))) >>
  simp_tac bool_ss [LET_THM] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!v. not_fresh_at sf v ==>
      lookup_var v t = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v)` by
    (qx_gen_tac `zv` >> strip_tac >>
     `not_fresh_at sa zv` by (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sf` >> simp[]) >>
     `not_fresh_at s4 zv` by (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sf` >> simp[]) >>
     `not_fresh_at s5 zv` by (drule loweringHaltTheory.compile_alloc_buffer_parts >> simp[]) >>
     qpat_assum `!v. not_fresh_at sa v ==> _` drule >>
     qpat_assum `!v. not_fresh_at s4 v ==> _` drule >>
     qpat_assum `!v. not_fresh_at s5 v ==> _` drule >>
     rpt (disch_then strip_assume_tac) >> simp[]) >>
  `!i. ~(w2n w <= i /\ i < w2n w+32) /\
       ~(b <= i /\ i < b+(64 + ((n+31) DIV 32)*32)) /\ i IN tnf.t_mem ==> i IN tn.t_mem` by
    (`b+32+(32+((n+31) DIV 32)*32) = b+(64+((n+31) DIV 32)*32)` by decide_tac >>
     qpat_assum `b+32+_ = _` (fn th =>
       mp_tac (PURE_REWRITE_RULE [th]
         (Q.INST [`a` |-> `w2n (w:256 word)`,`k` |-> `32+((n+31) DIV 32)*32`]
           tuple_copy_taint_window))) >>
     impl_tac
     >- (conj_tac >- first_assum ACCEPT_TAC >>
         reverse conj_tac
         >- (qpat_assum `tnf.t_mem = _` (ACCEPT_TAC o PURE_REWRITE_RULE [arithmeticTheory.ADD_ASSOC] ) ORELSE simp[]) >>
         qx_gen_tac `ix` >> strip_tac >>
         qpat_assum `!i. _ ==> (i IN tn2.t_mem <=> _)` (qspec_then `ix` mp_tac) >>
         `ix < b \/ b + (64 + ((n+31) DIV 32)*32) <= ix` suffices_by
           (disch_tac >> simp[]) >> decide_tac) >>
     disch_then ACCEPT_TAC) >>
  `i.inst_opcode = ALLOCA /\ i.inst_outputs = [p] /\ i.inst_id = s4.cs_next_id` by
    simp_tac (srw_ss()) [Abbr `i`,mk_inst_def] >>
  `FLOOKUP r.vs_allocas i.inst_id = SOME (b,64+((n+31) DIV 32)*32)` by simp[] >>
  `sf.cs_next_id <= i.inst_id` by (qpat_assum `i.inst_id = _` (pure_rewrite_tac o single) >> first_assum ACCEPT_TAC) >>
  `!z. not_fresh_at sf z ==> FLOOKUP Gf z = FLOOKUP G z /\ op_taint tnf (Var z) = op_taint tn (Var z)` by
    (gen_tac >> strip_tac >> qpat_assum `!v. not_fresh_at sf v ==> lookup_var v t = _ /\ _` drule >> simp[]) >>
  `ghost_kept_at lo cenv es0 sf G0 tn0 s0 Gf tnf` by
    (mp_tac (Q.INST [`H` |-> `H0`,`alloc'` |-> `i`,`a` |-> `w2n (w:256 word)`,
                    `L` |-> `32+((n+31) DIV 32)*32`,`k` |-> `64+((n+31) DIV 32)*32`]
      (INST_TYPE [``:α`` |-> ``:256``,``:β`` |-> ``:num # num``] raw_tuple_two_row_caller_kept)) >>
     (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >>
     disch_then ACCEPT_TAC) >>
  qabbrev_tac `k = 32 + ((n+31) DIV 32)*32` >>
  `(r with <|vs_vars := h.vs_vars; vs_allocas := h.vs_allocas;
             vs_alloca_next := h.vs_alloca_next|>) = h` by
    (qpat_assum `Abbrev (i = _)` (fn th =>
       qpat_assum `step_inst_base i h = OK r`
        (mp_tac o PURE_ONCE_REWRITE_RULE [PURE_REWRITE_RULE [markerTheory.Abbrev_def] th])) >>
     disch_then (mp_then (Pat `step_inst_base _ _ = _`) mp_tac tuple_alloca_rows) >>
     disch_then (qspec_then `b` mp_tac) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then (ACCEPT_TAC o CONJUNCT1)) >>
  `t.vs_data_section = s.vs_data_section /\ t.vs_call_ctx = s.vs_call_ctx /\
   t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
   t.vs_immutables = s.vs_immutables /\
   t.vs_allocas = r.vs_allocas /\ t.vs_alloca_next = r.vs_alloca_next` by
    (map_every (fn pat => qpat_assum pat
       (mp_tac o Q.AP_TERM `\v. (v.vs_data_section,v.vs_call_ctx,v.vs_accounts,v.vs_transient,v.vs_immutables)`))
       [`(r with <|vs_vars := _; vs_allocas := _; vs_alloca_next := _|>) = h`,
        `(h with vs_vars := _) = _`] >>
     qpat_assum `(t with vs_vars := _) = _` (mp_tac o Q.AP_TERM
       `\v. (v.vs_data_section,v.vs_call_ctx,v.vs_accounts,v.vs_transient,v.vs_immutables,v.vs_allocas,v.vs_alloca_next)`) >>
     simp_tac (srw_ss()) [mcopy_def,mstore_def,write_memory_with_expansion_def,
                           LET_THM,venom_state_accessors] >>
     rpt strip_tac >> asm_rewrite_tac[]) >>
  `tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm` by
    (map_every (fn pat => qpat_assum pat (pure_once_rewrite_tac o single))
      [`tnf.t_stor = tn2.t_stor`,`tn2.t_stor = tn1.t_stor`,`tn1.t_stor = tn.t_stor`,
       `tnf.t_trans = tn2.t_trans`,`tn2.t_trans = tn1.t_trans`,`tn1.t_trans = tn.t_trans`,
       `tnf.t_imm = tn2.t_imm`,`tn2.t_imm = tn1.t_imm`,`tn1.t_imm = tn.t_imm`] >> simp[]) >>
  `b+32+k = b+(64+((n+31) DIV 32)*32) /\ 32 <= k` by
    (simp_tac (srw_ss()) [Abbr `k`] >> decide_tac) >>
  `!off len. (off+len <= w2n w \/ w2n w+32 <= off) /\
      (off+len <= b \/ b+32+k <= off) ==>
      mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory` by
    (qpat_assum `(t with vs_vars := _) = _`
       (assume_tac o SIMP_RULE (srw_ss()) [venom_state_accessors] o Q.AP_TERM `\v. v.vs_memory`) >>
     qpat_assum `h.vs_memory = r.vs_memory` (fn th =>
       qpat_assum `(h with vs_vars := _) = _`
         (assume_tac o SIMP_RULE (srw_ss()) [venom_state_accessors,th] o Q.AP_TERM `\v. v.vs_memory`)) >>
     drule_all tuple_write_window >> disch_then (ACCEPT_TAC o CONJUNCT2)) >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH sb.cs_current_insts`,`Gf`,`tnf`] >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE ALL_TAC)
  >- suspend "current_ghost"
  >- (simp_tac bool_ss [bodyPtrIfExpAllocSourceTheory.ptr_vv_ok_inst_idx] >>
      irule bodyPtrAttributeFieldsTheory.ptr_vv_ok_memory >>
      `result = Var p` by simp[] >>
      qpat_assum `result = Var p` SUBST1_TAC >>
      qpat_assum `ptr_covers Gf tnf p t _`
        (strip_assume_tac o PURE_REWRITE_RULE [bodyPtrDefsTheory.ptr_covers_def]) >>
      `lookup_var p t = SOME (n2w b)` by
        (`not_fresh_at s5 p` by
           qpat_assum `safe_operand s5 (Var p)` (ACCEPT_TAC o SIMP_RULE (srw_ss()) [safe_operand_def]) >>
         qpat_assum `!v. not_fresh_at s5 v ==> _` drule >>
         disch_then (strip_assume_tac) >>
         qpat_assum `lookup_var p t = lookup_var p r` (pure_rewrite_tac o single) >> first_assum ACCEPT_TAC) >>
      simp_tac (srw_ss()) [contextTheory.mk_ptr_def,vyperStateTheory.read_result_def,vyperStateTheory.return_def,
           bodyPtrDefsTheory.ptr_mem_ok_def,eval_operand_def] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      map_every (fn pat => qpat_assum pat (pure_rewrite_tac o single))
        [`post_value_type cenv e = _`,`evaluate_type (get_tenv cx) (expr_type e) = _`,
         `lookup_var p t = SOME (n2w b)`,
         `v = ArrayV (TupleV [BoolV success;BytesV (TAKE n s.vs_returndata)])`] >>
      `w2n (n2w b : 256 word) = b` by (simp_tac (srw_ss()) [w2n_n2w] >> decide_tac) >>
      qpat_assum `w2n (n2w b : 256 word) = b` (fn tw =>
        simp_tac (srw_ss()) [optionTheory.SOME_11,tw]) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      disch_tac >> qexistsl_tac [`b'`,`sz'`] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      `w' = n2w b` by (qpat_assum `lookup_var p t = SOME w'` mp_tac >>
          qpat_assum `lookup_var p t = SOME (n2w b)` (pure_rewrite_tac o single) >>
          simp_tac (srw_ss()) []) >>
      qpat_assum `w' = n2w b` SUBST_ALL_TAC >>
      qpat_assum `w2n (n2w b : 256 word) = b` SUBST_ALL_TAC >>
      simp_tac (srw_ss()) [val_store_size_def,valueEncodingTheory.type_memory_size_def,
          vfmConstantsTheory.word_size_def,arithmeticTheory.ADD_ASSOC] >>
      decide_tac)
  >- (`result = Var p` by simp[] >>
      qpat_assum `result = Var p` SUBST1_TAC >>
      irule rawCallBufferPtrTheory.ptr_buf_ok_from_covers >>
      qexistsl_tac [`64 + ((n+31) DIV 32)*32`,`tnf`] >>
      simp[ghostPcTransportPtrTheory.ptr_covers_inst_idx,
           compileEnvTheory.type_memory_bytes_def] >> decide_tac)
  >- (qx_gen_tac `H` >> strip_tac >>
      asm "ordinary" (qspec_then `H` mp_tac) >> simp[LET_THM]) >>
  suspend "registered_frame"
QED

Resume raw_buffered_tuple_finish_frame_registered[current_ghost]:
  pure_rewrite_tac [ghostPcTransportPtrTheory.ghost_inv_at_inst_idx] >>
  gen_tac >> strip_tac >>
  `stor_taint_ok_at D tnf t` by
    (qpat_assum `ghost_inv_at D lo dep cenv cx es G tn s`
       (strip_assume_tac o PURE_REWRITE_RULE [bodyPtrDefsTheory.ghost_inv_at_def]) >>
     pure_rewrite_tac [bodyPtrDefsTheory.stor_taint_ok_at_def] >>
     map_every (fn pat => qpat_assum pat (pure_once_rewrite_tac o single))
       [`t.vs_call_ctx = _`,`t.vs_accounts = _`,`t.vs_transient = _`,`t.vs_immutables = _`,
        `tnf.t_stor = tn.t_stor`,`tnf.t_trans = tn.t_trans`,`tnf.t_imm = tn.t_imm`] >>
     qpat_assum `stor_taint_ok_at D tn s`
       (ACCEPT_TAC o PURE_REWRITE_RULE [bodyPtrDefsTheory.stor_taint_ok_at_def])) >>
  `lo <= b` by
    (qpat_assum `allocas_from lo r` (strip_assume_tac o REWRITE_RULE [allocas_from_def]) >>
     first_x_assum irule >> qexists_tac `s4.cs_next_id` >> simp[]) >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by
    (conj_tac
     >- (pure_rewrite_tac [allocas_from_def] >>
         qpat_assum `t.vs_allocas = _` (pure_once_rewrite_tac o single) >>
         qpat_assum `allocas_from lo r` (ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
     qpat_assum `t.vs_alloca_next = _` (pure_once_rewrite_tac o single) >> decide_tac) >>
  `local_ptrs_rel func cenv es.scopes s /\
   local_ptrs_rel func cenv es.scopes r /\ alloca_inv r` by
    (qpat_assum `stmt_state_rel H0 ctx func cenv cx es s`
       (mp_then Any assume_tac stmt_state_rel_local_ptrs_alloca) >>
     qpat_assum `stmt_state_rel H0 ctx func cenv cx es r`
       (mp_then Any assume_tac stmt_state_rel_local_ptrs_alloca) >> simp[]) >>
  `!lp zw. not_fresh_at sf lp /\ lookup_var lp s = SOME zw ==> lookup_var lp r = SOME zw` by
    (rpt gen_tac >> strip_tac >>
     `not_fresh_at sa lp /\ not_fresh_at s4 lp` by
       (conj_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sf` >> simp[]) >>
     qpat_assum `!v. not_fresh_at sa v ==> _` (qspec_then `lp` mp_tac) >>
     qpat_assum `!v. not_fresh_at s4 v ==> _` (qspec_then `lp` mp_tac) >>
     simp[]) >>
  `!name off len. local_region cenv es.scopes s name off len ==>
     mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory /\
     (!ix. off <= ix /\ ix < off+len /\ ix IN tnf.t_mem ==> ix IN tn.t_mem)` by
    (rpt gen_tac >> strip_tac >>
     `local_region cenv es.scopes r name off len` by
       (irule local_region_frame_fwd >> qexistsl_tac [`s`,`sf`,`es.scopes`] >>
        rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE REFL_TAC)) >>
     `regions_disjoint (w2n w) k off len` by
       (irule localPtrsPropsTheory.local_ptrs_rel_alloca_disjoint >>
        qexistsl_tac [`cenv`,`func`,`alloc`,`name`,`q`,`es.scopes`,`s`] >> simp[]) >>
     `regions_disjoint b (64 + ((n+31) DIV 32)*32) off len` by
       (irule localPtrsPropsTheory.local_ptrs_rel_alloca_disjoint >>
        qexistsl_tac [`cenv`,`func`,`i`,`name`,`p`,`es.scopes`,`r`] >> simp[]) >>
     qpat_assum `regions_disjoint (w2n w) k off len`
       (assume_tac o REWRITE_RULE [loweringStateRelDefsTheory.regions_disjoint_def]) >>
     qpat_assum `regions_disjoint b _ off len`
       (assume_tac o REWRITE_RULE [loweringStateRelDefsTheory.regions_disjoint_def]) >>
     conj_tac
     >- (qpat_assum `!off len. _ ==> mem_bytes_at off len t.vs_memory = _` irule >> decide_tac) >>
     gen_tac >> strip_tac >>
     qpat_assum `!i. _ ==> i IN tn.t_mem` irule >>
     conj_tac >- decide_tac >> conj_tac >- decide_tac >> first_assum ACCEPT_TAC) >>
  `mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo s.vs_memory` by
    (qpat_assum `!off len. _ ==> mem_bytes_at off len t.vs_memory = _` irule >> decide_tac) >>
  `!ix. ix < lo /\ ix IN tnf.t_mem ==> ix IN tn.t_mem` by
    (gen_tac >> strip_tac >> qpat_assum `!i. _ ==> i IN tn.t_mem` irule >>
     conj_tac >- decide_tac >> conj_tac >- decide_tac >> first_assum ACCEPT_TAC) >>
  `!lp zw. not_fresh_at sf lp /\ lookup_var lp s = SOME zw ==> lookup_var lp t = SOME zw` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!v. not_fresh_at sf v ==> lookup_var v t = _ /\ _` drule >> simp[]) >>
  irule bodyPtrBytestringBuiltinsWindowGhostTheory.ghost_inv_at_local_window_transport >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`G`,`es`,`func`,`s`,`sf`,`tn`] >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE REFL_TAC)
QED

Resume raw_buffered_tuple_finish_frame_registered[registered_frame]:
  qexistsl_tac [`i`,`b`] >>
  simp_tac (srw_ss()) [LET_THM, allocation_growth_index, venom_state_accessors] >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE ALL_TAC)
  >- (simp_tac (srw_ss()) [lookup_var_def,venom_state_accessors] >>
      rpt gen_tac >> strip_tac >>
      qpat_assum `!v. not_fresh_at sf v ==> lookup_var v t = _ /\ _` drule >>
      disch_then (SUBST1_TAC o REWRITE_RULE [lookup_var_def] o CONJUNCT1) >>
      first_assum ACCEPT_TAC)
  >- (irule run_inst_seq_allocation_growth >>
      qexists_tac `emitted_insts sa sb` >> first_assum ACCEPT_TAC)
  >- (irule run_inst_seq_memory_length >>
      qexists_tac `emitted_insts sa sb` >> first_assum ACCEPT_TAC)
  >- (`FLOOKUP t.vs_allocas alloc.inst_id = SOME (w2n w,k)` by
        (qpat_assum `t.vs_allocas = _` (pure_rewrite_tac o single) >>
         qpat_assum `!aid row. FLOOKUP h.vs_allocas aid = SOME row ==> _` irule >>
         first_assum ACCEPT_TAC) >>
      rpt gen_tac >> strip_tac
      >- (qexistsl_tac [`k`,`alloc`,`q`] >> simp[])
      >> qexistsl_tac [`64+((n+31) DIV 32)*32`,`i`,`p`] >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `len = 0` >- simp[valueEncodingDefsTheory.mem_bytes_at_def] >>
  Q.SUBGOAL_THEN `off+len <= w2n w \/ w2n w+32 <= off` assume_tac
  >- (qpat_assum `!aid p k. _ ==> venomMemDefs$regions_disjoint (off,len) (p,k)`
        (qspecl_then [`alloc.inst_id`,`w2n w`,`32`] mp_tac) >>
      qpat_assum `len <> 0` (fn th => simp_tac (srw_ss()) [th,venomMemDefsTheory.regions_disjoint_def])) >>
  Q.SUBGOAL_THEN `off+len <= b \/ b+(64+((n+31) DIV 32)*32) <= off` assume_tac
  >- (qpat_assum `!aid p k. _ ==> venomMemDefs$regions_disjoint (off,len) (p,k)`
        (qspecl_then [`i.inst_id`,`b`,`64+((n+31) DIV 32)*32`] mp_tac) >>
      qpat_assum `len <> 0` (fn th => simp_tac (srw_ss()) [th,venomMemDefsTheory.regions_disjoint_def])) >>
  conj_tac
  >- (qpat_assum `!off len. _ ==> mem_bytes_at off len t.vs_memory = _` irule >> decide_tac) >>
  gen_tac >> strip_tac >>
  qpat_assum `!i. _ ==> i IN tn.t_mem` irule >>
  conj_tac >- decide_tac >> conj_tac >- decide_tac >> first_assum ACCEPT_TAC
QED

Finalise raw_buffered_tuple_finish_frame_registered

(* Compatibility projection: both results use the same suffix endpoint. *)
Theorem raw_buffered_tuple_finish_frame:
  (if n > 0 then
       do z <- emit_op RETURNDATASIZE [];
          cmp <- emit_op LT [z;Lit (n2w n)];
          cap <- compile_select cmp z (Lit (n2w n));
          emit_void MSTORE [Var x;cap];
          buf <- compile_alloc_buffer (64 + ((n + 31) DIV 32) * 32);
          emit_void MSTORE [buf.buf_operand;ok];
          dst <- emit_op ADD [buf.buf_operand;Lit 32w];
          emit_void MCOPY [dst;Var x;Lit (n2w (32 + ((n + 31) DIV 32) * 32))];
          return buf.buf_operand od
     else return ok) sa = (result,sb) /\ 0 < n /\
  stmt_state_rel (H0:(bool # 256 word # type_value) list # num list)
    ctx func cenv cx es s /\ wb_frame cenv es0 es sf s0 s /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  MEM alloc (fn_insts func) /\ alloc.inst_opcode = ALLOCA /\
  alloc.inst_outputs = [q] /\ not_local_ptr cenv es.scopes q /\
  FLOOKUP s.vs_allocas alloc.inst_id = SOME (w2n w,32 + ((n + 31) DIV 32) * 32) /\
  local_ptrs_reserved cenv sf /\ local_ptrs_reserved cenv sa /\
  sf.cs_next_var <= sa.cs_next_var /\ sf.cs_next_id <= alloc.inst_id /\
  alloc.inst_id < sa.cs_next_id /\ MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  safe_operand sa (Var x) /\ safe_operand sa ok /\ lookup_var x s = SOME w /\
  eval_operand ok s = SOME (if success then 1w else 0w) /\
  op_taint tn ok = {} /\ ptr_covers G tn x s (32 + ((n+31) DIV 32) * 32) /\
  s.vs_memory = (write_memory_with_expansion (w2n ro) (TAKE n data) pre).vs_memory /\
  s.vs_returndata = data /\
  tn.t_mem = old_tn.t_mem DIFF {j | w2n ro <= j /\ j < w2n ro + LENGTH (TAKE n data)} /\
  w2n ro = w2n w + 32 /\ LENGTH data < dimword (:256) /\
  64 + ((n + 31) DIV 32) * 32 < dimword (:256) /\ n < dimword (:256) /\
  allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size func s <= w2n s.vs_initial_fmp) /\
  (!v sz. cenv.ce_return_buf = SOME (PtrVar (Var v) sz) ==> not_fresh_at sf v) /\
  (!v sz. cenv.ce_return_pc = SOME (PtrVar (Var v) sz) ==> not_fresh_at sf v) /\
  ghost_kept_at lo cenv es0 sf G0 tn0 s0 G tn /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ alloca_history func s /\
  expr_has_effect e /\ post_value_type cenv e = expr_type e /\
  lowered_value_type cenv e = expr_type e /\
  expr_type e = TupleT [BaseT BoolT;BaseT (BytesT (Dynamic n))] /\
  evaluate_type (get_tenv cx) (expr_type e) =
    SOME (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic n))]) /\
  v = ArrayV (TupleV [BoolV success;BytesV (TAKE n data)]) /\
  vv = LocatedValue (expr_type e) (mk_ptr result LocMemory) ==>
  ?u Gf tnf.
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func u /\
    ghost_kept_at lo cenv es0 sf G0 tn0 s0 Gf tnf /\
    (!D. ghost_inv_at D lo dep cenv cx es G tn s ==>
      ghost_inv_at D lo dep cenv cx es Gf tnf u) /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,Gf,tnf)) /\
    ptr_vv_ok cx (post_value_type cenv e) (Value v)
      (LocatedValue (expr_type e) (mk_ptr result LocMemory)) es Gf tnf u /\
    ptr_buf_ok cenv e result Gf u /\
    (!H:(bool # 256 word # type_value) list # num list.
         stmt_state_rel H ctx func cenv cx es s /\
         storage_well_formed_on cx es (FST H) ==>
      vv_post H ctx func cenv cx e es0 sf sb s0 es (Value v)
        (LocatedValue (expr_type e) (mk_ptr result LocMemory)) u /\
      vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e)
        es (Value v) (LocatedValue (expr_type e) (mk_ptr result LocMemory)) u /\
      vv_own cenv cx (post_value_type cenv e) sf sb es (Value v)
        (LocatedValue (expr_type e) (mk_ptr result LocMemory)) u)
Proof
  disch_then (mp_tac o MATCH_MP raw_buffered_tuple_finish_frame_registered) >>
  disch_then (qx_choose_then `u` (qx_choose_then `Gf` (qx_choose_then `tnf`
    (map_every assume_tac o CONJUNCTS)))) >>
  qexistsl_tac [`u`,`Gf`,`tnf`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

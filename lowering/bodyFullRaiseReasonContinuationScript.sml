(* Resource boundary for the shared nonliteral reason continuation. *)
Theory bodyFullRaiseReasonContinuation
Ancestors
  bodyFullRaiseReasonHeadFrame bodyFullRaiseReasonHead bodyFullRaiseReasonTail bodyFullUnwrap
  allocationPtr revertAllocationPtr reasonResourcesPtr stmtReasonMemory
  reasonRepresentationPtr loweringPosts bodyPtrDefs loweringStateRelDefs
  vyperValue vyperTypeSystem contractABI abiEncoderPathProps compileEnv vfmConstants
  exprLoweringProps venomMemDefs venomInst venomState
  revertReasonLayout fragExec rich_list vyperStorageFootprint stmtReasonLitFragMemory
  finite_map arithmetic list

(* The encoder's size slot is a genuine function allocation, not an
   additional allocation-room assumption at the body call site. *)
Theorem reason_tail_allocation_resources:
  stmt_state_rel H ctx func cenv cx ee s /\
  (!i. MEM i (reason_tail j u v op) ==> MEM i (fn_insts func)) /\
  FLOOKUP s.vs_allocas aid = SOME (TP,M) /\ aid <> j+6 /\ 32 <= M ==>
  s.vs_alloca_next < dimword(:256) /\
  TP+M <= s.vs_alloca_next /\
  (FLOOKUP s.vs_allocas (j+6) = NONE ==>
    s.vs_alloca_next+32 < dimword(:256)) /\
  (!a sz. FLOOKUP s.vs_allocas (j+6) = SOME (a,sz) ==>
    sz=32 /\ a+32 <= s.vs_alloca_next /\
    (a+32 <= TP \/ TP+32 <= a))
Proof
  strip_tac >>
  `MEM (mk_inst (j+6) ALLOCA [Lit 32w] ["%" ++ toString (u+5)])
    (reason_tail j u v op)` by simp[reason_tail_def] >>
  `MEM (mk_inst (j+6) ALLOCA [Lit 32w] ["%" ++ toString (u+5)])
    (fn_insts func)` by metis_tac[] >>
  `32 < dimword(:256)` by simp[wordsTheory.dimword_def] >>
  `MEM (mk_inst (j+6) ALLOCA [Lit (n2w 32)] ["%" ++ toString (u+5)])
    (fn_insts func)` by simp[] >>
  drule_all stmt_state_rel_alloca_bounds >> strip_tac >>
  `alloca_inv s /\ alloca_room ctx func s` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[stmt_state_rel_def] >> metis_tac[]) >>
  `s.vs_alloca_next < dimword(:256)` by metis_tac[alloca_room_next_lt] >>
  qpat_x_assum `alloca_inv s` mp_tac >>
  pure_rewrite_tac[alloca_inv_def, alloca_next_valid_def,
    allocas_non_overlapping_def] >> strip_tac >>
  conj_tac >- simp[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- simp[] >>
  rpt gen_tac >> disch_tac >>
  `sz = 32` by metis_tac[] >>
  qpat_x_assum `sz = 32` SUBST_ALL_TAC >> simp[NoAsms] >>
  conj_tac >- metis_tac[] >>
  `TP+M <= a \/ a+32 <= TP` by metis_tac[] >> decide_tac
QED

(* This boundary consumes precisely the old-variable/ghost and write-back
   frames returned by shared unwrap. The encoder's allocation premises
   are recovered here rather than passed to the body theorem. *)
Theorem reason_normalized_tail_origin_ptr:
  stmt_state_rel H ctx func cenv cx ee s ==>
  wb_frame cenv ee ee sb sh s ==>
  ghost_kept_at lo cenv ee sb Gh tnh sh G tn ==>
  expr_val_rel cx (BaseT (StringT cap)) (StringV str) op s ==>
  isPREFIX (reason_tail j u v op) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  (!x. op = Var x ==> not_fresh_at sc x) ==>
  sb.cs_next_id = id+4 ==>
  lookup_var ("%" ++ toString v) sh = SOME (n2w B) ==>
  lookup_var ("%" ++ toString (v+2)) sh = SOME (n2w TP) ==>
  ptr_covers Gh tnh ("%" ++ toString (v+2)) sh M ==>
  sb.cs_next_var = v+3 /\
  v+3 <= u /\ id+4 <= j /\ sc.cs_next_var = u /\
  (!x. not_fresh_at sb x ==> lookup_var x s = lookup_var x sh) /\
  lookup_var ("%" ++ toString v) sh = SOME (n2w B) /\
  lookup_var ("%" ++ toString (v+1)) sh = SOME (n2w (B+32)) /\
  lookup_var ("%" ++ toString (v+2)) sh = SOME (n2w TP) /\
  ptr_covers Gh tnh ("%" ++ toString v) sh (64+M) /\
  ptr_covers Gh tnh ("%" ++ toString (v+1)) sh (32+M) /\
  ptr_covers Gh tnh ("%" ++ toString (v+2)) sh M /\
  FLOOKUP sh.vs_allocas id = SOME (B,64+M) /\
  FLOOKUP sh.vs_allocas (id+3) = SOME (TP,M) /\
  ptr_val_ok cx (BaseT (StringT cap)) (StringV str) op G tn s /\
  evaluate_type (get_tenv cx) (BaseT (StringT cap)) = SOME (BaseTV (StringT cap)) /\
  val_wf (BaseTV (StringT cap)) (StringV str) /\
  M = type_memory_bytes cenv (BaseT (StringT cap)) /\
  expr_store_bound cx (BaseT (StringT cap)) (StringV str) op s /\
  64+M < dimword(:256) /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  (!i. MEM i (reason_tail j u v op) ==> MEM i (fn_insts func)) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next ==>
  ?z Gf tnf. !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (Abort Revert_abort z,Gf,tnf)
Proof
  rpt strip_tac >>
  `?w. eval_operand op s = SOME w` by metis_tac[expr_val_rel_def] >>
  `~is_word_type (BaseT (StringT cap))` by simp[is_word_type_def] >>
  drule_all ptr_val_ok_string_covers >> strip_tac >>
  rename1 `op = Var src` >> qpat_x_assum `op = Var src` SUBST_ALL_TAC >>
  suspend "source"
QED

Resume reason_normalized_tail_origin_ptr[source]:
  `ptr_mem_ok cx (BaseT (StringT cap)) (StringV str) (Var src) G tn s` by
    metis_tac[ptr_val_ok_def] >>
  drule_all reason_string_length_word >> strip_tac >>
  `!i. w2n w <= i /\ i < w2n w+32 ==> i NOTIN tn.t_mem` by
    metis_tac[reason_string_head_clean] >>
  drule reason_string_capacity_bounds >> strip_tac >>
  `32+32*word_size (LENGTH str) <= M` by
    metis_tac[reason_string_type_capacity] >>
  `32+contractABI$ceil32 (LENGTH str) <= M /\
    ptr_covers G tn src s (32+contractABI$ceil32 (LENGTH str))` by
    (pure_rewrite_tac[contractABITheory.ceil32_def, GSYM word_size_def] >>
     metis_tac[]) >>
  `mload (w2n w) s = n2w (LENGTH str)` by
    (qpat_assum `mem_word_at _ _ = _` mp_tac >>
     simp[NoAsms, mload_def, valueEncodingDefsTheory.mem_word_at_def]) >>
  `lookup_var src s = SOME (n2w (w2n w))` by
    (qpat_assum `eval_operand (Var src) s = SOME w` mp_tac >>
     simp[NoAsms, eval_operand_def]) >>
  `LENGTH str+63 < dimword(:256) /\ 32 <= M /\
    w2n w+32+contractABI$ceil32 (LENGTH str) <= s.vs_alloca_next` by
    (qpat_assum `expr_store_bound _ _ _ _ _` mp_tac >>
     simp[NoAsms, exprSimMemDefsTheory.expr_store_bound_def,
       exprSimPropsTheory.val_store_size_def, is_word_type_def] >>
     disch_then (qspecl_then [`BaseTV (StringT cap)`,`w`] mp_tac) >>
     simp[NoAsms] >>
     impl_tac >- metis_tac[] >>
     pure_rewrite_tac[contractABITheory.ceil32_def, GSYM word_size_def] >>
     strip_tac >> decide_tac) >>
  suspend "buffers"
QED

Resume reason_normalized_tail_origin_ptr[buffers]:
  `!k. k < 3 ==> not_fresh_at sb ("%" ++ toString (v+k))` by
    (rpt strip_tac >> simp[NoAsms, not_fresh_at_def,
       ASCIInumbersTheory.toString_inj] >> decide_tac) >>
  `not_fresh_at sb ("%" ++ toString v) /\
   not_fresh_at sb ("%" ++ toString (v+1)) /\
   not_fresh_at sb ("%" ++ toString (v+2))` by
    (simp[NoAsms, not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
     rpt strip_tac >> decide_tac) >>
  `!x. not_fresh_at sb x ==>
     FLOOKUP G x = FLOOKUP Gh x /\
     op_taint tn (Var x) = op_taint tnh (Var x)` by
    (qpat_assum `ghost_kept_at _ _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[ghost_kept_at_def] >> metis_tac[]) >>
  `lookup_var ("%" ++ toString v) s = SOME (n2w B) /\
   lookup_var ("%" ++ toString (v+1)) s = SOME (n2w (B+32)) /\
   lookup_var ("%" ++ toString (v+2)) s = SOME (n2w TP)` by
    (metis_tac[ADD_0]) >>
  `ptr_covers G tn ("%" ++ toString v) s (64+M) /\
   ptr_covers G tn ("%" ++ toString (v+1)) s (32+M) /\
   ptr_covers G tn ("%" ++ toString (v+2)) s M` by
    (pure_rewrite_tac[ptr_covers_def] >>
     qpat_assum `ptr_covers Gh tnh _ _ (64+M)` mp_tac >>
     qpat_assum `ptr_covers Gh tnh _ _ (32+M)` mp_tac >>
     qpat_assum `ptr_covers Gh tnh _ _ M` mp_tac >>
     pure_rewrite_tac[ptr_covers_def] >> metis_tac[ADD_0]) >>
  suspend "allocation"
QED

Resume reason_normalized_tail_origin_ptr[allocation]:
  `FLOOKUP s.vs_allocas id = SOME (B,64+M) /\
   FLOOKUP s.vs_allocas (id+3) = SOME (TP,M)` by
    (qpat_assum `wb_frame _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[wb_frame_def] >> metis_tac[]) >>
  `id+3 <> j+6` by decide_tac >>
  drule_all reason_tail_allocation_resources >> strip_tac >>
  `alloca_inv s` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[stmt_state_rel_def] >> metis_tac[]) >>
  `B+64+M <= s.vs_alloca_next` by
    (qpat_assum `alloca_inv s` mp_tac >>
     pure_rewrite_tac[alloca_inv_def, alloca_next_valid_def] >>
     metis_tac[ADD_ASSOC]) >>
  `v+2 < u` by decide_tac >>
  `!k. src <> "%" ++ toString (u+k)` by
    (qpat_assum `!x. Var src = Var x ==> _` mp_tac >>
     simp[NoAsms, not_fresh_at_def] >> strip_tac >>
     gen_tac >> first_x_assum irule >> decide_tac) >>
  irule reason_tail_origin_ptr_path >>
  ntac 5 (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`B`,`LENGTH str`,`M`,`TP`,`bb`,`j`,`w2n w`,`src`,`u`,`v`] >>
  metis_tac[]
QED

Finalise reason_normalized_tail_origin_ptr

Theorem reason_nonliteral_encoder_origin_ptr:
  compile_expr cenv ty e sa = (vv,sm) /\
  compile_revert_with_reason cenv vv mt M sm = ((),sf) /\
  expr_type e = BaseT (StringT cap) /\
  M = type_memory_bytes cenv (BaseT (StringT cap)) /\
  64+M < dimword(:256) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sf func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!rt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
       ~is_word_type (post_value_type cenv e) ==>
       type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rt /\
       type_memory_size rt < 2**64) /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty /\
  (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rty v) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
       vv_post H ctx func cenv cx e es sa sm s0 ee tv vv s /\
       ghost_inv_at (DF H) lo d cenv cx ee G tn s) /\
  vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv vv s /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn s /\
  (!vt op0. vv = StackValue vt op0 /\ ~is_word_type (post_value_type cenv e) ==>
           ptr_buf_ok cenv e op0 G s) /\
  (!vt p. vv = LocatedValue vt p /\ p.ptr_location = LocMemory ==>
         ptr_buf_ok cenv e p.ptr_operand G s) /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
   ?val. read_result cx tv ee = (INL val,ee) /\
   !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
          eval_operand (vv_operand vv) s = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
                 val_in_memory rt val (w2n w) mem)) /\
  ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?z Gf tnf. !H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (Abort Revert_abort z,Gf,tnf)
Proof
  strip_tac >>
  drule compile_revert_reason_layout >>
  disch_then (qx_choosel_then [`sb`,`sc`,`op`] strip_assume_tac) >>
  `ci_mono sb sc` by
    (qspecl_then [`cenv`,`vv`,`sb`] mp_tac ci_mono_unwrap_value >> simp[]) >>
  `cs_extends sm sb /\ cs_extends sb sc /\ cs_extends sc sf /\
   sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
   sb.cs_next_var <= sc.cs_next_var /\ sb.cs_next_id <= sc.cs_next_id` by
    (qpat_assum `ci_mono sb sc` mp_tac >>
     simp[NoAsms, ci_mono_def] >> strip_tac >>
     simp[cs_extends_def, IS_PREFIX_APPEND]) >>
  `fn_has_code sm sb func /\ fn_has_code sb sc func /\ fn_has_code sc sf func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  impl_tac >- fs[storage_trace_domain_def] >> strip_tac >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx ee s` by
    (qpat_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[vv_post_def] >> metis_tac[]) >>
  `alloca_room ctx func s /\ alloca_next_valid s` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[stmt_state_rel_def, alloca_inv_def] >> metis_tac[]) >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by
    (qpat_assum `ghost_inv_at _ _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[ghost_inv_at_def] >> metis_tac[]) >>
  `sb.cs_current_bb = sm.cs_current_bb /\
   sb.cs_current_insts = sm.cs_current_insts ++ reason_head sm.cs_next_id sm.cs_next_var M` by
    simp[reason_head_def, revert_reason_prefix_def] >>
  drule_all fn_has_code_code >> strip_tac >>
  `MEM (mk_inst sm.cs_next_id ALLOCA [Lit (n2w (64+M))]
      ["%" ++ toString sm.cs_next_var]) (fn_insts func) /\
   MEM (mk_inst (sm.cs_next_id+3) ALLOCA [Lit (n2w M)]
      ["%" ++ toString (sm.cs_next_var+2)]) (fn_insts func)` by
    (conj_tac >> first_x_assum irule >> simp[reason_head_def]) >>
  `M < dimword(:256)` by decide_tac >>
  `(!x. FLOOKUP s.vs_allocas sm.cs_next_id = SOME x ==> SND x = 64+M) /\
   (!x. FLOOKUP s.vs_allocas (sm.cs_next_id+3) = SOME x ==> SND x = M)` by
    (drule_all (Q.INST [`id` |-> `sm.cs_next_id`, `n` |-> `64+M`]
       stmt_state_rel_alloca_bounds) >> strip_tac >>
     drule_all (Q.INST [`id` |-> `sm.cs_next_id+3`, `n` |-> `M`]
       stmt_state_rel_alloca_bounds) >> strip_tac >>
     conj_tac >> gen_tac >> PairCases_on `x` >> simp[NoAsms] >>
     strip_tac >> metis_tac[ADD_COMM]) >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   isPREFIX (reason_head sm.cs_next_id sm.cs_next_var M)
     (DROP s.vs_inst_idx bb.bb_instructions)` by metis_tac[] >>
  drule_all reason_head_origin_ptr_path >>
  disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`]
    (qx_choosel_then [`th`,`Gh`,`thn`,`B`,`TP`] strip_assume_tac)) >>
  suspend "unwrap"
QED

Resume reason_nonliteral_encoder_origin_ptr[unwrap]:
  `post_value_type cenv e = expr_type e` by
    simp[post_value_type_bytestring, is_bytestring_type_def] >>
  `~is_word_type (post_value_type cenv e)` by
    simp[post_value_type_bytestring, is_bytestring_type_def, is_word_type_def] >>
  `is_word_type (post_value_type cenv e) ==> is_word_type (expr_type e)` by simp[] >>
  mp_tac (Q.INST [`t` |-> `th`,
    `z` |-> `th with vs_inst_idx := s.vs_inst_idx+4`,
    `Gf` |-> `Gh`, `tnf` |-> `thn`] reason_head_unwrap_inputs) >>
  (impl_tac >- (rpt conj_tac >> simp[])) >>
  disch_then strip_assume_tac >>
  mp_tac (Q.INST [`s` |-> `th with vs_inst_idx := s.vs_inst_idx+4`,
    `G` |-> `Gh`, `tn` |-> `thn`]
    bodyFullUnwrapTheory.unwrap_value_origin_ptr) >>
  (impl_tac >- (rpt conj_tac >>
    first_assum (ACCEPT_TAC o PURE_REWRITE_RULE
      [SYM (ASSUME ``post_value_type cenv e = expr_type e``)]))) >>
  disch_then (qx_choosel_then [`val`,`su`,`Gu`,`tu`] strip_assume_tac) >>
  `post_value_type cenv e = BaseT (StringT cap)` by
    simp[post_value_type_bytestring, is_bytestring_type_def] >>
  `rty = BaseTV (StringT cap)` by
    gvs[evaluate_type_def] >>
  `value_has_type (BaseTV (StringT cap)) val` by metis_tac[] >>
  `?str. val = StringV str` by
    metis_tac[vyperTypeValuesTheory.value_has_type_StringTV] >>
  qpat_x_assum `val = StringV str` SUBST_ALL_TAC >>
  `val_wf (BaseTV (StringT cap)) (StringV str)` by
    metis_tac[valueEncodingTypingTheory.value_has_type_val_wf] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  impl_tac >- fs[storage_trace_domain_def] >> strip_tac >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx ee su /\
   expr_val_rel cx (BaseT (StringT cap)) (StringV str) op su` by
    (qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[expr_post_def] >> metis_tac[]) >>
  `!x. op = Var x ==> not_fresh_at sc x` by
    (rpt strip_tac >> irule exprOperandVarTheory.compiler_unwrap_value_var >>
     qexistsl_tac [`cenv`,`op`,`sb`,`vv`] >> simp[] >>
     Cases_on `vv` >> simp[] >> rpt strip_tac >>
     irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sm` >> simp[] >>
     qpat_assum `!x. vv_operand _ = Var x ==> _` mp_tac >>
     simp[contextTheory.vv_operand_def]) >>
  `~su.vs_halted` by
    (qpat_assum `gas_origin_ptr_path _ _ [] (OK su,Gu,tu)` mp_tac >>
     disch_then (mp_tac o MATCH_MP fragGasOriginPtrExecTheory.gas_origin_ptr_path_exec) >>
     simp[fragExecTheory.exit_result_def]) >>
  `allocas_from lo su /\ lo <= su.vs_alloca_next` by
    (qpat_assum `ghost_inv_at _ _ _ _ _ _ _ _ su` mp_tac >>
     pure_rewrite_tac[ghost_inv_at_def] >> metis_tac[]) >>
  suspend "tail_inputs"
QED

Resume reason_nonliteral_encoder_origin_ptr[tail_inputs]:
  `sf.cs_current_bb = sc.cs_current_bb /\
   sf.cs_current_insts = sc.cs_current_insts ++
     reason_tail sc.cs_next_id sc.cs_next_var sm.cs_next_var op` by
    simp[reason_tail_def, revert_reason_copy_def, revert_reason_suffix_def] >>
  mp_tac (Q.INST [`sa` |-> `sc`, `sb` |-> `sf`,
    `code` |-> `reason_tail sc.cs_next_id sc.cs_next_var sm.cs_next_var op`]
    (SPEC_ALL fn_has_code_code)) >>
  impl_tac >- simp[] >> strip_tac >>
  `!k. k < 2 ==> not_local_ptr cenv ee.scopes
    ("%" ++ toString (sm.cs_next_var+k))` by
    (rpt strip_tac >> simp[] >> irule local_ptrs_reserved_fresh >>
     qexists_tac `sm` >> simp[]) >>
  qpat_assum `fn_inst_ids_distinct func /\ _ ==> _` mp_tac >>
  impl_tac >- simp[] >> strip_tac >>
  `sb.cs_next_var = sm.cs_next_var+3 /\
   sb.cs_next_id = sm.cs_next_id+4 /\
   sm.cs_next_var+3 <= sc.cs_next_var /\
   sm.cs_next_id+4 <= sc.cs_next_id` by
    (qpat_x_assum `sb = _` SUBST_ALL_TAC >> gvs[]) >>
  `lookup_block su.vs_current_bb func.fn_blocks = SOME bb' /\
   isPREFIX (reason_tail sc.cs_next_id sc.cs_next_var sm.cs_next_var op)
     (DROP su.vs_inst_idx bb'.bb_instructions)` by simp[] >>
  `lookup_var ("%" ++ toString sm.cs_next_var)
      (th with vs_inst_idx := s.vs_inst_idx+4) = SOME (n2w B) /\
   lookup_var ("%" ++ toString (sm.cs_next_var+1))
      (th with vs_inst_idx := s.vs_inst_idx+4) = SOME (n2w (B+32)) /\
   lookup_var ("%" ++ toString (sm.cs_next_var+2))
      (th with vs_inst_idx := s.vs_inst_idx+4) = SOME (n2w TP)` by
    fs[lookup_var_def] >>
  `ptr_covers Gh thn ("%" ++ toString sm.cs_next_var)
      (th with vs_inst_idx := s.vs_inst_idx+4) (64+M) /\
   ptr_covers Gh thn ("%" ++ toString (sm.cs_next_var+1))
      (th with vs_inst_idx := s.vs_inst_idx+4) (32+M) /\
   ptr_covers Gh thn ("%" ++ toString (sm.cs_next_var+2))
      (th with vs_inst_idx := s.vs_inst_idx+4) M` by
    (fs[ptr_covers_def, lookup_var_def]) >>
  qpat_assum `stmt_state_rel _ _ _ _ _ _ su`
    (mp_then Any mp_tac reason_normalized_tail_origin_ptr) >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then drule >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then drule >> disch_then drule >>
  disch_then (qspecl_then [`explicit`,`PG`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> simp[] >> gvs[]) >>
  strip_tac >> qexistsl_tac [`z`,`Gf`,`tnf`] >> rpt strip_tac >>
  irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
  qexistsl_tac [`Gh`,`th with vs_inst_idx := s.vs_inst_idx + 4`,`thn`] >>
  conj_tac >- metis_tac[] >>
  irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
  qexistsl_tac [`Gu`,`su`,`tu`] >> metis_tac[]
QED

Finalise reason_nonliteral_encoder_origin_ptr

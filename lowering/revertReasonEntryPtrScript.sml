(* Compiler-entry wrappers: source facts are transported through the actual
   checked prefix before invoking a concrete normalization continuation. *)
Theory revertReasonEntryPtr
Ancestors
  revertReasonAllocatedPtr revertReasonIdentityPtr revertReasonPrefixCodePtr
  revertReasonPrefixFramePtr revertReasonLayout exprLoweringProps exprSimCopy
  context compileEnv bodyPtrDefs loweringPosts venomInst venomState
  words arithmetic finite_map list ptrDiscipline fragGasPathPtr
  revertReasonMemoryFramePtr valueEncoding venomMemDefs instIdxIndep
  exprLowering revertReasonTailCodePtr

Theorem revert_reason_prefix_old_operand_frame:
  copy_old_operand sa op /\
  run_inst_seq (revert_reason_prefix sa.cs_next_id sa.cs_next_var ms) s = OK t /\
  inst_seq_ptr D lo ctx fn PG G tn
    (revert_reason_prefix sa.cs_next_id sa.cs_next_var ms) s Gf tf ==>
  eval_operand op t = eval_operand op s /\ op_taint tf op = op_taint tn op
Proof
  strip_tac >> drule revert_reason_prefix_labels_frame >> strip_tac >>
  Cases_on `op` >> simp[eval_operand_def, op_taint_def] >>
  rename1 `Var x` >>
  `!k. k < 3 ==> x <> STRING #"%" (toString (sa.cs_next_var+k))` by
    (fs[copy_old_operand_def, not_fresh_at_def] >> rpt strip_tac >>
     first_x_assum (qspec_then `sa.cs_next_var+k` mp_tac) >> simp[]) >>
  drule revert_reason_prefix_old_observations >> disch_then drule >> strip_tac >>
  first_x_assum (qspec_then `x` mp_tac) >>
  simp[op_taint_def, ADD_COMM]
QED

Theorem revert_reason_prefix_storage_holds:
  storage_holds cx tr ty tv a es s /\
  run_inst_seq (revert_reason_prefix id v ms) s = OK t ==>
  storage_holds cx tr ty tv a es t
Proof
  strip_tac >> drule revert_reason_prefix_data_frame >> strip_tac >>
  fs[storage_holds_def, contract_storage_def, contract_transient_def]
QED

Theorem compile_revert_reason_storage_path_ptr:
  compile_revert_with_reason cenv (LocatedValue (BaseT (StringT max)) r) mt ms sa = ((),sb) /\
  fn_has_code sa sb fn /\ stmt_state_rel ctx fn cenv cx es s /\
  fn_inst_ids_distinct fn /\
  (!k. k < 3 ==> not_local_ptr cenv es.scopes
    (STRING #"%" (toString (sa.cs_next_var+k)))) /\
  r.ptr_location = (if tr then LocTransient else LocStorage) /\
  storage_holds cx tr (BaseT (StringT max)) tv a es s /\
  read_result cx tv es = (INL (StringV str),es) /\
  val_wf (BaseTV (StringT max)) (StringV str) /\
  copy_old_operand sa r.ptr_operand /\
  eval_operand r.ptr_operand s = SOME a /\ op_taint tn r.ptr_operand = {} /\
  key_taint (if tr then tn.t_trans else tn.t_stor) a = {} /\
  32 * type_slot_size (BaseTV (StringT max)) < dimword(:256) /\
  32+contractABI$ceil32 (LENGTH str) <= ms /\ LENGTH str+63 < dimword(:256) /\
  64+ms < dimword(:256) /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?z Gf tnf. gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (Abort Revert_abort z)
Proof
  strip_tac >> drule_all compile_revert_reason_prefix_code >> strip_tac >>
  `sm.cs_current_bb = sa.cs_current_bb /\ sb.cs_current_bb = sn.cs_current_bb` by
    fs[same_blocks_def] >>
  drule_at (Pat `_ = _ ++ _`) revert_reason_prefix_at_compile_endpoint_ptr >>
  disch_then drule_all >>
  disch_then (qspecl_then [`tn`,`PG`,`G`,`D`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK u)` >>
  drule_all revert_reason_prefix_old_operand_frame >> strip_tac >>
  drule_all revert_reason_prefix_storage_holds >> strip_tac >>
  drule revert_reason_prefix_ghost_observations >> strip_tac >>
  `storage_holds cx tr (BaseT (StringT max)) tv a es u /\
   eval_operand r.ptr_operand u = SOME a /\ op_taint tnf r.ptr_operand = {} /\
   key_taint (if tr then tnf.t_trans else tnf.t_stor) a = {}` by
    fs[Abbr `u`, eval_operand_def, storage_holds_def,
       contract_storage_def, contract_transient_def] >>
  `copy_old_operand sm r.ptr_operand` by
    (fs[copy_old_operand_def] >> metis_tac[freshWritesTheory.not_fresh_at_mono, LESS_EQ_ADD]) >>
  `!k. k < 3 ==> not_fresh_at sm (STRING #"%" (toString (sa.cs_next_var+k)))` by
    (simp[not_fresh_at_def] >> rpt strip_tac >> simp[]) >>
  qpat_assum `!k. k < 3 ==> not_fresh_at sm _`
    (fn th => map_every (fn k => qspec_then k assume_tac th) [`0`,`1`,`2`]) >>
  `not_fresh_at sm (STRING #"%" (toString sa.cs_next_var)) /\
   not_fresh_at sm (STRING #"%" (toString (sa.cs_next_var+1))) /\
   not_fresh_at sm (STRING #"%" (toString (sa.cs_next_var+2))) /\
   sa.cs_next_id+3 < sm.cs_next_id /\
   w2n B+64+ms < dimword(:256) /\ w2n P+32+ms < dimword(:256) /\
   type_slot_size (BaseTV (StringT max)) < dimword(:256)` by
    (fs[] >> decide_tac) >>
  `?z Gh th. gas_path_ptr D 0 ctx fn PG Gf tnf u 0 Gh th (Abort Revert_abort z)` by
    (Cases_on `max = 0`
     >- (qpat_x_assum `max = 0` SUBST_ALL_TAC >>
         drule_at (Pat `_ = _ ++ _`) revert_reason_storage_zero_unwrap_path_ptr >>
         disch_then drule_all >> simp[]) >>
     `0 < max` by decide_tac >>
     drule_at (Pat `_ = _ ++ _`) revert_reason_storage_positive_unwrap_path_ptr >>
     disch_then drule_all >> simp[]) >>
  drule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ (OK _)`) gas_path_ptr_then >>
  disch_then drule >> simp[NoAsms] >> metis_tac[]
QED

Theorem immutable_holds_runtime_state_independent:
  ~cenv.ce_is_ctor /\ immutable_holds cenv cx ty tv a es s ==>
  immutable_holds cenv cx ty tv a es t
Proof
  simp[immutable_holds_def] >> metis_tac[]
QED

Theorem compile_revert_reason_runtime_code_path_ptr:
  compile_revert_with_reason cenv (LocatedValue (BaseT (StringT max)) r) mt ms sa = ((),sb) /\
  fn_has_code sa sb fn /\ stmt_state_rel ctx fn cenv cx es s /\
  fn_inst_ids_distinct fn /\
  (!k. k < 3 ==> not_local_ptr cenv es.scopes
    (STRING #"%" (toString (sa.cs_next_var+k)))) /\
  ~cenv.ce_is_ctor /\ r.ptr_location = LocCode /\
  immutable_holds cenv cx (BaseT (StringT max)) (Value (StringV str)) a es s /\
  evaluate_type (get_tenv cx) (BaseT (StringT max)) = SOME (BaseTV (StringT max)) /\
  copy_old_operand sa r.ptr_operand /\
  eval_operand r.ptr_operand s = SOME a /\ op_taint tn r.ptr_operand = {} /\
  32 * type_slot_size (BaseTV (StringT max)) < dimword(:256) /\
  32+contractABI$ceil32 (LENGTH str) <= ms /\ LENGTH str+63 < dimword(:256) /\
  64+ms < dimword(:256) /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?z Gf tnf. gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (Abort Revert_abort z)
Proof
  strip_tac >> drule_all compile_revert_reason_prefix_code >> strip_tac >>
  `sm.cs_current_bb = sa.cs_current_bb /\ sb.cs_current_bb = sn.cs_current_bb` by
    fs[same_blocks_def] >>
  drule_at (Pat `_ = _ ++ _`) revert_reason_prefix_at_compile_endpoint_ptr >>
  disch_then drule_all >>
  disch_then (qspecl_then [`tn`,`PG`,`G`,`D`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK u)` >>
  drule_all revert_reason_prefix_old_operand_frame >> strip_tac >>
  `immutable_holds cenv cx (BaseT (StringT max)) (Value (StringV str)) a es u /\
   eval_operand r.ptr_operand u = SOME a /\ op_taint tnf r.ptr_operand = {}` by
    (conj_tac >- metis_tac[immutable_holds_runtime_state_independent] >>
     simp[Abbr `u`, instIdxIndepTheory.eval_op_inst_idx]) >>
  `copy_old_operand sm r.ptr_operand` by
    (fs[copy_old_operand_def] >> metis_tac[freshWritesTheory.not_fresh_at_mono, LESS_EQ_ADD]) >>
  `!k. k < 3 ==> not_fresh_at sm (STRING #"%" (toString (sa.cs_next_var+k)))` by
    (simp[not_fresh_at_def] >> rpt strip_tac >> simp[]) >>
  qpat_assum `!k. k < 3 ==> not_fresh_at sm _`
    (fn th => map_every (fn k => qspec_then k assume_tac th) [`0`,`1`,`2`]) >>
  `not_fresh_at sm (STRING #"%" (toString sa.cs_next_var)) /\
   not_fresh_at sm (STRING #"%" (toString (sa.cs_next_var+1))) /\
   not_fresh_at sm (STRING #"%" (toString (sa.cs_next_var+2))) /\
   sa.cs_next_id+3 < sm.cs_next_id /\
   w2n B+64+ms < dimword(:256) /\ w2n P+32+ms < dimword(:256)` by fs[] >>
  `?z Gh th. gas_path_ptr D 0 ctx fn PG Gf tnf u 0 Gh th (Abort Revert_abort z)` by
    (drule_at (Pat `_ = _ ++ _`) revert_reason_runtime_immutable_unwrap_path_ptr >>
     disch_then drule_all >> simp[]) >>
  drule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ (OK _)`) gas_path_ptr_then >>
  disch_then drule >> simp[NoAsms] >> metis_tac[]
QED

Theorem compile_revert_reason_memory_path_ptr:
  compile_revert_with_reason cenv vv mt ms sa = ((),sb) /\
  (vv = StackValue ty (Var src) \/
   (vv = LocatedValue ty r /\ ~is_word_type ty /\
    r.ptr_location = LocMemory /\ r.ptr_operand = Var src)) /\
  fn_has_code sa sb fn /\ stmt_state_rel ctx fn cenv cx es s /\
  fn_inst_ids_distinct fn /\
  (!k. k < 3 ==> not_local_ptr cenv es.scopes
    (STRING #"%" (toString (sa.cs_next_var+k)))) /\
  copy_old_operand sa (Var src) /\ lookup_var src s = SOME A /\
  ptr_covers G tn src s (32+contractABI$ceil32 L) /\
  mload (w2n A) s = n2w L /\
  (!j. w2n A <= j /\ j < w2n A+32 ==> j NOTIN tn.t_mem) /\
  ((?aid a sz. FLOOKUP s.vs_allocas aid = SOME (a,sz) /\ aid < sa.cs_next_id /\
      a <= w2n A /\ w2n A+32 <= a+sz) \/
   (?name a sz. local_region cenv es.scopes s name a sz /\
      a <= w2n A /\ w2n A+32 <= a+sz)) /\
  32+contractABI$ceil32 L <= ms /\ L+63 < dimword(:256) /\
  64+ms < dimword(:256) /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?z Gf tnf. gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (Abort Revert_abort z)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all compile_revert_reason_prefix_code >> strip_tac >>
  `sm.cs_current_bb = sa.cs_current_bb /\ sb.cs_current_bb = sn.cs_current_bb` by
    fs[same_blocks_def] >>
  drule_at (Pat `_ = _ ++ _`) revert_reason_prefix_at_compile_endpoint_ptr >>
  disch_then drule_all >>
  disch_then (qspecl_then [`tn`,`PG`,`G`,`D`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK u)` >>
  `!k. k < 3 ==> src <> STRING #"%" (toString (sa.cs_next_var+k))` by
    (fs[copy_old_operand_def, not_fresh_at_def] >> rpt strip_tac >>
     first_x_assum (qspec_then `sa.cs_next_var+k` mp_tac) >> simp[]) >>
  drule_all revert_reason_prefix_lookup_frame >> strip_tac >>
  drule_all revert_reason_prefix_old_ptr_covers >> strip_tac >>
  drule_all revert_reason_prefix_code >> strip_tac >>
  `alloca_inv t` by
    (qpat_x_assum `alloca_inv u` mp_tac >>
     simp[Abbr `u`, alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def]) >>
  drule_all revert_reason_prefix_head_frame >> strip_tac >>
  `lookup_var src u = SOME A /\ ptr_covers Gf tnf src u (32+contractABI$ceil32 L) /\
   mload (w2n A) u = n2w L` by
    gvs[Abbr `u`, lookup_var_def, ptr_covers_def, mload_def] >>
  `not_fresh_at sm src /\ not_fresh_at sm (STRING #"%" (toString sa.cs_next_var)) /\
   not_fresh_at sm (STRING #"%" (toString (sa.cs_next_var+1))) /\
   not_fresh_at sm (STRING #"%" (toString (sa.cs_next_var+2))) /\
   sa.cs_next_id+3 <> sm.cs_next_id+5 /\
   w2n B+64+ms < dimword(:256) /\ w2n P+32+ms < dimword(:256)` by
    (fs[copy_old_operand_def, not_fresh_at_def] >> rpt strip_tac >> gvs[]) >>
  `op = Var src /\ sn = sm` by
    (qpat_x_assum `vv = _ \/ _` strip_assume_tac >>
     qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
     asm_rewrite_tac[unwrap_value_def, comp_return_def] >>
     simp[NoAsms, comp_return_def]) >>
  qpat_x_assum `op = Var src` SUBST_ALL_TAC >>
  qpat_x_assum `sn = sm` SUBST_ALL_TAC >>
  drule_at (Pat `_ = _ ++ _`) revert_reason_tail_code >> disch_then drule_all >> strip_tac >>
  `!a sz. FLOOKUP u.vs_allocas (sm.cs_next_id+5) = SOME (a,sz) ==> sz = 32` by
    (rpt strip_tac >> qpat_x_assum `!i n a sz. _` drule >>
     simp[NoAsms, mk_inst_def] >> disch_then drule >> simp[]) >>
  `?z Gh th. gas_path_ptr D 0 ctx fn PG Gf tnf u 0 Gh th (Abort Revert_abort z)` by
    (drule_at (Pat `_ = _ ++ _`) revert_reason_tail_at_compile_endpoint_ptr >>
     disch_then drule_all >> disch_then MATCH_ACCEPT_TAC) >>
  drule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ (OK _)`) gas_path_ptr_then >>
  disch_then drule >> simp[NoAsms] >> metis_tac[]
QED

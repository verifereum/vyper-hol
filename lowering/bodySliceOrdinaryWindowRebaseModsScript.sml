(* Rebase the successful window on the very same linked execution. *)
Theory bodySliceOrdinaryWindowRebaseMods
Ancestors
  bodyFullPostsMods exprSimCalldataSlice exprSimWordArgs wordArgsPtr
  bodyMemoryDefs logTupleOwnershipPtr actualAllocExec stateRelProj
  venomMemDefs loweringPosts bodyPtrDefs context exprSimProps loweringStateRelDefs
  abiDecoderFrame

Triviality slice_window_memory_post:
  vv_post_mods H ctx func cenv cx e es sa sb s0 ef (Value v)
    (LocatedValue ann (mk_ptr out LocMemory)) z <=>
  vv_post H ctx func cenv cx e es sa sb s0 ef (Value v)
    (LocatedValue ann (mk_ptr out LocMemory)) z /\
  immutable_frame_mods func cenv cx ef z
Proof
  simp[vv_post_mods_def,vv_post_def,vv_holds_mods_def,vv_place_ptr_mods_def,mk_ptr_def] >>
  rpt (EQ_TAC ORELSE disch_then (map_every assume_tac o CONJUNCTS)) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* Only the allocation interval and the entry frames change at a cut. *)
Triviality slice_window_extend:
  stmt_state_rel (H:(bool # bytes32 # type_value) list # num list) ctx func cenv cx es s /\
  local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  wb_frame cenv es ee sa s u /\
  (~expr_has_effect e ==> pure_frame cenv func es sa s u) /\
  ghost_kept_at lo cenv es sa G tn s Gu tu /\
  ghost_kept_at lo cenv ee sm Gu tu u Gz tz /\
  vv_post_mods H ctx func cenv cx e ee sm sb u ef (Value v)
    (LocatedValue ann (mk_ptr out LocMemory)) z ==>
  vv_post_mods H ctx func cenv cx e es sa sb s ef (Value v)
    (LocatedValue ann (mk_ptr out LocMemory)) z /\
  ghost_kept_at lo cenv es sa G tn s Gz tz
Proof
  simp[slice_window_memory_post] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  conj_tac
  >- (irule vv_post_prefix_frame >> simp[] >> qexistsl_tac [`ee`,`sm`,`u`] >> simp[]) >>
  drule_all_then ACCEPT_TAC ghost_kept_at_wb_trans
QED

Triviality slice_window_extend_read:
  stmt_state_rel (H:(bool # bytes32 # type_value) list # num list) ctx func cenv cx es s /\
  local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  expr_post_mods H ctx func cenv cx arg es sa sm s ee v op u /\
  (~expr_has_effect e ==> ~expr_has_effect arg) /\
  ghost_kept_at lo cenv es sa G tn s Gu tu /\
  ghost_kept_at lo cenv ee sm Gu tu u Gz tz /\
  vv_post_mods H ctx func cenv cx e ee sm sb u ef (Value result)
    (LocatedValue ann (mk_ptr out LocMemory)) z ==>
  vv_post_mods H ctx func cenv cx e es sa sb s ef (Value result)
    (LocatedValue ann (mk_ptr out LocMemory)) z /\
  ghost_kept_at lo cenv es sa G tn s Gz tz
Proof
  simp[expr_post_mods_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then assume_tac expr_post_frame >>
  `~expr_has_effect e ==> pure_frame cenv func es sa s u` by
    (strip_tac >> drule expr_post_pure_frame >> simp[]) >>
  irule slice_window_extend >>
  qpat_assum `vv_post_mods _ _ _ _ _ _ _ _ _ u _ _ _ _` (irule_at Any) >> simp[] >>
  qexistsl_tac [`tu`,`Gu`] >> simp[]
QED

Triviality slice_window_dynamic_capture:
  scs.vs_memory = sms.vs_memory /\ scs.vs_allocas = sms.vs_allocas /\
  scs.vs_alloca_next = sms.vs_alloca_next /\ tc.t_mem = tm.t_mem /\
  (!x. not_fresh_at sm x ==> lookup_var x scs = lookup_var x sms /\
       FLOOKUP Gc x = FLOOKUP Gm x /\ op_taint tc (Var x) = op_taint tm (Var x)) ==>
  wb_frame cenv ec ec sm sms scs /\ pure_frame cenv func ec sm sms scs /\
  ghost_kept_at lo cenv ec sm Gm tm sms Gc tc
Proof
  rw[wb_frame_def,pure_frame_def,ghost_kept_at_def,locals_kept_mem] >>
  qpat_assum `!x. not_fresh_at sm x ==> _` (drule_then strip_assume_tac) >> gvs[]
QED

(* The staging allocation may be reused.  Protect old regions by
   separation, not by assuming the staging base is above the frontier. *)
Triviality slice_window_fixed_capture:
  compile_alloc_buffer 32 sm = (buf,stage) /\ fn_has_code sm stage func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sm /\
  stmt_state_rel (H:(bool # bytes32 # type_value) list # num list) ctx func cenv cx ec sms /\
  stmt_state_rel H ctx func cenv cx ec scs /\
  FLOOKUP scs.vs_allocas sm.cs_next_id = SOME (p,32) /\
  (!aid entry. FLOOKUP sms.vs_allocas aid = SOME entry ==>
       FLOOKUP scs.vs_allocas aid = SOME entry) /\
  (!aid b len. aid < sm.cs_next_id /\ FLOOKUP sms.vs_allocas aid = SOME (b,len) ==>
       mem_bytes_at b len scs.vs_memory = mem_bytes_at b len sms.vs_memory) /\
  (!n b len. local_region cenv ec.scopes scs n b len ==>
       mem_bytes_at b len scs.vs_memory = mem_bytes_at b len sms.vs_memory) /\
  (!b len. b+len <= p \/ p+32 <= b ==>
       mem_bytes_at b len scs.vs_memory = mem_bytes_at b len sms.vs_memory) /\
  (!i. i < sms.vs_alloca_next /\ ~(p <= i /\ i < p+32) ==>
       (i IN tc.t_mem <=> i IN tm.t_mem)) /\
  (!x. not_fresh_at sm x ==> lookup_var x scs = lookup_var x sms /\
       FLOOKUP Gc x = FLOOKUP Gm x /\ op_taint tc (Var x) = op_taint tm (Var x)) ==>
  wb_frame cenv ec ec sm sms scs /\ pure_frame cenv func ec sm sms scs /\
  ghost_kept_at lo cenv ec sm Gm tm sms Gc tc
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!n b len. local_region cenv ec.scopes sms n b len ==>
       local_region cenv ec.scopes scs n b len` by
    (rpt strip_tac >> irule local_region_frame_fwd >>
     qexistsl_tac [`sms`,`sm`,`ec.scopes`] >> simp[] >> rpt strip_tac >>
     qpat_assum `!x. not_fresh_at sm x ==> _` (drule_then strip_assume_tac) >> simp[]) >>
  `!n b len. local_region cenv ec.scopes sms n b len ==>
       mem_bytes_at b len scs.vs_memory = mem_bytes_at b len sms.vs_memory` by
    (rpt strip_tac >>
     `local_region cenv ec.scopes scs n b len` by simp[] >>
     qpat_assum `!n b len. local_region _ _ scs n b len ==> _`
       (drule_then ACCEPT_TAC)) >>
  conj_tac
  >- (simp[wb_frame_def] >> conj_tac
      >- (rpt strip_tac >>
          qpat_assum `!aid b len. aid < sm.cs_next_id /\ _ ==> _`
            irule >> qexists_tac `aid` >> simp[]) >>
      irule locals_kept_regions >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (pure_rewrite_tac[pure_frame_def] >> conj_tac >- first_assum ACCEPT_TAC >>
      rpt gen_tac >> disch_then (qspecl_then
        [`mk_inst sm.cs_next_id ALLOCA [Lit 32w] [STRING #"%" (toString sm.cs_next_var)]`,
         `p`,`32`] mp_tac) >>
      `MEM (mk_inst sm.cs_next_id ALLOCA [Lit 32w]
           [STRING #"%" (toString sm.cs_next_var)]) (fn_insts func)` by
        (drule_all actual_alloc_buffer_site >> simp[]) >>
      simp[venomInstTheory.mk_inst_def,loweringStateRelDefsTheory.regions_disjoint_def] >>
      disch_tac >> qpat_assum `!b len. _ \/ _ ==> mem_bytes_at b len _ = _` irule >>
      decide_tac) >>
  `!b len i. b <= i /\ i < b+len /\ b+len <= sms.vs_alloca_next /\
       (b+len <= p \/ p+32 <= b) /\ i IN tc.t_mem ==> i IN tm.t_mem` by
    (rpt strip_tac >> `i < sms.vs_alloca_next /\ ~(p <= i /\ i < p+32)` by decide_tac >>
     qpat_assum `!i. i < sms.vs_alloca_next /\ _ ==> _` (drule_all_then mp_tac) >> simp[]) >>
  simp[ghost_kept_at_def] >>
  `alloca_inv sms /\ alloca_inv scs` by
    (conj_tac >> drule_then (ACCEPT_TAC o CONJUNCT2) stmt_state_rel_local_ptrs_alloca) >>
  `!aid off sz. FLOOKUP sms.vs_allocas aid = SOME (off,sz) ==>
     off+sz <= sms.vs_alloca_next` by
    (qpat_assum `alloca_inv sms` (strip_assume_tac o REWRITE_RULE
       [alloca_inv_def,alloca_next_valid_def]) >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!aid off sz. _ ==> off+sz <= sms.vs_alloca_next`
        (drule_then assume_tac) >>
      `FLOOKUP scs.vs_allocas aid = SOME (off,sz)` by simp[] >>
      `off+sz <= p \/ p+32 <= off` by
        (qpat_assum `alloca_inv scs` (strip_assume_tac o REWRITE_RULE
            [alloca_inv_def,allocas_non_overlapping_def]) >>
         qpat_assum `!a1 a2 b1 sz1 b2 sz2. _ ==> _`
            (qspecl_then [`aid`,`sm.cs_next_id`] mp_tac) >> simp[] >> decide_tac) >>
      qpat_assum `!b len i. _ ==> i IN tm.t_mem` irule >> simp[] >>
      qexistsl_tac [`off`,`sz`] >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `b+sz <= sms.vs_alloca_next` by (drule_all body_local_region_frontier >> simp[]) >>
  `local_region cenv ec.scopes scs n b sz` by simp[] >>
  `b+sz <= p \/ p+32 <= b` by
    (drule_all log_buffer_registered_local_region >>
     simp[abi_footprint_disjoint_def] >> disch_then (drule_then ACCEPT_TAC)) >>
  qpat_assum `!b len i. _ ==> i IN tm.t_mem` irule >> simp[] >>
  qexistsl_tac [`b`,`sz`] >> simp[]
QED


val read_cut = ``\arg es sa s0 (G0:string |-> num # num) tn0 ee sm s G tn v op.
  expr_post_mods (H:(bool # bytes32 # type_value) list # num list)
    ctx func cenv cx arg es sa sm s0 ee v op s /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn``;

val window_success = ``\es sa s0 G0 tn0.
  vv_post_mods (H:(bool # bytes32 # type_value) list # num list)
    ctx func cenv cx e es sa sb s0 ef (Value result) vv z /\
  vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e)
    ef (Value result) vv z /\
  z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
  s0.vs_alloca_next <= z.vs_alloca_next /\
  ghost_inv_at_mods (DF H) lo d cenv cx ef Gz tz z /\
  ptr_vv_ok cx (post_value_type cenv e) (Value result) vv ef Gz tz z /\
  ptr_buf_ok cenv e out Gz z /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 Gz tz``;

Theorem slice_ordinary_window_rebase_mods:
  let e = Builtin ann (Slice n) [src;start;len];
      vv = LocatedValue ann (mk_ptr out LocMemory)
  in
  is_bytestring_type ann /\
  stmt_state_rel H ctx func cenv cx es s0 /\
  stmt_state_rel H ctx func cenv cx ec scs /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  local_ptrs_reserved cenv sc /\ local_ptrs_reserved cenv sd /\
  ^read_cut src es sa s0 G0 tn0 ec sm sms Gm tm v0 op0 /\
  ^read_cut start ec sc scs Gc tc e1 sd sds Gd td v1 op1 /\
  ^read_cut len e1 sd sds Gd td e2 se ses Ge te v2 op2 /\
  sm.cs_next_var <= sc.cs_next_var /\ sm.cs_next_id <= sc.cs_next_id /\
  (!x. not_fresh_at sm x ==> lookup_var x scs = lookup_var x sms /\
       FLOOKUP Gc x = FLOOKUP Gm x /\ op_taint tc (Var x) = op_taint tm (Var x)) /\
  ((scs.vs_memory = sms.vs_memory /\ scs.vs_allocas = sms.vs_allocas /\
    scs.vs_alloca_next = sms.vs_alloca_next /\ tc.t_mem = tm.t_mem) \/
   (compile_alloc_buffer 32 sm = (buf,stage) /\ fn_has_code sm stage func /\
    fn_inst_ids_distinct func /\ sms.vs_alloca_next <= scs.vs_alloca_next /\
    FLOOKUP scs.vs_allocas sm.cs_next_id = SOME (p,32) /\
    (!aid entry. FLOOKUP sms.vs_allocas aid = SOME entry ==>
          FLOOKUP scs.vs_allocas aid = SOME entry) /\
    (!aid b len. aid < sm.cs_next_id /\ FLOOKUP sms.vs_allocas aid = SOME (b,len) ==>
          mem_bytes_at b len scs.vs_memory = mem_bytes_at b len sms.vs_memory) /\
    (!name b len. local_region cenv ec.scopes scs name b len ==>
          mem_bytes_at b len scs.vs_memory = mem_bytes_at b len sms.vs_memory) /\
    (!b len. b+len <= p \/ p+32 <= b ==>
          mem_bytes_at b len scs.vs_memory = mem_bytes_at b len sms.vs_memory) /\
    (!i. i < sms.vs_alloca_next /\ ~(p <= i /\ i < p+32) ==>
          (i IN tc.t_mem <=> i IN tm.t_mem)))) /\
  ^window_success e2 se ses Ge te ==>
  ^window_success es sa s0 G0 tn0 /\
  (!v. Value result = Value v /\ ~is_word_type (post_value_type cenv e) /\
       ~is_bytestring_type (post_value_type cenv e) ==>
       vv_own cenv cx (post_value_type cenv e) sa sb ef (Value result) vv z /\
       (!t p. vv = LocatedValue t p ==> p.ptr_location = LocMemory)) /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
   ?val. read_result cx (Value result) ef = (INL val,ef) /\
         !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
                eval_operand (vv_operand vv) z = SOME w ==>
                w2n w + type_memory_size rt <= lo /\
                (!mem. mem_agree_outside tz.t_mem z.vs_memory mem ==>
                       val_in_memory rt val (w2n w) mem)) /\
  (!t op. vv = StackValue t op /\ ~is_word_type (post_value_type cenv e) ==>
          ptr_buf_ok cenv e op Gz z) /\
  (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
         ptr_buf_ok cenv e p.ptr_operand Gz z)
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `stmt_state_rel H ctx func cenv cx ec sms` by
    (qpat_assum `expr_post_mods _ _ _ _ _ src _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
     drule_then ACCEPT_TAC expr_post_state) >>
  `stmt_state_rel H ctx func cenv cx e1 sds` by
    (qpat_assum `expr_post_mods _ _ _ _ _ start _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
     drule_then ACCEPT_TAC expr_post_state) >>
  `wb_frame cenv ec ec sm sms scs /\ pure_frame cenv func ec sm sms scs /\
   ghost_kept_at lo cenv ec sm Gm tm sms Gc tc /\ sms.vs_alloca_next <= scs.vs_alloca_next` by
    (qpat_x_assum `(_ /\ _) \/ (_ /\ _)` (DISJ_CASES_THEN (map_every assume_tac o CONJUNCTS))
     >- (drule_all slice_window_dynamic_capture >> simp[]) >>
     drule_all (SRULE [] slice_window_fixed_capture) >> simp[]) >>
  qabbrev_tac `e = Builtin ann (Slice n) [src;start;len]` >>
  `vv_post_mods H ctx func cenv cx e e1 sd sb sds ef (Value result)
     (LocatedValue ann (mk_ptr out LocMemory)) z /\
   ghost_kept_at lo cenv e1 sd Gd td sds Gz tz` by
    (irule slice_window_extend_read >>
     qpat_assum `expr_post_mods _ _ _ _ _ len _ _ _ _ _ _ _ _` (irule_at Any) >>
     `~expr_has_effect e ==> ~expr_has_effect len` by simp[Abbr `e`,expr_has_effect_thm] >>
     simp[] >> qexistsl_tac [`te`,`Ge`] >> simp[]) >>
  `vv_post_mods H ctx func cenv cx e ec sc sb scs ef (Value result)
     (LocatedValue ann (mk_ptr out LocMemory)) z /\
   ghost_kept_at lo cenv ec sc Gc tc scs Gz tz` by
    (irule slice_window_extend_read >>
     qpat_assum `expr_post_mods _ _ _ _ _ start _ _ _ _ _ _ _ _` (irule_at Any) >>
     `~expr_has_effect e ==> ~expr_has_effect start` by simp[Abbr `e`,expr_has_effect_thm] >>
     simp[] >> qexistsl_tac [`td`,`Gd`] >> simp[]) >>
  `vv_post_mods H ctx func cenv cx e ec sm sb sms ef (Value result)
     (LocatedValue ann (mk_ptr out LocMemory)) z /\
   ghost_kept_at lo cenv ec sm Gm tm sms Gz tz` by
    (irule slice_window_extend >>
     qpat_assum `vv_post_mods _ _ _ _ _ _ _ sc _ scs _ _ _ _` (irule_at Any) >>
     simp[] >> qexistsl_tac [`tc`,`Gc`] >> simp[]) >>
  `vv_post_mods H ctx func cenv cx e es sa sb s0 ef (Value result)
     (LocatedValue ann (mk_ptr out LocMemory)) z /\
   ghost_kept_at lo cenv es sa G0 tn0 s0 Gz tz` by
    (irule slice_window_extend_read >>
     qpat_assum `expr_post_mods _ _ _ _ _ src _ _ _ _ _ _ _ _` (irule_at Any) >>
     `~expr_has_effect e ==> ~expr_has_effect src` by simp[Abbr `e`,expr_has_effect_thm] >>
     simp[] >> qexistsl_tac [`tm`,`Gm`] >> simp[]) >>
  `post_value_type cenv e = ann` by simp[Abbr `e`,vyperASTTheory.expr_type_def] >>
  simp[mk_ptr_def,vv_location_def] >> decide_tac
QED

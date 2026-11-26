(* Finish a reached Concat operand fold with the logical-length store. *)
Theory bodyConcatHeaderMods
Ancestors
  bodyConcatCutsMods bodyFullBuiltinConcatFrame bodyECRecoverWriteFrameMods
  assignTuplePtrCopyLen exprSimConcatResult exprLoweringProps venomMemProps
  bodyPtrDefs bodyFullShadowBodyInv bodyFullPostsMods bodyInvSplit ptrDiscipline
  loweringStateRelDefs loweringShapeDefs exprSimFullBundleProps vyperStorageFootprint
  bodyPtrBytestringBuiltinsWindowGhost stateRelProj
  venomState arithmetic finite_map pred_set words

Theorem concat_header_mods:
  emit_op MLOAD [Var ov] s5 = (fo,sm) /\
  emit_void MSTORE [Var bv;fo] sm = ((),sb) /\
  fn_has_code s5 sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv s5 /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s5 x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s5 x) /\
  return_buf_frame d cenv s5 t5 /\
  not_fresh_at s4 bv /\ lookup_var bv t4 = SOME (n2w B) /\
  ptr_covers G4 tn4 bv t4 bsz /\
  concat_old_frame_mods (func,cenv,lo,pure) (dv,ov,ow,binst,oinst,B,bsz)
    (es,s4,t4,G4,tn4) (ee,s5,t5,G5,tn5) /\
  concat_live_mods (func,cenv,lo) (dv,ov,ow,binst,oinst,B,bsz)
    (ee,s5,t5,G5,tn5) p /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     concat_horizon_mods (ctx,func,cenv,cx,lo,d) (H,DF H) (ee,s5,t5,G5,tn5)) ==>
  ?t6 G6 tn6.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t5,G5,tn5) [] (OK t6,G6,tn6)) /\
    expr_sim_full_endpoint func sb t5 t6 /\ ~t6.vs_halted /\
    t6.vs_allocas = t5.vs_allocas /\ t6.vs_alloca_next = t5.vs_alloca_next /\
    (!x. not_fresh_at s5 x ==>
      lookup_var x t6 = lookup_var x t5 /\ FLOOKUP G6 x = FLOOKUP G5 x /\
      op_taint tn6 (Var x) = op_taint tn5 (Var x)) /\
    lookup_var bv t6 = SOME (n2w B) /\ ptr_covers G6 tn6 bv t6 bsz /\
    mload B t6 = n2w (LENGTH p) /\ mem_bytes_at (B+32) (LENGTH p) t6.vs_memory = p /\
    (!i. B <= i /\ i < B+32+LENGTH p ==> i NOTIN tn6.t_mem) /\
    (!a n. regions_disjoint a n B 32 ==>
      mem_bytes_at a n t6.vs_memory = mem_bytes_at a n t5.vs_memory) /\
    tn6.t_mem SUBSET tn5.t_mem /\ local_ptrs_reserved cenv sb /\
    return_buf_frame d cenv sb t6 /\ ghost_kept_at lo cenv ee s5 G5 tn5 t5 G6 tn6 /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      concat_horizon_mods (ctx,func,cenv,cx,lo,d) (H,DF H) (ee,sb,t6,G6,tn6))
Proof
  pure_rewrite_tac[concat_old_frame_mods_def,concat_live_mods_def,concat_horizon_mods_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `not_fresh_at s5 bv` by
    (irule not_fresh_at_mono >> qexists `s4` >> simp[]) >>
  `lookup_var bv t5 = SOME (n2w B)` by simp[] >>
  `ptr_covers G5 tn5 bv t5 bsz` by
    (qpat_assum `ghost_kept_at _ _ _ s4 _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >>
     irule ptr_covers_lookup_frame >> qexistsl_tac [`G4`,`t4`,`tn4`] >> simp[]) >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx ee t5` by
    (qpat_assum `storage_trace_domain _ _ _`
       (assume_tac o REWRITE_RULE [storage_trace_domain_def]) >>
     qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> _`
       (drule_then (map_every assume_tac o CONJUNCTS)) >> first_assum ACCEPT_TAC) >>
  `32 <= bsz /\ LENGTH p < dimword (:256) /\ w2n ow+32 <= t5.vs_alloca_next /\
   B+32 <= t5.vs_alloca_next` by decide_tac >>
  `!name b n. local_region cenv ee.scopes t5 name b n ==> regions_disjoint B 32 b n` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!name lb lsz. local_region cenv ee.scopes t5 name lb lsz ==> _ /\ _`
       (drule_then (map_every assume_tac o CONJUNCTS)) >>
     simp[regions_disjoint_def] >> decide_tac) >>
  drule_all concat_suffix_full >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`t6`,`G6`,`tn6`] (map_every assume_tac o CONJUNCTS))) >>
  qexistsl_tac [`t6`,`G6`,`tn6`] >>
  `mem_bytes_at (B+32) (LENGTH p) t6.vs_memory = p` by simp[] >>
  `!i. B <= i /\ i < B+32+LENGTH p ==> i NOTIN tn6.t_mem` by
    (gen_tac >> strip_tac >> Cases_on `i < B+32`
     >- (qpat_assum `!i. B <= i /\ i < B+32 ==> _` irule >> simp[]) >>
     `i NOTIN tn5.t_mem` by
       (qpat_assum `!i. B+32 <= i /\ i < B+32+LENGTH p ==> _` irule >> decide_tac) >>
     metis_tac[SUBSET_DEF]) >>
  `local_ptrs_reserved cenv sb` by
    (irule local_ptrs_reserved_next_var >> qexists `s5` >> simp[] >>
     drule_all concat_suffix_code >> strip_tac >> simp[]) >>
  `t6.vs_data_section = t5.vs_data_section /\
   t6.vs_call_ctx = t5.vs_call_ctx /\ t6.vs_accounts = t5.vs_accounts /\
   t6.vs_transient = t5.vs_transient /\ t6.vs_immutables = t5.vs_immutables /\
   LENGTH t5.vs_memory <= LENGTH t6.vs_memory` by
    (qpat_x_assum `t6 = mstore _ _ _ with vs_inst_idx := _`
       (fn th => simp_tac (srw_ss()) [th]) >>
     ntac 3 (conj_tac >- simp[mstore_def,update_var_def]) >>
     irule LESS_EQ_TRANS >>
     qmatch_goalsub_abbrev_tac `mstore B w (update_var x w t5)` >>
     qexists `LENGTH (update_var x w t5).vs_memory` >>
     conj_tac >- simp[update_var_def] >>
     simp[mstore_memory_nondecreasing]) >>
  qpat_x_assum `t6 = mstore _ _ _ with vs_inst_idx := _` kall_tac >>
  asm_simp_tac (srw_ss()) [expr_sim_full_endpoint_def] >>
  conj_tac
  >- (rewrite_tac[regions_disjoint_def] >>
      qpat_assum `!p n. _ ==> mem_bytes_at p n t6.vs_memory = _` ACCEPT_TAC) >>
  suspend "horizon"
QED

Resume concat_header_mods[horizon]:
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  `ghost_inv_at (DF H) 0 d cenv cx ee G5 tn5 t5` by
    (qpat_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`
       (map_every assume_tac o CONJUNCTS o REWRITE_RULE [ghost_inv_at_mods_def]) >>
     simp[ghost_inv_at_def,allocas_from_def] >> first_assum ACCEPT_TAC) >>
  `ghost_inv_at (DF H) 0 d cenv cx ee G6 tn6 t6` by
    (`local_ptrs_rel func cenv ee.scopes t5` by
       (drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >> first_assum ACCEPT_TAC) >>
     `stor_taint_ok_at (DF H) tn6 t6` by
       (qpat_assum `ghost_inv_at _ 0 _ _ _ _ _ _ _`
          (mp_tac o REWRITE_RULE [ghost_inv_at_def]) >> simp[stor_taint_ok_at_def]) >>
     irule ghost_inv_at_local_window_transport >>
     simp[allocas_from_def] >>
     qexistsl_tac [`G5`,`ee`,`func`,`t5`,`s5`,`tn5`] >>
     `mem_bytes_at 0 0 t6.vs_memory = mem_bytes_at 0 0 t5.vs_memory` by
       simp[valueEncodingDefsTheory.mem_bytes_at_def] >>
     simp[SUBSET_DEF] >>
     qx_genl_tac [`name`,`b`,`len`] >> disch_tac >>
     `local_region cenv ee.scopes t5 name b len` by simp[] >>
     conj_tac
     >- (qpat_assum `!p n. _ ==> mem_bytes_at p n t6.vs_memory = _` irule >>
         qpat_assum `!name b n. local_region cenv ee.scopes t5 name b n ==> regions_disjoint B 32 b n`
           (drule_then (mp_tac o REWRITE_RULE [regions_disjoint_def])) >>
         simp[DISJ_COMM]) >>
     rpt strip_tac >> fs[SUBSET_DEF]) >>
  `cenv.ce_is_ctor ==> !src tops name tv v off.
     ALOOKUP cenv.ce_modules src = SOME tops /\
     FLOOKUP (cenv with ce_module := src).ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
              | SOME imms => get_source_immutables src imms) name = SOME (tv,v) ==>
       regions_disjoint B 32 off (type_memory_size tv)` by
    (disch_tac >> rpt gen_tac >> strip_tac >>
     qpat_assum `immutable_frame_mods _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [immutable_frame_mods_def]) >>
     qpat_assum `immutable_alloca_sep_mods _ _ _ _ _`
       (drule_then assume_tac o REWRITE_RULE [immutable_alloca_sep_mods_def]) >>
     qpat_assum `immutable_alloca_sep _ _ _ _ _`
       (strip_assume_tac o SIMP_RULE (srw_ss()) [immutable_alloca_sep_def]) >>
     `regions_disjoint off (type_memory_size tv) B bsz` by
       (qpat_assum `cenv.ce_is_ctor ==> !name tv v off. _`
          (drule_then (qspecl_then [`name`,`tv`,`v`,`off`] mp_tac)) >>
        (impl_tac >- fs[]) >> disch_then (map_every assume_tac o CONJUNCTS) >>
        qpat_assum `!inst b sz. MEM inst (fn_insts func) /\ _ ==> regions_disjoint off _ b sz`
          irule >> qexists `binst` >> simp[]) >>
     fs[regions_disjoint_def] >> decide_tac) >>
  `immutable_frame_mods func cenv cx ee t6 /\ ghost_inv_at_mods (DF H) lo d cenv cx ee G6 tn6 t6` by
    (irule ecrecover_write_frame_mods >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`G5`,`B`,`32`,`ee`,`t5`,`s5`,`tn5`] >>
     conj_tac >- simp[] >>
     simp[SUBSET_DEF] >> conj_tac
     >- (qx_genl_tac [`a`,`n`] >> rewrite_tac[regions_disjoint_def] >>
         qpat_assum `!p n. _ ==> mem_bytes_at p n t6.vs_memory = _`
           (qspecl_then [`a`,`n`] mp_tac) >>
         simp[DISJ_COMM,ADD_COMM]) >>
     conj_tac
     >- (rpt strip_tac >> fs[SUBSET_DEF]) >>
     disch_tac >> rpt gen_tac >> strip_tac >>
     qpat_assum `cenv.ce_is_ctor ==> !src tops name tv v off. _`
       (drule_then (qspecl_then [`src`,`tops`,`name`,`tv`,`v`,`off`] mp_tac)) >> simp[]) >>
  simp[]
QED

Finalise concat_header_mods

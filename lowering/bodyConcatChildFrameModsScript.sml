(* The forced head may change source locals and storage, but both
   installed Concat allocations predate it and are separate from locals. *)
Theory bodyConcatChildFrameMods
Ancestors
  bodyConcatCutsMods bodyFullBuiltinConcatScratch tuplePlaceStep
  assignTuplePtrCopyLen bodyMemoryDefs exprLoweringProps freshWrites
  valueEncodingProps valueEncodingDefs venomState loweringPosts bodyPtrDefs
  exprSimFullBundleProps bodyFullPostsMods bodyFullShadowBodyInv

Theorem concat_child_window[local]:
  expr_post H ctx func cenv cx e es sa sc s ee v op t /\
  ghost_kept_at lo cenv es sa (G : string |-> num # num) tn s g ts /\
  FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ aid < sa.cs_next_id /\
  (!name lb lsz. local_region cenv es.scopes s name lb lsz ==>
     b+sz <= lb \/ lb+lsz <= b) /\
  off+n <= sz /\ (!i. b+off <= i /\ i < b+off+n ==> i NOTIN tn.t_mem) ==>
  FLOOKUP t.vs_allocas aid = SOME (b,sz) /\
  mem_bytes_at (b+off) n t.vs_memory = mem_bytes_at (b+off) n s.vs_memory /\
  (!i. b+off <= i /\ i < b+off+n ==> i NOTIN ts.t_mem)
Proof
  strip_tac >> drule_all concat_scratch_child_frame >> strip_tac >>
  simp[] >> conj_tac
  >- (qpat_assum `mem_bytes_at b sz _ = _`
        (mp_then Any mp_tac mem_bytes_at_translated_window) >>
      disch_then (qspecl_then [`off`,`n`] mp_tac) >> simp[]) >>
  rpt strip_tac >>
  `b <= i /\ i < b+sz /\ i < b+off+n` by decide_tac >> metis_tac[]
QED

Theorem concat_child_live[local]:
  concat_live_mods (func,cenv,lo) (dv,ov,ow,binst,oinst,B,bsz)
    (es,sa,s,G,tn) bs /\
  expr_post H ctx func cenv cx e es sa sc s ee v op t /\
  ghost_kept_at lo cenv es sa G tn s g ts /\
  (!name lb lsz. local_region cenv ee.scopes t name lb lsz <=>
                 local_region cenv es.scopes s name lb lsz) /\
  expr_sim_full_endpoint func sc s t /\ ~t.vs_halted /\
  allocas_from lo t /\ ci_mono sa sc ==>
  concat_live_mods (func,cenv,lo) (dv,ov,ow,binst,oinst,B,bsz)
    (ee,sc,t,g,ts) bs
Proof
  rewrite_tac[concat_live_mods_def,expr_sim_full_endpoint_def,ci_mono_def] >>
  strip_tac >>
  `FLOOKUP t.vs_allocas binst.inst_id = SOME (B,bsz) /\
   mem_bytes_at (B+32) (LENGTH bs) t.vs_memory = mem_bytes_at (B+32) (LENGTH bs) s.vs_memory /\
   (!i. B+32 <= i /\ i < B+32+LENGTH bs ==> i NOTIN ts.t_mem)` by
    (irule concat_child_window >>
     qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     qexistsl_tac [`tn`,`lo`,`g`,`G`] >> simp[] >> metis_tac[]) >>
  `FLOOKUP t.vs_allocas oinst.inst_id = SOME (w2n ow,64) /\
   mem_bytes_at (w2n ow) 32 t.vs_memory = mem_bytes_at (w2n ow) 32 s.vs_memory /\
   (!i. w2n ow <= i /\ i < w2n ow+32 ==> i NOTIN ts.t_mem)` by
    (irule (SIMP_RULE (srw_ss()) [] (Q.INST [`off` |-> `0`] concat_child_window)) >>
     qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     qexistsl_tac [`tn`,`lo`,`g`,`G`] >> simp[] >> metis_tac[]) >>
  `mload (w2n ow) t = mload (w2n ow) s` by
    fs[mload_def, GSYM mem_bytes_at_def] >>
  fs[expr_post_def,ghost_kept_at_def] >>
  `lookup_var dv t = SOME (n2w (B+32)) /\ lookup_var ov t = SOME ow` by simp[] >>
  `ptr_covers g ts dv t (bsz-32) /\ ptr_covers g ts ov t 32` by
    (conj_tac >> irule ptr_covers_lookup_frame >> qexistsl_tac [`G`,`s`,`tn`] >> simp[]) >>
  `not_fresh_at sc dv /\ not_fresh_at sc ov` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  simp[] >> first_assum ACCEPT_TAC
QED

Theorem concat_child_old_frame[local]:
  expr_post H ctx func cenv cx e es sa sc s ee v op t /\
  ghost_kept_at lo cenv es sa G tn s g ts /\
  (!name lb lsz. local_region cenv ee.scopes t name lb lsz <=>
                 local_region cenv es.scopes s name lb lsz) /\
  expr_sim_full_endpoint func sc s t /\ ci_mono sa sc /\
  (pure ==> ~expr_has_effect e) ==>
  concat_old_frame_mods (func,cenv,lo,pure) (dv,ov,ow,binst,oinst,B,bsz)
    (es,sa,s,G,tn) (ee,sc,t,g,ts)
Proof
  simp[concat_old_frame_mods_def,expr_post_def,expr_sim_full_endpoint_def,ci_mono_def] >>
  strip_tac >> simp[] >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by fs[locals_kept_def] >>
  simp[] >> conj_tac
  >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      qpat_assum `!aid p n. _ ==> mem_bytes_at p n _ = _` irule >>
      (conj_tac >- (simp[] >> first_assum ACCEPT_TAC)) >> qexists `aid` >> simp[]) >>
  strip_tac >> fs[pure_frame_def] >> conj_tac
  >- (rpt strip_tac >> qpat_assum `!n b sz. local_region _ _ _ _ _ _ ==> _` irule >>
      qexists `name` >> simp[]) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!off len. (!inst b sz. _ ==> regions_disjoint off len b sz) ==> _` irule >>
  first_assum ACCEPT_TAC
QED

Theorem concat_child_frame_mods:
  concat_live_mods (func,cenv,lo) (dv,ov,ow,binst,oinst,B,bsz)
    (es,sa,s,G,tn) bs /\
  stmt_state_rel H0 ctx func cenv cx es s /\
  concat_head_post_mods (DF,lo,d,ctx,func,cenv,cx) e (es,sa,s,G,tn) (op,sc)
    H (INL v) ee g ts t /\
  ci_mono sa sc /\ ~t.vs_halted /\ (pure ==> ~expr_has_effect e) /\
  local_ptrs_reserved cenv sa /\ return_buf_frame d cenv sa s /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) ==>
  concat_live_mods (func,cenv,lo) (dv,ov,ow,binst,oinst,B,bsz)
    (ee,sc,t,g,ts) bs /\
  concat_old_frame_mods (func,cenv,lo,pure) (dv,ov,ow,binst,oinst,B,bsz)
    (es,sa,s,G,tn) (ee,sc,t,g,ts) /\
  concat_horizon_mods (ctx,func,cenv,cx,lo,d) (H,DF H) (ee,sc,t,g,ts) /\
  local_ptrs_reserved cenv sc /\ return_buf_frame d cenv sc t /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sc z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sc z)
Proof
  rewrite_tac[concat_head_post_mods_def,expr_post_mods_def] >> simp[] >> strip_tac >>
  `!name lb lsz. local_region cenv ee.scopes t name lb lsz <=>
                 local_region cenv es.scopes s name lb lsz` by
    (irule tuple_place_endpoint_local_regions_some >>
     qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
     conj_tac >- fs[locals_kept_def] >>
     (conj_tac >- (qexists `sa` >> simp[] >> first_assum ACCEPT_TAC)) >>
     qexistsl_tac [`H0`,`ctx`,`cx`,`func`] >> simp[]) >>
  `allocas_from lo t` by fs[ghost_inv_at_mods_def] >>
  conj_tac
  >- metis_tac[concat_child_live] >>
  conj_tac
  >- metis_tac[concat_child_old_frame] >>
  fs[expr_post_def,concat_horizon_mods_def,ci_mono_def,expr_sim_full_endpoint_def] >>
  rpt conj_tac
  >- (irule local_ptrs_reserved_next_var >> qexists `sa` >> simp[])
  >- (irule return_buf_frame_frame >> metis_tac[]) >>
  rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> metis_tac[]
QED

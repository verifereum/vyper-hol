(* Assembly and transport of the anchored Concat loop certificates. *)
Theory bodyConcatFrameLawsMods
Ancestors
  bodyConcatCutsMods wordArgsPtr exprBopSimProps freshWrites valueEncodingProps
  exprSimWordArgs exprSimProps bodyFullPostsMods bodyFullShadowBodyInv
  exprSimHypsDefs exprLoweringProps bodyInvSplit
  loweringPosts bodyPtrDefs loweringStateRelDefs vyperStorageFootprint
  venomState vyperState list pair finite_map

Theorem concat_anchor_refl_mods[local]:
  concat_old_frame_mods (func,cenv,lo,pure) scratch
    (es,sa,s,G,tn) (es,sa,s,G,tn)
Proof
  PairCases_on `scratch` >> simp[concat_old_frame_mods_def,ghost_kept_at_refl]
QED

Theorem concat_anchor_start_mods:
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ alloca_history func s /\
  lookup_var dv s = SOME (n2w (B+32)) /\ lookup_var ov s = SOME ow /\
  not_fresh_at sa dv /\ not_fresh_at sa ov /\
  MEM binst (fn_insts func) /\ binst.inst_opcode = ALLOCA /\
  binst.inst_id < sa.cs_next_id /\ FLOOKUP s.vs_allocas binst.inst_id = SOME (B,bsz) /\
  MEM oinst (fn_insts func) /\ oinst.inst_opcode = ALLOCA /\
  oinst.inst_id < sa.cs_next_id /\ FLOOKUP s.vs_allocas oinst.inst_id = SOME (w2n ow,64) /\
  (!name lb lsz. local_region cenv es.scopes s name lb lsz ==>
    (B+bsz <= lb \/ lb+lsz <= B) /\ (w2n ow+64 <= lb \/ lb+lsz <= w2n ow)) /\
  (B+bsz <= w2n ow \/ w2n ow+64 <= B) /\
  B+bsz < dimword (:256) /\ w2n ow+64 < dimword (:256) /\
  B+bsz <= s.vs_alloca_next /\ w2n ow+64 <= s.vs_alloca_next /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ lo <= B /\ lo <= w2n ow /\
  ptr_covers G tn dv s (bsz-32) /\ ptr_covers G tn ov s 32 /\
  (!i. B+32 <= i /\ i < B+32+k ==> i NOTIN tn.t_mem) /\
  (!i. w2n ow <= i /\ i < w2n ow+32 ==> i NOTIN tn.t_mem) /\
  mload (w2n ow) s = n2w k /\ 32+k <= bsz ==>
  concat_live_mods (func,cenv,lo) (dv,ov,ow,binst,oinst,B,bsz)
    (es,sa,s,G,tn) (mem_bytes_at (B+32) k s.vs_memory) /\
  concat_old_frame_mods (func,cenv,lo,pure) (dv,ov,ow,binst,oinst,B,bsz)
    (es,sa,s,G,tn) (es,sa,s,G,tn)
Proof
  strip_tac >> simp[concat_anchor_refl_mods,concat_live_mods_def,LENGTH_mem_bytes_at] >>
  first_assum ACCEPT_TAC
QED

Theorem concat_horizon_gas_obs[local]:
  concat_horizon_mods (ctx,func,cenv,cx,lo,d) (H,D) (es with gas_obs := gs,sa,s,G,tn) <=>
  concat_horizon_mods (ctx,func,cenv,cx,lo,d) (H,D) (es,sa,s,G,tn)
Proof
  `storage_well_formed_on cx (es with gas_obs := gs) (FST H) <=>
   storage_well_formed_on cx es (FST H)` by
    (irule storage_well_formed_on_backends >> simp[]) >>
  simp[concat_horizon_mods_def,stmt_state_rel_gas_obs,
       immutable_frame_mods_def,immutables_rel_mods_def,immutable_alloca_sep_mods_def,
       immutable_alloca_sep_def,immutables_rel_def,ghost_inv_at_mods_def]
QED

Theorem concat_cut_gas_obs_mods:
  !ee s1 t g ts bs H gs.
  concat_live_mods (func,cenv,lo) scratch (ee,s1,t,g,ts) bs /\
  concat_old_frame_mods (func,cenv,lo,pure) scratch anchor (ee,s1,t,g,ts) /\
  concat_horizon_mods (ctx,func,cenv,cx,lo,d) (H,DF H) (ee,s1,t,g,ts) /\
  expr_sim_inv_mods mods cenv cx env ee ==>
  concat_live_mods (func,cenv,lo) scratch (ee with gas_obs := gs,s1,t,g,ts) bs /\
  concat_old_frame_mods (func,cenv,lo,pure) scratch anchor (ee with gas_obs := gs,s1,t,g,ts) /\
  concat_horizon_mods (ctx,func,cenv,cx,lo,d) (H,DF H) (ee with gas_obs := gs,s1,t,g,ts) /\
  expr_sim_inv_mods mods cenv cx env (ee with gas_obs := gs)
Proof
  PairCases_on `scratch` >> PairCases_on `anchor` >> rpt gen_tac >> strip_tac >>
  conj_tac
  >- (qpat_assum `concat_live_mods _ _ _ _` mp_tac >>
      pure_rewrite_tac[concat_live_mods_def,vyperStateTheory.evaluation_state_accfupds] >>
      disch_then ACCEPT_TAC) >>
  conj_tac
  >- (qpat_assum `concat_old_frame_mods _ _ _ _` mp_tac >>
      pure_rewrite_tac[concat_old_frame_mods_def,locals_kept_def,popped_kept_def,
                       vyperStateTheory.evaluation_state_accfupds] >>
      disch_then ACCEPT_TAC) >>
  conj_tac >- simp[concat_horizon_gas_obs] >>
  qpat_assum `expr_sim_inv_mods _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[expr_sim_inv_mods_def,
                   vyperTypeInvariantsTheory.gas_obs_type_invariants,
                   evaluation_state_accfupds] >> disch_then ACCEPT_TAC
QED

Theorem concat_old_frame_compose_mods:
  concat_old_frame_mods (func,cenv,lo,pure) scratch
    (es,sa,s,G,tn) (ee,sb,t,G1,tn1) /\
  concat_old_frame_mods (func,cenv,lo,pure) scratch
    (ee,sb,t,G1,tn1) (ef,sc,u,G2,tn2) /\
  local_ptrs_reserved cenv sa ==>
  concat_old_frame_mods (func,cenv,lo,pure) scratch
    (es,sa,s,G,tn) (ef,sc,u,G2,tn2)
Proof
  PairCases_on `scratch` >> pure_rewrite_tac[concat_old_frame_mods_def] >> strip_tac >>
  conj_tac >- (irule arithmeticTheory.LESS_EQ_TRANS >> qexists `sb.cs_next_var` >> simp[]) >>
  conj_tac >- (irule arithmeticTheory.LESS_EQ_TRANS >> qexists `sb.cs_next_id` >> simp[]) >>
  conj_tac >- (irule arithmeticTheory.LESS_EQ_TRANS >> qexists `t.vs_alloca_next` >> simp[]) >>
  conj_tac >- (drule_all wordArgsPtrTheory.ghost_kept_at_trans >> simp[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sb z` by (irule freshWritesTheory.not_fresh_at_mono >> qexists `sa` >> simp[]) >>
      simp[]) >>
  conj_tac >- simp[] >>
  conj_tac
  >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      `aid < sb.cs_next_id` by decide_tac >>
      `FLOOKUP t.vs_allocas aid = SOME (p,n)` by simp[] >>
      `mem_bytes_at p n t.vs_memory = mem_bytes_at p n s.vs_memory` by
        (qpat_assum `!aid p n. _ ==> mem_bytes_at p n t.vs_memory = _`
          (qspecl_then [`aid`,`p`,`n`] MATCH_MP_TAC) >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
      `mem_bytes_at p n u.vs_memory = mem_bytes_at p n t.vs_memory` by
        (qpat_assum `!aid p n. _ ==> mem_bytes_at p n u.vs_memory = _`
          (qspecl_then [`aid`,`p`,`n`] MATCH_MP_TAC) >>
         asm_simp_tac bool_ss [] >> first_assum ACCEPT_TAC) >>
      asm_rewrite_tac[]) >>
  conj_tac
  >- (irule exprBopSimPropsTheory.locals_kept_trans >> qexistsl [`ee`,`sa`,`t`] >> simp[] >> first_assum ACCEPT_TAC) >>
  strip_tac >> conj_tac
  >- (rpt strip_tac >> metis_tac[]) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `pure ==> _ /\ !p n. _ ==> mem_bytes_at p n t.vs_memory = _`
    (drule_then (assume_tac o CONJUNCT2)) >>
  qpat_assum `pure ==> _ /\ !p n. _ ==> mem_bytes_at p n u.vs_memory = _`
    (drule_then (assume_tac o CONJUNCT2)) >>
  `mem_bytes_at p n t.vs_memory = mem_bytes_at p n s.vs_memory` by
    (qpat_assum `!p n. _ ==> mem_bytes_at p n t.vs_memory = _`
       (qspecl_then [`p`,`n`] MATCH_MP_TAC) >>
     asm_simp_tac bool_ss [] >>
     rpt strip_tac >>
     qpat_assum `!inst b sz. _ ==> regions_disjoint p n b sz`
       (qspecl_then [`inst`,`b`,`sz`] MATCH_MP_TAC) >> simp[]) >>
  `mem_bytes_at p n u.vs_memory = mem_bytes_at p n t.vs_memory` by
    (qpat_assum `!p n. _ ==> mem_bytes_at p n u.vs_memory = _`
       (qspecl_then [`p`,`n`] MATCH_MP_TAC) >>
     asm_simp_tac bool_ss [] >>
     rpt strip_tac >>
     qpat_assum `!inst b sz. _ ==> regions_disjoint p n b sz`
       (qspecl_then [`inst`,`b`,`sz`] MATCH_MP_TAC) >> simp[] >> decide_tac) >>
  asm_rewrite_tac[]
QED

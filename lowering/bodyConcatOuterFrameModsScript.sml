(* The parent Concat frame crosses the zero store, the operand fold,
   and the final length store.  Only the middle interval can change source state. *)
Theory bodyConcatOuterFrameMods
Ancestors
  bodyConcatCutsMods exprSimConcatResult exprSimProps exprBopSimProps
  wordArgsPtr bodyFullUnwrapRun freshWrites loweringPosts loweringStateRelDefs
  arithmetic finite_map pred_set words

Theorem concat_outer_bytes[local]:
  32 <= bsz /\
  (!p n. regions_disjoint p n off 32 ==>
         mem_bytes_at p n t4.vs_memory = mem_bytes_at p n s0.vs_memory) /\
  (!p n. regions_disjoint p n B 32 ==>
         mem_bytes_at p n t6.vs_memory = mem_bytes_at p n t5.vs_memory) /\
  regions_disjoint p n B bsz /\ regions_disjoint p n off 64 ==>
  mem_bytes_at p n t6.vs_memory = mem_bytes_at p n t5.vs_memory /\
  mem_bytes_at p n t4.vs_memory = mem_bytes_at p n s0.vs_memory
Proof
  strip_tac >>
  `regions_disjoint p n B 32 /\ regions_disjoint p n off 32` by
    (fs[regions_disjoint_def] >> decide_tac) >>
  simp[]
QED

Theorem concat_outer_frame_mods:
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv s5 /\
  sa.cs_next_var <= s4.cs_next_var /\ sa.cs_next_id <= s4.cs_next_id /\
  s0.vs_alloca_next <= t4.vs_alloca_next /\ B+bsz <= t4.vs_alloca_next /\
  32 <= bsz /\
  (!z. not_fresh_at sa z ==> lookup_var z t4 = lookup_var z s0) /\
  (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==> FLOOKUP t4.vs_allocas aid = SOME a) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G4 tn4 /\
  (!aid p n. FLOOKUP s0.vs_allocas aid = SOME (p,n) /\ aid < sa.cs_next_id ==>
     regions_disjoint p n B bsz /\ regions_disjoint p n (w2n ow) 64) /\
  (!name b n. local_region cenv es.scopes s0 name b n ==>
     regions_disjoint b n B bsz /\ regions_disjoint b n (w2n ow) 64) /\
  (!p n. regions_disjoint p n (w2n ow) 32 ==>
         mem_bytes_at p n t4.vs_memory = mem_bytes_at p n s0.vs_memory) /\
  MEM binst (fn_insts func) /\ binst.inst_opcode = ALLOCA /\
  sa.cs_next_id <= binst.inst_id /\ FLOOKUP t4.vs_allocas binst.inst_id = SOME (B,bsz) /\
  MEM oinst (fn_insts func) /\ oinst.inst_opcode = ALLOCA /\
  sa.cs_next_id <= oinst.inst_id /\ FLOOKUP t4.vs_allocas oinst.inst_id = SOME (w2n ow,64) /\
  concat_old_frame_mods (func,cenv,lo,pure) (dv,ov,ow,binst,oinst,B,bsz)
     (es,s4,t4,G4,tn4) (ee,s5,t5,G5,tn5) /\
  (!z. not_fresh_at s5 z ==>
     lookup_var z t6 = lookup_var z t5 /\ FLOOKUP G6 z = FLOOKUP G5 z /\
     op_taint tn6 (Var z) = op_taint tn5 (Var z)) /\
  t6.vs_allocas = t5.vs_allocas /\ t6.vs_alloca_next = t5.vs_alloca_next /\
  tn6.t_mem SUBSET tn5.t_mem /\
  (!p n. regions_disjoint p n B 32 ==>
         mem_bytes_at p n t6.vs_memory = mem_bytes_at p n t5.vs_memory) ==>
  wb_frame cenv es ee sa s0 t6 /\
  (pure ==> pure_frame cenv func es sa s0 t6) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G6 tn6 /\
  (!name b n. local_region cenv ee.scopes t6 name b n <=>
             local_region cenv es.scopes s0 name b n) /\
  (!name b n. local_region cenv ee.scopes t6 name b n ==>
     regions_disjoint b n B bsz /\ regions_disjoint b n (w2n ow) 64) /\
  s0.vs_alloca_next <= t6.vs_alloca_next /\ B+bsz <= t6.vs_alloca_next
Proof
  pure_rewrite_tac[concat_old_frame_mods_def] >> strip_tac >>
  `!z. not_fresh_at sa z ==> not_fresh_at s4 z /\ not_fresh_at s5 z` by
    (rpt strip_tac >> irule not_fresh_at_mono >>
     qexists `sa` >> simp[] >> decide_tac) >>
  `!name b n. local_region cenv es.scopes t4 name b n <=>
              local_region cenv es.scopes s0 name b n` by
    (rpt gen_tac >> irule concat_local_region_vars >> qexists `sa` >> simp[]) >>
  `!name b n. local_region cenv ee.scopes t6 name b n <=>
              local_region cenv ee.scopes t5 name b n` by
    (rpt gen_tac >> irule concat_local_region_vars >> qexists `s5` >> simp[]) >>
  `!p n. regions_disjoint p n B bsz /\ regions_disjoint p n (w2n ow) 64 ==>
     mem_bytes_at p n t6.vs_memory = mem_bytes_at p n t5.vs_memory /\
     mem_bytes_at p n t4.vs_memory = mem_bytes_at p n s0.vs_memory` by
    (rpt gen_tac >> strip_tac >> irule concat_outer_bytes >>
     conj_tac >- (qexistsl [`B`,`bsz`] >> simp[]) >>
     qexists `w2n ow` >> simp[]) >>
  conj_tac >- suspend "wb" >>
  conj_tac >- suspend "pure" >>
  conj_tac >- suspend "ghost" >>
  conj_tac >- simp[] >>
  conj_tac
  >- (simp[] >>
      qpat_assum `!name b n. local_region cenv es.scopes s0 name b n ==> _` ACCEPT_TAC) >>
  simp[] >> decide_tac
QED

Resume concat_outer_frame_mods[wb]:
  rewrite_tac[wb_frame_def] >>
  conj_tac >- suspend "wb_var" >>
  conj_tac >- suspend "wb_alloc" >>
  conj_tac >- suspend "wb_mem" >>
  suspend "wb_locals"
QED

Resume concat_outer_frame_mods[wb_var]:
  qx_genl_tac [`z`,`w`] >> strip_tac >>
  `lookup_var z t4 = SOME w` by simp[] >>
  `lookup_var z t5 = SOME w` by simp[] >>
  simp[]
QED

Resume concat_outer_frame_mods[wb_alloc]:
  qx_genl_tac [`aid`,`a`] >> disch_tac >>
  `FLOOKUP t4.vs_allocas aid = SOME a` by simp[] >>
  simp[]
QED

Resume concat_outer_frame_mods[wb_mem]:
  qx_genl_tac [`aid`,`p`,`n`] >> strip_tac >>
  `FLOOKUP t4.vs_allocas aid = SOME (p,n)` by simp[] >>
  `aid < s4.cs_next_id` by decide_tac >>
  qpat_assum `!aid p n. _ ==> regions_disjoint p n B bsz /\ _`
    (qspecl_then [`aid`,`p`,`n`] mp_tac) >> simp[] >> strip_tac >>
  `mem_bytes_at p n t6.vs_memory = mem_bytes_at p n t5.vs_memory /\
   mem_bytes_at p n t4.vs_memory = mem_bytes_at p n s0.vs_memory` by simp[] >>
  `mem_bytes_at p n t5.vs_memory = mem_bytes_at p n t4.vs_memory` by
    (qpat_assum `!aid p n. _ ==> mem_bytes_at p n t5.vs_memory = _`
       (qspecl_then [`aid`,`p`,`n`] MATCH_MP_TAC) >>
     asm_simp_tac bool_ss [GSYM regions_disjoint_def] >>
     rewrite_tac[regions_disjoint_def] >> first_assum ACCEPT_TAC) >>
  simp[]
QED

Resume concat_outer_frame_mods[wb_locals]:
  `locals_kept cenv es es s0 t4` by
    (irule locals_kept_regions >> qx_genl_tac [`name`,`b`,`n`] >> disch_tac >>
     qpat_assum `!name b n. local_region cenv es.scopes s0 name b n ==> _`
       (qspecl_then [`name`,`b`,`n`] mp_tac) >> simp[]) >>
  `locals_kept cenv es ee s0 t5` by
    (irule locals_kept_trans >> qexistsl [`es`,`sa`,`t4`] >> simp[]) >>
  irule locals_kept_regions_tail >> qexists `t5` >> simp[] >>
  qx_genl_tac [`name`,`b`,`n`] >> disch_tac >>
  qpat_assum `!name b n. local_region cenv es.scopes s0 name b n ==> _`
    (qspecl_then [`name`,`b`,`n`] mp_tac) >> simp[]
QED

Resume concat_outer_frame_mods[pure]:
  disch_tac >> rewrite_tac[pure_frame_def] >>
  conj_tac >- suspend "pure_locals" >> suspend "pure_global"
QED

Resume concat_outer_frame_mods[pure_locals]:
  qx_genl_tac [`name`,`b`,`n`] >> disch_tac >>
  `local_region cenv es.scopes t4 name b n` by simp[] >>
  qpat_assum `!name b n. local_region cenv es.scopes s0 name b n ==> _`
    (qspecl_then [`name`,`b`,`n`] mp_tac) >> simp[] >> strip_tac >>
  `mem_bytes_at b n t5.vs_memory = mem_bytes_at b n t4.vs_memory` by
    (qpat_assum `pure ==> _ /\ _` (drule_then strip_assume_tac) >>
     qpat_assum `!name b n. local_region cenv es.scopes t4 name b n ==> _`
       (qspecl_then [`name`,`b`,`n`] mp_tac) >> simp[]) >>
  simp[]
QED

Resume concat_outer_frame_mods[pure_global]:
  qx_genl_tac [`p`,`n`] >> disch_tac >>
  `FLOOKUP t5.vs_allocas binst.inst_id = SOME (B,bsz) /\
   FLOOKUP t5.vs_allocas oinst.inst_id = SOME (w2n ow,64)` by simp[] >>
  `regions_disjoint p n B bsz` by
    (qpat_assum `!inst b sz. _ ==> regions_disjoint p n b sz`
       (qspecl_then [`binst`,`B`,`bsz`] mp_tac) >> simp[]) >>
  `regions_disjoint p n (w2n ow) 64` by
    (qpat_assum `!inst b sz. _ ==> regions_disjoint p n b sz`
       (qspecl_then [`oinst`,`w2n ow`,`64`] mp_tac) >> simp[]) >>
  `mem_bytes_at p n t6.vs_memory = mem_bytes_at p n t5.vs_memory /\
   mem_bytes_at p n t4.vs_memory = mem_bytes_at p n s0.vs_memory` by simp[] >>
  `mem_bytes_at p n t5.vs_memory = mem_bytes_at p n t4.vs_memory` by
    (qpat_assum `pure ==> _ /\ _` (drule_then strip_assume_tac) >>
     qpat_assum `!p n. _ /\ _ /\ (!inst b sz. _ ==> _) ==> mem_bytes_at p n t5.vs_memory = _`
       (qspecl_then [`p`,`n`] MATCH_MP_TAC) >>
     conj_tac >- fs[regions_disjoint_def] >>
     conj_tac >- fs[regions_disjoint_def] >>
     qx_genl_tac [`inst`,`b`,`sz`] >> strip_tac >>
     qpat_assum `!inst b sz. _ ==> regions_disjoint p n b sz`
       (qspecl_then [`inst`,`b`,`sz`] MATCH_MP_TAC) >> simp[] >> decide_tac) >>
  simp[]
QED

Resume concat_outer_frame_mods[ghost]:
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G5 tn5` by
    (drule_all ghost_kept_at_trans >> simp[]) >>
  irule ghost_kept_at_clean_suffix >> qexistsl [`G5`,`tn5`] >>
  simp[]
QED

Finalise concat_outer_frame_mods

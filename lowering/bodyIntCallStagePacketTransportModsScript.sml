Theory bodyIntCallStagePacketTransportMods
Ancestors
  bodyIntCallStagePacketMods bodyPtrBytestringBuiltinsWindowGhost
  valueEncodingProps loweringShapeDefs
  venomState ptrDiscipline list arithmetic

(* A protected row suffices for a robust read of any footprint within it. *)
Theorem stage_row_robust_transport[local]:
  mem_bytes_at b k mem' = mem_bytes_at b k mem /\
  (!i. b <= i /\ i < b+k /\ i IN dirty' ==> i IN dirty) /\
  (!m. mem_agree_outside dirty mem m ==> val_in_memory tv v a m) /\
  val_wf tv v /\ b <= a /\ a + val_footprint tv v <= b+k ==>
  !m. mem_agree_outside dirty' mem' m ==> val_in_memory tv v a m
Proof
  strip_tac >>
  `b + (a-b) = a /\ (a-b) + val_footprint tv v <= k` by decide_tac >>
  `mem_bytes_at a (val_footprint tv v) mem' =
   mem_bytes_at a (val_footprint tv v) mem` by
    (drule mem_bytes_at_translated_window >>
     disch_then (qspecl_then [`a-b`,`val_footprint tv v`] mp_tac) >> simp[]) >>
  `!i. a <= i /\ i < a + val_footprint tv v /\ i IN dirty' ==> i IN dirty` by
    (rpt strip_tac >> first_x_assum irule >> simp[] >> decide_tac) >>
  rpt strip_tac >> irule robust_val_in_memory_window_transport >> simp[] >>
  qexistsl_tac [`dirty`,`dirty'`,`val_footprint tv v`,`mem`,`mem'`] >> simp[]
QED

Theorem stage_eval_operands_transport[local]:
  !ops ws. eval_operands ops s = SOME ws /\
    (!op w. MEM op ops /\ eval_operand op s = SOME w ==>
       eval_operand op t = SOME w) ==>
    eval_operands ops t = SOME ws
Proof
  Induct >> simp[eval_operands_def] >> rpt gen_tac >>
  Cases_on `eval_operand h s` >> simp[] >>
  Cases_on `eval_operands ops s` >> simp[] >> strip_tac >>
  `eval_operand h t = SOME x` by metis_tac[] >>
  `eval_operands ops t = SOME x'` by metis_tac[] >> simp[]
QED

Theorem intcall_stage_ops_transport_mods:
  intcall_stage_ops_mods (lo,func) cenv cx sa (si,esi,s,G,tn) pin
    (ops,ws,vals,ptys,pflags) /\
  si.cs_next_var <= sj.cs_next_var /\ si.cs_next_id <= sj.cs_next_id /\
  s.vs_alloca_next <= t.vs_alloca_next /\ t.vs_labels = s.vs_labels /\
  (!x w. not_fresh_at si x /\ lookup_var x s = SOME w ==>
     lookup_var x t = SOME w) /\
  (!x. not_fresh_at si x ==>
     FLOOKUP Gj x = FLOOKUP G x /\ op_taint tj (Var x) = op_taint tn (Var x)) /\
  (!aid row. FLOOKUP s.vs_allocas aid = SOME row ==>
     FLOOKUP t.vs_allocas aid = SOME row) /\
  (!n lb sz. local_region cenv esj.scopes t n lb sz ==>
     local_region cenv esi.scopes s n lb sz) /\
  (!aid b k. FLOOKUP s.vs_allocas aid = SOME (b,k) /\ aid < si.cs_next_id /\
     (!n lb sz. local_region cenv esi.scopes s n lb sz ==>
        b+k <= lb \/ lb+sz <= b) ==>
     mem_bytes_at b k t.vs_memory = mem_bytes_at b k s.vs_memory /\
     (!i. b <= i /\ i < b+k /\ i IN tj.t_mem ==> i IN tn.t_mem)) ==>
  intcall_stage_ops_mods (lo,func) cenv cx sa (sj,esj,t,Gj,tj) pin
    (ops,ws,vals,ptys,pflags)
Proof
  rewrite_tac[intcall_stage_ops_mods_def] >> strip_tac >>
  `eval_operands ops t = SOME ws` by
    (irule stage_eval_operands_transport >> qexists `s` >> simp[] >>
     rpt strip_tac >> Cases_on `op` >> gvs[eval_operand_def] >>
     first_x_assum irule >> simp[]) >>
  `!op. MEM op ops ==>
       op_prov Gj op = op_prov G op /\ op_taint tj op = op_taint tn op` by
    (rpt strip_tac >> Cases_on `op` >>
     fs[op_prov_def,op_taint_def] >> metis_tac[]) >>
  `!j. j < LENGTH ops ==> op_prov Gj (EL j ops) = op_prov G (EL j ops)` by
    simp[EL_MEM] >>
  simp[] >> conj_tac
  >- (fs[EVERY_MEM] >> metis_tac[]) >>
  conj_tac >- metis_tac[not_fresh_at_mono] >>
  conj_tac
  >- (qx_gen_tac `j` >> strip_tac >>
      qpat_x_assum `!j. _ /\ ~EL j pflags ==> _`
        (qspec_then `j` mp_tac) >> simp[] >> strip_tac >>
      qexistsl_tac [`b`,`cap`,`aid`] >> simp[] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
  conj_tac
  >- (rpt strip_tac >> `i < LENGTH ops` by decide_tac >> metis_tac[]) >>
  map_every qx_gen_tac [`j`,`rt`] >> strip_tac >>
  qpat_x_assum `!j rt. _` (qspecl_then [`j`,`rt`] mp_tac) >>
  simp[] >> strip_tac >> simp[] >> strip_tac >>
  qpat_x_assum `~EL j pflags ==> _` (drule_then strip_assume_tac) >>
  qexistsl_tac [`b`,`cap`,`aid`] >> simp[] >>
  `mem_bytes_at b cap t.vs_memory = mem_bytes_at b cap s.vs_memory /\
   (!i. b <= i /\ i < b+cap /\ i IN tj.t_mem ==> i IN tn.t_mem)` by
    (first_x_assum irule >> metis_tac[]) >>
  conj_tac
  >- (`w2n (EL j ws) + val_footprint rt (EL j vals) <= b+cap` by decide_tac >>
      drule stage_row_robust_transport >> disch_then drule >>
      disch_then drule >> simp[])
  >> rpt strip_tac >>
  `local_region cenv esi.scopes s n lb sz` by simp[] >>
  first_x_assum irule >> qexists `n` >> simp[]
QED

(* Only the result pin is transported here; the linked frame has its own rule. *)
Theorem intcall_stage_pin_transport_mods:
  (case pin of NONE => T | SOME (rb,b,k) =>
     FLOOKUP G rb = SOME (b,k) /\ op_taint tn (Var rb) = {} /\
     lookup_var rb s = SOME (n2w b) /\
     FLOOKUP s.vs_allocas sa.cs_next_id = SOME (b,k) /\
     sa.cs_next_id < si.cs_next_id /\ lo <= b /\ b+k <= s.vs_alloca_next /\
     not_fresh_at si rb /\
     (!n lb sz. local_region cenv esi.scopes s n lb sz ==>
        b+k <= lb \/ lb+sz <= b)) /\
  si.cs_next_var <= sj.cs_next_var /\ si.cs_next_id <= sj.cs_next_id /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  (!x w. not_fresh_at si x /\ lookup_var x s = SOME w ==>
     lookup_var x t = SOME w) /\
  (!x. not_fresh_at si x ==>
     FLOOKUP Gj x = FLOOKUP G x /\ op_taint tj (Var x) = op_taint tn (Var x)) /\
  (!aid row. FLOOKUP s.vs_allocas aid = SOME row ==>
     FLOOKUP t.vs_allocas aid = SOME row) /\
  (!n lb sz. local_region cenv esj.scopes t n lb sz ==>
     local_region cenv esi.scopes s n lb sz) ==>
  (case pin of NONE => T | SOME (rb,b,k) =>
     FLOOKUP Gj rb = SOME (b,k) /\ op_taint tj (Var rb) = {} /\
     lookup_var rb t = SOME (n2w b) /\
     FLOOKUP t.vs_allocas sa.cs_next_id = SOME (b,k) /\
     sa.cs_next_id < sj.cs_next_id /\ lo <= b /\ b+k <= t.vs_alloca_next /\
     not_fresh_at sj rb /\
     (!n lb sz. local_region cenv esj.scopes t n lb sz ==>
        b+k <= lb \/ lb+sz <= b))
Proof
  Cases_on `pin` >> simp[] >> PairCases_on `x` >> simp[] >> strip_tac >>
  simp[] >> conj_tac
  >- (irule not_fresh_at_mono >> qexists `si` >> simp[]) >>
  rpt strip_tac >>
  `local_region cenv esi.scopes s n lb sz` by simp[] >>
  first_x_assum irule >> qexists `n` >> simp[]
QED

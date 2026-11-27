(* Transport the prefix over the formal's bounded store. *)
Theory bodyIntCallBufferHeadStoreFrameCutMods
Ancestors
  bodyIntCallBufferStoreFrameMods bodyIntCallStagePacketTransportMods
  bodyIntCallStagePacketMods typedMemoryCopy loweringStateRelDefs
  venomMemDefs venomInst venomState ptrDiscipline compileEnv finite_map list words

val _ = Parse.hide "base";

Theorem store_cut_static[local]:
  typed_copy_state_frame cu base nw z t ==>
  t.vs_allocas = z.vs_allocas /\ t.vs_alloca_next = z.vs_alloca_next /\
  t.vs_labels = z.vs_labels /\
  (!p. not_fresh_at cu p ==> lookup_var p t = lookup_var p z)
Proof
  simp[typed_copy_state_frame_def, Once venom_state_component_equality]
QED

Theorem store_cut_local_regions[local]:
  local_ptrs_reserved cenv cu /\
  (!p. not_fresh_at cu p ==> lookup_var p t = lookup_var p z) ==>
  !n b k. local_region cenv mid.scopes t n b k <=> local_region cenv mid.scopes z n b k
Proof
  strip_tac >> rpt gen_tac >> irule local_region_lookup_cong >>
  rpt strip_tac >> first_assum irule >> fs[local_ptrs_reserved_def] >> metis_tac[]
QED

Theorem store_cut_old_rows[local]:
  intcall_stage_ops_mods (lo,func) cenv cx sa (si,esi,s,Gi,ti)
    (pin : (string # num # num) option)
    (ops,ws,vals,ptys,pflags) /\
  (!j. j < LENGTH ops /\ ~EL j pflags ==> op_prov Gz (EL j ops) = op_prov Gi (EL j ops)) /\
  (!aid row. FLOOKUP s.vs_allocas aid = SOME row ==> FLOOKUP z.vs_allocas aid = SOME row) /\
  si.cs_next_id <= ci.cs_next_id ==>
  !j b k. j < LENGTH ops /\ ~EL j pflags /\ op_prov Gz (EL j ops) = SOME (b,k) ==>
    ?aid. FLOOKUP z.vs_allocas aid = SOME (b,k) /\
          sa.cs_next_id <= aid /\ aid < ci.cs_next_id /\
          ?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = aid
Proof
  rewrite_tac[intcall_stage_ops_mods_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_assum `!j. j < LENGTH ops /\ ~EL j pflags ==> ?b cap aid. _`
    (drule_all_then strip_assume_tac) >>
  qpat_assum `!j. _ ==> op_prov Gz _ = op_prov Gi _`
    (drule_all_then assume_tac) >>
  gvs[] >> qexists_tac `inst.inst_id` >>
  `inst.inst_id < ci.cs_next_id` by decide_tac >> simp[] >>
  qexists_tac `inst` >> simp[]
QED

(* Only this proof-local view lowers the id bound. The final packet is
   certified at the actual post-store cursor. *)
Theorem store_cut_restrict_ids[local]:
  intcall_stage_ops_mods (lo,func) cenv cx sa (cu,mid,z,Gz,tz) pin
    (ops,ws,vals,ptys,pflags) /\
  (!j b k. j < LENGTH ops /\ ~EL j pflags /\ op_prov Gz (EL j ops) = SOME (b,k) ==>
    ?aid. FLOOKUP z.vs_allocas aid = SOME (b,k) /\
          sa.cs_next_id <= aid /\ aid < ci.cs_next_id /\
          ?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = aid) ==>
  intcall_stage_ops_mods (lo,func) cenv cx sa (cu with cs_next_id := ci.cs_next_id,mid,z,Gz,tz)
    pin (ops,ws,vals,ptys,pflags)
Proof
  simp_tac (srw_ss()) [intcall_stage_ops_mods_def,not_fresh_at_def] >> strip_tac >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!j. j < LENGTH ops /\ ~EL j pflags ==> _`
        (drule_all_then strip_assume_tac) >>
      qpat_assum `!j b k. _ ==> ?aid. _` (drule_all_then strip_assume_tac) >>
      qexistsl_tac [`b`,`cap`,`aid'`] >> simp[] >> metis_tac[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!j rt. _ ==> _` (drule_all_then strip_assume_tac) >> simp[] >>
  strip_tac >> qpat_assum `~EL j pflags ==> _` (drule_then strip_assume_tac) >>
  qpat_assum `!j b k. _ ==> ?aid. _` (drule_all_then strip_assume_tac) >>
  qexistsl_tac [`b`,`cap`,`aid'`] >> simp[] >> first_assum ACCEPT_TAC
QED

Theorem store_cut_disjoint[local]:
  alloca_inv z /\ FLOOKUP z.vs_allocas site = SOME (base,cap) ==>
  !aid b k. aid < site /\ FLOOKUP z.vs_allocas aid = SOME (b,k) ==>
    b+k <= base \/ base+cap <= b
Proof
  rw[alloca_inv_def,allocas_non_overlapping_def] >>
  `aid <> site` by decide_tac >> metis_tac[]
QED

Theorem intcall_buffer_head_store_frame_cut_mods:
  intcall_stage_ops_mods (lo,func) cenv cx sa (si,esi,s,Gi,ti) pin
    (ops,ws,vals,ptys,pflags) /\
  intcall_stage_ops_mods (lo,func) cenv cx sa (cu,mid,z,Gz,tz) pin
    (ops,ws,vals,ptys,pflags) /\
  intcall_stage_frame_mods (DF,lo,d,ctx,func) cenv cx st0
    (sa,es0,s0,G0,tn0) (cu,mid,z,Gz,tz) pin /\
  (!j. j < LENGTH ops /\ ~EL j pflags ==> op_prov Gz (EL j ops) = op_prov Gi (EL j ops)) /\
  (!aid row. FLOOKUP s.vs_allocas aid = SOME row ==> FLOOKUP z.vs_allocas aid = SOME row) /\
  si.cs_next_id <= ci.cs_next_id /\ sa.cs_next_id <= ci.cs_next_id /\
  ci.cs_next_id < cu.cs_next_id /\
  (case pin of NONE => T | SOME (rb,pb,pk) => sa.cs_next_id < ci.cs_next_id) /\
  MEM (mk_inst ci.cs_next_id ALLOCA [Lit (n2w cap)] [dst]) (fn_insts func) /\
  FLOOKUP z.vs_allocas ci.cs_next_id = SOME (base,cap) /\ alloca_inv z /\ lo <= base /\
  (!n lb sz. local_region cenv mid.scopes z n lb sz ==> lb+sz <= base \/ base+cap <= lb) /\
  not_fresh_at cu dst /\ lookup_var dst z = SOME (n2w base) /\
  FLOOKUP Gz dst = SOME (base,cap) /\ op_taint tz (Var dst) = {} /\
  local_ptrs_reserved cenv cu /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at cu x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cu x) /\
  typed_copy_state_frame cu base nw z t /\ nw <= cap /\
  (!x. not_fresh_at cu x ==> FLOOKUP Gf x = FLOOKUP Gz x /\
       op_taint tf (Var x) = op_taint tz (Var x)) /\
  (!i. ~(base <= i /\ i < base+nw) ==> (i IN tf.t_mem <=> i IN tz.t_mem)) /\
  tf.t_stor = tz.t_stor /\ tf.t_trans = tz.t_trans /\ tf.t_imm = tz.t_imm /\
  cu.cs_next_id <= cs.cs_next_id /\ cu.cs_next_var <= cs.cs_next_var /\
  alloca_history func t /\ t.vs_current_bb = cs.cs_current_bb /\
  t.vs_inst_idx = LENGTH cs.cs_current_insts ==>
  intcall_stage_frame_mods (DF,lo,d,ctx,func) cenv cx st0
    (sa,es0,s0,G0,tn0) (cs,mid,t,Gf,tf) pin /\
  intcall_stage_ops_mods (lo,func) cenv cx sa (cs,mid,t,Gf,tf) pin
    (ops,ws,vals,ptys,pflags) /\
  lookup_var dst t = SOME (n2w base) /\ FLOOKUP Gf dst = SOME (base,cap) /\
  op_taint tf (Var dst) = {} /\ not_fresh_at cs dst /\
  FLOOKUP t.vs_allocas ci.cs_next_id = SOME (base,cap) /\ ci.cs_next_id < cs.cs_next_id /\
  base+cap <= t.vs_alloca_next /\
  (!n lb sz. local_region cenv mid.scopes t n lb sz ==> lb+sz <= base \/ base+cap <= lb) /\
  (!j b k. j < LENGTH ops /\ ~EL j pflags /\ op_prov Gf (EL j ops) = SOME (b,k) ==>
    loweringStateRelDefs$regions_disjoint b k base cap) /\
  (case pin of NONE => T | SOME (rb,pb,pk) => base+cap <= pb \/ pb+pk <= base)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then strip_assume_tac store_cut_static >>
  `!n b k. local_region cenv mid.scopes t n b k <=> local_region cenv mid.scopes z n b k` by
    (irule store_cut_local_regions >> qexists_tac `cu` >> simp[]) >>
  qhdtm_assum `intcall_stage_frame_mods`
    (strip_assume_tac o REWRITE_RULE [intcall_stage_frame_mods_def]) >>
  `case pin of NONE => T | SOME (rb,b,k) =>
    FLOOKUP Gf rb = SOME (b,k) /\ op_taint tf (Var rb) = {} /\
    lookup_var rb t = SOME (n2w b) /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (b,k) /\
    sa.cs_next_id < cs.cs_next_id /\ lo <= b /\ b+k <= t.vs_alloca_next /\
    not_fresh_at cs rb /\ (!n lb sz. local_region cenv mid.scopes t n lb sz ==>
      b+k <= lb \/ lb+sz <= b)` by suspend "pin" >>
  drule_all_then strip_assume_tac intcall_buffer_store_frame_mods >>
  mp_tac (Q.INST [`z` |-> `z`, `ci` |-> `ci`, `Gz` |-> `Gz`, `Gi` |-> `Gi`]
    store_cut_old_rows) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_tac >>
  `!aid b k. aid < ci.cs_next_id /\ FLOOKUP z.vs_allocas aid = SOME (b,k) ==>
     b+k <= base \/ base+cap <= b` by (match_mp_tac store_cut_disjoint >> simp[]) >>
  `intcall_stage_ops_mods (lo,func) cenv cx sa (cs,mid,t,Gf,tf) pin
    (ops,ws,vals,ptys,pflags)` by suspend "packet" >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >> suspend "finished"
QED

Resume intcall_buffer_head_store_frame_cut_mods[pin]:
  irule intcall_stage_pin_transport_mods >>
  qexistsl_tac [`Gz`,`mid`,`z`,`cu`,`tz`] >> simp[] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume intcall_buffer_head_store_frame_cut_mods[packet]:
  qabbrev_tac `pref = cu with cs_next_id := ci.cs_next_id` >>
  `intcall_stage_ops_mods (lo,func) cenv cx sa (pref,mid,z,Gz,tz) pin
    (ops,ws,vals,ptys,pflags)` by
    (simp[Abbr `pref`] >> irule store_cut_restrict_ids >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  irule intcall_stage_ops_transport_mods >>
  qexistsl_tac [`Gz`,`mid`,`z`,`pref`,`tz`] >>
  simp[Abbr `pref`,not_fresh_at_def] >>
  rpt (conj_tac >- (first_assum ACCEPT_TAC ORELSE decide_tac)) >>
  suspend "transport"
QED

Resume intcall_buffer_head_store_frame_cut_mods[transport]:
  rpt gen_tac >> strip_tac >>
  qpat_assum `!aid b k. _ ==> _ \/ _` (drule_all_then assume_tac) >>
  qpat_assum `!b n. _ ==> mem_bytes_at _ _ _ = _ /\ _`
    (drule_then strip_assume_tac) >> simp[] >>
  gen_tac >> strip_tac >>
  qpat_assum `!i. _ ==> (i IN tf.t_mem <=> _)` (drule_all_then mp_tac) >> simp[]
QED

Resume intcall_buffer_head_store_frame_cut_mods[finished]:
  `not_fresh_at cs dst` by (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `cu` >> simp[]) >>
  `ci.cs_next_id < cs.cs_next_id` by decide_tac >>
  `base+cap <= t.vs_alloca_next` by
    (qpat_assum `alloca_inv z` (strip_assume_tac o REWRITE_RULE [alloca_inv_def,alloca_next_valid_def]) >>
     qpat_assum `!aid b sz. FLOOKUP z.vs_allocas aid = SOME (b,sz) ==> _`
       (drule_then assume_tac) >> simp[]) >>
  `!n lb sz. local_region cenv mid.scopes t n lb sz ==> lb+sz <= base \/ base+cap <= lb` by
    (rpt gen_tac >> strip_tac >>
     `local_region cenv mid.scopes z n lb sz` by
       (qpat_assum `!n b k. local_region _ _ t n b k <=> _`
          (qspecl_then [`n`,`lb`,`sz`] (drule_then ACCEPT_TAC o iffLR))) >>
     qpat_assum `!n lb sz. local_region _ _ z n lb sz ==> _` (drule_then ACCEPT_TAC)) >>
  simp[] >> rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- suspend "mixed" >>
  Cases_on `pin` >- simp[] >> PairCases_on `x` >> gvs[] >>
  qpat_assum `!aid b k. _ ==> _ \/ _` (drule_all_then assume_tac) >>
  simp[DISJ_COMM]
QED

Resume intcall_buffer_head_store_frame_cut_mods[mixed]:
  rpt gen_tac >> strip_tac >>
  `op_prov Gz (EL j ops) = SOME (b,k)` by
    (qpat_assum `intcall_stage_ops_mods _ _ _ _ (cu,mid,z,Gz,tz) _ _`
       (strip_assume_tac o REWRITE_RULE [intcall_stage_ops_mods_def]) >>
     `MEM (EL j ops) ops` by simp[EL_MEM] >>
     Cases_on `EL j ops` >> gvs[op_prov_def] >> metis_tac[]) >>
  qpat_assum `!j b k. _ ==> ?aid. _` (drule_all_then strip_assume_tac) >>
  qpat_assum `!aid b k. _ ==> _ \/ _` (drule_all_then assume_tac) >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def]
QED

Finalise intcall_buffer_head_store_frame_cut_mods

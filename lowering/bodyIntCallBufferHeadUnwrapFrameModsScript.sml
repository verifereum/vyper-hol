(* Preserve the caller's staged operands across the three pre-store cuts. *)
Theory bodyIntCallBufferHeadUnwrapFrameMods
Ancestors
  bodyIntCallStagePacketTransportMods bodyIntCallStagePacketMods
  bodyFullPostsMods loweringPosts loweringStateRelDefs bodyMemoryDefs
  wordArgsPtr freshWrites vyperEvalScopesProgress vyperState
  ptrDiscipline venomState venomInst compileEnv finite_map arithmetic words
  vyperStorageFootprint bodyPtrDefs allocaHistory

val _ = Parse.hide "base";

Theorem head_locals_kept_trans[local]:
  (!n b k. local_region cenv ex.scopes x n b k ==>
           local_region cenv em.scopes m n b k) /\
  locals_kept cenv ex em x m /\ locals_kept cenv em ey m y ==>
  locals_kept cenv ex ey x y
Proof
  pure_rewrite_tac[locals_kept_def] >> strip_tac >> rpt conj_tac
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[scopes_progress_trans]
  >- (rpt strip_tac >>
      `?e e1. lookup_scopes n ex.scopes = SOME e /\
              lookup_scopes n em.scopes = SOME e1` by
        (gvs[local_region_def] >> metis_tac[optionTheory.option_CASES]) >>
      `e1 = e` by
        (qpat_assum `scopes_progress ex.scopes em.scopes`
           (qspecl_then [`n`,`e`,`e1`] mp_tac o REWRITE_RULE[scopes_progress_def]) >>
         qpat_assum `scopes_progress em.scopes ey.scopes`
           (qspecl_then [`n`,`e1`,`e`] mp_tac o REWRITE_RULE[scopes_progress_def]) >>
         gvs[] >> rw[] >> gvs[]) >>
      gvs[] >> metis_tac[]) >>
  fs[popped_kept_def] >> rpt strip_tac >>
  qpat_assum `!n b k entry h. local_region _ em.scopes _ _ _ _ /\ _ ==> _` irule >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists `n` >> simp[] >> rpt strip_tac >>
  qpat_assum `!n b k entry h. local_region _ ex.scopes _ _ _ _ /\ _ ==> _` irule >>
  conj_tac >- first_assum ACCEPT_TAC >> qexists `n` >> simp[]
QED

Theorem head_wb_frame_trans[local]:
  wb_frame cenv ex em sx x m /\ wb_frame cenv em ey sm m y /\
  sx.cs_next_var <= sm.cs_next_var /\ sx.cs_next_id <= sm.cs_next_id /\
  (!n b k. local_region cenv ex.scopes x n b k <=>
           local_region cenv em.scopes m n b k) ==>
  wb_frame cenv ex ey sx x y
Proof
  pure_rewrite_tac[wb_frame_def] >> strip_tac >> rpt conj_tac
  >- (rpt strip_tac >> `not_fresh_at sm x'` by metis_tac[not_fresh_at_mono] >> simp[])
  >- simp[]
  >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      `aid < sm.cs_next_id` by decide_tac >>
      `mem_bytes_at off sz m.vs_memory = mem_bytes_at off sz x.vs_memory` by
        (qpat_assum `!aid b k. _ ==> mem_bytes_at b k m.vs_memory = _`
           (qspecl_then [`aid`,`off`,`sz`] MATCH_MP_TAC) >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
      `mem_bytes_at off sz y.vs_memory = mem_bytes_at off sz m.vs_memory` by
        (qpat_assum `!aid b k. _ ==> mem_bytes_at b k y.vs_memory = _`
           (qspecl_then [`aid`,`off`,`sz`] MATCH_MP_TAC) >>
         conj_tac >- simp[] >> conj_tac >- first_assum ACCEPT_TAC >> metis_tac[]) >>
      asm_rewrite_tac[]) >>
  irule head_locals_kept_trans >> qexistsl [`em`,`m`] >> metis_tac[]
QED

(* These are statement abbreviations, not additional HOL invariants. *)
fun protected_taint cursor es s tn tt = ``
  !aid b k i. FLOOKUP (^s : venom_state).vs_allocas aid = SOME (b,k) /\
    aid < ^cursor.cs_next_id /\
    (!n lb sz. local_region cenv ^es.scopes ^s n lb sz ==> b+k <= lb \/ lb+sz <= b) /\
    b <= i /\ i < b+k /\ i IN ^tt.t_mem ==> i IN ^tn.t_mem``;

fun pin_at cursor es s G tn = ``
  case pin of NONE => T | SOME (rb,b,k) =>
    FLOOKUP ^G rb = SOME (b,k) /\ op_taint ^tn (Var rb) = {} /\
    lookup_var rb ^s = SOME (n2w b) /\
    FLOOKUP (^s : venom_state).vs_allocas sa.cs_next_id = SOME (b,k) /\
    sa.cs_next_id < ^cursor.cs_next_id /\ lo <= b /\ b+k <= ^s.vs_alloca_next /\
    not_fresh_at ^cursor rb /\
    (!n lb sz. local_region cenv ^es.scopes ^s n lb sz ==> b+k <= lb \/ lb+sz <= b)``;

fun edge sx ex x Gx tx sy ey y Gy ty = ``
  ^sx.cs_next_var <= ^sy.cs_next_var /\ ^sx.cs_next_id <= ^sy.cs_next_id /\
  (^x : venom_state).vs_alloca_next <= ^y.vs_alloca_next /\ ^y.vs_labels = ^x.vs_labels /\
  wb_frame cenv ^ex ^ey ^sx ^x ^y /\
  (!r. not_fresh_at ^sx r ==>
     FLOOKUP ^Gy r = FLOOKUP ^Gx r /\ op_taint ^ty (Var r) = op_taint ^tx (Var r)) /\
  (!n b k. local_region cenv ^ex.scopes ^x n b k <=> local_region cenv ^ey.scopes ^y n b k) /\
  ^(protected_taint sx ex x tx ty)``;

val edge_xy = edge ``sx:compile_state`` ``ex:evaluation_state`` ``x:venom_state``
  ``Gx:string |-> num # num`` ``tx:taint`` ``sy:compile_state`` ``ey:evaluation_state``
  ``y:venom_state`` ``Gy:string |-> num # num`` ``ty:taint``;
val pin_x = pin_at ``sx:compile_state`` ``ex:evaluation_state`` ``x:venom_state``
  ``Gx:string |-> num # num`` ``tx:taint``;
val pin_y = pin_at ``sy:compile_state`` ``ey:evaluation_state`` ``y:venom_state``
  ``Gy:string |-> num # num`` ``ty:taint``;

Theorem head_packet_pin_edge[local]:
  intcall_stage_ops_mods (lo,func) cenv cx sa (sx,ex,x,Gx,tx) pin packet /\
  ^pin_x /\ ^edge_xy ==>
  intcall_stage_ops_mods (lo,func) cenv cx sa (sy,ey,y,Gy,ty) pin packet /\ ^pin_y
Proof
  PairCases_on `packet` >> pure_rewrite_tac[wb_frame_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >> conj_tac
  >- (irule intcall_stage_ops_transport_mods >>
      qexistsl [`Gx`,`ex`,`x`,`sx`,`tx`] >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[]) >>
  irule intcall_stage_pin_transport_mods >>
  qexistsl [`Gx`,`ex`,`x`,`sx`,`tx`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[]
QED

val edge_iu = edge ``si:compile_state`` ``esi:evaluation_state`` ``s:venom_state``
  ``G:string |-> num # num`` ``tn:taint`` ``ci:compile_state`` ``mid:evaluation_state``
  ``u:venom_state`` ``Gu:string |-> num # num`` ``tu:taint``;
val edge_ua = edge ``ci:compile_state`` ``mid:evaluation_state`` ``u:venom_state``
  ``Gu:string |-> num # num`` ``tu:taint`` ``ca:compile_state`` ``mid:evaluation_state``
  ``a:venom_state`` ``Ga:string |-> num # num`` ``ta:taint``;
val edge_az = edge ``ca:compile_state`` ``mid:evaluation_state`` ``a:venom_state``
  ``Ga:string |-> num # num`` ``ta:taint`` ``cu:compile_state`` ``mid:evaluation_state``
  ``z:venom_state`` ``Gz:string |-> num # num`` ``tz:taint``;

Theorem intcall_buffer_head_unwrap_frame_mods:
  intcall_stage_frame_mods (DF,lo,d,ctx,func) cenv cx st0
    (sa,es0,s0,G0,tn0) (si,esi,s,G,tn) pin /\
  intcall_stage_ops_mods (lo,func) cenv cx sa (si,esi,s,G,tn) pin packet /\
  ^edge_iu /\ ^edge_ua /\ ^edge_az /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at si p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at si p) /\
  ghost_kept_at lo cenv esi si G tn s Gz tz /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
     expr_post_mods H ctx func cenv cx e esi si cu s mid v opn z /\
     ghost_inv_at_mods (DF H) lo d cenv cx mid Gz tz z /\
     storage_well_formed_on cx mid (FST H)) /\
  ~z.vs_halted /\ alloca_history func z /\
  z.vs_current_bb = cu.cs_current_bb /\ z.vs_inst_idx = LENGTH cu.cs_current_insts /\
  ci.cs_next_id < ca.cs_next_id /\
  FLOOKUP a.vs_allocas ci.cs_next_id = SOME (base,cap) /\
  (!n b k. local_region cenv mid.scopes a n b k ==> regions_disjoint base cap b k) /\
  (!aid b k. aid < ci.cs_next_id /\ FLOOKUP u.vs_allocas aid = SOME (b,k) ==>
     regions_disjoint base cap b k) ==>
  intcall_stage_frame_mods (DF,lo,d,ctx,func) cenv cx st0
    (sa,es0,s0,G0,tn0) (cu,mid,z,Gz,tz) pin /\
  intcall_stage_ops_mods (lo,func) cenv cx sa (cu,mid,z,Gz,tz) pin packet /\
  sa.cs_next_id <= ci.cs_next_id /\ ci.cs_next_id < cu.cs_next_id /\
  FLOOKUP z.vs_allocas ci.cs_next_id = SOME (base,cap) /\
  (!n b k. local_region cenv mid.scopes z n b k ==> b+k <= base \/ base+cap <= b) /\
  (!aid b k. aid < si.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,k) ==>
     regions_disjoint base cap b k)
Proof
  pure_rewrite_tac[intcall_stage_frame_mods_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac
    (Q.INST [`sx` |-> `si`, `sy` |-> `ci`] head_packet_pin_edge) >>
  drule_all_then strip_assume_tac
    (Q.INST [`sx` |-> `ci`, `sy` |-> `ca`] head_packet_pin_edge) >>
  drule_all_then strip_assume_tac
    (Q.INST [`sx` |-> `ca`, `sy` |-> `cu`] head_packet_pin_edge) >>
  suspend "origin"
QED

Resume intcall_buffer_head_unwrap_frame_mods[origin]:
  `wb_frame cenv mid mid ci u z` by
    (irule head_wb_frame_trans >> qexistsl [`mid`,`a`,`ca`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `wb_frame cenv esi mid si s z` by
    (irule head_wb_frame_trans >> qexistsl [`mid`,`u`,`ci`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `wb_frame cenv es0 mid sa s0 z` by
    (irule head_wb_frame_trans >> qexistsl [`esi`,`s`,`si`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `wb_frame cenv es0 esi sa s0 s`
    (strip_assume_tac o REWRITE_RULE[wb_frame_def]) >>
  `!n b k. local_region cenv esi.scopes s n b k <=> local_region cenv es0.scopes s0 n b k` by
    (qpat_assum `!n b k. local_region cenv es0.scopes s0 n b k <=> _` (fn th => simp[Once th])) >>
  drule_all_then assume_tac ghost_kept_at_trans >>
  `si.cs_next_var <= cu.cs_next_var /\ s.vs_alloca_next <= z.vs_alloca_next` by decide_tac >>
  `return_buf_frame d cenv cu z` by
    (qpat_assum `wb_frame cenv esi mid si s z`
       (strip_assume_tac o REWRITE_RULE[wb_frame_def]) >>
     irule return_buf_frame_frame >> qexistsl [`cenv`,`s`,`si`] >>
     simp[] >> first_assum ACCEPT_TAC) >>
  `MAP FDOM es0.scopes = MAP FDOM mid.scopes` by
    (qpat_assum `wb_frame cenv es0 mid sa s0 z`
       (strip_assume_tac o REWRITE_RULE[wb_frame_def,locals_kept_def]) >> simp[]) >>
  suspend "finish"
QED

Resume intcall_buffer_head_unwrap_frame_mods[finish]:
  `sa.cs_next_id <= cu.cs_next_id /\ sa.cs_next_var <= cu.cs_next_var /\
   s0.vs_alloca_next <= z.vs_alloca_next /\ sa.cs_next_id <= ci.cs_next_id /\
   ci.cs_next_id < cu.cs_next_id` by decide_tac >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (rpt gen_tac >> EQ_TAC >> strip_tac >> metis_tac[])
  >- (gen_tac >> disch_tac >>
      qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
        (drule_then strip_assume_tac) >> fs[expr_post_mods_def,expr_post_def])
  >- (qpat_assum `wb_frame cenv mid mid ca a z`
        (strip_assume_tac o REWRITE_RULE[wb_frame_def]) >> simp[])
  >- (rpt gen_tac >> disch_tac >>
      `local_region cenv mid.scopes a n b k` by metis_tac[] >>
      qpat_assum `!n b k. local_region _ _ a n b k ==> _` (drule_then mp_tac) >>
      simp[loweringStateRelDefsTheory.regions_disjoint_def,DISJ_COMM]) >>
  rpt gen_tac >> strip_tac >>
  `aid < ci.cs_next_id` by decide_tac >>
  `FLOOKUP u.vs_allocas aid = SOME (b,k)` by
    (qpat_assum `wb_frame cenv esi mid si s u`
       (strip_assume_tac o REWRITE_RULE[wb_frame_def]) >> simp[]) >>
  qpat_assum `!aid b k. aid < ci.cs_next_id /\ _ ==> _` (drule_all_then ACCEPT_TAC)
QED

Finalise intcall_buffer_head_unwrap_frame_mods

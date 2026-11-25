(* The snapshot copy writes into the item allocation without changing scopes. *)
Theory bodyForArraySnapshotFrameMods
Ancestors
  bodyForArrayHeaderMods bodyIfExpTypedGhostMods bodyIfExpTypedImmFrameMods
  bodyForRangeHeaderMods bodySimFull bodyMemoryDefs stateRelProj
  typedMemoryCopy typedCopyOriginPtrBase exprSimCopy exprSimStorageCopy
  stmtSimDefs stmtSimProps ptrDiscipline loweringStateRelDefs
  venomMemDefs venomState compileEnv finite_map arithmetic

(* One row argument applies at both compiler ages. *)
Theorem snapshot_older_rows[local]:
  alloca_frame cenv old age entry cenv ee u /\
  (!aid row. FLOOKUP entry.vs_allocas aid = SOME row ==>
             FLOOKUP u.vs_allocas aid = SOME row) /\
  allocas_non_overlapping u /\ FLOOKUP u.vs_allocas item_id = SOME (dst,cap) /\
  age.cs_next_id <= item_id /\
  (!nm b sz. local_region cenv ee.scopes z nm b sz ==>
             local_region cenv ee.scopes u nm b sz) /\
  (!b sz. b+sz <= dst \/ dst+cap <= b ==>
          mem_bytes_at b sz z.vs_memory = mem_bytes_at b sz u.vs_memory) /\
  (!i. i < dst \/ dst+cap <= i ==> (i IN tf.t_mem <=> i IN tu.t_mem)) ==>
  alloca_frame cenv old age entry cenv ee z /\
  !aid b sz i. FLOOKUP entry.vs_allocas aid = SOME (b,sz) /\
    aid < age.cs_next_id /\ b <= i /\ i < b+sz /\ i IN tf.t_mem ==> i IN tu.t_mem
Proof
  strip_tac >>
  `!aid b sz. FLOOKUP entry.vs_allocas aid = SOME (b,sz) /\ aid < age.cs_next_id ==>
             b+sz <= dst \/ dst+cap <= b` by
    (rpt strip_tac >> `aid <> item_id` by decide_tac >>
     `FLOOKUP u.vs_allocas aid = SOME (b,sz)` by simp[] >>
     qpat_x_assum `allocas_non_overlapping u` mp_tac >>
     simp[allocas_non_overlapping_def] >>
     disch_then (qspecl_then [`aid`,`item_id`,`b`,`sz`,`dst`,`cap`] mp_tac) >> simp[]) >>
  conj_tac
  >- (qhdtm_x_assum `alloca_frame` (assume_tac o REWRITE_RULE [alloca_frame_def]) >>
      pure_rewrite_tac[alloca_frame_def] >> rpt gen_tac >> strip_tac >>
      `mem_bytes_at off sz z.vs_memory = mem_bytes_at off sz u.vs_memory` by
        (qpat_assum `!b sz. _ ==> mem_bytes_at b sz z.vs_memory = _` irule >>
         qpat_assum `!aid b sz. FLOOKUP entry.vs_allocas aid = _ /\ _ ==> _`
           (drule_all_then ACCEPT_TAC)) >>
      qpat_assum `!aid off sz. _ ==> mem_bytes_at off sz u.vs_memory = _ /\ _`
        (qspecl_then [`aid`,`off`,`sz`] mp_tac) >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      strip_tac >> simp[] >> rpt gen_tac >> disch_tac >>
      qpat_assum `!nm b sz. local_region cenv ee.scopes z nm b sz ==> _`
        (drule_then assume_tac) >>
      qpat_assum `!n b sz. local_region cenv ee.scopes u n b sz ==> _`
        (drule_then ACCEPT_TAC)) >>
  rpt strip_tac >>
  `b+sz <= dst \/ dst+cap <= b` by
    (qpat_assum `!aid b sz. FLOOKUP entry.vs_allocas aid = _ /\ _ ==> _`
       (drule_all_then ACCEPT_TAC)) >>
  `i < dst \/ dst+cap <= i` by decide_tac >>
  qpat_assum `!i. _ ==> (i IN tf.t_mem <=> i IN tu.t_mem)`
    (qspec_then `i` mp_tac) >> simp[]
QED

Theorem for_array_snapshot_frame_mods:
  typed_copy_state_frame k (w2n dw) n u z /\ n <= cap /\
  tf.t_imm = tu.t_imm /\ tf.t_stor = tu.t_stor /\ tf.t_trans = tu.t_trans /\
  (!i. ~(w2n dw <= i /\ i < w2n dw+n) ==> (i IN tf.t_mem <=> i IN tu.t_mem)) /\
  (!x. not_fresh_at k x ==> FLOOKUP Gf x = FLOOKUP Gu x /\
                           op_taint tf (Var x) = op_taint tu (Var x)) /\
  stmt_state_rel H ctx func cenv cx ee u /\ immutable_frame_mods func cenv cx ee u /\
  ghost_inv_at_mods D lo d cenv cx ee Gu tu u /\
  ret_pc_ok cenv sa u /\ return_buf_frame d cenv sa u /\ return_buf_sep d cenv ee u /\
  allocas_from lo u /\ lo <= u.vs_alloca_next /\
  local_ptrs_reserved cenv k /\
  (!x. not_fresh_at sa x ==> not_fresh_at k x) /\
  (!x. not_fresh_at saLen x ==> not_fresh_at k x) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  for_array_outer_frame_mods ctx func cenv sa es0 s0 G0 tn0 ee Gu tu u /\
  for_array_capture_frame_mods cenv (em,saExpr,saLen,q,tq) ee tu u /\
  for_array_item_mods cenv sa saExpr (xd,dw,cap,inst.inst_id) ee Gu tu u /\
  lookup_var xd z = SOME dw /\ ptr_covers Gf tf xd z cap /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  alloca_history func z ==>
  stmt_state_rel H ctx func cenv cx ee z /\ immutable_frame_mods func cenv cx ee z /\
  ghost_inv_at_mods D lo d cenv cx ee Gf tf z /\
  ret_pc_ok cenv sa z /\ return_buf_frame d cenv sa z /\ return_buf_sep d cenv ee z /\
  allocas_from lo z /\ lo <= z.vs_alloca_next /\
  for_array_outer_frame_mods ctx func cenv sa es0 s0 G0 tn0 ee Gf tf z /\
  for_array_capture_frame_mods cenv (em,saExpr,saLen,q,tq) ee tf z /\
  for_array_item_mods cenv sa saExpr (xd,dw,cap,inst.inst_id) ee Gf tf z /\
  (!op. copy_old_operand k op ==> eval_operand op z = eval_operand op u /\
        op_prov Gf op = op_prov Gu op /\ op_taint tf op = op_taint tu op)
Proof
  strip_tac >>
  drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  `allocas_non_overlapping u` by fs[alloca_inv_def] >>
  `typed_copy_state_frame k (w2n dw) cap u z` by
    (irule typed_copy_state_frame_subinterval >> qexistsl [`w2n dw`,`n`] >> simp[]) >>
  `copy_static z = copy_static u /\ z.vs_allocas = u.vs_allocas /\
   z.vs_alloca_next = u.vs_alloca_next /\ LENGTH u.vs_memory <= LENGTH z.vs_memory /\
   (!x. not_fresh_at k x ==> lookup_var x z = lookup_var x u) /\
   (!b sz. b+sz <= w2n dw \/ w2n dw+cap <= b ==>
      mem_bytes_at b sz z.vs_memory = mem_bytes_at b sz u.vs_memory)` by
    (fs[typed_copy_state_frame_def,typed_copy_frame_def,copy_static_def,
        venom_state_component_equality] >> rpt strip_tac >> metis_tac[]) >>
  `!i. i < w2n dw \/ w2n dw+cap <= i ==> (i IN tf.t_mem <=> i IN tu.t_mem)` by
    (gen_tac >> disch_tac >> first_x_assum irule >> decide_tac) >>
  `!nm b sz. local_region cenv ee.scopes z nm b sz <=> local_region cenv ee.scopes u nm b sz` by
    (rpt gen_tac >> irule copy_buffer_local_region_frame >> qexists `k` >> simp[]) >>
  qhdtm_x_assum `for_array_item_mods` (strip_assume_tac o REWRITE_RULE [for_array_item_mods_def]) >>
  conj_tac >- suspend "state" >>
  conj_tac >- suspend "immutable" >>
  conj_tac >- suspend "ghost" >>
  conj_tac >- suspend "pc" >>
  conj_tac >- suspend "buffer" >>
  conj_tac >- suspend "separation" >>
  conj_tac >- (pure_rewrite_tac[allocas_from_def] >>
               qpat_assum `z.vs_allocas = u.vs_allocas` SUBST1_TAC >>
               qpat_assum `allocas_from lo u` (ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
  conj_tac >- simp[] >>
  conj_tac >- suspend "outer" >>
  conj_tac >- suspend "capture" >>
  conj_tac >- (simp[for_array_item_mods_def] >> rpt gen_tac >> disch_tac >>
               qpat_assum `!nm b sz. local_region cenv ee.scopes u nm b sz ==> _`
                 (drule_then mp_tac) >> simp[]) >>
  suspend "operands"
QED

Resume for_array_snapshot_frame_mods[state]:
  irule copy_buffer_state_rel_frame >>
  qexistsl [`w2n dw`,`inst`,`u`,`k`,`cap`] >>
  asm_rewrite_tac[ADD_COMM] >> rpt conj_tac >> rpt strip_tac >>
  first_x_assum (drule_then mp_tac) >> simp[]
QED

Resume for_array_snapshot_frame_mods[immutable]:
  irule ifexp_typed_immutable_frame_mods >>
  qexistsl [`w2n dw`,`inst`,`k`,`cap`,`u`] >> simp[]
QED

Resume for_array_snapshot_frame_mods[ghost]:
  `lo <= w2n dw` by
    (qpat_assum `allocas_from lo u`
       (drule_then ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
  `!name b sz. local_region cenv ee.scopes u name b sz ==>
                loweringStateRelDefs$regions_disjoint (w2n dw) n b sz` by
    (rpt strip_tac >> qpat_assum `!nm b sz. local_region cenv ee.scopes u nm b sz ==> _`
             (drule_then mp_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  irule ifexp_typed_copy_ghost_mods >>
  qexistsl [`Gu`,`w2n dw`,`func`,`k`,`n`,`u`,`tu`] >> simp[] >> metis_tac[]
QED

Resume for_array_snapshot_frame_mods[pc]:
  irule ret_pc_ok_frame >> qexistsl [`cenv`,`u`,`sa`] >> simp[] >> metis_tac[]
QED

Resume for_array_snapshot_frame_mods[buffer]:
  irule return_buf_frame_frame >> qexistsl [`cenv`,`u`,`sa`] >> simp[] >> metis_tac[]
QED

Resume for_array_snapshot_frame_mods[separation]:
  Cases_on `d` >- simp[return_buf_sep_def] >>
  rename1 `return_buf_sep (SOME rb) _ _ _` >> PairCases_on `rb` >>
  qpat_assum `return_buf_sep (SOME _) cenv ee u` mp_tac >>
  pure_rewrite_tac[return_buf_sep_def,allocas_from_def] >>
  asm_rewrite_tac[]
QED

Resume for_array_snapshot_frame_mods[outer]:
  qhdtm_x_assum `for_array_outer_frame_mods` mp_tac >>
  simp[for_array_outer_frame_mods_def,range_outer_frame_mods_def] >> strip_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp z` by
    metis_tac[typed_copy_state_frame_allocas_below_fmp] >>
  `alloca_frame cenv es0 sa s0 cenv ee z /\
   !aid b sz i. FLOOKUP s0.vs_allocas aid = SOME (b,sz) /\ aid < sa.cs_next_id /\
     b <= i /\ i < b+sz /\ i IN tf.t_mem ==> i IN tu.t_mem` by
    (irule snapshot_older_rows >> qexistsl [`cap`,`w2n dw`,`inst.inst_id`,`u`] >>
     asm_rewrite_tac[] >> rpt conj_tac >> rpt gen_tac >> disch_tac >>
     first_x_assum (drule_then mp_tac) >> simp[]) >>
  simp[] >> rpt conj_tac >> rpt strip_tac >> metis_tac[]
QED

Resume for_array_snapshot_frame_mods[capture]:
  qhdtm_x_assum `for_array_capture_frame_mods` mp_tac >>
  simp[for_array_capture_frame_mods_def] >> strip_tac >>
  `alloca_frame cenv em saExpr q cenv ee z /\
   !aid b sz i. FLOOKUP q.vs_allocas aid = SOME (b,sz) /\ aid < saExpr.cs_next_id /\
     b <= i /\ i < b+sz /\ i IN tf.t_mem ==> i IN tu.t_mem` by
    (irule snapshot_older_rows >> qexistsl [`cap`,`w2n dw`,`inst.inst_id`,`u`] >>
     asm_rewrite_tac[] >> rpt conj_tac >> rpt gen_tac >> disch_tac >>
     first_x_assum (drule_then mp_tac) >> simp[]) >>
  simp[] >> rpt conj_tac >> rpt strip_tac >> metis_tac[]
QED

Resume for_array_snapshot_frame_mods[operands]:
  drule_then strip_assume_tac copy_static_fields >>
  Cases >> simp[copy_old_operand_def,eval_operand_def,op_prov_def,op_taint_def] >>
  rpt strip_tac >> first_x_assum drule >> simp[op_taint_def]
QED

Finalise for_array_snapshot_frame_mods

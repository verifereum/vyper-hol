(* Reachable ISTORE effects; ownership is retained by the ordinary adapter. *)
Theory lowerDloadSafetyImmutableWriteCoverage
Ancestors
  lowerDloadSafetyImmutableWriteEffects lowerDloadSafetyWriteAssembly
  lowerDloadOracleCallAssembly
  lowerDloadSafetyAssemblyPremises lowerDloadSafetyTaintWidth
  lowerDloadSafetyOrdinaryCoverage lowerDloadSafetyAmbient
  lowerDloadSafetyValues lowerDloadSafetyRelation
  codegenRel contextCodegenRel venomWf ptrDiscipline pointerConfinedDefs
  memLocDefs venomInst venomExecSemantics venomState finite_map list pred_set

Theorem ld_istore_operand_unselected[local]:
  ld_vars P A f /\ fn_ptr_ok P f.lf_fn /\
  MEM inst (fn_insts f.lf_fn) /\ inst.inst_opcode = ISTORE /\
  MEM op inst.inst_operands ==> op_prov f.lf_H op = NONE
Proof
  strip_tac >> Cases_on `op` >> simp[op_prov_def] >>
  irule ld_vars_unselected >> simp[] >>
  fs[fn_ptr_ok_def] >> metis_tac[]
QED

Theorem ld_sync_istore_effect:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\ f.lf_src = s /\ f.lf_tgt = t /\ f.lf_fn = fn /\
  ptr_discipline lo C vs0 /\ fn_shape_ok fn /\ fn_inst_wf fn /\
  o1_ctx_shape C /\ mem_inv dload_headroom_ok C vs0 /\
  s.vs_labels = t.vs_labels /\ ~in_revert_forward fn s /\
  t.vs_alloca_next < dimword(:256) /\
  inst.inst_opcode = ISTORE /\
  step_inst fuel C' inst t = OK ts ==>
  ?ss. step_inst fuel C inst s = OK ss /\
    ld_vars P A (f with <|lf_src := ss; lf_tgt := ts;
      lf_tv := (step_taint inst s ss tn).t_var|>) /\
    ld_memory lo A (step_taint inst s ss tn) ss ts /\
    ld_nonghost (step_taint inst s ss tn) ss ts /\
    step_prov PG G inst ss = G /\
    ld_dyn_agree (dyn_floor C vs0) (step_taint inst s ss tn).t_mem
      ss.vs_memory ts.vs_memory /\
    ss.vs_allocas = s.vs_allocas /\ ss.vs_alloca_next = s.vs_alloca_next /\
    ss.vs_current_bb = s.vs_current_bb /\ ss.vs_prev_bb = s.vs_prev_bb /\
    ss.vs_inst_idx = s.vs_inst_idx /\
    ts.vs_allocas = t.vs_allocas /\ ts.vs_alloca_next = t.vs_alloca_next /\
    ts.vs_current_bb = t.vs_current_bb /\ ts.vs_prev_bb = t.vs_prev_bb /\
    ts.vs_inst_idx = t.vs_inst_idx /\
    (!a. a IN FRANGE f.lf_H ==> a IN FDOM A)
Proof
  strip_tac >>
  `MEM inst (fn_insts fn)` by
    (drule ld_sync_source >> metis_tac[ld_active_inst_member]) >>
  `fn_ptr_ok P fn` by metis_tac[ld_sync_ptr_ok] >>
  drule ld_sync_active >> simp[] >> strip_tac >>
  drule ld_sync_ghosts >> simp[] >> strip_tac >>
  drule ld_sync_memory >> strip_tac >>
  `access_ok lo G fn inst s` by metis_tac[ld_sync_access_ok] >>
  `taint_ok fn tn inst s` by metis_tac[ld_sync_taint_ok] >>
  `inst_wf inst` by
    (fs[fn_inst_wf_def, fn_insts_def, o1PassContractTheory.fn_insts_blocks_MEM] >>
     metis_tac[]) >>
  `FDOM A = ld_slots A (f::fs) /\ EVERY (ld_maps A) (f::fs)` by
    (qpat_assum `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[ld_sync_def] >> simp[EVERY_MEM] >>
     strip_tac >> metis_tac[]) >>
  `!a. a IN FRANGE f.lf_H ==> a IN FDOM A` by
    metis_tac[ld_global_selected, MEM] >>
  `!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==> c+sz < dimword(:256)` by
    (drule ld_alloc_target_no_wrap >> simp[] >> metis_tac[]) >>
  `lo <= dyn_floor C vs0 /\
   !a u v z. FLOOKUP A a = SOME (u,v,z) ==>
     u+z <= dyn_floor C vs0 /\ v+z <= dyn_floor C vs0` by
    (`EVERY (ld_maps A) (f::fs)` by
       FIRST [first_assum ACCEPT_TAC, rewrite_tac[listTheory.EVERY_DEF] >>
              conj_tac >> first_assum ACCEPT_TAC] >>
     drule_all ld_sync_dyn_floor >> metis_tac[]) >>
  drule ld_sync_dyn_agree >> strip_tac >>
  gvs[step_inst_non_invoke] >> suspend "operands"
QED

Resume ld_sync_istore_effect[operands]:
  `MEM inst.inst_opcode [MSTORE;MSTORE8;ISTORE]` by simp[] >>
  drule_all ld_write2_operands >> strip_tac >>
  `op_prov f.lf_H a = NONE /\ op_prov f.lf_H v = NONE` by
    (conj_tac >> irule ld_istore_operand_unselected >>
     metis_tac[MEM]) >>
  `word_agree_except (op_taint tn v) x y` by
    (irule ld_write_scalar_observation >> simp[] >>
     qexistsl_tac [`A`,`P`,`f`,`inst`] >> simp[]) >>
  `op_taint tn a = {}` by metis_tac[ld_write2_taint] >>
  `dst = dst'` by
    (drule ld_write_address_observation >> simp[] >>
     disch_then (qspecl_then [`dst'`,`dst`,`tn`,`a`,`inst`] mp_tac) >>
     fs[]) >>
  gvs[] >> suspend "write"
QED

Resume ld_sync_istore_effect[write]:
  `?ops. mem_write_ops inst = SOME ops /\ ops.iao_ofst = a` by
    simp[mem_write_ops_def] >>
  `MEM (w2n dst,32) (source_memory_write_ranges inst f.lf_src)` by
    simp[source_memory_write_ranges_def, fixed_source_write_range_def,
         eval_operands_def, mem_write_ops_def] >>
  `0 < (32:num)` by simp[] >>
  `(op_prov f.lf_H ops.iao_ofst = NONE ==> dst = dst) /\
   (!k. op_prov f.lf_H ops.iao_ofst = SOME k ==> ld_wordrel A (SOME k) dst dst)` by
    simp[] >>
  Q.SUBGOAL_THEN `w2n dst+32 <= lo \/
    (?k b c sz delta. FLOOKUP A k = SOME (b,c,sz) /\
      w2n dst=b+delta /\ w2n dst=c+delta /\ delta+32 <= sz) \/
    dyn_floor C vs0 <= w2n dst` ASSUME_TAC >-
    (drule_all (Q.INST [`n` |-> `32`] (cj 2 ld_access_dyn_cases)) >>
     metis_tac[]) >>
  `op_taint tn v SUBSET {j | j < 32}` by
    (drule ld_sync_source >> strip_tac >> irule ld_reachable_op_taint_width >> metis_tac[]) >>
  `tn.t_var = f.lf_tv /\ EVERY (ld_maps A) (f::fs)` by simp[] >>
  drule_all ld_istore_effect >> strip_tac >>
  qexists_tac `ss` >> simp[step_prov_def, set_prov_def, DRESTRICT_UNIV]
QED

Finalise ld_sync_istore_effect

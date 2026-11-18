(* Operational synchronization across the actual private DLOAD expansion. *)
Theory gasFocusLowerDloadScratchNext
Ancestors
  lowerDloadExpansionEndpoint lowerDloadScratchTransport lowerDloadPublicTrace
  lowerDloadSafetyRelation lowerDloadSafetyKernel lowerDloadSafetyAmbient
  lowerDloadSafetyLocations lowerDloadSafetyBoundary lowerDloadFrontier
  lowerDloadOracleCallAssembly lowerDloadAllocationOrigins lowerDloadSafetyAdvance
  ptrDisciplineEmptyTaint o1SafeUpto o1PassContract unitShapeDefs venomWf
  unitTransformDefs ptrDiscipline lowerDloadDefs oracleExecProps
  venomExecSemantics venomInst venomState finite_map pred_set list words arithmetic

Theorem ld_focus_dload_scratch_next:
  ld_sync lo P C vs stk PG G tn fn inst s t0 A (f::fs) N /\
  ld_global lo A (f::fs) /\ o1_ctx_shape C /\ o1_initial_state_ok vs /\
  vs.vs_fmp = vs.vs_initial_fmp /\ code_layout_valid vs /\
  o1_safe_upto D lo n C vs /\ gas_cut n vs s /\
  (!j k. j < k /\ k < LENGTH (f::fs) ==>
     list_precedes (EL j (f::fs)).lf_fn.fn_name (EL k (f::fs)).lf_fn.fn_name names) /\
  ir_supply_covers_fn f.lf_supply fn /\
  inst.inst_opcode = DLOAD /\ inst.inst_operands = [off] /\ inst.inst_outputs = [out] /\
  ld_envelope f.lf_supply fn s s.vs_inst_idx X p /\ t0.vs_inst_idx = p /\
  ld_prefix C' (ld_image f) X p h t0 t /\ SUC h = LENGTH X /\
  step_inst fuel C' (EL h X) t = OK u ==>
  ?ss v g c.
    step_inst 0 C inst s = OK ss /\ step_inst 0 C' (HD X) t0 = OK v /\
    h = 3 /\ LENGTH X = 4 /\ u.vs_inst_idx = t.vs_inst_idx /\
    SUC t.vs_inst_idx = p + LENGTH X /\
    g = f with <|lf_src := ss with vs_inst_idx := SUC s.vs_inst_idx;
                 lf_tgt := u with vs_inst_idx := SUC t.vs_inst_idx;
                 lf_H := set_prov f.lf_H [out] NONE;
                 lf_tv := (step_taint inst s ss tn).t_var;
                 lf_E := inst.inst_id INSERT f.lf_E|> /\
    ss.vs_gas_readings = s.vs_gas_readings /\ u.vs_gas_readings = t0.vs_gas_readings /\
    ld_private f inst.inst_id (HD X).inst_id /\
    FLOOKUP u.vs_allocas (HD X).inst_id = SOME (c,32) /\ lo <= c /\
    c + 32 <= u.vs_alloca_next /\
    (!k b e sz. FLOOKUP A k = SOME (b,e,sz) /\ 0 < sz ==> e+sz <= c \/ c+32 <= e) /\
    (!i. ~(c <= i /\ i < c+32) ==> read_byte i u.vs_memory = read_byte i t0.vs_memory) /\
    ld_global lo A (g::fs) /\ EVERY (ld_maps A) (g::fs) /\ FDOM A = ld_slots A (g::fs) /\
    ld_memory lo A (step_taint inst s ss tn) ss u /\ ld_nonghost (step_taint inst s ss tn) ss u /\
    ld_dyn_agree (dyn_floor C vs) (step_taint inst s ss tn).t_mem ss.vs_memory u.vs_memory /\
    (!next. active_inst fn next g.lf_src ==>
       ld_sync lo P C vs stk PG (step_prov PG G inst ss) (step_taint inst s ss tn)
         fn next g.lf_src g.lf_tgt A (g::fs) N)
Proof
  strip_tac >> drule ld_sync_source >> strip_tac >>
  `raw_reachable vs C fn inst s` by metis_tac[ld_frame_raw_reachable] >>
  qpat_x_assum `o1_safe_upto _ _ _ _ _` mp_tac >>
  simp[o1_safe_upto_def, o1_ptr_safe_upto_def, ptr_discipline_upto_def] >> strip_tac >>
  `taint_ok fn tn inst s` by
    (qpat_assum `!stk PG G tn fn inst s. frame_reachable _ _ stk PG G tn fn inst s /\ _ ==> _`
       (qspecl_then [`stk`, `PG`, `G`, `tn`, `fn`, `inst`, `s`] mp_tac) >> simp[]) >>
  `dload_offset_ok C fn inst s` by
    (qpat_assum `!fn inst s. raw_reachable _ _ fn inst s /\ _ ==> _`
       (qspecl_then [`fn`, `inst`, `s`] mp_tac) >> simp[]) >>
  drule ld_raw_reachable_frontier >> strip_tac >>
  drule ld_sync_frontier >> strip_tac >>
  `lo <= s.vs_alloca_next /\ lo <= t0.vs_alloca_next` by decide_tac >>
  `dload_headroom_ok C fn inst s` by (irule ld_sync_source_mem_inv >> metis_tac[]) >>
  drule_all ld_sync_fn_shape >> strip_tac >>
  drule o1_fn_shape_components >> strip_tac >>
  drule ld_sync_active >> simp[NoAsms] >> strip_tac >>
  drule_all ld_dload_envelope_temporary >>
  disch_then (qx_choose_then `ai` (qx_choose_then `zi` (qx_choose_then `ci`
    (qx_choose_then `mi` (qx_choose_then `a` (qx_choose_then `z` strip_assume_tac)))))) >>
  `h = 3 /\ LENGTH X = 4 /\ (HD X).inst_id = ai` by gvs[] >>
  qpat_x_assum `h = 3` SUBST_ALL_TAC >>
  drule_all ld_prefix_position >> strip_tac >>
  suspend "offset"
QED

Resume ld_focus_dload_scratch_next[offset]:
  `?ow basew. eval_operand off t0 = SOME ow /\
     eval_operand (Label "code_end") t0 = SOME basew` by
    (irule ld_dload_trace_offset >>
     qexistsl_tac [`C'`,`X`,`a`,`ld_image f`,`p`,`t`] >> simp[]) >>
  drule ld_sync_ptr_ok >> strip_tac >>
  drule ld_sync_labels >> strip_tac >>
  `MEM inst (fn_insts fn)` by metis_tac[ld_active_inst_member] >>
  `eval_operand off s = SOME ow` by
    (drule ld_dload_operand_equal >> simp[] >>
     disch_then drule >> simp[] >> disch_then (qspec_then `tn` mp_tac) >> simp[]) >>
  `code_layout_valid s` by (irule ld_sync_source_code_layout_static >> metis_tac[]) >>
  `eval_operand (Label "code_end") s = SOME basew` by fs[eval_operand_def] >>
  `w2n ow + (LENGTH s.vs_code - LENGTH s.vs_data_section) < dimword (:256)` by
    (qpat_x_assum `dload_offset_ok C fn inst s` mp_tac >>
     pure_rewrite_tac[dload_offset_ok_def] >>
     disch_then (qspecl_then [`off`,`ow`] mp_tac) >> simp[]) >>
  drule ld_sync_memory >> strip_tac >>
  `t0.vs_code = s.vs_code` by fs[ld_nonghost_def] >>
  suspend "exit"
QED

Resume ld_focus_dload_scratch_next[exit]:
  `vs.vs_allocas = FEMPTY` by fs[o1_initial_state_ok_def] >>
  `ir_supply_covers_fn f.lf_supply f.lf_fn` by simp[] >>
  `FLOOKUP s.vs_allocas ai = NONE` by
    (irule ld_sync_private_source_absent >> metis_tac[]) >>
  `ALL_DISTINCT (fn_ir_inst_ids f.lf_fn)` by
    (pure_asm_rewrite_tac[] >>
     qpat_assum `o1_fn_shape C fn` mp_tac >>
     pure_rewrite_tac[o1_fn_shape_def, wf_function_def, fn_inst_ids_distinct_def,
       irSupplyTheory.fn_ir_inst_ids_def, lambdify irSupplyTheory.block_ir_inst_ids_def] >>
     rpt strip_tac >> first_assum ACCEPT_TAC) >>
  `MEM out (fn_ir_vars f.lf_fn)` by
    (irule lowerDloadSafetyUpdatesTheory.ld_inst_output_ir >> qexists_tac `inst` >> simp[]) >>
  `EVERY (ld_maps A) (f::fs) /\ FDOM A = ld_slots A (f::fs) /\
   set (MAP (\f. f.lf_fn) (f::fs)) SUBSET set C.ctx_functions /\
   (!j. j < LENGTH (f::fs) ==>
     (EL j (f::fs)).lf_tgt.vs_alloca_next =
     (EL j (f::fs)).lf_src.vs_alloca_next + 32 * ld_charge (DROP j (f::fs)))` by
    (qpat_assum `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[ld_sync_def, EVERY_MEM, SUBSET_DEF, MEM_MAP] >> rpt strip_tac >> metis_tac[]) >>
  `ALL_DISTINCT (MAP (\f. f.lf_fn) (f::fs))` by
    (irule ld_frames_distinct >> metis_tac[]) >>
  `~MEM a (fn_ir_vars f.lf_fn) /\ ~MEM z (fn_ir_vars f.lf_fn) /\
   dload_headroom_ok C f.lf_fn inst s` by simp[] >>
  drule_all ld_dload_scratch_exit >>
  disch_then (qspec_then `PG` (qx_choose_then `ss`
    (qx_choose_then `v` (qx_choose_then `g` (REPEAT_TCL CONJUNCTS_THEN assume_tac))))) >>
  qpat_x_assum `?c. FLOOKUP u.vs_allocas ai = _ /\ _` (qx_choose_then `c` strip_assume_tac) >>
  suspend "assemble"
QED

Resume ld_focus_dload_scratch_next[assemble]:
  `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
   inst.inst_opcode <> GAS /\ ~MEM inst.inst_opcode [PARAM; ADD; SUB; ASSIGN]` by
    simp[is_terminator_def] >>
  `ss.vs_gas_readings = s.vs_gas_readings` by
    (drule_all step_inst_noninvoke_gas_readings >> simp[]) >>
  `u.vs_gas_readings = t0.vs_gas_readings` by
    (qpat_assum `ld_nonghost tn s t0` mp_tac >>
     qpat_assum `ld_nonghost (step_taint inst s ss tn) ss u` mp_tac >>
     pure_rewrite_tac[ld_nonghost_def] >> rpt strip_tac >> metis_tac[]) >>
  `u.vs_inst_idx = t.vs_inst_idx /\ SUC t.vs_inst_idx = p + LENGTH X` by decide_tac >>
  `g.lf_serial = f.lf_serial /\ g.lf_fn = f.lf_fn /\
   g.lf_supply = f.lf_supply /\ g.lf_Q = f.lf_Q /\
   g.lf_src = (ss with vs_inst_idx := SUC s.vs_inst_idx) /\
   g.lf_tgt = (u with vs_inst_idx := SUC t.vs_inst_idx) /\
   g.lf_tv = (step_taint inst s ss tn).t_var /\
   g.lf_H = set_prov f.lf_H [out] NONE` by simp[ADD1] >>
  `ld_vars P A g` by
    (qpat_assum `ld_vars P A (f with <|lf_src := ss; lf_tgt := u; lf_H := _; lf_tv := _|>)`
       (mp_tac o SRULE [ld_vars_def]) >> simp[ld_vars_def]) >>
  `g.lf_tgt.vs_alloca_next = u.vs_alloca_next /\
   g.lf_src.vs_alloca_next = s.vs_alloca_next` by simp[] >>
  `u.vs_alloca_next = s.vs_alloca_next + 32 * ld_charge (g::fs)` by
    (qpat_assum `!j. j < LENGTH (g::fs) ==> _` (qspec_then `0` mp_tac) >>
     simp_tac (srw_ss()) [] >> strip_tac >> decide_tac) >>
  `dyn_floor C vs < dimword (:256) ==> c + 32 <= dyn_floor C vs` by
    suspend "floor" >>
  `ld_dyn_agree (dyn_floor C vs) (step_taint inst s ss tn).t_mem
     ss.vs_memory u.vs_memory` by suspend "dynamic" >>
  `ld_ghost_ok (dyn_floor C vs) A g.lf_H (step_prov PG G inst ss)` by
    (drule ld_sync_ghosts >> simp[NoAsms] >> strip_tac >>
     qpat_assum `g.lf_H = _` (fn th => pure_rewrite_tac[th]) >>
     drule_then irule ld_ghost_ok_step_fixed >> metis_tac[]) >>
  `!next. active_inst fn next g.lf_src ==>
       ld_sync lo P C vs stk PG (step_prov PG G inst ss) (step_taint inst s ss tn)
         fn next g.lf_src g.lf_tgt A (g::fs) N` by suspend "successor" >>
  `g = f with <|lf_src := ss with vs_inst_idx := SUC s.vs_inst_idx;
                lf_tgt := u with vs_inst_idx := SUC t.vs_inst_idx;
                lf_H := set_prov f.lf_H [out] NONE;
                lf_E := inst.inst_id INSERT f.lf_E;
                lf_tv := (step_taint inst s ss tn).t_var|>` by simp[ADD1, ADD_ASSOC] >>
  map_every (Q_TAC EXISTS_TAC) [`ss`,`v`,`c`] >>
  pop_assum (SUBST1_TAC o SYM) >>
  qpat_assum `g.lf_src = _` (SUBST1_TAC o SYM) >>
  qpat_assum `g.lf_tgt = _` (SUBST1_TAC o SYM) >>
  qpat_assum `(HD X).inst_id = ai` SUBST1_TAC >>
  qpat_assum `EVERY (ld_maps A) (g::fs)` (strip_assume_tac o REWRITE_RULE[EVERY_DEF]) >>
  qpat_assum `!i. ~(c <= i /\ i < c+32) ==> _`
    (assume_tac o PURE_REWRITE_RULE[DE_MORGAN_THM]) >>
  qpat_x_assum `g = _` kall_tac >>
  asm_rewrite_tac[]
QED

Resume ld_focus_dload_scratch_next[floor]:
  rewrite_tac[dyn_floor_def] >> reverse IF_CASES_TAC >- simp[] >> strip_tac >>
  `s.vs_initial_fmp = vs.vs_initial_fmp` by
    (drule ptrDisciplineEmptyTaintTheory.frame_reachable_initial_fmp >> simp[]) >>
  pop_assum (fn th => rewrite_tac[GSYM th]) >>
  qpat_assum `dload_headroom_ok C fn inst s` mp_tac >>
  pure_rewrite_tac[dload_headroom_ok_def, GSYM ctx_has_dalloca_def] >>
  qpat_assum `ctx_has_dalloca C` (fn th => rewrite_tac[th]) >>
  strip_tac >> decide_tac
QED

Resume ld_focus_dload_scratch_next[dynamic]:
  `ss.vs_memory = s.vs_memory /\ (step_taint inst s ss tn).t_mem = tn.t_mem` by
    (drule_all ld_dload_memory_frame >> simp[]) >>
  drule ld_sync_dyn_agree >> strip_tac >>
  qpat_assum `ss.vs_memory = _` (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `(step_taint inst s ss tn).t_mem = _` (fn th => pure_rewrite_tac[th]) >>
  qpat_x_assum `ld_dyn_agree (dyn_floor C vs) tn.t_mem _ _` mp_tac >>
  pure_rewrite_tac[ld_dyn_agree_def] >> disch_tac >> qx_gen_tac `i` >> strip_tac >>
  `dyn_floor C vs < dimword (:256)` by decide_tac >>
  `~(c <= i /\ i < c+32)` by
    (qpat_assum `dyn_floor C vs < _ ==> _` mp_tac >> decide_tac) >>
  qpat_assum `!i. ~(c <= i /\ i < c+32) ==> _` (qspec_then `i` mp_tac) >> simp[]
QED

Resume ld_focus_dload_scratch_next[successor]:
  qx_gen_tac `next` >> strip_tac >>
  `active_inst fn next (ss with vs_inst_idx := SUC s.vs_inst_idx)` by
    (qpat_assum `g.lf_src = _` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  `g.lf_src.vs_inst_idx = SUC s.vs_inst_idx /\
   g.lf_tgt.vs_inst_idx = p + LENGTH X` by simp[ADD1] >>
  `?Y. ld_envelope f.lf_supply fn g.lf_src g.lf_src.vs_inst_idx Y
         g.lf_tgt.vs_inst_idx` by
    (drule_all ld_envelope_source_next >> asm_rewrite_tac[]) >>
  `frame_reachable vs C stk PG (step_prov PG G inst ss)
      (step_taint inst s ss tn) fn next g.lf_src` by
    (asm_rewrite_tac[] >> irule frame_reachable_next >> metis_tac[]) >>
  `g.lf_src.vs_current_bb = g.lf_tgt.vs_current_bb /\
   g.lf_src.vs_prev_bb = g.lf_tgt.vs_prev_bb` by
    (drule ld_sync_control >> simp[] >> metis_tac[]) >>
  `ld_memory lo A (step_taint inst s ss tn) g.lf_src g.lf_tgt` by
    (qpat_assum `g.lf_src = _` SUBST1_TAC >>
     qpat_assum `g.lf_tgt = _` SUBST1_TAC >>
     qpat_assum `ld_memory lo A (step_taint inst s ss tn) ss u` mp_tac >>
     simp[NoAsms, ld_memory_def] >> strip_tac >> first_assum ACCEPT_TAC) >>
  `ld_nonghost (step_taint inst s ss tn) g.lf_src g.lf_tgt` by
    (qpat_assum `g.lf_src = _` SUBST1_TAC >>
     qpat_assum `g.lf_tgt = _` SUBST1_TAC >>
     qpat_assum `ld_nonghost (step_taint inst s ss tn) ss u` mp_tac >>
     SIMP_TAC (srw_ss()) [ld_nonghost_def] >> strip_tac >> rpt conj_tac >> metis_tac[]) >>
  `ld_dyn_agree (dyn_floor C vs) (step_taint inst s ss tn).t_mem
      g.lf_src.vs_memory g.lf_tgt.vs_memory` by
    (qpat_assum `g.lf_src = _` SUBST1_TAC >>
     qpat_assum `g.lf_tgt = _` SUBST1_TAC >>
     qpat_assum `ld_dyn_agree (dyn_floor C vs) _ ss.vs_memory u.vs_memory` mp_tac >>
     simp[NoAsms]) >>
  rpt (qpat_x_assum `g = _` kall_tac) >>
  qpat_x_assum `g.lf_src = _` kall_tac >>
  qpat_x_assum `g.lf_tgt = _` kall_tac >>
  drule ld_sync_scratch_reconstruct >> disch_then irule >> asm_rewrite_tac[] >>
  Q_TAC EXISTS_TAC `Y` >> gvs[]
QED

Finalise ld_focus_dload_scratch_next

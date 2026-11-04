(* Original cached ALLOCA: requested sizes are irrelevant on cache hits. *)
Theory lowerDloadSafetyAllocation
Ancestors
  lowerDloadSafetyRelation lowerDloadSafetyAdvance lowerDloadSafetyUpdates
  lowerDloadConfiguredOrigins
  venomExecSemantics ptrDiscipline lowerDloadSafetyKernel
  venomState venomInst memLocDefs codegenRel finite_map pred_set

Theorem ld_cached_alloca_pair:
  ld_maps A f /\ inst.inst_outputs = [out] /\
  FLOOKUP f.lf_src.vs_allocas inst.inst_id = SOME (b,n) ==>
  ?c. FLOOKUP A (f.lf_serial,inst.inst_id) = SOME (b,c,n) /\
    FLOOKUP f.lf_tgt.vs_allocas inst.inst_id = SOME (c,n) /\
    exec_alloca inst f.lf_src szS = OK (update_var out (n2w b) f.lf_src) /\
    exec_alloca inst f.lf_tgt szT = OK (update_var out (n2w c) f.lf_tgt) /\
    ld_maps A (f with <|lf_src := update_var out (n2w b) f.lf_src;
                        lf_tgt := update_var out (n2w c) f.lf_tgt|>)
Proof
  strip_tac >> drule_all ld_maps_original >> strip_tac >>
  qexists_tac `c` >> simp[exec_alloca_def] >>
  irule ld_maps_cached_original >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`b`,`inst`,`n`,`szS`] >> simp[exec_alloca_def]
QED

Theorem ld_alloca_step:
  inst.inst_opcode = ALLOCA ==>
  (step_inst fuel C inst s = OK ss <=>
   ?sz. inst.inst_operands = [Lit sz] /\ exec_alloca inst s sz = OK ss)
Proof
  strip_tac >> simp[step_inst_non_invoke, Once step_inst_base_def] >>
  namedCases_on `inst.inst_operands` ["", "operand rest"] >> simp[] >>
  Cases_on `rest` >> simp[] >> Cases_on `operand` >> simp[]
QED

(* Shared output boundary: neither cache status nor frontier is relevant. *)
Theorem ld_vars_alloca_output:
  ld_vars P A f /\ MEM out (fn_ir_vars f.lf_fn) /\
  out IN fn_pv P f.lf_fn /\ FLOOKUP A k = SOME (b,c,n) ==>
  ld_vars P A
    (f with <|lf_src := update_var out (n2w b) f.lf_src;
              lf_tgt := update_var out (n2w c) f.lf_tgt;
              lf_H := f.lf_H |+ (out,k);
              lf_tv := f.lf_tv |+ (out,{})|>)
Proof
  strip_tac >>
  simp[update_var_def] >>
  irule (SRULE [set_prov_def] (Q.INST [`q` |-> `SOME k`] ld_vars_write)) >>
  simp[FLOOKUP_UPDATE] >> strip_tac >>
  pure_rewrite_tac [ld_wordrel_def, optionTheory.option_CLAUSES] >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  qexistsl_tac [`b`,`c`,`n`] >>
  asm_rewrite_tac [] >>
  pure_once_rewrite_tac [wordsTheory.WORD_ADD_COMM] >>
  rewrite_tac [wordsTheory.WORD_ADD_SUB]
QED

Theorem ld_alloca_prov_output:
  inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [out] /\
  FLOOKUP ss.vs_allocas inst.inst_id = SOME (b,n) /\
  FLOOKUP A k = SOME (b,c,n) ==>
  step_prov PG (ld_erase A o_f H) inst ss =
    ld_erase A o_f (H |+ (out,k))
Proof
  simp[step_prov_def, out_prov_def, GSYM ld_erase_set_prov,
       set_prov_def, ld_erase_def]
QED

Theorem ld_cached_alloca_taint:
  inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit sz] /\
  inst.inst_outputs = [out] ==>
  step_taint inst s (update_var out x s) tn =
    tn with t_var := tn.t_var |+ (out,{})
Proof
  strip_tac >>
  simp[step_taint_def, out_taint_def, mem_taint_def, update_var_def,
       new_site_bytes_def, step_writes_def, range_bytes_def,
       source_memory_write_ranges_def, written_taint_def,
       store_taint_def, adopt_reset_def, imm_taint_def,
       set_var_taint_def, eval_operand_def, FLOOKUP_DEF,
       taint_component_equality] >>
  SET_TAC[]
QED

Theorem ld_cached_alloca_effect:
  ld_maps A f /\ ld_vars P A f /\ f.lf_tv = tn.t_var /\
  ld_memory lo A tn f.lf_src f.lf_tgt /\
  ld_nonghost tn f.lf_src f.lf_tgt /\
  FRANGE f.lf_H SUBSET FDOM A /\
  MEM out (fn_ir_vars f.lf_fn) /\ out IN fn_pv P f.lf_fn /\
  inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [out] /\
  FLOOKUP f.lf_src.vs_allocas inst.inst_id = SOME (b,n) /\
  step_inst fuel C' inst f.lf_tgt = OK ts ==>
  ?c ss.
    step_inst fuel C inst f.lf_src = OK ss /\
    ss = update_var out (n2w b) f.lf_src /\
    ts = update_var out (n2w c) f.lf_tgt /\
    FLOOKUP A (f.lf_serial,inst.inst_id) = SOME (b,c,n) /\
    step_prov PG (ld_erase A o_f f.lf_H) inst ss =
      ld_erase A o_f (f.lf_H |+ (out,(f.lf_serial,inst.inst_id))) /\
    ld_vars P A (f with <|lf_src := ss; lf_tgt := ts;
      lf_H := f.lf_H |+ (out,(f.lf_serial,inst.inst_id));
      lf_tv := (step_taint inst f.lf_src ss tn).t_var|>) /\
    ld_memory lo A (step_taint inst f.lf_src ss tn) ss ts /\
    ld_nonghost (step_taint inst f.lf_src ss tn) ss ts /\
    FRANGE (f.lf_H |+ (out,(f.lf_serial,inst.inst_id))) SUBSET FDOM A
Proof
  strip_tac >>
  drule_all ld_alloca_step >> strip_tac >> gvs[] >>
  drule_all ld_cached_alloca_pair >>
  disch_then (strip_assume_tac o Q.ISPECL [`sz:bytes32`,`sz:bytes32`]) >>
  gvs[] >>
  `step_taint inst f.lf_src (update_var out (n2w b) f.lf_src) tn =
    tn with t_var := tn.t_var |+ (out,{})` by
      (irule ld_cached_alloca_taint >> simp[]) >>
  simp[ld_alloca_step] >>
  conj_tac >- (irule (SRULE [] ld_alloca_prov_output) >> simp[update_var_def] >> metis_tac[]) >>
  conj_tac >- (qpat_x_assum `f.lf_tv = tn.t_var` (SUBST1_TAC o SYM) >>
               irule ld_vars_alloca_output >> simp[] >> metis_tac[]) >>
  simp[ld_memory_update_var, ld_nonghost_update_var] >>
  simp[ld_memory_def, ld_nonghost_def] >>
  conj_tac >- gvs[FLOOKUP_DEF] >>
  irule SUBSET_TRANS >> qexists_tac `FRANGE f.lf_H` >>
  simp[] >> simp[SUBSET_DEF, IN_FRANGE, DOMSUB_FAPPLY_THM] >>
  metis_tac[]
QED

Theorem ld_cached_alloca_advance:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\
  inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [out] /\
  MEM out (fn_ir_vars fn) /\ out IN fn_pv P fn /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,n) /\
  ld_envelope f.lf_supply fn s s.vs_inst_idx [inst] p /\
  t.vs_inst_idx = p /\ step_inst fuel C' inst t = OK ts /\
  active_inst fn next ((update_var out (n2w b) s) with
                       vs_inst_idx := SUC s.vs_inst_idx) /\
  (?Y. ld_envelope f.lf_supply fn
        ((update_var out (n2w b) s) with vs_inst_idx := SUC s.vs_inst_idx)
        (SUC s.vs_inst_idx) Y (SUC p)) ==>
  ?ss g.
    step_inst fuel C inst s = OK ss /\
    ss = update_var out (n2w b) s /\
    g = f with <|lf_src := ss with vs_inst_idx := SUC s.vs_inst_idx;
                 lf_tgt := ts with vs_inst_idx := SUC p;
                 lf_H := f.lf_H |+ (out,(f.lf_serial,inst.inst_id));
                 lf_tv := (step_taint inst s ss tn).t_var|> /\
    ld_sync lo P C vs0 stk PG (step_prov PG G inst ss)
      (step_taint inst s ss tn) fn next
      (ss with vs_inst_idx := SUC s.vs_inst_idx)
      (ts with vs_inst_idx := SUC p) A (g::fs) N /\
    ld_global lo A (g::fs)
Proof
  strip_tac >>
  drule ld_sync_active >> simp[] >> strip_tac >>
  drule ld_sync_ghosts >> simp[] >> strip_tac >>
  drule ld_sync_memory >> strip_tac >>
  `FRANGE f.lf_H SUBSET FDOM A` by
    (simp[SUBSET_DEF] >> rpt strip_tac >>
     irule ld_global_selected >> qexistsl_tac [`f`,`f::fs`,`lo`] >> simp[]) >>
  qpat_x_assum `f.lf_src = s` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `f.lf_tgt = t` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `f.lf_fn = fn` (SUBST_ALL_TAC o SYM) >>
  drule_all ld_cached_alloca_effect >>
  disch_then (qspecl_then [`PG`,`C`] strip_assume_tac) >>
  `frame_reachable vs0 C stk PG (step_prov PG G inst ss)
     (step_taint inst f.lf_src ss tn) f.lf_fn next
     (ss with vs_inst_idx := SUC f.lf_src.vs_inst_idx)` by
    (irule frame_reachable_next >> drule ld_sync_source >>
     simp[is_terminator_def] >> metis_tac[]) >>
  qpat_assum `ld_vars P A (f with <|lf_src := ss; lf_tgt := ts; lf_H := _; lf_tv := _|>)`
    (assume_tac o MATCH_MP
      (Q.INST [`i` |-> `SUC f.lf_src.vs_inst_idx`, `j` |-> `SUC p`]
        (iffRL ld_vars_inst_indices))) >>
  qpat_x_assum `!j. j < LENGTH stk ==> _` kall_tac >>
  qpat_x_assum `ld_maps A f` kall_tac >>
  qpat_x_assum `ld_vars P A f` kall_tac >>
  qpat_x_assum `ld_intervals lo f.lf_src` kall_tac >>
  qpat_x_assum `ld_intervals lo f.lf_tgt` kall_tac >>
  drule ld_sync_control >> strip_tac >>
  gvs[] >> drule ld_sync_head_update >> disch_then drule >>
  disch_then irule >> simp[] >>
  gvs[update_var_def] >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (qexists_tac `f.lf_H |+ (out,(f.lf_serial,inst.inst_id))` >>
      simp[] >> gvs[SUBSET_DEF] >> metis_tac[]) >>
  gvs[ld_memory_def, ld_nonghost_def] >> first_assum ACCEPT_TAC
QED

(* A fresh identity cannot change any supported old provenance. *)
Theorem ld_erase_fresh_update:
  k NOTIN FDOM A /\ a IN FDOM A ==>
  ld_erase (A |+ (k,v)) a = ld_erase A a
Proof
  rpt strip_tac >> `a <> k` by metis_tac[] >>
  simp[ld_erase_def, FLOOKUP_UPDATE]
QED

Theorem ld_erase_fresh_compose:
  k NOTIN FDOM A /\ FRANGE H SUBSET FDOM A ==>
  ld_erase (A |+ (k,v)) o_f H = ld_erase A o_f H
Proof
  strip_tac >> simp[fmap_eq_flookup, FLOOKUP_o_f] >> gen_tac >>
  Cases_on `FLOOKUP H x` >> simp[] >>
  irule ld_erase_fresh_update >> simp[] >>
  metis_tac[SUBSET_DEF, FRANGE_FLOOKUP]
QED

Theorem ld_erase_fresh_params:
  k NOTIN FDOM A /\ (!a. MEM (SOME a) Q ==> a IN FDOM A) ==>
  MAP (OPTION_MAP (ld_erase (A |+ (k,v)))) Q =
  MAP (OPTION_MAP (ld_erase A)) Q
Proof
  strip_tac >> irule listTheory.MAP_CONG >> simp[] >>
  rpt strip_tac >> Cases_on `x` >> simp[] >>
  irule ld_erase_fresh_update >> metis_tac[]
QED

Theorem ld_vars_fresh_update:
  k NOTIN FDOM A /\ ld_vars P A f ==>
  ld_vars P (A |+ (k,v)) f
Proof
  simp[ld_vars_def] >> strip_tac >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      first_x_assum (drule_all_then mp_tac) >>
      Cases_on `retpc_var f.lf_fn v'` >> simp[] >>
      Cases_on `FLOOKUP f.lf_H v'` >> simp[] >>
      strip_tac >> irule ld_wordrel_fresh_update >> simp[]) >>
  rpt strip_tac >> irule ld_wordrel_fresh_update >> simp[]
QED

Theorem ld_maps_other_serial_update:
  f.lf_serial <> FST k /\ ld_maps A f ==>
  ld_maps (A |+ (k,v)) f
Proof
  Cases_on `k` >> strip_tac >> gvs[ld_maps_def, FLOOKUP_UPDATE] >>
  first_x_assum ACCEPT_TAC
QED

Theorem ld_slots_absent_head:
  FDOM A = ld_slots A (f::frames) /\
  (!g. MEM g frames ==> g.lf_serial <> f.lf_serial) /\
  FLOOKUP f.lf_src.vs_allocas aid = NONE ==>
  (f.lf_serial,aid) NOTIN FDOM A
Proof
  strip_tac >> simp[Once ld_slots_cons] >>
  gvs[ld_slots_def] >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem ld_maps_absent_original:
  ld_maps A f /\ FLOOKUP f.lf_src.vs_allocas aid = NONE /\
  (!d. ~ld_private f d aid) ==>
  FLOOKUP f.lf_tgt.vs_allocas aid = NONE
Proof
  strip_tac >> Cases_on `FLOOKUP f.lf_tgt.vs_allocas aid` >> simp[] >>
  PairCases_on `x` >> gvs[ld_maps_def] >>
  first_x_assum drule >> simp[] >> metis_tac[]
QED

Theorem ld_frames_fresh_update:
  k NOTIN FDOM A /\
  EVERY (\f. f.lf_serial <> FST k /\ ld_maps A f /\ ld_vars P A f) frames ==>
  EVERY (\f. ld_maps (A |+ (k,v)) f /\ ld_vars P (A |+ (k,v)) f) frames
Proof
  simp[listTheory.EVERY_MEM] >> rpt strip_tac >>
  metis_tac[ld_maps_other_serial_update, ld_vars_fresh_update]
QED

Theorem ld_private_supply_bound:
  ld_private f d ai ==> f.lf_supply.irs_next_inst <= ai
Proof
  simp[ld_private_def] >> rpt strip_tac >> gvs[] >>
  `f.lf_supply.irs_next_inst <=
    (SND (lower_dload_blocks_supply f.lf_supply
      (TAKE bi f.lf_fn.fn_blocks))).irs_next_inst` by
    (Cases_on `lower_dload_blocks_supply f.lf_supply (TAKE bi f.lf_fn.fn_blocks)` >>
     drule lower_dload_blocks_supply_flat >>
     strip_tac >> drule lower_dload_insts_supply_prefix >> simp[]) >>
  `(SND (lower_dload_blocks_supply f.lf_supply
      (TAKE bi f.lf_fn.fn_blocks))).irs_next_inst <=
    (SND (lower_dload_insts_supply
      (SND (lower_dload_blocks_supply f.lf_supply (TAKE bi f.lf_fn.fn_blocks)))
      (TAKE j (EL bi f.lf_fn.fn_blocks).bb_instructions))).irs_next_inst` by
    (Cases_on `lower_dload_insts_supply
      (SND (lower_dload_blocks_supply f.lf_supply (TAKE bi f.lf_fn.fn_blocks)))
      (TAKE j (EL bi f.lf_fn.fn_blocks).bb_instructions)` >>
     drule lower_dload_insts_supply_prefix >> simp[]) >>
  gvs[lowerDloadDefsTheory.lower_dload_inst_supply_def,
      irSupplyTheory.fresh_inst_id_def, AllCaseEqs()] >>
  qmatch_goalsub_abbrev_tac `fresh_ir_var ui` >>
  Cases_on `fresh_ir_var ui` >> gvs[] >>
  rename1 `fresh_ir_var ui = (av,u1)` >>
  Cases_on `fresh_ir_var u1` >> gvs[] >>
  imp_res_tac irSupplyTheory.fresh_ir_var_contract >> gvs[] >> decide_tac
QED

Theorem ld_original_not_private:
  ir_supply_covers_fn f.lf_supply f.lf_fn /\
  MEM aid (fn_ir_inst_ids f.lf_fn) ==>
  !d. ~ld_private f d aid
Proof
  simp[venomFnScheduleRunnerTheory.ir_supply_covers_fn_def,
       listTheory.EVERY_MEM] >> rpt strip_tac >>
  drule ld_private_supply_bound >> strip_tac >>
  first_x_assum drule >> decide_tac
QED

Theorem ld_sync_absent_alloca_key:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::frames) N /\
  FLOOKUP s.vs_allocas aid = NONE ==>
  (f.lf_serial,aid) NOTIN FDOM A
Proof
  simp[ld_sync_def] >> strip_tac >>
  drule ld_slots_absent_head >>
  disch_then (qspec_then `aid` mp_tac) >>
  simp[] >> impl_tac >- (gvs[listTheory.MEM_MAP] >> metis_tac[]) >>
  simp[]
QED

Theorem ld_original_alloca_fresh:
  ld_maps A f /\ ir_supply_covers_fn f.lf_supply f.lf_fn /\
  MEM aid (fn_ir_inst_ids f.lf_fn) /\
  FLOOKUP f.lf_src.vs_allocas aid = NONE ==>
  (!d. ~ld_private f d aid) /\
  FLOOKUP f.lf_tgt.vs_allocas aid = NONE
Proof
  strip_tac >> `!d. ~ld_private f d aid` by
    (irule ld_original_not_private >> simp[]) >>
  simp[] >> irule ld_maps_absent_original >> simp[] >>
  qexists_tac `A` >> simp[]
QED

Theorem ld_global_fresh_erasures:
  ld_global lo A frames /\ k NOTIN FDOM A ==>
  EVERY (\f.
    ld_erase (A |+ (k,v)) o_f f.lf_H = ld_erase A o_f f.lf_H /\
    MAP (OPTION_MAP (ld_erase (A |+ (k,v)))) f.lf_Q =
      MAP (OPTION_MAP (ld_erase A)) f.lf_Q) frames
Proof
  simp[ld_global_def, listTheory.EVERY_MEM] >> rpt strip_tac
  >- (irule ld_erase_fresh_compose >> simp[SUBSET_DEF] >> metis_tac[]) >>
  irule ld_erase_fresh_params >> metis_tac[]
QED

Theorem ld_sync_original_site_fresh:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::frames) N /\
  ir_supply_covers_fn f.lf_supply fn /\
  FLOOKUP s.vs_allocas inst.inst_id = NONE ==>
  (f.lf_serial,inst.inst_id) NOTIN FDOM A /\
  (!d. ~ld_private f d inst.inst_id) /\
  FLOOKUP t.vs_allocas inst.inst_id = NONE
Proof
  strip_tac >>
  ` (f.lf_serial,inst.inst_id) NOTIN FDOM A` by
    (drule_all ld_sync_absent_alloca_key >> simp[]) >>
  drule ld_sync_active >> simp[] >> strip_tac >>
  drule ld_sync_source >> strip_tac >>
  `MEM inst.inst_id (fn_ir_inst_ids fn)` by
    (gvs[contextCodegenRelTheory.active_inst_def, irSupplyTheory.fn_ir_inst_ids_def,
      irSupplyTheory.block_ir_inst_ids_def,
      listTheory.MEM_FLAT, listTheory.MEM_MAP, PULL_EXISTS] >>
     metis_tac[listTheory.MEM_EL]) >>
  simp[] >>
  qpat_x_assum `f.lf_src = s` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `f.lf_tgt = t` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `f.lf_fn = fn` (SUBST_ALL_TAC o SYM) >>
  irule ld_original_alloca_fresh >> simp[] >> qexists_tac `A` >> simp[]
QED

Theorem ld_fresh_alloca_taint:
  inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit sz] /\
  inst.inst_outputs = [out] /\
  FLOOKUP s.vs_allocas inst.inst_id = NONE /\
  exec_alloca inst s sz = OK ss ==>
  step_taint inst s ss tn =
    tn with <| t_var := tn.t_var |+ (out,{});
               t_mem := tn.t_mem UNION
                 {i | s.vs_alloca_next <= i /\
                      i < s.vs_alloca_next + w2n sz} |>
Proof
  strip_tac >> gvs[exec_alloca_def] >>
  simp[step_taint_def, out_taint_def, mem_taint_def, update_var_def,
       new_site_bytes_def, step_writes_def, range_bytes_def,
       source_memory_write_ranges_def, written_taint_def,
       store_taint_def, adopt_reset_def, imm_taint_def,
       set_var_taint_def, eval_operand_def,
       taint_component_equality] >>
  AP_TERM_TAC >> simp[EXTENSION, FLOOKUP_UPDATE, AllCaseEqs()] >>
  rpt strip_tac >> eq_tac >> rpt strip_tac >> gvs[] >>
  metis_tac[FLOOKUP_DEF, optionTheory.NOT_NONE_SOME]
QED

Theorem ld_fresh_alloca_effect:
  ld_vars P A f /\ f.lf_tv = tn.t_var /\
  ld_memory lo A tn f.lf_src f.lf_tgt /\
  ld_nonghost tn f.lf_src f.lf_tgt /\
  FRANGE f.lf_H SUBSET FDOM A /\
  MEM out (fn_ir_vars f.lf_fn) /\ out IN fn_pv P f.lf_fn /\
  inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit sz] /\
  inst.inst_outputs = [out] /\
  FLOOKUP f.lf_src.vs_allocas inst.inst_id = NONE /\
  FLOOKUP f.lf_tgt.vs_allocas inst.inst_id = NONE /\
  (f.lf_serial,inst.inst_id) NOTIN FDOM A /\
  A' = A |+ ((f.lf_serial,inst.inst_id),
    (f.lf_src.vs_alloca_next,f.lf_tgt.vs_alloca_next,w2n sz)) /\
  exec_alloca inst f.lf_src sz = OK ss /\
  exec_alloca inst f.lf_tgt sz = OK ts ==>
  step_inst fuel C inst f.lf_src = OK ss /\
  step_inst fuel C' inst f.lf_tgt = OK ts /\
  step_prov PG (ld_erase A o_f f.lf_H) inst ss =
    ld_erase A' o_f (f.lf_H |+ (out,(f.lf_serial,inst.inst_id))) /\
  ld_vars P A' (f with <|lf_src := ss; lf_tgt := ts;
    lf_H := f.lf_H |+ (out,(f.lf_serial,inst.inst_id));
    lf_tv := (step_taint inst f.lf_src ss tn).t_var|>) /\
  ld_memory lo A' (step_taint inst f.lf_src ss tn) ss ts /\
  ld_nonghost (step_taint inst f.lf_src ss tn) ss ts /\
  FRANGE (f.lf_H |+ (out,(f.lf_serial,inst.inst_id))) SUBSET FDOM A'
Proof
  strip_tac >>
  `ld_vars P A' f` by (gvs[] >> irule ld_vars_fresh_update >> simp[]) >>
  `ld_erase A' o_f f.lf_H = ld_erase A o_f f.lf_H` by
    (gvs[] >> irule ld_erase_fresh_compose >> simp[]) >>
  `step_taint inst f.lf_src ss tn =
    tn with <|t_var := tn.t_var |+ (out,{});
      t_mem := tn.t_mem UNION {i | f.lf_src.vs_alloca_next <= i /\
        i < f.lf_src.vs_alloca_next + w2n sz}|>` by
    (irule ld_fresh_alloca_taint >> simp[]) >>
  simp[ld_alloca_step] >>
  conj_tac
  >- (gvs[exec_alloca_def, update_var_def, step_prov_def, out_prov_def,
          set_prov_def, FLOOKUP_UPDATE, ld_erase_def, FLOOKUP_o_f]) >>
  conj_tac
  >- (`ld_vars P A' (f with <|
         lf_src := update_var out (n2w f.lf_src.vs_alloca_next) f.lf_src;
         lf_tgt := update_var out (n2w f.lf_tgt.vs_alloca_next) f.lf_tgt;
         lf_H := f.lf_H |+ (out,(f.lf_serial,inst.inst_id));
         lf_tv := f.lf_tv |+ (out,{})|>)` by
        (irule ld_vars_alloca_output >> simp[FLOOKUP_UPDATE] >>
         qexists_tac `w2n sz` >> simp[FLOOKUP_UPDATE]) >>
      gvs[exec_alloca_def, update_var_def, FLOOKUP_UPDATE, ld_vars_def]) >>
  gvs[exec_alloca_def, update_var_def] >>
  conj_tac
  >- (irule ld_memory_new_slot >>
      conj_tac >- (simp[] >> rpt strip_tac >> decide_tac) >>
      qexists_tac `tn` >>
      gvs[ld_memory_def, SUBSET_DEF] >> first_x_assum ACCEPT_TAC) >>
  conj_tac >- gvs[ld_nonghost_def] >>
  simp[SUBSET_DEF, IN_FRANGE, DOMSUB_FAPPLY_THM] >>
  metis_tac[SUBSET_DEF, IN_FRANGE]
QED

Theorem ld_fresh_alloca_dispatch:
  inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [out] /\
  FLOOKUP s.vs_allocas inst.inst_id = NONE /\
  FLOOKUP t.vs_allocas inst.inst_id = NONE /\
  step_inst fuel C' inst t = OK ts ==>
  ?sz ss.
    inst.inst_operands = [Lit sz] /\
    step_inst fuel C inst s = OK ss /\
    exec_alloca inst s sz = OK ss /\ exec_alloca inst t sz = OK ts /\
    ss = update_var out (n2w s.vs_alloca_next)
      (s with <|vs_allocas := s.vs_allocas |+
        (inst.inst_id,(s.vs_alloca_next,w2n sz));
        vs_alloca_next := s.vs_alloca_next + w2n sz|>) /\
    ts = update_var out (n2w t.vs_alloca_next)
      (t with <|vs_allocas := t.vs_allocas |+
        (inst.inst_id,(t.vs_alloca_next,w2n sz));
        vs_alloca_next := t.vs_alloca_next + w2n sz|>)
Proof
  strip_tac >> drule_all ld_alloca_step >> strip_tac >>
  gvs[exec_alloca_def] >> simp[ld_alloca_step, exec_alloca_def]
QED

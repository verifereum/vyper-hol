(* Original cached ALLOCA: requested sizes are irrelevant on cache hits. *)
Theory lowerDloadSafetyAllocation
Ancestors
  lowerDloadSafetyRelation lowerDloadSafetyAdvance lowerDloadSafetyUpdates
  lowerDloadConfiguredOrigins lowerDloadSafetyAmbient
  venomExecSemantics ptrDiscipline lowerDloadSafetyKernel
  venomState venomInst memLocDefs codegenRel finite_map pred_set
  lowerDloadSafetyLocations o1PassContract venomWf

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

val _ = if null (hyp ld_cached_alloca_pair) then ()
  else raise Fail "nonclosed ld_cached_alloca_pair";

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
  VALID (strip_tac >>
  drule_all ld_alloca_step >> strip_tac >> gvs[] >>
  (* Instantiate word widths before creating the implication assumption:
     type-instantiating an ASSUME theorem would change its hypothesis. *)
  drule_all (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``]
    ld_cached_alloca_pair) >>
  disch_then (qspecl_then [`sz:bytes32`,`sz:bytes32`] strip_assume_tac) >>
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
  metis_tac[])
QED

val _ = if null (hyp ld_cached_alloca_effect) then ()
  else raise Fail "nonclosed ld_cached_alloca_effect";

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

(* Allocation-changing reconstruction; the value/byte effect is supplied by
   ld_fresh_alloca_effect, independently of the next instruction location. *)
Theorem ld_fresh_alloca_structure:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\
  inst.inst_outputs = [out] /\
  FLOOKUP s.vs_allocas inst.inst_id = NONE /\
  FLOOKUP t.vs_allocas inst.inst_id = NONE /\
  (f.lf_serial,inst.inst_id) NOTIN FDOM A /\
  (!d. ~ld_private f d inst.inst_id) /\
  exec_alloca inst s sz = OK ss /\ exec_alloca inst t sz = OK ts /\
  A' = A |+ ((f.lf_serial,inst.inst_id),
    (s.vs_alloca_next,t.vs_alloca_next,w2n sz)) /\
  sn = ss with vs_inst_idx := SUC s.vs_inst_idx /\
  tt = ts with vs_inst_idx := SUC p /\
  g = f with <|lf_src := sn; lf_tgt := tt; lf_H := H'; lf_tv := tn'.t_var|> /\
  G' = ld_erase A' o_f H' /\ ld_vars P A' g /\
  ld_memory lo A' tn' sn tt /\ ld_nonghost tn' sn tt /\
  lo <= s.vs_alloca_next /\ lo <= t.vs_alloca_next /\
  FRANGE H' SUBSET FDOM A' ==>
  ld_maps A' g /\ ld_global lo A' (g::fs) /\
  FDOM A' = ld_slots A' (g::fs) /\
  EVERY (\h. ld_maps A' h /\ ld_vars P A' h) fs /\
  EVERY (\h. ld_erase A' o_f h.lf_H = ld_erase A o_f h.lf_H /\
    MAP (OPTION_MAP (ld_erase A')) h.lf_Q =
      MAP (OPTION_MAP (ld_erase A)) h.lf_Q) (f::fs) /\
  ld_intervals lo sn /\ ld_intervals lo tt /\
  (!j. j < LENGTH (g::fs) ==>
    (EL j (g::fs)).lf_tgt.vs_alloca_next =
    (EL j (g::fs)).lf_src.vs_alloca_next + 32 * ld_charge (DROP j (g::fs))) /\
  ld_charge (g::fs) <= ctx_dload_count C
Proof
  strip_tac >>
  `f.lf_src = s /\ f.lf_tgt = t /\ f.lf_fn = fn` by
    (drule ld_sync_active >> simp[]) >>
  `ld_maps A' (f with <|lf_src := ss; lf_tgt := ts|>)` by
    (gvs[] >> irule ld_maps_fresh_original >> simp[] >>
     drule ld_sync_active >> simp[]) >>
  `ld_intervals lo ss /\ ld_intervals lo ts` by
    (conj_tac >> irule ld_intervals_exec_alloca >>
     drule ld_sync_active >> simp[] >> metis_tac[]) >>
  `EVERY (\h. ld_erase A' o_f h.lf_H = ld_erase A o_f h.lf_H /\
    MAP (OPTION_MAP (ld_erase A')) h.lf_Q =
      MAP (OPTION_MAP (ld_erase A)) h.lf_Q) (f::fs)` by
    (qpat_x_assum `A' = _` SUBST1_TAC >>
     irule ld_global_fresh_erasures >> simp[] >> qexists_tac `lo` >> simp[]) >>
  `EVERY (\h. ld_maps A' h /\ ld_vars P A' h) fs` by
    (gvs[] >> irule ld_frames_fresh_update >> simp[] >>
     gvs[ld_sync_def, listTheory.EVERY_MEM, listTheory.MEM_MAP] >>
     metis_tac[]) >>
  `ld_global lo A' ((g with lf_H := f.lf_H)::fs)` by
    (irule ld_global_insert_head >>
     qexistsl_tac [`A`,`inst.inst_id`,`f`,`w2n sz`] >>
     gvs[exec_alloca_def, update_var_def]) >>
  `!source. ld_sites ((g with lf_H := f.lf_H)::fs) source =
      ld_sites (g::fs) source` by
    (gen_tac >> simp[NoAsms, ld_sites_def, EXTENSION] >>
     gen_tac >> PairCases_on `x` >> simp[] >>
     Cases_on `x0` >> simp[]) >>
  `g.lf_H = H'` by simp[] >>
  `ld_global lo A' (g::fs)` by
     (qpat_x_assum `g = _` kall_tac >>
      qpat_x_assum `A' = _` kall_tac >>
      qpat_x_assum `ld_global lo A' _` mp_tac >>
      simp[ld_global_def] >> strip_tac >>
      conj_tac >- (rpt gen_tac >> strip_tac >>
        qpat_x_assum `!source j aid b n. _ ==> _ /\ _` drule >> simp[]) >>
      conj_tac >- (rpt gen_tac >> strip_tac >>
        qpat_x_assum `!source j aid b n j' aid' b' n'. _` irule >>
        simp[] >> metis_tac[]) >>
      rpt gen_tac >> strip_tac >> gvs[SUBSET_DEF] >>
      metis_tac[]) >>
  `ld_slots A' (g::fs) = (f.lf_serial,inst.inst_id) INSERT ld_slots A (f::fs)` by
    (qpat_x_assum `A' = _` SUBST1_TAC >>
     irule ld_slots_insert_head >>
     gvs[exec_alloca_def, update_var_def, ld_sync_def, listTheory.MEM_MAP] >>
     metis_tac[]) >>
  `ld_maps A' g /\ ld_intervals lo sn /\ ld_intervals lo tt` by
    (conj_tac
     >- (qpat_x_assum `ld_maps _ (f with <|lf_src := ss; lf_tgt := ts|>)` mp_tac >>
         simp[ld_maps_def, ld_private_def] >> strip_tac >> asm_rewrite_tac[]) >>
     gvs[ld_intervals_def] >> rpt conj_tac >> first_x_assum ACCEPT_TAC) >>
  `g.lf_serial = f.lf_serial /\ g.lf_fn = fn /\
    g.lf_supply = f.lf_supply /\ g.lf_Q = f.lf_Q /\ g.lf_E = f.lf_E /\
    g.lf_src = sn /\ g.lf_tgt = tt /\ g.lf_tv = tn'.t_var /\
    sn.vs_alloca_next = s.vs_alloca_next + w2n sz /\
    tt.vs_alloca_next = t.vs_alloca_next + w2n sz /\
    sn.vs_current_bb = tt.vs_current_bb /\ sn.vs_prev_bb = tt.vs_prev_bb` by
    (drule ld_sync_control >> gvs[exec_alloca_def, update_var_def]) >>
  `!xs. ld_charge (g::xs) = ld_charge (f::xs)` by simp[ld_charge_def] >>
  qpat_x_assum `g = _` kall_tac >>
  qpat_x_assum `sn = _` kall_tac >> qpat_x_assum `tt = _` kall_tac >>
  `FDOM A' = (f.lf_serial,inst.inst_id) INSERT FDOM A` by simp[] >>
  qpat_x_assum `A' = _` kall_tac >>
  qpat_x_assum `ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N` mp_tac >>
  simp[ld_sync_def] >> strip_tac >>
  fs[listTheory.EVERY_MEM] >> simp[] >>
  gen_tac >> Cases_on `j`
  >- (qpat_x_assum `!j. _ ==> (EL j (f::fs)).lf_tgt.vs_alloca_next = _`
        (qspec_then `0` mp_tac) >> simp[]) >>
  qpat_x_assum `!j. _ ==> (EL j (f::fs)).lf_tgt.vs_alloca_next = _`
    (qspec_then `SUC n` mp_tac) >> simp[]
QED

Theorem ld_sync_fresh_alloca_update:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\
  inst.inst_outputs = [out] /\
  FLOOKUP s.vs_allocas inst.inst_id = NONE /\
  FLOOKUP t.vs_allocas inst.inst_id = NONE /\
  (f.lf_serial,inst.inst_id) NOTIN FDOM A /\
  (!d. ~ld_private f d inst.inst_id) /\
  exec_alloca inst s sz = OK ss /\ exec_alloca inst t sz = OK ts /\
  A' = A |+ ((f.lf_serial,inst.inst_id),
    (s.vs_alloca_next,t.vs_alloca_next,w2n sz)) /\
  sn = ss with vs_inst_idx := SUC s.vs_inst_idx /\
  tt = ts with vs_inst_idx := SUC p /\
  g = f with <|lf_src := sn; lf_tgt := tt; lf_H := H'; lf_tv := tn'.t_var|> /\
  frame_reachable vs0 C stk PG G' tn' fn next sn /\ active_inst fn next sn /\
  G' = ld_erase A' o_f H' /\ ld_vars P A' g /\
  ld_memory lo A' tn' sn tt /\ ld_nonghost tn' sn tt /\
  lo <= s.vs_alloca_next /\ lo <= t.vs_alloca_next /\
  (?Y. ld_envelope f.lf_supply fn sn sn.vs_inst_idx Y tt.vs_inst_idx) /\
  FRANGE H' SUBSET FDOM A' ==>
  ld_sync lo P C vs0 stk PG G' tn' fn next sn tt A' (g::fs) N /\
  ld_global lo A' (g::fs)
Proof
  strip_tac >>
  drule_all ld_fresh_alloca_structure >> strip_tac >>
  `f.lf_src = s /\ f.lf_tgt = t /\ f.lf_fn = fn` by
    (drule ld_sync_active >> simp[]) >>
  `sn.vs_current_bb = tt.vs_current_bb /\ sn.vs_prev_bb = tt.vs_prev_bb` by
    (drule ld_sync_control >> gvs[exec_alloca_def, update_var_def]) >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  `g.lf_serial = f.lf_serial /\ g.lf_fn = fn /\
    g.lf_supply = f.lf_supply /\ g.lf_Q = f.lf_Q /\ g.lf_E = f.lf_E /\
    g.lf_src = sn /\ g.lf_tgt = tt /\ g.lf_H = H' /\ g.lf_tv = tn'.t_var` by simp[] >>
  qpat_x_assum `g = _` kall_tac >>
  qpat_x_assum `sn = _` kall_tac >> qpat_x_assum `tt = _` kall_tac >>
  qpat_x_assum `A' = _` kall_tac >>
  qpat_x_assum `ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N` mp_tac >>
  simp[ld_sync_def] >> strip_tac >>
  fs[listTheory.EVERY_MEM] >> simp[] >>
  conj_tac
  >- (gen_tac >> Cases_on `j` >> simp[]
      >- metis_tac[] >>
      qpat_x_assum `!j. _ ==> ?X. ld_envelope _ _ _ _ X _`
        (qspec_then `SUC n` mp_tac) >> simp[]) >>
  rpt strip_tac >>
  `MEM (EL j fs) fs` by (irule listTheory.EL_MEM >> simp[]) >>
  qpat_x_assum `!h. MEM h fs ==> ld_erase _ o_f _ = _ /\ _` drule >>
  simp[]
QED

Theorem ld_fresh_alloca_advance:
  o1_ctx_shape C /\ ptr_discipline lo C vs0 /\
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\ ir_supply_covers_fn f.lf_supply fn /\
  inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [out] /\
  inst.inst_operands = [Lit sz] /\
  MEM out (fn_ir_vars fn) /\ out IN fn_pv P fn /\
  FLOOKUP s.vs_allocas inst.inst_id = NONE /\
  step_inst fuel C' inst t = OK ts /\
  ss = update_var out (n2w s.vs_alloca_next)
    (s with <|vs_allocas := s.vs_allocas |+
      (inst.inst_id,(s.vs_alloca_next,w2n sz));
      vs_alloca_next := s.vs_alloca_next + w2n sz|>) /\
  sn = ss with vs_inst_idx := SUC s.vs_inst_idx /\
  tt = ts with vs_inst_idx := SUC p /\
  A' = A |+ ((f.lf_serial,inst.inst_id),
    (s.vs_alloca_next,t.vs_alloca_next,w2n sz)) /\
  g = f with <|lf_src := sn; lf_tgt := tt;
    lf_H := f.lf_H |+ (out,(f.lf_serial,inst.inst_id));
    lf_tv := (step_taint inst s ss tn).t_var|> /\
  active_inst fn next sn /\
  (?Y. ld_envelope f.lf_supply fn sn sn.vs_inst_idx Y tt.vs_inst_idx) ==>
  step_inst fuel C inst s = OK ss /\
  ld_sync lo P C vs0 stk PG (step_prov PG G inst ss)
    (step_taint inst s ss tn) fn next sn tt A' (g::fs) N /\
  ld_global lo A' (g::fs)
Proof
  strip_tac >>
  `lo <= t.vs_alloca_next` by
    (irule ld_sync_frontier_lower_bound >> simp[] >> metis_tac[]) >>
  `lo <= s.vs_alloca_next` by
    (drule ld_sync_source >> strip_tac >>
     drule_all ld_frame_raw_reachable >> strip_tac >>
     drule lowerDloadFrontierTheory.ld_raw_reachable_frontier >> gvs[ptr_discipline_def]) >>
  drule_all ld_sync_original_site_fresh >> strip_tac >>
  drule ld_sync_active >> simp[] >> strip_tac >>
  drule ld_sync_ghosts >> simp[] >> strip_tac >>
  drule ld_sync_memory >> strip_tac >>
  `FRANGE f.lf_H SUBSET FDOM A` by
    (simp[SUBSET_DEF] >> rpt strip_tac >>
     irule ld_global_selected >> qexistsl_tac [`f`,`f::fs`,`lo`] >> simp[]) >>
  `exec_alloca inst s sz = OK ss /\ exec_alloca inst t sz = OK ts` by
    (conj_tac >- gvs[exec_alloca_def] >>
     qpat_x_assum `step_inst fuel C' inst t = OK ts` mp_tac >>
     simp[ld_alloca_step]) >>
  qpat_x_assum `f.lf_src = s` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `f.lf_tgt = t` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `f.lf_fn = fn` (SUBST_ALL_TAC o SYM) >>
  drule_all ld_fresh_alloca_effect >>
  disch_then (qspecl_then [`fuel`,`PG`,`C'`,`C`] strip_assume_tac) >>
  `frame_reachable vs0 C stk PG (step_prov PG G inst ss)
     (step_taint inst f.lf_src ss tn) f.lf_fn next sn` by
    (qpat_assum `sn = _` SUBST1_TAC >>
     irule frame_reachable_next >> drule ld_sync_source >> strip_tac >>
     gvs[is_terminator_def] >> qexists_tac `fuel` >> simp[]) >>
  `ld_vars P A' g` by
    (gvs[ld_vars_def] >> first_x_assum ACCEPT_TAC) >>
  `ld_memory lo A' (step_taint inst f.lf_src ss tn) sn tt /\
   ld_nonghost (step_taint inst f.lf_src ss tn) sn tt` by
    (gvs[ld_memory_def, ld_nonghost_def] >>
     rpt conj_tac >> first_x_assum ACCEPT_TAC) >>
  qpat_assum `ss = _` (SUBST1_TAC o SYM) >>
  qpat_assum `sn = _` (SUBST1_TAC o SYM) >>
  qpat_assum `tt = _` (SUBST1_TAC o SYM) >>
  qpat_assum `A' = _` (SUBST1_TAC o SYM) >>
  qpat_assum `g = _` (SUBST1_TAC o SYM) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `PG = _` (SUBST1_TAC o SYM) >>
  qpat_assum `G = _` (SUBST1_TAC o SYM) >>
  drule (INST_TYPE [alpha |-> ``:256``] ld_sync_fresh_alloca_update) >>
  disch_then drule >>
  disch_then irule >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (qexists_tac `Y` >> first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (qexists_tac `out` >> first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (qexistsl_tac [`p`,`ss`,`sz`,`ts`] >>
    rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >- (qexists_tac `f.lf_H |+ (out,(f.lf_serial,inst.inst_id))` >>
    conj_tac >- metis_tac[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* Exported allocation interfaces must be closed kernel theorems. *)
val _ = List.app (fn (name, th) =>
  if null (hyp th) then () else raise Fail ("nonclosed " ^ name))
  [("ld_fresh_alloca_structure", ld_fresh_alloca_structure),
   ("ld_sync_fresh_alloca_update", ld_sync_fresh_alloca_update),
   ("ld_cached_alloca_advance", ld_cached_alloca_advance),
   ("ld_fresh_alloca_advance", ld_fresh_alloca_advance)];

(* Cached original allocations also have an endpoint at the end of a block. *)
Theorem ld_cached_alloca_endpoint:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\ o1_ctx_shape C /\
  inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [out] /\
  MEM out (fn_ir_vars fn) /\ out IN fn_pv P fn /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,n) /\
  ld_envelope f.lf_supply fn s s.vs_inst_idx [inst] p /\
  t.vs_inst_idx = p /\ step_inst fuel C' inst t = OK ts ==>
  ?ss g.
    step_inst 0 C inst s = OK ss /\
    g = f with <|lf_src := ss with vs_inst_idx := SUC s.vs_inst_idx;
      lf_tgt := ts with vs_inst_idx := p + 1;
      lf_H := f.lf_H |+ (out,(f.lf_serial,inst.inst_id));
      lf_tv := (step_taint inst s ss tn).t_var|> /\
    step_prov PG G inst ss = ld_erase A o_f g.lf_H /\
    ld_vars P A g /\ ld_maps A g /\
    ld_memory lo A (step_taint inst s ss tn) ss ts /\
    ld_nonghost (step_taint inst s ss tn) ss ts /\
    ld_global lo A (g::fs) /\ FDOM A = ld_slots A (g::fs) /\
    EVERY (ld_maps A) fs /\
    (!next. active_inst fn next g.lf_src ==>
      ld_sync lo P C vs0 stk PG (step_prov PG G inst ss)
        (step_taint inst s ss tn) fn next g.lf_src g.lf_tgt A (g::fs) N)
Proof
  strip_tac >>
  drule ld_sync_active >> simp[] >> strip_tac >>
  drule ld_sync_ghosts >> simp[] >> strip_tac >>
  drule ld_sync_memory >> strip_tac >>
  `FRANGE f.lf_H SUBSET FDOM A` by
    (simp[SUBSET_DEF] >> rpt strip_tac >>
     irule ld_global_selected >> qexistsl [`f`,`f::fs`,`lo`] >> simp[]) >>
  qpat_x_assum `f.lf_src = s` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `f.lf_tgt = t` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `f.lf_fn = fn` (SUBST_ALL_TAC o SYM) >>
  drule_all ld_cached_alloca_effect >>
  disch_then (qspecl_then [`PG`,`C`] strip_assume_tac) >>
  `step_inst 0 C inst f.lf_src = OK ss` by
    gvs[step_inst_non_invoke] >>
  `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
   step_prov PG G inst ss =
     ld_erase A o_f (f.lf_H |+ (out,(f.lf_serial,inst.inst_id))) /\
   (!a. a IN FRANGE (f.lf_H |+ (out,(f.lf_serial,inst.inst_id))) ==>
      a IN FDOM A) /\
   ss.vs_allocas = f.lf_src.vs_allocas /\ ts.vs_allocas = f.lf_tgt.vs_allocas /\
   ss.vs_alloca_next = f.lf_src.vs_alloca_next /\
   ts.vs_alloca_next = f.lf_tgt.vs_alloca_next /\
   ss.vs_current_bb = f.lf_src.vs_current_bb /\
   ts.vs_current_bb = f.lf_tgt.vs_current_bb /\
   ss.vs_prev_bb = f.lf_src.vs_prev_bb /\
   ts.vs_prev_bb = f.lf_tgt.vs_prev_bb` by
    (gvs[update_var_def, is_terminator_def, SUBSET_DEF] >> metis_tac[]) >>
  qabbrev_tac `g = f with
    <|lf_src := ss with vs_inst_idx := SUC f.lf_src.vs_inst_idx;
      lf_tgt := ts with vs_inst_idx := p + 1;
      lf_H := f.lf_H |+ (out,(f.lf_serial,inst.inst_id));
      lf_tv := (step_taint inst f.lf_src ss tn).t_var|>` >>
  `ld_vars P A g /\ ld_maps A g /\
   ld_global lo A (g::fs) /\ FDOM A = ld_slots A (g::fs) /\
   EVERY (ld_maps A) fs /\
   (!next. active_inst f.lf_fn next g.lf_src ==>
     ld_sync lo P C vs0 stk PG (step_prov PG G inst ss)
       (step_taint inst f.lf_src ss tn) f.lf_fn next g.lf_src g.lf_tgt A (g::fs) N)` by
    (drule_all (SRULE [SUBSET_DEF] ld_nonallocating_endpoint) >>
     simp[Abbr `g`, update_var_def, is_terminator_def]) >>
  qexists `ss` >> gvs[Abbr `g`]
QED

Theorem ld_fresh_alloca_endpoint:
  o1_ctx_shape C /\ ptr_discipline lo C vs0 /\
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\ ir_supply_covers_fn f.lf_supply fn /\
  inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [out] /\
  inst.inst_operands = [Lit sz] /\
  MEM out (fn_ir_vars fn) /\ out IN fn_pv P fn /\
  FLOOKUP s.vs_allocas inst.inst_id = NONE /\
  ld_envelope f.lf_supply fn s s.vs_inst_idx [inst] p /\
  t.vs_inst_idx = p /\ step_inst fuel C' inst t = OK ts ==>
  ?ss Ar g.
    Ar = A |+ ((f.lf_serial,inst.inst_id),
      (s.vs_alloca_next,t.vs_alloca_next,w2n sz)) /\
    step_inst 0 C inst s = OK ss /\
    g.lf_serial = f.lf_serial /\ g.lf_supply = f.lf_supply /\
    g.lf_fn = f.lf_fn /\ g.lf_Q = f.lf_Q /\
    g.lf_src = (ss with vs_inst_idx := SUC s.vs_inst_idx) /\
    g.lf_tgt = (ts with vs_inst_idx := p + 1) /\
    g.lf_tv = (step_taint inst s ss tn).t_var /\
    step_prov PG G inst ss = ld_erase Ar o_f g.lf_H /\
    ld_vars P Ar g /\ ld_maps Ar g /\
    ld_memory lo Ar (step_taint inst s ss tn) ss ts /\
    ld_nonghost (step_taint inst s ss tn) ss ts /\
    ld_global lo Ar (g::fs) /\ FDOM Ar = ld_slots Ar (g::fs) /\
    EVERY (ld_maps Ar) fs /\
    (!next. active_inst fn next g.lf_src ==>
      ld_sync lo P C vs0 stk PG (step_prov PG G inst ss)
        (step_taint inst s ss tn) fn next g.lf_src g.lf_tgt Ar (g::fs) N)
Proof
  strip_tac >>
  `lo <= t.vs_alloca_next` by
    (irule ld_sync_frontier_lower_bound >> simp[] >> metis_tac[]) >>
  `lo <= s.vs_alloca_next` by
    (drule ld_sync_source >> strip_tac >>
     drule_all ld_frame_raw_reachable >> strip_tac >>
     drule lowerDloadFrontierTheory.ld_raw_reachable_frontier >> gvs[ptr_discipline_def]) >>
  drule_all ld_sync_original_site_fresh >> strip_tac >>
  drule ld_sync_active >> simp[] >> strip_tac >>
  drule ld_sync_ghosts >> simp[] >> strip_tac >>
  drule ld_sync_memory >> strip_tac >>
  `FRANGE f.lf_H SUBSET FDOM A` by
    (simp[SUBSET_DEF] >> rpt strip_tac >>
     irule ld_global_selected >> qexistsl [`f`,`f::fs`,`lo`] >> simp[]) >>
  `?ss. exec_alloca inst s sz = OK ss` by simp[exec_alloca_def] >>
  `exec_alloca inst t sz = OK ts` by
    (qpat_x_assum `step_inst fuel C' inst t = OK ts` mp_tac >>
     simp[ld_alloca_step]) >>
  qabbrev_tac `Ar = A |+ ((f.lf_serial,inst.inst_id),
    (s.vs_alloca_next,t.vs_alloca_next,w2n sz))` >>
  qpat_x_assum `f.lf_src = s` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `f.lf_tgt = t` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `f.lf_fn = fn` (SUBST_ALL_TAC o SYM) >>
  `Ar = A |+ ((f.lf_serial,inst.inst_id),
    (f.lf_src.vs_alloca_next,f.lf_tgt.vs_alloca_next,w2n sz))` by simp[Abbr `Ar`] >>
  drule_all ld_fresh_alloca_effect >>
  disch_then (qspecl_then [`0`,`PG`,`C'`,`C`] strip_assume_tac) >>
  qabbrev_tac `sn = ss with vs_inst_idx := SUC f.lf_src.vs_inst_idx` >>
  qabbrev_tac `tt = ts with vs_inst_idx := p + 1` >>
  qabbrev_tac `g = f with <|lf_src := sn; lf_tgt := tt;
    lf_H := f.lf_H |+ (out,(f.lf_serial,inst.inst_id));
    lf_tv := (step_taint inst f.lf_src ss tn).t_var|>` >>
  `ld_vars P Ar g /\
   ld_memory lo Ar (step_taint inst f.lf_src ss tn) sn tt /\
   ld_nonghost (step_taint inst f.lf_src ss tn) sn tt` by
    (gvs[Abbr `g`, Abbr `sn`, Abbr `tt`, ld_vars_def,
         ld_memory_def, ld_nonghost_def] >>
     rpt conj_tac >> first_x_assum ACCEPT_TAC) >>
  `ld_maps Ar g /\ ld_global lo Ar (g::fs) /\
   FDOM Ar = ld_slots Ar (g::fs) /\
   EVERY (\h. ld_maps Ar h /\ ld_vars P Ar h) fs` by
    suspend "structure" >>
  `!next. active_inst f.lf_fn next sn ==>
    ld_sync lo P C vs0 stk PG (step_prov PG G inst ss)
      (step_taint inst f.lf_src ss tn) f.lf_fn next sn tt Ar (g::fs) N` by
    suspend "continuation" >>
  qexistsl [`ss`,`g`] >>
  gvs[Abbr `g`, Abbr `sn`, Abbr `tt`, Abbr `Ar`, listTheory.EVERY_MEM]
QED

Resume ld_fresh_alloca_endpoint[structure]:
  qpat_x_assum `Abbrev (Ar = _)` kall_tac >>
  `sn = ss with vs_inst_idx := SUC f.lf_src.vs_inst_idx /\
   tt = ts with vs_inst_idx := SUC p /\
   g = f with <|lf_src := sn; lf_tgt := tt;
     lf_H := f.lf_H |+ (out,(f.lf_serial,inst.inst_id));
     lf_tv := (step_taint inst f.lf_src ss tn).t_var|> /\
   step_prov PG G inst ss =
     ld_erase Ar o_f (f.lf_H |+ (out,(f.lf_serial,inst.inst_id)))` by
    (rpt conj_tac
     >- simp[NoAsms, Abbr `sn`]
     >- simp[NoAsms, Abbr `tt`, arithmeticTheory.ADD1]
     >- simp[NoAsms, Abbr `g`]
     >> metis_tac[]) >>
  drule_all ld_fresh_alloca_structure >> strip_tac >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
Resume ld_fresh_alloca_endpoint[continuation]:
  gen_tac >> strip_tac >>
  qpat_x_assum `Abbrev (Ar = _)` kall_tac >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) f.lf_fn.fn_blocks)` by
    (drule_all ld_sync_fn_shape >>
     simp[o1_fn_shape_def, wf_function_def, fn_labels_def]) >>
  `ss.vs_current_bb = f.lf_src.vs_current_bb /\
   ss.vs_prev_bb = f.lf_src.vs_prev_bb` by
    gvs[exec_alloca_def, update_var_def] >>
  `active_inst f.lf_fn next (ss with vs_inst_idx := SUC f.lf_src.vs_inst_idx)` by
    fs[Abbr `sn`] >>
  `?Y. ld_envelope f.lf_supply f.lf_fn sn sn.vs_inst_idx Y tt.vs_inst_idx` by
    (drule_all ld_envelope_source_next >>
     simp[Abbr `sn`, Abbr `tt`, arithmeticTheory.ADD1]) >>
  `ss = update_var out (n2w f.lf_src.vs_alloca_next)
     (f.lf_src with <|vs_allocas := f.lf_src.vs_allocas |+
       (inst.inst_id,(f.lf_src.vs_alloca_next,w2n sz));
       vs_alloca_next := f.lf_src.vs_alloca_next + w2n sz|>)` by
    gvs[exec_alloca_def] >>
  `sn = ss with vs_inst_idx := SUC f.lf_src.vs_inst_idx /\
   tt = ts with vs_inst_idx := SUC p /\
   g = f with <|lf_src := sn; lf_tgt := tt;
     lf_H := f.lf_H |+ (out,(f.lf_serial,inst.inst_id));
     lf_tv := (step_taint inst f.lf_src ss tn).t_var|>` by
    (rpt conj_tac
     >- simp[NoAsms, Abbr `sn`]
     >- simp[NoAsms, Abbr `tt`, arithmeticTheory.ADD1]
     >> simp[NoAsms, Abbr `g`]) >>
  drule_all (SRULE [PULL_EXISTS] ld_fresh_alloca_advance) >>
  strip_tac >>
  qpat_x_assum `Abbrev (sn = _)` kall_tac >>
  qpat_x_assum `Abbrev (tt = _)` kall_tac >>
  qpat_x_assum `Abbrev (g = _)` kall_tac >> gvs[]
QED
Finalise ld_fresh_alloca_endpoint

val _ = List.app (fn th => if null (hyp th) then ()
  else raise Fail "allocation endpoint has hypotheses")
  [ld_cached_alloca_endpoint, ld_fresh_alloca_endpoint];

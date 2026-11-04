(* Original cached ALLOCA: requested sizes are irrelevant on cache hits. *)
Theory lowerDloadSafetyAllocation
Ancestors
  lowerDloadSafetyRelation lowerDloadSafetyAdvance lowerDloadSafetyUpdates
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

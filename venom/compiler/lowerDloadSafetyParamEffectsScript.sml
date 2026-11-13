(* PARAM transports selected identities, not numerically equal pointers. *)
Theory lowerDloadSafetyParamEffects
Ancestors
  lowerDloadSafetyKernel lowerDloadSafetyRelation lowerDloadSafetyUpdates lowerDloadSafetyValues
  lowerDloadPointerClosure ptrDiscipline venomState venomExecSemantics
  venomInst pointerConfinedDefs unitShapeDefs memLocDefs codegenRel
  contextCodegenRel finite_map list pred_set words While

Theorem ld_pointer_use_seed:
  MEM v vars ==> MEM v (pointer_use_vars fn vars)
Proof
  strip_tac >> simp[pointer_use_vars_def] >>
  qabbrev_tac `iterfn = \w:string list + string list.
    case pointer_use_step_step fn (OUTL w) of
      NONE => INR (OUTL w) | SOME vs => INL vs` >>
  qspecl_then [`ISL`, `iterfn`, `INL vars`] mp_tac
    (INST_TYPE [alpha |-> ``:string list + string list``] OWHILE_INV_IND
       |> Q.INST [`P` |-> `\s. case s of INL l => MEM v l | INR l => MEM v l`]) >>
  simp[] >> impl_tac
  >- (rpt strip_tac >> rename1 `ISL st` >> Cases_on `st` >>
      gvs[Abbr `iterfn`] >> Cases_on `pointer_use_step_step fn x` >>
      gvs[pointer_use_step_step_def, AllCaseEqs()] >> simp[]) >>
  strip_tac >> Cases_on `OWHILE ISL iterfn (INL vars)` >> simp[] >>
  Cases_on `x` >> gvs[]
QED

Theorem ld_ptr_roots_finite[local]:
  FINITE (ptr_roots P fn)
Proof
  irule SUBSET_FINITE_I >>
  qexists_tac `set (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn)))` >> simp[] >>
  simp[ptr_roots_def, alloca_roots_def, SUBSET_DEF, MEM_FLAT, MEM_MAP] >>
  rpt strip_tac >> gvs[inst_output_def, AllCaseEqs()] >>
  metis_tac[MEM]
QED

Theorem ld_param_selected_output[local]:
  MEM inst (fn_insts fn) /\ inst.inst_opcode = PARAM /\
  inst.inst_operands = [Lit idx] /\ inst.inst_outputs = [out] /\
  w2n idx IN P fn.fn_name ==>
  out IN fn_pv P fn
Proof
  strip_tac >> simp[fn_pv_def, pointer_derived_vars_def] >>
  irule ld_pointer_use_seed >> simp[MEM_SET_TO_LIST, ld_ptr_roots_finite] >>
  simp[ptr_roots_def] >> disj2_tac >>
  qexistsl_tac [`inst`, `idx`] >> simp[inst_output_def]
QED

Theorem ld_param_taint[local]:
  inst.inst_opcode = PARAM ==>
  step_taint inst s (update_var v x s) tn =
    tn with t_var := set_var_taint tn.t_var inst.inst_outputs {}
Proof
  strip_tac >>
  `written_taint tn inst s = {}` by
    (namedCases_on `inst.inst_operands` ["", "a rest"]
     >- simp[written_taint_def] >>
     namedCases_on `rest` ["", "b tail"]
     >- simp[written_taint_def] >>
     namedCases_on `tail` ["", "c more"]
     >- simp[written_taint_def] >>
     Cases_on `more` >> simp[written_taint_def]) >>
  simp[step_taint_def, out_taint_def, mem_taint_def, update_var_def,
       new_site_bytes_def, step_writes_def, range_bytes_def,
       source_memory_write_ranges_def, store_taint_def, adopt_reset_def,
       imm_taint_def, FLOOKUP_DEF, taint_component_equality] >>
  conj_tac >- SET_TAC[] >>
  namedCases_on `inst.inst_operands` ["", "a rest"] >- simp[] >>
  namedCases_on `rest` ["", "b tail"]
  >- (Cases_on `eval_operand a s` >> simp[]) >>
  namedCases_on `tail` ["", "c more"]
  >- (Cases_on `eval_operand a s` >> simp[]) >> simp[]
QED

Theorem ld_param_write[local]:
  ld_vars P A f /\ MEM inst (fn_insts f.lf_fn) /\
  inst.inst_opcode = PARAM /\ inst.inst_operands = [Lit idx] /\
  inst.inst_outputs = [out] /\ w2n idx < LENGTH f.lf_src.vs_params /\
  (!j a. j < LENGTH f.lf_Q /\ EL j f.lf_Q = SOME a ==> j IN P f.lf_fn.fn_name) ==>
  ld_vars P A (f with <|
    lf_src := update_var out (EL (w2n idx) f.lf_src.vs_params) f.lf_src;
    lf_tgt := update_var out (EL (w2n idx) f.lf_tgt.vs_params) f.lf_tgt;
    lf_H := set_prov f.lf_H [out]
      (if w2n idx < LENGTH f.lf_Q then EL (w2n idx) f.lf_Q else NONE);
    lf_tv := set_var_taint f.lf_tv [out] {} |> )
Proof
  strip_tac >>
  `ld_wordrel A (if w2n idx < LENGTH f.lf_Q then EL (w2n idx) f.lf_Q else NONE)
    (EL (w2n idx) f.lf_src.vs_params) (EL (w2n idx) f.lf_tgt.vs_params)` by
    (irule ld_vars_param >> simp[] >> qexists_tac `P` >> simp[]) >>
  `MEM out (fn_ir_vars f.lf_fn)` by metis_tac[ld_inst_output_ir, MEM] >>
  pure_rewrite_tac[update_var_def] >> irule ld_vars_write >>
  simp[set_var_taint_def, FLOOKUP_UPDATE] >>
  conj_tac
  >- (rpt strip_tac >> irule ld_param_selected_output >>
      qexistsl_tac [`idx`, `inst`] >> simp[] >>
      Cases_on `w2n idx < LENGTH f.lf_Q` >> gvs[] >> metis_tac[]) >>
  simp[set_var_taint_def, FLOOKUP_UPDATE] >>
  Cases_on `w2n idx < LENGTH f.lf_Q` >> gvs[ld_wordrel_def] >>
  Cases_on `EL (w2n idx) f.lf_Q` >> gvs[ld_wordrel_def, word_agree_except_def]
QED

Theorem ld_param_effect:
  ld_vars P A f /\ tn.t_var = f.lf_tv /\
  MEM inst (fn_insts f.lf_fn) /\ inst.inst_opcode = PARAM /\
  step_inst_base inst f.lf_tgt = OK ts /\
  ld_memory lo A tn f.lf_src f.lf_tgt /\ ld_nonghost tn f.lf_src f.lf_tgt /\
  (!j a. j < LENGTH f.lf_Q /\ EL j f.lf_Q = SOME a ==> j IN P f.lf_fn.fn_name) ==>
  ?ss q. step_inst_base inst f.lf_src = OK ss /\
    q = (case inst.inst_operands of [Lit idx] =>
      if w2n idx < LENGTH f.lf_Q then EL (w2n idx) f.lf_Q else NONE | _ => NONE) /\
    ld_vars P A (f with <| lf_src := ss; lf_tgt := ts;
      lf_H := set_prov f.lf_H inst.inst_outputs q;
      lf_tv := (step_taint inst f.lf_src ss tn).t_var |> ) /\
    ld_memory lo A (step_taint inst f.lf_src ss tn) ss ts /\
    ld_nonghost (step_taint inst f.lf_src ss tn) ss ts /\
    ld_erase A o_f set_prov f.lf_H inst.inst_outputs q =
      step_prov (MAP (OPTION_MAP (ld_erase A)) f.lf_Q)
        (ld_erase A o_f f.lf_H) inst ss /\
    ss.vs_allocas = f.lf_src.vs_allocas /\
    ss.vs_alloca_next = f.lf_src.vs_alloca_next /\
    ss.vs_params = f.lf_src.vs_params /\
    ss.vs_current_bb = f.lf_src.vs_current_bb /\
    ss.vs_prev_bb = f.lf_src.vs_prev_bb /\
    ss.vs_inst_idx = f.lf_src.vs_inst_idx /\
    ts.vs_allocas = f.lf_tgt.vs_allocas /\
    ts.vs_alloca_next = f.lf_tgt.vs_alloca_next /\
    ts.vs_params = f.lf_tgt.vs_params /\
    ts.vs_current_bb = f.lf_tgt.vs_current_bb /\
    ts.vs_prev_bb = f.lf_tgt.vs_prev_bb /\
    ts.vs_inst_idx = f.lf_tgt.vs_inst_idx
Proof
  strip_tac >>
  `LENGTH f.lf_src.vs_params = LENGTH f.lf_tgt.vs_params` by
    gvs[ld_vars_def] >>
  qpat_x_assum `step_inst_base inst f.lf_tgt = OK ts` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[opcode_case_def] >>
  simp[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  `step_taint inst f.lf_src
      (update_var out (EL (w2n idx) f.lf_src.vs_params) f.lf_src) tn =
    tn with t_var := set_var_taint tn.t_var [out] {}` by
    (drule ld_param_taint >> simp[]) >>
  simp[] >>
  conj_tac >- (irule ld_param_write >> simp[] >> qexists_tac `inst` >> simp[]) >>
  conj_tac >- (irule ld_memory_update_var >> simp[]) >>
  conj_tac >- (irule ld_nonghost_update_var >> simp[]) >>
  simp[ld_erase_set_prov, step_prov_def, out_prov_def, EL_MAP] >>
  Cases_on `w2n idx < LENGTH f.lf_Q` >> simp[]
QED

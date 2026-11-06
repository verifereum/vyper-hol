(* TOP-LEVEL: cached allocation sizes come from the literal request at the
   actual instruction in the current function. The invariant starts from an
   empty frame and is preserved by allocation and by unchanged cache fields.
   Helpers use the function's existing instruction-ID uniqueness condition. *)
Theory allocaCacheProps
Ancestors
  venomFnInstsProofs venomWf venomInst venomState venomExecSemantics venomMemProofs venomInstProofs1 finite_map list words

val alloca_step_rule = valOf (List.find (fn th =>
  let val guard = #1 (dest_imp (#2 (strip_forall (concl th))))
  in aconv (rhs guard) ``ALLOCA`` end) (CONJUNCTS step_inst_base_opcode_eqs));

Definition alloca_cache_matches_def:
  alloca_cache_matches func ss <=>
    !id region_base recorded_size.
      FLOOKUP ss.vs_allocas id = SOME (region_base,recorded_size) ==>
      ?inst size_word. MEM inst (fn_insts func) /\ inst.inst_id = id /\
        inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit size_word] /\
        recorded_size = w2n size_word
End

Theorem alloca_cache_matches_empty:
  !func ss. ss.vs_allocas = FEMPTY ==> alloca_cache_matches func ss
Proof
  simp[alloca_cache_matches_def]
QED

Theorem alloca_cache_matches_fields:
  !func before after.
    alloca_cache_matches func before /\ after.vs_allocas = before.vs_allocas ==>
    alloca_cache_matches func after
Proof
  simp[alloca_cache_matches_def]
QED

Theorem alloca_cache_literal_size:
  !func ss inst size_word region_base recorded_size.
    alloca_cache_matches func ss /\ fn_inst_ids_distinct func /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit size_word] /\
    FLOOKUP ss.vs_allocas inst.inst_id = SOME (region_base,recorded_size) ==>
    recorded_size = w2n size_word
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `alloca_cache_matches func ss`
    (mp_tac o REWRITE_RULE [alloca_cache_matches_def]) >>
  disch_then (qspecl_then [`inst.inst_id`, `region_base`, `recorded_size`] mp_tac) >>
  impl_tac >- simp[] >>
  disch_then (qx_choose_then `cached_inst` (qx_choose_then `cached_word` strip_assume_tac)) >>
  `cached_inst = inst` by (drule_all fn_insts_id_unique >> simp[]) >> gvs[]
QED

Theorem alloca_cache_matches_record:
  !func ss inst size_word region_base.
    alloca_cache_matches func ss /\ MEM inst (fn_insts func) /\
    inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit size_word] ==>
    alloca_cache_matches func
      (ss with vs_allocas := ss.vs_allocas |+ (inst.inst_id,(region_base,w2n size_word)))
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [alloca_cache_matches_def] >>
  rpt gen_tac >> simp_tac (srw_ss()) [FLOOKUP_UPDATE] >> IF_CASES_TAC >> simp[] >> strip_tac
  >- (gvs[] >> qexists_tac `inst` >> simp[]) >>
  fs[alloca_cache_matches_def] >> first_x_assum drule >> simp[]
QED

Theorem alloca_cache_matches_exec_alloca:
  !func ss out inst size_word.
    alloca_cache_matches func ss /\ MEM inst (fn_insts func) /\
    inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit size_word] /\
    exec_alloca inst ss size_word = OK out ==> alloca_cache_matches func out
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_outputs` >> gvs[exec_alloca_def] >>
  rename1 `inst.inst_outputs = output_name :: outputs` >> Cases_on `outputs` >> gvs[] >>
  Cases_on `FLOOKUP ss.vs_allocas inst.inst_id` >> gvs[exec_alloca_def, LET_THM]
  >- (irule alloca_cache_matches_fields >>
      qexists_tac `ss with vs_allocas := ss.vs_allocas |+
        (inst.inst_id,(ss.vs_alloca_next,w2n size_word))` >>
      simp[update_var_def] >> irule alloca_cache_matches_record >> simp[]) >>
  rename1 `FLOOKUP ss.vs_allocas inst.inst_id = SOME region` >> PairCases_on `region` >>
  gvs[exec_alloca_def] >> irule alloca_cache_matches_fields >> qexists_tac `ss` >> simp[update_var_def]
QED

Theorem alloca_cache_matches_step_literal:
  !func ss out inst size_word.
    alloca_cache_matches func ss /\ MEM inst (fn_insts func) /\
    inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit size_word] /\
    step_inst_base inst ss = OK out ==> alloca_cache_matches func out
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `step_inst_base inst ss = OK out` mp_tac >>
  asm_simp_tac (srw_ss()) [alloca_step_rule] >> strip_tac >>
  drule_all alloca_cache_matches_exec_alloca >> simp[]
QED

Theorem alloca_cache_matches_step_nonalloca:
  !func ss out inst.
    alloca_cache_matches func ss /\ step_inst_base inst ss = OK out /\
    inst.inst_opcode <> ALLOCA /\ inst.inst_opcode <> INVOKE ==>
    alloca_cache_matches func out
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`inst`, `ss`, `out`] mp_tac step_inst_base_preserves_allocas >>
  impl_tac >- simp[] >> DISCH_TAC >>
  irule alloca_cache_matches_fields >> qexists_tac `ss` >> simp[]
QED

Theorem alloca_success_literal:
  !inst ss out.
    inst.inst_opcode = ALLOCA /\ step_inst_base inst ss = OK out ==>
    ?size_word. inst.inst_operands = [Lit size_word]
Proof
  rpt gen_tac >> strip_tac >> qpat_x_assum `step_inst_base inst ss = OK out` mp_tac >>
  asm_simp_tac (srw_ss()) [alloca_step_rule, AllCaseEqs()] >> metis_tac[]
QED

Theorem invoke_success_allocas:
  !fuel ctx inst ss out.
    inst.inst_opcode = INVOKE /\ step_inst fuel ctx inst ss = OK out ==>
    out.vs_allocas = ss.vs_allocas
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `step_inst fuel ctx inst ss = OK out` mp_tac >>
  simp_tac (srw_ss()) [Once step_inst_def, AllCaseEqs()] >> strip_tac >>
  qspec_then `\s. s.vs_allocas` mp_tac bind_outputs_preserves >>
  impl_tac >- simp[update_var_def] >>
  disch_then drule_all >> simp[merge_callee_state_def]
QED

Theorem alloca_cache_matches_step:
  !func fuel ctx inst ss out.
    alloca_cache_matches func ss /\ MEM inst (fn_insts func) /\
    step_inst fuel ctx inst ss = OK out ==> alloca_cache_matches func out
Proof
  rpt gen_tac >> strip_tac >> Cases_on `inst.inst_opcode = INVOKE`
  >- (drule_all invoke_success_allocas >> DISCH_TAC >>
      irule alloca_cache_matches_fields >> qexists_tac `ss` >> simp[]) >>
  `step_inst_base inst ss = OK out` by fs[step_inst_non_invoke] >>
  Cases_on `inst.inst_opcode = ALLOCA`
  >- (drule_all alloca_success_literal >> disch_then (qx_choose_then `size_word` ASSUME_TAC) >>
      drule_all alloca_cache_matches_step_literal >> simp[]) >>
  drule_all alloca_cache_matches_step_nonalloca >> simp[]
QED

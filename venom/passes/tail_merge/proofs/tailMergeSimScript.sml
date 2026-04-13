(*
 * Tail Merge Simulation Helpers
 *
 * Definitions and lemmas for canonical instruction simulation:
 * var_corr, var_map_wf, sim_inv, and all canon_* / halting helpers
 * Split from tailMergeProofScript for build caching
 *)

Theory tailMergeSim
Ancestors
  tailMergeHelpers tailMergeStep tailMergeDefs stateEquiv venomExecSemantics
  cfgTransformProofs execEquivProofs venomInstProps
Libs
  tailMergeHelpersTheory tailMergeStepTheory cfgTransformTheory venomStateTheory
  venomExecSemanticsTheory venomInstTheory venomWfTheory
  tailMergeDefsTheory stateEquivTheory cfgTransformProofsTheory
  execEquivProofsTheory stateEquivProofsTheory venomInstPropsTheory

(* ================================================================
   result_equiv UNIV reflexivity
   ================================================================ *)

Theorem result_equiv_UNIV_refl[simp]:
  !r. result_equiv UNIV r r
Proof
  Cases >> simp[result_equiv_def, state_equiv_def, execution_equiv_def]
QED

(* ================================================================
   Variable correspondence for canonical instructions
   ================================================================ *)

Definition var_corr_def:
  var_corr vm1 vm2 s1 s2 <=>
    !v1 v2 idx.
      ALOOKUP vm1 v1 = SOME idx /\
      ALOOKUP vm2 v2 = SOME idx ==>
      lookup_var v1 s1 = lookup_var v2 s2
End

Definition var_map_wf_def:
  var_map_wf vm <=> !v idx. ALOOKUP vm v = SOME idx ==> idx < LENGTH vm
End

Definition sim_inv_def:
  sim_inv vm1 vm2 s1 s2 <=>
    var_corr vm1 vm2 s1 s2 /\
    var_map_wf vm1 /\ var_map_wf vm2 /\
    LENGTH vm1 = LENGTH vm2 /\
    execution_equiv UNIV s1 s2
End

Theorem sim_inv_init:
  !s. sim_inv [] [] s s
Proof
  rw[sim_inv_def, var_corr_def, var_map_wf_def, execution_equiv_def]
QED

(* ================================================================
   canon_insts structural lemmas
   ================================================================ *)

Theorem canon_insts_same_length:
  !vm1 vm2 insts1 insts2.
    canon_insts vm1 insts1 = canon_insts vm2 insts2 ==>
    LENGTH insts1 = LENGTH insts2
Proof
  Induct_on `insts1` >> Cases_on `insts2` >>
  rw[canon_insts_def, LET_THM] >>
  rpt (pairarg_tac >> fs[]) >> metis_tac[]
QED

Theorem canon_insts_cons:
  !vm1 vm2 h1 h2 t1 t2.
    canon_insts vm1 (h1::t1) = canon_insts vm2 (h2::t2) ==>
    ?vm1' vm2' ci.
      canon_inst vm1 h1 = (vm1', ci) /\
      canon_inst vm2 h2 = (vm2', ci) /\
      canon_insts vm1' t1 = canon_insts vm2' t2
Proof
  rw[canon_insts_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[])
QED

(* Same canonical instruction implies same opcode, id, and output count *)
Theorem canon_inst_same_fields:
  !vm1 vm2 inst1 inst2 vm1' vm2' ci.
    canon_inst vm1 inst1 = (vm1', ci) /\
    canon_inst vm2 inst2 = (vm2', ci) ==>
    inst1.inst_opcode = inst2.inst_opcode /\
    inst1.inst_id = inst2.inst_id
Proof
  rw[canon_inst_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[])
QED

(* Convenience projections *)
Theorem canon_inst_same_opcode:
  !vm1 vm2 inst1 inst2 vm1' vm2' ci.
    canon_inst vm1 inst1 = (vm1', ci) /\
    canon_inst vm2 inst2 = (vm2', ci) ==>
    inst1.inst_opcode = inst2.inst_opcode
Proof
  metis_tac[canon_inst_same_fields]
QED

Theorem canon_inst_same_id:
  !vm1 vm2 inst1 inst2 vm1' vm2' ci.
    canon_inst vm1 inst1 = (vm1', ci) /\
    canon_inst vm2 inst2 = (vm2', ci) ==>
    inst1.inst_id = inst2.inst_id
Proof
  metis_tac[canon_inst_same_fields]
QED

(* ================================================================
   canon_operand / canon_operands lemmas
   ================================================================ *)

Theorem canon_operand_eval:
  !vm1 vm2 op1 op2 vm1' vm2' cop s1 s2.
    canon_operand vm1 op1 = (vm1', cop) /\
    canon_operand vm2 op2 = (vm2', cop) /\
    var_corr vm1 vm2 s1 s2 /\
    execution_equiv UNIV s1 s2 /\
    (!v. op1 = Var v ==> ?idx. ALOOKUP vm1 v = SOME idx) /\
    (!v. op2 = Var v ==> ?idx. ALOOKUP vm2 v = SOME idx) ==>
    eval_operand op1 s1 = eval_operand op2 s2
Proof
  Cases_on `op1` >> Cases_on `op2` >>
  simp[canon_operand_def, LET_THM, eval_operand_def] >>
  rpt strip_tac >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  fs[var_corr_def, lookup_var_def, execution_equiv_def]
QED

Theorem canon_operand_preserves:
  !vm1 vm2 op1 op2 vm1' vm2' cop s1 s2.
    canon_operand vm1 op1 = (vm1', cop) /\
    canon_operand vm2 op2 = (vm2', cop) /\
    var_corr vm1 vm2 s1 s2 /\
    var_map_wf vm1 /\ var_map_wf vm2 /\
    LENGTH vm1 = LENGTH vm2 /\
    eval_operand op1 s1 = eval_operand op2 s2 ==>
    var_corr vm1' vm2' s1 s2 /\
    var_map_wf vm1' /\ var_map_wf vm2' /\
    LENGTH vm1' = LENGTH vm2'
Proof
  Cases_on `op1` >> Cases_on `op2` >>
  simp[canon_operand_def, LET_THM, eval_operand_def] >>
  rpt strip_tac >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  gvs[var_corr_def, lookup_var_def, var_map_wf_def,
      alistTheory.ALOOKUP_def] >>
  rpt strip_tac >> rpt (CASE_TAC >> gvs[]) >>
  TRY (res_tac >> fs[] >> NO_TAC) >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  TRY (res_tac >> fs[] >> NO_TAC)
QED

Theorem canon_operands_cons_result:
  !vm h t vm' cops.
    canon_operands vm (h::t) = (vm', cops) ==>
    ?cop cops'. cops = cop :: cops'
Proof
  rw[Once canon_operands_def, LET_THM] >>
  pairarg_tac >> fs[] >> pairarg_tac >> fs[] >> metis_tac[]
QED

Theorem canon_operands_nil:
  !vm vm' cops. canon_operands vm [] = (vm', cops) ==> vm' = vm /\ cops = []
Proof
  simp[Once canon_operands_def]
QED

Theorem canon_operand_var_in_tail:
  !vm h vm' cop v.
    canon_operand vm h = (vm', cop) /\
    (?idx. ALOOKUP vm v = SOME idx) ==>
    ?idx. ALOOKUP vm' v = SOME idx
Proof
  Cases_on `h` >> simp[canon_operand_def, LET_THM] >>
  rpt strip_tac >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[alistTheory.ALOOKUP_def])
QED

(* Combined: eval equality + invariant preservation for canon_operands *)
Theorem canon_operands_step:
  !ops1 vm1 vm2 ops2 vm1' vm2' cops s1 s2.
    canon_operands vm1 ops1 = (vm1', cops) /\
    canon_operands vm2 ops2 = (vm2', cops) /\
    var_corr vm1 vm2 s1 s2 /\
    execution_equiv UNIV s1 s2 /\
    var_map_wf vm1 /\ var_map_wf vm2 /\
    LENGTH vm1 = LENGTH vm2 /\
    (!v. MEM (Var v) ops1 ==> ?idx. ALOOKUP vm1 v = SOME idx) /\
    (!v. MEM (Var v) ops2 ==> ?idx. ALOOKUP vm2 v = SOME idx) ==>
    MAP (\op. eval_operand op s1) ops1 =
    MAP (\op. eval_operand op s2) ops2 /\
    var_corr vm1' vm2' s1 s2 /\
    var_map_wf vm1' /\ var_map_wf vm2' /\
    LENGTH vm1' = LENGTH vm2'
Proof
  Induct >> rpt gen_tac >> strip_tac >>
  TRY (
    imp_res_tac canon_operands_nil >> BasicProvers.VAR_EQ_TAC >> fs[] >>
    Cases_on `ops2` >> fs[] >>
    imp_res_tac canon_operands_nil >> imp_res_tac canon_operands_cons_result >>
    BasicProvers.VAR_EQ_TAC >> fs[] >> NO_TAC) >>
  (* cons: extract head/tail from canon_operands vm1 (h::ops1) *)
  qpat_x_assum `canon_operands vm1 (_::_) = _` mp_tac >>
  simp[Once canon_operands_def, LET_THM] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  (* ops2 must also be cons *)
  `?h' t'. ops2 = h'::t'` by (
    Cases_on `ops2` >> fs[] >>
    imp_res_tac canon_operands_nil >> fs[]) >>
  BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `canon_operands vm2 (_::_) = _` mp_tac >>
  simp[Once canon_operands_def, LET_THM] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  (* cops from both sides must match: cop::cops' = cop'::cops'' *)
  `cop::cops' = cop'::cops''` by metis_tac[] >>
  fs[] >>
  BasicProvers.VAR_EQ_TAC >>
  (* Head: eval equality *)
  `eval_operand h s1 = eval_operand h' s2` by (
    irule canon_operand_eval >>
    metis_tac[]) >>
  (* Head: preservation *)
  `var_corr var_map' var_map''' s1 s2 /\
   var_map_wf var_map' /\ var_map_wf var_map''' /\
   LENGTH var_map' = LENGTH var_map'''`
    by metis_tac[canon_operand_preserves] >>
  simp[] >>
  (* Tail: apply IH *)
  first_x_assum (qspecl_then [`var_map'`, `var_map'''`, `t'`,
    `vm1'`, `vm2'`, `cops'`, `s1`, `s2`] mp_tac) >>
  (impl_tac >- (
    simp[] >> rpt strip_tac >>
    metis_tac[canon_operand_var_in_tail])) >>
  simp[]
QED

(* ================================================================
   canon_outputs lemmas
   ================================================================ *)

Theorem canon_outputs_single_step:
  !vm1 vm2 v1 v2 val s1 s2.
    LENGTH vm1 = LENGTH vm2 /\
    var_corr vm1 vm2 s1 s2 /\
    var_map_wf vm1 /\ var_map_wf vm2 ==>
    var_corr ((v1, LENGTH vm1)::vm1) ((v2, LENGTH vm2)::vm2)
      (update_var v1 val s1) (update_var v2 val s2) /\
    var_map_wf ((v1, LENGTH vm1)::vm1) /\
    var_map_wf ((v2, LENGTH vm2)::vm2) /\
    LENGTH ((v1, LENGTH vm1)::vm1) = LENGTH ((v2, LENGTH vm2)::vm2)
Proof
  rw[var_corr_def, update_var_def, lookup_var_def,
     finite_mapTheory.FLOOKUP_UPDATE, alistTheory.ALOOKUP_def,
     var_map_wf_def] >>
  rpt strip_tac >>
  rpt (CASE_TAC >> fs[]) >>
  TRY (first_x_assum irule >> simp[] >> NO_TAC) >>
  TRY (res_tac >> fs[] >> NO_TAC) >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >> res_tac >> gvs[]
QED

Theorem canon_outputs_has_var:
  !vs vm vm' idxs v.
    canon_outputs vm vs = (vm', idxs) /\
    (MEM v vs \/ ?idx. ALOOKUP vm v = SOME idx) ==>
    ?idx'. ALOOKUP vm' v = SOME idx'
Proof
  Induct >> simp[canon_outputs_def] >> rpt gen_tac >>
  pairarg_tac >> simp[] >> rpt strip_tac >> gvs[]
  >- (first_x_assum (qspecl_then
        [`(h, LENGTH vm)::vm`, `var_map''`, `idxs'`, `h`] mp_tac) >>
      simp[alistTheory.ALOOKUP_def])
  >- (first_x_assum (qspecl_then
        [`(h, LENGTH vm)::vm`, `var_map''`, `idxs'`, `v`] mp_tac) >>
      simp[alistTheory.ALOOKUP_def])
  >- (first_x_assum (qspecl_then
        [`(h, LENGTH vm)::vm`, `var_map''`, `idxs'`, `v`] mp_tac) >>
      simp[alistTheory.ALOOKUP_def] >>
      Cases_on `h = v` >> simp[])
QED

Theorem canon_operand_has_var:
  !vm op vm' cop v.
    canon_operand vm op = (vm', cop) /\
    (?idx. ALOOKUP vm v = SOME idx) ==>
    ?idx'. ALOOKUP vm' v = SOME idx'
Proof
  Cases_on `op` >> simp[canon_operand_def, LET_THM] >>
  rpt strip_tac >> gvs[] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[alistTheory.ALOOKUP_def]) >>
  Cases_on `s = v` >> gvs[]
QED

Theorem canon_operands_has_var:
  !ops vm vm' cops v.
    canon_operands vm ops = (vm', cops) /\
    (?idx. ALOOKUP vm v = SOME idx) ==>
    ?idx'. ALOOKUP vm' v = SOME idx'
Proof
  Induct >> simp[Once canon_operands_def] >> rpt gen_tac >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  rpt strip_tac >> gvs[] >>
  first_x_assum irule >> simp[] >>
  metis_tac[canon_operand_has_var]
QED

Theorem canon_inst_has_var:
  !vm inst vm' ci v.
    canon_inst vm inst = (vm', ci) /\
    (MEM v inst.inst_outputs \/ ?idx. ALOOKUP vm v = SOME idx) ==>
    ?idx'. ALOOKUP vm' v = SOME idx'
Proof
  simp[canon_inst_def, LET_THM] >> rpt gen_tac >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  rpt strip_tac >> gvs[]
  >- (irule canon_operands_has_var >> simp[] >>
      metis_tac[canon_outputs_has_var])
  >- (metis_tac[canon_operands_has_var, canon_outputs_has_var])
QED

(* ================================================================
   Halting terminator simulation helpers
   ================================================================ *)

Theorem halt_state_ee_UNIV:
  !s1 s2. execution_equiv UNIV s1 s2 ==>
    execution_equiv UNIV (halt_state s1) (halt_state s2)
Proof
  rw[execution_equiv_def, halt_state_def, lookup_var_def]
QED

Theorem set_returndata_ee_UNIV:
  !rd s1 s2. execution_equiv UNIV s1 s2 ==>
    execution_equiv UNIV (set_returndata rd s1) (set_returndata rd s2)
Proof
  rw[execution_equiv_def, set_returndata_def, lookup_var_def]
QED

Theorem ee_UNIV_same_memory:
  !s1 s2. execution_equiv UNIV s1 s2 ==> s1.vs_memory = s2.vs_memory
Proof
  rw[execution_equiv_def]
QED

Theorem map_eval_same_length:
  !ops1 ops2 s1 s2.
    MAP (\op. eval_operand op s1) ops1 =
    MAP (\op. eval_operand op s2) ops2 ==>
    LENGTH ops1 = LENGTH ops2
Proof
  Induct >> Cases_on `ops2` >> simp[] >> metis_tac[]
QED

Theorem ee_UNIV_with_accounts:
  !s1 s2 f.
    execution_equiv UNIV s1 s2 ==>
    execution_equiv UNIV (s1 with vs_accounts := f) (s2 with vs_accounts := f)
Proof
  simp[execution_equiv_def, lookup_var_def]
QED

Theorem halting_term_sim:
  !inst1 inst2 s1 s2.
    is_halting_opcode inst1.inst_opcode /\
    inst1.inst_opcode = inst2.inst_opcode /\
    execution_equiv UNIV s1 s2 /\
    MAP (\op. eval_operand op s1) inst1.inst_operands =
    MAP (\op. eval_operand op s2) inst2.inst_operands ==>
    result_equiv UNIV (step_inst_base inst1 s1) (step_inst_base inst2 s2)
Proof
  rpt strip_tac >>
  `s1.vs_memory = s2.vs_memory /\ s1.vs_accounts = s2.vs_accounts /\
   s1.vs_call_ctx = s2.vs_call_ctx`
    by gvs[execution_equiv_def] >>
  `LENGTH inst1.inst_operands = LENGTH inst2.inst_operands`
    by metis_tac[map_eval_same_length] >>
  Cases_on `inst1.inst_opcode` >>
  gvs[is_halting_opcode_def, step_inst_base_def] >>
  Cases_on `inst1.inst_operands` >> Cases_on `inst2.inst_operands` >>
  gvs[result_equiv_def] >>
  TRY (Cases_on `t` >> Cases_on `t'` >> gvs[result_equiv_def]) >>
  TRY (Cases_on `t''` >> Cases_on `t'''` >> gvs[result_equiv_def]) >>
  gvs[AllCaseEqs(), result_equiv_def, LET_THM, revert_state_def] >>
  rpt strip_tac >>
  rpt (CASE_TAC >> gvs[result_equiv_def]) >>
  TRY (irule halt_state_ee_UNIV >> irule set_returndata_ee_UNIV >> simp[] >> NO_TAC) >>
  TRY (irule halt_state_ee_UNIV >> irule ee_UNIV_with_accounts >> simp[] >> NO_TAC) >>
  TRY (irule halt_state_ee_UNIV >> simp[] >> NO_TAC) >>
  TRY (irule set_returndata_ee_UNIV >> simp[] >> NO_TAC) >>
  simp[execution_equiv_def, set_returndata_def, halt_state_def,
       lookup_var_def] >> gvs[execution_equiv_def]
QED

Theorem is_halting_is_terminator:
  !opc. is_halting_opcode opc ==> is_terminator opc
Proof
  Cases >> simp[is_halting_opcode_def, is_terminator_def]
QED

Theorem halting_non_last_not_terminator:
  !bb i.
    bb_is_halting bb /\
    i < LENGTH bb.bb_instructions /\
    ~is_terminator (EL i bb.bb_instructions).inst_opcode ==>
    SUC i < LENGTH bb.bb_instructions
Proof
  rw[bb_is_halting_def] >>
  Cases_on `bb.bb_instructions` >> gvs[] >>
  CCONTR_TAC >> gvs[arithmeticTheory.NOT_LESS] >>
  `i = PRE (LENGTH (h::t))` by gvs[] >>
  gvs[listTheory.LAST_EL] >>
  imp_res_tac is_halting_is_terminator
QED

(* ================================================================
   sim_pre construction helpers
   ================================================================ *)

Theorem canon_operands_length:
  !vm ops vm' cops.
    canon_operands vm ops = (vm', cops) ==>
    LENGTH cops = LENGTH ops
Proof
  Induct_on `ops` >> rw[canon_operands_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> res_tac
QED

Theorem canon_outputs_length:
  !vm vs vm' idxs.
    canon_outputs vm vs = (vm', idxs) ==>
    LENGTH idxs = LENGTH vs
Proof
  Induct_on `vs` >> rw[canon_outputs_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> res_tac
QED

Theorem canon_outputs_map_length:
  !vm vs vm' idxs.
    canon_outputs vm vs = (vm', idxs) ==>
    LENGTH vm' = LENGTH vm + LENGTH vs
Proof
  Induct_on `vs` >> rw[canon_outputs_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  res_tac >> simp[]
QED

Theorem canon_operands_label_lit:
  !ops1 ops2 vm1 vm2 vm1' vm2' cops.
    canon_operands vm1 ops1 = (vm1', cops) /\
    canon_operands vm2 ops2 = (vm2', cops) ==>
    LENGTH ops1 = LENGTH ops2 /\
    (!i l. i < LENGTH ops1 /\ EL i ops1 = Label l ==> EL i ops2 = Label l) /\
    (!i l. i < LENGTH ops2 /\ EL i ops2 = Label l ==> EL i ops1 = Label l) /\
    (!i w. i < LENGTH ops1 /\ EL i ops1 = Lit w ==> EL i ops2 = Lit w) /\
    (!i w. i < LENGTH ops2 /\ EL i ops2 = Lit w ==> EL i ops1 = Lit w)
Proof
  Induct_on `ops1` >> rpt gen_tac >> strip_tac
  >- (imp_res_tac canon_operands_nil >> gvs[] >>
      imp_res_tac canon_operands_length >> gvs[])
  >> qpat_x_assum `canon_operands vm1 (_::_) = _` mp_tac
  >> simp[Once canon_operands_def, LET_THM]
  >> rpt (pairarg_tac >> simp[]) >> strip_tac
  >> `?h2 t2. ops2 = h2::t2` by (
       Cases_on `ops2` >> gvs[] >>
       imp_res_tac canon_operands_nil >> gvs[])
  >> gvs[]
  >> qpat_x_assum `canon_operands vm2 (_::_) = _` mp_tac
  >> simp[Once canon_operands_def, LET_THM]
  >> rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[]
  >> first_x_assum drule >> disch_then drule >> strip_tac
  >> conj_tac >- simp[]
  >> rpt conj_tac >> rpt gen_tac
  >> (Cases_on `i` >> simp[] >>
      Cases_on `h` >> Cases_on `h2` >>
      gvs[canon_operand_def, LET_THM] >>
      rpt (BasicProvers.FULL_CASE_TAC >> gvs[]))
QED

Theorem canon_outputs_alookup_orig:
  !vs vm vm' idxs v idx.
    canon_outputs vm vs = (vm', idxs) /\
    ~MEM v vs /\
    ALOOKUP vm v = SOME idx ==>
    ALOOKUP vm' v = SOME idx
Proof
  Induct >> simp[canon_outputs_def, LET_THM] >>
  rpt gen_tac >> pairarg_tac >> gvs[] >> rpt strip_tac >>
  first_x_assum (qspecl_then [`(h,LENGTH vm)::vm`, `var_map''`,
    `idxs'`, `v`, `idx`] mp_tac) >>
  simp[alistTheory.ALOOKUP_def]
QED

Theorem canon_operand_ext:
  !vm1 vm2 op vm1' cop.
    canon_operand vm1 op = (vm1', cop) /\
    LENGTH vm1 = LENGTH vm2 /\
    (!v. op = Var v ==> ALOOKUP vm2 v = ALOOKUP vm1 v) ==>
    ?vm2'. canon_operand vm2 op = (vm2', cop) /\
           LENGTH vm2' = LENGTH vm1'
Proof
  Cases_on `op` >> rw[canon_operand_def, LET_THM] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >> gvs[]
QED

Theorem canon_operand_alookup_agree:
  !vm1 vm2 op vm1' vm2' cop v.
    canon_operand vm1 op = (vm1', cop) /\
    canon_operand vm2 op = (vm2', cop) /\
    LENGTH vm1 = LENGTH vm2 /\
    ALOOKUP vm2 v = ALOOKUP vm1 v ==>
    ALOOKUP vm2' v = ALOOKUP vm1' v
Proof
  Cases_on `op` >> rw[canon_operand_def, LET_THM] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[alistTheory.ALOOKUP_def]) >>
  gvs[]
QED

Theorem canon_operands_ext:
  !ops vm1 vm2 vm1' cops.
    canon_operands vm1 ops = (vm1', cops) /\
    LENGTH vm1 = LENGTH vm2 /\
    (!v. MEM (Var v) ops ==> ALOOKUP vm2 v = ALOOKUP vm1 v) ==>
    ?vm2'. canon_operands vm2 ops = (vm2', cops) /\
           LENGTH vm2' = LENGTH vm1'
Proof
  Induct >> simp[canon_operands_def, LET_THM] >>
  rpt gen_tac >>
  Cases_on `canon_operand vm1 h` >> simp[] >>
  Cases_on `canon_operands q ops` >> simp[] >>
  rpt strip_tac >> gvs[] >>
  `?vm2a. canon_operand vm2 h = (vm2a, r) /\
          LENGTH vm2a = LENGTH q` by (
    Cases_on `h` >>
    gvs[canon_operand_def, LET_THM] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[])) >>
  simp[] >>
  first_x_assum (qspecl_then [`q`, `vm2a`, `q'`, `r'`] mp_tac) >>
  impl_tac >- (
    simp[] >> rpt strip_tac >>
    metis_tac[canon_operand_alookup_agree]) >>
  strip_tac >> qexists_tac `vm2'` >> simp[]
QED

Theorem canon_operands_alookup_only:
  !ops vm1 vm2 vm1' cops.
    canon_operands vm1 ops = (vm1', cops) /\
    (!v. MEM (Var v) ops ==> ALOOKUP vm2 v = ALOOKUP vm1 v) /\
    (!v. MEM (Var v) ops ==> ?idx. ALOOKUP vm1 v = SOME idx) ==>
    ?vm2'. canon_operands vm2 ops = (vm2', cops)
Proof
  Induct >> simp[canon_operands_def, LET_THM] >>
  rpt gen_tac >>
  Cases_on `canon_operand vm1 h` >> simp[] >>
  Cases_on `canon_operands q ops` >> simp[] >>
  rpt strip_tac >> gvs[] >>
  `?vm2a. canon_operand vm2 h = (vm2a, r)` by (
    Cases_on `h` >> gvs[canon_operand_def, LET_THM] >>
    `?idx. ALOOKUP vm1 s = SOME idx` by metis_tac[] >>
    `ALOOKUP vm2 s = SOME idx` by metis_tac[] >>
    gvs[]) >>
  simp[] >>
  `(!v. MEM (Var v) ops ==> ALOOKUP vm2a v = ALOOKUP q v)` by (
    Cases_on `h` >> gvs[canon_operand_def, LET_THM] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[alistTheory.ALOOKUP_def]) >>
    rpt strip_tac >> metis_tac[]) >>
  `(!v. MEM (Var v) ops ==> ?idx. ALOOKUP q v = SOME idx)` by (
    Cases_on `h` >> gvs[canon_operand_def, LET_THM] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
    metis_tac[]) >>
  first_x_assum (qspecl_then [`q`, `vm2a`, `q'`, `r'`] mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `canon_operands vm2a ops` >> gvs[]
QED

Theorem canon_operands_orig:
  !vm ops outputs evm couts cops evm'.
    canon_outputs vm outputs = (evm, couts) /\
    canon_operands evm ops = (evm', cops) /\
    (!v. MEM (Var v) ops ==> ~MEM v outputs) /\
    (!v. MEM (Var v) ops ==> ?idx. ALOOKUP vm v = SOME idx) ==>
    ?vm'. canon_operands vm ops = (vm', cops)
Proof
  rpt strip_tac >>
  irule (REWRITE_RULE [GSYM AND_IMP_INTRO]
    (SPEC_ALL canon_operands_alookup_only)) >>
  qexistsl_tac [`evm`, `evm'`] >> rpt conj_tac
  >- (rpt strip_tac >>
      `~MEM v outputs` by metis_tac[] >>
      `?idx. ALOOKUP vm v = SOME idx` by metis_tac[] >>
      imp_res_tac canon_outputs_alookup_orig >> metis_tac[])
  >- (rpt strip_tac >>
      `~MEM v outputs` by metis_tac[] >>
      `?idx. ALOOKUP vm v = SOME idx` by metis_tac[] >>
      imp_res_tac canon_outputs_alookup_orig >> gvs[])
  >- first_assum ACCEPT_TAC
QED

Theorem canon_inst_eval_match:
  !vm1 vm2 h1 h2 vm1' vm2' ci s1 s2.
    canon_inst vm1 h1 = (vm1', ci) /\
    canon_inst vm2 h2 = (vm2', ci) /\
    sim_inv vm1 vm2 s1 s2 /\
    (!v. MEM (Var v) h1.inst_operands ==> ?idx. ALOOKUP vm1 v = SOME idx) /\
    (!v. MEM (Var v) h2.inst_operands ==> ?idx. ALOOKUP vm2 v = SOME idx) /\
    (!v. MEM (Var v) h1.inst_operands ==> ~MEM v h1.inst_outputs) /\
    (!v. MEM (Var v) h2.inst_operands ==> ~MEM v h2.inst_outputs) ==>
    MAP (\op. eval_operand op s1) h1.inst_operands =
    MAP (\op. eval_operand op s2) h2.inst_operands
Proof
  rpt strip_tac >>
  qpat_x_assum `canon_inst vm1 _ = _` mp_tac >>
  simp[canon_inst_def, LET_THM] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  qpat_x_assum `canon_inst vm2 _ = _` mp_tac >>
  simp[canon_inst_def, LET_THM] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  gvs[] >>
  rename1 `canon_outputs vm1 h1.inst_outputs = (evm1, _)` >>
  rename1 `canon_outputs vm2 h2.inst_outputs = (evm2, _)` >>
  `?vm1a vm2a.
    canon_operands vm1 h1.inst_operands = (vm1a, cops) /\
    canon_operands vm2 h2.inst_operands = (vm2a, cops)`
    suffices_by (
      strip_tac >>
      pop_assum (fn eq2 => pop_assum (fn eq1 =>
        mp_tac (MATCH_MP (MATCH_MP
          (REWRITE_RULE [GSYM AND_IMP_INTRO]
            (SPEC_ALL canon_operands_step)) eq1) eq2))) >>
      gvs[sim_inv_def]) >>
  imp_res_tac canon_operands_orig >>
  metis_tac[]
QED

val _ = export_theory();

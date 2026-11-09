(*
 * Generic Venom SSA, dominance and block-execution lemmas.
 *
 * Facts about well-formed functions in SSA form (output uniqueness,
 * dominance of definitions, reachability in the CFG) and about
 * exec_block (variable-domain monotonicity, prefix skipping).
 * They hold for any function, independent of a pass, so pass proofs
 * and the codegen and pipeline proofs share them from here.
 *)

Theory venomWfProps
Ancestors
  venomWf venomInst venomInstProps venomState
  venomExecSemantics venomExecProofs venomExecProps instIdxIndep
  stateEquiv stateEquivProps stateEquivProofs execEquivProps execEquivProofs
  passSimulationDefs passSimulationProps passSimulationProofs
  passSharedDefs passSharedProps
  analysisSimDefs analysisSimProps analysisSimProofsBase
  cfgDefs cfgAnalysisProps cfgTransform cfgTransformProps
  dfAnalyzeDefs dfAnalyzeProps dfHelperProps worklistDefs
  livenessDefs livenessProofs opcodeClass indexedLists pointerConfinedDefs
  finite_map pred_set list rich_list combin
Libs
  BasicProvers

(* ---- from sccpCorrectnessProofs ---- *)

(* ================================================================= *)
(*  Part 3: FDOM monotonicity and output tracking                    *)
(* ================================================================= *)

Theorem exec_block_fdom_mono:
  !fuel ctx bb s s'.
    exec_block fuel ctx bb s = OK s' /\
    bb_well_formed bb /\ EVERY inst_wf bb.bb_instructions ==>
    FDOM s.vs_vars SUBSET FDOM s'.vs_vars
Proof
  rpt gen_tac >> strip_tac >>
  `!n f c st st'.
     n = LENGTH bb.bb_instructions - st.vs_inst_idx /\
     exec_block f c bb st = OK st' /\
     bb_well_formed bb /\ EVERY inst_wf bb.bb_instructions ==>
     FDOM st.vs_vars SUBSET FDOM st'.vs_vars`
    suffices_by (
      disch_then (qspecl_then
        [`LENGTH bb.bb_instructions - s.vs_inst_idx`,
         `fuel`, `ctx`, `s`, `s'`] mp_tac) >>
      simp[]) >>
  completeInduct_on `n` >> rw[] >>
  qabbrev_tac `idx = st.vs_inst_idx` >>
  Cases_on `idx >= LENGTH bb.bb_instructions`
  >- (
    qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
    ONCE_REWRITE_TAC[exec_block_def] >>
    simp[get_instruction_def]) >>
  `idx < LENGTH bb.bb_instructions` by fs[] >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  ONCE_REWRITE_TAC[exec_block_def] >>
  simp[get_instruction_def] >>
  Cases_on `step_inst f c (EL idx bb.bb_instructions) st` >> gvs[] >>
  Cases_on `is_terminator (EL idx bb.bb_instructions).inst_opcode` >> gvs[]
  >- (
    (* Terminator: lookup_var preserved => FDOM preserved *)
    Cases_on `v.vs_halted` >> gvs[] >>
    simp[pred_setTheory.SUBSET_DEF] >> rpt strip_tac >>
    irule lookup_var_fdom >> qexists_tac `st` >>
    metis_tac[step_terminator_preserves_vars]) >>
  (* Non-terminator: step_inst_fdom gives FDOM grows, then IH *)
  strip_tac >>
  `FDOM v.vs_vars = FDOM st.vs_vars UNION
     set (EL idx bb.bb_instructions).inst_outputs` by (
    `inst_wf (EL idx bb.bb_instructions)` by
	      fs[EVERY_EL] >>
	    `(EL idx bb.bb_instructions).inst_opcode ≠ PHI` by
	      metis_tac[step_inst_ok_imp_not_phi] >>
	    metis_tac[step_inst_fdom]) >>
  `FDOM st.vs_vars SUBSET FDOM v.vs_vars` by
    (simp[] >> simp[pred_setTheory.SUBSET_DEF]) >>
  `FDOM v.vs_vars SUBSET FDOM st'.vs_vars` by (
    first_x_assum (qspec_then `LENGTH bb.bb_instructions - SUC idx` mp_tac) >>
    (impl_tac >- simp[Abbr `idx`]) >>
    disch_then (qspecl_then [`f`, `c`,
      `v with vs_inst_idx := SUC idx`, `st'`] mp_tac) >>
    simp[]) >>
  metis_tac[pred_setTheory.SUBSET_TRANS]
QED

(* After running a block, non-terminator instruction outputs are in FDOM.
   Proof approach: completeInduct_on with rpt strip_tac (NOT rw[]).
   rw[] is too aggressive with arithmetic premises. *)
(* Separate the induction to avoid scoping issues with outer exec_block *)
Theorem exec_block_output_in_fdom_aux:
  !bb idx v n f c st st'.
    idx < LENGTH bb.bb_instructions /\
    ~is_terminator (EL idx bb.bb_instructions).inst_opcode /\
    MEM v (EL idx bb.bb_instructions).inst_outputs /\
    n = LENGTH bb.bb_instructions - st.vs_inst_idx /\
    exec_block f c bb st = OK st' /\
    bb_well_formed bb /\ EVERY inst_wf bb.bb_instructions /\
    st.vs_inst_idx <= idx ==>
    v IN FDOM st'.vs_vars
Proof
  ntac 3 gen_tac >>
  completeInduct_on `n` >> rw[] >>
  qabbrev_tac `k = st.vs_inst_idx` >>
  Cases_on `k >= LENGTH bb.bb_instructions`
  >- fs[Abbr `k`] >>
  `k < LENGTH bb.bb_instructions` by fs[] >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  ONCE_REWRITE_TAC[exec_block_def] >>
  simp[get_instruction_def, Abbr `k`] >>
  Cases_on `step_inst f c (EL st.vs_inst_idx bb.bb_instructions) st` >>
  gvs[] >>
  Cases_on `is_terminator (EL st.vs_inst_idx bb.bb_instructions).inst_opcode`
  >> gvs[]
  >- (
    (* terminator case: contradiction *)
    fs[bb_well_formed_def] >>
    `st.vs_inst_idx = PRE (LENGTH bb.bb_instructions)` by
      (first_x_assum irule >> simp[]) >>
    `idx = st.vs_inst_idx` by simp[] >>
    gvs[]
  ) >>
  strip_tac >>
  Cases_on `st.vs_inst_idx = idx`
  >- (
    `inst_wf (EL idx bb.bb_instructions)` by fs[EVERY_EL] >>
    `(EL idx bb.bb_instructions).inst_opcode ≠ PHI` by
      metis_tac[step_inst_ok_imp_not_phi] >>
    `FDOM v'.vs_vars = FDOM st.vs_vars UNION
       set (EL idx bb.bb_instructions).inst_outputs` by
      metis_tac[step_inst_fdom] >>
    `v IN FDOM v'.vs_vars` by simp[] >>
    `FDOM v'.vs_vars SUBSET FDOM st'.vs_vars` by (
      mp_tac (Q.SPECL [`f`, `c`, `bb`,
        `v' with vs_inst_idx := SUC st.vs_inst_idx`, `st'`]
        exec_block_fdom_mono) >>
      simp[]) >>
    metis_tac[pred_setTheory.SUBSET_DEF]
  ) >>
  (* recursive case: st.vs_inst_idx < idx *)
  `st.vs_inst_idx < idx` by simp[] >>
  first_x_assum (qspec_then
    `LENGTH bb.bb_instructions - SUC st.vs_inst_idx` mp_tac) >>
  simp[] >>
  disch_then (qspecl_then [`f`, `c`,
    `v' with vs_inst_idx := SUC st.vs_inst_idx`, `st'`] mp_tac) >>
  simp[]
QED

Theorem exec_block_outputs_in_fdom:
  !fuel ctx bb s s' idx v.
    exec_block fuel ctx bb s = OK s' /\
    s.vs_inst_idx = 0 /\
    bb_well_formed bb /\
    EVERY inst_wf bb.bb_instructions /\
    idx < LENGTH bb.bb_instructions /\
    ~is_terminator (EL idx bb.bb_instructions).inst_opcode /\
    MEM v (EL idx bb.bb_instructions).inst_outputs ==>
    v IN FDOM s'.vs_vars
Proof
  rpt gen_tac >> strip_tac >>
  irule exec_block_output_in_fdom_aux >>
  qexistsl_tac [`bb`, `ctx`, `fuel`, `idx`,
    `LENGTH bb.bb_instructions`, `s`] >>
  simp[]
QED

(* ================================================================= *)
(*  Part 4: The dominance invariant                                  *)
(* ================================================================= *)

Definition strict_dom_vars_defined_def:
  strict_dom_vars_defined f s <=>
    !d_bb d_inst v.
      MEM d_bb f.fn_blocks /\
      MEM d_inst d_bb.bb_instructions /\
      MEM v d_inst.inst_outputs /\
      fn_dominates f d_bb.bb_label s.vs_current_bb /\
      d_bb.bb_label <> s.vs_current_bb ==>
      v IN FDOM s.vs_vars
End

(* At entry: vacuously true because entry has no strict dominator.
   Any path from entry to entry is [entry]; a strict dominator must
   appear on it AND differ from entry — contradiction. *)
Theorem strict_dom_vars_defined_entry:
  !f s.
    fn_entry_label f = SOME s.vs_current_bb ==>
    strict_dom_vars_defined f s
Proof
  rw[strict_dom_vars_defined_def] >> rpt strip_tac >>
  `F` suffices_by simp[] >>
  qpat_x_assum `fn_dominates _ _ _` mp_tac >>
  simp[fn_dominates_def] >> DISJ2_TAC >>
  qmatch_asmsub_abbrev_tac `fn_entry_label _ = SOME lbl` >>
  qexists_tac `[lbl]` >>
  simp[is_fn_path_def, fn_entry_label_def, entry_block_def, Abbr `lbl`]
QED

Theorem strict_dom_vars_defined_preserved:
  !f bb s s' fuel ctx.
    wf_function f /\ ssa_form f /\
    MEM bb f.fn_blocks /\
    bb.bb_label = s.vs_current_bb /\
    exec_block fuel ctx bb s = OK s' /\
    s.vs_inst_idx = 0 /\
    ~s'.vs_halted /\
    strict_dom_vars_defined f s /\
    fn_reachable f s.vs_current_bb /\
    bb_well_formed bb /\
    EVERY inst_wf bb.bb_instructions ==>
    strict_dom_vars_defined f s'
Proof
  rw[strict_dom_vars_defined_def] >> rpt strip_tac >>
  Cases_on `d_bb.bb_label = s.vs_current_bb`
  >- (
    (* Case 1: d_bb is the block we just ran *)
    `d_bb.bb_label = bb.bb_label` by simp[] >>
    `d_bb = bb` by metis_tac[same_label_same_block] >>
    gvs[] >>
    (* d_inst is at some index idx *)
    `?idx. idx < LENGTH bb.bb_instructions /\
           EL idx bb.bb_instructions = d_inst` by
      metis_tac[MEM_EL] >>
    (* d_inst has outputs, so it's not a terminator *)
    `~is_terminator d_inst.inst_opcode` by (
      spose_not_then assume_tac >>
      `d_inst.inst_outputs = []` by
        metis_tac[terminator_no_outputs, EVERY_MEM] >>
      fs[]) >>
    irule exec_block_outputs_in_fdom >>
    qexistsl_tac [`bb`, `ctx`, `fuel`, `idx`, `s`] >> simp[])
  >- (
    (* Case 2: d_bb is NOT the current block *)
    (* s'.vs_current_bb is a successor of bb *)
    `MEM s'.vs_current_bb (bb_succs bb)` by (
      mp_tac (Q.SPECL [`fuel`, `ctx`, `bb`, `s`, `s'`]
        exec_block_current_bb_in_succs) >>
      simp[] >> disch_then irule >>
      fs[bb_well_formed_def] >>
      rpt strip_tac >> spose_not_then assume_tac >>
      res_tac >> fs[]) >>
    (* fn_cfg_edge from bb to s'.vs_current_bb *)
    `fn_cfg_edge f s.vs_current_bb s'.vs_current_bb` by
      (simp[fn_cfg_edge_def] >> metis_tac[]) >>
    (* d_bb dominates s.vs_current_bb (predecessor of s'.vs_current_bb) *)
    `fn_dominates f d_bb.bb_label s.vs_current_bb` by
      metis_tac[fn_dominates_predecessor] >>
    (* strict dominance: d_bb.bb_label <> s.vs_current_bb *)
    `v IN FDOM s.vs_vars` by metis_tac[] >>
    (* FDOM mono *)
    `FDOM s.vs_vars SUBSET FDOM s'.vs_vars` by
      metis_tac[exec_block_fdom_mono] >>
    metis_tac[pred_setTheory.SUBSET_DEF])
QED

(* ================================================================= *)
(*  Part 5: Operand vars in FDOM at each instruction                 *)
(* ================================================================= *)

(* Under wf_ssa + wf_function + strict_dom_vars_defined + intra-block
   outputs in FDOM, all Var operands at instruction idx are in FDOM.
   def_dominates_uses gives i < j with EL j = EL idx in same-block case.
   inst_ids_el_eq (from fn_inst_ids_distinct) gives j = idx, hence i < idx. *)
Theorem operand_vars_in_fdom:
  !f bb idx s.
    wf_ssa f /\ wf_function f /\ fn_inst_wf f /\
    MEM bb f.fn_blocks /\
    bb.bb_label = s.vs_current_bb /\
    idx < LENGTH bb.bb_instructions /\
    (EL idx bb.bb_instructions).inst_opcode <> PHI /\
    strict_dom_vars_defined f s /\
    (!j v. j < idx /\ MEM v (EL j bb.bb_instructions).inst_outputs ==>
           v IN FDOM s.vs_vars) ==>
    !v. MEM (Var v) (EL idx bb.bb_instructions).inst_operands ==>
        v IN FDOM s.vs_vars
Proof
  rpt strip_tac >>
  fs[wf_ssa_def] >>
  `MEM (EL idx bb.bb_instructions) bb.bb_instructions` by
    metis_tac[MEM_EL] >>
  fs[def_dominates_uses_def] >>
  `def_available_at f bb (SOME (EL idx bb.bb_instructions)) v` by (
    first_x_assum (qspecl_then [`bb`, `EL idx bb.bb_instructions`] mp_tac) >>
    simp[] >> disch_then (qspec_then `v` mp_tac) >> simp[]) >>
  qpat_x_assum `def_available_at f bb _ v`
    (strip_assume_tac o REWRITE_RULE[def_available_at_def]) >>
  Cases_on `def_bb.bb_label = bb.bb_label`
  >- (
    (* Same block: def_bb = bb by label uniqueness *)
    `def_bb = bb` by metis_tac[same_label_same_block] >>
    gvs[] >>
    (* i < j, EL j = EL idx. fn_inst_ids_distinct gives j = idx. *)
    `fn_inst_ids_distinct f` by fs[wf_function_def] >>
    `j = idx` by metis_tac[inst_ids_el_eq] >>
    gvs[] >>
    first_x_assum irule >> simp[] >> metis_tac[])
  >- (
    (* Different block: strict_dom_vars_defined *)
    fs[strict_dom_vars_defined_def] >>
    qpat_x_assum `!d_bb d_inst v. _` (qspecl_then
      [`def_bb`, `def_inst`, `v`] mp_tac) >>
    simp[] >> gvs[])
QED

(* ---- from phiBlock ---- *)

Theorem ssa_form_block_outputs_distinct:
  !fn bb. ssa_form fn /\ MEM bb fn.fn_blocks ==>
    ALL_DISTINCT (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))
Proof
  simp[venomWfTheory.ssa_form_def, venomInstTheory.fn_insts_def] >>
  rpt strip_tac >>
  ntac 2 (pop_assum mp_tac) >>
  qspec_tac (`fn.fn_blocks`, `bbs`) >>
  Induct >> simp[venomInstTheory.fn_insts_blocks_def] >>
  rpt strip_tac >> gvs[ALL_DISTINCT_APPEND, MAP_APPEND, FLAT_APPEND]
QED

(* ---- from phiBlock ---- *)

Triviality step_inst_idx_ok_non_invoke:
  !fuel ctx inst s j s'.
    ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
    step_inst fuel ctx inst s = OK s' ==>
    step_inst fuel ctx inst (s with vs_inst_idx := j) =
      OK (s' with vs_inst_idx := j)
Proof
  rpt strip_tac >>
  `step_inst fuel ctx inst (s with vs_inst_idx := j) =
   exec_result_map (\s'. s' with vs_inst_idx := j) (step_inst fuel ctx inst s)` by
    simp[step_inst_idx_indep] >>
  gvs[instIdxIndepTheory.exec_result_map_def]
QED

Theorem exec_block_skip_prefix_non_invoke:
  !prefix fuel ctx bb s j s'.
    j + LENGTH prefix <= LENGTH bb.bb_instructions /\
    EVERY (\inst. ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE) prefix /\
    (!k. k < LENGTH prefix ==> EL (j + k) bb.bb_instructions = EL k prefix) /\
    run_insts fuel ctx prefix s = OK s' ==>
    exec_block fuel ctx bb (s with vs_inst_idx := j) =
    exec_block fuel ctx bb (s' with vs_inst_idx := j + LENGTH prefix)
Proof
  Induct >> rw[run_insts_def] >>
  rename1 `h :: prefix` >>
  `j < LENGTH bb.bb_instructions` by simp[] >>
  `EL j bb.bb_instructions = h` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  Cases_on `step_inst fuel ctx h s` >> gvs[run_insts_def] >>
  rename1 `step_inst _ _ h s = OK s1` >>
  `step_inst fuel ctx h (s with vs_inst_idx := j) =
     OK (s1 with vs_inst_idx := j)` by
    (irule step_inst_idx_ok_non_invoke >> simp[]) >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
  simp[get_instruction_def] >>
  `bb.bb_instructions❲j❳ = h` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  asm_rewrite_tac[] >> simp[] >>
  first_x_assum (qspecl_then [`fuel`, `ctx`, `bb`, `s1`, `SUC j`, `s'`] mp_tac) >>
  simp[arithmeticTheory.ADD_CLAUSES] >>
  impl_tac
  >- (rw[] >> first_x_assum (qspec_then `SUC k` mp_tac) >>
      simp[arithmeticTheory.ADD_CLAUSES]) >>
  simp[]
QED

(* ---- from phiWellFormed ---- *)

Theorem phi_pairs_resolve_phi_some:
  !ops l v. MEM (l,v) (phi_pairs ops) ==> ?op. resolve_phi l ops = SOME op
Proof
  recInduct phi_pairs_ind >> simp[phi_pairs_def, resolve_phi_def] >>
  rpt strip_tac >> gvs[] >>
  rpt CASE_TAC >> simp[]
  >- metis_tac[] >>
  rename1 `resolve_phi _ (head::_::_)` >>
  Cases_on `head` >> gvs[resolve_phi_def] >>
  rpt CASE_TAC >> simp[] >> metis_tac[]
QED

Theorem resolve_phi_well_formed:
  !prev_bb ops v.
    phi_well_formed ops /\
    resolve_phi prev_bb ops = SOME v ==>
    ?var. v = Var var
Proof
  measureInduct_on `LENGTH ops` >>
  Cases_on `ops` >- rw[resolve_phi_def] >>
  Cases_on `t` >- rw[resolve_phi_def] >>
  Cases_on `h` >> Cases_on `h'` >>
  rpt strip_tac >> fs[resolve_phi_def, phi_well_formed_def] >>
  TRY (Cases_on `s = prev_bb` >> fs[]) >>
  first_x_assum (qspec_then `t'` mp_tac) >> simp[] >>
  strip_tac >> res_tac >> metis_tac[]
QED

(* ---- from removeUnusedProofs ---- *)

(* ALL_DISTINCT outputs in fn_insts_blocks implies same for each block *)
Theorem all_distinct_outputs_block:
  !bbs bb. MEM bb bbs ==>
    ALL_DISTINCT (FLAT (MAP (\inst. inst.inst_outputs)
                            (fn_insts_blocks bbs))) ==>
    ALL_DISTINCT (FLAT (MAP (\inst. inst.inst_outputs)
                            bb.bb_instructions))
Proof
  Induct >> rw[fn_insts_blocks_def] >>
  gvs[listTheory.MAP_APPEND, listTheory.FLAT_APPEND,
      listTheory.ALL_DISTINCT_APPEND]
QED

(* Within a block with ALL_DISTINCT outputs, positions define same var ⟹ same *)
Theorem all_distinct_outputs_unique_pos:
  !insts v i k.
    ALL_DISTINCT (FLAT (MAP (\inst. inst.inst_outputs) insts)) /\
    i < LENGTH insts /\ k < LENGTH insts /\
    MEM v (EL i insts).inst_outputs /\
    MEM v (EL k insts).inst_outputs ==>
    i = k
Proof
  Induct >> rw[] >>
  Cases_on `i` >> Cases_on `k` >> gvs[] >>
  gvs[listTheory.ALL_DISTINCT_APPEND, listTheory.MEM_FLAT,
      listTheory.MEM_MAP] >>
  metis_tac[listTheory.MEM_EL]
QED

(* ssa_form implies: if v is output at position i in block bb,
   then no other position in bb has v as output. *)
Theorem ssa_form_no_dup_in_block:
  !fn bb v i k.
    ssa_form fn /\
    MEM bb fn.fn_blocks /\
    i < LENGTH bb.bb_instructions /\
    k < LENGTH bb.bb_instructions /\
    MEM v (EL i bb.bb_instructions).inst_outputs /\
    MEM v (EL k bb.bb_instructions).inst_outputs ==>
    i = k
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))` by (
    irule all_distinct_outputs_block >>
    qexists_tac `fn.fn_blocks` >> gvs[] >>
    gvs[ssa_form_def, fn_insts_def]) >>
  irule all_distinct_outputs_unique_pos >>
  qexistsl_tac [`bb.bb_instructions`, `v`] >> gvs[]
QED


(* ---- from removeUnusedProofs ---- *)

Theorem all_distinct_flat_map_inj:
  !f (ls:'b list) (a:'b) (b:'b) (x:'a).
    ALL_DISTINCT (FLAT (MAP f ls)) /\
    MEM a ls /\ MEM b ls /\
    MEM x (f a) /\ MEM x (f b) ==> a = b
Proof
  Induct_on `ls` >> simp[] >> rpt strip_tac >>
  gvs[listTheory.ALL_DISTINCT_APPEND, listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
  metis_tac[]
QED

(* fn_insts_blocks = FLAT of per-block instructions *)
Theorem fn_insts_blocks_flat:
  !bbs. fn_insts_blocks bbs = FLAT (MAP (\bb. bb.bb_instructions) bbs)
Proof
  Induct >> simp[fn_insts_blocks_def]
QED

(* ALL_DISTINCT outputs → ALL_DISTINCT per-block flattened outputs *)
Theorem ssa_form_per_block:
  !fn. ssa_form fn ==>
    ALL_DISTINCT (FLAT (MAP (\bb. FLAT (MAP (\i. i.inst_outputs)
      bb.bb_instructions)) fn.fn_blocks))
Proof
  rpt strip_tac >>
  fs[ssa_form_def, fn_insts_def] >>
  pop_assum mp_tac >>
  ONCE_REWRITE_TAC [fn_insts_blocks_flat] >>
  simp[listTheory.MAP_FLAT, rich_listTheory.FLAT_FLAT,
       listTheory.MAP_MAP_o, combinTheory.o_DEF]
QED

(* Under ssa_form, v in outputs of two instructions → same instruction *)
Theorem ssa_outputs_same_inst:
  !fn inst1 inst2 v.
    ssa_form fn /\
    MEM inst1 (fn_insts_blocks fn.fn_blocks) /\
    MEM inst2 (fn_insts_blocks fn.fn_blocks) /\
    MEM v inst1.inst_outputs /\ MEM v inst2.inst_outputs ==>
    inst1 = inst2
Proof
  rpt strip_tac >>
  fs[ssa_form_def, fn_insts_def] >>
  mp_tac (Q.ISPECL [
    `\(i:instruction). i.inst_outputs`,
    `fn_insts_blocks fn.fn_blocks`,
    `inst1:instruction`, `inst2:instruction`, `v:string`
  ] all_distinct_flat_map_inj) >>
  simp[]
QED

(* ---- from removeUnusedSsaProofs ---- *)

(* Helper: operand var in inst_uses *)
Theorem mem_var_operand_vars[local]:
  !ops v. MEM (Var v) ops ==> MEM v (operand_vars ops)
Proof
  Induct >> simp[operand_vars_def] >> rpt strip_tac >> gvs[] >>
  Cases_on `operand_var h` >> simp[] >>
  Cases_on `h` >> gvs[operand_var_def]
QED

Theorem operand_var_in_inst_uses:
  !inst v. MEM (Var v) inst.inst_operands ==>
           MEM v (inst_uses inst)
Proof
  simp[inst_uses_def] >> metis_tac[mem_var_operand_vars]
QED

(* ALL_DISTINCT (FLAT (MAP f l)) + v in two different elements => F *)
Theorem all_distinct_flat_map_cross[local]:
  !f l (x:'a) y (v:'b).
    ALL_DISTINCT (FLAT (MAP f l)) /\
    MEM x l /\ MEM y l /\ x <> y /\
    MEM v (f x) /\ MEM v (f y) ==> F
Proof
  Induct_on `l` >> rw[MEM_FLAT, MEM_MAP, ALL_DISTINCT_APPEND] >> metis_tac[]
QED

(* ALL_DISTINCT (FLAT (MAP f l)) + MEM x l => ALL_DISTINCT (f x) *)
Theorem all_distinct_flat_map_member:
  !(f:'a -> 'b list) l x.
    ALL_DISTINCT (FLAT (MAP f l)) /\ MEM x l ==> ALL_DISTINCT (f x)
Proof
  Induct_on `l` >> rw[ALL_DISTINCT_APPEND] >> metis_tac[]
QED


(* Strongest SSA uniqueness: same output var ⇒ same instruction AND same block *)
Theorem ssa_unique_output_block:
  !fn bb1 inst1 bb2 inst2 v.
    ssa_form fn /\
    MEM bb1 fn.fn_blocks /\ MEM inst1 bb1.bb_instructions /\
    MEM v inst1.inst_outputs /\
    MEM bb2 fn.fn_blocks /\ MEM inst2 bb2.bb_instructions /\
    MEM v inst2.inst_outputs ==> bb1 = bb2 /\ inst1 = inst2
Proof
  rpt strip_tac >> spose_not_then strip_assume_tac >>
  rename1 `ssa_form func` >>
  gvs[ssa_form_def, fn_insts_def, fn_insts_blocks_flat] >>
  (* The key: rewrite the flat-inst ALL_DISTINCT to block-level form *)
  `!bbs. FLAT (MAP (\i:instruction. i.inst_outputs)
              (FLAT (MAP (\bb:basic_block. bb.bb_instructions) bbs))) =
         FLAT (MAP (\bb. FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions))
              bbs)` by
    rw[MAP_FLAT, FLAT_FLAT, MAP_MAP_o, combinTheory.o_DEF] >>
  fs[] >>
  (* Specialize the cross lemma for blocks *)
  qabbrev_tac `bouts = \bb:basic_block.
    FLAT (MAP (\i:instruction. i.inst_outputs) bb.bb_instructions)` >>
  `MEM v (bouts bb1) /\ MEM v (bouts bb2)` by
    (simp[Abbr `bouts`, MEM_FLAT, MEM_MAP] >> metis_tac[])
  >- (
    (* bb1 ≠ bb2: block-level *)
    metis_tac[all_distinct_flat_map_cross])
  >- (
    (* inst1 ≠ inst2: within-block *)
    Cases_on `bb1 = bb2`
    >- (
      gvs[] >>
      drule_all all_distinct_flat_map_member >> strip_tac >>
      gvs[Abbr `bouts`] >>
      metis_tac[all_distinct_flat_map_cross])
    >- metis_tac[all_distinct_flat_map_cross])
QED

(* ===== Boilerplate: reachability / lookup helpers ===== *)

Theorem fn_reachable_in_cfg_dfs_pre:
  !fn lbl. wf_function fn /\ fn_reachable fn lbl ==>
    MEM lbl (cfg_analyze fn).cfg_dfs_pre
Proof
  rpt strip_tac >>
  gvs[fn_reachable_def, fn_entry_label_def, entry_block_def] >>
  Cases_on `NULL fn.fn_blocks` >> gvs[] >>
  (* Goal: MEM lbl cfg_dfs_pre. Strategy: show cfg_reachable_of *)
  `cfg_reachable_of (cfg_analyze fn) lbl` suffices_by (
    strip_tac >>
    `wf_function fn` by simp[] >>
    drule cfg_analyze_reachable_sets >> strip_tac >>
    fs[pred_setTheory.EXTENSION] >> metis_tac[]) >>
  (* cfg_reachable_of ⟺ cfg_path from entry *)
  drule_at Any cfg_analyze_semantic_reachability >>
  disch_then (qspecl_then [`HD fn.fn_blocks`, `lbl`] mp_tac) >>
  simp[entry_block_def] >> strip_tac >>
  (* cfg_path from RTC fn_cfg_edge via RTC_MONOTONE *)
  pop_assum kall_tac >>
  simp[cfg_path_def] >>
  irule relationTheory.RTC_MONOTONE >>
  qexists_tac `fn_cfg_edge fn` >> simp[] >>
  rw[fn_cfg_edge_def] >>
  irule bb_succs_in_cfg_succs >> gvs[wf_function_def]
QED

(* fn_cfg_edge → cfg_succs_of (bridge from path-level to analysis-level) *)
Theorem fn_cfg_edge_succs:
  !fn a b. wf_function fn /\ fn_cfg_edge fn a b ==>
    MEM b (cfg_succs_of (cfg_analyze fn) a)
Proof
  rw[fn_cfg_edge_def] >>
  irule bb_succs_in_cfg_succs >> gvs[wf_function_def]
QED


(* Helper: fn_cfg_edge target has a block *)
Theorem fn_cfg_edge_target_block:
  !fn a b. wf_function fn /\ fn_cfg_edge fn a b ==>
    ?bb. lookup_block b fn.fn_blocks = SOME bb
Proof
  rw[fn_cfg_edge_def, wf_function_def] >> rpt strip_tac >>
  `MEM b (fn_labels fn)` by metis_tac[fn_succs_closed_def] >>
  gvs[fn_labels_def, MEM_MAP] >>
  metis_tac[MEM_lookup_block]
QED

(* Helper: is_fn_path init (drop last element) *)
Theorem is_fn_path_init:
  !fn path x. is_fn_path fn (SNOC x path) ==> is_fn_path fn path
Proof
  Induct_on `path` >> simp[is_fn_path_def, SNOC] >> rpt strip_tac >>
  Cases_on `path` >> gvs[SNOC, is_fn_path_def] >>
  metis_tac[]
QED

(* Helper: is_fn_path last edge *)
Theorem is_fn_path_last_edge:
  !fn path x. is_fn_path fn (SNOC x path) /\ path <> [] ==>
    fn_cfg_edge fn (LAST path) x
Proof
  Induct_on `path` >> simp[SNOC] >> rpt strip_tac >>
  Cases_on `path` >> gvs[SNOC, is_fn_path_def, listTheory.LAST_DEF]
QED

(* Helper: is_fn_path suffix — if d ∈ path, take suffix from d *)
Theorem is_fn_path_mem_suffix:
  !fn path d. is_fn_path fn path /\ MEM d path ==>
    ?suffix. is_fn_path fn (d :: suffix) /\
             LAST (d :: suffix) = LAST path
Proof
  Induct_on `path` >> simp[] >> rpt strip_tac >> gvs[]
  >- (qexists_tac `path` >> Cases_on `path` >> gvs[is_fn_path_def])
  >- (Cases_on `path` >> gvs[is_fn_path_def] >>
      first_x_assum drule_all >> strip_tac >>
      qexists_tac `suffix` >> simp[] >>
      Cases_on `suffix` >> gvs[listTheory.LAST_DEF])
QED

(* Helper: reachable node along path from reachable start *)
Theorem is_fn_path_all_reachable:
  !fn path lbl. is_fn_path fn path /\ path <> [] /\
    fn_reachable fn (HD path) /\ MEM lbl path ==>
    fn_reachable fn lbl
Proof
  Induct_on `path` >> simp[] >> rpt strip_tac >> gvs[] >>
  Cases_on `path` >> gvs[is_fn_path_def, listTheory.MEM]
  >- metis_tac[fn_reachable_step]
  >- (first_x_assum irule >> simp[] >> metis_tac[fn_reachable_step])
QED

(* Helper: reachable implies has a block (via wf_function) *)
Theorem fn_reachable_has_block:
  !fn lbl. wf_function fn /\ fn_reachable fn lbl ==>
    ?bb. lookup_block lbl fn.fn_blocks = SOME bb
Proof
  rpt strip_tac >> gvs[fn_reachable_def] >>
  gvs[Once relationTheory.RTC_CASES2]
  >- (
    (* lbl = entry: entry block exists *)
    gvs[fn_entry_label_def, entry_block_def] >>
    Cases_on `fn.fn_blocks` >> gvs[] >>
    rename1 `hd :: tl` >>
    qexists_tac `hd` >>
    irule MEM_lookup_block >>
    gvs[wf_function_def, fn_labels_def])
  >- metis_tac[fn_cfg_edge_target_block]
QED

(* Availability is a path property independently of any compiler pipeline. *)
Theorem def_available_on_all_paths:
  wf_function fn /\ MEM bb fn.fn_blocks /\ def_available_at fn bb point v ==>
  def_on_all_paths fn bb point v
Proof
  simp[def_available_at_def] >> rpt strip_tac >>
  simp[def_on_all_paths_def] >> rpt strip_tac >>
  Cases_on `def_bb = bb`
  >- (gvs[] >> disj2_tac >> Cases_on `point` >> gvs[]
      >- metis_tac[MEM_EL] >>
      qexists_tac `i` >> simp[] >> metis_tac[arithmeticTheory.LESS_TRANS]) >>
  disj1_tac >>
  `MEM def_bb.bb_label path` by metis_tac[fn_dominates_def] >>
  `def_bb.bb_label <> bb.bb_label` by metis_tac[same_label_same_block] >>
  qpat_x_assum `MEM def_bb.bb_label path` mp_tac >>
  disch_then (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
  rename1 `k < LENGTH path` >>
  qexistsl_tac [`k`, `def_bb`, `def_inst`] >> simp[] >>
  `LAST path = EL (LENGTH path - 1) path` by
    (qspec_then `path` mp_tac LAST_EL >> simp[arithmeticTheory.PRE_SUB1]) >>
  Cases_on `k = LENGTH path - 1` >> gvs[] >> decide_tac
QED

Theorem wf_ssa_defs_reach_uses:
  wf_ssa fn /\ wf_function fn ==> fn_defs_reach_uses fn
Proof
  simp[wf_ssa_def, fn_defs_reach_uses_def, def_dominates_uses_def] >>
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = PHI` >> simp[]
  >- (rpt strip_tac >>
      `phi_edge_uses_wf fn bb inst` by metis_tac[] >>
      qpat_x_assum `phi_edge_uses_wf _ _ _` mp_tac >>
      pure_rewrite_tac[phi_edge_uses_wf_def] >> strip_tac >>
      qpat_x_assum `!pred v. MEM (pred,v) _ ==> _` drule >>
      strip_tac >> rename1 `def_available_at fn source NONE v` >>
      `source = pred_bb` by metis_tac[same_label_same_block] >>
      gvs[] >> irule def_available_on_all_paths >> metis_tac[]) >>
  rpt strip_tac >> irule def_available_on_all_paths >> metis_tac[]
QED

Theorem is_fn_path_take:
  !path n. is_fn_path fn path ==> is_fn_path fn (TAKE n path)
Proof
  Induct >> simp[] >> Cases_on `n` >> simp[] >>
  Cases_on `path` >> simp[is_fn_path_def] >> rpt strip_tac >>
  rename1 `is_fn_path fn (head::TAKE k (next::rest))` >>
  Cases_on `k` >> simp[is_fn_path_def] >>
  rename1 `is_fn_path fn (next::TAKE nn rest)` >>
  first_x_assum (qspec_then `SUC nn` mp_tac) >>
  simp[is_fn_path_def]
QED

Theorem is_fn_path_prefix_at:
  is_fn_path fn path /\ k < LENGTH path ==>
  is_fn_path fn (TAKE (SUC k) path) /\
  TAKE (SUC k) path <> [] /\
  HD (TAKE (SUC k) path) = HD path /\
  LAST (TAKE (SUC k) path) = EL k path /\
  LENGTH (TAKE (SUC k) path) = SUC k
Proof
  strip_tac >> simp[is_fn_path_take, listTheory.LENGTH_TAKE] >>
  `TAKE (SUC k) path <> []` by
    (Cases_on `path` >> gvs[]) >>
  simp[listTheory.LAST_EL, listTheory.LENGTH_TAKE, listTheory.EL_TAKE] >>
  Cases_on `path` >> gvs[]
QED

Theorem distinct_projection_member_eq:
  !xs. ALL_DISTINCT (FLAT (MAP f xs)) ==>
  !x y v. MEM x xs /\ MEM y xs /\ MEM v (f x) /\ MEM v (f y) ==> x = y
Proof
  Induct >> simp[ALL_DISTINCT_APPEND] >> rpt strip_tac >>
  fs[MEM_FLAT, MEM_MAP] >> metis_tac[]
QED

Theorem wf_function_instruction_block:
  wf_function fn /\ MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\
  MEM inst a.bb_instructions /\ MEM inst b.bb_instructions ==> a = b
Proof
  strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions)
     fn.fn_blocks))` by fs[wf_function_def, fn_inst_ids_distinct_def] >>
  drule distinct_projection_member_eq >>
  disch_then (qspecl_then [`a`, `b`, `inst.inst_id`] mp_tac) >>
  simp[MEM_MAP] >> metis_tac[]
QED

Theorem ssa_form_output_unique:
  ssa_form fn /\ MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
  MEM bb' fn.fn_blocks /\ MEM inst' bb'.bb_instructions /\
  MEM v inst.inst_outputs /\ MEM v inst'.inst_outputs ==> inst' = inst
Proof
  strip_tac >> fs[ssa_form_def] >>
  drule distinct_projection_member_eq >>
  disch_then (qspecl_then [`inst'`, `inst`, `v`] mp_tac) >>
  simp[] >> fs[fn_insts_def] >> metis_tac[fmp_fn_insts_blocks_intro]
QED

Theorem is_fn_path_first_arrival:
  !path. path <> [] /\ is_fn_path fn path /\ LAST path = b ==>
  ?pre. is_fn_path fn (pre ++ [b]) /\ HD (pre ++ [b]) = HD path /\
        ~MEM b pre
Proof
  Induct >> simp[] >> qx_gen_tac `a` >> strip_tac >>
  Cases_on `a = b`
  >- (qexists `[]` >> simp[is_fn_path_def]) >>
  Cases_on `path` >- gvs[] >>
  fs[is_fn_path_def] >>
  qexists `a::pre` >> Cases_on `pre` >> gvs[is_fn_path_def]
QED

Theorem def_on_all_paths_first_witness:
  MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
  def_on_all_paths fn bb use_opt v ==>
  ?db di. MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
    MEM v di.inst_outputs /\
    (db = bb ==> case use_opt of NONE => T | SOME use =>
      ?i j. i < j /\ j < LENGTH bb.bb_instructions /\
            EL i bb.bb_instructions = di /\ EL j bb.bb_instructions = use)
Proof
  strip_tac >> fs[fn_reachable_def] >>
  drule rtc_to_fn_path >> strip_tac >>
  `?pre. is_fn_path fn (pre ++ [bb.bb_label]) /\
     HD (pre ++ [bb.bb_label]) = entry /\ ~MEM bb.bb_label pre` by
    metis_tac[is_fn_path_first_arrival] >>
  qpat_x_assum `def_on_all_paths fn bb use_opt v` mp_tac >>
  simp[def_on_all_paths_def] >>
  disch_then (qspec_then `pre ++ [bb.bb_label]` mp_tac) >>
  simp[] >> strip_tac
  >- (qexistsl [`def_bb`, `def_inst`] >> simp[] >>
      `MEM def_bb.bb_label pre` by
        (simp[MEM_EL] >> qexists `k` >> fs[EL_APPEND1]) >>
      `def_bb <> bb` by metis_tac[] >> simp[]) >>
  qexistsl [`bb`, `EL i bb.bb_instructions`] >> simp[EL_MEM] >>
  Cases_on `use_opt` >> gvs[] >> metis_tac[]
QED

Theorem def_on_all_paths_dominating_witness:
  wf_function fn /\ ssa_form fn /\ MEM bb fn.fn_blocks /\
  fn_reachable fn bb.bb_label /\ def_on_all_paths fn bb use_opt v /\
  MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\ MEM v di.inst_outputs ==>
  fn_dominates fn db.bb_label bb.bb_label
Proof
  strip_tac >> simp[fn_dominates_def] >> rpt strip_tac >>
  qpat_x_assum `def_on_all_paths fn bb use_opt v` mp_tac >>
  simp[def_on_all_paths_def] >>
  disch_then (qspec_then `path` mp_tac) >> simp[] >> strip_tac
  >- (`def_inst = di` by metis_tac[ssa_form_output_unique] >>
      `def_bb = db` by metis_tac[wf_function_instruction_block] >>
      gvs[] >> simp[MEM_EL] >> qexists `k` >> simp[]) >>
  `MEM (EL i bb.bb_instructions) bb.bb_instructions` by simp[EL_MEM] >>
  `EL i bb.bb_instructions = di` by metis_tac[ssa_form_output_unique] >>
  `bb = db` by metis_tac[wf_function_instruction_block] >>
  metis_tac[LAST_MEM]
QED

Theorem def_on_all_paths_available:
  wf_function fn /\ ssa_form fn /\ MEM bb fn.fn_blocks /\
  fn_reachable fn bb.bb_label /\ def_on_all_paths fn bb use_opt v ==>
  def_available_at fn bb use_opt v
Proof
  strip_tac >> drule_all def_on_all_paths_first_witness >> strip_tac >>
  simp[def_available_at_def] >> qexistsl [`db`, `di`] >> simp[] >>
  irule def_on_all_paths_dominating_witness >> metis_tac[]
QED

Theorem resolve_phi_pair:
  !p ops v. resolve_phi p ops = SOME (Var v) ==>
    MEM (p,v) (phi_pairs ops)
Proof
  recInduct resolve_phi_ind >>
  rw[resolve_phi_def, phi_pairs_def]
  >- (Cases_on `val_op` >> gvs[phi_pairs_def] >> metis_tac[]) >>
  Cases_on `v2` >> gvs[phi_pairs_def] >> metis_tac[]
QED

Theorem resolved_phi_input_available:
  wf_ssa fn /\ MEM bb fn.fn_blocks /\ MEM i bb.bb_instructions /\
  i.inst_opcode = PHI /\ resolve_phi pred i.inst_operands = SOME (Var v) ==>
  ?pb. MEM pb fn.fn_blocks /\ pb.bb_label = pred /\
    fn_cfg_edge fn pred bb.bb_label /\ def_available_at fn pb NONE v
Proof
  strip_tac >> drule resolve_phi_pair >> strip_tac >>
  fs[wf_ssa_def, def_dominates_uses_def, phi_edge_uses_wf_def] >>
  metis_tac[]
QED

Theorem exec_block_outputs_in_fdom_from_prefix:
  exec_block fuel ctx bb st = OK st' /\
  bb_well_formed bb /\ EVERY inst_wf bb.bb_instructions /\
  (!j w. j < st.vs_inst_idx /\ j < LENGTH bb.bb_instructions /\
         MEM w (EL j bb.bb_instructions).inst_outputs ==>
         w IN FDOM st.vs_vars) /\
  idx < LENGTH bb.bb_instructions /\
  ~is_terminator (EL idx bb.bb_instructions).inst_opcode /\
  MEM v (EL idx bb.bb_instructions).inst_outputs ==>
  v IN FDOM st'.vs_vars
Proof
  rpt strip_tac >> Cases_on `idx < st.vs_inst_idx`
  >- (`v IN FDOM st.vs_vars` by metis_tac[] >>
      drule exec_block_fdom_mono >>
      simp[pred_setTheory.SUBSET_DEF]) >>
  irule exec_block_output_in_fdom_aux >>
  qexistsl [`bb`, `ctx`, `fuel`, `idx`,
            `LENGTH bb.bb_instructions - st.vs_inst_idx`, `st`] >> simp[]
QED

Theorem strict_dom_vars_defined_preserved_from_prefix:
  wf_function f /\ MEM bb f.fn_blocks /\
  bb.bb_label = st.vs_current_bb /\
  exec_block fuel ctx bb st = OK st' /\
  st.vs_inst_idx <= LENGTH bb.bb_instructions /\
  strict_dom_vars_defined f st /\ fn_reachable f st.vs_current_bb /\
  EVERY inst_wf bb.bb_instructions /\
  (!j w. j < st.vs_inst_idx /\ j < LENGTH bb.bb_instructions /\
         MEM w (EL j bb.bb_instructions).inst_outputs ==>
         w IN FDOM st.vs_vars) ==>
  strict_dom_vars_defined f st'
Proof
  rpt strip_tac >>
  `bb_well_formed bb` by gvs[wf_function_def] >>
  simp[strict_dom_vars_defined_def] >> rpt strip_tac >>
  Cases_on `d_bb.bb_label = st.vs_current_bb`
  >- (`d_bb = bb` by
        metis_tac[venomExecProofsTheory.same_label_same_block] >> gvs[] >>
      `?idx. idx < LENGTH bb.bb_instructions /\
             EL idx bb.bb_instructions = d_inst` by
        metis_tac[listTheory.MEM_EL] >>
      `~is_terminator d_inst.inst_opcode` by
        (strip_tac >>
         `d_inst.inst_outputs = []` by
           metis_tac[venomExecProofsTheory.terminator_no_outputs,
                     listTheory.EVERY_MEM] >> gvs[]) >>
      irule exec_block_outputs_in_fdom_from_prefix >>
      qexistsl [`bb`, `ctx`, `fuel`, `idx`, `st`] >> simp[] >>
      metis_tac[]) >>
  `MEM st'.vs_current_bb (bb_succs bb)` by
    (irule exec_block_current_bb_in_succs >>
     conj_tac
     >- (gvs[bb_well_formed_def] >> rpt strip_tac >>
         `i < LENGTH bb.bb_instructions` by decide_tac >>
         `i = PRE (LENGTH bb.bb_instructions)` by metis_tac[] >>
         decide_tac) >>
     `bb.bb_instructions <> []` by gvs[bb_well_formed_def] >>
     simp[] >> qexistsl [`ctx`, `fuel`, `st`] >> simp[]) >>
  `fn_cfg_edge f st.vs_current_bb st'.vs_current_bb` by
    (simp[fn_cfg_edge_def] >> metis_tac[]) >>
  `fn_dominates f d_bb.bb_label st.vs_current_bb` by
    metis_tac[venomExecProofsTheory.fn_dominates_predecessor] >>
  `v IN FDOM st.vs_vars` by
    (gvs[strict_dom_vars_defined_def] >> metis_tac[]) >>
  drule exec_block_fdom_mono >> simp[pred_setTheory.SUBSET_DEF]
QED

Theorem strict_dom_vars_defined_eval_phis:
  strict_dom_vars_defined f st /\ eval_phis st insts = OK st' ==>
  strict_dom_vars_defined f st'
Proof
  rpt strip_tac >>
  `st'.vs_current_bb = st.vs_current_bb` by
    metis_tac[venomExecProofsTheory.eval_phis_preserves_current_bb] >>
  drule venomExecProofsTheory.eval_phis_vars_grow >>
  gvs[strict_dom_vars_defined_def, pred_setTheory.SUBSET_DEF] >> metis_tac[]
QED

Theorem strict_dom_vars_defined_inst_idx[simp]:
  strict_dom_vars_defined f (st with vs_inst_idx := idx) <=>
  strict_dom_vars_defined f st
Proof
  simp[strict_dom_vars_defined_def]
QED

Theorem strict_dom_vars_defined_run_block_entry:
  wf_function f /\ MEM bb f.fn_blocks /\
  bb.bb_label = st.vs_current_bb /\
  run_block_entry fuel ctx bb st = OK st' /\
  strict_dom_vars_defined f st /\ fn_reachable f st.vs_current_bb /\
  EVERY inst_wf bb.bb_instructions ==>
  strict_dom_vars_defined f st'
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`st`, `bb.bb_instructions`]
    venomExecSemanticsTheory.eval_phis_ok_or_error_defs) >> strip_tac >>
  gvs[venomExecSemanticsTheory.run_block_def] >>
  rename1 `eval_phis st bb.bb_instructions = OK st_phi` >>
  irule strict_dom_vars_defined_preserved_from_prefix >> simp[] >>
  qexistsl [`bb`, `ctx`, `fuel`,
            `st_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions`] >>
  simp[venomExecProofsTheory.phi_prefix_length_le] >>
  `st_phi.vs_current_bb = st.vs_current_bb` by
    metis_tac[venomExecProofsTheory.eval_phis_preserves_current_bb] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >>
      drule_all venomExecProofsTheory.eval_phis_outputs_in_fdom_idx >> simp[]) >>
  drule_all strict_dom_vars_defined_eval_phis >> simp[]
QED

(* Contiguous predicate prefixes, shared by pass and pipeline proofs. *)
Theorem every_prefix_split:
  !P l. (!i j. i < j /\ j < LENGTH l /\ P (EL j l) ==> P (EL i l)) <=>
        ?ps rs. l = ps ++ rs /\ EVERY P ps /\ EVERY (\x. ~P x) rs
Proof
  rpt gen_tac >> eq_tac
  >- (qid_spec_tac `l` >> Induct >- simp[] >>
      rpt strip_tac >>
      `?ps rs. l = ps ++ rs /\ EVERY P ps /\ EVERY (\x. ~P x) rs` by
        (first_x_assum irule >> rpt strip_tac >>
         first_x_assum (qspecl_then [`SUC i`,`SUC j`] mp_tac) >> simp[]) >>
      Cases_on `P h`
      >- (qexistsl [`h::ps`,`rs`] >> simp[]) >>
      qexistsl [`[]`,`h::l`] >> simp[listTheory.EVERY_EL] >>
      rpt strip_tac >>
      first_x_assum (qspecl_then [`0`,`SUC n`] mp_tac) >> simp[]) >>
  rpt strip_tac >> gvs[] >>
  Cases_on `j < LENGTH ps`
  >- (`i < LENGTH ps` by simp[] >>
      gvs[rich_listTheory.EL_APPEND1, listTheory.EVERY_EL]) >>
  gvs[rich_listTheory.EL_APPEND2, listTheory.EVERY_EL, arithmeticTheory.NOT_LESS] >>
  first_x_assum (qspec_then `j - LENGTH ps` mp_tac) >> simp[]
QED

Theorem pseudos_prefix_split:
  pseudos_prefix bb <=>
  ?ps rs. bb.bb_instructions = ps ++ rs /\
    EVERY (\i. is_pseudo i.inst_opcode) ps /\
    EVERY (\i. ~is_pseudo i.inst_opcode) rs
Proof
  simp[pseudos_prefix_def] >>
  qspecl_then [`\i. is_pseudo i.inst_opcode`, `bb.bb_instructions`]
    mp_tac every_prefix_split >>
  simp[]
QED

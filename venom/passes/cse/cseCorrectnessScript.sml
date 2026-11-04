(*
 * CSE — Correctness Statement
 *
 * Replacing a redundant computation with ASSIGN from the available
 * expression's result preserves semantics.
 *)

Theory cseCorrectness
Ancestors
  cseProofs cseDefs venomInst venomWf passSharedDefs passSharedProps
  passSimulationDefs passSimulationProps list rich_list While
Libs
  BasicProvers

Theorem cse_function_correct:
  !fuel ctx fn s.
    wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
    (!inst. MEM inst (fn_insts fn) ==> inst.inst_opcode <> ALLOCA) /\
    s.vs_inst_idx = 0 /\ fn_entry_label fn = SOME s.vs_current_bb ==>
    (?e. run_blocks fuel ctx fn s = Error e) \/
    lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (cse_function fn) s)
Proof
  ACCEPT_TAC cse_function_correct_proof
QED

(* ===== Shape of the transform ===== *)

(* cse_inst keeps the instruction, or turns a non-terminator, non-PHI
   instruction into an ASSIGN, or into a NOP when it has no outputs. *)
Theorem cse_inst_shape[local]:
  !ids canon dav inst.
    cse_inst ids canon dav inst = inst \/
    (~is_terminator inst.inst_opcode /\ inst.inst_opcode <> PHI /\
     ((?op. cse_inst ids canon dav inst = mk_assign_inst inst op) \/
      (cse_inst ids canon dav inst = mk_nop_inst inst /\
       inst.inst_outputs = [])))
Proof
  rpt gen_tac >> PairCases_on `dav` >>
  Cases_on `inst.inst_opcode = PHI`
  >- simp[cse_inst_def, cse_skip_opcode_def] >>
  Cases_on `is_terminator inst.inst_opcode`
  >- simp[cse_inst_def] >>
  simp[cse_inst_def] >>
  rpt (TOP_CASE_TAC >> gvs[]) >>
  metis_tac[]
QED

Theorem cse_inst_terminator[local]:
  !ids canon dav inst.
    is_terminator inst.inst_opcode ==> cse_inst ids canon dav inst = inst
Proof
  rpt gen_tac >> PairCases_on `dav` >> rw[cse_inst_def]
QED

Theorem cse_inst_props[local]:
  !ids canon dav inst.
    (cse_inst ids canon dav inst).inst_id = inst.inst_id /\
    ((cse_inst ids canon dav inst).inst_outputs = inst.inst_outputs \/
     (cse_inst ids canon dav inst).inst_outputs = []) /\
    (~is_terminator inst.inst_opcode ==>
     ~is_terminator (cse_inst ids canon dav inst).inst_opcode) /\
    (inst.inst_opcode = PHI ==>
     (cse_inst ids canon dav inst).inst_opcode = PHI) /\
    (inst.inst_opcode <> PHI ==>
     (cse_inst ids canon dav inst).inst_opcode <> PHI)
Proof
  rpt gen_tac >>
  qspecl_then [`ids`, `canon`, `dav`, `inst`] strip_assume_tac
    cse_inst_shape >>
  gvs[mk_assign_inst_def, mk_nop_inst_def, is_terminator_def]
QED

Theorem cse_single_pass_mapi[local]:
  !fn. ?g. (!bb i inst. ?ids canon dav. g bb i inst = cse_inst ids canon dav inst) /\
           cse_single_pass fn =
           function_map_transform
             (\bb. bb with bb_instructions := MAPi (g bb) bb.bb_instructions) fn
Proof
  gen_tac >>
  qexists_tac `\bb idx inst.
    cse_inst (set (MAP (\inst. inst.inst_id) bb.bb_instructions))
      (compute_canon (dfg_build_function fn) (avail_analyze fn) fn)
      (dfg_build_function fn, df_at NONE (avail_analyze fn) bb.bb_label idx)
      inst` >>
  simp[] >> conj_tac >- metis_tac[] >>
  simp[cse_single_pass_def, function_map_transform_def,
       ir_function_component_equality, MAP_EQ_f] >>
  simp[cse_block_transform_def, LET_THM]
QED

Theorem mapi_outputs_sublist[local]:
  !l (f:num -> instruction -> instruction).
    (!i inst. (f i inst).inst_outputs = inst.inst_outputs \/
              (f i inst).inst_outputs = []) ==>
    sublist (FLAT (MAP (\i. i.inst_outputs) (MAPi f l)))
            (FLAT (MAP (\i. i.inst_outputs) l))
Proof
  Induct >> simp[rich_listTheory.sublist_nil] >> rpt strip_tac >>
  `sublist (FLAT (MAP (\i. i.inst_outputs) (MAPi (f o SUC) l)))
           (FLAT (MAP (\i. i.inst_outputs) l))`
    by (first_x_assum irule >> simp[]) >>
  first_x_assum (qspecl_then [`0`, `h`] strip_assume_tac) >>
  fs[combinTheory.o_DEF]
  >- (irule rich_listTheory.sublist_append_pair >>
      simp[rich_listTheory.sublist_refl])
  >- (irule rich_listTheory.sublist_append_include >> simp[])
QED

(* Unlike mapi_transform_preserves_ssa_bb, needs no wf_function. *)
Theorem mapi_transform_preserves_ssa_form[local]:
  !(g : basic_block -> num -> instruction -> instruction) fn.
    (!bb i inst. (g bb i inst).inst_outputs = inst.inst_outputs \/
                 (g bb i inst).inst_outputs = []) /\
    ssa_form fn ==>
    ssa_form (function_map_transform
      (\bb. bb with bb_instructions := MAPi (g bb) bb.bb_instructions) fn)
Proof
  rpt strip_tac >> fs[ssa_form_def] >>
  irule rich_listTheory.sublist_ALL_DISTINCT >>
  qexists_tac `FLAT (MAP (\i. i.inst_outputs) (fn_insts fn))` >> simp[] >>
  simp[fn_insts_def, function_map_transform_def] >>
  Q.SPEC_TAC (`fn.fn_blocks`, `bbs`) >>
  Induct >> simp[fn_insts_blocks_def, rich_listTheory.sublist_nil] >>
  rpt strip_tac >>
  irule rich_listTheory.sublist_append_pair >> simp[] >>
  REWRITE_TAC [GSYM indexedListsTheory.MAP_MAPi] >>
  irule mapi_outputs_sublist >> simp[]
QED

Theorem cse_single_pass_preserves_ssa_form[local]:
  !fn. ssa_form fn ==> ssa_form (cse_single_pass fn)
Proof
  rpt strip_tac >>
  qspec_then `fn` strip_assume_tac cse_single_pass_mapi >>
  pop_assum SUBST1_TAC >>
  irule mapi_transform_preserves_ssa_form >> simp[] >>
  metis_tac[cse_inst_props]
QED

Theorem cse_single_pass_preserves_wf_function[local]:
  !fn. wf_function fn ==> wf_function (cse_single_pass fn)
Proof
  rpt strip_tac >>
  qspec_then `fn` strip_assume_tac cse_single_pass_mapi >>
  pop_assum SUBST1_TAC >>
  irule mapi_transform_preserves_wf_bb >> simp[] >>
  metis_tac[cse_inst_props, cse_inst_terminator]
QED

Theorem cse_iterate_inv[local]:
  !P fn fn'.
    P fn /\ (!x. P x ==> P (cse_single_pass x)) /\
    cse_iterate fn = SOME fn' ==> P fn'
Proof
  rpt strip_tac >> fs[cse_iterate_def] >>
  qpat_x_assum `OWHILE _ _ _ = _` mp_tac >>
  Q.SPEC_TAC (`fn'`, `fn'`) >>
  ho_match_mp_tac (GEN_ALL WhileTheory.OWHILE_INV_IND) >>
  simp[]
QED

(* ===== Obligations ===== *)

Theorem cse_preserves_ssa_form:
  ∀fn. ssa_form fn ⇒ ssa_form (cse_function fn)
Proof
  rpt strip_tac >> simp[cse_function_def] >>
  Cases_on `cse_iterate fn` >> simp[] >>
  irule clear_nops_function_preserves_ssa >> fs[] >>
  irule (Q.SPEC `ssa_form` cse_iterate_inv) >>
  simp[cse_single_pass_preserves_ssa_form] >>
  qexists_tac `fn` >> simp[]
QED

Theorem cse_preserves_wf_function:
  ∀fn. wf_function fn ⇒ wf_function (cse_function fn)
Proof
  rpt strip_tac >> simp[cse_function_def] >>
  Cases_on `cse_iterate fn` >> simp[] >>
  irule clear_nops_function_preserves_wf >> fs[] >>
  irule (Q.SPEC `wf_function` cse_iterate_inv) >>
  simp[cse_single_pass_preserves_wf_function] >>
  qexists_tac `fn` >> simp[]
QED

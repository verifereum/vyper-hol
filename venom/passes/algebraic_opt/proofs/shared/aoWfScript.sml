(* Algebraic Optimization — Well-formedness & SSA Preservation
 *
 * Key lemmas:
 *   ao_fresh_id_gt_mid     — fresh IDs are > max_id
 *   ao_fresh_id_inj        — fresh IDs are injective in (id, slot)
 *   ao_transform_function preserves wf_function and ssa_form
 *)

Theory aoWf
Ancestors
  algebraicOptDefs aoPhase1Wf aoPeepholeSim aoResolveSim
  venomState venomWf venomInst passSimulationProps passSimulationDefs
  passSharedDefs analysisSimDefs
Libs
  pairLib BasicProvers

(* ===== ao_fresh_id properties ===== *)

Theorem ao_fresh_id_gt:
  !mid id slot. ao_fresh_id mid id slot > mid
Proof
  simp[ao_fresh_id_def]
QED

Theorem ao_fresh_id_ge:
  !mid id slot. ao_fresh_id mid id slot >= mid + 1
Proof
  simp[ao_fresh_id_def]
QED

Theorem ao_fresh_id_inj:
  !mid id1 slot1 id2 slot2.
    slot1 < 3 /\ slot2 < 3 /\
    ao_fresh_id mid id1 slot1 = ao_fresh_id mid id2 slot2 ==>
    id1 = id2 /\ slot1 = slot2
Proof
  simp[ao_fresh_id_def] >> rpt strip_tac >>
  `id1 * 3 + slot1 = id2 * 3 + slot2` by simp[] >>
  `(id1 * 3 + slot1) MOD 3 = (id2 * 3 + slot2) MOD 3` by simp[] >>
  `slot1 MOD 3 = slot2 MOD 3` by metis_tac[arithmeticTheory.MOD_TIMES] >>
  `slot1 = slot2` by metis_tac[arithmeticTheory.LESS_MOD]
QED

(* FOLDL MAX monotone: a <= FOLDL MAX a l *)
Triviality foldl_max_base[local]:
  !(l:num list) a. a <= FOLDL MAX a l
Proof
  Induct >> simp[] >> rpt gen_tac >>
  `MAX a h <= FOLDL MAX (MAX a h) l` suffices_by simp[] >>
  metis_tac[]
QED

(* FOLDL MAX monotone in accumulator *)
Triviality foldl_max_mono[local]:
  !(l:num list) a b. a <= b ==> FOLDL MAX a l <= FOLDL MAX b l
Proof
  Induct >> simp[arithmeticTheory.MAX_DEF]
QED

(* MEM x l ==> x <= FOLDL MAX a l *)
Triviality foldl_max_mem[local]:
  !(l:num list) x a. MEM x l ==> x <= FOLDL MAX a l
Proof
  Induct >> simp[] >> rpt gen_tac >>
  DISCH_THEN DISJ_CASES_TAC
  >- (pop_assum SUBST_ALL_TAC >>
      match_mp_tac arithmeticTheory.LESS_EQ_TRANS >>
      qexists_tac `MAX a h` >>
      conj_tac >- simp[arithmeticTheory.MAX_LE]
      >- MATCH_ACCEPT_TAC foldl_max_base)
  >- (match_mp_tac arithmeticTheory.LESS_EQ_TRANS >>
      qexists_tac `FOLDL MAX a l` >>
      conj_tac
      >- (first_x_assum match_mp_tac >> simp[])
      >- (irule foldl_max_mono >> simp[]))
QED

(* Any original ID <= fn_max_inst_id *)
Theorem fn_max_inst_id_bound:
  !fn inst. MEM inst (fn_insts fn) ==> inst.inst_id <= fn_max_inst_id fn
Proof
  rpt strip_tac >>
  simp[fn_max_inst_id_def] >>
  irule foldl_max_mem >>
  simp[listTheory.MEM_MAP] >>
  metis_tac[]
QED

(* ===== Phase 1: offset lemmas (ao_handle_offset_inst_*, term_not_add,
   ao_phase1_preserves_wf/ssa) reused from aoPhase1Wf ancestor. ===== *)

(* Well-formed terminators have no outputs *)
Triviality terminator_no_outputs[local]:
  !inst. inst_wf inst /\ is_terminator inst.inst_opcode ==>
    inst.inst_outputs = []
Proof
  rw[inst_wf_def] >> Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]
QED

(* ===== ao_resolve_iszero_inst properties ===== *)

Theorem ao_resolve_iszero_inst_opcode:
  !targets inst.
    (ao_resolve_iszero_inst targets inst).inst_opcode = inst.inst_opcode
Proof
  simp[ao_resolve_iszero_inst_def]
QED

Theorem ao_resolve_iszero_inst_id:
  !targets inst.
    (ao_resolve_iszero_inst targets inst).inst_id = inst.inst_id
Proof
  simp[ao_resolve_iszero_inst_def]
QED

Theorem ao_resolve_iszero_inst_outputs:
  !targets inst.
    (ao_resolve_iszero_inst targets inst).inst_outputs = inst.inst_outputs
Proof
  simp[ao_resolve_iszero_inst_def]
QED

(* ===== ao_transform_inst structural properties ===== *)

(* When inst has empty outputs (terminators), ao_transform_inst returns
   a singleton with the same opcode *)
Theorem ao_transform_inst_empty_outputs:
  !mid dfg ra lbl idx targets inst.
    inst.inst_outputs = [] ==>
    ao_transform_inst mid dfg ra lbl idx targets inst =
      [ao_resolve_iszero_inst targets inst]
Proof
  simp[ao_transform_inst_def, LET_THM, ao_resolve_iszero_inst_outputs]
QED

(* PHI maps to singleton *)
Theorem ao_transform_inst_phi:
  !mid dfg ra lbl idx targets inst.
    inst.inst_opcode = PHI ==>
    ao_transform_inst mid dfg ra lbl idx targets inst =
      [ao_resolve_iszero_inst targets inst]
Proof
  simp[ao_transform_inst_def, LET_THM, ao_resolve_iszero_inst_opcode]
QED

(* ASSIGN maps to singleton *)
Theorem ao_transform_inst_assign:
  !mid dfg ra lbl idx targets inst.
    inst.inst_opcode = ASSIGN ==>
    ao_transform_inst mid dfg ra lbl idx targets inst =
      [ao_resolve_iszero_inst targets inst]
Proof
  simp[ao_transform_inst_def, LET_THM, ao_resolve_iszero_inst_opcode]
QED

(* ===== ALL_DISTINCT bound split ===== *)

(* If every element is either <= mid or > mid, and both halves are
   ALL_DISTINCT, then the whole list is ALL_DISTINCT *)
Theorem all_distinct_bound_split:
  !(l:num list) mid.
    ALL_DISTINCT (FILTER (\id. id <= mid) l) /\
    ALL_DISTINCT (FILTER (\id. ~(id <= mid)) l) ==>
    ALL_DISTINCT l
Proof
  Induct >> simp[] >> rpt strip_tac >>
  Cases_on `h <= mid` >> gvs[listTheory.MEM_FILTER] >>
  first_x_assum irule >>
  metis_tac[listTheory.FILTER_ALL_DISTINCT]
QED

Theorem all_distinct_pred_split:
  !(l:'a list) P.
    ALL_DISTINCT (FILTER P l) /\
    ALL_DISTINCT (FILTER ($~ o P) l) ==>
    ALL_DISTINCT l
Proof
  Induct >> simp[] >> rpt strip_tac >>
  Cases_on `P h` >> gvs[listTheory.MEM_FILTER] >>
  first_x_assum irule >>
  metis_tac[listTheory.FILTER_ALL_DISTINCT]
QED

(* ===== Top-level preservation ===== *)

(* Phase 1 transform equals function_map_transform *)
Triviality ao_phase1_eq_fmt[local]:
  !fn. fn with fn_blocks :=
    MAP (\bb. bb with bb_instructions :=
      MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks =
    function_map_transform (block_map_transform ao_handle_offset_inst) fn
Proof
  simp[function_map_transform_def, block_map_transform_def,
       ir_function_component_equality, listTheory.MAP_EQ_f]
QED

(* ===== ao_transform_inst: non-empty, non-term, non-phi ===== *)

(* ao_opt_producer: non-empty result when SOME *)
Triviality ao_opt_producer_ne[local]:
  !dfg inst r. ao_opt_producer dfg inst = SOME r ==> r <> []
Proof
  rw[ao_opt_producer_def] >>
  every_case_tac >> gvs[]
QED

(* ao_post_flip preserves opcode *)
Triviality ao_post_flip_opcode[local]:
  !inst. (ao_post_flip_inst inst).inst_opcode = inst.inst_opcode
Proof
  rw[ao_post_flip_inst_def] >> every_case_tac >> simp[]
QED

(* ao_pre_flip preserves opcode *)
Triviality ao_pre_flip_opcode[local]:
  !inst. (ao_pre_flip_inst inst).inst_opcode = inst.inst_opcode
Proof
  rw[ao_pre_flip_inst_def] >> every_case_tac >> simp[]
QED

Triviality ao_opt_comparator_ne[local]:
  !mid dfg ra lbl idx inst.
    ao_opt_comparator mid dfg ra lbl idx inst <> []
Proof
  rpt gen_tac
  >> simp[ao_opt_comparator_def, LET_THM]
  >> Cases_on `inst.inst_operands` >> simp[]
  >> Cases_on `t` >> simp[]
  >> Cases_on `t'`
  >- (IF_CASES_TAC >> simp[]
      >> simp[ao_unsigned_boundaries_def, ao_signed_boundaries_def, LET_THM]
      >> Cases_on `ao_opt_cmp_range ra lbl idx inst
           (inst.inst_opcode = GT \/ inst.inst_opcode = SGT)
           (inst.inst_opcode = SGT \/ inst.inst_opcode = SLT)`
      >> simp[]
      >> rpt (IF_CASES_TAC >> simp[])
      >> simp[ao_cmp_prefer_iz_zero_def, ao_cmp_prefer_iz_max_def,
              ao_cmp_prefer_iz_general_def, LET_THM]
      >> every_case_tac >> simp[])
  >> simp[]
QED

Triviality ao_peephole_inst_ne[local]:
  !mid dfg ra lbl idx inst.
    ao_peephole_inst mid dfg ra lbl idx inst <> []
Proof
  rpt gen_tac
  >> simp[ao_peephole_inst_def, LET_THM]
  >> rpt (IF_CASES_TAC >> simp[])
  >> simp[ao_opt_shift_def, ao_opt_signextend_def, ao_opt_exp_def,
          ao_opt_addsub_def, ao_opt_and_def, ao_opt_muldiv_def,
          ao_opt_or_def, ao_opt_eq_def, ao_opt_comparator_ne, LET_THM]
  >> every_case_tac
QED

(* ao_transform_inst always returns non-empty.
   Each branch of ao_transform_inst returns a non-empty list:
   - outputs=[] or PHI/ASSIGN/PARAM: [inst0]
   - ao_opt_producer SOME: MAP post_flip (non-empty by ao_opt_producer_ne)
   - peephole: MAP post_flip (ao_peephole_inst ...) — every ao_opt_* returns non-empty *)
Theorem ao_transform_inst_ne:
  !mid dfg ra lbl idx targets inst.
    ao_transform_inst mid dfg ra lbl idx targets inst <> []
Proof
  rpt gen_tac >>
  simp[ao_transform_inst_def, LET_THM] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  Cases_on `ao_opt_producer dfg (ao_resolve_iszero_inst targets inst)`
  >- simp[listTheory.MAP_EQ_NIL, ao_peephole_inst_ne]
  >- (simp[listTheory.MAP_EQ_NIL] >> drule ao_opt_producer_ne >> simp[])
QED

(* ao_transform_inst: terminators are preserved (given inst_wf) *)
Theorem ao_transform_inst_term:
  !mid dfg ra lbl idx targets inst.
    inst_wf inst /\ is_terminator inst.inst_opcode ==>
    ao_transform_inst mid dfg ra lbl idx targets inst =
      [ao_resolve_iszero_inst targets inst]
Proof
  rpt strip_tac >>
  `inst.inst_outputs = []` by metis_tac[terminator_no_outputs] >>
  simp[ao_transform_inst_def, LET_THM, ao_resolve_iszero_inst_outputs]
QED

(* ao_opt_producer: results are non-terminator *)
Triviality ao_opt_producer_non_term[local]:
  !dfg inst r.
    ao_opt_producer dfg inst = SOME r /\ ~is_terminator inst.inst_opcode ==>
    EVERY (\i. ~is_terminator i.inst_opcode) r
Proof
  rw[ao_opt_producer_def] >>
  every_case_tac >> gvs[is_terminator_def, listTheory.EVERY_DEF]
QED

(* ao_opt_producer: results are non-PHI *)
Triviality ao_opt_producer_non_phi[local]:
  !dfg inst r.
    ao_opt_producer dfg inst = SOME r /\ inst.inst_opcode <> PHI ==>
    EVERY (\i. i.inst_opcode <> PHI) r
Proof
  rw[ao_opt_producer_def] >>
  every_case_tac >> gvs[listTheory.EVERY_DEF]
QED

(* resolve preserves Label operands *)
Triviality resolve_op_label[local]:
  !targets opc lbl.
    ao_resolve_iszero_op targets opc (Label lbl) = Label lbl
Proof
  simp[ao_resolve_iszero_op_def]
QED

(* resolve_op preserves get_label *)
Triviality resolve_op_get_label[local]:
  !targets opc op.
    IS_SOME (get_label op) ==>
    IS_SOME (get_label (ao_resolve_iszero_op targets opc op))
Proof
  Cases_on `op` >>
  simp[venomStateTheory.get_label_def, ao_resolve_iszero_op_def]
QED

(* resolve_op preserves get_label when target chains have no labels *)
Triviality resolve_op_get_label_eq[local]:
  !targets opc op.
    (!v chain. ALOOKUP targets v = SOME chain ==>
       EVERY (\op. get_label op = NONE) chain) ==>
    get_label (ao_resolve_iszero_op targets opc op) = get_label op
Proof
  Cases_on `op` >>
  simp[venomStateTheory.get_label_def, ao_resolve_iszero_op_def] >>
  rpt strip_tac >> every_case_tac >>
  simp[venomStateTheory.get_label_def] >>
  gvs[] >> first_x_assum drule >> simp[listTheory.EVERY_EL]
QED

(* get_successors preserved by ao_resolve_iszero_inst *)
Triviality resolve_inst_get_successors[local]:
  !targets inst.
    (!v chain. ALOOKUP targets v = SOME chain ==>
       EVERY (\op. get_label op = NONE) chain) ==>
    get_successors (ao_resolve_iszero_inst targets inst) =
    get_successors inst
Proof
  rpt strip_tac >>
  simp[get_successors_def, ao_resolve_iszero_inst_def,
       ao_resolve_iszero_inst_opcode] >>
  IF_CASES_TAC >> simp[] >>
  simp[listTheory.MAP_MAP_o, combinTheory.o_DEF] >>
  AP_TERM_TAC >> AP_TERM_TAC >>
  irule listTheory.MAP_CONG >> simp[] >> rpt strip_tac >>
  irule resolve_op_get_label_eq >> metis_tac[]
QED

(* ao_resolve_iszero_inst preserves inst_wf for non-PHI opcodes.
   resolve only changes operand VALUES (not LENGTH), and preserves Labels. *)
Theorem ao_resolve_iszero_inst_wf:
  !targets inst.
    inst_wf inst /\ inst.inst_opcode <> PHI ==>
    inst_wf (ao_resolve_iszero_inst targets inst)
Proof
  rpt strip_tac >>
  fs[ao_resolve_iszero_inst_def, inst_wf_def] >>
  Cases_on `inst.inst_opcode` >> gvs[listTheory.LENGTH_MAP] >>
  simp[resolve_op_label, ao_resolve_iszero_op_def] >>
  fs[listTheory.EVERY_MAP, listTheory.EVERY_MEM] >>
  rpt strip_tac >> res_tac >>
  irule resolve_op_get_label >> simp[]
QED

(* ao_pre_flip_inst preserves inst_wf *)
Triviality ao_pre_flip_inst_wf[local]:
  !inst. inst_wf inst ==> inst_wf (ao_pre_flip_inst inst)
Proof
  rpt strip_tac >>
  gvs[ao_pre_flip_inst_def] >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  Cases_on `t'` >> gvs[] >>
  IF_CASES_TAC >> gvs[] >>
  fs[inst_wf_def]
QED

(* ao_transform_inst: non-terminators produce only non-terminators *)
Theorem ao_transform_inst_non_term:
  !mid dfg ra lbl idx targets inst.
    inst_wf inst /\ ~is_terminator inst.inst_opcode ==>
    EVERY (\i. ~is_terminator i.inst_opcode)
          (ao_transform_inst mid dfg ra lbl idx targets inst)
Proof
  rpt strip_tac >>
  simp[ao_transform_inst_def, LET_THM] >>
  `~is_terminator (ao_resolve_iszero_inst targets inst).inst_opcode` by
    simp[ao_resolve_iszero_inst_opcode] >>
  rpt (IF_CASES_TAC >> simp[listTheory.EVERY_DEF]) >>
  Cases_on `ao_opt_producer dfg (ao_resolve_iszero_inst targets inst)`
  >- (* NONE: peephole path *)
     (`EVERY (\i. ~is_terminator i.inst_opcode)
             (ao_peephole_inst mid dfg ra lbl idx
               (ao_pre_flip_inst (ao_resolve_iszero_inst targets inst)))` by (
        irule ao_peephole_inst_non_term >>
        simp[ao_pre_flip_opcode, ao_resolve_iszero_inst_opcode] >>
        irule ao_pre_flip_inst_wf >>
        irule ao_resolve_iszero_inst_wf >>
        gvs[ao_resolve_iszero_inst_opcode]) >>
      simp[listTheory.EVERY_MAP, ao_post_flip_opcode] >>
      fs[listTheory.EVERY_MEM] >> rpt strip_tac >>
      res_tac >> simp[ao_post_flip_opcode])
  >- (* SOME: producer path *)
     (simp[listTheory.EVERY_MAP, ao_post_flip_opcode] >>
      fs[listTheory.EVERY_MEM] >> rpt strip_tac >>
      `EVERY (\i. ~is_terminator i.inst_opcode) x` by (
        drule ao_opt_producer_non_term >>
        simp[ao_resolve_iszero_inst_opcode]) >>
      fs[listTheory.EVERY_MEM] >> res_tac >> simp[ao_post_flip_opcode])
QED

(* Each ao_opt_* function returns instructions with non-PHI opcodes *)
Triviality opt_shift_non_phi[local]:
  !inst. inst.inst_opcode <> PHI ==>
    EVERY (\i. i.inst_opcode <> PHI) (ao_opt_shift inst)
Proof
  simp[ao_opt_shift_def] >> rpt gen_tac >> strip_tac >>
  every_case_tac >> simp[listTheory.EVERY_DEF]
QED

Triviality opt_exp_non_phi[local]:
  !inst. inst.inst_opcode <> PHI ==>
    EVERY (\i. i.inst_opcode <> PHI) (ao_opt_exp inst)
Proof
  simp[ao_opt_exp_def] >> rpt gen_tac >> strip_tac >>
  every_case_tac >> simp[listTheory.EVERY_DEF]
QED

Triviality opt_addsub_non_phi[local]:
  !inst. inst.inst_opcode <> PHI ==>
    EVERY (\i. i.inst_opcode <> PHI) (ao_opt_addsub inst)
Proof
  simp[ao_opt_addsub_def, LET_THM] >> rpt gen_tac >> strip_tac >>
  every_case_tac >> simp[listTheory.EVERY_DEF]
QED

Triviality opt_and_non_phi[local]:
  !inst. inst.inst_opcode <> PHI ==>
    EVERY (\i. i.inst_opcode <> PHI) (ao_opt_and inst)
Proof
  simp[ao_opt_and_def] >> rpt gen_tac >> strip_tac >>
  every_case_tac >> simp[listTheory.EVERY_DEF]
QED

Triviality opt_muldiv_non_phi[local]:
  !inst. inst.inst_opcode <> PHI ==>
    EVERY (\i. i.inst_opcode <> PHI) (ao_opt_muldiv inst)
Proof
  simp[ao_opt_muldiv_def, LET_THM] >> rpt gen_tac >> strip_tac >>
  every_case_tac >> simp[listTheory.EVERY_DEF]
QED

Triviality opt_or_non_phi[local]:
  !dfg inst. inst.inst_opcode <> PHI ==>
    EVERY (\i. i.inst_opcode <> PHI) (ao_opt_or dfg inst)
Proof
  simp[ao_opt_or_def] >> rpt gen_tac >> strip_tac >>
  every_case_tac >> simp[listTheory.EVERY_DEF]
QED

Triviality opt_eq_non_phi[local]:
  !mid dfg inst. inst.inst_opcode <> PHI ==>
    EVERY (\i. i.inst_opcode <> PHI) (ao_opt_eq mid dfg inst)
Proof
  simp[ao_opt_eq_def, LET_THM] >> rpt gen_tac >> strip_tac >>
  every_case_tac >> simp[listTheory.EVERY_DEF]
QED

Triviality opt_signextend_non_phi[local]:
  !ra lbl idx inst. inst.inst_opcode <> PHI ==>
    EVERY (\i. i.inst_opcode <> PHI) (ao_opt_signextend ra lbl idx inst)
Proof
  simp[ao_opt_signextend_def, LET_THM] >> rpt gen_tac >> strip_tac >>
  every_case_tac >> simp[listTheory.EVERY_DEF]
QED

Triviality opt_comparator_non_phi[local]:
  !mid dfg ra lbl idx inst.
    inst.inst_opcode <> PHI ==>
    EVERY (\i. i.inst_opcode <> PHI)
          (ao_opt_comparator mid dfg ra lbl idx inst)
Proof
  rpt strip_tac >>
  simp[ao_opt_comparator_def, LET_THM] >>
  Cases_on `inst.inst_operands` >> simp[listTheory.EVERY_DEF] >>
  Cases_on `t` >> simp[listTheory.EVERY_DEF] >>
  Cases_on `t'` >> simp[listTheory.EVERY_DEF] >>
  simp[ao_unsigned_boundaries_def, ao_signed_boundaries_def] >>
  CASE_TAC >> gvs[listTheory.EVERY_DEF] >>
  simp[ao_opt_cmp_range_def, LET_THM,
       ao_wrap_lit_def, ao_range_valid_for_cmp_def,
       passSharedDefsTheory.is_lit_op_def, passSharedDefsTheory.lit_eq_def,
       ao_cmp_prefer_iz_zero_def, ao_cmp_prefer_iz_max_def,
       ao_cmp_prefer_iz_general_def] >>
  rpt (IF_CASES_TAC >> gvs[listTheory.EVERY_DEF])
QED

Triviality ao_peephole_inst_non_phi[local]:
  !mid dfg ra lbl idx inst.
    inst.inst_opcode <> PHI ==>
    EVERY (\i. i.inst_opcode <> PHI)
          (ao_peephole_inst mid dfg ra lbl idx inst)
Proof
  rpt strip_tac >>
  simp[ao_peephole_inst_def, LET_THM] >>
  rpt (IF_CASES_TAC >> simp[listTheory.EVERY_DEF]) >>
  gvs[] >>
  FIRST [
    irule opt_shift_non_phi >> gvs[],
    irule opt_exp_non_phi >> gvs[],
    irule opt_addsub_non_phi >> gvs[],
    irule opt_and_non_phi >> gvs[],
    irule opt_muldiv_non_phi >> gvs[],
    irule opt_or_non_phi >> gvs[],
    irule opt_eq_non_phi >> gvs[],
    irule opt_signextend_non_phi >> gvs[],
    irule opt_comparator_non_phi >> gvs[]
  ]
QED

(* ao_transform_inst: non-PHIs produce only non-PHIs *)
Theorem ao_transform_inst_non_phi:
  !mid dfg ra lbl idx targets inst.
    inst_wf inst /\ inst.inst_opcode <> PHI ==>
    EVERY (\i. i.inst_opcode <> PHI)
          (ao_transform_inst mid dfg ra lbl idx targets inst)
Proof
  rpt strip_tac >>
  simp[ao_transform_inst_def, LET_THM] >>
  `(ao_resolve_iszero_inst targets inst).inst_opcode <> PHI` by
    simp[ao_resolve_iszero_inst_opcode] >>
  rpt (IF_CASES_TAC >> simp[listTheory.EVERY_DEF]) >>
  Cases_on `ao_opt_producer dfg (ao_resolve_iszero_inst targets inst)`
  >- (* NONE: peephole path *)
     (`EVERY (\i. i.inst_opcode <> PHI)
             (ao_peephole_inst mid dfg ra lbl idx
               (ao_pre_flip_inst (ao_resolve_iszero_inst targets inst)))` by (
        irule ao_peephole_inst_non_phi >>
        simp[ao_pre_flip_opcode, ao_resolve_iszero_inst_opcode]) >>
      simp[listTheory.EVERY_MAP, ao_post_flip_opcode] >>
      fs[listTheory.EVERY_MEM] >> rpt strip_tac >>
      res_tac >> simp[ao_post_flip_opcode])
  >- (* SOME: producer path *)
     (simp[listTheory.EVERY_MAP, ao_post_flip_opcode] >>
      fs[listTheory.EVERY_MEM] >> rpt strip_tac >>
      `EVERY (\i. i.inst_opcode <> PHI) x` by (
        drule ao_opt_producer_non_phi >>
        simp[ao_resolve_iszero_inst_opcode]) >>
      fs[listTheory.EVERY_MEM] >> res_tac >> simp[ao_post_flip_opcode])
QED

(* ===== ao_transform_inst structural property (wf-free) ===== *)

(* terminators are not ASSIGN/PHI/PARAM/INVOKE *)
Triviality terminator_not_ssa[local]:
  !opc. is_terminator opc ==>
    opc <> ASSIGN /\ opc <> PHI /\ opc <> PARAM /\ opc <> INVOKE
Proof
  Cases >> simp[is_terminator_def]
QED

(* ao_opt_producer always returns NONE for terminators and INVOKE *)
Triviality ao_opt_producer_non_special[local]:
  !dfg inst.
    is_terminator inst.inst_opcode \/ inst.inst_opcode = INVOKE ==>
    ao_opt_producer dfg inst = NONE
Proof
  rpt strip_tac >> Cases_on `inst.inst_opcode` >>
  gvs[ao_opt_producer_def, is_terminator_def]
QED

(* ao_opt_producer results are non-terminator non-INVOKE *)
Triviality ao_opt_producer_every_non_special[local]:
  !dfg inst result.
    ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
    ao_opt_producer dfg inst = SOME result ==>
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) result
Proof
  rpt strip_tac >>
  qpat_x_assum `ao_opt_producer _ _ = _` mp_tac >>
  simp[ao_opt_producer_def] >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  rpt (CASE_TAC >> gvs[]) >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  rpt strip_tac >> gvs[listTheory.EVERY_DEF, is_terminator_def]
QED

(* MAP ao_post_flip_inst preserves non-terminator non-INVOKE *)
Triviality map_post_flip_every_non_special[local]:
  !insts.
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) insts ==>
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE)
          (MAP ao_post_flip_inst insts)
Proof
  Induct >> simp[] >> rpt strip_tac >> gvs[ao_post_flip_opcode]
QED

(* Comparator output is always non-terminator non-INVOKE (wf-free) *)
Triviality ao_opt_comparator_non_special[local]:
  !mid dfg ra lbl idx inst.
    ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE ==>
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE)
      (ao_opt_comparator mid dfg ra lbl idx inst)
Proof
  rpt strip_tac >>
  simp[ao_opt_comparator_def, LET_THM,
       ao_unsigned_boundaries_def, ao_signed_boundaries_def] >>
  Cases_on `inst.inst_operands` >> gvs[listTheory.EVERY_DEF] >>
  Cases_on `t` >> gvs[listTheory.EVERY_DEF] >>
  Cases_on `t'` >> gvs[listTheory.EVERY_DEF] >>
  IF_CASES_TAC >> gvs[listTheory.EVERY_DEF, is_terminator_def] >>
  CASE_TAC >> gvs[listTheory.EVERY_DEF, is_terminator_def] >>
  rpt IF_CASES_TAC >>
  gvs[listTheory.EVERY_DEF, is_terminator_def,
      ao_cmp_prefer_iz_zero_def, ao_cmp_prefer_iz_max_def,
      ao_cmp_prefer_iz_general_def] >>
  BasicProvers.EVERY_CASE_TAC >>
  gvs[listTheory.EVERY_DEF, is_terminator_def]
QED

(* Peephole output is always non-terminator non-INVOKE (wf-free) *)
Triviality ao_peephole_inst_non_special[local]:
  !mid dfg ra lbl idx inst.
    ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE ==>
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE)
      (ao_peephole_inst mid dfg ra lbl idx inst)
Proof
  rpt gen_tac >> strip_tac >>
  simp[ao_peephole_inst_def, LET_THM] >>
  rpt (IF_CASES_TAC >> simp[listTheory.EVERY_DEF]) >>
  gvs[] >>
  simp[ao_opt_shift_def, ao_opt_signextend_def, ao_opt_exp_def,
       ao_opt_addsub_def, ao_opt_and_def, ao_opt_muldiv_def,
       ao_opt_or_def, ao_opt_eq_def, LET_THM] >>
  rpt (FIRST [CASE_TAC, IF_CASES_TAC]) >>
  gvs[listTheory.EVERY_DEF, is_terminator_def] >>
  irule ao_opt_comparator_non_special >> simp[is_terminator_def]
QED

(* ao_transform_inst is structural: preserves terminator/INVOKE/other class *)
Theorem ao_transform_inst_structural:
  !mid dfg ra lbl targets.
    inst_transform_structural
      (\(v:num) inst. ao_transform_inst mid dfg ra lbl v targets inst)
Proof
  rpt gen_tac >> simp[inst_transform_structural_def] >> rpt conj_tac
  >- (* Terminators: singleton terminator *)
     (rpt gen_tac >> strip_tac >>
      Cases_on `inst.inst_outputs = []`
      >- (qexists_tac `ao_resolve_iszero_inst targets inst` >>
          simp[ao_transform_inst_def, LET_THM,
               ao_resolve_iszero_inst_outputs,
               ao_resolve_iszero_inst_opcode])
      >- (imp_res_tac terminator_not_ssa >>
          `ao_opt_producer dfg (ao_resolve_iszero_inst targets inst) = NONE` by
            (irule ao_opt_producer_non_special >>
             simp[ao_resolve_iszero_inst_opcode]) >>
          `ao_peephole_inst mid dfg ra lbl v
             (ao_pre_flip_inst (ao_resolve_iszero_inst targets inst)) =
           [ao_pre_flip_inst (ao_resolve_iszero_inst targets inst)]` by
            (irule ao_peephole_inst_terminator >>
             simp[ao_pre_flip_opcode, ao_resolve_iszero_inst_opcode]) >>
          qexists_tac
            `ao_post_flip_inst
               (ao_pre_flip_inst (ao_resolve_iszero_inst targets inst))` >>
          gvs[ao_transform_inst_def, LET_THM,
              ao_resolve_iszero_inst_opcode,
              ao_resolve_iszero_inst_outputs,
              ao_post_flip_opcode, ao_pre_flip_opcode]))
  >- (* INVOKE: singleton INVOKE *)
     (rpt gen_tac >> strip_tac >>
      qspecl_then [`mid`, `dfg`, `ra`, `lbl`, `v`, `targets`, `inst`]
        strip_assume_tac ao_transform_inst_invoke >>
      gvs[] >> qexists_tac `inst'` >> simp[])
  >- (* Non-term non-INVOKE: EVERY non-term non-INVOKE *)
     (rpt gen_tac >> strip_tac >>
      simp[ao_transform_inst_def, LET_THM,
           ao_resolve_iszero_inst_opcode,
           ao_resolve_iszero_inst_outputs] >>
      Cases_on `inst.inst_outputs = []`
      >- simp[ao_resolve_iszero_inst_opcode, is_terminator_def]
      >- (simp[] >>
          Cases_on `inst.inst_opcode = ASSIGN \/ inst.inst_opcode = PHI \/
                    inst.inst_opcode = PARAM`
          >- simp[ao_resolve_iszero_inst_opcode, is_terminator_def]
          >- (simp[ao_resolve_iszero_inst_opcode] >>
              Cases_on `ao_opt_producer dfg (ao_resolve_iszero_inst targets inst)`
              >- (simp[] >>
                  irule map_post_flip_every_non_special >>
                  irule ao_peephole_inst_non_special >>
                  simp[ao_pre_flip_opcode, ao_resolve_iszero_inst_opcode])
              >- (`~is_terminator
                      (ao_resolve_iszero_inst targets inst).inst_opcode`
                      by simp[ao_resolve_iszero_inst_opcode] >>
                  `(ao_resolve_iszero_inst targets inst).inst_opcode <> INVOKE`
                      by simp[ao_resolve_iszero_inst_opcode] >>
                  simp[] >>
                  imp_res_tac ao_opt_producer_every_non_special >>
                  irule map_post_flip_every_non_special >> simp[]))))
QED

val _ = export_theory();

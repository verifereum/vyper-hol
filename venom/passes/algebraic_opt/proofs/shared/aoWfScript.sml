(* Algebraic Optimization — Well-formedness & SSA Preservation
 *
 * Key lemmas:
 *   ao_fresh_id_gt_mid     — fresh IDs are > max_id
 *   ao_fresh_id_inj        — fresh IDs are injective in (id, slot)
 *   ao_transform_function preserves wf_function and ssa_form
 *)

Theory aoWf
Ancestors
  algebraicOptDefs aoPeepholeSim aoResolveSim
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

(* ===== Phase 1: offset preserves inst_id ===== *)

Theorem ao_handle_offset_inst_preserves_id:
  !inst. (ao_handle_offset_inst inst).inst_id = inst.inst_id
Proof
  gen_tac >> simp[ao_handle_offset_inst_def] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `h` >> simp[] >>
  Cases_on `h'` >> simp[] >>
  Cases_on `t'` >> simp[]
QED

(* ao_handle_offset_inst preserves outputs *)
Theorem ao_handle_offset_inst_outputs:
  !inst. (ao_handle_offset_inst inst).inst_outputs = inst.inst_outputs
Proof
  gen_tac >> simp[ao_handle_offset_inst_def] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `h` >> simp[] >>
  Cases_on `h'` >> simp[] >>
  Cases_on `t'` >> simp[]
QED

(* Terminators have opcode <> ADD *)
Triviality term_not_add[local]:
  !opc. is_terminator opc ==> opc <> ADD
Proof
  Cases >> simp[is_terminator_def]
QED

(* OFFSET is not a terminator *)
Triviality offset_not_term[local]:
  ~is_terminator OFFSET
Proof
  simp[is_terminator_def]
QED

(* OFFSET is not PHI *)
Triviality offset_not_phi[local]:
  OFFSET <> PHI
Proof
  simp[]
QED

(* ao_handle_offset_inst: terminators pass through unchanged *)
Theorem ao_handle_offset_inst_term:
  !inst. is_terminator inst.inst_opcode ==> ao_handle_offset_inst inst = inst
Proof
  rpt strip_tac >>
  `inst.inst_opcode <> ADD` by metis_tac[term_not_add] >>
  simp[ao_handle_offset_inst_def]
QED

(* ao_handle_offset_inst: non-terminators stay non-terminators *)
Theorem ao_handle_offset_inst_not_term:
  !inst. ~is_terminator inst.inst_opcode ==>
    ~is_terminator (ao_handle_offset_inst inst).inst_opcode
Proof
  gen_tac >> simp[ao_handle_offset_inst_def] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `h` >> simp[] >>
  Cases_on `h'` >> simp[] >>
  Cases_on `t'` >> simp[is_terminator_def]
QED

(* ao_handle_offset_inst: PHI preserved *)
Theorem ao_handle_offset_inst_phi:
  !inst. inst.inst_opcode = PHI ==>
    (ao_handle_offset_inst inst).inst_opcode = PHI
Proof
  simp[ao_handle_offset_inst_def]
QED

(* ao_handle_offset_inst: non-PHI stays non-PHI *)
Theorem ao_handle_offset_inst_not_phi:
  !inst. inst.inst_opcode <> PHI ==>
    (ao_handle_offset_inst inst).inst_opcode <> PHI
Proof
  gen_tac >> simp[ao_handle_offset_inst_def] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `h` >> simp[] >>
  Cases_on `h'` >> simp[] >>
  Cases_on `t'` >> simp[]
QED

(* ao_handle_offset_inst preserves inst_wf *)
Theorem ao_handle_offset_inst_wf:
  !inst. inst_wf inst ==> inst_wf (ao_handle_offset_inst inst)
Proof
  gen_tac >> strip_tac >>
  simp[ao_handle_offset_inst_def] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `h` >> simp[] >>
  Cases_on `h'` >> simp[] >>
  Cases_on `t'` >> simp[] >>
  fs[inst_wf_def]
QED

(* ===== Phase 1 preserves wf_function ===== *)

Theorem ao_phase1_preserves_wf:
  !fn. wf_function fn ==>
    wf_function (function_map_transform
      (block_map_transform ao_handle_offset_inst) fn)
Proof
  rpt strip_tac >>
  irule map_transform_preserves_wf >> simp[] >>
  metis_tac[ao_handle_offset_inst_preserves_id,
            ao_handle_offset_inst_term,
            ao_handle_offset_inst_not_term,
            ao_handle_offset_inst_phi,
            ao_handle_offset_inst_not_phi]
QED

(* ===== Phase 1 preserves ssa_form ===== *)

Theorem ao_phase1_preserves_ssa:
  !fn. wf_function fn /\ ssa_form fn ==>
    ssa_form (function_map_transform
      (block_map_transform ao_handle_offset_inst) fn)
Proof
  rpt strip_tac >>
  irule map_transform_preserves_ssa >>
  simp[ao_handle_offset_inst_preserves_id, ao_handle_offset_inst_outputs]
QED

(* ===== FLAT MAP list helpers ===== *)

(* LAST of FLAT MAP when last sub-list is a singleton *)
Triviality last_flat_map[local]:
  !(l:'a list) f.
    l <> [] /\ (!x. MEM x l ==> f x <> []) ==>
    LAST (FLAT (MAP f l)) = LAST (f (LAST l))
Proof
  Induct >- simp[] >>
  rpt gen_tac >> simp[] >> strip_tac >>
  Cases_on `l` >- simp[] >>
  `FLAT (MAP f (h'::t)) <> []` by (
    simp[listTheory.FLAT_EQ_NIL, listTheory.EVERY_MAP,
         listTheory.EVERY_MEM]) >>
  simp[rich_listTheory.LAST_APPEND_NOT_NIL]
QED

(* FLAT MAP non-empty *)
Triviality flat_map_ne[local]:
  !(l:'a list) f.
    l <> [] /\ (!x. MEM x l ==> f x <> []) ==>
    FLAT (MAP f l) <> []
Proof
  Cases >> simp[]
QED

(* FRONT of FLAT MAP = FLAT (MAP f (FRONT l)) when f (LAST l) singleton *)
Triviality front_flat_map_singleton[local]:
  !(l:'a list) f.
    l <> [] /\ (!x. MEM x l ==> f x <> []) /\
    (?v. f (LAST l) = [v]) ==>
    FRONT (FLAT (MAP f l)) = FLAT (MAP f (FRONT l))
Proof
  Induct >- simp[] >>
  rpt gen_tac >> simp[] >> strip_tac >>
  Cases_on `l` >- (gvs[] >> Cases_on `f h` >> fs[]) >>
  `FLAT (MAP f (h'::t)) <> []` by (
    simp[listTheory.FLAT_EQ_NIL, listTheory.EVERY_MAP,
         listTheory.EVERY_MEM]) >>
  simp[rich_listTheory.FRONT_APPEND_NOT_NIL] >>
  first_x_assum (qspec_then `f` mp_tac) >>
  impl_tac >- (simp[] >> qexists_tac `v` >> gvs[]) >>
  simp[]
QED

(* bb_well_formed implies all non-LAST elements are non-terminators *)
Triviality wf_front_non_term[local]:
  !bb. bb_well_formed bb ==>
    EVERY (\r. ~is_terminator r.inst_opcode) (FRONT bb.bb_instructions)
Proof
  rw[bb_well_formed_def, listTheory.EVERY_EL,
     rich_listTheory.LENGTH_FRONT, rich_listTheory.EL_FRONT,
     listTheory.NULL_EQ] >>
  CCONTR_TAC >> fs[] >>
  qpat_x_assum `!i. i < LENGTH _ /\ is_terminator _ ==> _`
    (qspec_then `n` mp_tac) >>
  `n < LENGTH bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> fs[]) >>
  simp[]
QED

(* FLAT MAP preserves PHI prefix ordering.
   Induction: PHI heads map to singletons, non-PHI heads start a non-PHI tail. *)
Triviality flat_map_phi_prefix[local]:
  !l f.
    (!i j. i < j /\ j < LENGTH l /\ (EL j l).inst_opcode = PHI ==>
           (EL i l).inst_opcode = PHI) /\
    (!inst. MEM inst l /\ inst.inst_opcode = PHI ==> f inst = [inst]) /\
    (!inst r. MEM inst l /\ inst.inst_opcode <> PHI /\ MEM r (f inst) ==>
              r.inst_opcode <> PHI) /\
    (!inst. MEM inst l ==> f inst <> [])
    ==>
    (!i j. i < j /\ j < LENGTH (FLAT (MAP f l)) /\
           (EL j (FLAT (MAP f l))).inst_opcode = PHI ==>
           (EL i (FLAT (MAP f l))).inst_opcode = PHI)
Proof
  Induct >- simp[] >>
  rpt gen_tac >> strip_tac >> rename1 `h :: t` >>
  `f h <> []` by simp[] >>
  Cases_on `h.inst_opcode = PHI`
  >- (
    `f h = [h]` by simp[] >>
    fs[] >> rpt strip_tac >>
    Cases_on `i` >- simp[] >>
    rename1 `SUC n < j` >>
    Cases_on `j` >- fs[] >>
    rename1 `SUC n < SUC m` >>
    fs[] >>
    first_x_assum (qspec_then `f` mp_tac) >>
    impl_tac
    >- (rpt conj_tac
        >- (rpt strip_tac >>
            first_x_assum (qspecl_then [`SUC i`, `SUC j`] mp_tac) >> simp[])
        >> metis_tac[listTheory.MEM])
    >> disch_then (qspecl_then [`n`, `m`] mp_tac) >> simp[])
  >- (
    (* h is not PHI — no element of t is PHI either *)
    `EVERY (\inst. inst.inst_opcode <> PHI) t` by (
      simp[listTheory.EVERY_EL] >> rpt strip_tac >>
      spose_not_then strip_assume_tac >> gvs[] >>
      first_x_assum (qspecl_then [`0`, `SUC n`] mp_tac) >> simp[]) >>
    (* So every element in the flat result is non-PHI — contradiction *)
    rpt strip_tac >>
    `EVERY (\r. r.inst_opcode <> PHI) (f h ++ FLAT (MAP f t))` by (
      simp[listTheory.EVERY_APPEND, listTheory.EVERY_FLAT,
           listTheory.EVERY_MAP, listTheory.EVERY_MEM] >>
      conj_tac >> rpt strip_tac
      >- (`MEM h (h::t)` by simp[] >> metis_tac[])
      >- (`MEM x (h::t)` by simp[] >>
          `x.inst_opcode <> PHI` by fs[listTheory.EVERY_MEM] >>
          metis_tac[])) >>
    `FLAT (MAP f (h::t)) = f h ++ FLAT (MAP f t)` by simp[] >>
    fs[] >>
    `MEM ((f h ++ FLAT (MAP f t))❲j❳) (f h ++ FLAT (MAP f t))` by (
      irule listTheory.EL_MEM >> simp[]) >>
    fs[listTheory.MEM_APPEND, listTheory.EVERY_MEM] >>
    res_tac >> fs[])
QED

(* ===== FLAT MAP preserves bb_well_formed ===== *)

Theorem flat_map_preserves_bb_wf:
  !f bb.
    bb_well_formed bb /\
    (!inst. MEM inst bb.bb_instructions ==> f inst <> []) /\
    (!inst. MEM inst bb.bb_instructions /\
            is_terminator inst.inst_opcode ==> f inst = [inst]) /\
    (!inst r. MEM inst bb.bb_instructions /\
              ~is_terminator inst.inst_opcode /\ MEM r (f inst) ==>
              ~is_terminator r.inst_opcode) /\
    (!inst. MEM inst bb.bb_instructions /\
            inst.inst_opcode = PHI ==> f inst = [inst]) /\
    (!inst r. MEM inst bb.bb_instructions /\
              inst.inst_opcode <> PHI /\ MEM r (f inst) ==>
              r.inst_opcode <> PHI)
    ==>
    bb_well_formed (bb with bb_instructions := FLAT (MAP f bb.bb_instructions))
Proof
  rpt strip_tac >>
  fs[bb_well_formed_def] >>
  rpt conj_tac
  (* non-empty *)
  >- (irule flat_map_ne >> simp[])
  (* LAST is terminator *)
  >- (`LAST (FLAT (MAP f bb.bb_instructions)) =
       LAST (f (LAST bb.bb_instructions))`
        by (irule last_flat_map >> simp[]) >>
      `f (LAST bb.bb_instructions) = [LAST bb.bb_instructions]`
        by (qpat_x_assum `!inst. MEM inst _ /\ is_terminator _ ==> _`
              (qspec_then `LAST bb.bb_instructions` mp_tac) >>
            simp[rich_listTheory.MEM_LAST_NOT_NIL]) >>
      simp[listTheory.LAST_DEF])
  (* terminator only at end: use EVERY on FRONT *)
  >- (rpt strip_tac >>
      spose_not_then strip_assume_tac >>
      `FLAT (MAP f bb.bb_instructions) <> []` by (irule flat_map_ne >> simp[]) >>
      `i < PRE (LENGTH (FLAT (MAP f bb.bb_instructions)))` by simp[] >>
      (* FRONT of original has no terminators *)
      `EVERY (\r. ~is_terminator r.inst_opcode) (FRONT bb.bb_instructions)` by (
        rw[listTheory.EVERY_EL, rich_listTheory.LENGTH_FRONT,
           rich_listTheory.EL_FRONT, listTheory.NULL_EQ] >>
        CCONTR_TAC >> fs[] >>
        qpat_x_assum `!i. i < LENGTH _ /\ is_terminator _ ==> _`
          (qspec_then `n` mp_tac) >>
        `n < LENGTH bb.bb_instructions` by
          (Cases_on `bb.bb_instructions` >> fs[]) >>
        simp[]) >>
      (* FRONT(FLAT(MAP f insts)) = FLAT(MAP f (FRONT insts)) *)
      `FRONT (FLAT (MAP f bb.bb_instructions)) =
       FLAT (MAP f (FRONT bb.bb_instructions))` by (
        irule front_flat_map_singleton >> simp[] >>
        qexists_tac `LAST bb.bb_instructions` >>
        qpat_x_assum `!inst. MEM inst _ /\ is_terminator _ ==> _`
          (qspec_then `LAST bb.bb_instructions` mp_tac) >>
        simp[rich_listTheory.MEM_LAST_NOT_NIL]) >>
      (* EVERY non-term on FLAT(MAP f (FRONT insts)) *)
      `EVERY (\r. ~is_terminator r.inst_opcode)
             (FLAT (MAP f (FRONT bb.bb_instructions)))` by (
        simp[listTheory.EVERY_FLAT, listTheory.EVERY_MAP,
             listTheory.EVERY_MEM] >>
        rpt strip_tac >> rename1 `MEM finst (FRONT bb.bb_instructions)` >>
        `MEM finst bb.bb_instructions` by
          (irule rich_listTheory.MEM_FRONT_NOT_NIL >> simp[]) >>
        `~is_terminator finst.inst_opcode` by
          fs[listTheory.EVERY_MEM] >>
        res_tac) >>
      (* EL i is in FRONT — derive contradiction *)
      `EL i (FLAT (MAP f bb.bb_instructions)) =
       EL i (FRONT (FLAT (MAP f bb.bb_instructions)))` by (
        irule (GSYM rich_listTheory.EL_FRONT) >>
        fs[listTheory.NULL_EQ, rich_listTheory.LENGTH_FRONT]) >>
      `~is_terminator (EL i (FRONT (FLAT (MAP f bb.bb_instructions)))).inst_opcode`
        by (qpat_x_assum `EVERY _ (FLAT (MAP f (FRONT _)))` mp_tac >>
            qpat_x_assum `FRONT _ = _` (fn th => REWRITE_TAC [GSYM th]) >>
            simp[listTheory.EVERY_EL, rich_listTheory.LENGTH_FRONT,
                 listTheory.NULL_EQ]) >>
      gvs[])
  (* PHI prefix: use flat_map_phi_prefix helper *)
  >- (rpt strip_tac >>
      irule flat_map_phi_prefix >> simp[] >>
      metis_tac[])
QED

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

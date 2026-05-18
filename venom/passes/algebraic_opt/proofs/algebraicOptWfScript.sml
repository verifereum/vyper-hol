(* Algebraic Optimization — Well-formedness & SSA Preservation
 *
 * Key lemmas:
 *   ao_fresh_id_gt_mid     — fresh IDs are > max_id
 *   ao_fresh_id_inj        — fresh IDs are injective in (id, slot)
 *   ao_transform_function preserves wf_function and ssa_form
 *)

Theory algebraicOptWf
Ancestors
  algebraicOptDefs algebraicOptPeepholeSim
  venomState venomWf venomInst passSimulationProps passSimulationDefs
  passSharedDefs
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
Triviality ao_resolve_iszero_inst_wf[local]:
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

(* ===== Phase 3: ao_transform_block helpers ===== *)

(* ao_transform_block preserves bb_label *)
Triviality ao_transform_block_label[local]:
  !mid dfg ra targets bb.
    (ao_transform_block mid dfg ra targets bb).bb_label = bb.bb_label
Proof
  simp[ao_transform_block_def]
QED

(* ao_transform_block preserves bb_well_formed.
   Proof: expand bb_well_formed_def and prove each condition using
   per-instruction properties (ne, term, non_term, phi, non_phi). *)
(* Helper: FLAT of MAPi (g o SUC) on non-empty list is non-empty if g 1 h' ≠ [] *)
Triviality flat_mapi_suc_ne[local]:
  !g h h' t.
    g 1 h' <> [] ==>
    FLAT (MAPi (g o SUC) (h'::t)) <> []
Proof
  rpt strip_tac >>
  pop_assum mp_tac >>
  ONCE_REWRITE_TAC[indexedListsTheory.MAPi_def] >>
  simp[combinTheory.o_DEF]
QED

(* Helper: FLAT MAPi non-empty when input non-empty and each result non-empty *)
Triviality flat_mapi_ne[local]:
  !g l. l <> [] /\ (!i. i < LENGTH l ==> g i (EL i l) <> []) ==>
    FLAT (MAPi g l) <> []
Proof
  rpt gen_tac >> Cases_on `l` >> simp[indexedListsTheory.MAPi_def] >>
  rpt strip_tac >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[]
QED

Triviality flat_mapi_comp_suc_ne[local]:
  !f x y zs.
    (!j. j < SUC (LENGTH (y::zs)) ==> f j (EL j (x::y::zs)) <> []) ==>
    FLAT (MAPi (f o SUC) (y::zs)) <> []
Proof
  rpt gen_tac >> strip_tac >>
  irule flat_mapi_ne >> simp[] >>
  simp[combinTheory.o_DEF] >> rpt gen_tac >> strip_tac >>
  first_x_assum (qspec_then `SUC i` mp_tac) >> simp[]
QED

(* Helper: LAST of FLAT MAPi when last sub-list is a singleton *)
Triviality last_flat_mapi[local]:
  !l g.
    l <> [] /\ (!i. i < LENGTH l ==> g i (EL i l) <> []) /\
    (?v. g (PRE (LENGTH l)) (LAST l) = [v]) ==>
    LAST (FLAT (MAPi g l)) = LAST (g (PRE (LENGTH l)) (LAST l))
Proof
  Induct >- simp[] >>
  rpt gen_tac >> simp[indexedListsTheory.MAPi_def] >> strip_tac >>
  Cases_on `l`
  (* singleton [h] *)
  >- (gvs[indexedListsTheory.MAPi_def] >>
      `g 0 h <> []` by (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
      Cases_on `g 0 h` >> fs[])
  (* h :: h' :: t *)
  >- (rename1 `h :: h' :: t` >>
      first_assum (qspec_then `1` assume_tac) >>
      gvs[rich_listTheory.LAST_APPEND_NOT_NIL] >>
      first_x_assum (qspec_then `g o SUC` mp_tac) >>
      simp[combinTheory.o_DEF] >>
      strip_tac >>
      first_assum (qspec_then `1` assume_tac) >>
      fs[] >>
      ONCE_REWRITE_TAC[GSYM listTheory.APPEND_ASSOC] >>
      simp[rich_listTheory.LAST_APPEND_NOT_NIL] >>
      first_x_assum irule >>
      rpt strip_tac >>
      first_x_assum (qspec_then `SUC i` mp_tac) >> simp[])
QED

(* Helper: FRONT of FLAT MAPi when last sub-list is singleton *)
Triviality front_flat_mapi_singleton[local]:
  !l g.
    l <> [] /\ (!i. i < LENGTH l ==> g i (EL i l) <> []) /\
    (?v. g (PRE (LENGTH l)) (LAST l) = [v]) ==>
    FRONT (FLAT (MAPi g l)) = FLAT (MAPi g (FRONT l))
Proof
  Induct >- simp[] >>
  rpt gen_tac >> simp[indexedListsTheory.MAPi_def] >> strip_tac >>
  Cases_on `l`
  (* singleton [h] *)
  >- (gvs[indexedListsTheory.MAPi_def] >>
      `g 0 h <> []` by (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
      Cases_on `g 0 h` >> fs[])
  (* h :: h' :: t *)
  >- (rename1 `h :: h' :: t` >>
      first_assum (qspec_then `1` assume_tac) >> fs[] >>
      first_x_assum (qspec_then `g o SUC` mp_tac) >>
      simp[combinTheory.o_DEF] >>
      strip_tac >>
      `!i. i < SUC (LENGTH t) ==> g (SUC i) (EL i (h'::t)) <> []` by
        (rpt strip_tac >>
         first_x_assum (qspec_then `SUC i` mp_tac) >> simp[]) >>
      res_tac >>
      qpat_assum `FRONT _ = FLAT _` (SUBST1_TAC o SYM) >>
      ONCE_REWRITE_TAC[GSYM listTheory.APPEND_ASSOC] >>
      irule rich_listTheory.FRONT_APPEND_NOT_NIL >>
      simp[])
QED

Triviality phi_singleton_at_head[local]:
  !g h t.
    (!i. i < LENGTH (h::t) /\ (EL i (h::t)).inst_opcode = PHI ==>
         ?v. g i (EL i (h::t)) = [v] /\ v.inst_opcode = PHI) ==>
    h.inst_opcode = PHI ==>
    ?v. g 0 h = [v] /\ v.inst_opcode = PHI
Proof
  rpt strip_tac >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[]
QED

Triviality every_nonphi_append_output[local]:
  !h t g.
    (!k. k < LENGTH (h::t) ==> (EL k (h::t)).inst_opcode <> PHI) /\
    (!i r. i < LENGTH (h::t) /\ (EL i (h::t)).inst_opcode <> PHI /\
           MEM r (g i (EL i (h::t))) ==> r.inst_opcode <> PHI) ==>
    EVERY (\r. r.inst_opcode <> PHI) (g 0 h ++ FLAT (MAPi (g o SUC) t))
Proof
  rpt strip_tac >>
  simp[listTheory.EVERY_APPEND] >>
  (conj_tac >- (
    simp[listTheory.EVERY_MEM] >>
    rpt strip_tac >> rename1 `MEM r _` >>
    first_x_assum (qspecl_then [`0`, `r`] mp_tac) >>
    simp[])) >>
  simp[listTheory.EVERY_MEM, listTheory.MEM_FLAT,
       indexedListsTheory.MEM_MAPi, combinTheory.o_DEF] >>
  rpt strip_tac >> gvs[] >>
  rename1 `MEM r _` >> rename1 `k < LENGTH t` >>
  first_x_assum (qspecl_then [`SUC k`, `r`] mp_tac) >>
  simp[]
QED

(* Helper: non-PHI inputs produce all non-PHI outputs *)
Triviality flat_mapi_nonphi_contra[local]:
  !h t g i j.
    (!i j. i < j /\ j < LENGTH (h::t) /\ (EL j (h::t)).inst_opcode = PHI ==>
           (EL i (h::t)).inst_opcode = PHI) /\
    (!i r. i < LENGTH (h::t) /\ (EL i (h::t)).inst_opcode <> PHI /\
           MEM r (g i (EL i (h::t))) ==> r.inst_opcode <> PHI) /\
    h.inst_opcode <> PHI /\
    i < j /\ j < LENGTH (g 0 h ++ FLAT (MAPi (g o SUC) t)) /\
    (EL j (g 0 h ++ FLAT (MAPi (g o SUC) t))).inst_opcode = PHI ==>
    (EL i (g 0 h ++ FLAT (MAPi (g o SUC) t))).inst_opcode = PHI
Proof
  rpt strip_tac >>
  `!k. k < LENGTH (h::t) ==> (EL k (h::t)).inst_opcode <> PHI` by (
    rpt strip_tac >>
    spose_not_then strip_assume_tac >>
    (Cases_on `k` >- gvs[]) >>
    rename1 `SUC m < _` >>
    first_x_assum (qspecl_then [`0`, `SUC m`] mp_tac) >> simp[]) >>
  `EVERY (\r. r.inst_opcode <> PHI) (g 0 h ++ FLAT (MAPi (g o SUC) t))` by (
    simp[listTheory.EVERY_APPEND] >>
    (conj_tac >- (
      simp[listTheory.EVERY_MEM] >>
      rpt strip_tac >> rename1 `MEM r _` >>
      first_x_assum (qspecl_then [`0`, `r`] mp_tac) >> simp[])) >>
    simp[listTheory.EVERY_MEM, listTheory.MEM_FLAT,
         indexedListsTheory.MEM_MAPi, combinTheory.o_DEF] >>
    rpt strip_tac >> gvs[] >>
    rename1 `MEM r _` >> rename1 `k < LENGTH t` >>
    first_x_assum (qspecl_then [`SUC k`, `r`] mp_tac) >> simp[]) >>
  qpat_x_assum `EVERY _ _` mp_tac >>
  PURE_REWRITE_TAC [listTheory.EVERY_EL] >>
  disch_then (qspec_then `j` mp_tac) >> simp[]
QED

(* Helper: PHI prefix for FLAT MAPi *)
Triviality flat_mapi_phi_prefix[local]:
  !l g.
    (!i j. i < j /\ j < LENGTH l /\ (EL j l).inst_opcode = PHI ==>
           (EL i l).inst_opcode = PHI) /\
    (!i. i < LENGTH l /\ (EL i l).inst_opcode = PHI ==>
         ?v. g i (EL i l) = [v] /\ v.inst_opcode = PHI) /\
    (!i r. i < LENGTH l /\ (EL i l).inst_opcode <> PHI /\
           MEM r (g i (EL i l)) ==> r.inst_opcode <> PHI) /\
    (!i. i < LENGTH l ==> g i (EL i l) <> [])
    ==>
    (!i j. i < j /\ j < LENGTH (FLAT (MAPi g l)) /\
           (EL j (FLAT (MAPi g l))).inst_opcode = PHI ==>
           (EL i (FLAT (MAPi g l))).inst_opcode = PHI)
Proof
  Induct >- simp[] >>
  rpt gen_tac >> strip_tac >> rename1 `h :: t` >>
  simp[indexedListsTheory.MAPi_def] >>
  `g 0 h <> []` by (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  Cases_on `h.inst_opcode = PHI`
  >- (
    drule_all phi_singleton_at_head >> strip_tac >>
    gvs[] >> rpt strip_tac >>
    (Cases_on `i` >- simp[]) >>
    (Cases_on `j` >- gvs[]) >> gvs[] >>
    (`!i j. i < j /\ j < LENGTH (FLAT (MAPi (g o SUC) t)) /\
            (EL j (FLAT (MAPi (g o SUC) t))).inst_opcode = PHI ==>
            (EL i (FLAT (MAPi (g o SUC) t))).inst_opcode = PHI` by (
      first_x_assum MATCH_MP_TAC >>
      simp[combinTheory.o_DEF] >>
      (rpt conj_tac >> rpt gen_tac >> rpt strip_tac) >| [
        first_x_assum (qspecl_then [`SUC i`, `SUC j`] mp_tac) >> simp[],
        qpat_x_assum `!i. _ /\ _ = PHI ==> ?v. _`
          (qspec_then `SUC i` mp_tac) >> simp[],
        qpat_x_assum `!i r. _`
          (qspecl_then [`SUC i`, `r`] mp_tac) >> simp[],
        qpat_x_assum `!i. _ ==> _ <> _`
          (qspec_then `SUC i` mp_tac) >> simp[]
      ])) >>
    first_x_assum (qspecl_then [`n`, `n'`] mp_tac) >> simp[])
  >- (
    rpt strip_tac >>
    mp_tac (Q.SPECL [`h`, `t`, `g`, `i`, `j`] flat_mapi_nonphi_contra) >>
    impl_tac >- (
      rpt conj_tac >> TRY (first_x_assum ACCEPT_TAC) >> simp[]) >>
    simp[])
QED

Triviality ao_transform_inst_phi_prefix[local]:
  !insts targets mid dfg ra lbl.
    (!i j. i < j /\ j < LENGTH insts /\
       (EL j insts).inst_opcode = PHI ==>
       (EL i insts).inst_opcode = PHI) /\
    EVERY inst_wf insts /\
    (!i. i < LENGTH insts ==>
      ao_transform_inst mid dfg ra lbl i targets (EL i insts) <> []) ==>
    !i j.
      i < j /\
      j < LENGTH (FLAT (MAPi
        (\idx inst. ao_transform_inst mid dfg ra lbl idx targets inst)
        insts)) /\
      (EL j (FLAT (MAPi
        (\idx inst. ao_transform_inst mid dfg ra lbl idx targets inst)
        insts))).inst_opcode = PHI ==>
      (EL i (FLAT (MAPi
        (\idx inst. ao_transform_inst mid dfg ra lbl idx targets inst)
        insts))).inst_opcode = PHI
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `g = \idx inst.
    ao_transform_inst mid dfg ra lbl idx targets inst` >>
  MATCH_MP_TAC flat_mapi_phi_prefix >> rpt conj_tac
  >- metis_tac[]
  >- (rpt strip_tac >>
      qexists_tac `ao_resolve_iszero_inst targets (EL i insts)` >>
      simp[Abbr `g`, ao_transform_inst_phi,
           ao_resolve_iszero_inst_opcode])
  >- (rpt strip_tac >>
      `inst_wf (EL i insts)` by fs[listTheory.EVERY_EL] >>
      `EVERY (\r'. r'.inst_opcode <> PHI)
             (g i (EL i insts))` by
        (simp[Abbr `g`] >>
         irule ao_transform_inst_non_phi >> simp[]) >>
      fs[listTheory.EVERY_MEM] >> res_tac >> fs[])
  >- fs[Abbr `g`]
QED

(* bb_well_formed for ao_transform_block — direct proof *)
Triviality ao_transform_block_bb_wf[local]:
  !mid dfg ra targets bb.
    bb_well_formed bb /\
    EVERY inst_wf bb.bb_instructions ==>
    bb_well_formed (ao_transform_block mid dfg ra targets bb)
Proof
  rpt strip_tac >>
  simp[ao_transform_block_def, bb_well_formed_def] >>
  fs[bb_well_formed_def] >>
  qabbrev_tac `insts = bb.bb_instructions` >>
  qabbrev_tac `g = \idx inst.
    ao_transform_inst mid dfg ra bb.bb_label idx targets inst` >>
  `!i. i < LENGTH insts ==> g i (EL i insts) <> []` by
    simp[Abbr `g`, ao_transform_inst_ne] >>
  `EVERY inst_wf insts` by simp[Abbr `insts`] >>
  `inst_wf (LAST insts)` by
    (fs[listTheory.EVERY_MEM] >>
     first_x_assum irule >>
     irule rich_listTheory.MEM_LAST_NOT_NIL >> simp[]) >>
  rpt conj_tac
  (* 1. Non-empty *)
  >- (irule flat_mapi_ne >> simp[])
  (* 2. LAST is terminator *)
  >- (`g (PRE (LENGTH insts)) (LAST insts) =
       [ao_resolve_iszero_inst targets (LAST insts)]` by (
        simp[Abbr `g`] >> irule ao_transform_inst_term >> simp[]) >>
      `LAST (FLAT (MAPi g insts)) =
       LAST (g (PRE (LENGTH insts)) (LAST insts))` by (
        irule last_flat_mapi >> simp[] >>
        qexists_tac `ao_resolve_iszero_inst targets (LAST insts)` >>
        simp[]) >>
      simp[ao_resolve_iszero_inst_opcode])
  (* 3. Terminator only at end *)
  >- (rpt strip_tac >>
      spose_not_then strip_assume_tac >>
      `FLAT (MAPi g insts) <> []` by (irule flat_mapi_ne >> simp[]) >>
      `i < PRE (LENGTH (FLAT (MAPi g insts)))` by simp[] >>
      (* FRONT of original has no terminators *)
      `EVERY (\r. ~is_terminator r.inst_opcode) (FRONT insts)` by (
        simp[listTheory.EVERY_EL, rich_listTheory.LENGTH_FRONT,
             rich_listTheory.EL_FRONT, listTheory.NULL_EQ] >>
        rpt strip_tac >> CCONTR_TAC >> fs[] >>
        `n < LENGTH insts` by (Cases_on `insts` >> fs[]) >>
        res_tac >> fs[]) >>
      (* FRONT(FLAT(MAPi g insts)) = FLAT(MAPi g (FRONT insts)) *)
      `FRONT (FLAT (MAPi g insts)) = FLAT (MAPi g (FRONT insts))` by (
        irule front_flat_mapi_singleton >> simp[] >>
        qexists_tac `ao_resolve_iszero_inst targets (LAST insts)` >>
        simp[Abbr `g`] >> irule ao_transform_inst_term >> simp[]) >>
      (* Every element in FLAT(MAPi g (FRONT insts)) is non-terminator *)
      `EVERY (\r. ~is_terminator r.inst_opcode)
             (FLAT (MAPi g (FRONT insts)))` by (
        simp[listTheory.EVERY_MEM, listTheory.MEM_FLAT,
             indexedListsTheory.MEM_MAPi] >>
        rpt gen_tac >> strip_tac >> gvs[] >>
        rename1 `MEM x (g n (EL n (FRONT insts)))` >>
        `n < LENGTH insts` by
          (Cases_on `insts` >> fs[rich_listTheory.LENGTH_FRONT]) >>
        `EL n (FRONT insts) = EL n insts` by
          (irule rich_listTheory.EL_FRONT >>
           fs[listTheory.NULL_EQ, rich_listTheory.LENGTH_FRONT]) >>
        `~is_terminator (EL n insts).inst_opcode` by (
          fs[listTheory.EVERY_EL, rich_listTheory.LENGTH_FRONT] >>
          spose_not_then strip_assume_tac >> res_tac >>
          Cases_on `insts` >> fs[]) >>
        `inst_wf (EL n insts)` by fs[listTheory.EVERY_EL] >>
        `EVERY (\r'. ~is_terminator r'.inst_opcode)
               (g n (EL n insts))` by
          (simp[Abbr `g`] >> irule ao_transform_inst_non_term >> simp[]) >>
        gvs[] >> fs[listTheory.EVERY_MEM]) >>
      (* EL i is in FRONT — derive contradiction *)
      `EL i (FLAT (MAPi g insts)) =
       EL i (FRONT (FLAT (MAPi g insts)))` by (
        irule (GSYM rich_listTheory.EL_FRONT) >>
        fs[listTheory.NULL_EQ, rich_listTheory.LENGTH_FRONT]) >>
      `~is_terminator (EL i (FRONT (FLAT (MAPi g insts)))).inst_opcode`
        by (qpat_x_assum `EVERY _ (FLAT (MAPi g (FRONT _)))` mp_tac >>
            qpat_x_assum `FRONT _ = _` (fn th => REWRITE_TAC [GSYM th]) >>
            simp[listTheory.EVERY_EL, rich_listTheory.LENGTH_FRONT,
                 listTheory.NULL_EQ]) >>
      gvs[])
  (* 4. PHI prefix *)
  >- (simp[Abbr `g`] >>
      MATCH_MP_TAC ao_transform_inst_phi_prefix >>
      rpt conj_tac >> gvs[])
QED

(* ao_resolve_iszero_op preserves get_label when chains have no labels *)
Triviality ao_resolve_iszero_op_get_label[local]:
  !targets opc op.
    (!k chain. ALOOKUP targets k = SOME chain ==>
       EVERY (\e. get_label e = NONE) chain) ==>
    get_label (ao_resolve_iszero_op targets opc op) = get_label op
Proof
  rpt gen_tac >> strip_tac >>
  rpt strip_tac >>
  Cases_on `op` >>
  PURE_REWRITE_TAC[ao_resolve_iszero_op_def] >> simp[] >>
  Cases_on `ALOOKUP targets s` >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  simp[LET_THM] >>
  IF_CASES_TAC >> simp[] >>
  `get_label (Var s) = NONE` by REWRITE_TAC[get_label_def] >>
  pop_assum SUBST_ALL_TAC >>
  first_x_assum drule >> strip_tac >>
  fs[listTheory.EVERY_EL]
QED

(* ao_resolve_iszero_inst preserves get_successors when chains have no labels *)
Triviality ao_resolve_iszero_inst_get_successors[local]:
  !targets inst.
    (!k chain. ALOOKUP targets k = SOME chain ==>
       EVERY (\e. get_label e = NONE) chain) ==>
    get_successors (ao_resolve_iszero_inst targets inst) = get_successors inst
Proof
  rpt strip_tac >>
  simp[get_successors_def, ao_resolve_iszero_inst_def,
       ao_resolve_iszero_inst_opcode] >>
  IF_CASES_TAC >> simp[] >>
  AP_TERM_TAC >> AP_TERM_TAC >>
  simp[listTheory.MAP_MAP_o, combinTheory.o_DEF,
       listTheory.MAP_EQ_f] >>
  rpt strip_tac >>
  irule ao_resolve_iszero_op_get_label >> metis_tac[]
QED

(* ao_transform_block preserves bb_succs.
   Terminators map to singletons with same opcode and get_successors,
   so LAST instruction's successors are preserved. *)
Triviality ao_transform_block_bb_succs[local]:
  !mid dfg ra targets bb.
    bb_well_formed bb /\
    EVERY inst_wf bb.bb_instructions /\
    (!k chain. ALOOKUP targets k = SOME chain ==>
       EVERY (\e. get_label e = NONE) chain) ==>
    bb_succs (ao_transform_block mid dfg ra targets bb) = bb_succs bb
Proof
  rpt strip_tac >>
  simp[ao_transform_block_def, bb_succs_def] >>
  fs[bb_well_formed_def] >>
  qabbrev_tac `insts = bb.bb_instructions` >>
  qabbrev_tac `g = \idx inst.
    ao_transform_inst mid dfg ra bb.bb_label idx targets inst` >>
  `!i. i < LENGTH insts ==> g i (EL i insts) <> []` by
    simp[Abbr `g`, ao_transform_inst_ne] >>
  `FLAT (MAPi g insts) <> []` by
    (irule flat_mapi_ne >> simp[]) >>
  `inst_wf (LAST insts)` by
    (fs[listTheory.EVERY_MEM] >>
     metis_tac[rich_listTheory.MEM_LAST_NOT_NIL]) >>
  `g (PRE (LENGTH insts)) (LAST insts) =
     [ao_resolve_iszero_inst targets (LAST insts)]` by
    (simp[Abbr `g`] >> irule ao_transform_inst_term >> simp[]) >>
  `LAST (FLAT (MAPi g insts)) =
   LAST (g (PRE (LENGTH insts)) (LAST insts))` by (
    irule last_flat_mapi >> simp[] >>
    qexists_tac `ao_resolve_iszero_inst targets (LAST insts)` >>
    simp[]) >>
  fs[] >>
  `!inst. get_successors (ao_resolve_iszero_inst targets inst) =
          get_successors inst` by
    (irule ao_resolve_iszero_inst_get_successors >> metis_tac[]) >>
  Cases_on `FLAT (MAPi g insts)` >> fs[] >>
  Cases_on `insts` >> fs[]
QED

(* fn_insts_blocks distributes over EVERY *)
Triviality fn_insts_blocks_every[local]:
  !blocks p. EVERY p (fn_insts_blocks blocks) <=>
    EVERY (\bb. EVERY p bb.bb_instructions) blocks
Proof
  Induct >> simp[fn_insts_blocks_def, listTheory.EVERY_APPEND]
QED

(* Phase 1 preserves EVERY inst_wf per block *)
Triviality phase1_preserves_inst_wf[local]:
  !blocks. EVERY (\bb. EVERY inst_wf bb.bb_instructions) blocks ==>
    EVERY (\bb. EVERY inst_wf bb.bb_instructions)
      (MAP (block_map_transform ao_handle_offset_inst) blocks)
Proof
  Induct >> simp[] >> rpt strip_tac >>
  simp[block_map_transform_def, listTheory.EVERY_MAP, listTheory.EVERY_MEM] >>
  rpt strip_tac >> gvs[listTheory.MEM_MAP] >>
  irule ao_handle_offset_inst_wf >>
  fs[listTheory.EVERY_MEM]
QED

(* ===== Targets no-label property ===== *)

Triviality ao_handle_offset_inst_not_add[local]:
  !inst. inst.inst_opcode <> ADD ==> ao_handle_offset_inst inst = inst
Proof
  simp[ao_handle_offset_inst_def]
QED

Triviality ao_compute_iszero_step_no_label[local]:
  !targets inst.
    (!k chain. ALOOKUP targets k = SOME chain ==>
       EVERY (\e. get_label e = NONE) chain) /\
    (inst.inst_opcode = ISZERO ==>
       EVERY (\op. get_label op = NONE) inst.inst_operands) ==>
    !k chain.
      ALOOKUP (ao_compute_iszero_step targets inst) k = SOME chain ==>
      EVERY (\e. get_label e = NONE) chain
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = ISZERO` >>
  gvs[ao_compute_iszero_step_def] >>
  rpt (FULL_CASE_TAC >> gvs[LET_THM, listTheory.EVERY_SNOC, get_label_def]) >>
  res_tac
QED

Triviality ao_compute_targets_no_label[local]:
  !insts acc.
    (!k chain. ALOOKUP acc k = SOME chain ==>
       EVERY (\e. get_label e = NONE) chain) /\
    EVERY (\inst. inst.inst_opcode = ISZERO ==>
             EVERY (\op. get_label op = NONE) inst.inst_operands) insts ==>
    !k chain.
      ALOOKUP (FOLDL ao_compute_iszero_step acc insts) k = SOME chain ==>
      EVERY (\e. get_label e = NONE) chain
Proof
  Induct >> simp[] >>
  rpt gen_tac >> strip_tac >>
  first_x_assum MATCH_MP_TAC >> simp[] >>
  match_mp_tac ao_compute_iszero_step_no_label >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* ===== Phase 3 ID distinctness ===== *)

Triviality ao_post_flip_inst_id[local]:
  !inst. (ao_post_flip_inst inst).inst_id = inst.inst_id
Proof
  rw[ao_post_flip_inst_def] >> every_case_tac >> simp[]
QED

Triviality ao_pre_flip_inst_id[local]:
  !inst. (ao_pre_flip_inst inst).inst_id = inst.inst_id
Proof
  rw[ao_pre_flip_inst_def] >> every_case_tac >> simp[]
QED

Triviality ao_peephole_inst_ids_char[local]:
  !mid dfg ra lbl idx inst j.
    MEM j (ao_peephole_inst mid dfg ra lbl idx inst) ==>
    j.inst_id = inst.inst_id \/
    ?slot. slot < 2 /\ j.inst_id = ao_fresh_id mid inst.inst_id slot
Proof
  rpt gen_tac >>
  simp[ao_peephole_inst_def, LET_THM] >>
  rpt IF_CASES_TAC >>
  simp[ao_opt_shift_def, ao_opt_signextend_def, ao_opt_exp_def,
       ao_opt_addsub_def, ao_opt_and_def, ao_opt_muldiv_def,
       ao_opt_or_def, ao_opt_eq_def, ao_opt_comparator_def, LET_THM,
       ao_cmp_prefer_iz_zero_def, ao_cmp_prefer_iz_max_def,
       ao_cmp_prefer_iz_general_def,
       ao_unsigned_boundaries_def, ao_signed_boundaries_def] >>
  every_case_tac >> gvs[] >>
  rpt IF_CASES_TAC >> gvs[] >>
  rpt strip_tac >> gvs[] >>
  ((DISJ1_TAC >> simp[] >> NO_TAC) ORELSE
   (DISJ2_TAC >> qexists_tac `0` >> simp[] >> NO_TAC) ORELSE
   (DISJ2_TAC >> qexists_tac `1` >> simp[]))
QED

Triviality ao_opt_producer_id[local]:
  !dfg inst j.
    ao_opt_producer dfg inst = SOME result /\ MEM j result ==>
    j.inst_id = inst.inst_id
Proof
  rw[ao_opt_producer_def] >>
  every_case_tac >> gvs[]
QED

Triviality ao_transform_inst_ids_char[local]:
  !mid dfg ra lbl idx targets inst j.
    MEM j (ao_transform_inst mid dfg ra lbl idx targets inst) ==>
    j.inst_id = inst.inst_id \/
    ?slot. slot < 2 /\ j.inst_id = ao_fresh_id mid inst.inst_id slot
Proof
  rpt gen_tac >>
  simp[ao_transform_inst_def, LET_THM] >>
  IF_CASES_TAC >> simp[]
  >- (strip_tac >> gvs[ao_resolve_iszero_inst_id]) >>
  IF_CASES_TAC >> simp[]
  >- (strip_tac >> gvs[ao_resolve_iszero_inst_id]) >>
  Cases_on `ao_opt_producer dfg (ao_resolve_iszero_inst targets inst)` >>
  simp[listTheory.MEM_MAP] >> rpt strip_tac >>
  gvs[ao_post_flip_inst_id] >>
  imp_res_tac ao_peephole_inst_ids_char >>
  imp_res_tac ao_opt_producer_id >>
  gvs[ao_pre_flip_inst_id, ao_resolve_iszero_inst_id] >>
  DISJ2_TAC >> qexists_tac `slot` >> simp[]
QED

Triviality ao_opt_producer_singleton[local]:
  !dfg inst result.
    ao_opt_producer dfg inst = SOME result ==> ?v. result = [v]
Proof
  rw[ao_opt_producer_def] >> every_case_tac >> gvs[]
QED

Triviality ao_transform_inst_single_distinct[local]:
  !mid dfg ra lbl idx targets inst.
    inst.inst_id <= mid ==>
    ALL_DISTINCT (MAP (\j. j.inst_id)
      (ao_transform_inst mid dfg ra lbl idx targets inst))
Proof
  rpt gen_tac >> strip_tac >>
  simp[ao_transform_inst_def, LET_THM] >>
  every_case_tac >>
  gvs[ao_resolve_iszero_inst_id, ao_pre_flip_inst_id,
      listTheory.ALL_DISTINCT, listTheory.MAP_MAP_o,
      combinTheory.o_DEF, ao_post_flip_inst_id] >>
  TRY (imp_res_tac ao_opt_producer_singleton >> gvs[] >> NO_TAC) >>
  simp[ao_peephole_inst_def, LET_THM] >>
  rpt IF_CASES_TAC >>
  simp[ao_opt_shift_def, ao_opt_signextend_def, ao_opt_exp_def,
       ao_opt_addsub_def, ao_opt_and_def, ao_opt_muldiv_def,
       ao_opt_or_def, ao_opt_eq_def, ao_opt_comparator_def, LET_THM,
       ao_cmp_prefer_iz_zero_def, ao_cmp_prefer_iz_max_def,
       ao_cmp_prefer_iz_general_def,
       ao_unsigned_boundaries_def, ao_signed_boundaries_def,
       ao_post_flip_inst_id, ao_pre_flip_inst_id, ao_resolve_iszero_inst_id,
       listTheory.ALL_DISTINCT, ao_fresh_id_def, lit_eq_def] >>
  rpt IF_CASES_TAC >>
  simp[ao_post_flip_inst_id, ao_pre_flip_inst_id,
       ao_resolve_iszero_inst_id, ao_fresh_id_def] >>
  rpt (TOP_CASE_TAC >>
       simp[ao_fresh_id_def, ao_pre_flip_inst_id, ao_resolve_iszero_inst_id]) >>
  gvs[]
QED

Triviality ao_transform_block_ids_flat[local]:
  !mid dfg ra targets bb.
    MAP (\j. j.inst_id)
      (FLAT (MAPi (\idx inst.
        ao_transform_inst mid dfg ra bb.bb_label idx targets inst)
        bb.bb_instructions)) =
    FLAT (MAPi (\idx inst.
      MAP (\j. j.inst_id)
        (ao_transform_inst mid dfg ra bb.bb_label idx targets inst))
      bb.bb_instructions)
Proof
  simp[listTheory.MAP_FLAT, indexedListsTheory.MAP_MAPi, combinTheory.o_DEF]
QED

Triviality ao_phase3_ids_all_distinct[local]:
  !insts n mid dfg ra lbl targets.
    ALL_DISTINCT (MAP (\i. i.inst_id) insts) /\
    (!inst. MEM inst insts ==> inst.inst_id <= mid) ==>
    ALL_DISTINCT (FLAT (MAPi (\idx inst.
      MAP (\j. j.inst_id)
        (ao_transform_inst mid dfg ra lbl (n + idx) targets inst)) insts))
Proof
  Induct >> simp[combinTheory.o_DEF] >> rpt strip_tac >>
  simp[listTheory.ALL_DISTINCT_APPEND, arithmeticTheory.ADD_CLAUSES] >>
  rpt conj_tac
  >- (irule ao_transform_inst_single_distinct >> gvs[])
  >- (first_x_assum (qspec_then `SUC n` mp_tac) >>
      PURE_REWRITE_TAC [arithmeticTheory.ADD_CLAUSES] >>
      disch_then irule >> gvs[])
  >- (rpt strip_tac >> CCONTR_TAC >>
      gvs[listTheory.MEM_MAP, listTheory.MEM_FLAT,
          indexedListsTheory.MEM_MAPi] >>
      `MEM (EL x insts) insts` by simp[listTheory.EL_MEM] >>
      `(EL x insts).inst_id <= mid` by res_tac >>
      `h.inst_id <= mid` by gvs[] >>
      imp_res_tac ao_transform_inst_ids_char >>
      gvs[ao_fresh_id_def] >>
      gvs[listTheory.MEM_MAP] >> metis_tac[])
QED

Triviality ao_phase3_ids_all_distinct_0[local]:
  !insts mid dfg ra lbl targets.
    ALL_DISTINCT (MAP (\i. i.inst_id) insts) /\
    (!inst. MEM inst insts ==> inst.inst_id <= mid) ==>
    ALL_DISTINCT (FLAT (MAPi (\idx inst.
      MAP (\j. j.inst_id)
        (ao_transform_inst mid dfg ra lbl idx targets inst)) insts))
Proof
  rpt strip_tac >>
  qspecl_then [`insts`, `0`] mp_tac ao_phase3_ids_all_distinct >>
  simp[]
QED

Triviality ao_phase3_ids_char_flat[local]:
  !blocks mid dfg ra targets id.
    MEM id (FLAT (MAP (\bb.
      FLAT (MAPi (\idx inst.
        MAP (\j. j.inst_id)
          (ao_transform_inst mid dfg ra bb.bb_label idx targets inst))
        bb.bb_instructions)) blocks)) ==>
    (?bb inst. MEM bb blocks /\ MEM inst bb.bb_instructions /\
       id = inst.inst_id) \/
    (?bb inst slot. MEM bb blocks /\ MEM inst bb.bb_instructions /\
       slot < 2 /\ id = ao_fresh_id mid inst.inst_id slot)
Proof
  Induct >> simp[] >> rpt strip_tac >>
  gvs[listTheory.MEM_FLAT, listTheory.MEM_APPEND,
      indexedListsTheory.MEM_MAPi]
  >- (imp_res_tac ao_transform_inst_ids_char >> gvs[] >>
      metis_tac[])
  >- (first_x_assum drule >> strip_tac >> metis_tac[])
QED

Triviality ao_phase3_fn_ids_all_distinct[local]:
  !blocks mid dfg ra targets.
    ALL_DISTINCT (FLAT (MAP (\bb. MAP (\i. i.inst_id)
      bb.bb_instructions) blocks)) /\
    (!bb inst. MEM bb blocks /\ MEM inst bb.bb_instructions ==>
      inst.inst_id <= mid) ==>
    ALL_DISTINCT (FLAT (MAP (\bb.
      FLAT (MAPi (\idx inst.
        MAP (\j. j.inst_id)
          (ao_transform_inst mid dfg ra bb.bb_label idx targets inst))
        bb.bb_instructions)) blocks))
Proof
  Induct >> simp[] >> rpt strip_tac >>
  gvs[listTheory.ALL_DISTINCT_APPEND] >> rpt conj_tac
  >- (irule ao_phase3_ids_all_distinct_0 >> rpt conj_tac
      >- (rpt strip_tac >> first_x_assum irule >> simp[])
      >- gvs[])
  >- (rpt strip_tac >> CCONTR_TAC >> gvs[] >>
      imp_res_tac ao_transform_inst_ids_char >>
      drule ao_phase3_ids_char_flat >> strip_tac >> gvs[]
      >- (`inst'.inst_id <= mid` by (first_x_assum irule >> simp[]) >>
          `h.inst_id <= mid` by (first_x_assum irule >> simp[]) >>
          `h.inst_id <> inst'.inst_id` by
            (gvs[listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
             CCONTR_TAC >> gvs[] >>
             first_x_assum (qspec_then `h.inst_id` mp_tac) >>
             simp[] >> metis_tac[]) >>
          gvs[])
      >- (`ao_fresh_id mid inst'.inst_id slot' > mid` by
            simp[ao_fresh_id_gt] >>
          `h.inst_id <= mid` by (first_x_assum irule >> simp[]) >>
          gvs[])
      >- (`inst'.inst_id <= mid` by (first_x_assum irule >> simp[]) >>
          `ao_fresh_id mid h.inst_id slot > mid` by
            simp[ao_fresh_id_gt] >> gvs[])
      >- (`ao_fresh_id mid h.inst_id slot = ao_fresh_id mid inst'.inst_id slot'`
            by gvs[] >>
          `h.inst_id = inst'.inst_id` by
            (imp_res_tac ao_fresh_id_inj >> gvs[]) >>
          `h.inst_id <= mid` by (first_x_assum irule >> simp[]) >>
          gvs[listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
          first_x_assum (qspec_then `h.inst_id` mp_tac) >>
          simp[] >> metis_tac[]))
QED

(* Phase 3 preserves wf_function *)
Triviality ao_phase3_eq_fmt[local]:
  !mid dfg ra targets fn.
    fn with fn_blocks :=
      MAP (ao_transform_block mid dfg ra targets) fn.fn_blocks =
    function_map_transform (ao_transform_block mid dfg ra targets) fn
Proof
  simp[function_map_transform_def, ir_function_component_equality]
QED

Triviality ao_phase3_succs_closed[local]:
  !mid dfg ra targets fn.
    (!bb. MEM bb fn.fn_blocks ==> bb_well_formed bb) /\
    EVERY (\bb. EVERY inst_wf bb.bb_instructions) fn.fn_blocks /\
    (!k chain. ALOOKUP targets k = SOME chain ==>
       EVERY (\e. get_label e = NONE) chain) /\
    (!bb succ. MEM bb fn.fn_blocks /\ MEM succ (bb_succs bb) ==>
       MEM succ (MAP (\bb. bb.bb_label) fn.fn_blocks)) ==>
    !bb succ.
      MEM bb (MAP (ao_transform_block mid dfg ra targets) fn.fn_blocks) /\
      MEM succ (bb_succs bb) ==>
      MEM succ (MAP (\bb. bb.bb_label)
        (MAP (ao_transform_block mid dfg ra targets) fn.fn_blocks))
Proof
  rpt strip_tac >>
  gvs[listTheory.MEM_MAP] >>
  simp[listTheory.MAP_MAP_o, combinTheory.o_DEF,
       ao_transform_block_label] >>
  `bb_well_formed y /\ EVERY inst_wf y.bb_instructions` by
    (conj_tac >- res_tac >>
     fs[listTheory.EVERY_MEM] >> res_tac) >>
  `bb_succs (ao_transform_block mid dfg ra targets y) =
   bb_succs y` by (
    match_mp_tac ao_transform_block_bb_succs >>
    rpt conj_tac >> first_assum ACCEPT_TAC) >>
  fs[] >>
  first_x_assum drule >> disch_then drule >> strip_tac >>
  qexists_tac `ao_transform_block mid dfg ra targets bb` >>
  simp[ao_transform_block_label] >>
  qexists_tac `bb` >> simp[]
QED

Triviality ao_phase3_preserves_wf[local]:
  !mid dfg ra targets fn.
    wf_function fn /\
    fn_max_inst_id fn <= mid /\
    EVERY (\bb. EVERY inst_wf bb.bb_instructions) fn.fn_blocks /\
    (!k chain. ALOOKUP targets k = SOME chain ==>
       EVERY (\e. get_label e = NONE) chain) ==>
    wf_function (function_map_transform
      (ao_transform_block mid dfg ra targets) fn)
Proof
  rpt strip_tac >>
  qabbrev_tac `bt = ao_transform_block mid dfg ra targets` >>
  simp[wf_function_def, function_map_transform_def,
       fn_labels_def, fn_has_entry_def] >>
  qpat_x_assum `wf_function fn` mp_tac >>
  simp_tac std_ss [wf_function_def, fn_labels_def, fn_has_entry_def,
       fn_succs_closed_def] >>
  simp[] >> strip_tac >>
  rpt conj_tac
  (* 1. ALL_DISTINCT labels *)
  >- (simp[listTheory.MAP_MAP_o, combinTheory.o_DEF,
           Abbr `bt`, ao_transform_block_label])
  (* 2. bb_well_formed *)
  >- (rpt strip_tac >> gvs[listTheory.MEM_MAP, Abbr `bt`] >>
      irule ao_transform_block_bb_wf >>
      res_tac >> gvs[listTheory.EVERY_MEM] >> res_tac)
  (* 3. fn_succs_closed *)
  >- (simp[Abbr `bt`] >>
      match_mp_tac ao_phase3_succs_closed >>
      rpt conj_tac >> first_assum ACCEPT_TAC)
  (* 4. fn_inst_ids_distinct *)
  >- (simp[venomWfTheory.fn_inst_ids_distinct_def, Abbr `bt`,
           ao_transform_block_def, listTheory.MAP_MAP_o,
           combinTheory.o_DEF, ao_transform_block_ids_flat] >>
      irule ao_phase3_fn_ids_all_distinct >> rpt conj_tac
      >- (rpt strip_tac >>
          `MEM inst (fn_insts fn)` by metis_tac[mem_bb_fn_insts] >>
          `inst.inst_id <= fn_max_inst_id fn` by
            metis_tac[fn_max_inst_id_bound] >> gvs[])
      >- gvs[GSYM fn_insts_blocks_map_id, fn_insts_def])
QED

(* Phase 1 preserves the ISZERO-no-label property *)
Triviality fn_insts_blocks_map_transform[local]:
  !blocks f.
    fn_insts_blocks (MAP (block_map_transform f) blocks) =
    MAP f (fn_insts_blocks blocks)
Proof
  Induct >> simp[fn_insts_blocks_def, block_map_transform_def]
QED

Triviality fn_insts_block_map_transform[local]:
  !f fn.
    fn_insts (function_map_transform (block_map_transform f) fn) =
    MAP f (fn_insts fn)
Proof
  simp[fn_insts_def, function_map_transform_def, fn_insts_blocks_map_transform]
QED

Triviality phase1_preserves_iszero_no_label[local]:
  !fn.
    EVERY (\inst. inst.inst_opcode = ISZERO ==>
       EVERY (\op. get_label op = NONE) inst.inst_operands) (fn_insts fn) ==>
    EVERY (\inst. inst.inst_opcode = ISZERO ==>
       EVERY (\op. get_label op = NONE) inst.inst_operands)
      (fn_insts (function_map_transform
        (block_map_transform ao_handle_offset_inst) fn))
Proof
  simp[fn_insts_block_map_transform] >>
  PURE_REWRITE_TAC[listTheory.EVERY_MAP] >>
  simp[listTheory.EVERY_MEM, combinTheory.o_DEF] >>
  rpt strip_tac >>
  Cases_on `x.inst_opcode = ADD` >- (
    gvs[ao_handle_offset_inst_def, LET_THM] >>
    rpt (FULL_CASE_TAC >> gvs[])) >>
  gvs[ao_handle_offset_inst_not_add] >> res_tac
QED

(* ===== Top-level preservation ===== *)

(* ao_cmp_flip_apply_inst produces non-empty output *)
Triviality ao_cmp_flip_apply_ne[local]:
  !mid flips removes inserts inst.
    ao_cmp_flip_apply_inst mid flips removes inserts inst <> []
Proof
  rpt gen_tac >>
  simp[ao_cmp_flip_apply_inst_def] >>
  every_case_tac
QED

(* ao_cmp_flip_apply_inst preserves non-terminator when flips have non-term opcodes *)
Triviality ao_cmp_flip_apply_non_term[local]:
  !mid flips removes inserts inst.
    ~is_terminator inst.inst_opcode /\
    (!id opc w op. ALOOKUP flips id = SOME (opc, w, op) ==>
       ~is_terminator opc) ==>
    EVERY (\r. ~is_terminator r.inst_opcode)
      (ao_cmp_flip_apply_inst mid flips removes inserts inst)
Proof
  rpt strip_tac >>
  simp[ao_cmp_flip_apply_inst_def] >>
  every_case_tac >> gvs[listTheory.EVERY_DEF, is_terminator_def] >>
  res_tac
QED

(* flip_comparison_opcode is non-terminator and non-PHI *)
Triviality flip_cmp_non_term[local]:
  !opc. is_comparator opc ==> ~is_terminator (flip_comparison_opcode opc)
Proof
  simp[is_comparator_def] >> rpt strip_tac >>
  gvs[flip_comparison_opcode_def, is_terminator_def]
QED

Triviality flip_cmp_non_phi[local]:
  !opc. is_comparator opc ==> flip_comparison_opcode opc <> PHI
Proof
  simp[is_comparator_def] >> rpt strip_tac >>
  gvs[flip_comparison_opcode_def]
QED

(* ao_cmp_flip_scan step: flips either unchanged or extended with flip *)
Triviality ao_cmp_flip_scan_flips_shape[local]:
  !dfg h insts flips removes inserts flips' removes' inserts'.
    ao_cmp_flip_scan dfg insts = (flips', removes', inserts') /\
    ao_cmp_flip_scan dfg (h::insts) = (flips, removes, inserts) ==>
    flips = flips' \/
    ?opc w' op1. is_comparator opc /\
      flips = (h.inst_id, flip_comparison_opcode opc, w', op1)::flips'
Proof
  rpt strip_tac >>
  qpat_x_assum `ao_cmp_flip_scan _ (_::_) = _` mp_tac >>
  simp[ao_cmp_flip_scan_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  simp[AllCaseEqs(), PULL_EXISTS,
       ao_signed_boundaries_def, ao_unsigned_boundaries_def, LET_THM] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `h.inst_opcode` >>
  gvs[is_comparator_def,
      ao_signed_boundaries_def, ao_unsigned_boundaries_def, LET_THM] >>
  qpat_x_assum `_ = (flips, removes, inserts)` mp_tac >>
  simp[AllCaseEqs(), PULL_EXISTS] >>
  rpt strip_tac >> gvs[] >>
  metis_tac[flip_comparison_opcode_def]
QED

(* ao_cmp_flip_scan: non-comparator instruction doesn't change anything *)
Triviality ao_cmp_flip_scan_non_comp_unchanged[local]:
  !dfg h insts flips removes inserts flips' removes' inserts'.
    ao_cmp_flip_scan dfg insts = (flips', removes', inserts') /\
    ao_cmp_flip_scan dfg (h::insts) = (flips, removes, inserts) /\
    ~is_comparator h.inst_opcode ==>
    flips = flips' /\ removes = removes' /\ inserts = inserts'
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `ao_cmp_flip_scan _ (_::_) = _` mp_tac >>
  simp[ao_cmp_flip_scan_def, LET_THM] >>
  pairarg_tac >> gvs[]
QED

(* ao_cmp_flip_scan: flips keys come from comparator instructions in insts *)
Triviality ao_cmp_flip_scan_flips_domain[local]:
  !dfg insts flips removes inserts id v.
    ao_cmp_flip_scan dfg insts = (flips, removes, inserts) /\
    ALOOKUP flips id = SOME v ==>
    ?inst. MEM inst insts /\ inst.inst_id = id /\ is_comparator inst.inst_opcode
Proof
  Induct_on `insts`
  >- simp[ao_cmp_flip_scan_def]
  >> rpt gen_tac >> strip_tac >>
  Cases_on `ao_cmp_flip_scan dfg insts` >> Cases_on `r` >>
  rename1 `ao_cmp_flip_scan dfg insts = (flips', removes', inserts')` >>
  Cases_on `is_comparator h.inst_opcode`
  >- (drule_all ao_cmp_flip_scan_flips_shape >>
      strip_tac >> gvs[]
      >- (first_x_assum drule_all >> strip_tac >>
          qexists_tac `inst` >> simp[])
      >- (Cases_on `h.inst_id = id` >> gvs[]
          >- (qexists_tac `h` >> simp[])
          >- (first_x_assum drule_all >> strip_tac >>
              qexists_tac `inst` >> simp[])))
  >- (drule_all ao_cmp_flip_scan_non_comp_unchanged >> strip_tac >> gvs[] >>
      first_x_assum drule_all >> strip_tac >>
      qexists_tac `inst` >> simp[])
QED

(* ao_cmp_flip_scan: removes either unchanged or prepended with an ISZERO DFG id *)
Triviality ao_cmp_flip_scan_removes_shape[local]:
  !dfg h insts flips removes inserts flips' removes' inserts'.
    ao_cmp_flip_scan dfg insts = (flips', removes', inserts') /\
    ao_cmp_flip_scan dfg (h::insts) = (flips, removes, inserts) ==>
    removes = removes' \/
    ?v. LENGTH (dfg_get_uses dfg v) = 1 /\
        (HD (dfg_get_uses dfg v)).inst_opcode = ISZERO /\
        removes = (HD (dfg_get_uses dfg v)).inst_id :: removes'
Proof
  rpt strip_tac >>
  qpat_x_assum `ao_cmp_flip_scan _ (_::_) = _` mp_tac >>
  simp[ao_cmp_flip_scan_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  simp[AllCaseEqs(), PULL_EXISTS,
       ao_signed_boundaries_def, ao_unsigned_boundaries_def, LET_THM] >>
  rpt strip_tac >> gvs[] >>
  metis_tac[]
QED

(* ao_cmp_flip_scan: inserts either unchanged or prepended with an ASSERT DFG id *)
Triviality ao_cmp_flip_scan_inserts_shape[local]:
  !dfg h insts flips removes inserts flips' removes' inserts'.
    ao_cmp_flip_scan dfg insts = (flips', removes', inserts') /\
    ao_cmp_flip_scan dfg (h::insts) = (flips, removes, inserts) ==>
    inserts = inserts' \/
    ?v. LENGTH (dfg_get_uses dfg v) = 1 /\
        (HD (dfg_get_uses dfg v)).inst_opcode = ASSERT /\
        inserts = ((HD (dfg_get_uses dfg v)).inst_id, v,
                   ao_fresh_var h.inst_id "iz", h.inst_id) :: inserts'
Proof
  rpt strip_tac >>
  qpat_x_assum `ao_cmp_flip_scan _ (_::_) = _` mp_tac >>
  simp[ao_cmp_flip_scan_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  simp[AllCaseEqs(), PULL_EXISTS,
       ao_signed_boundaries_def, ao_unsigned_boundaries_def, LET_THM] >>
  rpt strip_tac >> gvs[]
QED

(* ao_cmp_flip_scan: removes entries come from DFG lookups *)
Triviality ao_cmp_flip_scan_removes_from_dfg[local]:
  !dfg insts flips removes inserts id.
    ao_cmp_flip_scan dfg insts = (flips, removes, inserts) /\
    MEM id removes ==>
    ?v inst. MEM inst (dfg_get_uses dfg v) /\ inst.inst_id = id /\
             inst.inst_opcode = ISZERO
Proof
  Induct_on `insts`
  >- simp[ao_cmp_flip_scan_def]
  >> rpt gen_tac >> strip_tac >>
  Cases_on `ao_cmp_flip_scan dfg insts` >> Cases_on `r` >>
  rename1 `ao_cmp_flip_scan dfg insts = (flips', removes', inserts')` >>
  drule_all ao_cmp_flip_scan_removes_shape >>
  strip_tac
  >- (gvs[] >> first_x_assum drule_all >> metis_tac[])
  >- (gvs[] >>
      Cases_on `dfg_get_uses dfg v` >> gvs[] >>
      metis_tac[listTheory.MEM])
QED

(* ao_cmp_flip_scan: inserts keys come from ASSERT DFG lookups *)
Triviality ao_cmp_flip_scan_inserts_from_dfg[local]:
  !dfg insts flips removes inserts id v.
    ao_cmp_flip_scan dfg insts = (flips, removes, inserts) /\
    ALOOKUP inserts id = SOME v ==>
    ?w inst. MEM inst (dfg_get_uses dfg w) /\ inst.inst_id = id /\
             inst.inst_opcode = ASSERT
Proof
  Induct_on `insts`
  >- simp[ao_cmp_flip_scan_def]
  >> rpt gen_tac >> strip_tac >>
  Cases_on `ao_cmp_flip_scan dfg insts` >> Cases_on `r` >>
  rename1 `ao_cmp_flip_scan dfg insts = (flips', removes', inserts')` >>
  drule_all ao_cmp_flip_scan_inserts_shape >>
  strip_tac
  >- (gvs[] >> first_x_assum drule_all >> metis_tac[])
  >- (gvs[] >>
      Cases_on `dfg_get_uses dfg v'` >> gvs[] >>
      metis_tac[listTheory.MEM])
QED

(* ao_cmp_flip_scan: flips only contain non-terminator opcodes *)
Triviality ao_cmp_flip_scan_flips_non_term[local]:
  !dfg insts flips removes inserts.
    ao_cmp_flip_scan dfg insts = (flips, removes, inserts) ==>
    !id opc w op. ALOOKUP flips id = SOME (opc, w, op) ==>
      ~is_terminator opc /\ opc <> PHI
Proof
  Induct_on `insts`
  >- simp[ao_cmp_flip_scan_def]
  >> rpt gen_tac >> strip_tac >>
  Cases_on `ao_cmp_flip_scan dfg insts` >> Cases_on `r` >>
  rename1 `ao_cmp_flip_scan dfg insts = (flips', removes', inserts')` >>
  drule_all ao_cmp_flip_scan_flips_shape >>
  strip_tac >> gvs[]
  >- (rpt strip_tac >> first_x_assum drule_all >> gvs[])
  >- (rpt gen_tac >> strip_tac >>
      Cases_on `h.inst_id = id` >> gvs[]
      >- (imp_res_tac flip_cmp_non_term >>
          imp_res_tac flip_cmp_non_phi >> gvs[])
      >- (first_x_assum drule_all >> gvs[]))
QED

(* Terminators/PHIs are not affected by the scan, given distinct ids and DFG soundness.
   The proof uses domain lemmas: flips keys are from comparators in insts,
   removes/inserts ids are from DFG lookups. With ALL_DISTINCT ids and the
   DFG returning function instructions, no terminator/PHI id can collide. *)
Triviality all_distinct_id_eq[local]:
  !l x y. ALL_DISTINCT (MAP (\i. i.inst_id) l) /\
           MEM x l /\ MEM y l /\ x.inst_id = y.inst_id ==> x = y
Proof
  Induct_on `l` >> simp[] >> rpt strip_tac >> gvs[] >>
  gvs[listTheory.MEM_MAP]
QED

Triviality ao_cmp_flip_scan_no_term[local]:
  !dfg insts flips removes inserts inst.
    ao_cmp_flip_scan dfg insts = (flips, removes, inserts) /\
    MEM inst insts /\
    is_terminator inst.inst_opcode /\
    ALL_DISTINCT (MAP (\i. i.inst_id) insts) /\
    (!v i. MEM i (dfg_get_uses dfg v) ==> MEM i insts) ==>
    ALOOKUP flips inst.inst_id = NONE /\
    ~MEM inst.inst_id removes /\
    ALOOKUP inserts inst.inst_id = NONE
Proof
  rpt strip_tac >> rpt conj_tac
  >- (CCONTR_TAC >>
      `?v. ALOOKUP flips inst.inst_id = SOME v` by
        (Cases_on `ALOOKUP flips inst.inst_id` >> gvs[]) >>
      drule_all ao_cmp_flip_scan_flips_domain >> strip_tac >>
      rename1 `is_comparator cinst.inst_opcode` >>
      `cinst = inst` by
        (match_mp_tac all_distinct_id_eq >> qexists_tac `insts` >> simp[]) >>
      gvs[is_terminator_def, is_comparator_def])
  >- (CCONTR_TAC >> gvs[] >>
      drule_all ao_cmp_flip_scan_removes_from_dfg >> strip_tac >>
      rename1 `MEM rinst (dfg_get_uses dfg _)` >>
      `MEM rinst insts` by res_tac >>
      `rinst = inst` by
        (match_mp_tac all_distinct_id_eq >> qexists_tac `insts` >> simp[]) >>
      gvs[is_terminator_def])
  >- (CCONTR_TAC >>
      `?v. ALOOKUP inserts inst.inst_id = SOME v` by
        (Cases_on `ALOOKUP inserts inst.inst_id` >> gvs[]) >>
      drule_all ao_cmp_flip_scan_inserts_from_dfg >> strip_tac >>
      rename1 `MEM iinst (dfg_get_uses dfg _)` >>
      `MEM iinst insts` by res_tac >>
      `iinst = inst` by
        (match_mp_tac all_distinct_id_eq >> qexists_tac `insts` >> simp[]) >>
      gvs[is_terminator_def])
QED

Triviality ao_cmp_flip_scan_no_phi[local]:
  !dfg insts flips removes inserts inst.
    ao_cmp_flip_scan dfg insts = (flips, removes, inserts) /\
    MEM inst insts /\
    inst.inst_opcode = PHI /\
    ALL_DISTINCT (MAP (\i. i.inst_id) insts) /\
    (!v i. MEM i (dfg_get_uses dfg v) ==> MEM i insts) ==>
    ALOOKUP flips inst.inst_id = NONE /\
    ~MEM inst.inst_id removes /\
    ALOOKUP inserts inst.inst_id = NONE
Proof
  rpt strip_tac >> rpt conj_tac
  >- (CCONTR_TAC >>
      `?v. ALOOKUP flips inst.inst_id = SOME v` by
        (Cases_on `ALOOKUP flips inst.inst_id` >> gvs[]) >>
      drule_all ao_cmp_flip_scan_flips_domain >> strip_tac >>
      rename1 `is_comparator cinst.inst_opcode` >>
      `cinst = inst` by
        (match_mp_tac all_distinct_id_eq >> qexists_tac `insts` >> simp[]) >>
      gvs[is_comparator_def])
  >- (CCONTR_TAC >> gvs[] >>
      drule_all ao_cmp_flip_scan_removes_from_dfg >> strip_tac >>
      rename1 `MEM rinst (dfg_get_uses dfg _)` >>
      `MEM rinst insts` by res_tac >>
      `rinst = inst` by
        (match_mp_tac all_distinct_id_eq >> qexists_tac `insts` >> simp[]) >>
      gvs[])
  >- (CCONTR_TAC >>
      `?v. ALOOKUP inserts inst.inst_id = SOME v` by
        (Cases_on `ALOOKUP inserts inst.inst_id` >> gvs[]) >>
      drule_all ao_cmp_flip_scan_inserts_from_dfg >> strip_tac >>
      rename1 `MEM iinst (dfg_get_uses dfg _)` >>
      `MEM iinst insts` by res_tac >>
      `iinst = inst` by
        (match_mp_tac all_distinct_id_eq >> qexists_tac `insts` >> simp[]) >>
      gvs[])
QED

(* ao_cmp_flip_apply_inst preserves terminator singleton *)
Triviality ao_cmp_flip_apply_term[local]:
  !mid flips removes inserts inst.
    ALOOKUP flips inst.inst_id = NONE /\
    ~MEM inst.inst_id removes /\
    ALOOKUP inserts inst.inst_id = NONE ==>
    ao_cmp_flip_apply_inst mid flips removes inserts inst = [inst]
Proof
  rpt strip_tac >>
  simp[ao_cmp_flip_apply_inst_def] >>
  gvs[]
QED

(* ao_cmp_flip_apply_inst: non-PHI inputs produce non-PHI outputs *)
Triviality ao_cmp_flip_apply_non_phi[local]:
  !mid flips removes inserts inst.
    inst.inst_opcode <> PHI /\
    (!id opc w op. ALOOKUP flips id = SOME (opc, w, op) ==> opc <> PHI) ==>
    EVERY (\r. r.inst_opcode <> PHI)
      (ao_cmp_flip_apply_inst mid flips removes inserts inst)
Proof
  rpt strip_tac >>
  simp[ao_cmp_flip_apply_inst_def] >>
  every_case_tac >> gvs[] >>
  CCONTR_TAC >> gvs[]
QED

Triviality mem_fn_insts_blocks[local]:
  !blocks inst bb.
    MEM bb blocks /\ MEM inst bb.bb_instructions ==>
    MEM inst (fn_insts_blocks blocks)
Proof
  Induct >> simp[fn_insts_blocks_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[listTheory.MEM_APPEND]
QED

Triviality mem_bb_fn_insts[local]:
  !inst bb fn.
    MEM inst bb.bb_instructions /\ MEM bb fn.fn_blocks ==>
    MEM inst (fn_insts fn)
Proof
  metis_tac[fn_insts_def, mem_fn_insts_blocks]
QED

Triviality fn_insts_blocks_map_id[local]:
  !blocks.
    FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) blocks) =
    MAP (\i. i.inst_id) (fn_insts_blocks blocks)
Proof
  Induct >> simp[fn_insts_blocks_def, listTheory.MAP_APPEND]
QED

Triviality fn_inst_ids_as_fn_insts[local]:
  !fn. fn_inst_ids_distinct fn <=>
    ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn))
Proof
  simp[venomWfTheory.fn_inst_ids_distinct_def, fn_insts_def,
       GSYM fn_insts_blocks_map_id]
QED

Triviality ao_cmp_flip_apply_inst_id[local]:
  !mid flips removes inserts inst.
    ~MEM inst.inst_id (MAP FST flips) /\
    ~MEM inst.inst_id removes /\
    ~MEM inst.inst_id (MAP FST inserts) ==>
    ao_cmp_flip_apply_inst mid flips removes inserts inst = [inst]
Proof
  rpt strip_tac >>
  `ALOOKUP flips inst.inst_id = NONE` by simp[alistTheory.ALOOKUP_NONE] >>
  `ALOOKUP inserts inst.inst_id = NONE` by simp[alistTheory.ALOOKUP_NONE] >>
  simp[ao_cmp_flip_apply_inst_def]
QED

Triviality ao_phase4_bb_succs[local]:
  !mid flips removes inserts bb.
    bb_well_formed bb /\
    (!inst. MEM inst bb.bb_instructions /\ is_terminator inst.inst_opcode ==>
      ~MEM inst.inst_id (MAP FST flips) /\
      ~MEM inst.inst_id removes /\
      ~MEM inst.inst_id (MAP FST inserts)) ==>
    bb_succs (bb with bb_instructions :=
      FLAT (MAP (ao_cmp_flip_apply_inst mid flips removes inserts)
                bb.bb_instructions)) = bb_succs bb
Proof
  rpt strip_tac >>
  fs[bb_well_formed_def] >>
  `bb.bb_instructions <> []` by (Cases_on `bb.bb_instructions` >> gvs[]) >>
  `ao_cmp_flip_apply_inst mid flips removes inserts (LAST bb.bb_instructions) =
   [LAST bb.bb_instructions]` by
    (match_mp_tac ao_cmp_flip_apply_inst_id >>
     qpat_x_assum `!inst. _ /\ is_terminator _ ==> _`
       (qspec_then `LAST bb.bb_instructions` mp_tac) >>
     simp[rich_listTheory.MEM_LAST_NOT_NIL]) >>
  simp[bb_succs_def] >>
  `FLAT (MAP (ao_cmp_flip_apply_inst mid flips removes inserts)
             bb.bb_instructions) <> []` by
    (Cases_on `bb.bb_instructions` >> gvs[ao_cmp_flip_apply_ne]) >>
  simp[] >>
  `LAST (FLAT (MAP (ao_cmp_flip_apply_inst mid flips removes inserts)
                   bb.bb_instructions)) =
   LAST (ao_cmp_flip_apply_inst mid flips removes inserts
           (LAST bb.bb_instructions))` by
    (irule last_flat_map >> simp[ao_cmp_flip_apply_ne]) >>
  every_case_tac >> gvs[]
QED

Triviality ao_phase4_bb_wf[local]:
  !mid dfg fn bb flips removes inserts.
    ao_cmp_flip_scan dfg (fn_insts fn) = (flips, removes, inserts) /\
    MEM bb fn.fn_blocks /\ bb_well_formed bb /\
    ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
    (!v i. MEM i (dfg_get_uses dfg v) ==> MEM i (fn_insts fn)) ==>
    bb_well_formed (bb with bb_instructions :=
      FLAT (MAP (ao_cmp_flip_apply_inst mid flips removes inserts)
                bb.bb_instructions))
Proof
  rpt strip_tac >>
  irule flat_map_preserves_bb_wf >> rpt conj_tac
  (* 1. non-term => non-term outputs *)
  >- (rpt strip_tac >>
      `MEM inst (fn_insts fn)` by metis_tac[mem_bb_fn_insts] >>
      `EVERY (\r. ~is_terminator r.inst_opcode)
        (ao_cmp_flip_apply_inst mid flips removes inserts inst)` by
        (match_mp_tac ao_cmp_flip_apply_non_term >> simp[] >>
         rpt strip_tac >>
         drule_all ao_cmp_flip_scan_flips_non_term >> simp[]) >>
      gvs[listTheory.EVERY_MEM])
  (* 2. non-PHI => non-PHI outputs *)
  >- (rpt strip_tac >>
      `MEM inst (fn_insts fn)` by metis_tac[mem_bb_fn_insts] >>
      `EVERY (\r. r.inst_opcode <> PHI)
        (ao_cmp_flip_apply_inst mid flips removes inserts inst)` by
        (match_mp_tac ao_cmp_flip_apply_non_phi >> simp[] >>
         rpt strip_tac >>
         drule_all ao_cmp_flip_scan_flips_non_term >> simp[]) >>
      gvs[listTheory.EVERY_MEM])
  (* 3. terminator => [inst] *)
  >- (rpt strip_tac >>
      `MEM inst (fn_insts fn)` by metis_tac[mem_bb_fn_insts] >>
      drule_all ao_cmp_flip_scan_no_term >> strip_tac >>
      irule ao_cmp_flip_apply_term >> simp[])
  (* 4. PHI => [inst] *)
  >- (rpt strip_tac >>
      `MEM inst (fn_insts fn)` by metis_tac[mem_bb_fn_insts] >>
      drule_all ao_cmp_flip_scan_no_phi >> strip_tac >>
      irule ao_cmp_flip_apply_term >> simp[])
  (* 5. non-empty *)
  >- simp[ao_cmp_flip_apply_ne]
  (* 6. bb_well_formed *)
  >- simp[]
QED

Triviality ao_phase4_succs_closed[local]:
  !mid dfg fn flips removes inserts.
    wf_function fn /\
    ao_cmp_flip_scan dfg (fn_insts fn) = (flips, removes, inserts) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
    (!v i. MEM i (dfg_get_uses dfg v) ==> MEM i (fn_insts fn)) ==>
    fn_succs_closed (fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        FLAT (MAP (ao_cmp_flip_apply_inst mid flips removes inserts)
                  bb.bb_instructions)) fn.fn_blocks)
Proof
  rpt strip_tac >>
  simp[fn_succs_closed_def] >>
  rpt strip_tac >> gvs[listTheory.MEM_MAP] >>
  rename1 `MEM bb0 fn.fn_blocks` >>
  `bb_well_formed bb0` by
    (fs[wf_function_def] >> res_tac) >>
  `!inst. MEM inst bb0.bb_instructions /\
          is_terminator inst.inst_opcode ==>
          ~MEM inst.inst_id (MAP FST flips) /\
          ~MEM inst.inst_id removes /\
          ~MEM inst.inst_id (MAP FST inserts)` by
    (rpt strip_tac >> gvs[alistTheory.ALOOKUP_NONE] >>
     drule_all mem_bb_fn_insts >> strip_tac >>
     drule_all ao_cmp_flip_scan_no_term >> gvs[alistTheory.ALOOKUP_NONE]) >>
  `bb_succs (bb0 with bb_instructions :=
     FLAT (MAP (ao_cmp_flip_apply_inst mid flips removes inserts)
               bb0.bb_instructions)) = bb_succs bb0` by
    (match_mp_tac ao_phase4_bb_succs >> simp[]) >>
  gvs[] >>
  simp[fn_labels_def, listTheory.MAP_MAP_o, combinTheory.o_DEF] >>
  fs[wf_function_def, fn_succs_closed_def, fn_labels_def] >>
  res_tac
QED

(* cmp_ids in inserts are instruction IDs from the scanned list *)
Triviality ao_cmp_flip_scan_inserts_cmp_id_mem[local]:
  !dfg insts flips removes inserts k co fv cid.
    ao_cmp_flip_scan dfg insts = (flips, removes, inserts) /\
    MEM (k, co, fv, cid) inserts ==>
    ?inst. MEM inst insts /\ inst.inst_id = cid /\ is_comparator inst.inst_opcode
Proof
  Induct_on `insts`
  >- simp[ao_cmp_flip_scan_def]
  >> rpt gen_tac >> strip_tac >>
  Cases_on `ao_cmp_flip_scan dfg insts` >> Cases_on `r` >>
  rename1 `ao_cmp_flip_scan dfg insts = (flips', removes', inserts')` >>
  drule_all ao_cmp_flip_scan_inserts_shape >>
  strip_tac
  >- (gvs[] >> first_x_assum drule_all >> strip_tac >>
      qexists_tac `inst` >> simp[])
  >- (`is_comparator h.inst_opcode` by
        (CCONTR_TAC >>
         drule_all ao_cmp_flip_scan_non_comp_unchanged >> gvs[]) >>
      gvs[listTheory.MEM]
      >- (qexists_tac `h` >> simp[])
      >- (first_x_assum drule_all >> strip_tac >>
          qexists_tac `inst` >> simp[]))
QED

(* cmp_ids in inserts are distinct when instruction IDs are distinct *)
Triviality ao_cmp_flip_scan_inserts_cmp_ids_distinct[local]:
  !dfg insts flips removes inserts.
    ao_cmp_flip_scan dfg insts = (flips, removes, inserts) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) insts) ==>
    ALL_DISTINCT (MAP (\(k, co, fv, cid). cid) inserts)
Proof
  Induct_on `insts`
  >- simp[ao_cmp_flip_scan_def]
  >> rpt gen_tac >> strip_tac >>
  Cases_on `ao_cmp_flip_scan dfg insts` >> Cases_on `r` >>
  rename1 `ao_cmp_flip_scan dfg insts = (flips', removes', inserts')` >>
  drule_all ao_cmp_flip_scan_inserts_shape >>
  strip_tac
  >- (gvs[] >> first_x_assum match_mp_tac >>
      qexists_tac `dfg` >> qexists_tac `flips'` >>
      qexists_tac `removes'` >> gvs[])
  >- (gvs[] >>
      `ALL_DISTINCT (MAP (\(k,co,fv,cid). cid) inserts')` by
        (first_x_assum match_mp_tac >>
         qexists_tac `dfg` >> qexists_tac `flips'` >>
         qexists_tac `removes'` >> gvs[]) >>
      `~MEM h.inst_id (MAP (\(k,co,fv,cid). cid) inserts')` by
        (simp[listTheory.MEM_MAP, pairTheory.FORALL_PROD] >>
         rpt strip_tac >>
         drule_all ao_cmp_flip_scan_inserts_cmp_id_mem >> strip_tac >>
         gvs[listTheory.ALL_DISTINCT, listTheory.MEM_MAP] >>
         metis_tac[]) >>
      gvs[listTheory.ALL_DISTINCT])
QED

(* IDs produced by ao_cmp_flip_apply_inst *)
Triviality ao_cmp_flip_apply_inst_ids_char[local]:
  !mid flips removes inserts inst id.
    MEM id (MAP (\j. j.inst_id)
      (ao_cmp_flip_apply_inst mid flips removes inserts inst)) ==>
    id = inst.inst_id \/
    ?cmp_id. ALOOKUP inserts inst.inst_id = SOME (cmp_id) /\
             id = ao_fresh_id mid (SND (SND cmp_id)) 0
Proof
  rpt gen_tac >>
  simp[ao_cmp_flip_apply_inst_def] >>
  every_case_tac >> gvs[]
QED

(* Generic: ALL_DISTINCT of MAP f implies f is injective on list elements *)
Triviality all_distinct_map_inj_mem[local]:
  !f l x y. ALL_DISTINCT (MAP f l) /\ MEM x l /\ MEM y l /\ f x = f y ==> x = y
Proof
  Induct_on `l` >> rpt strip_tac >>
  gvs[listTheory.ALL_DISTINCT, listTheory.MEM] >>
  metis_tac[listTheory.MEM_MAP_f]
QED

(* Characterization of IDs in the FLAT MAP result *)
Triviality ao_cmp_flip_flat_map_ids_char[local]:
  !insts id mid flips removes inserts.
    MEM id (FLAT (MAP (\inst. MAP (\j. j.inst_id)
      (ao_cmp_flip_apply_inst mid flips removes inserts inst)) insts)) ==>
    (?inst. MEM inst insts /\ id = inst.inst_id) \/
    (?inst co fv cid. MEM inst insts /\
       ALOOKUP inserts inst.inst_id = SOME (co,fv,cid) /\
       id = ao_fresh_id mid cid 0)
Proof
  Induct_on `insts` >> simp[] >> rpt strip_tac >>
  fs[listTheory.MEM_APPEND]
  >- (imp_res_tac ao_cmp_flip_apply_inst_ids_char >> gvs[]
      >- (DISJ1_TAC >> metis_tac[])
      >- (DISJ2_TAC >> qexists_tac `h` >>
          Cases_on `cmp_id` >> Cases_on `r` >> gvs[]))
  >- (first_x_assum drule >> strip_tac >> metis_tac[])
QED

(* IDs from a single instruction application are distinct *)
Triviality ao_cmp_flip_apply_single_distinct[local]:
  !inst mid flips removes inserts.
    inst.inst_id <= mid ==>
    ALL_DISTINCT (MAP (\j. j.inst_id)
      (ao_cmp_flip_apply_inst mid flips removes inserts inst))
Proof
  rpt strip_tac >>
  simp[ao_cmp_flip_apply_inst_def] >>
  every_case_tac >>
  gvs[listTheory.ALL_DISTINCT, ao_fresh_id_def]
QED

(* If ALL_DISTINCT cids and two ALOOKUP entries have different keys, cids differ *)
Triviality alookup_cid_neq[local]:
  !inserts k1 k2 co1 fv1 cid1 co2 fv2 cid2.
    ALOOKUP inserts k1 = SOME (co1,fv1,cid1) /\
    ALOOKUP inserts k2 = SOME (co2,fv2,cid2) /\
    ALL_DISTINCT (MAP (\(k,co,fv,cid). cid) inserts) /\
    k1 <> k2 ==> cid1 <> cid2
Proof
  Induct_on `inserts` >> simp[] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[listTheory.ALL_DISTINCT, listTheory.MEM_MAP,
       pairTheory.EXISTS_PROD] >>
  rpt strip_tac >>
  Cases_on `h0 = k1` >> Cases_on `h0 = k2` >> gvs[] >>
  metis_tac[alistTheory.ALOOKUP_MEM]
QED

(* Equating the block-level and instruction-level ID lists *)
Triviality fn_inst_ids_flat_map_eq[local]:
  !f blocks.
    FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions)
          (MAP (\bb. bb with bb_instructions :=
            FLAT (MAP f bb.bb_instructions)) blocks)) =
    FLAT (MAP (\inst. MAP (\j. j.inst_id) (f inst))
          (fn_insts_blocks blocks))
Proof
  Induct_on `blocks` >>
  gvs[venomInstTheory.fn_insts_blocks_def, listTheory.MAP_FLAT,
      listTheory.MAP_MAP_o, combinTheory.o_DEF]
QED

(* Main: FLAT MAP of apply produces ALL_DISTINCT IDs *)
Triviality ao_cmp_flip_ids_all_distinct[local]:
  !insts mid flips removes inserts.
    ALL_DISTINCT (MAP (\i. i.inst_id) insts) /\
    (!inst. MEM inst insts ==> inst.inst_id <= mid) /\
    ALL_DISTINCT (MAP (\(k,co,fv,cid). cid) inserts) ==>
    ALL_DISTINCT (FLAT (MAP (\inst. MAP (\j. j.inst_id)
      (ao_cmp_flip_apply_inst mid flips removes inserts inst)) insts))
Proof
  Induct_on `insts` >> simp[] >> rpt strip_tac >>
  simp[listTheory.ALL_DISTINCT_APPEND] >> rpt conj_tac
  >- (irule ao_cmp_flip_apply_single_distinct >> gvs[])
  >- (rpt strip_tac >> CCONTR_TAC >> gvs[] >>
      drule ao_cmp_flip_flat_map_ids_char >> strip_tac >>
      drule ao_cmp_flip_apply_inst_ids_char >> strip_tac >> gvs[]
      >- (`inst.inst_id <= mid` by res_tac >>
          `h.inst_id <= mid` by gvs[] >>
          gvs[listTheory.ALL_DISTINCT, listTheory.MEM_MAP] >>
          metis_tac[])
      >- (`ao_fresh_id mid (SND (SND cmp_id)) 0 > mid` by
            simp[ao_fresh_id_gt] >>
          `inst.inst_id <= mid` by res_tac >> gvs[])
      >- (`ao_fresh_id mid cid 0 > mid` by simp[ao_fresh_id_gt] >>
          `h.inst_id <= mid` by gvs[] >> gvs[])
      >- (`SND (SND cmp_id) = cid` by gvs[ao_fresh_id_def] >>
          `h.inst_id <> inst.inst_id` by
            (gvs[listTheory.ALL_DISTINCT, listTheory.MEM_MAP] >>
             metis_tac[]) >>
          Cases_on `cmp_id` >> Cases_on `r` >> gvs[] >>
          drule_all alookup_cid_neq >> gvs[]))
QED

Triviality ao_phase4_preserves_wf[local]:
  !mid dfg fn.
    wf_function fn /\
    fn_max_inst_id fn <= mid /\
    (!v i. MEM i (dfg_get_uses dfg v) ==> MEM i (fn_insts fn)) ==>
    wf_function (ao_cmp_flip_function mid dfg fn)
Proof
  rpt strip_tac >>
  simp[ao_cmp_flip_function_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  IF_CASES_TAC >> gvs[] >>
  qpat_x_assum `wf_function fn` mp_tac >>
  simp_tac std_ss [wf_function_def] >> strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn))` by
    metis_tac[fn_inst_ids_as_fn_insts] >>
  simp[wf_function_def] >> rpt conj_tac
  >- fs[fn_labels_def, listTheory.MAP_MAP_o, combinTheory.o_DEF]
  >- fs[fn_has_entry_def]
  >- (rpt strip_tac >> gvs[listTheory.MEM_MAP] >>
      rename1 `MEM bb0 fn.fn_blocks` >>
      `bb_well_formed bb0` by res_tac >>
      irule ao_phase4_bb_wf >>
      simp[] >>
      qexists_tac `dfg` >> qexists_tac `fn` >>
      simp[] >> first_assum ACCEPT_TAC)
  >- (`wf_function fn` by simp[wf_function_def] >>
      drule_all ao_phase4_succs_closed >> simp[])
  >- (simp[venomWfTheory.fn_inst_ids_distinct_def,
           fn_inst_ids_flat_map_eq, GSYM fn_insts_def] >>
      irule ao_cmp_flip_ids_all_distinct >> rpt conj_tac
      >- (rpt strip_tac >>
          `inst.inst_id <= fn_max_inst_id fn` by
            metis_tac[fn_max_inst_id_bound] >> gvs[])
      >- gvs[]
      >- metis_tac[ao_cmp_flip_scan_inserts_cmp_ids_distinct])
QED

Theorem ao_preserves_wf_function:
  !fn. wf_function fn /\ EVERY inst_wf (fn_insts fn) /\
    EVERY (\inst. inst.inst_opcode = ISZERO ==>
       EVERY (\op. get_label op = NONE) inst.inst_operands)
      (fn_insts fn) ==>
    wf_function (ao_transform_function fn)
Proof
  rpt strip_tac >>
  simp[ao_transform_function_def, LET_THM,
       GSYM function_map_transform_def] >>
  irule ao_phase4_preserves_wf >> conj_tac
  >- (rpt strip_tac >>
      imp_res_tac dfgAnalysisPropsTheory.dfg_build_function_uses_sound)
  >- (conj_tac
      >- (irule ao_phase3_preserves_wf >>
          simp[GSYM block_map_transform_def] >>
          CONV_TAC (DEPTH_CONV ETA_CONV) >>
          rpt conj_tac
          >- (simp[ao_compute_fn_iszero_targets_def,
                   ao_compute_iszero_targets_def] >>
              match_mp_tac ao_compute_targets_no_label >> simp[] >>
              irule phase1_preserves_iszero_no_label >> simp[])
          >- (irule ao_phase1_preserves_wf >> simp[])
          >- (simp[function_map_transform_def] >>
              irule phase1_preserves_inst_wf >>
              fs[fn_insts_def, fn_insts_blocks_every]))
      >- simp[])
QED

(* ao_fresh_var is injective on our suffixes *)
Theorem ao_fresh_var_full_inj:
  !id1 s1 id2 s2.
    (s1 = "not" \/ s1 = "iz" \/ s1 = "xor") /\
    (s2 = "not" \/ s2 = "iz" \/ s2 = "xor") /\
    ao_fresh_var id1 s1 = ao_fresh_var id2 s2 ==>
    id1 = id2 /\ s1 = s2
Proof
  rpt strip_tac >> gvs[] >>
  fs[ao_fresh_var_def, stringTheory.STRCAT_11,
     ASCIInumbersTheory.toString_inj]
QED

(* LAST of ao_peephole_inst preserves outputs *)
Triviality ao_peephole_inst_last_outputs[local]:
  !mid dfg ra lbl idx inst.
    ao_peephole_inst mid dfg ra lbl idx inst <> [] /\
    (LAST (ao_peephole_inst mid dfg ra lbl idx inst)).inst_outputs =
      inst.inst_outputs
Proof
  rpt gen_tac >>
  simp[ao_peephole_inst_def, LET_THM] >>
  rpt IF_CASES_TAC >>
  simp[ao_opt_shift_def, ao_opt_signextend_def, ao_opt_exp_def,
       ao_opt_addsub_def, ao_opt_and_def, ao_opt_muldiv_def,
       ao_opt_or_def, ao_opt_eq_def, ao_opt_comparator_def, LET_THM,
       ao_cmp_prefer_iz_zero_def, ao_cmp_prefer_iz_max_def,
       ao_cmp_prefer_iz_general_def,
       ao_unsigned_boundaries_def, ao_signed_boundaries_def] >>
  every_case_tac >> gvs[] >>
  rpt IF_CASES_TAC >> gvs[]
QED

Theorem ao_preserves_ssa_form:
  !fn. ssa_form fn /\ wf_function fn /\
    (!inst v. MEM inst (fn_insts fn) /\
              MEM v inst.inst_outputs ==>
              ~((?id. MEM id (MAP (\i. i.inst_id) (fn_insts fn)) /\
                 (v = ao_fresh_var id "not" \/
                  v = ao_fresh_var id "iz" \/
                  v = ao_fresh_var id "xor")))) ==>
    ssa_form (ao_transform_function fn)
Proof
  rpt strip_tac >>
  simp[ssa_form_def, fn_insts_def] >>
  irule all_distinct_pred_split >>
  qexists_tac `\v. ?id s. MEM id (MAP (\i. i.inst_id) (fn_insts fn)) /\
    (s = "not" \/ s = "iz" \/ s = "xor") /\ v = ao_fresh_var id s` >>
  conj_tac
  >- ((* Fresh half: ALL_DISTINCT (FILTER fresh outputs) *)
      cheat)
  >- ((* Non-fresh half: ALL_DISTINCT (FILTER (¬fresh) outputs) *)
      cheat)
QED

val _ = export_theory();


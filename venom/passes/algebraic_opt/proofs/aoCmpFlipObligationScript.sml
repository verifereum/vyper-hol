(* Obligation: cmp_flip preserves block execution up to dead variables. *)
Theory aoCmpFlipObligation
Ancestors
  algebraicOptDefs algebraicOptCmpFlipSim
  analysisSimDefs
  stateEquiv stateEquivProps execEquivProps passSimulationProps
  passSharedDefs venomInstProps
  venomExecSemantics venomState venomInst venomWf
Libs
  pairLib BasicProvers

(* ===== Helper: NULL flips => scan = ([],[],[]) ===== *)
(* Mechanical case analysis on ao_cmp_flip_scan_def.
   True because flips, removes, inserts only grow together. *)

Theorem scan_null_triple[local]:
  !dfg insts. NULL (FST (ao_cmp_flip_scan dfg insts)) ==>
              ao_cmp_flip_scan dfg insts = ([],[],[])
Proof
  Induct_on `insts` >> simp[ao_cmp_flip_scan_def] >>
  rpt gen_tac >> simp[Once ao_cmp_flip_scan_def, LET_THM] >>
  pairarg_tac >> simp[] >>
  IF_CASES_TAC >> simp[]
  >- (* ~is_comparator: passthrough *)
     (strip_tac >>
      first_x_assum (qspec_then `dfg` mp_tac) >> gvs[listTheory.NULL_EQ])
  >> (* is_comparator: case analysis *)
  every_case_tac >>
  rpt (pairarg_tac >> simp[]) >>
  rpt IF_CASES_TAC >> simp[] >>
  rpt strip_tac >> gvs[listTheory.NULL_EQ] >>
  TRY (first_x_assum (qspec_then `dfg` mp_tac) >> gvs[listTheory.NULL_EQ])
QED

Triviality dead_empty_when_null[local]:
  !dfg fn1.
    NULL (FST (ao_cmp_flip_scan dfg (fn_insts fn1))) ==>
    ao_cmp_flip_dead_vars dfg fn1 = {}
Proof
  rpt strip_tac >>
  `ao_cmp_flip_scan dfg (fn_insts fn1) = ([],[],[])` by
    metis_tac[scan_null_triple] >>
  simp[ao_cmp_flip_dead_vars_def, LET_THM]
QED

(* ===== Infrastructure for non-NULL case ===== *)

(* run_insts on appended lists *)
Triviality run_insts_append[local]:
  !l1 l2 fuel ctx s.
    run_insts fuel ctx (l1 ++ l2) s =
    case run_insts fuel ctx l1 s of
      OK s' => run_insts fuel ctx l2 s'
    | Halt v => Halt v
    | Abort a v => Abort a v
    | IntRet v1 v2 => IntRet v1 v2
    | Error e => Error e
Proof
  Induct >- simp[run_insts_def] >>
  rpt gen_tac >> simp[run_insts_def] >>
  Cases_on `step_inst fuel ctx h s` >> simp[]
QED

(* run_insts on singleton = step_inst *)
Triviality run_insts_singleton[local]:
  !fuel ctx x s. run_insts fuel ctx [x] s = step_inst fuel ctx x s
Proof
  simp[run_insts_def] >> rpt gen_tac >>
  Cases_on `step_inst fuel ctx x s` >> simp[run_insts_def]
QED

(* ===== Iszero invariant for flip-remove pairing ===== *)

(* After the flip instruction executes, the comparator output in s2
   is the iszero of the value in s1. This is needed by the remove step
   (ISZERO → ASSIGN) to show the ASSIGN produces the same value as ISZERO. *)
Definition cmp_flip_iszero_inv_def:
  cmp_flip_iszero_inv flips all_insts s1 s2 <=>
    !inst out v1 v2.
      MEM inst all_insts /\
      ALOOKUP flips inst.inst_id <> NONE /\
      MEM out inst.inst_outputs /\
      lookup_var out s1 = SOME v1 /\
      lookup_var out s2 = SOME v2 ==>
      v2 = bool_to_word (v1 = 0w)
End

(* ===== Per-instruction simulation: case helpers ===== *)

(* Iszero_inv maintenance helper: step_inst on non-INVOKE, non-terminator
   preserves the invariant if the instruction's outputs don't overlap
   other flip instruction outputs. *)
Triviality iszero_inv_frame[local]:
  !flips all_insts inst fuel ctx s1 s2 s1' s2'.
    cmp_flip_iszero_inv flips all_insts s1 s2 /\
    ~is_terminator inst.inst_opcode /\
    step_inst fuel ctx inst s1 = OK s1' /\
    (!fi out. MEM fi all_insts /\ ALOOKUP flips fi.inst_id <> NONE /\
             MEM out fi.inst_outputs /\ ~MEM out inst.inst_outputs ==>
             lookup_var out s1' = lookup_var out s1) /\
    (!fi out. MEM fi all_insts /\ ALOOKUP flips fi.inst_id <> NONE /\
             MEM out fi.inst_outputs /\ ~MEM out inst.inst_outputs ==>
             lookup_var out s2' = lookup_var out s2) /\
    (!fi out v1' v2'. MEM fi all_insts /\ ALOOKUP flips fi.inst_id <> NONE /\
             MEM out fi.inst_outputs /\ MEM out inst.inst_outputs /\
             lookup_var out s1' = SOME v1' /\
             lookup_var out s2' = SOME v2' ==>
             v2' = bool_to_word (v1' = 0w))
    ==>
    cmp_flip_iszero_inv flips all_insts s1' s2'
Proof
  rw[cmp_flip_iszero_inv_def] >> rpt strip_tac >>
  Cases_on `MEM out inst.inst_outputs`
  >- (first_x_assum irule >> metis_tac[])
  >> `lookup_var out s1' = lookup_var out s1` by metis_tac[] >>
  `lookup_var out s2' = lookup_var out s2` by metis_tac[] >>
  gvs[] >> metis_tac[]
QED

(* Case 1: Unchanged instruction — same inst on both sides *)
Triviality per_inst_unchanged[local]:
  !dead flips all_insts inst fuel ctx s1 s2.
    state_equiv dead s1 s2 /\
    cmp_flip_iszero_inv flips all_insts s1 s2 /\
    inst.inst_opcode <> INVOKE /\
    ~is_terminator inst.inst_opcode /\
    ALOOKUP flips inst.inst_id = NONE /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN dead) /\
    (!fi. MEM fi all_insts /\ fi.inst_id <> inst.inst_id /\
          ALOOKUP flips fi.inst_id <> NONE ==>
          !out. MEM out fi.inst_outputs ==> ~MEM out inst.inst_outputs)
    ==>
    case (step_inst fuel ctx inst s1,
          step_inst fuel ctx inst s2) of
      (OK s1', OK s2') =>
        state_equiv dead s1' s2' /\
        cmp_flip_iszero_inv flips all_insts s1' s2'
    | (OK _, _) => F
    | (_, OK _) => F
    | _ => T
Proof
  rpt strip_tac >>
  `result_equiv dead (step_inst fuel ctx inst s1)
                     (step_inst fuel ctx inst s2)` by
    (irule step_inst_result_equiv >> simp[]) >>
  Cases_on `step_inst fuel ctx inst s1` >>
  Cases_on `step_inst fuel ctx inst s2` >>
  gvs[result_equiv_def] >>
  TRY (simp[] >> NO_TAC) >>
  irule iszero_inv_frame >>
  qexistsl_tac [`ctx`, `fuel`, `inst`, `s1`, `s2`] >> simp[] >>
  rpt conj_tac >> rpt strip_tac
  >- (* Overlap case: impossible *)
     (`fi.inst_id <> inst.inst_id` by (CCONTR_TAC >> gvs[]) >>
      metis_tac[])
  >- (irule step_preserves_non_output_vars >> metis_tac[])
  >> irule step_preserves_non_output_vars >> metis_tac[]
QED

(* update_var on dead variable preserves state_equiv *)
Triviality update_dead_var_state_equiv[local]:
  !dead x v1 v2 s1 s2.
    state_equiv dead s1 s2 /\ x IN dead ==>
    state_equiv dead (update_var x v1 s1) (update_var x v2 s2)
Proof
  rw[state_equiv_def, execution_equiv_def, update_var_def, lookup_var_def] >>
  simp[finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> IF_CASES_TAC >> gvs[]
QED

(* Instructions not in any scan list are unchanged *)
Triviality apply_inst_unchanged[local]:
  !mid flips removes inserts inst.
    ALOOKUP flips inst.inst_id = NONE /\
    ~MEM inst.inst_id removes /\
    ALOOKUP inserts inst.inst_id = NONE ==>
    ao_cmp_flip_apply_inst mid flips removes inserts inst = [inst]
Proof
  simp[ao_cmp_flip_apply_inst_def]
QED

(* Case 2: Flip — flipped comparator output = iszero(original) *)
Triviality per_inst_flip[local]:
  !dead flips all_insts inst fuel ctx s1 s2 w out_var x2.
    state_equiv dead s1 s2 /\
    cmp_flip_iszero_inv flips all_insts s1 s2 /\
    MEM inst all_insts /\
    inst.inst_opcode <> INVOKE /\
    ~is_terminator inst.inst_opcode /\
    is_comparator inst.inst_opcode /\
    inst.inst_operands = [x2; Lit w] /\
    inst.inst_outputs = [out_var] /\
    out_var IN dead /\
    (!x. MEM (Var x) [x2; Lit w] ==> x NOTIN dead) /\
    ALOOKUP flips inst.inst_id <> NONE /\
    (inst.inst_opcode = GT ==> w <> 0w - 1w) /\
    (inst.inst_opcode = LT ==> w <> 0w) /\
    (inst.inst_opcode = SGT ==> w <> i2w INT256_MAX) /\
    (inst.inst_opcode = SLT ==> w <> i2w INT256_MIN) /\
    (!fi. MEM fi all_insts /\ fi.inst_id <> inst.inst_id /\
          ALOOKUP flips fi.inst_id <> NONE ==>
          !out. MEM out fi.inst_outputs ==> out <> out_var)
    ==>
    let new_w = if inst.inst_opcode = GT \/ inst.inst_opcode = SGT
                then w + 1w else w - 1w in
    let flipped = inst with
      <| inst_opcode := flip_comparison_opcode inst.inst_opcode;
         inst_operands := [x2; Lit new_w] |> in
    case (step_inst fuel ctx inst s1,
          step_inst fuel ctx flipped s2) of
      (OK s1', OK s2') =>
        state_equiv dead s1' s2' /\
        cmp_flip_iszero_inv flips all_insts s1' s2'
    | (OK _, _) => F
    | (_, OK _) => F
    | _ => T
Proof
  rpt strip_tac >> simp[LET_THM] >>
  `step_inst fuel ctx inst s1 = step_inst_base inst s1` by
    (irule step_inst_non_invoke >> simp[]) >>
  qabbrev_tac `flipped = inst with
    <| inst_opcode := flip_comparison_opcode inst.inst_opcode;
       inst_operands := [x2; Lit (if inst.inst_opcode = GT \/
         inst.inst_opcode = SGT then w + 1w else w - 1w)] |>` >>
  `flipped.inst_opcode <> INVOKE` by
    (simp[Abbr`flipped`] >>
     gvs[is_comparator_def] >> simp[flip_comparison_opcode_def]) >>
  `step_inst fuel ctx flipped s2 = step_inst_base flipped s2` by
    (irule step_inst_non_invoke >> simp[]) >>
  gvs[] >>
  `eval_operand x2 s1 = eval_operand x2 s2` by
    (Cases_on `x2` >> simp[eval_operand_def] >>
     rename1 `MEM (Var vn) _` >>
     `vn NOTIN dead` by (first_x_assum irule >> simp[]) >>
     gvs[state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  Cases_on `eval_operand x2 s1` >> gvs[]
  >- ( (* NONE: both fail *)
    simp[Abbr`flipped`] >>
    gvs[is_comparator_def, step_inst_base_def, eval_operand_def,
        exec_pure2_def])
  >> (* SOME v1: operand evaluates *)
  rename1 `eval_operand x2 s1 = SOME v1` >>
  gvs[is_comparator_def] >>
  gvs[step_inst_base_def, eval_operand_def, exec_pure2_def,
      Abbr`flipped`, flip_comparison_opcode_def,
      update_var_def] >> (
  conj_tac
  >- (irule update_dead_var_state_equiv >> simp[])
  >> rw[cmp_flip_iszero_inv_def] >> rpt strip_tac >>
  Cases_on `out = out_var`
  >- (gvs[lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE,
          cmp_flip_iszero_equiv_gt, cmp_flip_iszero_equiv_lt,
          cmp_flip_iszero_equiv_sgt, cmp_flip_iszero_equiv_slt])
  >> `lookup_var out (s1 with vs_vars := s1.vs_vars |+ (out_var, _)) =
      lookup_var out s1` by
       simp[lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
     `lookup_var out (s2 with vs_vars := s2.vs_vars |+ (out_var, _)) =
      lookup_var out s2` by
       simp[lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
     gvs[cmp_flip_iszero_inv_def] >>
     first_x_assum irule >> simp[] >>
     metis_tac[])
QED

(* Case 3: Remove — ISZERO replaced by ASSIGN.
   The iszero invariant ensures the flipped output in s2 already equals
   iszero(original output in s1), so ASSIGN copies the same value as
   ISZERO would produce. *)
Triviality per_inst_remove[local]:
  !dead flips all_insts inst fuel ctx s1 s2 cmp_out iz_out fi v0.
    state_equiv dead s1 s2 /\
    cmp_flip_iszero_inv flips all_insts s1 s2 /\
    MEM inst all_insts /\
    inst.inst_opcode = ISZERO /\
    inst.inst_operands = [Var cmp_out] /\
    inst.inst_outputs = [iz_out] /\
    ALOOKUP flips inst.inst_id = NONE /\
    MEM fi all_insts /\
    ALOOKUP flips fi.inst_id <> NONE /\
    MEM cmp_out fi.inst_outputs /\
    lookup_var cmp_out s1 = SOME v0 /\
    (?v0'. lookup_var cmp_out s2 = SOME v0') /\
    (!fi'. MEM fi' all_insts /\ fi'.inst_id <> inst.inst_id /\
           ALOOKUP flips fi'.inst_id <> NONE ==>
           !out. MEM out fi'.inst_outputs ==> out <> iz_out)
    ==>
    case (step_inst fuel ctx inst s1,
          step_inst fuel ctx (inst with inst_opcode := ASSIGN) s2) of
      (OK s1', OK s2') =>
        state_equiv dead s1' s2' /\
        cmp_flip_iszero_inv flips all_insts s1' s2'
    | (OK _, _) => F
    | (_, OK _) => F
    | _ => T
Proof
  rpt strip_tac >>
  `step_inst fuel ctx inst s1 = step_inst_base inst s1` by
    (irule step_inst_non_invoke >> gvs[]) >>
  `step_inst fuel ctx (inst with inst_opcode := ASSIGN) s2 =
   step_inst_base (inst with inst_opcode := ASSIGN) s2` by
    (irule step_inst_non_invoke >> simp[]) >>
  `v0' = bool_to_word (v0 = 0w)` by (
    qpat_x_assum `cmp_flip_iszero_inv _ _ _ _` mp_tac >>
    simp_tac std_ss [cmp_flip_iszero_inv_def] >>
    disch_then (qspecl_then [`fi`, `cmp_out`, `v0`, `v0'`] mp_tac) >>
    simp[]) >>
  gvs[step_inst_base_def, exec_pure1_def, eval_operand_def] >>
  conj_tac
  >- (irule update_var_preserves >> simp[])
  >> rw[cmp_flip_iszero_inv_def] >> rpt strip_tac >>
  rename1 `MEM fi' all_insts` >>
  Cases_on `out = iz_out`
  >- (`fi'.inst_id <> inst.inst_id` by (CCONTR_TAC >> gvs[]) >>
      res_tac >> gvs[])
  >> `lookup_var out s1 = SOME v1` by
       (qpat_x_assum `lookup_var out (update_var _ _ s1) = _` mp_tac >>
        simp[update_var_def, lookup_var_def,
             finite_mapTheory.FLOOKUP_UPDATE]) >>
     `lookup_var out s2 = SOME v2` by
       (qpat_x_assum `lookup_var out (update_var _ _ s2) = _` mp_tac >>
        simp[update_var_def, lookup_var_def,
             finite_mapTheory.FLOOKUP_UPDATE]) >>
     qpat_x_assum `cmp_flip_iszero_inv _ _ _ _` mp_tac >>
     simp_tac std_ss [cmp_flip_iszero_inv_def] >>
     disch_then (qspecl_then [`fi'`, `out`, `v1`, `v2`] mp_tac) >>
     simp[]
QED

(* Per-instruction simulation with iszero invariant.
   Relates step_inst on original vs run_insts on transformed,
   maintaining both state_equiv and the iszero invariant. *)
Triviality per_inst_sim[local]:
  !dead mid flips removes inserts inst all_insts fuel ctx s1 s2.
    state_equiv dead s1 s2 /\
    cmp_flip_iszero_inv flips all_insts s1 s2 /\
    MEM inst all_insts /\
    inst.inst_opcode <> INVOKE /\
    ~is_terminator inst.inst_opcode /\
    (* Unchanged/flip: operands not dead *)
    (~MEM inst.inst_id removes /\
     ALOOKUP inserts inst.inst_id = NONE ==>
     !x. MEM (Var x) inst.inst_operands ==> x NOTIN dead) /\
    (* Flip outputs are dead *)
    (!fi out. MEM fi all_insts /\ ALOOKUP flips fi.inst_id <> NONE /\
             MEM out fi.inst_outputs ==> out IN dead) /\
    (* Output disjointness for iszero_inv maintenance *)
    (!fi. MEM fi all_insts /\ fi.inst_id <> inst.inst_id /\
          ALOOKUP flips fi.inst_id <> NONE ==>
          !out. MEM out fi.inst_outputs ==> ~MEM out inst.inst_outputs) /\
    (* Scan disjointness: flips don't overlap with removes/inserts *)
    (!id. ALOOKUP flips id <> NONE ==>
     ~MEM id removes /\ ALOOKUP inserts id = NONE) /\
    (* Flip structural info *)
    (!new_opc new_w orig_op1.
       ALOOKUP flips inst.inst_id = SOME (new_opc, new_w, orig_op1) ==>
       ?w out_var.
         is_comparator inst.inst_opcode /\
         inst.inst_operands = [orig_op1; Lit w] /\
         inst.inst_outputs = [out_var] /\
         new_opc = flip_comparison_opcode inst.inst_opcode /\
         new_w = (if inst.inst_opcode = GT \/ inst.inst_opcode = SGT
                  then w + 1w else w - 1w) /\
         (inst.inst_opcode = GT ==> w <> 0w - 1w) /\
         (inst.inst_opcode = LT ==> w <> 0w) /\
         (inst.inst_opcode = SGT ==> w <> i2w INT256_MAX) /\
         (inst.inst_opcode = SLT ==> w <> i2w INT256_MIN))
    ==>
    case (step_inst fuel ctx inst s1,
          run_insts fuel ctx
            (ao_cmp_flip_apply_inst mid flips removes inserts inst) s2) of
      (OK s1', OK s2') =>
        state_equiv dead s1' s2' /\
        cmp_flip_iszero_inv flips all_insts s1' s2'
    | (OK _, _) => F
    | (_, OK _) => F
    | _ => T
Proof
  rpt strip_tac >>
  Cases_on `ALOOKUP flips inst.inst_id`
  >- ( (* NONE: not flipped *)
    Cases_on `MEM inst.inst_id removes`
    >- ( (* Remove case *)
      `ao_cmp_flip_apply_inst mid flips removes inserts inst =
       [inst with inst_opcode := ASSIGN]` by
        simp[ao_cmp_flip_apply_inst_def] >>
      simp[run_insts_singleton] >>
      cheat)
    >> Cases_on `ALOOKUP inserts inst.inst_id`
    >- ( (* NONE: Unchanged *)
      `ao_cmp_flip_apply_inst mid flips removes inserts inst = [inst]` by
        (irule apply_inst_unchanged >> simp[]) >>
      pop_assum (fn th => REWRITE_TAC [th]) >>
      REWRITE_TAC [run_insts_singleton] >>
      irule per_inst_unchanged >> gvs[] >> metis_tac[])
    >> (* SOME: Insert case *)
    PairCases_on `x` >> cheat)
  >> (* Flip case *)
  PairCases_on `x` >>
  first_x_assum (qspecl_then [`x0`, `x1`, `x2`] mp_tac) >> simp[] >>
  strip_tac >> gvs[] >>
  `~MEM inst.inst_id removes /\ ALOOKUP inserts inst.inst_id = NONE` by
    (first_x_assum (qspec_then `inst.inst_id` mp_tac) >> simp[]) >>
  `ao_cmp_flip_apply_inst mid flips removes inserts inst =
   [inst with <| inst_opcode := flip_comparison_opcode inst.inst_opcode;
                 inst_operands := [x2; Lit (if inst.inst_opcode = GT \/
                   inst.inst_opcode = SGT then w + 1w else w - 1w)] |>]` by
    simp[ao_cmp_flip_apply_inst_def] >>
  simp[run_insts_singleton] >>
  irule (SIMP_RULE (srw_ss()) [LET_THM] per_inst_flip) >> gvs[] >>
  metis_tac[]
QED

(* Body simulation: run_insts on original body vs FLAT MAP transformed *)
Triviality body_sim[local]:
  !body_insts mid flips removes inserts dead all_insts fuel ctx s1 s2.
    state_equiv dead s1 s2 /\
    cmp_flip_iszero_inv flips all_insts s1 s2 /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) body_insts /\
    (!inst. MEM inst body_insts ==> MEM inst all_insts) /\
    (!inst. MEM inst body_insts ==>
      ~MEM inst.inst_id removes /\
      ALOOKUP inserts inst.inst_id = NONE ==>
      !x. MEM (Var x) inst.inst_operands ==> x NOTIN dead) /\
    (!fi out. MEM fi all_insts /\ ALOOKUP flips fi.inst_id <> NONE /\
             MEM out fi.inst_outputs ==> out IN dead) /\
    (!inst fi. MEM inst body_insts /\
      MEM fi all_insts /\ fi.inst_id <> inst.inst_id /\
      ALOOKUP flips fi.inst_id <> NONE ==>
      !out. MEM out fi.inst_outputs ==> ~MEM out inst.inst_outputs) /\
    (!id. ALOOKUP flips id <> NONE ==>
     ~MEM id removes /\ ALOOKUP inserts id = NONE) /\
    (!inst new_opc new_w orig_op1.
       MEM inst body_insts /\
       ALOOKUP flips inst.inst_id = SOME (new_opc, new_w, orig_op1) ==>
       ?w out_var.
         is_comparator inst.inst_opcode /\
         inst.inst_operands = [orig_op1; Lit w] /\
         inst.inst_outputs = [out_var] /\
         new_opc = flip_comparison_opcode inst.inst_opcode /\
         new_w = (if inst.inst_opcode = GT \/ inst.inst_opcode = SGT
                  then w + 1w else w - 1w) /\
         (inst.inst_opcode = GT ==> w <> 0w - 1w) /\
         (inst.inst_opcode = LT ==> w <> 0w) /\
         (inst.inst_opcode = SGT ==> w <> i2w INT256_MAX) /\
         (inst.inst_opcode = SLT ==> w <> i2w INT256_MIN))
    ==>
    case (run_insts fuel ctx body_insts s1,
          run_insts fuel ctx
            (FLAT (MAP (ao_cmp_flip_apply_inst mid flips removes inserts)
                       body_insts)) s2) of
      (OK s1', OK s2') =>
        state_equiv dead s1' s2' /\
        cmp_flip_iszero_inv flips all_insts s1' s2'
    | (OK _, _) => F
    | (_, OK _) => F
    | _ => T
Proof
  Induct >- simp[run_insts_def]
  >> rpt gen_tac >> strip_tac >>
  simp[run_insts_def, run_insts_append] >>
  `case (step_inst fuel ctx h s1,
         run_insts fuel ctx
           (ao_cmp_flip_apply_inst mid flips removes inserts h) s2) of
     (OK s1', OK s2') =>
       state_equiv dead s1' s2' /\
       cmp_flip_iszero_inv flips all_insts s1' s2'
   | (OK _, _) => F
   | (_, OK _) => F
   | _ => T` by
    (irule per_inst_sim >> gvs[] >> metis_tac[]) >>
  Cases_on `step_inst fuel ctx h s1` >>
  Cases_on `run_insts fuel ctx
    (ao_cmp_flip_apply_inst mid flips removes inserts h) s2` >>
  gvs[] >>
  first_x_assum irule >> gvs[] >> metis_tac[]
QED

(* Block structure: relate bb' to bb1 via ao_cmp_flip_function *)
Triviality cmp_flip_block_structure[local]:
  !mid dfg fn1 lbl bb1 bb' flips removes inserts.
    ~NULL flips /\
    ao_cmp_flip_scan dfg (fn_insts fn1) = (flips, removes, inserts) /\
    lookup_block lbl fn1.fn_blocks = SOME bb1 /\
    lookup_block lbl (ao_cmp_flip_function mid dfg fn1).fn_blocks = SOME bb'
    ==>
    bb'.bb_instructions =
      FLAT (MAP (ao_cmp_flip_apply_inst mid flips removes inserts)
                bb1.bb_instructions) /\
    bb'.bb_label = bb1.bb_label
Proof
  rpt strip_tac >>
  gvs[ao_cmp_flip_function_def, LET_THM] >>
  qabbrev_tac `bt = \bb. bb with bb_instructions :=
    FLAT (MAP (ao_cmp_flip_apply_inst mid flips removes inserts)
              bb.bb_instructions)` >>
  `!bb. (bt bb).bb_label = bb.bb_label` by simp[Abbr `bt`] >>
  `bb' = bt bb1` by
    (`lookup_block lbl (MAP bt fn1.fn_blocks) =
      OPTION_MAP bt (lookup_block lbl fn1.fn_blocks)` by
       metis_tac[lookup_block_map] >>
     gvs[]) >>
  gvs[Abbr `bt`]
QED

(* ===== Scan step characterization ===== *)

(* Each step of the scan either passes through or prepends to flips/removes/inserts.
   This lemma captures what IDs can appear in the scan output. *)
Triviality scan_step_flips_subset[local]:
  !dfg h rest flips removes inserts flips' removes' inserts'.
    ao_cmp_flip_scan dfg rest = (flips', removes', inserts') /\
    ao_cmp_flip_scan dfg (h :: rest) = (flips, removes, inserts) ==>
    flips = flips' \/
    (?opc w op1. flips = (h.inst_id, opc, w, op1) :: flips' /\
                 is_comparator h.inst_opcode)
Proof
  rpt gen_tac >>
  simp[Once ao_cmp_flip_scan_def, LET_THM] >>
  pairarg_tac >> simp[] >>
  IF_CASES_TAC >> simp[]
  >- (strip_tac >> gvs[])
  >> every_case_tac >>
  rpt (pairarg_tac >> simp[]) >>
  rpt IF_CASES_TAC >> simp[] >>
  rpt strip_tac >> gvs[]
QED

Triviality scan_step_removes_subset[local]:
  !dfg h rest flips removes inserts flips' removes' inserts'.
    ao_cmp_flip_scan dfg rest = (flips', removes', inserts') /\
    ao_cmp_flip_scan dfg (h :: rest) = (flips, removes, inserts) ==>
    removes = removes' \/
    (?v ui. removes = ui.inst_id :: removes' /\
            MEM ui (dfg_get_uses dfg v) /\ ui.inst_opcode = ISZERO)
Proof
  rpt gen_tac >>
  simp[Once ao_cmp_flip_scan_def, LET_THM] >>
  pairarg_tac >> simp[] >>
  IF_CASES_TAC >> simp[]
  >- (strip_tac >> gvs[])
  >> every_case_tac >>
  rpt (pairarg_tac >> simp[]) >>
  rpt IF_CASES_TAC >> simp[] >>
  rpt strip_tac >>
  simp_tac std_ss [] >>
  TRY (gvs[] >> NO_TAC) >>
  DISJ2_TAC >>
  qexists_tac `h'` >> qexists_tac `HD (dfg_get_uses dfg h')` >>
  gvs[] >>
  `LENGTH (dfg_get_uses dfg h') = 1` by
    (CCONTR_TAC >> fs[]) >>
  Cases_on `dfg_get_uses dfg h'` >> fs[] >>
  Cases_on `t` >> fs[]
QED

Triviality scan_step_inserts_subset[local]:
  !dfg h rest flips removes inserts flips' removes' inserts'.
    ao_cmp_flip_scan dfg rest = (flips', removes', inserts') /\
    ao_cmp_flip_scan dfg (h :: rest) = (flips, removes, inserts) ==>
    inserts = inserts' \/
    (?v ui.
       inserts = (ui.inst_id, v, ao_fresh_var h.inst_id "iz",
                  h.inst_id) :: inserts' /\
       MEM ui (dfg_get_uses dfg v) /\ ui.inst_opcode = ASSERT)
Proof
  rpt gen_tac >>
  simp[Once ao_cmp_flip_scan_def, LET_THM] >>
  pairarg_tac >> simp[] >>
  IF_CASES_TAC >> simp[]
  >- (strip_tac >> gvs[])
  >> every_case_tac >>
  rpt (pairarg_tac >> simp[]) >>
  rpt IF_CASES_TAC >> simp[] >>
  rpt strip_tac >>
  simp_tac std_ss [] >>
  TRY (gvs[] >> NO_TAC) >>
  DISJ2_TAC >>
  qexists_tac `h'` >> qexists_tac `HD (dfg_get_uses dfg h')` >>
  gvs[] >>
  `LENGTH (dfg_get_uses dfg h') = 1` by
    (CCONTR_TAC >> fs[]) >>
  Cases_on `dfg_get_uses dfg h'` >> fs[] >>
  Cases_on `t` >> fs[]
QED

(* Flips keys come from comparator instructions in insts *)
Triviality scan_flips_are_comparators[local]:
  !dfg insts flips removes inserts id.
    ao_cmp_flip_scan dfg insts = (flips, removes, inserts) /\
    MEM id (MAP FST flips) ==>
    ?i. MEM i insts /\ i.inst_id = id /\ is_comparator i.inst_opcode
Proof
  Induct_on `insts`
  >- simp[ao_cmp_flip_scan_def]
  >> rpt gen_tac >> strip_tac >>
  Cases_on `ao_cmp_flip_scan dfg insts` >> Cases_on `r` >>
  rename1 `_ = (flips', removes', inserts')` >>
  `flips = flips' \/
   (?opc w op1. flips = (h.inst_id, opc, w, op1) :: flips' /\
                is_comparator h.inst_opcode)` by
    metis_tac[scan_step_flips_subset] >>
  gvs[]
  >- (first_x_assum drule_all >> metis_tac[])
  >> metis_tac[]
QED

(* Removes IDs come from ISZERO instructions in dfg_get_uses *)
Triviality scan_removes_are_iszero[local]:
  !dfg insts flips removes inserts id.
    ao_cmp_flip_scan dfg insts = (flips, removes, inserts) /\
    MEM id removes ==>
    ?v ui. MEM ui (dfg_get_uses dfg v) /\ ui.inst_id = id /\
           ui.inst_opcode = ISZERO
Proof
  Induct_on `insts`
  >- simp[ao_cmp_flip_scan_def]
  >> rpt gen_tac >> strip_tac >>
  Cases_on `ao_cmp_flip_scan dfg insts` >> Cases_on `r` >>
  rename1 `_ = (flips', removes', inserts')` >>
  `removes = removes' \/
   (?v ui. removes = ui.inst_id :: removes' /\
           MEM ui (dfg_get_uses dfg v) /\ ui.inst_opcode = ISZERO)` by
    metis_tac[scan_step_removes_subset] >>
  gvs[] >> metis_tac[]
QED

(* Inserts keys come from ASSERT instructions in dfg_get_uses *)
Triviality scan_inserts_are_assert[local]:
  !dfg insts flips removes inserts id.
    ao_cmp_flip_scan dfg insts = (flips, removes, inserts) /\
    MEM id (MAP FST inserts) ==>
    ?v ui. MEM ui (dfg_get_uses dfg v) /\ ui.inst_id = id /\
           ui.inst_opcode = ASSERT
Proof
  Induct_on `insts`
  >- simp[ao_cmp_flip_scan_def]
  >> rpt gen_tac >> strip_tac >>
  Cases_on `ao_cmp_flip_scan dfg insts` >> Cases_on `r` >>
  rename1 `_ = (flips', removes', inserts')` >>
  `inserts = inserts' \/
   (?v ui. inserts = (ui.inst_id, v, ao_fresh_var h.inst_id "iz",
                      h.inst_id) :: inserts' /\
           MEM ui (dfg_get_uses dfg v) /\ ui.inst_opcode = ASSERT)` by
    metis_tac[scan_step_inserts_subset] >>
  gvs[] >> metis_tac[]
QED

(* Single step: full structural info when a flip entry is prepended *)
Triviality scan_step_flip_info[local]:
  !dfg h rest flips removes inserts flips' removes' inserts'.
    ao_cmp_flip_scan dfg rest = (flips', removes', inserts') /\
    ao_cmp_flip_scan dfg (h :: rest) = (flips, removes, inserts) /\
    flips <> flips' ==>
    ?w op1 out_var.
      is_comparator h.inst_opcode /\
      h.inst_operands = [op1; Lit w] /\
      h.inst_outputs = [out_var] /\
      flips = (h.inst_id, flip_comparison_opcode h.inst_opcode,
               (if h.inst_opcode = GT \/ h.inst_opcode = SGT
                then w + 1w else w - 1w), op1) :: flips' /\
      (h.inst_opcode = GT ==> w <> 0w - 1w) /\
      (h.inst_opcode = LT ==> w <> 0w) /\
      (h.inst_opcode = SGT ==> w <> i2w INT256_MAX) /\
      (h.inst_opcode = SLT ==> w <> i2w INT256_MIN)
Proof
  rpt gen_tac >>
  simp[Once ao_cmp_flip_scan_def, LET_THM] >>
  pairarg_tac >> simp[] >>
  reverse IF_CASES_TAC >> simp[]
  >- (
    every_case_tac >>
    rpt (pairarg_tac >> simp[]) >>
    rpt IF_CASES_TAC >> simp[] >>
    rpt strip_tac >> gvs[is_comparator_def, flip_comparison_opcode_def,
      ao_unsigned_boundaries_def, ao_signed_boundaries_def, LET_THM])
  >> rpt strip_tac >> gvs[]
QED

(* Full structural info for flip entries — by induction using step lemma *)
Triviality scan_flip_info[local]:
  !dfg insts flips removes inserts id new_opc new_w op1.
    ao_cmp_flip_scan dfg insts = (flips, removes, inserts) /\
    ALOOKUP flips id = SOME (new_opc, new_w, op1) ==>
    ?inst w out_var.
      MEM inst insts /\ inst.inst_id = id /\
      is_comparator inst.inst_opcode /\
      inst.inst_operands = [op1; Lit w] /\
      inst.inst_outputs = [out_var] /\
      new_opc = flip_comparison_opcode inst.inst_opcode /\
      new_w = (if inst.inst_opcode = GT \/ inst.inst_opcode = SGT
               then w + 1w else w - 1w) /\
      (inst.inst_opcode = GT ==> w <> 0w - 1w) /\
      (inst.inst_opcode = LT ==> w <> 0w) /\
      (inst.inst_opcode = SGT ==> w <> i2w INT256_MAX) /\
      (inst.inst_opcode = SLT ==> w <> i2w INT256_MIN)
Proof
  Induct_on `insts`
  >- simp[ao_cmp_flip_scan_def]
  >> rpt gen_tac >> strip_tac >>
  `?flips0 removes0 inserts0.
     ao_cmp_flip_scan dfg insts = (flips0, removes0, inserts0)` by
    metis_tac[pairTheory.PAIR] >>
  Cases_on `flips = flips0`
  >- ( (* Passthrough: IH applies directly *)
    gvs[] >>
    qpat_x_assum `!dfg'. _` (drule_all_then strip_assume_tac) >>
    qexists_tac `inst` >> qexists_tac `w` >>
    qexists_tac `out_var` >> gvs[])
  >> (* Flip was prepended — use step info *)
  `?w' op1' out_var'.
     is_comparator h.inst_opcode /\
     h.inst_operands = [op1'; Lit w'] /\
     h.inst_outputs = [out_var'] /\
     flips = (h.inst_id, flip_comparison_opcode h.inst_opcode,
              (if h.inst_opcode = GT \/ h.inst_opcode = SGT
               then w' + 1w else w' - 1w), op1') :: flips0 /\
     (h.inst_opcode = GT ==> w' <> 0w - 1w) /\
     (h.inst_opcode = LT ==> w' <> 0w) /\
     (h.inst_opcode = SGT ==> w' <> i2w INT256_MAX) /\
     (h.inst_opcode = SLT ==> w' <> i2w INT256_MIN)` by
    (irule scan_step_flip_info >> metis_tac[]) >>
  gvs[] >>
  Cases_on `id = h.inst_id`
  >- (qexists_tac `h` >> gvs[])
  >> gvs[] >>
  `ALOOKUP flips0 id = SOME (new_opc, new_w, op1)` by gvs[] >>
  qpat_x_assum `!dfg'. _` (drule_all_then strip_assume_tac) >>
  qexists_tac `inst` >> qexists_tac `w` >>
  qexists_tac `out_var` >> gvs[]
QED

(* Terminators are disjoint from comparators/ISZERO/ASSERT *)
Triviality terminator_not_comparator[local]:
  !opc. is_terminator opc ==> ~is_comparator opc
Proof
  Cases >> simp[is_terminator_def, is_comparator_def]
QED

Triviality terminator_not_iszero[local]:
  !opc. is_terminator opc ==> opc <> ISZERO
Proof
  Cases >> simp[is_terminator_def]
QED

Triviality terminator_not_assert[local]:
  !opc. is_terminator opc ==> opc <> ASSERT
Proof
  Cases >> simp[is_terminator_def]
QED

(* Key: ALL_DISTINCT IDs + same ID in list => same element *)
Triviality all_distinct_id_unique[local]:
  !insts x y.
    ALL_DISTINCT (MAP (\i. i.inst_id) insts) /\
    MEM x insts /\ MEM y insts /\
    x.inst_id = y.inst_id ==>
    x = y
Proof
  Induct >> simp[] >>
  rpt gen_tac >> strip_tac >>
  gvs[listTheory.ALL_DISTINCT, listTheory.MAP, listTheory.MEM_MAP] >>
  metis_tac[listTheory.MEM_MAP]
QED

(* Scan only adds comparator/ISZERO/ASSERT IDs to lists.
   With unique IDs and dfg-closed, terminators can't collide. *)
Triviality scan_terminator_untouched[local]:
  !dfg insts inst flips removes inserts.
    ao_cmp_flip_scan dfg insts = (flips, removes, inserts) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) insts) /\
    (!v ui. MEM ui (dfg_get_uses dfg v) ==> MEM ui insts) /\
    MEM inst insts /\ is_terminator inst.inst_opcode ==>
    ALOOKUP flips inst.inst_id = NONE /\
    ~MEM inst.inst_id removes /\
    ALOOKUP inserts inst.inst_id = NONE
Proof
  rpt strip_tac >>
  simp[alistTheory.ALOOKUP_NONE]
  >- (* flips *)
     (CCONTR_TAC >> gvs[] >>
      drule_all scan_flips_are_comparators >> strip_tac >>
      `i = inst` by (irule all_distinct_id_unique >> metis_tac[]) >>
      gvs[] >> metis_tac[terminator_not_comparator])
  >- (* removes *)
     (CCONTR_TAC >> gvs[] >>
      drule_all scan_removes_are_iszero >> strip_tac >>
      `MEM ui insts` by metis_tac[] >>
      `ui = inst` by (irule all_distinct_id_unique >> metis_tac[]) >>
      gvs[] >> metis_tac[terminator_not_iszero])
  >- (* inserts *)
     (CCONTR_TAC >> gvs[] >>
      drule_all scan_inserts_are_assert >> strip_tac >>
      `MEM ui insts` by metis_tac[] >>
      `ui = inst` by (irule all_distinct_id_unique >> metis_tac[]) >>
      gvs[] >> metis_tac[terminator_not_assert])
QED

(* exec_block on same instruction from state_equiv states at terminator *)
Triviality exec_block_terminator_equiv[local]:
  !dead fuel ctx bb1 bb2 s1 s2 n inst.
    state_equiv dead s1 s2 /\
    s1.vs_inst_idx = n /\ s2.vs_inst_idx = n /\
    n < LENGTH bb1.bb_instructions /\
    n < LENGTH bb2.bb_instructions /\
    EL n bb1.bb_instructions = inst /\
    EL n bb2.bb_instructions = inst /\
    is_terminator inst.inst_opcode /\
    inst.inst_opcode <> INVOKE /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN dead)
    ==>
    lift_result (state_equiv dead) (execution_equiv dead)
      (execution_equiv dead)
      (exec_block fuel ctx bb1 s1) (exec_block fuel ctx bb2 s2)
Proof
  rpt strip_tac >>
  ONCE_REWRITE_TAC[exec_block_def] >> simp[get_instruction_def] >>
  `result_equiv dead (step_inst fuel ctx inst s1)
                      (step_inst fuel ctx inst s2)` by
    (irule step_inst_result_equiv >> simp[]) >>
  Cases_on `step_inst fuel ctx inst s1` >>
  Cases_on `step_inst fuel ctx inst s2` >>
  gvs[result_equiv_is_lift_result, stateEquivTheory.lift_result_def] >>
  `v.vs_halted <=> v'.vs_halted` by
    gvs[stateEquivTheory.state_equiv_def, stateEquivTheory.execution_equiv_def] >>
  IF_CASES_TAC >> gvs[] >>
  gvs[stateEquivTheory.lift_result_def,
      stateEquivTheory.execution_equiv_def, stateEquivTheory.state_equiv_def]
QED

(* ===== Non-NULL case: helpers + main proof ===== *)

(* FRONT of well-formed block are non-terminators *)
Triviality front_non_terminators[local]:
  !bb.
    bb_well_formed bb ==>
    EVERY (\i. ~is_terminator i.inst_opcode) (FRONT bb.bb_instructions)
Proof
  rpt strip_tac >>
  gvs[bb_well_formed_def] >>
  simp[listTheory.EVERY_EL] >> rpt strip_tac >>
  `n < LENGTH bb.bb_instructions` by
    (imp_res_tac rich_listTheory.FRONT_LENGTH >>
     gvs[listTheory.LENGTH_NIL]) >>
  `(FRONT bb.bb_instructions)❲n❳ = bb.bb_instructions❲n❳` by
    (irule rich_listTheory.EL_FRONT >> gvs[listTheory.NULL_EQ]) >>
  gvs[] >>
  first_x_assum (qspec_then `n` mp_tac) >> simp[] >>
  imp_res_tac rich_listTheory.FRONT_LENGTH >>
  gvs[listTheory.LENGTH_NIL]
QED

(* exec_block_skip_prefix index match for FRONT *)
Triviality front_prefix_index_match[local]:
  !bb.
    bb.bb_instructions <> [] ==>
    !k. k < LENGTH (FRONT bb.bb_instructions) ==>
        bb.bb_instructions❲0 + k❳ = (FRONT bb.bb_instructions)❲k❳
Proof
  rpt strip_tac >> simp[] >>
  irule (GSYM rich_listTheory.EL_FRONT) >>
  gvs[listTheory.NULL_EQ]
QED

(* Non-NULL case *)
Theorem non_null_block_sim[local]:
  !mid dfg fn1 lbl bb1 bb' fuel ctx s1 s2 dead.
    dead = ao_cmp_flip_dead_vars dfg fn1 /\
    dfg = dfg_build_function fn1 /\
    (!inst. MEM inst (fn_insts fn1) ==> inst.inst_opcode <> INVOKE) /\
    fn_inst_ids_distinct fn1 /\
    ~NULL (FST (ao_cmp_flip_scan dfg (fn_insts fn1))) /\
    bb_well_formed bb1 /\
    lookup_block lbl fn1.fn_blocks = SOME bb1 /\
    lookup_block lbl (ao_cmp_flip_function mid dfg fn1).fn_blocks = SOME bb' /\
    state_equiv dead s1 s2 /\ s1.vs_inst_idx = 0 ==>
    lift_result (state_equiv dead) (execution_equiv dead)
      (execution_equiv dead)
      (exec_block fuel ctx bb1 s1) (exec_block fuel ctx bb' s2)
Proof
  rpt strip_tac >> gvs[] >>
  Cases_on `ao_cmp_flip_scan (dfg_build_function fn1) (fn_insts fn1)` >>
  Cases_on `r` >> rename1 `(flips, removes, inserts)` >>
  `bb'.bb_instructions =
    FLAT (MAP (ao_cmp_flip_apply_inst mid flips removes inserts)
              bb1.bb_instructions) /\
   bb'.bb_label = bb1.bb_label` by
    (`~NULL flips` by gvs[] >>
     metis_tac[cmp_flip_block_structure]) >>
  cheat
QED

(* ===== Main theorem ===== *)

Theorem ao_cmp_flip_block_sim:
  !mid dfg fn1 lbl bb1 bb' fuel ctx s1 s2.
    let dead = ao_cmp_flip_dead_vars dfg fn1 in
    dfg = dfg_build_function fn1 /\
    (!inst. MEM inst (fn_insts fn1) ==> inst.inst_opcode <> INVOKE) /\
    fn_inst_ids_distinct fn1 /\
    bb_well_formed bb1 /\
    lookup_block lbl fn1.fn_blocks = SOME bb1 /\
    lookup_block lbl (ao_cmp_flip_function mid dfg fn1).fn_blocks = SOME bb' /\
    state_equiv dead s1 s2 /\ s1.vs_inst_idx = 0 ==>
    lift_result (state_equiv dead) (execution_equiv dead)
      (execution_equiv dead)
      (exec_block fuel ctx bb1 s1) (exec_block fuel ctx bb' s2)
Proof
  simp[LET_THM] >> rpt gen_tac >> strip_tac >>
  Cases_on `NULL (FST (ao_cmp_flip_scan (dfg_build_function fn1)
                                         (fn_insts fn1)))`
  >- (* NULL: function unchanged, dead={}, s1=s2 *)
     (`ao_cmp_flip_function mid (dfg_build_function fn1) fn1 = fn1` by
        (irule ao_cmp_flip_null_sim >> simp[]) >>
      `bb' = bb1` by gvs[] >> gvs[] >>
      `ao_cmp_flip_dead_vars (dfg_build_function fn1) fn1 = {}` by
        metis_tac[dead_empty_when_null] >>
      gvs[] >>
      `s1 = s2` by (irule state_equiv_empty_eq >> simp[]) >>
      gvs[] >>
      irule lift_result_refl >>
      simp[state_equiv_refl, execution_equiv_refl])
  >- metis_tac[non_null_block_sim]
QED

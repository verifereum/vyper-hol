(* Obligation: cmp_flip preserves block execution up to dead variables. *)
Theory aoCmpFlipObligation
Ancestors
  algebraicOptDefs algebraicOptCmpFlipSim
  analysisSimDefs analysisSimProofsBase
  stateEquiv stateEquivProps execEquivProps passSimulationProps
  passSharedDefs venomInstProps
  venomExecSemantics venomState venomInst venomWf
Libs
  pairLib BasicProvers

(* ===== Scan step characterization ===== *)

Triviality scan_step_detail[local]:
  !dfg h rest fl0 rm0 ins0 fl1 rm1 ins1.
    ao_cmp_flip_scan dfg rest = (fl0, rm0, ins0) /\
    ao_cmp_flip_scan dfg (h :: rest) = (fl1, rm1, ins1) ==>
    (fl1 = fl0 /\ rm1 = rm0 /\ ins1 = ins0) \/
    (?w op1 out_var.
       is_comparator h.inst_opcode /\
       h.inst_operands = [op1; Lit w] /\
       h.inst_outputs = [out_var] /\
       fl1 = (h.inst_id, flip_comparison_opcode h.inst_opcode,
              (if h.inst_opcode = GT \/ h.inst_opcode = SGT
               then w + 1w else w - 1w), op1) :: fl0 /\
       (h.inst_opcode = GT ==> w <> 0w - 1w) /\
       (h.inst_opcode = LT ==> w <> 0w) /\
       (h.inst_opcode = SGT ==> w <> i2w INT256_MAX) /\
       (h.inst_opcode = SLT ==> w <> i2w INT256_MIN) /\
       LENGTH (dfg_get_uses dfg out_var) = 1 /\
       ((rm1 = (HD (dfg_get_uses dfg out_var)).inst_id :: rm0 /\
         ins1 = ins0 /\
         (HD (dfg_get_uses dfg out_var)).inst_opcode = ISZERO) \/
        (rm1 = rm0 /\
         ins1 = ((HD (dfg_get_uses dfg out_var)).inst_id, out_var,
                  ao_fresh_var h.inst_id "iz", h.inst_id) :: ins0 /\
         (HD (dfg_get_uses dfg out_var)).inst_opcode = ASSERT)))
Proof
  rpt gen_tac >>
  ONCE_REWRITE_TAC [ao_cmp_flip_scan_def] >>
  simp_tac std_ss [LET_THM] >>
  pairarg_tac >> simp_tac std_ss [] >>
  strip_tac >> gvs[] >>
  pop_assum mp_tac >>
  IF_CASES_TAC >> simp[] >>
  every_case_tac >> simp[] >>
  rpt (pairarg_tac >> simp[]) >>
  rpt IF_CASES_TAC >> simp[] >>
  rpt strip_tac >> gvs[is_comparator_def, flip_comparison_opcode_def,
    ao_unsigned_boundaries_def, ao_signed_boundaries_def, LET_THM]
QED

(* ===== Helper: NULL flips => scan = ([],[],[]) ===== *)

Theorem scan_null_triple[local]:
  !dfg insts. NULL (FST (ao_cmp_flip_scan dfg insts)) ==>
              ao_cmp_flip_scan dfg insts = ([],[],[])
Proof
  Induct_on `insts`
  >- simp[ao_cmp_flip_scan_def]
  >> rpt strip_tac >>
  `?f r ins. ao_cmp_flip_scan dfg insts = (f,r,ins)` by
    metis_tac[pairTheory.PAIR] >>
  `?fl1 rm1 ins1. ao_cmp_flip_scan dfg (h::insts) = (fl1,rm1,ins1)` by
    metis_tac[pairTheory.PAIR] >>
  drule_all scan_step_detail >>
  disch_then strip_assume_tac >> gvs[] >>
  first_x_assum (qspec_then `dfg` mp_tac) >> gvs[]
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

Triviality run_insts_pair_base[local]:
  !fuel ctx i1 i2 s.
    i1.inst_opcode <> INVOKE /\ i2.inst_opcode <> INVOKE ==>
    run_insts fuel ctx [i1; i2] s =
    case step_inst_base i1 s of
      OK s' => step_inst_base i2 s'
    | r => r
Proof
  rpt strip_tac >>
  simp[run_insts_def, run_insts_singleton] >>
  `step_inst fuel ctx i1 s = step_inst_base i1 s` by
    (irule step_inst_non_invoke >> simp[]) >>
  gvs[] >>
  Cases_on `step_inst_base i1 s` >> gvs[] >>
  irule step_inst_non_invoke >> simp[]
QED

Triviality run_insts_pair_ok_fst[local]:
  !fuel ctx i1 i2 s s'.
    i1.inst_opcode <> INVOKE /\ i2.inst_opcode <> INVOKE /\
    step_inst_base i1 s = OK s' ==>
    run_insts fuel ctx [i1; i2] s = step_inst_base i2 s'
Proof
  rpt strip_tac >>
  `run_insts fuel ctx [i1; i2] s =
   case step_inst_base i1 s of
     OK s'' => step_inst_base i2 s''
   | r => r` by (irule run_insts_pair_base >> simp[]) >>
  gvs[]
QED

(* ===== Iszero invariant for flip-remove pairing ===== *)

(* After the flip instruction executes, the comparator output in s2
   is the iszero of the value in s1. This is needed by the remove step
   (ISZERO → ASSIGN) to show the ASSIGN produces the same value as ISZERO. *)
Definition cmp_flip_iszero_inv_def:
  cmp_flip_iszero_inv flips all_insts s1 s2 <=>
    !inst out.
      MEM inst all_insts /\
      ALOOKUP flips inst.inst_id <> NONE /\
      MEM out inst.inst_outputs ==>
      (IS_SOME (lookup_var out s1) <=> IS_SOME (lookup_var out s2)) /\
      !v1 v2. lookup_var out s1 = SOME v1 /\
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
    (!fi out. MEM fi all_insts /\ ALOOKUP flips fi.inst_id <> NONE /\
             MEM out fi.inst_outputs /\ MEM out inst.inst_outputs ==>
             (IS_SOME (lookup_var out s1') <=> IS_SOME (lookup_var out s2'))) /\
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
  >- metis_tac[]
  >- ( (* non-overlap IS_SOME *)
    `lookup_var out s1' = lookup_var out s1` by metis_tac[] >>
    `lookup_var out s2' = lookup_var out s2` by metis_tac[] >>
    gvs[] >> metis_tac[])
  >- metis_tac[]
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
  rpt conj_tac >> rpt strip_tac >>
  TRY (`fi.inst_id <> inst.inst_id` by (CCONTR_TAC >> gvs[]) >>
       metis_tac[]) >>
  TRY (irule step_preserves_non_output_vars >> metis_tac[])
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

(* update_var on dead variable, right side only, preserves state_equiv *)
Triviality update_dead_var_right_equiv[local]:
  !dead x v s1 s2.
    state_equiv dead s1 s2 /\ x IN dead ==>
    state_equiv dead s1 (update_var x v s2)
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

(* Helper: comparator with NONE first operand always errors *)
Triviality comparator_none_errors[local]:
  !inst s x2 w.
    is_comparator inst.inst_opcode /\
    inst.inst_operands = [x2; Lit w] /\
    eval_operand x2 s = NONE ==>
    !v. step_inst_base inst s <> OK v
Proof
  rpt strip_tac >> gvs[is_comparator_def] >>
  gvs[step_inst_base_def, exec_pure2_def, eval_operand_def]
QED

(* Helper: flip_comparison_opcode preserves is_comparator *)
Triviality flip_is_comparator[local]:
  !opc. is_comparator opc ==> is_comparator (flip_comparison_opcode opc)
Proof
  Cases >> simp[is_comparator_def, flip_comparison_opcode_def]
QED

(* Helper: comparator flip step gives original result + iszero relationship *)
Triviality flip_step_gives_iszero[local]:
  !inst s1 s2 x2 w new_w v out_var.
    is_comparator inst.inst_opcode /\
    inst.inst_operands = [x2; Lit w] /\
    inst.inst_outputs = [out_var] /\
    new_w = (if inst.inst_opcode = GT \/ inst.inst_opcode = SGT
             then w + 1w else w - 1w) /\
    eval_operand x2 s1 = SOME v /\
    eval_operand x2 s2 = SOME v /\
    (inst.inst_opcode = GT ==> w <> 0w - 1w) /\
    (inst.inst_opcode = LT ==> w <> 0w) /\
    (inst.inst_opcode = SGT ==> w <> i2w INT256_MAX) /\
    (inst.inst_opcode = SLT ==> w <> i2w INT256_MIN) ==>
    ?r1 r2.
      step_inst_base inst s1 = OK (update_var out_var r1 s1) /\
      step_inst_base (inst with
        <| inst_opcode := flip_comparison_opcode inst.inst_opcode;
           inst_operands := [x2; Lit new_w] |>) s2 =
      OK (update_var out_var r2 s2) /\
      r2 = bool_to_word (r1 = 0w)
Proof
  rpt strip_tac >> gvs[is_comparator_def] >>
  simp[step_inst_base_def, exec_pure2_def, eval_operand_def,
       flip_comparison_opcode_def] >> (
  simp[GSYM cmp_flip_iszero_equiv_gt, GSYM cmp_flip_iszero_equiv_lt,
       GSYM cmp_flip_iszero_equiv_sgt, GSYM cmp_flip_iszero_equiv_slt] >>
  metis_tac[])
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
    case (step_inst fuel ctx inst s1,
          step_inst fuel ctx
            (inst with
              <| inst_opcode := flip_comparison_opcode inst.inst_opcode;
                 inst_operands := [x2; Lit (if inst.inst_opcode = GT \/
                   inst.inst_opcode = SGT then w + 1w else w - 1w)] |>) s2) of
      (OK s1', OK s2') =>
        state_equiv dead s1' s2' /\
        cmp_flip_iszero_inv flips all_insts s1' s2'
    | (OK _, _) => F
    | (_, OK _) => F
    | _ => T
Proof
  rpt strip_tac >>
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
    (irule eval_operand_equiv >> qexists_tac `dead` >> simp[]) >>
  Cases_on `eval_operand x2 s1`
  >- ( (* NONE: comparator errors on both sides *)
    `!v. step_inst_base inst s1 <> OK v` by
      (irule comparator_none_errors >> metis_tac[]) >>
    `!v. step_inst_base flipped s2 <> OK v` by
      (simp[Abbr `flipped`] >> strip_tac >>
       irule comparator_none_errors >> simp[] >>
       metis_tac[flip_is_comparator]) >>
    Cases_on `step_inst_base inst s1` >> gvs[] >>
    Cases_on `step_inst_base flipped s2` >> gvs[])
  >> (* SOME: use flip_step_gives_iszero *)
  rename1 `eval_operand x2 s1 = SOME v` >>
  `?r1 r2.
     step_inst_base inst s1 = OK (update_var out_var r1 s1) /\
     step_inst_base (inst with
       <| inst_opcode := flip_comparison_opcode inst.inst_opcode;
          inst_operands := [x2; Lit (if inst.inst_opcode = GT \/
            inst.inst_opcode = SGT then w + 1w else w - 1w)] |>) s2 =
     OK (update_var out_var r2 s2) /\
     r2 = bool_to_word (r1 = 0w)` by
    (irule flip_step_gives_iszero >> gvs[] >> metis_tac[]) >>
  `step_inst_base flipped s2 = OK (update_var out_var r2 s2)` by
    (simp[Abbr `flipped`]) >>
  simp[] >> conj_tac
  >- (irule update_dead_var_state_equiv >> simp[])
  >> irule iszero_inv_frame >>
  qexistsl_tac [`ctx`, `fuel`, `inst`, `s1`, `s2`] >>
  simp[step_inst_non_invoke] >> rpt conj_tac >> rpt strip_tac >>
  gvs[update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

val per_inst_flip_exp =
  SIMP_RULE std_ss [pairTheory.pair_case_thm] per_inst_flip;

(* Case 3: Remove — ISZERO replaced by ASSIGN.
   The iszero invariant ensures the flipped output in s2 already equals
   iszero(original output in s1), so ASSIGN copies the same value as
   ISZERO would produce. *)
Triviality per_inst_remove[local]:
  !dead flips all_insts inst fuel ctx s1 s2 cmp_out iz_out fi.
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
  `(IS_SOME (lookup_var cmp_out s1) <=> IS_SOME (lookup_var cmp_out s2)) /\
   !v1 v2. lookup_var cmp_out s1 = SOME v1 /\
           lookup_var cmp_out s2 = SOME v2 ==>
           v2 = bool_to_word (v1 = 0w)` by (
    qpat_x_assum `cmp_flip_iszero_inv _ _ _ _`
      (fn th => mp_tac (REWRITE_RULE [cmp_flip_iszero_inv_def] th)) >>
    disch_then (qspecl_then [`fi`, `cmp_out`] mp_tac) >> simp[]) >>
  Cases_on `lookup_var cmp_out s1`
  >- ( (* NONE: both error *)
    `lookup_var cmp_out s2 = NONE` by
      (Cases_on `lookup_var cmp_out s2` >> gvs[]) >>
    gvs[step_inst_base_def, exec_pure1_def, eval_operand_def])
  >> (* SOME: use iszero relationship *)
  rename1 `lookup_var cmp_out s1 = SOME v0` >>
  `?v0'. lookup_var cmp_out s2 = SOME v0'` by
    (Cases_on `lookup_var cmp_out s2` >> gvs[]) >>
  `v0' = bool_to_word (v0 = 0w)` by metis_tac[] >>
  gvs[step_inst_base_def, exec_pure1_def, eval_operand_def] >>
  conj_tac
  >- (irule update_var_preserves >> simp[])
  >> rw[cmp_flip_iszero_inv_def] >> rpt strip_tac >>
  rename1 `MEM fi' all_insts` >>
  `fi'.inst_id <> inst.inst_id` by (CCONTR_TAC >> gvs[]) >>
  `out <> iz_out` by metis_tac[] >>
  gvs[update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  qpat_x_assum `cmp_flip_iszero_inv _ _ _ _`
    (fn th => mp_tac (REWRITE_RULE [cmp_flip_iszero_inv_def] th)) >>
  disch_then (qspecl_then [`fi'`, `out`] mp_tac) >>
  simp[] >> strip_tac >> gvs[lookup_var_def]
QED

val per_inst_remove_exp =
  SIMP_RULE std_ss [pairTheory.pair_case_thm] per_inst_remove;

(* Helper: ISZERO step on a known value *)
Triviality iszero_step_known[local]:
  !inst_id s cmp_out fresh v.
    lookup_var cmp_out s = SOME v ==>
    step_inst_base
      <| inst_id := inst_id; inst_opcode := ISZERO;
         inst_operands := [Var cmp_out]; inst_outputs := [fresh] |> s =
    OK (update_var fresh (bool_to_word (v = 0w)) s)
Proof
  rpt strip_tac >>
  simp[step_inst_base_def, exec_pure1_def, eval_operand_def]
QED

(* Helper: ISZERO step when operand is NONE → not OK *)
Triviality iszero_step_none[local]:
  !inst_id s cmp_out fresh.
    lookup_var cmp_out s = NONE ==>
    !v. step_inst_base
      <| inst_id := inst_id; inst_opcode := ISZERO;
         inst_operands := [Var cmp_out]; inst_outputs := [fresh] |> s <>
    OK v
Proof
  simp[step_inst_base_def, exec_pure1_def, eval_operand_def]
QED

(* Helper: ASSERT step when operand is NONE → not OK *)
Triviality assert_step_none[local]:
  !inst s cmp_out.
    inst.inst_opcode = ASSERT /\
    inst.inst_operands = [Var cmp_out] /\
    lookup_var cmp_out s = NONE ==>
    !v. step_inst_base inst s <> OK v
Proof
  simp[step_inst_base_def, exec_pure1_def, eval_operand_def]
QED

(* Helper: ASSERT step on known nonzero value succeeds *)
Triviality assert_step_nonzero[local]:
  !inst s cmp_out v.
    inst.inst_opcode = ASSERT /\
    inst.inst_operands = [Var cmp_out] /\
    lookup_var cmp_out s = SOME v /\ v <> 0w ==>
    step_inst_base inst s = OK s
Proof
  simp[step_inst_base_def, exec_pure1_def, eval_operand_def]
QED

(* Helper: ASSERT step on zero value is not OK *)
Triviality assert_step_zero[local]:
  !inst s cmp_out.
    inst.inst_opcode = ASSERT /\
    inst.inst_operands = [Var cmp_out] /\
    lookup_var cmp_out s = SOME 0w ==>
    !v'. step_inst_base inst s <> OK v'
Proof
  simp[step_inst_base_def, exec_pure1_def, eval_operand_def]
QED

(* Case 4: Insert — ASSERT inst with iszero prepended.
   Split into sub-cases to stay under proof timeout. *)

(* Insert sub-case: state_equiv + inv maintained after update_var fresh *)
Triviality per_inst_insert_nonzero_equiv[local]:
  !dead flips all_insts s1 s2 fresh v.
    state_equiv dead s1 s2 /\
    cmp_flip_iszero_inv flips all_insts s1 s2 /\
    fresh IN dead /\
    (!fi' out. MEM fi' all_insts /\ ALOOKUP flips fi'.inst_id <> NONE /\
               MEM out fi'.inst_outputs ==> fresh <> out) ==>
    state_equiv dead s1 (update_var fresh v s2) /\
    cmp_flip_iszero_inv flips all_insts s1 (update_var fresh v s2)
Proof
  rpt strip_tac
  >- (irule update_dead_var_right_equiv >> simp[])
  >> rw[cmp_flip_iszero_inv_def] >> rpt strip_tac >>
  rename1 `MEM fi' all_insts` >>
  `fresh <> out` by metis_tac[] >>
  simp[update_var_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  qpat_x_assum `cmp_flip_iszero_inv _ _ _ _`
    (fn th => mp_tac (REWRITE_RULE [cmp_flip_iszero_inv_def] th)) >>
  disch_then (qspecl_then [`fi'`, `out`] mp_tac) >>
  simp[] >> strip_tac >> gvs[lookup_var_def, update_var_def,
    finite_mapTheory.FLOOKUP_UPDATE]
QED

(* Case 4: Insert — ASSERT inst with iszero prepended.
   Uses run_insts_pair_base to rewrite to step_inst_base. *)
Triviality per_inst_insert[local]:
  !dead flips all_insts inst fuel ctx s1 s2 mid cmp_out fresh cmp_id fi.
    state_equiv dead s1 s2 /\
    cmp_flip_iszero_inv flips all_insts s1 s2 /\
    MEM inst all_insts /\
    inst.inst_opcode = ASSERT /\
    inst.inst_operands = [Var cmp_out] /\
    ALOOKUP flips inst.inst_id = NONE /\
    fresh IN dead /\
    MEM fi all_insts /\
    ALOOKUP flips fi.inst_id <> NONE /\
    MEM cmp_out fi.inst_outputs /\
    (!fi' out. MEM fi' all_insts /\ ALOOKUP flips fi'.inst_id <> NONE /\
               MEM out fi'.inst_outputs ==> fresh <> out)
    ==>
    case (step_inst fuel ctx inst s1,
          run_insts fuel ctx
            [<| inst_id := ao_fresh_id mid cmp_id 0;
                inst_opcode := ISZERO;
                inst_operands := [Var cmp_out];
                inst_outputs := [fresh] |>;
             inst with inst_operands := [Var fresh]] s2) of
      (OK s1', OK s2') =>
        state_equiv dead s1' s2' /\
        cmp_flip_iszero_inv flips all_insts s1' s2'
    | (OK _, _) => F
    | (_, OK _) => F
    | _ => T
Proof
  rpt strip_tac >>
  `(IS_SOME (lookup_var cmp_out s1) <=> IS_SOME (lookup_var cmp_out s2)) /\
   !v1 v2. lookup_var cmp_out s1 = SOME v1 /\
           lookup_var cmp_out s2 = SOME v2 ==>
           v2 = bool_to_word (v1 = 0w)` by
    (fs[cmp_flip_iszero_inv_def] >>
     first_x_assum (qspecl_then [`fi`, `cmp_out`] mp_tac) >> simp[]) >>
  `step_inst fuel ctx inst s1 = step_inst_base inst s1` by
    (irule step_inst_non_invoke >> simp[]) >>
  pop_assum (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
  Cases_on `lookup_var cmp_out s1`
  >- (
    `lookup_var cmp_out s2 = NONE` by
      (Cases_on `lookup_var cmp_out s2` >> gvs[]) >>
    `!v. step_inst_base inst s1 <> OK v` by
      (irule assert_step_none >> simp[]) >>
    `run_insts fuel ctx
       [<|inst_id := ao_fresh_id mid cmp_id 0; inst_opcode := ISZERO;
          inst_operands := [Var cmp_out]; inst_outputs := [fresh]|>;
        inst with inst_operands := [Var fresh]] s2 =
     case step_inst_base
       <|inst_id := ao_fresh_id mid cmp_id 0; inst_opcode := ISZERO;
          inst_operands := [Var cmp_out]; inst_outputs := [fresh]|> s2 of
       OK s' => step_inst_base (inst with inst_operands := [Var fresh]) s'
     | r => r` by (irule run_insts_pair_base >> simp[]) >>
    pop_assum (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
    Cases_on `step_inst_base inst s1` >> gvs[] >>
    simp[step_inst_base_def, exec_pure1_def, eval_operand_def])
  >> rename1 `lookup_var cmp_out s1 = SOME v1` >>
  `?v2. lookup_var cmp_out s2 = SOME v2 /\ v2 = bool_to_word (v1 = 0w)` by
    (Cases_on `lookup_var cmp_out s2` >> gvs[] >> metis_tac[]) >>
  `run_insts fuel ctx
     [<|inst_id := ao_fresh_id mid cmp_id 0; inst_opcode := ISZERO;
        inst_operands := [Var cmp_out]; inst_outputs := [fresh]|>;
      inst with inst_operands := [Var fresh]] s2 =
   step_inst_base (inst with inst_operands := [Var fresh])
     (update_var fresh (bool_to_word (v2 = 0w)) s2)` by
    (irule run_insts_pair_ok_fst >> simp[] >>
     irule iszero_step_known >> simp[]) >>
  pop_assum (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
  Cases_on `v1 = 0w`
  >- (
    gvs[bool_to_word_def] >>
    `!v. step_inst_base inst s1 <> OK v` by
      (irule assert_step_zero >> simp[]) >>
    `!v. step_inst_base (inst with inst_operands := [Var fresh])
         (update_var fresh 0w s2) <> OK v` by
      (irule assert_step_zero >>
       simp[update_var_def, lookup_var_def,
            finite_mapTheory.FLOOKUP_UPDATE]) >>
    Cases_on `step_inst_base inst s1` >> gvs[] >>
    Cases_on `step_inst_base (inst with inst_operands := [Var fresh])
              (update_var fresh 0w s2)` >> gvs[])
  >> gvs[bool_to_word_def] >>
  `step_inst_base inst s1 = OK s1` by
    (irule assert_step_nonzero >> simp[]) >>
  `step_inst_base (inst with inst_operands := [Var fresh])
     (update_var fresh 1w s2) = OK (update_var fresh 1w s2)` by
    (irule assert_step_nonzero >>
     simp[update_var_def, lookup_var_def,
          finite_mapTheory.FLOOKUP_UPDATE]) >>
  pop_assum (fn th => REWRITE_TAC [th]) >>
  pop_assum (fn th => REWRITE_TAC [th]) >>
  simp[] >>
  irule per_inst_insert_nonzero_equiv >> gvs[]
QED

val per_inst_insert_exp =
  SIMP_RULE std_ss [pairTheory.pair_case_thm] per_inst_insert;

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
         (inst.inst_opcode = SLT ==> w <> i2w INT256_MIN)) /\
    (* Remove structural info *)
    (MEM inst.inst_id removes ==>
      ?cmp_out iz_out fi.
        inst.inst_opcode = ISZERO /\
        inst.inst_operands = [Var cmp_out] /\
        inst.inst_outputs = [iz_out] /\
        MEM fi all_insts /\
        ALOOKUP flips fi.inst_id <> NONE /\
        MEM cmp_out fi.inst_outputs) /\
    (* Insert structural info *)
    (!cmp_out fresh cmp_id.
      ALOOKUP inserts inst.inst_id = SOME (cmp_out, fresh, cmp_id) ==>
      inst.inst_opcode = ASSERT /\
      inst.inst_operands = [Var cmp_out] /\
      fresh IN dead /\
      (!fi' out. MEM fi' all_insts /\ ALOOKUP flips fi'.inst_id <> NONE /\
                 MEM out fi'.inst_outputs ==> fresh <> out) /\
      (?fi. MEM fi all_insts /\
            ALOOKUP flips fi.inst_id <> NONE /\
            MEM cmp_out fi.inst_outputs))
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
      pop_assum (fn th => REWRITE_TAC [th]) >>
      simp[run_insts_singleton] >>
      `?cmp_out iz_out fi.
         inst.inst_opcode = ISZERO /\
         inst.inst_operands = [Var cmp_out] /\
         inst.inst_outputs = [iz_out] /\
         MEM fi all_insts /\
         ALOOKUP flips fi.inst_id <> NONE /\
         MEM cmp_out fi.inst_outputs` by metis_tac[] >>
      irule per_inst_remove_exp >>
      gvs[] >> metis_tac[])
    >> Cases_on `ALOOKUP inserts inst.inst_id`
    >- ( (* NONE: Unchanged *)
      `ao_cmp_flip_apply_inst mid flips removes inserts inst = [inst]` by
        (irule apply_inst_unchanged >> simp[]) >>
      pop_assum (fn th => REWRITE_TAC [th]) >>
      REWRITE_TAC [run_insts_singleton] >>
      irule per_inst_unchanged >> gvs[] >>
      first_x_assum ACCEPT_TAC)
    >> (* SOME: Insert case *)
    PairCases_on `x` >>
    `ao_cmp_flip_apply_inst mid flips removes inserts inst =
     [<| inst_id := ao_fresh_id mid x2 0; inst_opcode := ISZERO;
         inst_operands := [Var x0]; inst_outputs := [x1] |>;
      inst with inst_operands := [Var x1]]` by
      simp[ao_cmp_flip_apply_inst_def] >>
    pop_assum (fn th => REWRITE_TAC [th]) >>
    irule per_inst_insert >>
    qpat_x_assum `!_ _ _. SOME _ = SOME _ ==> _`
      (qspecl_then [`x0`, `x1`, `x2`] mp_tac) >> simp[] >> strip_tac >>
    qexists_tac `fi` >> gvs[])
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
  pop_assum (fn th => REWRITE_TAC [th]) >>
  REWRITE_TAC [run_insts_singleton] >>
  irule per_inst_flip_exp >> simp[] >>
  `ALOOKUP flips inst.inst_id <> NONE` by simp[] >>
  metis_tac[listTheory.MEM]
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
         (inst.inst_opcode = SLT ==> w <> i2w INT256_MIN)) /\
    (* Remove structural info *)
    (!inst. MEM inst body_insts /\ MEM inst.inst_id removes ==>
      ?cmp_out iz_out fi.
        inst.inst_opcode = ISZERO /\
        inst.inst_operands = [Var cmp_out] /\
        inst.inst_outputs = [iz_out] /\
        MEM fi all_insts /\
        ALOOKUP flips fi.inst_id <> NONE /\
        MEM cmp_out fi.inst_outputs) /\
    (* Insert structural info *)
    (!inst cmp_out fresh cmp_id.
      MEM inst body_insts /\
      ALOOKUP inserts inst.inst_id = SOME (cmp_out, fresh, cmp_id) ==>
      inst.inst_opcode = ASSERT /\
      inst.inst_operands = [Var cmp_out] /\
      fresh IN dead /\
      (!fi' out. MEM fi' all_insts /\ ALOOKUP flips fi'.inst_id <> NONE /\
                 MEM out fi'.inst_outputs ==> fresh <> out) /\
      (?fi. MEM fi all_insts /\
            ALOOKUP flips fi.inst_id <> NONE /\
            MEM cmp_out fi.inst_outputs))
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
  Induct_on `body_insts`
  >- simp[run_insts_def]
  >> rpt gen_tac >> strip_tac >>
  `~is_terminator h.inst_opcode /\ h.inst_opcode <> INVOKE /\
   EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE)
         body_insts` by
    (qpat_x_assum `EVERY _ (_::_)` mp_tac >>
     simp[listTheory.EVERY_DEF]) >>
  `case (step_inst fuel ctx h s1,
        run_insts fuel ctx
          (ao_cmp_flip_apply_inst mid flips removes inserts h) s2) of
     (OK s1', OK s2') =>
       state_equiv dead s1' s2' /\
       cmp_flip_iszero_inv flips all_insts s1' s2'
   | (OK _, _) => F | (_, OK _) => F | _ => T` by
    (irule per_inst_sim >> simp[] >>
     rpt conj_tac >> simp[] >>
     metis_tac[listTheory.MEM]) >>
  Cases_on `step_inst fuel ctx h s1` >>
  Cases_on `run_insts fuel ctx
    (ao_cmp_flip_apply_inst mid flips removes inserts h) s2` >> gvs[]
  >- (* OK, OK: apply IH *)
    (simp[Once run_insts_def, run_insts_append] >>
     `!inst. MEM inst body_insts ==> MEM inst (h::body_insts)` by
       simp[listTheory.MEM] >>
     first_x_assum irule >> simp[] >>
     rpt conj_tac >> simp[] >> metis_tac[])
  >> (* Non-OK: unfold and simplify to T *)
  simp[Once run_insts_def, run_insts_append]
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

Triviality scan_step_flips_subset[local]:
  !dfg h rest flips removes inserts fl0 rm0 ins0.
    ao_cmp_flip_scan dfg rest = (fl0, rm0, ins0) /\
    ao_cmp_flip_scan dfg (h :: rest) = (flips, removes, inserts) ==>
    flips = fl0 \/
    (?opc w op1. flips = (h.inst_id, opc, w, op1) :: fl0 /\
                 is_comparator h.inst_opcode)
Proof
  rpt strip_tac >>
  drule_all scan_step_detail >> strip_tac >> gvs[]
QED

Triviality scan_step_removes_subset[local]:
  !dfg h rest flips removes inserts fl0 rm0 ins0.
    ao_cmp_flip_scan dfg rest = (fl0, rm0, ins0) /\
    ao_cmp_flip_scan dfg (h :: rest) = (flips, removes, inserts) ==>
    removes = rm0 \/
    (?v ui. removes = ui.inst_id :: rm0 /\
            MEM ui (dfg_get_uses dfg v) /\ ui.inst_opcode = ISZERO)
Proof
  rpt strip_tac >>
  drule_all scan_step_detail >>
  disch_then strip_assume_tac >> gvs[] >>
  qexists_tac `out_var` >>
  qexists_tac `HD (dfg_get_uses dfg out_var)` >>
  `dfg_get_uses dfg out_var <> []` by
    (Cases_on `dfg_get_uses dfg out_var` >> gvs[]) >>
  simp[rich_listTheory.HEAD_MEM]
QED

Triviality scan_step_inserts_subset[local]:
  !dfg h rest flips removes inserts fl0 rm0 ins0.
    ao_cmp_flip_scan dfg rest = (fl0, rm0, ins0) /\
    ao_cmp_flip_scan dfg (h :: rest) = (flips, removes, inserts) ==>
    inserts = ins0 \/
    (?v ui.
       inserts = (ui.inst_id, v, ao_fresh_var h.inst_id "iz",
                  h.inst_id) :: ins0 /\
       MEM ui (dfg_get_uses dfg v) /\ ui.inst_opcode = ASSERT)
Proof
  rpt strip_tac >>
  drule_all scan_step_detail >>
  disch_then strip_assume_tac >> gvs[] >>
  qexists_tac `HD (dfg_get_uses dfg out_var)` >>
  `dfg_get_uses dfg out_var <> []` by
    (Cases_on `dfg_get_uses dfg out_var` >> gvs[]) >>
  simp[rich_listTheory.HEAD_MEM]
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
  !dfg h rest flips removes inserts fl0 rm0 ins0.
    ao_cmp_flip_scan dfg rest = (fl0, rm0, ins0) /\
    ao_cmp_flip_scan dfg (h :: rest) = (flips, removes, inserts) /\
    flips <> fl0 ==>
    ?w op1 out_var.
      is_comparator h.inst_opcode /\
      h.inst_operands = [op1; Lit w] /\
      h.inst_outputs = [out_var] /\
      flips = (h.inst_id, flip_comparison_opcode h.inst_opcode,
               (if h.inst_opcode = GT \/ h.inst_opcode = SGT
                then w + 1w else w - 1w), op1) :: fl0 /\
      (h.inst_opcode = GT ==> w <> 0w - 1w) /\
      (h.inst_opcode = LT ==> w <> 0w) /\
      (h.inst_opcode = SGT ==> w <> i2w INT256_MAX) /\
      (h.inst_opcode = SLT ==> w <> i2w INT256_MIN)
Proof
  rpt strip_tac >>
  drule_all scan_step_detail >>
  disch_then strip_assume_tac >> gvs[]
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
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  rpt strip_tac >> gvs[] >>
  TRY (first_x_assum irule >> gvs[] >> NO_TAC) >>
  fs[listTheory.MEM_MAP] >> metis_tac[]
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

(* ===== Lift-result version of body simulation ===== *)

(* set_returndata + revert_state preserves execution_equiv *)
Triviality revert_set_rd_execution_equiv[local]:
  !dead s1 s2.
    execution_equiv dead s1 s2 ==>
    execution_equiv dead
      (revert_state (set_returndata [] s1))
      (revert_state (set_returndata [] s2))
Proof
  rw[execution_equiv_def, revert_state_def, set_returndata_def,
     lookup_var_def]
QED

(* state_equiv implies execution_equiv *)
Triviality state_equiv_imp_execution_equiv[local]:
  !dead s1 s2.
    state_equiv dead s1 s2 ==> execution_equiv dead s1 s2
Proof
  rw[state_equiv_def]
QED

(* update_var on dead variable preserves execution_equiv *)
Triviality update_dead_var_right_execution_equiv[local]:
  !dead x v s1 s2.
    execution_equiv dead s1 s2 /\ x IN dead ==>
    execution_equiv dead s1 (update_var x v s2)
Proof
  rw[execution_equiv_def, update_var_def, lookup_var_def] >>
  simp[finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> IF_CASES_TAC >> gvs[]
QED

(* ===== Per-instruction lift_result helpers (one per case) ===== *)

(* Unchanged case: lift_result version *)
Triviality per_inst_lr_unchanged[local]:
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
    lift_result
      (\s1' s2'. state_equiv dead s1' s2' /\
                 cmp_flip_iszero_inv flips all_insts s1' s2')
      (execution_equiv dead) (execution_equiv dead)
      (step_inst fuel ctx inst s1)
      (step_inst fuel ctx inst s2)
Proof
  rpt strip_tac >>
  `result_equiv dead (step_inst fuel ctx inst s1)
                     (step_inst fuel ctx inst s2)` by
    (irule step_inst_result_equiv >> simp[]) >>
  Cases_on `step_inst fuel ctx inst s1` >>
  Cases_on `step_inst fuel ctx inst s2` >>
  gvs[result_equiv_is_lift_result, stateEquivTheory.lift_result_def] >>
  irule iszero_inv_frame >>
  qexistsl_tac [`ctx`, `fuel`, `inst`, `s1`, `s2`] >> simp[] >>
  rpt conj_tac >> rpt strip_tac >>
  TRY (`fi.inst_id <> inst.inst_id` by (CCONTR_TAC >> gvs[]) >>
       metis_tac[]) >>
  TRY (irule step_preserves_non_output_vars >> metis_tac[])
QED

(* Remove case: lift_result version *)
Triviality per_inst_lr_remove[local]:
  !dead flips all_insts inst fuel ctx s1 s2 cmp_out iz_out fi.
    state_equiv dead s1 s2 /\
    cmp_flip_iszero_inv flips all_insts s1 s2 /\
    inst.inst_opcode = ISZERO /\
    inst.inst_operands = [Var cmp_out] /\
    inst.inst_outputs = [iz_out] /\
    ALOOKUP flips inst.inst_id = NONE /\
    MEM fi all_insts /\
    ALOOKUP flips fi.inst_id <> NONE /\
    MEM cmp_out fi.inst_outputs /\
    (!fi'. MEM fi' all_insts /\ fi'.inst_id <> inst.inst_id /\
           ALOOKUP flips fi'.inst_id <> NONE ==>
           !out. MEM out fi'.inst_outputs ==> ~MEM out inst.inst_outputs)
    ==>
    lift_result
      (\s1' s2'. state_equiv dead s1' s2' /\
                 cmp_flip_iszero_inv flips all_insts s1' s2')
      (execution_equiv dead) (execution_equiv dead)
      (step_inst_base inst s1)
      (step_inst_base (inst with inst_opcode := ASSIGN) s2)
Proof
  rpt strip_tac >>
  `(IS_SOME (lookup_var cmp_out s1) <=> IS_SOME (lookup_var cmp_out s2)) /\
   !v1 v2. lookup_var cmp_out s1 = SOME v1 /\
           lookup_var cmp_out s2 = SOME v2 ==>
           v2 = bool_to_word (v1 = 0w)` by
    (qpat_x_assum `cmp_flip_iszero_inv _ _ _ _`
      (fn th => ASSUME_TAC th >>
       mp_tac (REWRITE_RULE [cmp_flip_iszero_inv_def] th)) >>
     disch_then (qspecl_then [`fi`, `cmp_out`] mp_tac) >> simp[]) >>
  Cases_on `lookup_var cmp_out s1`
  >- (`lookup_var cmp_out s2 = NONE` by
        (Cases_on `lookup_var cmp_out s2` >> gvs[]) >>
      gvs[step_inst_base_def, exec_pure1_def, eval_operand_def,
          stateEquivTheory.lift_result_def])
  >> rename1 `lookup_var cmp_out s1 = SOME v0` >>
  `?v0'. lookup_var cmp_out s2 = SOME v0'` by
    (Cases_on `lookup_var cmp_out s2` >> gvs[]) >>
  `v0' = bool_to_word (v0 = 0w)` by metis_tac[] >>
  simp[step_inst_base_def, exec_pure1_def, eval_operand_def,
      stateEquivTheory.lift_result_def] >>
  conj_tac >- (irule update_var_preserves >> simp[]) >>
  rw[cmp_flip_iszero_inv_def] >> rpt strip_tac >>
  rename1 `MEM fi' all_insts` >>
  `fi'.inst_id <> inst.inst_id` by (CCONTR_TAC >> gvs[]) >>
  `~MEM out inst.inst_outputs` by metis_tac[] >>
  `out <> iz_out` by gvs[] >>
  gvs[update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  qpat_x_assum `cmp_flip_iszero_inv _ _ _ _`
    (fn th => mp_tac (REWRITE_RULE [cmp_flip_iszero_inv_def] th)) >>
  disch_then (qspecl_then [`fi'`, `out`] mp_tac) >>
  simp[] >> strip_tac >> gvs[lookup_var_def]
QED

(* Insert v1=0w case: both Abort *)
Triviality per_inst_lr_insert_zero[local]:
  !dead flips all_insts inst fuel ctx s1 s2 mid cmp_out fresh cmp_id.
    state_equiv dead s1 s2 /\
    inst.inst_opcode = ASSERT /\
    inst.inst_operands = [Var cmp_out] /\
    ALOOKUP flips inst.inst_id = NONE /\
    fresh IN dead /\
    lookup_var cmp_out s1 = SOME 0w /\
    lookup_var cmp_out s2 = SOME 1w
    ==>
    lift_result
      (\s1' s2'. state_equiv dead s1' s2' /\
                 cmp_flip_iszero_inv flips all_insts s1' s2')
      (execution_equiv dead) (execution_equiv dead)
      (step_inst_base inst s1)
      (run_insts fuel ctx
        [<| inst_id := ao_fresh_id mid cmp_id 0; inst_opcode := ISZERO;
            inst_operands := [Var cmp_out]; inst_outputs := [fresh] |>;
         inst with inst_operands := [Var fresh]] s2)
Proof
  rpt strip_tac >>
  `step_inst_base inst s1 =
   Abort Revert_abort (set_returndata [] (revert_state s1))` by
    simp[step_inst_base_def, exec_pure1_def, eval_operand_def] >>
  `step_inst_base
    <|inst_id := ao_fresh_id mid cmp_id 0; inst_opcode := ISZERO;
      inst_operands := [Var cmp_out]; inst_outputs := [fresh]|> s2 =
   OK (update_var fresh (bool_to_word (1w = 0w)) s2)` by
    (irule iszero_step_known >> simp[]) >>
  gvs[bool_to_word_def] >>
  `step_inst_base (inst with inst_operands := [Var fresh])
     (update_var fresh 0w s2) =
   Abort Revert_abort (set_returndata []
     (revert_state (update_var fresh 0w s2)))` by
    simp[step_inst_base_def, exec_pure1_def, eval_operand_def,
         update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  `run_insts fuel ctx
    [<|inst_id := ao_fresh_id mid cmp_id 0; inst_opcode := ISZERO;
       inst_operands := [Var cmp_out]; inst_outputs := [fresh]|>;
     inst with inst_operands := [Var fresh]] s2 =
   Abort Revert_abort (set_returndata []
     (revert_state (update_var fresh 0w s2)))` by
    (irule run_insts_pair_ok_fst >> simp[]) >>
  gvs[stateEquivTheory.lift_result_def] >>
  irule revert_set_rd_execution_equiv >>
  irule update_dead_var_right_execution_equiv >> simp[] >>
  irule state_equiv_imp_execution_equiv >> simp[]
QED

(* Insert v1<>0w case: both OK *)
Triviality per_inst_lr_insert_nonzero[local]:
  !dead flips all_insts inst fuel ctx s1 s2 mid cmp_out fresh cmp_id v1.
    state_equiv dead s1 s2 /\
    cmp_flip_iszero_inv flips all_insts s1 s2 /\
    inst.inst_opcode = ASSERT /\
    inst.inst_operands = [Var cmp_out] /\
    ALOOKUP flips inst.inst_id = NONE /\
    fresh IN dead /\
    (!fi' out. MEM fi' all_insts /\ ALOOKUP flips fi'.inst_id <> NONE /\
               MEM out fi'.inst_outputs ==> fresh <> out) /\
    lookup_var cmp_out s1 = SOME v1 /\ v1 <> 0w /\
    lookup_var cmp_out s2 = SOME 0w
    ==>
    lift_result
      (\s1' s2'. state_equiv dead s1' s2' /\
                 cmp_flip_iszero_inv flips all_insts s1' s2')
      (execution_equiv dead) (execution_equiv dead)
      (step_inst_base inst s1)
      (run_insts fuel ctx
        [<| inst_id := ao_fresh_id mid cmp_id 0; inst_opcode := ISZERO;
            inst_operands := [Var cmp_out]; inst_outputs := [fresh] |>;
         inst with inst_operands := [Var fresh]] s2)
Proof
  rpt strip_tac >>
  `step_inst_base inst s1 = OK s1` by
    (irule assert_step_nonzero >> simp[]) >>
  `step_inst_base
    <|inst_id := ao_fresh_id mid cmp_id 0; inst_opcode := ISZERO;
      inst_operands := [Var cmp_out]; inst_outputs := [fresh]|> s2 =
   OK (update_var fresh (bool_to_word (0w = 0w)) s2)` by
    (irule iszero_step_known >> simp[]) >>
  gvs[bool_to_word_def] >>
  `step_inst_base (inst with inst_operands := [Var fresh])
     (update_var fresh 1w s2) = OK (update_var fresh 1w s2)` by
    (irule assert_step_nonzero >>
     simp[update_var_def, lookup_var_def,
          finite_mapTheory.FLOOKUP_UPDATE]) >>
  `run_insts fuel ctx
    [<|inst_id := ao_fresh_id mid cmp_id 0; inst_opcode := ISZERO;
       inst_operands := [Var cmp_out]; inst_outputs := [fresh]|>;
     inst with inst_operands := [Var fresh]] s2 =
   OK (update_var fresh 1w s2)` by
    (irule run_insts_pair_ok_fst >> simp[]) >>
  gvs[stateEquivTheory.lift_result_def] >>
  irule per_inst_insert_nonzero_equiv >> gvs[]
QED

(* Flip case: lift_result version *)
Triviality per_inst_lr_flip[local]:
  !dead flips all_insts inst fuel ctx s1 s2
   out_var orig_op1 w.
    state_equiv dead s1 s2 /\
    cmp_flip_iszero_inv flips all_insts s1 s2 /\
    inst.inst_opcode <> INVOKE /\
    ~is_terminator inst.inst_opcode /\
    is_comparator inst.inst_opcode /\
    inst.inst_operands = [orig_op1; Lit w] /\
    inst.inst_outputs = [out_var] /\
    out_var IN dead /\
    (!x. orig_op1 = Var x ==> x NOTIN dead) /\
    (inst.inst_opcode = GT ==> w <> 0w - 1w) /\
    (inst.inst_opcode = LT ==> w <> 0w) /\
    (inst.inst_opcode = SGT ==> w <> i2w INT256_MAX) /\
    (inst.inst_opcode = SLT ==> w <> i2w INT256_MIN) /\
    (!fi. MEM fi all_insts /\ fi.inst_id <> inst.inst_id /\
          ALOOKUP flips fi.inst_id <> NONE ==>
          !out. MEM out fi.inst_outputs ==> ~MEM out inst.inst_outputs)
    ==>
    lift_result
      (\s1' s2'. state_equiv dead s1' s2' /\
                 cmp_flip_iszero_inv flips all_insts s1' s2')
      (execution_equiv dead) (execution_equiv dead)
      (step_inst_base inst s1)
      (step_inst_base (inst with
        <| inst_opcode := flip_comparison_opcode inst.inst_opcode;
           inst_operands := [orig_op1; Lit (if inst.inst_opcode = GT \/
             inst.inst_opcode = SGT then w + 1w else w - 1w)] |>) s2)
Proof
  rpt strip_tac >>
  `eval_operand orig_op1 s1 = eval_operand orig_op1 s2` by
    (irule eval_operand_equiv >> qexists_tac `dead` >> simp[]) >>
  Cases_on `eval_operand orig_op1 s1`
  >- (gvs[is_comparator_def] >>
      gvs[step_inst_base_def, exec_pure2_def, eval_operand_def,
          flip_comparison_opcode_def, stateEquivTheory.lift_result_def])
  >> rename1 `eval_operand orig_op1 s1 = SOME v` >>
  `?r1 r2.
     step_inst_base inst s1 = OK (update_var out_var r1 s1) /\
     step_inst_base (inst with
       <| inst_opcode := flip_comparison_opcode inst.inst_opcode;
          inst_operands := [orig_op1; Lit (if inst.inst_opcode = GT \/
            inst.inst_opcode = SGT then w + 1w else w - 1w)] |>) s2 =
     OK (update_var out_var r2 s2) /\
     r2 = bool_to_word (r1 = 0w)` by
    (irule flip_step_gives_iszero >> gvs[] >> metis_tac[]) >>
  gvs[stateEquivTheory.lift_result_def] >>
  conj_tac >- (irule update_dead_var_state_equiv >> simp[]) >>
  irule iszero_inv_frame >>
  qexistsl_tac [`ctx`, `fuel`, `inst`, `s1`, `s2`] >>
  simp[step_inst_non_invoke] >> rpt conj_tac >> rpt strip_tac >>
  gvs[update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

(* Per-instruction lift_result: dispatches to case helpers *)
Triviality per_inst_lr[local]:
  !dead mid flips removes inserts inst all_insts fuel ctx s1 s2.
    state_equiv dead s1 s2 /\
    cmp_flip_iszero_inv flips all_insts s1 s2 /\
    MEM inst all_insts /\
    inst.inst_opcode <> INVOKE /\
    ~is_terminator inst.inst_opcode /\
    (~MEM inst.inst_id removes /\
     ALOOKUP inserts inst.inst_id = NONE ==>
     !x. MEM (Var x) inst.inst_operands ==> x NOTIN dead) /\
    (!fi out. MEM fi all_insts /\ ALOOKUP flips fi.inst_id <> NONE /\
             MEM out fi.inst_outputs ==> out IN dead) /\
    (!fi. MEM fi all_insts /\ fi.inst_id <> inst.inst_id /\
          ALOOKUP flips fi.inst_id <> NONE ==>
          !out. MEM out fi.inst_outputs ==> ~MEM out inst.inst_outputs) /\
    (!id. ALOOKUP flips id <> NONE ==>
     ~MEM id removes /\ ALOOKUP inserts id = NONE) /\
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
         (inst.inst_opcode = SLT ==> w <> i2w INT256_MIN)) /\
    (MEM inst.inst_id removes ==>
      ?cmp_out iz_out fi.
        inst.inst_opcode = ISZERO /\
        inst.inst_operands = [Var cmp_out] /\
        inst.inst_outputs = [iz_out] /\
        MEM fi all_insts /\
        ALOOKUP flips fi.inst_id <> NONE /\
        MEM cmp_out fi.inst_outputs) /\
    (!cmp_out fresh cmp_id.
      ALOOKUP inserts inst.inst_id = SOME (cmp_out, fresh, cmp_id) ==>
      inst.inst_opcode = ASSERT /\
      inst.inst_operands = [Var cmp_out] /\
      fresh IN dead /\
      (!fi' out. MEM fi' all_insts /\ ALOOKUP flips fi'.inst_id <> NONE /\
                 MEM out fi'.inst_outputs ==> fresh <> out) /\
      (?fi. MEM fi all_insts /\
            ALOOKUP flips fi.inst_id <> NONE /\
            MEM cmp_out fi.inst_outputs))
    ==>
    lift_result
      (\s1' s2'. state_equiv dead s1' s2' /\
                 cmp_flip_iszero_inv flips all_insts s1' s2')
      (execution_equiv dead) (execution_equiv dead)
      (step_inst fuel ctx inst s1)
      (run_insts fuel ctx
        (ao_cmp_flip_apply_inst mid flips removes inserts inst) s2)
Proof
  cheat
QED

(* Body simulation with lift_result conclusion *)
Triviality body_lr[local]:
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
         (inst.inst_opcode = SLT ==> w <> i2w INT256_MIN)) /\
    (!inst. MEM inst body_insts /\ MEM inst.inst_id removes ==>
      ?cmp_out iz_out fi.
        inst.inst_opcode = ISZERO /\
        inst.inst_operands = [Var cmp_out] /\
        inst.inst_outputs = [iz_out] /\
        MEM fi all_insts /\
        ALOOKUP flips fi.inst_id <> NONE /\
        MEM cmp_out fi.inst_outputs) /\
    (!inst cmp_out fresh cmp_id.
      MEM inst body_insts /\
      ALOOKUP inserts inst.inst_id = SOME (cmp_out, fresh, cmp_id) ==>
      inst.inst_opcode = ASSERT /\
      inst.inst_operands = [Var cmp_out] /\
      fresh IN dead /\
      (!fi' out. MEM fi' all_insts /\ ALOOKUP flips fi'.inst_id <> NONE /\
                 MEM out fi'.inst_outputs ==> fresh <> out) /\
      (?fi. MEM fi all_insts /\
            ALOOKUP flips fi.inst_id <> NONE /\
            MEM cmp_out fi.inst_outputs))
    ==>
    lift_result
      (\s1' s2'. state_equiv dead s1' s2' /\
                 cmp_flip_iszero_inv flips all_insts s1' s2')
      (execution_equiv dead) (execution_equiv dead)
      (run_insts fuel ctx body_insts s1)
      (run_insts fuel ctx
        (FLAT (MAP (ao_cmp_flip_apply_inst mid flips removes inserts)
                   body_insts)) s2)
Proof
  Induct_on `body_insts`
  >- simp[run_insts_def, stateEquivTheory.lift_result_def]
  >> rpt gen_tac >> strip_tac >>
  `~is_terminator h.inst_opcode /\ h.inst_opcode <> INVOKE /\
   EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE)
         body_insts` by
    (qpat_x_assum `EVERY _ (_::_)` mp_tac >>
     simp[listTheory.EVERY_DEF]) >>
  `lift_result
     (\s1' s2'. state_equiv dead s1' s2' /\
                cmp_flip_iszero_inv flips all_insts s1' s2')
     (execution_equiv dead) (execution_equiv dead)
     (step_inst fuel ctx h s1)
     (run_insts fuel ctx
       (ao_cmp_flip_apply_inst mid flips removes inserts h) s2)` by
    (irule per_inst_lr >> simp[] >>
     rpt conj_tac >> simp[] >>
     metis_tac[listTheory.MEM]) >>
  Cases_on `step_inst fuel ctx h s1` >>
  Cases_on `run_insts fuel ctx
    (ao_cmp_flip_apply_inst mid flips removes inserts h) s2` >>
  gvs[stateEquivTheory.lift_result_def]
  >- ( (* OK, OK: apply IH *)
    simp[Once run_insts_def, run_insts_append] >>
    `!inst. MEM inst body_insts ==> MEM inst (h::body_insts)` by
      simp[listTheory.MEM] >>
    first_x_assum irule >> simp[] >>
    rpt conj_tac >> simp[] >> metis_tac[])
  >> (* Non-OK matching: propagate through remaining body *)
  simp[Once run_insts_def, run_insts_append]
QED

(* exec_block_skip_prefix for body starting at idx 0 *)
Triviality exec_block_skip_body[local]:
  !bb fuel ctx s s'.
    bb_well_formed bb /\
    (!inst. MEM inst bb.bb_instructions ==> inst.inst_opcode <> INVOKE) /\
    run_insts fuel ctx (FRONT bb.bb_instructions) s = OK s' ==>
    exec_block fuel ctx bb (s with vs_inst_idx := 0) =
    exec_block fuel ctx bb (s' with vs_inst_idx :=
      LENGTH (FRONT bb.bb_instructions))
Proof
  rpt strip_tac >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  qspecl_then [`FRONT bb.bb_instructions`, `fuel`, `ctx`, `bb`, `s`, `0`, `s'`]
    mp_tac exec_block_skip_prefix >>
  simp[] >> disch_then irule >> rpt conj_tac
  >- (imp_res_tac rich_listTheory.FRONT_LENGTH >>
      gvs[listTheory.LENGTH_NIL])
  >- (drule front_non_terminators >> strip_tac >>
      fs[listTheory.EVERY_MEM] >> rpt strip_tac >>
      first_x_assum (qspec_then `i` mp_tac) >> simp[] >>
      `MEM i bb.bb_instructions` by
        metis_tac[rich_listTheory.MEM_FRONT, listTheory.NULL_EQ] >>
      metis_tac[])
  >- (rpt strip_tac >> simp[] >>
      irule (GSYM rich_listTheory.EL_FRONT) >>
      gvs[listTheory.NULL_EQ])
QED

(* When body returns non-OK, exec_block returns same constructor.
   States in Abort results are execution_equiv {} (differ only in inst_idx). *)
Triviality exec_block_body_non_ok[local]:
  !prefix fuel ctx bb s j.
    j + LENGTH prefix <= LENGTH bb.bb_instructions /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) prefix /\
    (!k. k < LENGTH prefix ==> EL (j + k) bb.bb_instructions = EL k prefix) /\
    ~(?v. run_insts fuel ctx prefix s = OK v)
    ==>
    (?e. run_insts fuel ctx prefix s = Error e /\
         ?e'. exec_block fuel ctx bb (s with vs_inst_idx := j) = Error e') \/
    (?a s1. run_insts fuel ctx prefix s = Abort a s1 /\
            ?s2. exec_block fuel ctx bb (s with vs_inst_idx := j) = Abort a s2 /\
                 execution_equiv {} s1 s2)
Proof
  Induct >> rw[run_insts_def] >>
  rename1 `_ :: prefix` >>
  `j < LENGTH bb.bb_instructions` by simp[] >>
  `h = EL j bb.bb_instructions` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `~is_terminator h.inst_opcode /\ h.inst_opcode <> INVOKE` by gvs[] >>
  `step_inst fuel ctx h (s with vs_inst_idx := j) =
   exec_result_map (\s'. s' with vs_inst_idx := j)
     (step_inst fuel ctx h s)` by
    (irule step_inst_idx_indep >> simp[]) >>
  Cases_on `step_inst fuel ctx h s` >>
  gvs[instIdxIndepTheory.exec_result_map_def]
  >- ( (* OK: head succeeds, tail is non-OK *)
    rename1 `_ = OK s1` >>
    `s1.vs_inst_idx = s.vs_inst_idx` by
      metis_tac[step_inst_preserves_inst_idx] >>
    first_x_assum (qspecl_then [`fuel`, `ctx`, `bb`, `s1`, `SUC j`] mp_tac) >>
    simp[arithmeticTheory.ADD_CLAUSES] >>
    impl_tac
    >- (rpt strip_tac >>
        first_x_assum (qspec_then `SUC k` mp_tac) >>
        simp[arithmeticTheory.ADD_CLAUSES])
    >> strip_tac >>
    ONCE_REWRITE_TAC[exec_block_def] >>
    simp[get_instruction_def] >> gvs[])
  >> (* Non-OK first step: propagates through exec_block *)
  ONCE_REWRITE_TAC[exec_block_def] >>
  simp[get_instruction_def] >>
  gvs[instIdxIndepTheory.exec_result_map_def] >>
  TRY (disj1_tac >> metis_tac[]) >>
  TRY (disj2_tac >> irule_at Any EQ_REFL >> simp[execution_equiv_def,
       lookup_var_def])
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

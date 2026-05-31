(* Obligation: cmp_flip preserves block execution up to dead variables. *)
Theory aoCmpFlipObligation
Ancestors
  algebraicOptDefs aoCmpFlipSim
  analysisSimDefs analysisSimProofsBase
  stateEquiv stateEquivProps stateEquivProofs execEquivProps passSimulationProps
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

(* INVOKE step_inst preserves result_equiv: callee gets identical state
   because setup_callee zeroes vs_vars and all other fields are equal
   under state_equiv, so run_blocks produces identical results. *)
Triviality eval_operands_equiv[local]:
  !ops dead s1 s2.
    state_equiv dead s1 s2 /\
    (!x. MEM (Var x) ops ==> x NOTIN dead) ==>
    eval_operands ops s1 = eval_operands ops s2
Proof
  Induct >> simp[eval_operands_def] >> rpt strip_tac >>
  `eval_operand h s1 = eval_operand h s2` by
    (irule eval_operand_equiv >> qexists_tac `dead` >> simp[] >>
     Cases_on `h` >> simp[] >> metis_tac[]) >>
  gvs[] >> Cases_on `eval_operand h s2` >> gvs[] >>
  `eval_operands ops s1 = eval_operands ops s2` by
    (first_x_assum irule >> qexists_tac `dead` >> simp[]) >>
  gvs[]
QED

Triviality merge_callee_state_equiv[local]:
  !dead s1 s2 cs.
    state_equiv dead s1 s2 ==>
    state_equiv dead (merge_callee_state s1 cs) (merge_callee_state s2 cs)
Proof
  rw[merge_callee_state_def, state_equiv_def, execution_equiv_def,
     lookup_var_def]
QED

Triviality foldl_update_var_state_equiv[local]:
  !pairs dead s1 s2.
    state_equiv dead s1 s2 ==>
    state_equiv dead
      (FOLDL (\s' (out, val). update_var out val s') s1 pairs)
      (FOLDL (\s' (out, val). update_var out val s') s2 pairs)
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  PairCases_on `h` >> simp[] >>
  first_x_assum irule >>
  gvs[state_equiv_def, execution_equiv_def, update_var_def,
      lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> IF_CASES_TAC >> gvs[]
QED

Triviality bind_outputs_state_equiv[local]:
  !outs vals dead s1 s2.
    state_equiv dead s1 s2 ==>
    case (bind_outputs outs vals s1, bind_outputs outs vals s2) of
      (SOME s1', SOME s2') => state_equiv dead s1' s2'
    | (NONE, NONE) => T
    | _ => F
Proof
  rpt strip_tac >> simp[bind_outputs_def] >>
  IF_CASES_TAC >> simp[] >>
  irule foldl_update_var_state_equiv >> simp[]
QED

Triviality step_inst_invoke_result_equiv[local]:
  !fuel ctx dead inst s1 s2.
    state_equiv dead s1 s2 /\
    inst.inst_opcode = INVOKE /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN dead) ==>
    result_equiv dead (step_inst fuel ctx inst s1) (step_inst fuel ctx inst s2)
Proof
  rpt strip_tac >>
  simp_tac std_ss [Once step_inst_def] >>
  simp_tac std_ss [Once step_inst_def] >>
  Cases_on `decode_invoke inst`
  >- simp[result_equiv_def] >>
  PairCases_on `x` >>
  rename1 `SOME (cname, arg_ops)` >>
  `inst.inst_operands = Label cname :: arg_ops` by
    (qpat_x_assum `decode_invoke _ = _` mp_tac >>
     simp[decode_invoke_def, AllCaseEqs()] >>
     Cases_on `inst.inst_operands` >> simp[]) >>
  simp[] >>
  Cases_on `lookup_function cname ctx.ctx_functions`
  >- simp[result_equiv_def] >>
  rename1 `SOME callee_fn` >>
  `eval_operands arg_ops s1 = eval_operands arg_ops s2` by
    (irule eval_operands_equiv >> qexists_tac `dead` >> simp[]) >>
  simp[] >>
  Cases_on `eval_operands arg_ops s2`
  >- simp[result_equiv_def] >>
  rename1 `SOME args` >> simp[] >>
  `setup_callee callee_fn args s1 = setup_callee callee_fn args s2` by
    (simp[setup_callee_def] >> IF_CASES_TAC >> simp[] >>
     simp[venomStateTheory.venom_state_component_equality] >>
     fs[state_equiv_def, execution_equiv_def]) >>
  simp[] >>
  Cases_on `setup_callee callee_fn args s2`
  >- simp[result_equiv_def] >>
  rename1 `SOME callee_s` >> simp[] >>
  Cases_on `run_blocks fuel ctx callee_fn callee_s` >>
  simp[result_equiv_def] >>
  `state_equiv dead (merge_callee_state s1 v) (merge_callee_state s2 v)` by
    (irule merge_callee_state_equiv >> simp[]) >>
  `case (bind_outputs inst.inst_outputs l (merge_callee_state s1 v),
         bind_outputs inst.inst_outputs l (merge_callee_state s2 v)) of
     (SOME s1', SOME s2') => state_equiv dead s1' s2'
   | (NONE, NONE) => T
   | _ => F` by
    (irule bind_outputs_state_equiv >> simp[]) >>
  Cases_on `bind_outputs inst.inst_outputs l (merge_callee_state s1 v)` >>
  Cases_on `bind_outputs inst.inst_outputs l (merge_callee_state s2 v)` >>
  gvs[result_equiv_def, state_equiv_def, execution_equiv_def]
QED

(* Case 1: Unchanged instruction — same inst on both sides *)
Triviality per_inst_unchanged[local]:
  !dead flips all_insts inst fuel ctx s1 s2.
    state_equiv dead s1 s2 /\
    cmp_flip_iszero_inv flips all_insts s1 s2 /\
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
    (Cases_on `inst.inst_opcode = INVOKE`
     >- (irule step_inst_invoke_result_equiv >> simp[])
     >> irule step_inst_result_equiv >> simp[]) >>
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
  `inst.inst_opcode <> INVOKE` by (gvs[is_comparator_def]) >>
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

(* Like scan_inserts_are_assert but uses MEM tuple directly,
   connecting the ALOOKUP value field cmp_out to the DFG variable *)
Triviality scan_insert_mem_assert[local]:
  !dfg insts flips removes inserts aid cmp_out fresh cmp_id.
    ao_cmp_flip_scan dfg insts = (flips, removes, inserts) /\
    MEM (aid, cmp_out, fresh, cmp_id) inserts ==>
    ?ui. MEM ui (dfg_get_uses dfg cmp_out) /\ ui.inst_id = aid /\
         ui.inst_opcode = ASSERT
Proof
  Induct_on `insts`
  >- simp[ao_cmp_flip_scan_def]
  >> rpt gen_tac >> strip_tac >>
  Cases_on `ao_cmp_flip_scan dfg insts` >> Cases_on `r` >>
  rename1 `_ = (fl0, rm0, ins0)` >>
  `inserts = ins0 \/
   (?v ui. inserts = (ui.inst_id, v, ao_fresh_var h.inst_id "iz",
                      h.inst_id) :: ins0 /\
           MEM ui (dfg_get_uses dfg v) /\ ui.inst_opcode = ASSERT)` by
    metis_tac[scan_step_inserts_subset] >>
  gvs[] >> metis_tac[]
QED

(* Insert tuple structure: fresh = ao_fresh_var cmp_id "iz", cmp_id in insts *)
Triviality scan_insert_fresh_form[local]:
  !dfg insts flips removes inserts aid out_var fresh cmp_id.
    ao_cmp_flip_scan dfg insts = (flips, removes, inserts) /\
    MEM (aid, out_var, fresh, cmp_id) inserts ==>
    fresh = ao_fresh_var cmp_id "iz" /\
    ?i. MEM i insts /\ i.inst_id = cmp_id /\ is_comparator i.inst_opcode
Proof
  Induct_on `insts`
  >- simp[ao_cmp_flip_scan_def]
  >> rpt gen_tac >> strip_tac >>
  Cases_on `ao_cmp_flip_scan dfg insts` >> Cases_on `r` >>
  rename1 `_ = (fl0, rm0, ins0)` >>
  `inserts = ins0 \/
   (?v ui. inserts = (ui.inst_id, v, ao_fresh_var h.inst_id "iz",
                      h.inst_id) :: ins0 /\
           MEM ui (dfg_get_uses dfg v) /\ ui.inst_opcode = ASSERT)` by
    metis_tac[scan_step_inserts_subset] >>
  gvs[]
  >- metis_tac[]
  >> (* Entry is either h (head) or in ins0 (tail) *)
  gvs[listTheory.MEM]
  >- (* Head: cmp_id = h.inst_id, need is_comparator h *)
     (drule_all scan_step_detail >>
      strip_tac >> gvs[] >> metis_tac[])
  >- metis_tac[]
QED

(* Remove entries pair with a flip: removed ISZERO uses flip output *)
Triviality scan_remove_has_flip[local]:
  !dfg insts flips removes inserts id.
    ao_cmp_flip_scan dfg insts = (flips, removes, inserts) /\
    MEM id removes ==>
    ?fi out_var.
      MEM fi insts /\ ALOOKUP flips fi.inst_id <> NONE /\
      fi.inst_outputs = [out_var] /\
      MEM (HD (dfg_get_uses dfg out_var)) (dfg_get_uses dfg out_var) /\
      (HD (dfg_get_uses dfg out_var)).inst_id = id /\
      (HD (dfg_get_uses dfg out_var)).inst_opcode = ISZERO
Proof
  Induct_on `insts`
  >- simp[ao_cmp_flip_scan_def]
  >> rpt gen_tac >> strip_tac >>
  Cases_on `ao_cmp_flip_scan dfg insts` >> Cases_on `r` >>
  rename1 `_ = (fl0, rm0, ins0)` >>
  `removes = rm0 \/
   (?v ui. removes = ui.inst_id :: rm0 /\
           MEM ui (dfg_get_uses dfg v) /\ ui.inst_opcode = ISZERO)` by
    metis_tac[scan_step_removes_subset] >>
  gvs[]
  >- (first_x_assum drule_all >> strip_tac >>
      qexistsl_tac [`fi`, `out_var`] >> simp[] >>
      `flips = fl0 \/
       (?opc w op1. flips = (h.inst_id, opc, w, op1) :: fl0 /\
                    is_comparator h.inst_opcode)` by
        metis_tac[scan_step_flips_subset] >>
      gvs[] >> Cases_on `fi.inst_id = h.inst_id` >> gvs[])
  >> drule_all scan_step_detail >> strip_tac >> gvs[]
  >- (* id = new remove entry *)
     (qexistsl_tac [`h`, `out_var`] >> simp[] >>
      `dfg_get_uses dfg out_var <> []` by
        (Cases_on `dfg_get_uses dfg out_var` >> gvs[]) >>
      simp[rich_listTheory.HEAD_MEM])
  >> (* id in old rm0 — use IH *)
  first_x_assum drule_all >> strip_tac >>
  qexistsl_tac [`fi`, `out_var'`] >> gvs[]
QED

(* Insert entries pair with a flip *)
Triviality scan_insert_has_flip[local]:
  !dfg insts flips removes inserts inst_id cmp_out fresh cmp_id.
    ao_cmp_flip_scan dfg insts = (flips, removes, inserts) /\
    ALOOKUP inserts inst_id = SOME (cmp_out, fresh, cmp_id) ==>
    ?fi.
      MEM fi insts /\ ALOOKUP flips fi.inst_id <> NONE /\
      MEM cmp_out fi.inst_outputs /\
      fi.inst_id = cmp_id
Proof
  Induct_on `insts`
  >- simp[ao_cmp_flip_scan_def]
  >> rpt gen_tac >> strip_tac >>
  Cases_on `ao_cmp_flip_scan dfg insts` >> Cases_on `r` >>
  rename1 `_ = (fl0, rm0, ins0)` >>
  `inserts = ins0 \/
   (?v ui. inserts = (ui.inst_id, v, ao_fresh_var h.inst_id "iz",
                      h.inst_id) :: ins0 /\
           MEM ui (dfg_get_uses dfg v) /\ ui.inst_opcode = ASSERT)` by
    metis_tac[scan_step_inserts_subset] >>
  gvs[]
  >- (first_x_assum drule_all >> strip_tac >>
      qexists_tac `fi` >> simp[] >>
      `flips = fl0 \/
       (?opc w op1. flips = (h.inst_id, opc, w, op1) :: fl0 /\
                    is_comparator h.inst_opcode)` by
        metis_tac[scan_step_flips_subset] >>
      gvs[] >> Cases_on `fi.inst_id = h.inst_id` >> gvs[])
  >> drule_all scan_step_detail >> strip_tac >> gvs[] >>
  Cases_on `inst_id = ui.inst_id` >> gvs[]
  >- (qexists_tac `h` >> gvs[])
  >> first_x_assum drule_all >> strip_tac >>
  qexists_tac `fi` >> gvs[]
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

(* ===== Non-NULL case: helpers + main proof ===== *)

Triviality find_mem_local[local]:
  !P l x. FIND P l = SOME x ==> MEM x l
Proof
  Induct_on `l`
  >- simp[listTheory.FIND_thm]
  >> rpt gen_tac >> simp[listTheory.FIND_thm] >>
     IF_CASES_TAC >> gvs[] >> strip_tac >> res_tac >> simp[]
QED

(* mem_fn_insts_blocks shared from passSimulationProps *)

Triviality block_inst_in_fn_insts[local]:
  !lbl fn bb inst.
    lookup_block lbl fn.fn_blocks = SOME bb /\
    MEM inst bb.bb_instructions ==>
    MEM inst (fn_insts fn)
Proof
  rpt strip_tac >> simp[fn_insts_def] >>
  irule mem_fn_insts_blocks >> qexists_tac `bb` >> simp[] >>
  gvs[lookup_block_def] >> irule find_mem_local >> metis_tac[]
QED

(* For a terminator, step_inst_base at different idx values gives
   results that are identical modulo idx — hence execution_equiv. *)
Triviality step_inst_base_idx_exec_equiv[local]:
  !vars inst s n1 n2.
    is_terminator inst.inst_opcode ==>
    lift_result (execution_equiv vars) (execution_equiv vars)
      (execution_equiv vars)
      (step_inst_base inst (s with vs_inst_idx := n1))
      (step_inst_base inst (s with vs_inst_idx := n2))
Proof
  rpt strip_tac >>
  `exec_result_map (\s'. s' with vs_inst_idx := 0)
     (step_inst_base inst (s with vs_inst_idx := n1)) =
   exec_result_map (\s'. s' with vs_inst_idx := 0)
     (step_inst_base inst (s with vs_inst_idx := n2))` by
    metis_tac[instIdxIndepTheory.terminator_step_inst_base_idx_norm0] >>
  Cases_on `step_inst_base inst (s with vs_inst_idx := n1)` >>
  Cases_on `step_inst_base inst (s with vs_inst_idx := n2)` >>
  gvs[instIdxIndepTheory.exec_result_map_def,
      stateEquivTheory.lift_result_def,
      stateEquivTheory.execution_equiv_def, lookup_var_def,
      venomStateTheory.venom_state_component_equality]
QED

Triviality terminator_ok_idx_zero[local]:
  !inst s s'.
    is_terminator inst.inst_opcode /\
    step_inst_base inst s = OK s' ==>
    s'.vs_inst_idx = 0
Proof
  rpt strip_tac >>
  gvs[step_inst_base_def, is_terminator_def, jump_to_def,
      AllCaseEqs()]
QED

(* Terminator exec_block simulation with different indices.
   Takes state_equiv (ensures matching current_bb/prev_bb needed for
   step_inst_base_result_equiv). Conclusion uses state_equiv for OK case:
   terminators returning OK (JMP/JNZ) set vs_inst_idx := 0 and vs_current_bb/
   vs_prev_bb deterministically, so state_equiv is preserved. *)
Triviality exec_block_same_terminator[local]:
  !dead fuel ctx bb1 bb2 s1 s2 n1 n2 inst.
    state_equiv dead s1 s2 /\
    n1 < LENGTH bb1.bb_instructions /\
    n2 < LENGTH bb2.bb_instructions /\
    EL n1 bb1.bb_instructions = inst /\
    EL n2 bb2.bb_instructions = inst /\
    is_terminator inst.inst_opcode /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN dead)
    ==>
    lift_result (state_equiv dead) (execution_equiv dead)
      (execution_equiv dead)
      (exec_block fuel ctx bb1 (s1 with vs_inst_idx := n1))
      (exec_block fuel ctx bb2 (s2 with vs_inst_idx := n2))
Proof
  rpt strip_tac >>
  `inst.inst_opcode <> INVOKE` by (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]) >>
  ONCE_REWRITE_TAC[exec_block_def] >> simp[get_instruction_def] >>
  `step_inst fuel ctx inst (s1 with vs_inst_idx := n1) =
   step_inst_base inst (s1 with vs_inst_idx := n1)` by
    (irule step_inst_non_invoke >> simp[]) >>
  `step_inst fuel ctx inst (s2 with vs_inst_idx := n2) =
   step_inst_base inst (s2 with vs_inst_idx := n2)` by
    (irule step_inst_non_invoke >> simp[]) >>
  simp[] >>
  (* Intermediate: same state s2 but with idx n1 *)
  `state_equiv dead (s1 with vs_inst_idx := n1)
                    (s2 with vs_inst_idx := n1)` by
    (fs[state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  `result_equiv dead
     (step_inst_base inst (s1 with vs_inst_idx := n1))
     (step_inst_base inst (s2 with vs_inst_idx := n1))` by
    (irule step_inst_base_result_equiv >> simp[]) >>
  `lift_result (execution_equiv dead) (execution_equiv dead)
     (execution_equiv dead)
     (step_inst_base inst (s2 with vs_inst_idx := n1))
     (step_inst_base inst (s2 with vs_inst_idx := n2))` by
    (irule step_inst_base_idx_exec_equiv >> simp[]) >>
  qabbrev_tac `r1 = step_inst_base inst (s1 with vs_inst_idx := n1)` >>
  qabbrev_tac `r12 = step_inst_base inst (s2 with vs_inst_idx := n1)` >>
  qabbrev_tac `r2 = step_inst_base inst (s2 with vs_inst_idx := n2)` >>
  Cases_on `r1` >> Cases_on `r12` >> Cases_on `r2` >>
  gvs[stateEquivTheory.lift_result_def,
      result_equiv_is_lift_result] >>
  TRY (irule execution_equiv_trans >> metis_tac[]) >>
  (* OK-OK-OK case: have state_equiv dead v v', execution_equiv dead v' v''.
     Need state_equiv dead v v'' for the lift_result goal. *)
  `v'.vs_inst_idx = 0` by
    (irule terminator_ok_idx_zero >>
     qexistsl_tac [`bb1.bb_instructions❲n1❳`, `s2 with vs_inst_idx := n1`] >>
     simp[]) >>
  `v''.vs_inst_idx = 0` by
    (irule terminator_ok_idx_zero >>
     qexistsl_tac [`bb1.bb_instructions❲n1❳`, `s2 with vs_inst_idx := n2`] >>
     simp[]) >>
  `v'.vs_current_bb = v''.vs_current_bb /\
   v'.vs_prev_bb = v''.vs_prev_bb` by
    (`exec_result_map (\s'. s' with vs_inst_idx := 0)
        (step_inst_base bb1.bb_instructions❲n1❳ (s2 with vs_inst_idx := n1)) =
      exec_result_map (\s'. s' with vs_inst_idx := 0)
        (step_inst_base bb1.bb_instructions❲n1❳ (s2 with vs_inst_idx := n2))`
       by metis_tac[instIdxIndepTheory.terminator_step_inst_base_idx_norm0] >>
     gvs[instIdxIndepTheory.exec_result_map_def,
         venomStateTheory.venom_state_component_equality]) >>
  Cases_on `v.vs_halted` >> Cases_on `v''.vs_halted` >>
  gvs[stateEquivTheory.lift_result_def,
      stateEquivTheory.state_equiv_def,
      stateEquivTheory.execution_equiv_def, lookup_var_def]
QED

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
    (Cases_on `inst.inst_opcode = INVOKE`
     >- (irule step_inst_invoke_result_equiv >> simp[])
     >> irule step_inst_result_equiv >> simp[]) >>
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
  `!v. lookup_var fresh (update_var fresh v s2) = SOME v` by
    simp[update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[run_insts_def, step_inst_non_invoke,
       step_inst_base_def, exec_pure1_def, eval_operand_def,
       bool_to_word_def,
       stateEquivTheory.lift_result_def] >>
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
  `!v. lookup_var fresh (update_var fresh v s2) = SOME v` by
    simp[update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[run_insts_def, step_inst_non_invoke,
       step_inst_base_def, exec_pure1_def, eval_operand_def,
       bool_to_word_def,
       stateEquivTheory.lift_result_def] >>
  irule per_inst_insert_nonzero_equiv >> gvs[]
QED

(* Flip case: lift_result version *)
Triviality per_inst_lr_flip[local]:
  !dead flips all_insts inst fuel ctx s1 s2
   out_var orig_op1 w.
    state_equiv dead s1 s2 /\
    cmp_flip_iszero_inv flips all_insts s1 s2 /\
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
  `inst.inst_opcode <> INVOKE` by (gvs[is_comparator_def]) >>
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
      `step_inst fuel ctx inst s1 = step_inst_base inst s1` by
        (irule step_inst_non_invoke >> gvs[]) >>
      `step_inst fuel ctx (inst with inst_opcode := ASSIGN) s2 =
       step_inst_base (inst with inst_opcode := ASSIGN) s2` by
        (irule step_inst_non_invoke >> simp[]) >>
      ntac 2 (pop_assum (fn th => REWRITE_TAC [th])) >>
      `?cmp_out iz_out fi.
         inst.inst_opcode = ISZERO /\
         inst.inst_operands = [Var cmp_out] /\
         inst.inst_outputs = [iz_out] /\
         MEM fi all_insts /\
         ALOOKUP flips fi.inst_id <> NONE /\
         MEM cmp_out fi.inst_outputs` by metis_tac[] >>
      irule per_inst_lr_remove >> gvs[] >> metis_tac[])
    >> Cases_on `ALOOKUP inserts inst.inst_id`
    >- ( (* NONE: Unchanged *)
      `ao_cmp_flip_apply_inst mid flips removes inserts inst = [inst]` by
        (irule apply_inst_unchanged >> simp[]) >>
      pop_assum (fn th => REWRITE_TAC [th]) >>
      REWRITE_TAC [run_insts_singleton] >>
      irule per_inst_lr_unchanged >> gvs[] >>
      first_x_assum ACCEPT_TAC)
    >> (* SOME: Insert case *)
    PairCases_on `x` >>
    `ao_cmp_flip_apply_inst mid flips removes inserts inst =
     [<| inst_id := ao_fresh_id mid x2 0; inst_opcode := ISZERO;
         inst_operands := [Var x0]; inst_outputs := [x1] |>;
      inst with inst_operands := [Var x1]]` by
      simp[ao_cmp_flip_apply_inst_def] >>
    pop_assum (fn th => REWRITE_TAC [th]) >>
    `step_inst fuel ctx inst s1 = step_inst_base inst s1` by
      (irule step_inst_non_invoke >> gvs[]) >>
    pop_assum (fn th => REWRITE_TAC [th]) >>
    qpat_x_assum `!_ _ _. SOME _ = SOME _ ==> _`
      (qspecl_then [`x0`, `x1`, `x2`] mp_tac) >> simp[] >> strip_tac >>
    `(IS_SOME (lookup_var x0 s1) <=> IS_SOME (lookup_var x0 s2)) /\
     !v1 v2. lookup_var x0 s1 = SOME v1 /\
             lookup_var x0 s2 = SOME v2 ==>
             v2 = bool_to_word (v1 = 0w)` by
      (qpat_x_assum `cmp_flip_iszero_inv _ _ _ _`
        (fn th => mp_tac (REWRITE_RULE [cmp_flip_iszero_inv_def] th)) >>
       disch_then (qspecl_then [`fi`, `x0`] mp_tac) >> simp[]) >>
    Cases_on `lookup_var x0 s1`
    >- (`lookup_var x0 s2 = NONE` by
          (Cases_on `lookup_var x0 s2` >> gvs[]) >>
        simp[step_inst_base_def, exec_pure1_def, eval_operand_def,
             stateEquivTheory.lift_result_def,
             run_insts_def, step_inst_non_invoke])
    >> rename1 `lookup_var x0 s1 = SOME v1` >>
    `?v2. lookup_var x0 s2 = SOME v2 /\ v2 = bool_to_word (v1 = 0w)` by
      (Cases_on `lookup_var x0 s2` >> gvs[] >> metis_tac[]) >>
    Cases_on `v1 = 0w` >> fs[bool_to_word_def]
    >- (irule per_inst_lr_insert_zero >> simp[])
    >> irule per_inst_lr_insert_nonzero >> simp[] >> metis_tac[])
  >> (* Flip case *)
  PairCases_on `x` >>
  first_x_assum (qspecl_then [`x0`, `x1`, `x2`] mp_tac) >> simp[] >>
  strip_tac >> gvs[] >>
  `inst.inst_opcode <> INVOKE` by (gvs[is_comparator_def]) >>
  `~MEM inst.inst_id removes /\ ALOOKUP inserts inst.inst_id = NONE` by
    (first_x_assum (qspec_then `inst.inst_id` mp_tac) >> simp[]) >>
  `ao_cmp_flip_apply_inst mid flips removes inserts inst =
   [inst with <| inst_opcode := flip_comparison_opcode inst.inst_opcode;
                 inst_operands := [x2; Lit (if inst.inst_opcode = GT \/
                   inst.inst_opcode = SGT then w + 1w else w - 1w)] |>]` by
    simp[ao_cmp_flip_apply_inst_def] >>
  pop_assum (fn th => REWRITE_TAC [th]) >>
  REWRITE_TAC [run_insts_singleton] >>
  `step_inst fuel ctx inst s1 = step_inst_base inst s1` by
    (irule step_inst_non_invoke >> simp[]) >>
  `step_inst fuel ctx
     (inst with <| inst_opcode := flip_comparison_opcode inst.inst_opcode;
                   inst_operands := [x2; Lit (if inst.inst_opcode = GT \/
                     inst.inst_opcode = SGT then w + 1w else w - 1w)] |>) s2 =
   step_inst_base
     (inst with <| inst_opcode := flip_comparison_opcode inst.inst_opcode;
                   inst_operands := [x2; Lit (if inst.inst_opcode = GT \/
                     inst.inst_opcode = SGT then w + 1w else w - 1w)] |>) s2` by
    (irule step_inst_non_invoke >> simp[] >>
     gvs[is_comparator_def] >> simp[flip_comparison_opcode_def]) >>
  gvs[] >>
  irule per_inst_lr_flip >> simp[] >>
  `ALOOKUP flips inst.inst_id <> NONE` by simp[] >>
  metis_tac[listTheory.MEM]
QED

(* Body simulation with lift_result conclusion *)
Triviality body_lr[local]:
  !body_insts mid flips removes inserts dead all_insts fuel ctx s1 s2.
    state_equiv dead s1 s2 /\
    cmp_flip_iszero_inv flips all_insts s1 s2 /\
    EVERY (\i. ~is_terminator i.inst_opcode) body_insts /\
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
  `~is_terminator h.inst_opcode /\
   EVERY (\i. ~is_terminator i.inst_opcode)
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
  simp[Once run_insts_def, run_insts_append,
       stateEquivTheory.lift_result_def]
QED

Triviality step_inst_idx_ok_general[local]:
  !fuel ctx inst s j s'.
    ~is_terminator inst.inst_opcode /\
    step_inst fuel ctx inst s = OK s' ==>
    step_inst fuel ctx inst (s with vs_inst_idx := j) =
      OK (s' with vs_inst_idx := j)
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- simp[invoke_step_inst_idx_OK_only]
  >> (`step_inst fuel ctx inst (s with vs_inst_idx := j) =
       exec_result_map (\s'. s' with vs_inst_idx := j)
         (step_inst fuel ctx inst s)` by
        simp[step_inst_idx_indep] >>
      gvs[instIdxIndepTheory.exec_result_map_def])
QED

Triviality step_inst_idx_non_ok_lift[local]:
  !fuel ctx inst s j.
    ~is_terminator inst.inst_opcode /\
    ~(?v. step_inst fuel ctx inst s = OK v) ==>
    lift_result (\_ _. T) (execution_equiv {}) (execution_equiv {})
      (step_inst fuel ctx inst s)
      (step_inst fuel ctx inst (s with vs_inst_idx := j))
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (qspecl_then [`fuel`,`ctx`,`inst`,`s`,`j`] mp_tac
        invoke_step_inst_idx_OK_only >> simp[] >>
      Cases_on `step_inst fuel ctx inst s` >>
      gvs[stateEquivTheory.lift_result_def,
          execution_equiv_def, finite_mapTheory.FDOM_FEMPTY, lookup_var_def])
  >> (`step_inst fuel ctx inst (s with vs_inst_idx := j) =
        exec_result_map (\s'. s' with vs_inst_idx := j)
          (step_inst fuel ctx inst s)` by simp[step_inst_idx_indep] >>
      Cases_on `step_inst fuel ctx inst s` >>
      gvs[instIdxIndepTheory.exec_result_map_def,
          stateEquivTheory.lift_result_def,
          execution_equiv_def, finite_mapTheory.FDOM_FEMPTY, lookup_var_def])
QED

Triviality exec_block_skip_prefix_general[local]:
  !prefix fuel ctx bb s j s'.
    j + LENGTH prefix <= LENGTH bb.bb_instructions /\
    EVERY (\i. ~is_terminator i.inst_opcode) prefix /\
    (!k. k < LENGTH prefix ==> EL (j + k) bb.bb_instructions = EL k prefix) /\
    run_insts fuel ctx prefix s = OK s'
  ==>
    exec_block fuel ctx bb (s with vs_inst_idx := j) =
    exec_block fuel ctx bb (s' with vs_inst_idx := j + LENGTH prefix)
Proof
  Induct >> rw[run_insts_def] >>
  rename1 `h :: prefix` >>
  `j < LENGTH bb.bb_instructions` by simp[] >>
  Cases_on `step_inst fuel ctx h s` >> gvs[run_insts_def] >>
  rename1 `step_inst _ _ h s = OK s1` >>
  `EL j bb.bb_instructions = h` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `step_inst fuel ctx h (s with vs_inst_idx := j) =
     OK (s1 with vs_inst_idx := j)` by
    (irule step_inst_idx_ok_general >> simp[]) >>
  `s1.vs_inst_idx = s.vs_inst_idx` by
    metis_tac[step_inst_preserves_inst_idx] >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
  simp[get_instruction_def] >>
  first_x_assum (qspecl_then [`fuel`, `ctx`, `bb`, `s1`, `SUC j`, `s'`]
    mp_tac) >>
  simp[arithmeticTheory.ADD_CLAUSES] >>
  impl_tac
  >- (rw[] >> first_x_assum (qspec_then `SUC k` mp_tac) >>
      simp[arithmeticTheory.ADD_CLAUSES])
  >> simp[]
QED

(* exec_block_skip_prefix for the (non-PHI) body starting at idx n.
   DROP n (FRONT ...) are the body instructions after the PHI prefix. *)
Triviality exec_block_skip_body[local]:
  !bb fuel ctx s s' n.
    bb_well_formed bb /\
    n <= LENGTH (FRONT bb.bb_instructions) /\
    s.vs_inst_idx = n /\
    run_insts fuel ctx (DROP n (FRONT bb.bb_instructions)) s = OK s' ==>
    exec_block fuel ctx bb s =
    exec_block fuel ctx bb (s' with vs_inst_idx :=
      LENGTH (FRONT bb.bb_instructions))
Proof
  rpt strip_tac >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  `EVERY (\i. ~is_terminator i.inst_opcode)
     (DROP n (FRONT bb.bb_instructions))` by
    (imp_res_tac front_non_terminators >>
     gvs[listTheory.EVERY_MEM] >> rpt strip_tac >>
     metis_tac[rich_listTheory.MEM_DROP_IMP]) >>
  `s with vs_inst_idx := n = s` by
    fs[venomStateTheory.venom_state_component_equality] >>
  qspecl_then [`DROP n (FRONT bb.bb_instructions)`, `fuel`, `ctx`, `bb`, `s`, `n`, `s'`]
    mp_tac exec_block_skip_prefix_general >>
  `LENGTH (DROP n (FRONT bb.bb_instructions)) =
     LENGTH (FRONT bb.bb_instructions) - n` by simp[listTheory.LENGTH_DROP] >>
  impl_tac
  >- (rpt conj_tac
      >- (imp_res_tac rich_listTheory.FRONT_LENGTH >> simp[])
      >- first_assum ACCEPT_TAC
      >- (rpt strip_tac >> simp[listTheory.EL_DROP] >>
          irule (GSYM rich_listTheory.EL_FRONT) >>
          gvs[listTheory.NULL_EQ])
      >- first_assum ACCEPT_TAC)
  >> simp[]
QED

(* When body returns non-OK, exec_block returns matching result.
   States in non-OK results are execution_equiv {} (differ only in inst_idx). *)
Triviality exec_block_body_non_ok[local]:
  !prefix fuel ctx bb s j.
    j + LENGTH prefix <= LENGTH bb.bb_instructions /\
    EVERY (\i. ~is_terminator i.inst_opcode) prefix /\
    (!k. k < LENGTH prefix ==> EL (j + k) bb.bb_instructions = EL k prefix) /\
    ~(?v. run_insts fuel ctx prefix s = OK v)
    ==>
    lift_result (\_ _. T) (execution_equiv {}) (execution_equiv {})
      (run_insts fuel ctx prefix s)
      (exec_block fuel ctx bb (s with vs_inst_idx := j))
Proof
  Induct >> rw[run_insts_def] >>
  rename1 `_ :: prefix` >>
  `j < LENGTH bb.bb_instructions` by simp[] >>
  `h = EL j bb.bb_instructions` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `~is_terminator h.inst_opcode` by gvs[] >>
  Cases_on `step_inst fuel ctx h s` >> gvs[run_insts_def]
  >- ( (* OK: head succeeds, tail is non-OK *)
    rename1 `step_inst _ _ _ s = OK s1` >>
    `step_inst fuel ctx bb.bb_instructions❲j❳ (s with vs_inst_idx := j) =
       OK (s1 with vs_inst_idx := j)` by
      (irule step_inst_idx_ok_general >> simp[]) >>
    `s1.vs_inst_idx = s.vs_inst_idx` by
      metis_tac[step_inst_preserves_inst_idx] >>
    first_x_assum (qspecl_then [`fuel`, `ctx`, `bb`, `s1`, `SUC j`] mp_tac) >>
    simp[arithmeticTheory.ADD_CLAUSES] >>
    impl_tac
    >- (rw[] >> first_x_assum (qspec_then `SUC k` mp_tac) >>
        simp[arithmeticTheory.ADD_CLAUSES])
    >> strip_tac >>
    ONCE_REWRITE_TAC[exec_block_def] >>
    simp[get_instruction_def])
  >> (* Non-OK: use step_inst_idx_non_ok_lift *)
  (qspecl_then [`fuel`, `ctx`, `bb.bb_instructions❲j❳`, `s`, `j`]
     mp_tac step_inst_idx_non_ok_lift >> simp[] >>
   Cases_on `step_inst fuel ctx bb.bb_instructions❲j❳
               (s with vs_inst_idx := j)` >>
   gvs[stateEquivTheory.lift_result_def] >>
   rpt strip_tac >> gvs[] >>
   ONCE_REWRITE_TAC[exec_block_def] >>
   simp[get_instruction_def, stateEquivTheory.lift_result_def,
        execution_equiv_def, lookup_var_def])
QED

(* SSA: same output variable => same instruction *)
Triviality ssa_output_unique[local]:
  !insts i j v.
    ALL_DISTINCT (FLAT (MAP (\x. x.inst_outputs) insts)) /\
    MEM i insts /\ MEM j insts /\
    MEM v i.inst_outputs /\ MEM v j.inst_outputs ==>
    i = j
Proof
  Induct >> simp[] >> rpt gen_tac >>
  simp[listTheory.ALL_DISTINCT_APPEND] >> rpt strip_tac >> gvs[]
  >- metis_tac[listTheory.MEM_FLAT, listTheory.MEM_MAP]
  >- metis_tac[listTheory.MEM_FLAT, listTheory.MEM_MAP]
  >- (first_x_assum irule >> metis_tac[])
QED

(* Bridge: fn_inst_ids_distinct => ALL_DISTINCT on fn_insts *)
Triviality fn_insts_ids_all_distinct[local]:
  !fn. fn_inst_ids_distinct fn ==>
       ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn))
Proof
  simp[fn_inst_ids_distinct_def, fn_insts_def] >> gen_tac >>
  `FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) fn.fn_blocks) =
   MAP (\i. i.inst_id) (fn_insts_blocks fn.fn_blocks)` suffices_by simp[] >>
  qspec_tac (`fn.fn_blocks`, `bbs`) >>
  Induct >> simp[fn_insts_blocks_def]
QED


(* Terminator of a well-formed block is untouched by cmp_flip_scan *)
Triviality last_untouched[local]:
  !dfg fn1 bb1 lbl flips removes inserts.
    ao_cmp_flip_scan dfg (fn_insts fn1) = (flips, removes, inserts) /\
    fn_inst_ids_distinct fn1 /\
    (!v ui. MEM ui (dfg_get_uses dfg v) ==> MEM ui (fn_insts fn1)) /\
    bb_well_formed bb1 /\
    lookup_block lbl fn1.fn_blocks = SOME bb1 ==>
    ALOOKUP flips (LAST bb1.bb_instructions).inst_id = NONE /\
    ~MEM (LAST bb1.bb_instructions).inst_id removes /\
    ALOOKUP inserts (LAST bb1.bb_instructions).inst_id = NONE
Proof
  rpt gen_tac >> strip_tac >>
  `bb1.bb_instructions <> [] /\
   is_terminator (LAST bb1.bb_instructions).inst_opcode` by
    fs[bb_well_formed_def] >>
  `MEM (LAST bb1.bb_instructions) bb1.bb_instructions` by
    (irule rich_listTheory.MEM_LAST_NOT_NIL >> simp[]) >>
  `MEM (LAST bb1.bb_instructions) (fn_insts fn1)` by
    metis_tac[block_inst_in_fn_insts] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn1))` by
    metis_tac[fn_insts_ids_all_distinct] >>
  metis_tac[scan_terminator_untouched]
QED

(* Structural: apply on untouched instruction is singleton *)
Triviality apply_untouched[local]:
  !mid flips removes inserts inst.
    ALOOKUP flips inst.inst_id = NONE /\
    ~MEM inst.inst_id removes /\
    ALOOKUP inserts inst.inst_id = NONE ==>
    ao_cmp_flip_apply_inst mid flips removes inserts inst = [inst]
Proof
  rpt strip_tac >> simp[ao_cmp_flip_apply_inst_def]
QED

(* Structural: FRONT/LAST of transformed block *)
Triviality transformed_block_front_last[local]:
  !mid flips removes inserts insts.
    insts <> [] /\
    ALOOKUP flips (LAST insts).inst_id = NONE /\
    ~MEM (LAST insts).inst_id removes /\
    ALOOKUP inserts (LAST insts).inst_id = NONE ==>
    FRONT (FLAT (MAP (ao_cmp_flip_apply_inst mid flips removes inserts) insts)) =
      FLAT (MAP (ao_cmp_flip_apply_inst mid flips removes inserts) (FRONT insts)) /\
    LAST (FLAT (MAP (ao_cmp_flip_apply_inst mid flips removes inserts) insts)) =
      LAST insts /\
    FLAT (MAP (ao_cmp_flip_apply_inst mid flips removes inserts) insts) <> []
Proof
  rpt strip_tac >>
  `insts = SNOC (LAST insts) (FRONT insts)` by
    metis_tac[listTheory.SNOC_LAST_FRONT] >>
  `ao_cmp_flip_apply_inst mid flips removes inserts (LAST insts) =
   [LAST insts]` by (irule apply_untouched >> simp[]) >>
  qabbrev_tac `f = ao_cmp_flip_apply_inst mid flips removes inserts` >>
  `MAP f insts = SNOC (f (LAST insts)) (MAP f (FRONT insts))` by
    (pop_assum kall_tac >> pop_assum kall_tac >>
     qpat_x_assum `insts = _` (fn th => ONCE_REWRITE_TAC[th]) >>
     simp[listTheory.MAP_SNOC]) >>
  `FLAT (MAP f insts) = FLAT (MAP f (FRONT insts)) ++ [LAST insts]` by
    (pop_assum (fn th => REWRITE_TAC[th]) >>
     simp[rich_listTheory.FLAT_SNOC]) >>
  pop_assum (fn th => REWRITE_TAC[th]) >>
  simp[GSYM listTheory.SNOC_APPEND,
       listTheory.FRONT_SNOC, listTheory.LAST_SNOC] >>
  gvs[rich_listTheory.FLAT_SNOC, listTheory.MAP_SNOC]
QED

(* MEM (Var x) ops ==> MEM x (operand_vars ops) *)
Triviality mem_var_operand_vars[local]:
  !x ops. MEM (Var x) ops ==> MEM x (operand_vars ops)
Proof
  Induct_on `ops` >>
  simp[dfgDefsTheory.operand_vars_def, dfgDefsTheory.operand_var_def] >>
  rpt gen_tac >> Cases_on `h` >>
  simp[dfgDefsTheory.operand_vars_def, dfgDefsTheory.operand_var_def] >>
  metis_tac[]
QED

Triviality operand_vars_mem_var[local]:
  !x ops. MEM x (operand_vars ops) ==> MEM (Var x) ops
Proof
  Induct_on `ops` >>
  simp[dfgDefsTheory.operand_vars_def, dfgDefsTheory.operand_var_def] >>
  rpt gen_tac >> Cases_on `h` >>
  simp[dfgDefsTheory.operand_vars_def, dfgDefsTheory.operand_var_def] >>
  metis_tac[]
QED

(* Flip outputs are single-use: accumulated from scan *)
Triviality scan_flip_single_use[local]:
  !dfg insts flips removes inserts id new_opc new_w op1.
    ao_cmp_flip_scan dfg insts = (flips, removes, inserts) /\
    ALOOKUP flips id = SOME (new_opc, new_w, op1) ==>
    ?out_var.
      (?inst. MEM inst insts /\ inst.inst_id = id /\
              inst.inst_outputs = [out_var]) /\
      LENGTH (dfg_get_uses dfg out_var) = 1
Proof
  Induct_on `insts`
  >- simp[ao_cmp_flip_scan_def]
  >> rpt gen_tac >> strip_tac >>
  Cases_on `ao_cmp_flip_scan dfg insts` >> Cases_on `r` >>
  rename1 `_ = (fl0, rm0, ins0)` >>
  Cases_on `flips = fl0`
  >- (gvs[] >>
      first_x_assum drule_all >> strip_tac >>
      qexists_tac `out_var` >> simp[] >>
      metis_tac[listTheory.MEM])
  >> `?w' op1' out_var'.
       h.inst_outputs = [out_var'] /\
       flips = (h.inst_id, flip_comparison_opcode h.inst_opcode,
                (if h.inst_opcode = GT \/ h.inst_opcode = SGT
                 then w' + 1w else w' - 1w), op1') :: fl0 /\
       LENGTH (dfg_get_uses dfg out_var') = 1` by
    (drule_all scan_step_detail >> strip_tac >> gvs[] >>
     metis_tac[]) >>
  gvs[] >>
  Cases_on `id = h.inst_id`
  >- (gvs[] >> qexists_tac `out_var'` >> simp[] >>
      qexists_tac `h` >> simp[])
  >> gvs[] >>
  first_x_assum drule_all >> strip_tac >>
  qexists_tac `out_var` >> simp[] >>
  metis_tac[listTheory.MEM]
QED

(* The single user of a flip's output has its ID in removes or inserts *)
Triviality flip_output_user_in_scan[local]:
  !dfg insts flips removes inserts fi out_var.
    ao_cmp_flip_scan dfg insts = (flips, removes, inserts) /\
    MEM fi insts /\ MEM fi.inst_id (MAP FST flips) /\
    fi.inst_outputs = [out_var] /\
    ALL_DISTINCT (MAP (\i. i.inst_id) insts) ==>
    MEM (HD (dfg_get_uses dfg out_var)).inst_id removes \/
    MEM (HD (dfg_get_uses dfg out_var)).inst_id (MAP FST inserts)
Proof
  Induct_on `insts`
  >- simp[ao_cmp_flip_scan_def]
  >> rpt gen_tac >> strip_tac >>
  Cases_on `ao_cmp_flip_scan dfg insts` >> Cases_on `r` >>
  rename1 `ao_cmp_flip_scan dfg insts = (fl0, rm0, ins0)` >>
  Cases_on `fi = h`
  >- ((* fi = h: h must be a flip target *)
      `flips = fl0 \/
       ?opc w op1. flips = (h.inst_id, opc, w, op1) :: fl0 /\
                   is_comparator h.inst_opcode` by
        metis_tac[scan_step_flips_subset] >>
      gvs[]
      >- ((* No flip on h: fi.inst_id can't be in fl0 by ALL_DISTINCT *)
          `?i. MEM i insts /\ i.inst_id = fi.inst_id` by
            metis_tac[scan_flips_are_comparators] >>
          fs[listTheory.ALL_DISTINCT, listTheory.MEM_MAP] >>
          metis_tac[])
      >> (* Flip on fi: user goes to removes or inserts *)
      `?w' op1' out'.
         fi.inst_outputs = [out'] /\
         LENGTH (dfg_get_uses dfg out') = 1 /\
         (removes = (HD (dfg_get_uses dfg out')).inst_id :: rm0 /\
          inserts = ins0 \/
          removes = rm0 /\
          inserts = ((HD (dfg_get_uses dfg out')).inst_id, out',
                     ao_fresh_var fi.inst_id "iz", fi.inst_id) :: ins0)` by
        (drule_all scan_step_detail >> strip_tac >> gvs[] >>
         metis_tac[]) >>
      gvs[] >>
      metis_tac[listTheory.MEM, listTheory.MEM_MAP, pairTheory.FST])
  >> (* fi ≠ h: use IH *)
  `MEM fi insts` by (fs[] >> metis_tac[]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) insts)` by fs[] >>
  `MEM fi.inst_id (MAP FST fl0)` by
    (`flips = fl0 \/
      ?opc w op1. flips = (h.inst_id, opc, w, op1) :: fl0` by
       metis_tac[scan_step_flips_subset] >>
     gvs[] >>
     fs[listTheory.MEM_MAP] >>
     Cases_on `fi.inst_id = h.inst_id` >> gvs[] >>
     fs[listTheory.ALL_DISTINCT, listTheory.MEM_MAP] >>
     metis_tac[]) >>
  first_x_assum drule_all >> strip_tac >>
  `removes = rm0 \/
   ?v ui. removes = ui.inst_id :: rm0` by
    metis_tac[scan_step_removes_subset] >>
  `inserts = ins0 \/
   ?v ui. inserts = (ui.inst_id, v, ao_fresh_var h.inst_id "iz",
                     h.inst_id) :: ins0` by
    metis_tac[scan_step_inserts_subset] >>
  gvs[]
QED

(* Combines scan_flip_single_use + all_distinct_id_unique:
   if fi is in the flip list and fn_insts has distinct IDs,
   then fi has single output with single use *)
Triviality flip_member_outputs_single_use[local]:
  !dfg fn1 fi flips removes inserts.
    ao_cmp_flip_scan dfg (fn_insts fn1) = (flips, removes, inserts) /\
    MEM fi.inst_id (MAP FST flips) /\
    MEM fi (fn_insts fn1) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn1)) ==>
    ?out_var. fi.inst_outputs = [out_var] /\
              LENGTH (dfg_get_uses dfg out_var) = 1
Proof
  rpt strip_tac >>
  Cases_on `ALOOKUP flips fi.inst_id`
  >- fs[alistTheory.ALOOKUP_NONE]
  >> rename1 `_ = SOME trip` >>
  Cases_on `trip` >> Cases_on `r` >>
  drule_all scan_flip_single_use >> strip_tac >>
  `inst = fi` by (irule all_distinct_id_unique >> metis_tac[]) >>
  gvs[]
QED

(* Insert fresh vars are distinct from flip outputs *)
Triviality insert_fresh_neq_flip_output[local]:
  !dfg fn1 flips removes inserts cmp_id fi' out.
    ao_cmp_flip_scan dfg (fn_insts fn1) = (flips, removes, inserts) /\
    dfg = dfg_build_function fn1 /\
    fn_inst_ids_distinct fn1 /\
    (!inst v. MEM inst (fn_insts fn1) /\ MEM (Var v) inst.inst_operands ==>
      v NOTIN ao_cmp_fresh_vars fn1) /\
    (?i. MEM i (fn_insts fn1) /\ i.inst_id = cmp_id /\
         is_comparator i.inst_opcode) /\
    MEM fi' (fn_insts fn1) /\ ALOOKUP flips fi'.inst_id <> NONE /\
    MEM out fi'.inst_outputs ==>
    ao_fresh_var cmp_id "iz" <> out
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn1))` by
    metis_tac[fn_insts_ids_all_distinct] >>
  `MEM fi'.inst_id (MAP FST flips)` by
    metis_tac[alistTheory.ALOOKUP_NONE, optionTheory.NOT_NONE_SOME,
              listTheory.MEM_MAP] >>
  `?out_var. fi'.inst_outputs = [out_var] /\
             LENGTH (dfg_get_uses dfg out_var) = 1` by
    (drule_all flip_member_outputs_single_use >> strip_tac >>
     qexists_tac `out_var` >> gvs[]) >>
  `out = out_var` by (Cases_on `fi'.inst_outputs` >> gvs[listTheory.MEM]) >>
  pop_assum SUBST_ALL_TAC >>
  `MEM (HD (dfg_get_uses dfg out_var)) (dfg_get_uses dfg out_var)` by
    (Cases_on `dfg_get_uses dfg out_var` >> gvs[]) >>
  `MEM (HD (dfg_get_uses dfg out_var)) (fn_insts fn1) /\
   MEM out_var (operand_vars
     (HD (dfg_get_uses dfg out_var)).inst_operands)` by
    metis_tac[dfgAnalysisPropsTheory.dfg_build_function_uses_sound] >>
  `MEM (Var out_var) (HD (dfg_get_uses dfg out_var)).inst_operands` by
    (irule operand_vars_mem_var >> first_assum ACCEPT_TAC) >>
  `out_var NOTIN ao_cmp_fresh_vars fn1` by metis_tac[] >>
  `ao_fresh_var cmp_id "iz" IN ao_cmp_fresh_vars fn1` by
    (simp[ao_cmp_fresh_vars_def, pred_setTheory.GSPECIFICATION,
          listTheory.MEM_MAP] >>
     metis_tac[]) >>
  metis_tac[]
QED

Triviality iszero_inst_wf_lengths[local]:
  !inst. inst_wf inst /\ inst.inst_opcode = ISZERO ==>
         LENGTH inst.inst_operands = 1 /\ LENGTH inst.inst_outputs = 1
Proof
  rpt strip_tac >> fs[inst_wf_def]
QED

Triviality assert_inst_wf_lengths[local]:
  !inst. inst_wf inst /\ inst.inst_opcode = ASSERT ==>
         LENGTH inst.inst_operands = 1 /\ inst.inst_outputs = []
Proof
  rpt strip_tac >> fs[inst_wf_def]
QED

Triviality non_null_body_sim[local]:
  !mid dfg fn1 lbl bb1 flips removes inserts dead fuel ctx s1 s2 n.
    dead = ao_cmp_flip_dead_vars dfg fn1 /\
    dfg = dfg_build_function fn1 /\
    ao_cmp_flip_scan dfg (fn_insts fn1) = (flips, removes, inserts) /\

    (!inst. MEM inst (fn_insts fn1) ==> inst_wf inst) /\
    (!inst v. MEM inst (fn_insts fn1) /\ MEM (Var v) inst.inst_operands ==>
      v NOTIN ao_cmp_fresh_vars fn1) /\
    fn_inst_ids_distinct fn1 /\
    ssa_form fn1 /\
    ~NULL flips /\
    bb_well_formed bb1 /\
    bb1.bb_instructions <> [] /\
    lookup_block lbl fn1.fn_blocks = SOME bb1 /\
    state_equiv dead s1 s2 /\
    cmp_flip_iszero_inv flips (fn_insts fn1) s1 s2 ==>
    lift_result
      (\s1' s2'. state_equiv dead s1' s2' /\
                 cmp_flip_iszero_inv flips (fn_insts fn1) s1' s2')
      (execution_equiv dead) (execution_equiv dead)
      (run_insts fuel ctx (DROP n (FRONT bb1.bb_instructions)) s1)
      (run_insts fuel ctx
        (FLAT (MAP (ao_cmp_flip_apply_inst mid flips removes inserts)
                   (DROP n (FRONT bb1.bb_instructions)))) s2)
Proof
  rpt strip_tac >>
  qspecl_then [`DROP n (FRONT bb1.bb_instructions)`, `mid`, `flips`, `removes`,
               `inserts`, `dead`, `fn_insts fn1`, `fuel`, `ctx`, `s1`, `s2`]
    match_mp_tac body_lr >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- (imp_res_tac front_non_terminators >>
      gvs[listTheory.EVERY_MEM] >> rpt strip_tac >>
      metis_tac[rich_listTheory.MEM_DROP_IMP])
  >- (rpt strip_tac >>
      metis_tac[rich_listTheory.MEM_DROP_IMP,
                rich_listTheory.MEM_FRONT_NOT_NIL, block_inst_in_fn_insts])
  >- (rpt strip_tac >>
      qpat_x_assum `x IN dead` mp_tac >>
      simp[ao_cmp_flip_dead_vars_def, LET_THM, pairTheory.pair_case_thm,
           pred_setTheory.IN_UNION, pred_setTheory.GSPECIFICATION] >>
      rpt strip_tac >> CCONTR_TAC >> gvs[]
      >- (rename1 `MEM fi (fn_insts fn1)` >>
          `ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn1))` by
            metis_tac[fn_insts_ids_all_distinct] >>
          drule_all flip_member_outputs_single_use >> strip_tac >>
          gvs[listTheory.MEM] >>
          `MEM inst (fn_insts fn1)` by
            (qpat_x_assum `!inst v. _ /\ _ ==> v NOTIN _` kall_tac >>
             metis_tac[rich_listTheory.MEM_DROP_IMP,
                       rich_listTheory.MEM_FRONT_NOT_NIL,
                       block_inst_in_fn_insts]) >>
          `MEM out_var (operand_vars inst.inst_operands)` by
            (irule mem_var_operand_vars >> simp[]) >>
          `MEM inst (dfg_get_uses (dfg_build_function fn1) out_var)` by
            (irule dfgAnalysisPropsTheory.dfg_build_function_uses_complete >>
             simp[]) >>
          `HD (dfg_get_uses (dfg_build_function fn1) out_var) = inst` by
            (Cases_on `dfg_get_uses (dfg_build_function fn1) out_var` >>
             gvs[]) >>
          `MEM inst.inst_id removes \/
           MEM inst.inst_id (MAP FST inserts)` by
            (drule_all flip_output_user_in_scan >> simp[]) >>
          gvs[alistTheory.ALOOKUP_NONE])
      >- (drule_all scan_insert_fresh_form >> strip_tac >> gvs[] >>
          qpat_x_assum `!inst v. _ /\ _ ==> v NOTIN _`
            (qspecl_then [`inst`, `ao_fresh_var i.inst_id "iz"`] mp_tac) >>
          `MEM inst (fn_insts fn1)` by
            metis_tac[rich_listTheory.MEM_DROP_IMP,
                      rich_listTheory.MEM_FRONT_NOT_NIL,
                      block_inst_in_fn_insts] >>
          simp[] >>
          simp[ao_cmp_fresh_vars_def, pred_setTheory.GSPECIFICATION,
               listTheory.MEM_MAP] >>
          qexists_tac `i.inst_id` >> simp[] >>
          qexists_tac `i` >> simp[]))
  >- (rpt strip_tac >>
      simp[ao_cmp_flip_dead_vars_def, LET_THM, pairTheory.pair_case_thm,
           pred_setTheory.IN_UNION, pred_setTheory.GSPECIFICATION] >>
      disj1_tac >>
      qexists_tac `fi` >> simp[] >>
      metis_tac[alistTheory.ALOOKUP_NONE])
  >- (rpt strip_tac >>
      CCONTR_TAC >> gvs[ssa_form_def] >>
      `MEM inst bb1.bb_instructions` by
        metis_tac[rich_listTheory.MEM_DROP_IMP,
                  rich_listTheory.MEM_FRONT_NOT_NIL] >>
      `MEM inst (fn_insts fn1)` by
        metis_tac[block_inst_in_fn_insts] >>
      metis_tac[ssa_output_unique])
  >- (gen_tac >> strip_tac >>
      `MEM id (MAP FST flips)` by
        metis_tac[alistTheory.ALOOKUP_NONE, optionTheory.NOT_NONE_SOME] >>
      `ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn1))` by
        metis_tac[fn_insts_ids_all_distinct] >>
      drule_all scan_flips_are_comparators >> strip_tac >>
      conj_tac
      >- (strip_tac >>
          drule_all scan_removes_are_iszero >> strip_tac >>
          `MEM ui (fn_insts fn1)` by
            metis_tac[dfgAnalysisPropsTheory.dfg_build_function_uses_sound] >>
          `i = ui` by
            (irule all_distinct_id_unique >> metis_tac[]) >>
          fs[is_comparator_def])
      >- (CCONTR_TAC >> gvs[] >>
          `MEM i.inst_id (MAP FST inserts)` by
            metis_tac[alistTheory.ALOOKUP_NONE] >>
          drule_all scan_inserts_are_assert >> strip_tac >>
          `MEM ui (fn_insts fn1)` by
            metis_tac[dfgAnalysisPropsTheory.dfg_build_function_uses_sound] >>
          `i = ui` by
            (irule all_distinct_id_unique >> metis_tac[]) >>
          fs[is_comparator_def]))
  >- (rpt strip_tac >> drule_all scan_flip_info >> strip_tac >>
      `MEM inst (fn_insts fn1)` by
        metis_tac[rich_listTheory.MEM_DROP_IMP, rich_listTheory.MEM_FRONT_NOT_NIL, block_inst_in_fn_insts] >>
      `inst' = inst` by
        (irule all_distinct_id_unique >>
         metis_tac[fn_insts_ids_all_distinct]) >>
      gvs[] >> qexistsl_tac [`w`, `out_var`] >> gvs[])
  >- (rpt strip_tac >>
      drule_all scan_remove_has_flip >> strip_tac >>
      `MEM (HD (dfg_get_uses dfg out_var)) (fn_insts fn1) /\
       MEM out_var (operand_vars (HD (dfg_get_uses dfg out_var)).inst_operands)` by
        metis_tac[dfgAnalysisPropsTheory.dfg_build_function_uses_sound] >>
      `MEM inst (fn_insts fn1)` by
        metis_tac[rich_listTheory.MEM_DROP_IMP, rich_listTheory.MEM_FRONT_NOT_NIL, block_inst_in_fn_insts] >>
      `ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn1))` by
        metis_tac[fn_insts_ids_all_distinct] >>
      `HD (dfg_get_uses dfg out_var) = inst` by
        (irule all_distinct_id_unique >> metis_tac[]) >>
      pop_assum SUBST_ALL_TAC >>
      `inst_wf inst` by (first_x_assum irule >> first_assum ACCEPT_TAC) >>
      drule_all iszero_inst_wf_lengths >> strip_tac >>
      `inst.inst_operands = [Var out_var]` by (
        Cases_on `inst.inst_operands` >> gvs[] >>
        rename1 `operand_vars [op1]` >>
        Cases_on `op1` >>
        gvs[dfgDefsTheory.operand_vars_def, dfgDefsTheory.operand_var_def]) >>
      Cases_on `inst.inst_outputs` >> gvs[] >>
      qexists_tac `fi` >> simp[listTheory.MEM])
  >- (rpt gen_tac >> strip_tac >>
      `MEM (inst.inst_id, cmp_out, fresh, cmp_id) inserts` by
        metis_tac[alistTheory.ALOOKUP_MEM] >>
      drule_all scan_insert_mem_assert >> strip_tac >>
      `MEM inst (fn_insts fn1)` by
        metis_tac[rich_listTheory.MEM_DROP_IMP, rich_listTheory.MEM_FRONT_NOT_NIL, block_inst_in_fn_insts] >>
      `MEM ui (fn_insts fn1) /\
       MEM cmp_out (operand_vars ui.inst_operands)` by
        metis_tac[dfgAnalysisPropsTheory.dfg_build_function_uses_sound] >>
      `ui = inst` by
        (irule all_distinct_id_unique >>
         metis_tac[fn_insts_ids_all_distinct]) >>
      pop_assum SUBST_ALL_TAC >>
      `inst_wf inst` by (first_x_assum irule >> first_assum ACCEPT_TAC) >>
      drule_all assert_inst_wf_lengths >> strip_tac >>
      `inst.inst_operands = [Var cmp_out]` by (
        Cases_on `inst.inst_operands` >> gvs[] >>
        rename1 `operand_vars [op1]` >>
        Cases_on `op1` >>
        gvs[dfgDefsTheory.operand_vars_def, dfgDefsTheory.operand_var_def]) >>
      drule_all scan_insert_has_flip >> strip_tac >>
      drule_all scan_insert_fresh_form >> strip_tac >> gvs[] >>
      rpt conj_tac
      >- (simp[ao_cmp_flip_dead_vars_def, LET_THM, pairTheory.pair_case_thm,
               pred_setTheory.IN_UNION, pred_setTheory.GSPECIFICATION] >>
          disj2_tac >> metis_tac[])
      >- metis_tac[insert_fresh_neq_flip_output]
      >- (qexists_tac `fi` >> simp[]))
QED

Triviality scan_flips_opcode_non_term[local]:
  !dfg insts flips removes inserts id opc w op.
    ao_cmp_flip_scan dfg insts = (flips, removes, inserts) ==>
    ALOOKUP flips id = SOME (opc, w, op) ==>
    ~is_terminator opc /\ opc <> INVOKE
Proof
  Induct_on `insts` >- simp[ao_cmp_flip_scan_def] >>
  rpt gen_tac >> ntac 2 strip_tac >>
  Cases_on `ao_cmp_flip_scan dfg insts` >> Cases_on `r` >>
  rename1 `_ = (fl0, rm0, ins0)` >>
  drule_all scan_step_detail >> strip_tac >> gvs[] >>
  TRY (qpat_x_assum `!dfg flips removes inserts id opc w op. _` drule >>
       disch_then drule >> simp[] >> NO_TAC) >>
  Cases_on `id = h.inst_id` >> gvs[]
  >- (qpat_x_assum `is_comparator _`
        (strip_assume_tac o REWRITE_RULE [is_comparator_def]) >>
      gvs[flip_comparison_opcode_def, is_terminator_def])
  >- (qpat_x_assum `!dfg flips removes inserts id opc w op. _` drule >>
      disch_then drule >> simp[])
  >- (qpat_x_assum `is_comparator _`
        (strip_assume_tac o REWRITE_RULE [is_comparator_def]) >>
      gvs[flip_comparison_opcode_def, is_terminator_def])
  >> qpat_x_assum `!dfg flips removes inserts id opc w op. _` drule >>
     disch_then drule >> simp[]
QED

Triviality apply_inst_every_non_term_non_invoke[local]:
  !mid flips removes inserts inst.
    ~is_terminator inst.inst_opcode /\
    (!id opc w op. ALOOKUP flips id = SOME (opc, w, op) ==>
       ~is_terminator opc) ==>
    EVERY (\j. ~is_terminator j.inst_opcode)
      (ao_cmp_flip_apply_inst mid flips removes inserts inst)
Proof
  rpt strip_tac >>
  simp[ao_cmp_flip_apply_inst_def] >>
  every_case_tac >> gvs[listTheory.EVERY_DEF] >>
  TRY (res_tac >> gvs[]) >>
  simp[is_terminator_def]
QED

Triviality scan_phi_untouched[local]:
  !dfg insts inst flips removes inserts.
    ao_cmp_flip_scan dfg insts = (flips, removes, inserts) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) insts) /\
    (!v ui. MEM ui (dfg_get_uses dfg v) ==> MEM ui insts) /\
    MEM inst insts /\ inst.inst_opcode = PHI ==>
    ALOOKUP flips inst.inst_id = NONE /\
    ~MEM inst.inst_id removes /\
    ALOOKUP inserts inst.inst_id = NONE
Proof
  rpt strip_tac >>
  simp[alistTheory.ALOOKUP_NONE]
  >- (CCONTR_TAC >> gvs[] >>
      drule_all scan_flips_are_comparators >> strip_tac >>
      `i = inst` by (irule all_distinct_id_unique >> metis_tac[]) >>
      gvs[is_comparator_def])
  >- (CCONTR_TAC >> gvs[] >>
      drule_all scan_removes_are_iszero >> strip_tac >>
      `MEM ui insts` by metis_tac[] >>
      `ui = inst` by (irule all_distinct_id_unique >> metis_tac[]) >>
      gvs[])
  >- (CCONTR_TAC >> gvs[] >>
      Cases_on `ALOOKUP inserts inst.inst_id` >> gvs[] >>
      imp_res_tac alistTheory.ALOOKUP_MEM >>
      `MEM inst.inst_id (MAP FST inserts)` by
        (simp[listTheory.MEM_MAP] >> metis_tac[pairTheory.FST]) >>
      drule_all scan_inserts_are_assert >> strip_tac >>
      `MEM ui insts` by metis_tac[] >>
      `ui = inst` by (irule all_distinct_id_unique >> metis_tac[]) >>
      gvs[])
QED


Triviality flip_comparison_not_phi[local]:
  !opc. is_comparator opc ==> flip_comparison_opcode opc <> PHI
Proof
  Cases >> simp[is_comparator_def, flip_comparison_opcode_def]
QED

Triviality apply_inst_non_phi[local]:
  !mid flips removes inserts inst.
    inst.inst_opcode <> PHI /\
    (!id opc w op. ALOOKUP flips id = SOME (opc, w, op) ==> opc <> PHI) ==>
    EVERY (\j. j.inst_opcode <> PHI)
      (ao_cmp_flip_apply_inst mid flips removes inserts inst)
Proof
  rpt strip_tac >>
  simp[ao_cmp_flip_apply_inst_def] >>
  Cases_on `ALOOKUP flips inst.inst_id` >>
  simp[listTheory.EVERY_DEF]
  >- (Cases_on `MEM inst.inst_id removes` >>
      simp[listTheory.EVERY_DEF] >>
      Cases_on `ALOOKUP inserts inst.inst_id` >>
      simp[listTheory.EVERY_DEF] >>
      PairCases_on `x` >> simp[listTheory.EVERY_DEF])
  >- (PairCases_on `x` >> simp[listTheory.EVERY_DEF] >>
      res_tac)
QED

(* Terminator operands are never dead: dead vars are either flip outputs
   (single-use, consumed by iszero/assert in body) or insert fresh vars
   (which are ao_fresh_var, never in original operands). *)
Triviality terminator_operands_not_dead[local]:
  !dfg fn1 flips removes inserts bb1 lbl x.
    ao_cmp_flip_scan dfg (fn_insts fn1) = (flips, removes, inserts) /\
    dfg = dfg_build_function fn1 /\
    fn_inst_ids_distinct fn1 /\
    ssa_form fn1 /\
    (!inst v. MEM inst (fn_insts fn1) /\ MEM (Var v) inst.inst_operands ==>
      v NOTIN ao_cmp_fresh_vars fn1) /\
    bb_well_formed bb1 /\
    lookup_block lbl fn1.fn_blocks = SOME bb1 /\
    MEM (Var x) (LAST bb1.bb_instructions).inst_operands ==>
    x NOTIN ao_cmp_flip_dead_vars dfg fn1
Proof
  rpt strip_tac >>
  `bb1.bb_instructions <> []` by fs[bb_well_formed_def] >>
  `is_terminator (LAST bb1.bb_instructions).inst_opcode` by
    fs[bb_well_formed_def] >>
  `MEM (LAST bb1.bb_instructions) (fn_insts fn1)` by
    (irule block_inst_in_fn_insts >>
     qexistsl_tac [`bb1`, `lbl`] >> simp[] >>
     irule rich_listTheory.MEM_LAST_NOT_NIL >> simp[]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn1))` by
    metis_tac[fn_insts_ids_all_distinct] >>
  `~MEM (LAST bb1.bb_instructions).inst_id removes /\
   ALOOKUP inserts (LAST bb1.bb_instructions).inst_id = NONE` by
    (qspecl_then [`dfg`, `fn_insts fn1`,
                  `LAST bb1.bb_instructions`, `flips`, `removes`, `inserts`]
       mp_tac scan_terminator_untouched >>
     impl_tac
     >- (simp[] >> gvs[] >>
         metis_tac[dfgAnalysisPropsTheory.dfg_build_function_uses_sound])
     >> simp[]) >>
  gvs[ao_cmp_flip_dead_vars_def, LET_THM, pairTheory.pair_case_thm,
      pred_setTheory.IN_UNION, pred_setTheory.GSPECIFICATION]
  >- ((* x is output of flip inst, used by terminator — contradiction *)
      `inst.inst_outputs = [x] /\
       LENGTH (dfg_get_uses (dfg_build_function fn1) x) = 1` by
        (qspecl_then [`dfg_build_function fn1`, `fn1`, `inst`,
                      `flips`, `removes`, `inserts`]
           mp_tac flip_member_outputs_single_use >>
         simp[] >> strip_tac >> gvs[listTheory.MEM]) >>
      `MEM x (operand_vars (LAST bb1.bb_instructions).inst_operands)` by
        (irule mem_var_operand_vars >> first_assum ACCEPT_TAC) >>
      `MEM (LAST bb1.bb_instructions)
         (dfg_get_uses (dfg_build_function fn1) x)` by
        (irule dfgAnalysisPropsTheory.dfg_build_function_uses_complete >>
         simp[]) >>
      `HD (dfg_get_uses (dfg_build_function fn1) x) =
         LAST bb1.bb_instructions` by
        (Cases_on `dfg_get_uses (dfg_build_function fn1) x` >> gvs[]) >>
      `MEM (LAST bb1.bb_instructions).inst_id removes \/
       MEM (LAST bb1.bb_instructions).inst_id (MAP FST inserts)` by
        (qspecl_then [`dfg_build_function fn1`, `fn_insts fn1`,
                      `flips`, `removes`, `inserts`, `inst`, `x`]
           mp_tac flip_output_user_in_scan >>
         simp[]) >>
      gvs[alistTheory.ALOOKUP_NONE])
  >- (drule_all scan_insert_fresh_form >> strip_tac >> gvs[] >>
      `MEM (LAST bb1.bb_instructions) (fn_insts fn1)` by
        (irule block_inst_in_fn_insts >>
         qexistsl_tac [`bb1`, `lbl`] >> simp[] >>
         irule rich_listTheory.MEM_LAST_NOT_NIL >> simp[]) >>
      first_x_assum (qspecl_then [`LAST bb1.bb_instructions`,
                                  `ao_fresh_var i.inst_id "iz"`] mp_tac) >>
      simp[] >>
      simp[ao_cmp_fresh_vars_def, pred_setTheory.GSPECIFICATION,
           listTheory.MEM_MAP] >>
      qexists_tac `i.inst_id` >> simp[] >>
      qexists_tac `i` >> simp[])
QED

Triviality iszero_inv_lookup_eq[local]:
  !flips insts s1 s2 s1' s2'.
    cmp_flip_iszero_inv flips insts s1 s2 /\
    (!v. lookup_var v s1' = lookup_var v s1) /\
    (!v. lookup_var v s2' = lookup_var v s2) ==>
    cmp_flip_iszero_inv flips insts s1' s2'
Proof
  rw[cmp_flip_iszero_inv_def] >> rpt strip_tac >> metis_tac[]
QED

(* FLAT of MAP over a singleton-producing function is the identity *)
Triviality flat_map_singleton_id[local]:
  !f L. (!i. MEM i L ==> f i = [i]) ==> FLAT (MAP f L) = L
Proof
  Induct_on `L` >> simp[] >> rpt strip_tac >>
  `f h = [h]` by (first_x_assum irule >> simp[]) >>
  simp[] >> first_x_assum irule >> metis_tac[]
QED

(* The PHI prefix of a well-formed (terminated) block fits within FRONT *)
Triviality ppl_le_front[local]:
  !bb. bb_well_formed bb ==>
       phi_prefix_length bb.bb_instructions <= LENGTH (FRONT bb.bb_instructions)
Proof
  rpt strip_tac >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  `is_terminator (LAST bb.bb_instructions).inst_opcode` by fs[bb_well_formed_def] >>
  `(LAST bb.bb_instructions).inst_opcode <> PHI` by
    (Cases_on `(LAST bb.bb_instructions).inst_opcode` >> fs[is_terminator_def]) >>
  `LENGTH (FRONT bb.bb_instructions) = LENGTH bb.bb_instructions - 1` by
    (imp_res_tac rich_listTheory.FRONT_LENGTH >> simp[]) >>
  `phi_prefix_length bb.bb_instructions <= LENGTH bb.bb_instructions` by
    simp[venomExecProofsTheory.phi_prefix_length_le] >>
  `phi_prefix_length bb.bb_instructions <> LENGTH bb.bb_instructions` by
    (CCONTR_TAC >> gvs[] >>
     `EVERY (\i. i.inst_opcode = PHI)
        (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions)` by
       simp[phi_prefix_all_phi] >>
     `MEM (LAST bb.bb_instructions) bb.bb_instructions` by
       (irule rich_listTheory.MEM_LAST_NOT_NIL >> simp[]) >>
     gvs[listTheory.TAKE_LENGTH_ID, listTheory.EVERY_MEM]) >>
  decide_tac
QED

(* Non-NULL case. Starts exec_block past the PHI prefix (idx n = ppl),
   matching the new run_block semantics where eval_phis handles PHIs. *)
Theorem non_null_block_sim[local]:
  !mid dfg fn1 lbl bb1 bb' fuel ctx s1 s2 dead flips removes inserts n.
    dead = ao_cmp_flip_dead_vars dfg fn1 /\
    dfg = dfg_build_function fn1 /\
    ao_cmp_flip_scan dfg (fn_insts fn1) = (flips, removes, inserts) /\

    (!inst. MEM inst (fn_insts fn1) ==> inst_wf inst) /\
    (!inst v. MEM inst (fn_insts fn1) /\ MEM (Var v) inst.inst_operands ==>
      v NOTIN ao_cmp_fresh_vars fn1) /\
    fn_inst_ids_distinct fn1 /\
    ssa_form fn1 /\
    ~NULL flips /\
    bb_well_formed bb1 /\
    lookup_block lbl fn1.fn_blocks = SOME bb1 /\
    lookup_block lbl (ao_cmp_flip_function mid dfg fn1).fn_blocks = SOME bb' /\
    state_equiv dead s1 s2 /\
    cmp_flip_iszero_inv flips (fn_insts fn1) s1 s2 /\
    n = phi_prefix_length bb1.bb_instructions /\
    s1.vs_inst_idx = n ==>
    lift_result (state_equiv dead) (execution_equiv dead)
      (execution_equiv dead)
      (exec_block fuel ctx bb1 s1) (exec_block fuel ctx bb' s2)
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `f = ao_cmp_flip_apply_inst mid flips removes inserts` >>
  qabbrev_tac `fr = FRONT bb1.bb_instructions` >>
  qabbrev_tac `bdy = DROP n fr` >>
  `bb1.bb_instructions <> []` by fs[bb_well_formed_def] >>
  `s2.vs_inst_idx = n` by gvs[state_equiv_def] >>
  `n <= LENGTH fr` by
    (qpat_x_assum `n = _` SUBST_ALL_TAC >> qunabbrev_tac `fr` >>
     irule ppl_le_front >> simp[]) >>
  `LENGTH fr < LENGTH bb1.bb_instructions` by
    (imp_res_tac rich_listTheory.FRONT_LENGTH >>
     gvs[Abbr `fr`] >> Cases_on `bb1.bb_instructions` >> fs[]) >>
  `bb'.bb_instructions = FLAT (MAP f bb1.bb_instructions) /\
   bb'.bb_label = bb1.bb_label` by
    (simp[Abbr `f`] >> metis_tac[cmp_flip_block_structure]) >>
  `ALOOKUP flips (LAST bb1.bb_instructions).inst_id = NONE /\
   ~MEM (LAST bb1.bb_instructions).inst_id removes /\
   ALOOKUP inserts (LAST bb1.bb_instructions).inst_id = NONE` by
    metis_tac[last_untouched,
              dfgAnalysisPropsTheory.dfg_build_function_uses_sound] >>
  `FRONT bb'.bb_instructions = FLAT (MAP f fr) /\
   LAST bb'.bb_instructions = LAST bb1.bb_instructions /\
   bb'.bb_instructions <> []` by
    (qunabbrev_tac `fr` >> qunabbrev_tac `f` >> gvs[] >>
     irule transformed_block_front_last >> simp[]) >>
  (* The first n FRONT instructions are PHIs untouched by the transform *)
  `!i. i < n ==> f (EL i fr) = [EL i fr]` by
    (rpt strip_tac >>
     `i < LENGTH bb1.bb_instructions` by gvs[] >>
     `EL i fr = EL i bb1.bb_instructions` by
       (qunabbrev_tac `fr` >> irule rich_listTheory.EL_FRONT >>
        gvs[listTheory.NULL_EQ]) >>
     `(EL i bb1.bb_instructions).inst_opcode = PHI` by
       (`EVERY (\inst. inst.inst_opcode = PHI)
           (TAKE n bb1.bb_instructions)` by simp[phi_prefix_all_phi] >>
        `MEM (EL i bb1.bb_instructions) (TAKE n bb1.bb_instructions)` by
          (simp[listTheory.MEM_EL] >> qexists_tac `i` >>
           simp[listTheory.LENGTH_TAKE_EQ, listTheory.EL_TAKE] >>
           qpat_x_assum `n <= LENGTH fr` mp_tac >> simp[Abbr `fr`] >>
           imp_res_tac rich_listTheory.FRONT_LENGTH >> simp[]) >>
        gvs[listTheory.EVERY_MEM]) >>
     `MEM (EL i bb1.bb_instructions) bb1.bb_instructions` by
       (simp[listTheory.MEM_EL] >> qexists_tac `i` >> simp[]) >>
     `MEM (EL i bb1.bb_instructions) (fn_insts fn1)` by
       metis_tac[block_inst_in_fn_insts] >>
     `ALOOKUP flips (EL i bb1.bb_instructions).inst_id = NONE /\
      ~MEM (EL i bb1.bb_instructions).inst_id removes /\
      ALOOKUP inserts (EL i bb1.bb_instructions).inst_id = NONE` by
       (match_mp_tac scan_phi_untouched >>
        qexistsl_tac [`dfg`, `fn_insts fn1`] >>
        simp[] >> rpt conj_tac
        >- (irule fn_insts_ids_all_distinct >> simp[])
        >- (rpt strip_tac >> gvs[] >>
            drule_all dfgAnalysisPropsTheory.dfg_build_function_uses_sound >>
            simp[])) >>
     simp[Abbr `f`] >> irule apply_untouched >> simp[]) >>
  `LENGTH (TAKE n fr) = n` by simp[listTheory.LENGTH_TAKE_EQ] >>
  `FRONT bb'.bb_instructions = TAKE n fr ++ FLAT (MAP f bdy)` by
    (qpat_x_assum `FRONT bb'.bb_instructions = FLAT (MAP f fr)`
       (fn th => REWRITE_TAC[th]) >>
     `fr = TAKE n fr ++ bdy` by simp[Abbr `bdy`, listTheory.TAKE_DROP] >>
     pop_assum (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV[th]))) >>
     simp[listTheory.MAP_APPEND, rich_listTheory.FLAT_APPEND] >>
     irule flat_map_singleton_id >> rpt strip_tac >>
     gvs[listTheory.MEM_EL, listTheory.LENGTH_TAKE_EQ, listTheory.EL_TAKE]) >>
  `LENGTH (FRONT bb'.bb_instructions) = n + LENGTH (FLAT (MAP f bdy))` by
    (qpat_x_assum `FRONT bb'.bb_instructions = TAKE n fr ++ _`
       (fn th => REWRITE_TAC[th]) >> simp[]) >>
  `n <= LENGTH (FRONT bb'.bb_instructions)` by simp[] >>
  `LENGTH (FRONT bb'.bb_instructions) < LENGTH bb'.bb_instructions` by
    (imp_res_tac rich_listTheory.FRONT_LENGTH >>
     Cases_on `bb'.bb_instructions` >> fs[]) >>
  `!k. k < LENGTH (FLAT (MAP f bdy)) ==>
       EL (n + k) bb'.bb_instructions = EL k (FLAT (MAP f bdy))` by
    (rpt strip_tac >>
     `EL (n + k) bb'.bb_instructions =
        EL (n + k) (FRONT bb'.bb_instructions)` by
       (irule (GSYM rich_listTheory.EL_FRONT) >>
        simp[listTheory.NULL_EQ]) >>
     pop_assum SUBST1_TAC >>
     qpat_x_assum `FRONT bb'.bb_instructions = TAKE n fr ++ _`
       (fn th => REWRITE_TAC[th]) >>
     simp[rich_listTheory.EL_APPEND2]) >>
  `lift_result
     (\s1' s2'. state_equiv dead s1' s2' /\
                cmp_flip_iszero_inv flips (fn_insts fn1) s1' s2')
     (execution_equiv dead) (execution_equiv dead)
     (run_insts fuel ctx bdy s1)
     (run_insts fuel ctx (FLAT (MAP f bdy)) s2)` by
    (qunabbrev_tac `f` >> qunabbrev_tac `bdy` >> qunabbrev_tac `fr` >>
     match_mp_tac non_null_body_sim >>
     qexistsl_tac [`dfg`, `lbl`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `EVERY (\j. ~is_terminator j.inst_opcode)
     (FLAT (MAP f bdy))` by
    (simp[listTheory.EVERY_MEM, listTheory.MEM_FLAT, listTheory.MEM_MAP,
           PULL_EXISTS] >>
     rpt strip_tac >> rename1 `MEM inst0 bdy` >>
     `~is_terminator inst0.inst_opcode` by
       (imp_res_tac front_non_terminators >>
        qunabbrev_tac `bdy` >> qunabbrev_tac `fr` >> gvs[listTheory.EVERY_MEM] >>
        metis_tac[rich_listTheory.MEM_DROP_IMP]) >>
     `MEM inst0 bb1.bb_instructions` by
       (qunabbrev_tac `bdy` >> qunabbrev_tac `fr` >>
        metis_tac[rich_listTheory.MEM_DROP_IMP,
                  rich_listTheory.MEM_FRONT_NOT_NIL]) >>
     qunabbrev_tac `f` >>
     `EVERY (\j. ~is_terminator j.inst_opcode)
        (ao_cmp_flip_apply_inst mid flips removes inserts inst0)` by
       (match_mp_tac apply_inst_every_non_term_non_invoke >>
        rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        rpt strip_tac >> drule_all scan_flips_opcode_non_term >> simp[]) >>
     gvs[listTheory.EVERY_MEM]) >>
  Cases_on `run_insts fuel ctx bdy s1` >>
  Cases_on `run_insts fuel ctx (FLAT (MAP f bdy)) s2` >>
  fs[stateEquivTheory.lift_result_def]
  >- ( (* OK, OK: terminator step *)
    `exec_block fuel ctx bb1 s1 =
     exec_block fuel ctx bb1 (v with vs_inst_idx := LENGTH fr)` by
      (qunabbrev_tac `bdy` >> qunabbrev_tac `fr` >>
       match_mp_tac exec_block_skip_body >> qexists_tac `n` >>
       rpt conj_tac >> first_assum ACCEPT_TAC) >>
    `exec_block fuel ctx bb' s2 =
     exec_block fuel ctx bb' (v' with vs_inst_idx :=
       LENGTH (FRONT bb'.bb_instructions))` by
      (`s2 with vs_inst_idx := n = s2` by
         fs[venomStateTheory.venom_state_component_equality] >>
       qspecl_then [`FLAT (MAP f bdy)`, `fuel`, `ctx`, `bb'`, `s2`, `n`, `v'`]
         mp_tac exec_block_skip_prefix_general >>
       impl_tac
       >- (rpt conj_tac
           >- (qpat_x_assum `LENGTH (FRONT bb'.bb_instructions) = _`
                 (fn th => REWRITE_TAC[GSYM th]) >>
               qpat_x_assum `LENGTH (FRONT bb'.bb_instructions) <
                             LENGTH bb'.bb_instructions` mp_tac >>
               DECIDE_TAC)
           >- first_assum ACCEPT_TAC
           >- (rpt strip_tac >>
               ONCE_REWRITE_TAC[arithmeticTheory.ADD_COMM] >>
               first_x_assum irule >> gvs[])
           >- first_assum ACCEPT_TAC)
       >> strip_tac >>
       qpat_x_assum `LENGTH (FRONT bb'.bb_instructions) = _`
         (fn th => PURE_REWRITE_TAC[th]) >>
       qpat_x_assum `s2 with vs_inst_idx := n = s2`
         (fn th => PURE_ONCE_REWRITE_TAC[GSYM th]) >>
       first_assum ACCEPT_TAC) >>
    ntac 2 (pop_assum SUBST1_TAC) >>
    qspecl_then [`dead`, `fuel`, `ctx`, `bb1`, `bb'`, `v`, `v'`,
                 `LENGTH fr`, `LENGTH (FRONT bb'.bb_instructions)`,
                 `LAST bb1.bb_instructions`]
      mp_tac exec_block_same_terminator >>
    impl_tac
    >- (rpt conj_tac
        (* 1. state_equiv dead v v' *)
        >- first_assum ACCEPT_TAC
        (* 2. LENGTH fr < LENGTH bb1.bb_instructions *)
        >- first_assum ACCEPT_TAC
        (* 3. LENGTH (FRONT bb') < LENGTH bb' *)
        >- first_assum ACCEPT_TAC
        (* 4. EL (LENGTH fr) bb1 = LAST bb1 *)
        >- simp[Abbr `fr`, rich_listTheory.LENGTH_FRONT,
                rich_listTheory.EL_PRE_LENGTH]
        (* 5. EL (LENGTH (FRONT bb')) bb' = LAST bb1 *)
        >- (`LENGTH (FRONT bb'.bb_instructions) =
               PRE (LENGTH bb'.bb_instructions)`
              by (irule rich_listTheory.FRONT_LENGTH >> first_assum ACCEPT_TAC) >>
            pop_assum SUBST1_TAC >>
            `EL (PRE (LENGTH bb'.bb_instructions)) bb'.bb_instructions =
               LAST bb'.bb_instructions`
              by (irule rich_listTheory.EL_PRE_LENGTH >> first_assum ACCEPT_TAC) >>
            pop_assum SUBST1_TAC >>
            first_assum ACCEPT_TAC)
        (* 6. is_terminator *)
        >- fs[bb_well_formed_def]
        (* 7. operands not dead *)
        >- (rpt strip_tac >> CCONTR_TAC >>
            drule_all terminator_operands_not_dead >> gvs[]))
    >> simp[])
  >> (* Non-OK cases *)
  `lift_result (\_ _. T) (execution_equiv {}) (execution_equiv {})
    (run_insts fuel ctx bdy s1)
    (exec_block fuel ctx bb1 s1)` by
    (qspecl_then [`bdy`, `fuel`, `ctx`, `bb1`, `s1`, `n`]
       mp_tac exec_block_body_non_ok >>
     impl_tac
     >- (rpt conj_tac
         >- (simp[Abbr `bdy`] >>
             `LENGTH (DROP n fr) = LENGTH fr - n` by simp[listTheory.LENGTH_DROP] >>
             simp[])
         >- (simp[listTheory.EVERY_MEM, Abbr `bdy`, Abbr `fr`] >> rpt strip_tac >>
             imp_res_tac front_non_terminators >>
             gvs[listTheory.EVERY_MEM] >>
             metis_tac[rich_listTheory.MEM_DROP_IMP])
         >- (simp[Abbr `bdy`, Abbr `fr`] >> rpt strip_tac >>
             simp[listTheory.EL_DROP] >>
             irule (GSYM rich_listTheory.EL_FRONT) >>
             gvs[listTheory.NULL_EQ])
         >- (simp[] >>
             Cases_on `run_insts fuel ctx bdy s1` >> gvs[]))
     >> strip_tac >>
     `s1 with vs_inst_idx := n = s1` by
       fs[venomStateTheory.venom_state_component_equality] >>
     gvs[]) >>
  `lift_result (\_ _. T) (execution_equiv {}) (execution_equiv {})
    (run_insts fuel ctx (FLAT (MAP f bdy)) s2)
    (exec_block fuel ctx bb' s2)` by
    (qspecl_then [`FLAT (MAP f bdy)`, `fuel`, `ctx`, `bb'`, `s2`, `n`]
       mp_tac exec_block_body_non_ok >>
     impl_tac
     >- (rpt conj_tac
         >- (qpat_x_assum `LENGTH (FRONT bb'.bb_instructions) = _`
               (fn th => REWRITE_TAC[GSYM th]) >>
             qpat_x_assum `LENGTH (FRONT bb'.bb_instructions) <
                           LENGTH bb'.bb_instructions` mp_tac >>
             DECIDE_TAC)
         >- first_assum ACCEPT_TAC
         >- (rpt strip_tac >>
             ONCE_REWRITE_TAC[arithmeticTheory.ADD_COMM] >>
             first_x_assum irule >> gvs[])
         >- (simp[] >>
             Cases_on `run_insts fuel ctx (FLAT (MAP f bdy)) s2` >> gvs[]))
     >> strip_tac >>
     `s2 with vs_inst_idx := n = s2` by
       fs[venomStateTheory.venom_state_component_equality] >>
     gvs[]) >>
  Cases_on `exec_block fuel ctx bb1 s1` >>
  Cases_on `exec_block fuel ctx bb' s2` >>
  gvs[stateEquivTheory.lift_result_def] >>
  metis_tac[execution_equiv_trans, execution_equiv_sym,
            execution_equiv_subset, pred_setTheory.EMPTY_SUBSET]
QED

(* ===== eval_phis bridges for run_block ===== *)

(* Equal vs_inst_idx update preserves state_equiv *)
Triviality state_equiv_idx_update[local]:
  !dead s1 s2 k.
    state_equiv dead s1 s2 ==>
    state_equiv dead (s1 with vs_inst_idx := k) (s2 with vs_inst_idx := k)
Proof
  rw[state_equiv_def, execution_equiv_def, lookup_var_def]
QED

(* An operand of any source instruction is never a dead var:
   dead vars are flip outputs (single-use, consumed by the removed iszero) or
   insert fresh vars (never appear in source operands). *)
Triviality operand_not_dead[local]:
  !dfg fn1 flips removes inserts pinst x.
    ao_cmp_flip_scan dfg (fn_insts fn1) = (flips, removes, inserts) /\
    dfg = dfg_build_function fn1 /\
    fn_inst_ids_distinct fn1 /\
    (!inst v. MEM inst (fn_insts fn1) /\ MEM (Var v) inst.inst_operands ==>
      v NOTIN ao_cmp_fresh_vars fn1) /\
    MEM pinst (fn_insts fn1) /\
    pinst.inst_opcode = PHI /\
    MEM (Var x) pinst.inst_operands ==>
    x NOTIN ao_cmp_flip_dead_vars dfg fn1
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn1))` by
    metis_tac[fn_insts_ids_all_distinct] >>
  `~MEM pinst.inst_id removes /\
   ALOOKUP inserts pinst.inst_id = NONE` by
    (qspecl_then [`dfg_build_function fn1`, `fn_insts fn1`,
                  `pinst`, `flips`, `removes`, `inserts`]
       mp_tac scan_phi_untouched >>
     impl_tac
     >- (simp[] >> gvs[] >>
         metis_tac[dfgAnalysisPropsTheory.dfg_build_function_uses_sound])
     >> simp[]) >>
  gvs[ao_cmp_flip_dead_vars_def, LET_THM, pairTheory.pair_case_thm,
      pred_setTheory.IN_UNION, pred_setTheory.GSPECIFICATION]
  >- ((* x is a flip output, whose single user is pinst — contradiction *)
      `inst.inst_outputs = [x] /\
       LENGTH (dfg_get_uses (dfg_build_function fn1) x) = 1` by
        (qspecl_then [`dfg_build_function fn1`, `fn1`, `inst`,
                      `flips`, `removes`, `inserts`]
           mp_tac flip_member_outputs_single_use >>
         simp[] >> strip_tac >> gvs[listTheory.MEM]) >>
      `MEM x (operand_vars pinst.inst_operands)` by
        (irule mem_var_operand_vars >> first_assum ACCEPT_TAC) >>
      `MEM pinst (dfg_get_uses (dfg_build_function fn1) x)` by
        (irule dfgAnalysisPropsTheory.dfg_build_function_uses_complete >> simp[]) >>
      `HD (dfg_get_uses (dfg_build_function fn1) x) = pinst` by
        (Cases_on `dfg_get_uses (dfg_build_function fn1) x` >> gvs[]) >>
      `MEM pinst.inst_id removes \/ MEM pinst.inst_id (MAP FST inserts)` by
        (qspecl_then [`dfg_build_function fn1`, `fn_insts fn1`,
                      `flips`, `removes`, `inserts`, `inst`, `x`]
           mp_tac flip_output_user_in_scan >>
         simp[]) >>
      gvs[alistTheory.ALOOKUP_NONE])
  >- (drule_all scan_insert_fresh_form >> strip_tac >> gvs[] >>
      first_x_assum (qspecl_then [`pinst`, `ao_fresh_var i.inst_id "iz"`] mp_tac) >>
      simp[] >>
      simp[ao_cmp_fresh_vars_def, pred_setTheory.GSPECIFICATION,
           listTheory.MEM_MAP] >>
      qexists_tac `i.inst_id` >> simp[] >>
      qexists_tac `i` >> simp[])
QED

(* The cmp_flip transform leaves the PHI prefix untouched, so eval_phis and
   phi_prefix_length agree on the original and transformed instruction lists. *)
Triviality cmp_flip_eval_phis_eq[local]:
  !mid dfg fn1 lbl bb1 bb' flips removes inserts.
    ao_cmp_flip_scan dfg (fn_insts fn1) = (flips, removes, inserts) /\
    dfg = dfg_build_function fn1 /\
    fn_inst_ids_distinct fn1 /\
    bb_well_formed bb1 /\
    lookup_block lbl fn1.fn_blocks = SOME bb1 /\
    bb'.bb_instructions =
      FLAT (MAP (ao_cmp_flip_apply_inst mid flips removes inserts)
                bb1.bb_instructions) ==>
    (!s. eval_phis s bb'.bb_instructions = eval_phis s bb1.bb_instructions) /\
    phi_prefix_length bb'.bb_instructions = phi_prefix_length bb1.bb_instructions
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `f = ao_cmp_flip_apply_inst mid flips removes inserts` >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn1))` by
    metis_tac[fn_insts_ids_all_distinct] >>
  `!v ui. MEM ui (dfg_get_uses (dfg_build_function fn1) v) ==>
          MEM ui (fn_insts fn1)` by
    metis_tac[dfgAnalysisPropsTheory.dfg_build_function_uses_sound] >>
  `!idx inst. idx < LENGTH bb1.bb_instructions /\
              EL idx bb1.bb_instructions = inst /\ inst.inst_opcode = PHI ==>
              f inst = [inst]` by
    (rpt strip_tac >>
     `MEM inst bb1.bb_instructions` by metis_tac[listTheory.MEM_EL] >>
     `MEM inst (fn_insts fn1)` by metis_tac[block_inst_in_fn_insts] >>
     `ALOOKUP flips inst.inst_id = NONE /\ ~MEM inst.inst_id removes /\
      ALOOKUP inserts inst.inst_id = NONE` by
       (qspecl_then [`dfg_build_function fn1`, `fn_insts fn1`, `inst`,
                     `flips`, `removes`, `inserts`]
          mp_tac scan_phi_untouched >>
        impl_tac
        >- (simp[] >> gvs[] >>
            metis_tac[dfgAnalysisPropsTheory.dfg_build_function_uses_sound])
        >> simp[]) >>
     simp[Abbr `f`] >> irule apply_untouched >> simp[]) >>
  `!idx inst. idx < LENGTH bb1.bb_instructions /\
              EL idx bb1.bb_instructions = inst /\ inst.inst_opcode <> PHI ==>
              EVERY (\i. i.inst_opcode <> PHI) (f inst)` by
    (rpt strip_tac >> simp[Abbr `f`] >> match_mp_tac apply_inst_non_phi >>
     simp[] >> rpt strip_tac >> drule_all scan_flip_info >> strip_tac >> gvs[] >>
     imp_res_tac flip_comparison_not_phi) >>
  `!i j. i < j /\ j < LENGTH bb1.bb_instructions /\
         (EL j bb1.bb_instructions).inst_opcode = PHI ==>
         (EL i bb1.bb_instructions).inst_opcode = PHI` by
    fs[bb_well_formed_def] >>
  `bb'.bb_instructions = FLAT (MAPi (\i x. f x) bb1.bb_instructions)` by
    simp[indexedListsTheory.MAPi_EQ_MAP] >>
  pop_assum (fn th => PURE_REWRITE_TAC[th]) >>
  conj_tac
  >- (gen_tac >> irule eval_phis_flat_mapi >>
      CONV_TAC (DEPTH_CONV BETA_CONV) >> rpt conj_tac >> first_assum ACCEPT_TAC)
  >- (irule phi_prefix_length_flat_mapi >>
      CONV_TAC (DEPTH_CONV BETA_CONV) >> rpt conj_tac >> first_assum ACCEPT_TAC)
QED

(* The iszero invariant reads only flip (comparator) outputs, which are not
   PHI outputs under SSA, so eval_phis (touching only PHI outputs) preserves
   the invariant. *)
Triviality cmp_flip_iszero_inv_eval_phis[local]:
  !dfg fn1 flips removes inserts s1 s2 sp1 sp2 insts.
    ao_cmp_flip_scan dfg (fn_insts fn1) = (flips, removes, inserts) /\
    ssa_form fn1 /\
    fn_inst_ids_distinct fn1 /\
    (!inst. MEM inst insts ==> MEM inst (fn_insts fn1)) /\
    cmp_flip_iszero_inv flips (fn_insts fn1) s1 s2 /\
    eval_phis s1 insts = OK sp1 /\
    eval_phis s2 insts = OK sp2 ==>
    cmp_flip_iszero_inv flips (fn_insts fn1) sp1 sp2
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn1))` by
    metis_tac[fn_insts_ids_all_distinct] >>
  simp[cmp_flip_iszero_inv_def] >> rpt gen_tac >> strip_tac >>
  rename1 `MEM fi (fn_insts fn1)` >>
  `!phi. MEM phi insts /\ phi.inst_opcode = PHI ==> ~MEM out phi.inst_outputs` by
    (rpt strip_tac >>
     `MEM phi (fn_insts fn1)` by metis_tac[] >>
     `MEM fi.inst_id (MAP FST flips)` by
       metis_tac[alistTheory.ALOOKUP_NONE, optionTheory.NOT_NONE_SOME] >>
     drule_all scan_flips_are_comparators >> strip_tac >>
     `i = fi` by (irule all_distinct_id_unique >> metis_tac[]) >>
     gvs[] >>
     `MEM phi (fn_insts fn1)` by metis_tac[] >>
     `fi = phi` by
       (irule ssa_output_unique >>
        conj_tac
        >- (qexists_tac `fn_insts fn1` >> fs[ssa_form_def])
        >- (qexists_tac `out` >> simp[])) >>
     gvs[is_comparator_def]) >>
  `FLOOKUP sp1.vs_vars out = FLOOKUP s1.vs_vars out` by
    (qspecl_then [`s1`, `insts`, `out`, `sp1`] mp_tac
       venomExecProofsTheory.eval_phis_flookup_not_phi_output >>
     impl_tac >- (simp[] >> metis_tac[]) >> simp[]) >>
  `FLOOKUP sp2.vs_vars out = FLOOKUP s2.vs_vars out` by
    (qspecl_then [`s2`, `insts`, `out`, `sp2`] mp_tac
       venomExecProofsTheory.eval_phis_flookup_not_phi_output >>
     impl_tac >- (simp[] >> metis_tac[]) >> simp[]) >>
  `lookup_var out sp1 = lookup_var out s1 /\
   lookup_var out sp2 = lookup_var out s2` by simp[lookup_var_def] >>
  gvs[cmp_flip_iszero_inv_def] >> metis_tac[]
QED

(* ===== Main theorem ===== *)

Theorem ao_cmp_flip_block_sim:
  !mid dfg fn1 lbl bb1 bb' fuel ctx s1 s2.
    let dead = ao_cmp_flip_dead_vars dfg fn1 in
    let flips = FST (ao_cmp_flip_scan dfg (fn_insts fn1)) in
    dfg = dfg_build_function fn1 /\

    (!inst. MEM inst (fn_insts fn1) ==> inst_wf inst) /\
    (!inst v. MEM inst (fn_insts fn1) /\ MEM (Var v) inst.inst_operands ==>
      v NOTIN ao_cmp_fresh_vars fn1) /\
    fn_inst_ids_distinct fn1 /\
    ssa_form fn1 /\
    bb_well_formed bb1 /\
    lookup_block lbl fn1.fn_blocks = SOME bb1 /\
    lookup_block lbl (ao_cmp_flip_function mid dfg fn1).fn_blocks = SOME bb' /\
    state_equiv dead s1 s2 /\
    cmp_flip_iszero_inv flips (fn_insts fn1) s1 s2 ==>
    (?e. run_block fuel ctx bb1 s1 = Error e) \/
    lift_result (state_equiv dead) (execution_equiv dead)
      (execution_equiv dead)
      (run_block fuel ctx bb1 s1) (run_block fuel ctx bb' s2)
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
      gvs[] >> DISJ2_TAC >>
      irule lift_result_refl >>
      simp[state_equiv_refl, execution_equiv_refl])
  >> (* Non-NULL *)
  Cases_on `ao_cmp_flip_scan (dfg_build_function fn1) (fn_insts fn1)` >>
  Cases_on `r` >> gvs[] >>
  rename1 `_ = (flips, removes, inserts)` >>
  qabbrev_tac `f = ao_cmp_flip_apply_inst mid flips removes inserts` >>
  `bb1.bb_instructions <> []` by fs[bb_well_formed_def] >>
  `bb'.bb_instructions = FLAT (MAP f bb1.bb_instructions) /\
   bb'.bb_label = bb1.bb_label` by
    (simp[Abbr `f`] >> metis_tac[cmp_flip_block_structure]) >>
  `(!s. eval_phis s bb'.bb_instructions = eval_phis s bb1.bb_instructions) /\
   phi_prefix_length bb'.bb_instructions =
     phi_prefix_length bb1.bb_instructions` by
    (irule cmp_flip_eval_phis_eq >>
     simp[Abbr `f`] >>
     qexistsl_tac [`flips`, `fn1`, `inserts`, `lbl`, `mid`, `removes`] >>
     simp[]) >>
  (* PHI operands are never dead, so eval_phis transfers across state_equiv *)
  `EVERY (\inst. inst.inst_opcode = PHI ==>
            !x. MEM (Var x) inst.inst_operands ==>
              x NOTIN ao_cmp_flip_dead_vars (dfg_build_function fn1) fn1)
          bb1.bb_instructions` by
    (simp[listTheory.EVERY_MEM] >> rpt strip_tac >>
     `MEM inst (fn_insts fn1)` by
       (irule block_inst_in_fn_insts >> qexistsl_tac [`bb1`, `lbl`] >> simp[]) >>
     `x NOTIN ao_cmp_flip_dead_vars (dfg_build_function fn1) fn1`
       suffices_by simp[] >>
     irule operand_not_dead >>
     rpt conj_tac
     >- first_assum ACCEPT_TAC
     >- first_assum ACCEPT_TAC
     >- REFL_TAC
     >- (qexistsl_tac [`flips`, `inserts`, `removes`] >> first_assum ACCEPT_TAC)
     >- (qexists_tac `inst` >> simp[])) >>
  simp[run_block_def] >>
  qpat_x_assum `!s. eval_phis s bb'.bb_instructions = _`
    (fn th => simp[th]) >>
  qpat_x_assum `phi_prefix_length bb'.bb_instructions = _`
    (fn th => simp[th]) >>
  `(?sp1. eval_phis s1 bb1.bb_instructions = OK sp1) \/
   (?e. eval_phis s1 bb1.bb_instructions = Error e)` by
    metis_tac[eval_phis_ok_or_error_defs] >>
  pop_assum strip_assume_tac
  >- ((* eval_phis OK: reduce to exec_block past the PHI prefix *)
      rename1 `eval_phis s1 bb1.bb_instructions = OK sp1` >>
      qspecl_then [`s1`, `s2`,
                   `ao_cmp_flip_dead_vars (dfg_build_function fn1) fn1`,
                   `bb1.bb_instructions`, `sp1`]
        mp_tac venomExecProofsTheory.eval_phis_state_equiv >>
      impl_tac >- simp[] >> strip_tac >>
      rename1 `eval_phis s2 bb1.bb_instructions = OK sp2` >>
      `cmp_flip_iszero_inv flips (fn_insts fn1) sp1 sp2` by
        (qspecl_then [`dfg_build_function fn1`, `fn1`, `flips`, `removes`,
                      `inserts`, `s1`, `s2`, `sp1`, `sp2`, `bb1.bb_instructions`]
           mp_tac cmp_flip_iszero_inv_eval_phis >>
         impl_tac
         >- (simp[] >> rpt strip_tac >>
             irule block_inst_in_fn_insts >> qexistsl_tac [`bb1`, `lbl`] >>
             simp[])
         >> simp[]) >>
      `state_equiv (ao_cmp_flip_dead_vars (dfg_build_function fn1) fn1)
         (sp1 with vs_inst_idx := phi_prefix_length bb1.bb_instructions)
         (sp2 with vs_inst_idx := phi_prefix_length bb1.bb_instructions)` by
        (irule state_equiv_idx_update >> simp[]) >>
      `cmp_flip_iszero_inv flips (fn_insts fn1)
         (sp1 with vs_inst_idx := phi_prefix_length bb1.bb_instructions)
         (sp2 with vs_inst_idx := phi_prefix_length bb1.bb_instructions)` by
        (irule iszero_inv_lookup_eq >> qexistsl_tac [`sp1`, `sp2`] >>
         simp[lookup_var_def]) >>
      `lift_result (state_equiv (ao_cmp_flip_dead_vars (dfg_build_function fn1) fn1))
         (execution_equiv (ao_cmp_flip_dead_vars (dfg_build_function fn1) fn1))
         (execution_equiv (ao_cmp_flip_dead_vars (dfg_build_function fn1) fn1))
         (exec_block fuel ctx bb1
            (sp1 with vs_inst_idx := phi_prefix_length bb1.bb_instructions))
         (exec_block fuel ctx bb'
            (sp2 with vs_inst_idx := phi_prefix_length bb1.bb_instructions))` by
        (qspecl_then [`mid`, `dfg_build_function fn1`, `fn1`, `lbl`, `bb1`, `bb'`,
                      `fuel`, `ctx`,
                      `sp1 with vs_inst_idx := phi_prefix_length bb1.bb_instructions`,
                      `sp2 with vs_inst_idx := phi_prefix_length bb1.bb_instructions`,
                      `ao_cmp_flip_dead_vars (dfg_build_function fn1) fn1`,
                      `flips`, `removes`, `inserts`,
                      `phi_prefix_length bb1.bb_instructions`]
           mp_tac non_null_block_sim >>
         impl_tac
         >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[])
         >> simp[]) >>
      simp[Excl "ao_cmp_flip_dead_vars_def", Excl "cmp_flip_iszero_inv_def",
           Excl "ao_cmp_flip_scan_def"] >> DISJ2_TAC >>
      first_assum ACCEPT_TAC)
  >> (* eval_phis Error: run_block bb1 s1 = Error *)
  simp[]
QED

(* exec_block OK (from idx n past the PHI prefix) implies the non-PHI body
   runs OK and the terminator preserves variable lookups. *)
Triviality exec_block_ok_lookup_body[local]:
  !fuel ctx bb s s' n.
    bb_well_formed bb /\
    n <= LENGTH (FRONT bb.bb_instructions) /\
    s.vs_inst_idx = n /\
    exec_block fuel ctx bb s = OK s' ==>
    ?v. run_insts fuel ctx (DROP n (FRONT bb.bb_instructions)) s = OK v /\
        !x. lookup_var x s' = lookup_var x v
Proof
  rpt strip_tac >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  qabbrev_tac `flen = LENGTH (FRONT bb.bb_instructions)` >>
  qabbrev_tac `bdy = DROP n (FRONT bb.bb_instructions)` >>
  `LENGTH bdy = flen - n` by simp[Abbr `bdy`, Abbr `flen`, listTheory.LENGTH_DROP] >>
  `flen < LENGTH bb.bb_instructions` by
    (imp_res_tac rich_listTheory.FRONT_LENGTH >>
     gvs[Abbr `flen`] >> Cases_on `bb.bb_instructions` >> fs[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) bdy` by
    (simp[listTheory.EVERY_MEM, Abbr `bdy`] >> rpt strip_tac >>
     imp_res_tac front_non_terminators >> gvs[listTheory.EVERY_MEM] >>
     metis_tac[rich_listTheory.MEM_DROP_IMP]) >>
  `!k. k < LENGTH bdy ==> EL (n + k) bb.bb_instructions = EL k bdy` by
    (rpt strip_tac >> simp[Abbr `bdy`, listTheory.EL_DROP] >>
     irule (GSYM rich_listTheory.EL_FRONT) >> gvs[listTheory.NULL_EQ]) >>
  `s with vs_inst_idx := n = s` by
    fs[venomStateTheory.venom_state_component_equality] >>
  `?v. run_insts fuel ctx bdy s = OK v` by
    (CCONTR_TAC >> gvs[] >>
     qspecl_then [`bdy`, `fuel`, `ctx`, `bb`, `s`, `s.vs_inst_idx`]
       mp_tac exec_block_body_non_ok >>
     impl_tac
     >- (rpt conj_tac
         >- (qpat_x_assum `LENGTH bdy = _` mp_tac >>
             qpat_x_assum `flen < LENGTH bb.bb_instructions` mp_tac >>
             qpat_x_assum `s.vs_inst_idx <= flen` mp_tac >> DECIDE_TAC)
         >- first_assum ACCEPT_TAC
         >- (rpt strip_tac >>
             ONCE_REWRITE_TAC[arithmeticTheory.ADD_COMM] >>
             first_x_assum irule >> gvs[])
         >- simp[])
     >> strip_tac >> gvs[] >>
     Cases_on `run_insts fuel ctx bdy s` >> gvs[lift_result_def]) >>
  qexists_tac `v` >> simp[] >>
  `exec_block fuel ctx bb s =
   exec_block fuel ctx bb (v with vs_inst_idx := flen)` by
    (qunabbrev_tac `bdy` >> qunabbrev_tac `flen` >>
     match_mp_tac exec_block_skip_body >> qexists_tac `n` >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qabbrev_tac `term = LAST bb.bb_instructions` >>
  `is_terminator term.inst_opcode` by fs[bb_well_formed_def, Abbr `term`] >>
  `get_instruction bb flen = SOME term` by
    simp[get_instruction_def, Abbr `flen`, Abbr `term`,
         rich_listTheory.LENGTH_FRONT, rich_listTheory.EL_PRE_LENGTH] >>
  rpt strip_tac >>
  `exec_block fuel ctx bb (v with vs_inst_idx := flen) = OK s'` by gvs[] >>
  qpat_x_assum `exec_block fuel ctx bb (v with vs_inst_idx := flen) = OK s'`
    (fn th => mp_tac (ONCE_REWRITE_RULE [exec_block_def] th)) >>
  simp[] >>
  Cases_on `step_inst fuel ctx term (v with vs_inst_idx := flen)` >>
  gvs[] >> strip_tac >> gvs[AllCaseEqs()] >>
  drule_all venomExecPropsTheory.step_terminator_preserves_vars >>
  disch_then (qspec_then `x` mp_tac) >>
  simp[lookup_var_def]
QED

Triviality no_phi_in_flat_map[local]:
  !insts f.
    (!inst. MEM inst insts ==> inst.inst_opcode <> PHI) /\
    (!inst. MEM inst insts ==>
       EVERY (\j. j.inst_opcode <> PHI) (f inst)) ==>
    EVERY (\j. j.inst_opcode <> PHI) (FLAT (MAP f insts))
Proof
  Induct >> simp[] >>
  rpt strip_tac >> res_tac >> gvs[listTheory.EVERY_APPEND]
QED


Triviality flat_map_preserves_phi_prefix[local]:
  !insts f.
    (!i j. i < j /\ j < LENGTH insts /\ (EL j insts).inst_opcode = PHI ==>
           (EL i insts).inst_opcode = PHI) /\
    (!inst. MEM inst insts /\ inst.inst_opcode = PHI ==> f inst = [inst]) /\
    (!inst. MEM inst insts /\ inst.inst_opcode <> PHI ==>
       EVERY (\j. j.inst_opcode <> PHI) (f inst)) ==>
    !i j. i < j /\ j < LENGTH (FLAT (MAP f insts)) /\
          (EL j (FLAT (MAP f insts))).inst_opcode = PHI ==>
          (EL i (FLAT (MAP f insts))).inst_opcode = PHI
Proof
  Induct >- simp[] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `h.inst_opcode = PHI`
  >- (`f h = [h]` by (first_assum irule >> simp[]) >>
      rpt gen_tac >> strip_tac >>
      `FLAT (MAP f (h::insts)) = h :: FLAT (MAP f insts)` by
        simp[] >>
      Cases_on `i`
      >- gvs[]
      >- (Cases_on `j` >> gvs[] >>
          first_x_assum irule >> gvs[] >>
          rpt conj_tac
          >- (rpt strip_tac >>
              qpat_x_assum `!i j. i < j /\ j < SUC _ /\ _ ==> _`
                (qspecl_then [`SUC i`, `SUC j`] mp_tac) >>
              simp[])
          >- (qexists_tac `n'` >> simp[])))
  >- (rpt strip_tac >>
      `!inst. MEM inst (h::insts) ==> inst.inst_opcode <> PHI` by
        (rpt strip_tac >> gvs[listTheory.MEM] >>
         CCONTR_TAC >> gvs[] >>
         `?k. k < LENGTH insts /\ EL k insts = inst` by
           metis_tac[listTheory.MEM_EL] >>
         qpat_x_assum `!i j. i < j /\ _ ==> _`
           (qspecl_then [`0`, `SUC k`] mp_tac) >>
         simp[]) >>
      `EVERY (\j. j.inst_opcode <> PHI) (FLAT (MAP f (h::insts)))` by
        (irule no_phi_in_flat_map >> rpt conj_tac >> rpt strip_tac
         >- res_tac
         >- (`inst.inst_opcode <> PHI` by res_tac >> res_tac)) >>
      qpat_x_assum `EVERY _ _`
        (mp_tac o SIMP_RULE std_ss [listTheory.EVERY_EL]) >>
      disch_then (qspec_then `j` mp_tac) >> simp[])
QED

Triviality bb_wf_front_phi_prefix[local]:
  !bb. bb_well_formed bb ==>
    !i j. i < j /\ j < LENGTH (FRONT bb.bb_instructions) /\
      (EL j (FRONT bb.bb_instructions)).inst_opcode = PHI ==>
      (EL i (FRONT bb.bb_instructions)).inst_opcode = PHI
Proof
  rpt strip_tac >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  `j < LENGTH bb.bb_instructions` by
    (imp_res_tac rich_listTheory.FRONT_LENGTH >> DECIDE_TAC) >>
  `i < LENGTH bb.bb_instructions` by
    (imp_res_tac rich_listTheory.FRONT_LENGTH >> DECIDE_TAC) >>
  `EL j (FRONT bb.bb_instructions) = EL j bb.bb_instructions` by
    (irule rich_listTheory.EL_FRONT >> fs[listTheory.NULL_EQ]) >>
  `EL i (FRONT bb.bb_instructions) = EL i bb.bb_instructions` by
    (irule rich_listTheory.EL_FRONT >> fs[listTheory.NULL_EQ]) >>
  ntac 2 (pop_assum SUBST_ALL_TAC) >>
  qpat_x_assum `bb_well_formed bb`
    (strip_assume_tac o REWRITE_RULE [bb_well_formed_def]) >>
  qpat_x_assum `!i j. i < j /\ _ ==> _`
    (qspecl_then [`i`, `j`] mp_tac) >>
  simp[]
QED

Triviality transformed_bb_well_formed[local]:
  !bb1 bb' f.
    bb_well_formed bb1 /\
    bb'.bb_instructions = FLAT (MAP f bb1.bb_instructions) /\
    bb'.bb_instructions <> [] /\
    LAST bb'.bb_instructions = LAST bb1.bb_instructions /\
    FRONT bb'.bb_instructions = FLAT (MAP f (FRONT bb1.bb_instructions)) /\
    EVERY (\j. ~is_terminator j.inst_opcode)
      (FLAT (MAP f (FRONT bb1.bb_instructions))) /\
    (!inst. MEM inst (FRONT bb1.bb_instructions) /\
            inst.inst_opcode <> PHI ==>
      EVERY (\j. j.inst_opcode <> PHI) (f inst)) /\
    (!inst. MEM inst (FRONT bb1.bb_instructions) /\
            inst.inst_opcode = PHI ==>
      f inst = [inst]) ==>
    bb_well_formed bb'
Proof
  rpt strip_tac >>
  `bb1.bb_instructions <> []` by fs[bb_well_formed_def] >>
  `is_terminator (LAST bb1.bb_instructions).inst_opcode` by
    fs[bb_well_formed_def] >>
  qpat_x_assum `bb'.bb_instructions = _` kall_tac >>
  simp_tac std_ss [bb_well_formed_def] >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- fs[]
  >- (rpt strip_tac >>
      CCONTR_TAC >>
      `i < PRE (LENGTH bb'.bb_instructions)` by
        (Cases_on `bb'.bb_instructions` >> fs[] >> DECIDE_TAC) >>
      `EL i bb'.bb_instructions =
       EL i (FRONT bb'.bb_instructions)` by
        (irule (GSYM rich_listTheory.EL_FRONT) >>
         conj_tac >- simp[listTheory.NULL_EQ]
         >- (imp_res_tac rich_listTheory.FRONT_LENGTH >> DECIDE_TAC)) >>
      `MEM (EL i (FRONT bb'.bb_instructions))
           (FRONT bb'.bb_instructions)` by
        (simp_tac std_ss [listTheory.MEM_EL] >> qexists_tac `i` >>
         imp_res_tac rich_listTheory.FRONT_LENGTH >> DECIDE_TAC) >>
      `MEM (EL i (FRONT bb'.bb_instructions))
           (FLAT (MAP f (FRONT bb1.bb_instructions)))` by metis_tac[] >>
      qpat_x_assum `EVERY _ (FLAT (MAP f (FRONT _)))`
        (mp_tac o SIMP_RULE std_ss [listTheory.EVERY_MEM]) >>
      disch_then drule >> strip_tac >>
      qpat_x_assum `EL i bb'.bb_instructions = _` SUBST_ALL_TAC >>
      fs[])
  >- (rpt strip_tac >>
      `0 < LENGTH bb'.bb_instructions` by
        (Cases_on `bb'.bb_instructions` >> fs[]) >>
      Cases_on `j < PRE (LENGTH bb'.bb_instructions)`
      >- (`j < LENGTH (FRONT bb'.bb_instructions)` by
            (imp_res_tac rich_listTheory.FRONT_LENGTH >> DECIDE_TAC) >>
          `i < LENGTH (FRONT bb'.bb_instructions)` by
            (imp_res_tac rich_listTheory.FRONT_LENGTH >> DECIDE_TAC) >>
          drule bb_wf_front_phi_prefix >> strip_tac >>
          `!i j. i < j /\ j < LENGTH (FLAT (MAP f (FRONT bb1.bb_instructions))) /\
            (EL j (FLAT (MAP f (FRONT bb1.bb_instructions)))).inst_opcode = PHI ==>
            (EL i (FLAT (MAP f (FRONT bb1.bb_instructions)))).inst_opcode = PHI` by
            (match_mp_tac flat_map_preserves_phi_prefix >>
             rpt conj_tac
             >- first_assum ACCEPT_TAC
             >- (rpt strip_tac >> res_tac)
             >- (rpt strip_tac >> res_tac)) >>
          `EL j (FRONT bb'.bb_instructions) =
           EL j bb'.bb_instructions` by
            (irule rich_listTheory.EL_FRONT >> fs[listTheory.NULL_EQ]) >>
          `EL i (FRONT bb'.bb_instructions) =
           EL i bb'.bb_instructions` by
            (irule rich_listTheory.EL_FRONT >> fs[listTheory.NULL_EQ]) >>
          metis_tac[])
      >- (`j = PRE (LENGTH bb'.bb_instructions)` by DECIDE_TAC >>
          `EL j bb'.bb_instructions = LAST bb'.bb_instructions` by
            simp[rich_listTheory.EL_PRE_LENGTH] >>
          pop_assum SUBST_ALL_TAC >>
          `~is_terminator PHI` by simp[is_terminator_def] >>
          metis_tac[]))
QED

(* DROP past the PHI prefix commutes with the cmp_flip transform on the FRONT:
   the leading PHIs map to singletons, so dropping the prefix on the transformed
   FRONT equals transforming the dropped original FRONT. *)
Triviality cmp_flip_front_drop_eq[local]:
  !dfg fn1 lbl bb1 bb' mid flips removes inserts n.
    ao_cmp_flip_scan dfg (fn_insts fn1) = (flips, removes, inserts) /\
    dfg = dfg_build_function fn1 /\
    fn_inst_ids_distinct fn1 /\
    bb_well_formed bb1 /\
    lookup_block lbl fn1.fn_blocks = SOME bb1 /\
    FRONT bb'.bb_instructions =
      FLAT (MAP (ao_cmp_flip_apply_inst mid flips removes inserts)
                (FRONT bb1.bb_instructions)) /\
    n = phi_prefix_length bb1.bb_instructions ==>
    DROP n (FRONT bb'.bb_instructions) =
      FLAT (MAP (ao_cmp_flip_apply_inst mid flips removes inserts)
                (DROP n (FRONT bb1.bb_instructions)))
Proof
  rpt strip_tac >>
  qabbrev_tac `f = ao_cmp_flip_apply_inst mid flips removes inserts` >>
  qabbrev_tac `fr = FRONT bb1.bb_instructions` >>
  `bb1.bb_instructions <> []` by fs[bb_well_formed_def] >>
  `n <= LENGTH fr` by
    (qpat_x_assum `n = _` SUBST_ALL_TAC >> qunabbrev_tac `fr` >>
     irule ppl_le_front >> simp[]) >>
  `LENGTH fr < LENGTH bb1.bb_instructions` by
    (imp_res_tac rich_listTheory.FRONT_LENGTH >>
     gvs[Abbr `fr`] >> Cases_on `bb1.bb_instructions` >> fs[]) >>
  `!i. i < n ==> f (EL i fr) = [EL i fr]` by
    (rpt strip_tac >>
     `i < LENGTH bb1.bb_instructions` by gvs[] >>
     `EL i fr = EL i bb1.bb_instructions` by
       (qunabbrev_tac `fr` >> irule rich_listTheory.EL_FRONT >>
        gvs[listTheory.NULL_EQ]) >>
     `(EL i bb1.bb_instructions).inst_opcode = PHI` by
       (`EVERY (\inst. inst.inst_opcode = PHI)
           (TAKE n bb1.bb_instructions)` by simp[phi_prefix_all_phi] >>
        `MEM (EL i bb1.bb_instructions) (TAKE n bb1.bb_instructions)` by
          (simp[listTheory.MEM_EL] >> qexists_tac `i` >>
           simp[listTheory.LENGTH_TAKE_EQ, listTheory.EL_TAKE] >>
           qpat_x_assum `n <= LENGTH fr` mp_tac >> simp[Abbr `fr`] >>
           imp_res_tac rich_listTheory.FRONT_LENGTH >> simp[]) >>
        gvs[listTheory.EVERY_MEM]) >>
     `MEM (EL i bb1.bb_instructions) bb1.bb_instructions` by
       (simp[listTheory.MEM_EL] >> qexists_tac `i` >> simp[]) >>
     `MEM (EL i bb1.bb_instructions) (fn_insts fn1)` by
       metis_tac[block_inst_in_fn_insts] >>
     `ALOOKUP flips (EL i bb1.bb_instructions).inst_id = NONE /\
      ~MEM (EL i bb1.bb_instructions).inst_id removes /\
      ALOOKUP inserts (EL i bb1.bb_instructions).inst_id = NONE` by
       (match_mp_tac scan_phi_untouched >>
        qexistsl_tac [`dfg`, `fn_insts fn1`] >>
        simp[] >> rpt conj_tac
        >- (irule fn_insts_ids_all_distinct >> simp[])
        >- (rpt strip_tac >> gvs[] >>
            drule_all dfgAnalysisPropsTheory.dfg_build_function_uses_sound >>
            simp[])) >>
     simp[Abbr `f`] >> irule apply_untouched >> simp[]) >>
  `fr = TAKE n fr ++ DROP n fr` by simp[listTheory.TAKE_DROP] >>
  `FLAT (MAP f fr) = TAKE n fr ++ FLAT (MAP f (DROP n fr))` by
    (pop_assum (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV[th]))) >>
     simp[listTheory.MAP_APPEND, rich_listTheory.FLAT_APPEND] >>
     irule flat_map_singleton_id >> rpt strip_tac >>
     gvs[listTheory.MEM_EL, listTheory.LENGTH_TAKE_EQ, listTheory.EL_TAKE]) >>
  `LENGTH (TAKE n fr) = n` by simp[listTheory.LENGTH_TAKE_EQ] >>
  qpat_x_assum `FRONT bb'.bb_instructions = FLAT (MAP f fr)`
    (fn th => REWRITE_TAC[th]) >>
  qpat_x_assum `FLAT (MAP f fr) = TAKE n fr ++ _`
    (fn th => REWRITE_TAC[th]) >>
  metis_tac[rich_listTheory.DROP_LENGTH_APPEND]
QED

(* For OK outputs, iszero_inv is preserved through run_block.
   Uses: body sim gives iszero_inv, terminator preserves all vars. *)
Theorem ao_cmp_flip_block_ok_inv:
  !mid dfg fn1 lbl bb1 bb' fuel ctx s1 s2 s1' s2'.
    let dead = ao_cmp_flip_dead_vars dfg fn1 in
    let flips = FST (ao_cmp_flip_scan dfg (fn_insts fn1)) in
    dfg = dfg_build_function fn1 /\

    (!inst. MEM inst (fn_insts fn1) ==> inst_wf inst) /\
    (!inst v. MEM inst (fn_insts fn1) /\ MEM (Var v) inst.inst_operands ==>
      v NOTIN ao_cmp_fresh_vars fn1) /\
    fn_inst_ids_distinct fn1 /\
    ssa_form fn1 /\
    bb_well_formed bb1 /\
    lookup_block lbl fn1.fn_blocks = SOME bb1 /\
    lookup_block lbl (ao_cmp_flip_function mid dfg fn1).fn_blocks = SOME bb' /\
    state_equiv dead s1 s2 /\
    cmp_flip_iszero_inv flips (fn_insts fn1) s1 s2 /\
    run_block fuel ctx bb1 s1 = OK s1' /\
    run_block fuel ctx bb' s2 = OK s2' ==>
    cmp_flip_iszero_inv flips (fn_insts fn1) s1' s2'
Proof
  simp_tac std_ss [LET_THM] >> rpt gen_tac >> strip_tac >>
  Cases_on `NULL (FST (ao_cmp_flip_scan (dfg_build_function fn1) (fn_insts fn1)))`
  >- (`FST (ao_cmp_flip_scan (dfg_build_function fn1) (fn_insts fn1)) = []` by
        (Cases_on `ao_cmp_flip_scan (dfg_build_function fn1) (fn_insts fn1)` >>
         Cases_on `r` >> gvs[listTheory.NULL_EQ]) >>
      rw[cmp_flip_iszero_inv_def] >> gvs[alistTheory.ALOOKUP_def])
  >>
  Cases_on `ao_cmp_flip_scan (dfg_build_function fn1) (fn_insts fn1)` >>
  Cases_on `r` >> gvs[] >>
  rename1 `_ = (flips', removes, inserts)` >>
  qabbrev_tac `f = ao_cmp_flip_apply_inst mid flips' removes inserts` >>
  `bb1.bb_instructions <> []` by fs[bb_well_formed_def] >>
  `bb'.bb_instructions = FLAT (MAP f bb1.bb_instructions) /\
   bb'.bb_label = bb1.bb_label` by
    (simp[Abbr `f`] >> metis_tac[cmp_flip_block_structure]) >>
  `ALOOKUP flips' (LAST bb1.bb_instructions).inst_id = NONE /\
   ~MEM (LAST bb1.bb_instructions).inst_id removes /\
   ALOOKUP inserts (LAST bb1.bb_instructions).inst_id = NONE` by
    metis_tac[last_untouched,
              dfgAnalysisPropsTheory.dfg_build_function_uses_sound] >>
  `FRONT bb'.bb_instructions = FLAT (MAP f (FRONT bb1.bb_instructions)) /\
   LAST bb'.bb_instructions = LAST bb1.bb_instructions /\
   bb'.bb_instructions <> []` by
    (qunabbrev_tac `f` >> gvs[] >>
     irule transformed_block_front_last >> simp[]) >>
  `EVERY (\j. ~is_terminator j.inst_opcode)
     (FLAT (MAP f (FRONT bb1.bb_instructions)))` by
    (simp[listTheory.EVERY_MEM, listTheory.MEM_FLAT, listTheory.MEM_MAP,
           PULL_EXISTS] >>
     rpt strip_tac >> rename1 `MEM inst1 (FRONT bb1.bb_instructions)` >>
     `~is_terminator inst1.inst_opcode` by
       (imp_res_tac front_non_terminators >> gvs[listTheory.EVERY_MEM]) >>
     `MEM inst1 bb1.bb_instructions` by
       metis_tac[rich_listTheory.MEM_FRONT_NOT_NIL] >>
     simp[Abbr `f`] >>
     `EVERY (\j. ~is_terminator j.inst_opcode)
        (ao_cmp_flip_apply_inst mid flips' removes inserts inst1)` by
       (match_mp_tac apply_inst_every_non_term_non_invoke >>
        simp[] >>
        rpt strip_tac >> drule_all scan_flips_opcode_non_term >> simp[]) >>
     qpat_x_assum `EVERY _ (ao_cmp_flip_apply_inst _ _ _ _ _)`
       (mp_tac o SIMP_RULE std_ss [listTheory.EVERY_MEM]) >>
     disch_then drule >> simp[]) >>
  sg `bb_well_formed bb'`
  >- (match_mp_tac transformed_bb_well_formed >>
      qexistsl_tac [`bb1`, `f`] >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY (simp[])
      >- (rpt strip_tac >> simp[Abbr `f`] >>
          match_mp_tac apply_inst_non_phi >> simp[] >>
          rpt strip_tac >>
          drule_all scan_flip_info >> strip_tac >> gvs[] >>
          imp_res_tac flip_comparison_not_phi)
      >- (rpt strip_tac >>
          `MEM inst (fn_insts fn1)` by
            (imp_res_tac rich_listTheory.MEM_FRONT_NOT_NIL >>
             imp_res_tac block_inst_in_fn_insts >> gvs[]) >>
          `ALOOKUP flips' inst.inst_id = NONE /\
           ~MEM inst.inst_id removes /\
           ALOOKUP inserts inst.inst_id = NONE` by
            (match_mp_tac scan_phi_untouched >>
             qexistsl_tac [`dfg_build_function fn1`, `fn_insts fn1`] >>
             simp[] >> rpt conj_tac
             >- (irule fn_insts_ids_all_distinct >> simp[])
             >- (rpt strip_tac >>
                 drule_all dfgAnalysisPropsTheory.dfg_build_function_uses_sound >>
                 simp[])) >>
          simp[Abbr `f`] >> irule apply_untouched >> simp[])) >>
  (* eval_phis / ppl bridge *)
  `(!s. eval_phis s bb'.bb_instructions = eval_phis s bb1.bb_instructions) /\
   phi_prefix_length bb'.bb_instructions =
     phi_prefix_length bb1.bb_instructions` by
    (irule cmp_flip_eval_phis_eq >>
     simp[Abbr `f`] >>
     qexistsl_tac [`flips'`, `fn1`, `inserts`, `lbl`, `mid`, `removes`] >>
     simp[]) >>
  `DROP (phi_prefix_length bb1.bb_instructions) (FRONT bb'.bb_instructions) =
     FLAT (MAP f (DROP (phi_prefix_length bb1.bb_instructions)
                       (FRONT bb1.bb_instructions)))` by
    (qunabbrev_tac `f` >> irule cmp_flip_front_drop_eq >>
     rpt conj_tac >>
     TRY (qexistsl_tac [`dfg_build_function fn1`, `fn1`, `lbl`]) >>
     simp[]) >>
  `phi_prefix_length bb1.bb_instructions <= LENGTH (FRONT bb1.bb_instructions)` by
    (irule ppl_le_front >> simp[]) >>
  `phi_prefix_length bb1.bb_instructions <= LENGTH (FRONT bb'.bb_instructions)` by
    (`phi_prefix_length bb1.bb_instructions =
      phi_prefix_length bb'.bb_instructions` by simp[] >>
     pop_assum SUBST1_TAC >> irule ppl_le_front >> simp[]) >>
  (* PHI operands are never dead *)
  `EVERY (\inst. inst.inst_opcode = PHI ==>
            !x. MEM (Var x) inst.inst_operands ==>
              x NOTIN ao_cmp_flip_dead_vars (dfg_build_function fn1) fn1)
          bb1.bb_instructions` by
    (simp[listTheory.EVERY_MEM] >> rpt strip_tac >>
     `MEM inst (fn_insts fn1)` by metis_tac[block_inst_in_fn_insts] >>
     `x NOTIN ao_cmp_flip_dead_vars (dfg_build_function fn1) fn1`
       suffices_by simp[] >>
     irule operand_not_dead >> metis_tac[]) >>
  (* decompose run_block hypotheses *)
  qpat_x_assum `run_block fuel ctx bb1 s1 = OK s1'` mp_tac >>
  simp[run_block_def] >>
  `(?sp1. eval_phis s1 bb1.bb_instructions = OK sp1) \/
   (?e. eval_phis s1 bb1.bb_instructions = Error e)` by
    metis_tac[eval_phis_ok_or_error_defs] >>
  pop_assum strip_assume_tac >> simp[] >>
  rename1 `eval_phis s1 bb1.bb_instructions = OK sp1` >> strip_tac >>
  drule_all venomExecProofsTheory.eval_phis_state_equiv >> strip_tac >>
  rename1 `eval_phis s2 bb1.bb_instructions = OK sp2` >>
  qpat_x_assum `run_block fuel ctx bb' s2 = OK s2'` mp_tac >>
  simp[run_block_def] >>
  qpat_x_assum `!s. eval_phis s bb'.bb_instructions = _`
    (fn th => simp[th]) >>
  qpat_x_assum `phi_prefix_length bb'.bb_instructions = _`
    (fn th => simp[th]) >>
  strip_tac >>
  (* sp-level state_equiv and iszero invariant *)
  `cmp_flip_iszero_inv flips' (fn_insts fn1) sp1 sp2` by
    (qspecl_then [`dfg_build_function fn1`, `fn1`, `flips'`, `removes`,
                  `inserts`, `s1`, `s2`, `sp1`, `sp2`, `bb1.bb_instructions`]
       mp_tac cmp_flip_iszero_inv_eval_phis >>
     impl_tac
     >- (simp[] >> rpt strip_tac >>
         irule block_inst_in_fn_insts >> qexistsl_tac [`bb1`, `lbl`] >> simp[])
     >> simp[]) >>
  `state_equiv (ao_cmp_flip_dead_vars (dfg_build_function fn1) fn1)
     (sp1 with vs_inst_idx := phi_prefix_length bb1.bb_instructions)
     (sp2 with vs_inst_idx := phi_prefix_length bb1.bb_instructions)` by
    (irule state_equiv_idx_update >> simp[]) >>
  `cmp_flip_iszero_inv flips' (fn_insts fn1)
     (sp1 with vs_inst_idx := phi_prefix_length bb1.bb_instructions)
     (sp2 with vs_inst_idx := phi_prefix_length bb1.bb_instructions)` by
    (irule iszero_inv_lookup_eq >> qexistsl_tac [`sp1`, `sp2`] >>
     simp[lookup_var_def]) >>
  (* body-end states and terminator variable preservation *)
  sg `?v. run_insts fuel ctx
            (DROP (phi_prefix_length bb1.bb_instructions)
                  (FRONT bb1.bb_instructions))
            (sp1 with vs_inst_idx := phi_prefix_length bb1.bb_instructions) = OK v /\
          !x. lookup_var x s1' = lookup_var x v`
  >- (irule exec_block_ok_lookup_body >> simp[]) >>
  sg `?v'. run_insts fuel ctx
             (DROP (phi_prefix_length bb1.bb_instructions)
                   (FRONT bb'.bb_instructions))
             (sp2 with vs_inst_idx := phi_prefix_length bb1.bb_instructions) = OK v' /\
           !x. lookup_var x s2' = lookup_var x v'`
  >- (irule exec_block_ok_lookup_body >> simp[]) >>
  qpat_x_assum `DROP _ (FRONT bb'.bb_instructions) = _`
    (fn th => fs[th]) >>
  sg `lift_result
     (\s1' s2'. state_equiv
       (ao_cmp_flip_dead_vars (dfg_build_function fn1) fn1) s1' s2' /\
       cmp_flip_iszero_inv flips' (fn_insts fn1) s1' s2')
     (execution_equiv (ao_cmp_flip_dead_vars (dfg_build_function fn1) fn1))
     (execution_equiv (ao_cmp_flip_dead_vars (dfg_build_function fn1) fn1))
     (run_insts fuel ctx
        (DROP (phi_prefix_length bb1.bb_instructions)
              (FRONT bb1.bb_instructions))
        (sp1 with vs_inst_idx := phi_prefix_length bb1.bb_instructions))
     (run_insts fuel ctx
        (FLAT (MAP f (DROP (phi_prefix_length bb1.bb_instructions)
                           (FRONT bb1.bb_instructions))))
        (sp2 with vs_inst_idx := phi_prefix_length bb1.bb_instructions))`
  >- (qunabbrev_tac `f` >>
      match_mp_tac non_null_body_sim >>
      qexistsl_tac [`dfg_build_function fn1`, `lbl`] >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
  gvs[lift_result_def] >>
  irule iszero_inv_lookup_eq >>
  qexistsl_tac [`v`, `v'`] >> simp[]
QED

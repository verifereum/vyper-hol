(*
 * Fragment fuel bounds
 *
 * The lowering's code runs within a number of blocks that does not depend
 * on the state it starts from.  frag_fuel says so of the code a compile
 * action emits between two compile states, in any function containing it:
 * from the point where the first state left off, or from the start of a
 * block the code begins, the run either reaches the point where the second
 * state leaves off, jumps to one of a set of exit labels, or ends with a
 * result that no longer changes with more fuel, all within a bounded
 * number of blocks.  Every loop the lowering emits counts a bounded counter
 * towards its exit, so the bounds compose.
 *
 * Fuel enters a function's run twice: one unit per block entered, and the
 * remaining fuel of the calling block for an INVOKE's callee.  The judgment
 * is relative to a bound G on the callees: an INVOKE gives the same result
 * at every fuel from G on (fuel_stable).
 *
 * TOP-LEVEL:
 *   no_phi_fn, fuel_stable, callees_stable — the function-level notions
 *   var_below, vars_kept   — the variables a fragment leaves alone
 *   at_point               — a state at the point a compile state left off
 *   fuel_outcome           — the outcome of a run from one state
 *   frag_fuel              — the fragment judgment
 *   cs_no_phi, fuel_ok     — the judgment of a compile action
 *   fuel_ok_bind, fuel_ok_fresh_var, fuel_ok_emit, fuel_ok_emit_jmp,
 *   fuel_ok_emit_jnz, fuel_ok_emit_halt, fuel_ok_new_block — its rules
 *   fuel_outcome_iterate   — a loop whose measure drops each round
 *   fuel_stable_of_frag    — a function whose body is a fragment
 *)

Theory fragFuel
Ancestors
  list rich_list pred_set arithmetic compileEnv emitHelper
  venomExecSemantics venomExecProofs venomExecProps venomInst venomInstProps
  venomState fragExec

(* ===== Definitions ===== *)

(* No block starts with a PHI.  The lowering emits none, and then entering
   a block is running it from its first instruction. *)
Definition no_phi_fn_def:
  no_phi_fn fn <=>
    EVERY (\bb. phi_prefix_length bb.bb_instructions = 0) fn.fn_blocks
End

(* From fuel G on, a call of fn gives the same result. *)
Definition fuel_stable_def:
  fuel_stable G ctx fn <=>
    !s f. G <= f /\ fn.fn_blocks <> [] /\
          s.vs_current_bb = (HD fn.fn_blocks).bb_label /\ s.vs_inst_idx = 0 ==>
          run_blocks f ctx fn s = run_blocks G ctx fn s
End

Definition callees_stable_def:
  callees_stable G ctx fn <=>
    !inst name args callee.
      MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE /\
      decode_invoke inst = SOME (name, args) /\
      lookup_function name ctx.ctx_functions = SOME callee ==>
      fuel_stable G ctx callee
End

(* x is not one of the variables fresh_var hands out from N on. *)
Definition var_below_def:
  var_below N x <=> !n. N <= n ==> x <> STRING #"%" (toString n)
End

Definition vars_kept_def:
  vars_kept N Wv s t <=>
    !x. var_below N x /\ x NOTIN Wv ==> lookup_var x t = lookup_var x s
End

Definition at_point_def:
  at_point (st:compile_state) (s:venom_state) <=>
    s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts
End

(* Running fn from s with j more blocks of fuel either is running it from a
   state t satisfying P, or gives one result from fuel G + j on. *)
Definition fuel_outcome_def:
  fuel_outcome G ctx fn s j P <=>
    (?t. P t /\ !f. G <= f ==> run_from (f + j) ctx fn s = run_from f ctx fn t) \/
    (!f. G <= f ==> run_from (f + j) ctx fn s = run_from (G + j) ctx fn s)
End

(* The fragment judgment.  Entered where st left off, or at the start of a
   block labelled in L, the code emitted between st and st' reaches the
   point where st' leaves off, or a jump to a label in E, within Kb blocks,
   keeping the variables below N other than those in Wv; or its result is
   fixed from fuel G + Kb on. *)
Definition frag_fuel_def:
  frag_fuel Wv L E (st:compile_state) (st':compile_state) Kb <=>
    !G N ctx fn s.
      N <= st.cs_next_var /\ no_phi_fn fn /\ fn_has_code st st' fn /\
      callees_stable G ctx fn /\
      (at_point st s \/ (s.vs_current_bb IN L /\ s.vs_inst_idx = 0)) ==>
      ?j. j <= Kb /\
          fuel_outcome G ctx fn s j
            (\t. vars_kept N Wv s t /\
                 (at_point st' t \/ (t.vs_current_bb IN E /\ t.vs_inst_idx = 0)))
End

Definition cs_no_phi_def:
  cs_no_phi (st:compile_state) <=>
    EVERY (\bb. EVERY (\i. i.inst_opcode <> PHI) bb.bb_instructions)
      st.cs_blocks /\
    EVERY (\i. i.inst_opcode <> PHI) st.cs_current_insts
End

Definition fuel_ok_def:
  fuel_ok Wv L E (m : 'a compiler) <=>
    !st x st'. m st = (x, st') ==>
      cs_extends st st' /\ st.cs_next_var <= st'.cs_next_var /\
      (cs_no_phi st ==> cs_no_phi st') /\
      ?Kb. frag_fuel Wv L E st st' Kb
End

(* ===== Running instructions ===== *)

Theorem run_from_nonterm:
  !f ctx fn s bb inst.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    ~is_terminator inst.inst_opcode ==>
    run_from f ctx fn s =
      case step_inst f ctx inst s of
        OK s1 => run_from f ctx fn (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      | IntRet v s1 => IntRet v s1
      | Halt s1 => Halt s1
      | Abort a s1 => Abort a s1
      | Error e => Error e
Proof
  rpt strip_tac >>
  simp[run_from_def, Once exec_block_def] >>
  Cases_on `step_inst f ctx inst s` >> simp[] >>
  drule_all step_preserves_control_flow >> simp[]
QED

Theorem step_inst_fuel_stable:
  !G f ctx fn inst s.
    callees_stable G ctx fn /\ MEM inst (fn_insts fn) /\ G <= f ==>
    step_inst f ctx inst s = step_inst G ctx inst s
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE` >> simp[step_inst_non_invoke] >>
  simp[Once step_inst_def] >> CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [step_inst_def])) >>
  simp[] >>
  Cases_on `decode_invoke inst` >> simp[] >>
  rename1 `decode_invoke inst = SOME p` >> PairCases_on `p` >> simp[] >>
  Cases_on `lookup_function p0 ctx.ctx_functions` >> simp[] >>
  Cases_on `eval_operands p1 s` >> simp[] >>
  Cases_on `setup_callee x x' s` >> simp[] >>
  rename1 `lookup_function _ _ = SOME callee` >>
  rename1 `setup_callee _ _ _ = SOME cs` >>
  `fuel_stable G ctx callee` by metis_tac[callees_stable_def] >>
  `run_blocks f ctx callee cs = run_blocks G ctx callee cs` suffices_by simp[] >>
  gvs[fuel_stable_def, setup_callee_def] >>
  first_x_assum irule >> simp[] >> Cases_on `callee.fn_blocks` >> gvs[]
QED

Theorem lookup_block_get_instruction_fn_insts:
  !lbl fn bb i inst.
    lookup_block lbl fn.fn_blocks = SOME bb /\
    get_instruction bb i = SOME inst ==>
    MEM inst (fn_insts fn)
Proof
  rw[get_instruction_def] >> irule lookup_block_fn_insts >>
  qexistsl_tac [`bb`, `lbl`] >> simp[MEM_EL] >> metis_tac[]
QED

(* A non-terminator either steps to the next instruction, the same way at
   every fuel from G on, or gives one result from G on. *)
Theorem run_from_nonterm_stable:
  !G ctx fn s bb inst.
    callees_stable G ctx fn /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    ~is_terminator inst.inst_opcode ==>
    (?s1. step_inst G ctx inst s = OK s1 /\
          (!x. ~MEM x inst.inst_outputs ==> lookup_var x s1 = lookup_var x s) /\
          s1.vs_current_bb = s.vs_current_bb /\
          !f. G <= f ==>
              run_from f ctx fn s =
              run_from f ctx fn (s1 with vs_inst_idx := SUC s.vs_inst_idx)) \/
    (!f. G <= f ==> run_from f ctx fn s = run_from G ctx fn s)
Proof
  rpt strip_tac >>
  `MEM inst (fn_insts fn)` by metis_tac[lookup_block_get_instruction_fn_insts] >>
  `!f. G <= f ==> step_inst f ctx inst s = step_inst G ctx inst s` by
    metis_tac[step_inst_fuel_stable] >>
  `!f. run_from f ctx fn s =
       case step_inst f ctx inst s of
         OK s1 => run_from f ctx fn (s1 with vs_inst_idx := SUC s.vs_inst_idx)
       | IntRet v s1 => IntRet v s1
       | Halt s1 => Halt s1
       | Abort a s1 => Abort a s1
       | Error e => Error e` by metis_tac[run_from_nonterm] >>
  Cases_on `step_inst G ctx inst s`
  >- (disj1_tac >> simp[] >>
      metis_tac[step_preserves_non_output_vars, step_preserves_control_flow]) >>
  disj2_tac >> rw[] >> gvs[]
QED

Theorem jump_to_vars[simp]:
  lookup_var x (jump_to lbl s) = lookup_var x s
Proof
  simp[jump_to_def, lookup_var_def]
QED

(* With no PHIs, a jump costs exactly one unit of fuel. *)
Theorem run_from_jump_exact:
  !f ctx fn s bb inst lbl.
    no_phi_fn fn /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
    step_inst_base inst s = OK (jump_to lbl s) /\ ~s.vs_halted ==>
    run_from (SUC f) ctx fn s = run_from f ctx fn (jump_to lbl s)
Proof
  rpt strip_tac >>
  Cases_on `lookup_block lbl fn.fn_blocks`
  >- (`exec_block (SUC f) ctx bb s = OK (jump_to lbl s)` by
        simp[Once exec_block_def, step_inst_non_invoke, jump_to_def] >>
      simp[run_from_def] >> simp[Once run_blocks_def] >>
      simp[jump_to_def]) >>
  irule run_from_jump >> simp[] >>
  drule lookup_block_MEM >> fs[no_phi_fn_def, EVERY_MEM]
QED

(* A jump from a halted state is the result. *)
Theorem run_from_jump_halted:
  !f ctx fn s bb inst lbl.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
    step_inst_base inst s = OK (jump_to lbl s) /\ s.vs_halted ==>
    run_from f ctx fn s = Halt (jump_to lbl s)
Proof
  rpt strip_tac >>
  simp[run_from_def, Once exec_block_def, step_inst_non_invoke, jump_to_def]
QED

(* ===== Outcomes ===== *)

Theorem fuel_outcome_refl:
  !G ctx fn s P. P s ==> fuel_outcome G ctx fn s 0 P
Proof
  rw[fuel_outcome_def] >> disj1_tac >> qexists_tac `s` >> simp[]
QED

Theorem fuel_outcome_weaken:
  !G ctx fn s j P Q.
    fuel_outcome G ctx fn s j P /\ (!t. P t ==> Q t) ==>
    fuel_outcome G ctx fn s j Q
Proof
  rw[fuel_outcome_def] >> metis_tac[]
QED

Theorem fuel_outcome_compose:
  !G ctx fn s j1 P Q K2.
    fuel_outcome G ctx fn s j1 P /\
    (!t. P t ==> ?j2. j2 <= K2 /\ fuel_outcome G ctx fn t j2 Q) ==>
    ?j. j <= j1 + K2 /\ fuel_outcome G ctx fn s j Q
Proof
  rw[fuel_outcome_def]
  >- (first_x_assum drule >> strip_tac
      >- (qexists_tac `j1 + j2` >> simp[] >> disj1_tac >>
          goal_assum (drule_at Any) >> rpt strip_tac >>
          `f + (j1 + j2) = (f + j2) + j1` by decide_tac >>
          `run_from (f + j2 + j1) ctx fn s = run_from (f + j2) ctx fn t`
            by (first_x_assum irule >> decide_tac) >>
          metis_tac[])
      >- (qexists_tac `j1 + j2` >> simp[] >> disj2_tac >> rpt strip_tac >>
          `f + (j1 + j2) = (f + j2) + j1 /\ G + (j1 + j2) = (G + j2) + j1`
            by decide_tac >>
          `run_from (f + j2 + j1) ctx fn s = run_from (f + j2) ctx fn t /\
           run_from (G + j2 + j1) ctx fn s = run_from (G + j2) ctx fn t`
            by (conj_tac >> first_x_assum irule >> decide_tac) >>
          `G <= G:num` by simp[] >> metis_tac[])) >>
  qexists_tac `j1` >> simp[]
QED

Theorem fuel_outcome_jump:
  !G ctx fn s j P lbl bb inst.
    no_phi_fn fn /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
    step_inst_base inst s = OK (jump_to lbl s) /\
    (~s.vs_halted ==> P (jump_to lbl s)) ==>
    fuel_outcome G ctx fn s 1 P
Proof
  rpt strip_tac >> simp[fuel_outcome_def] >>
  Cases_on `s.vs_halted`
  >- (disj2_tac >> metis_tac[run_from_jump_halted]) >>
  disj1_tac >> qexists_tac `jump_to lbl s` >> simp[] >> rpt strip_tac >>
  `f + 1 = SUC f` by decide_tac >> simp[] >>
  irule run_from_jump_exact >> simp[] >> metis_tac[]
QED

(* A loop whose measure, below M, drops on every round that does not leave
   it, leaves it within M rounds. *)
Theorem fuel_outcome_iterate:
  !G ctx fn H Q mu M Kb.
    (!s. H s ==> mu s < M) /\
    (!s. H s ==> ?j. j <= Kb /\
                     fuel_outcome G ctx fn s j (\t. Q t \/ (H t /\ mu t < mu s))) ==>
    !s. H s ==> ?j. j <= M * Kb /\ fuel_outcome G ctx fn s j Q
Proof
  rpt gen_tac >> strip_tac >>
  `!n s. H s /\ mu s = n ==> ?j. j <= (n + 1) * Kb /\ fuel_outcome G ctx fn s j Q`
    suffices_by
      (rpt strip_tac >> first_x_assum (qspecl_then [`mu s`, `s`] mp_tac) >>
       simp[] >> strip_tac >> qexists_tac `j` >> simp[] >>
       `mu s + 1 <= M` by metis_tac[DECIDE ``a < b ==> a + 1 <= b:num``] >>
       `(mu s + 1) * Kb <= M * Kb` by simp[] >> decide_tac) >>
  completeInduct_on `n` >> rpt strip_tac >>
  first_x_assum (drule_then strip_assume_tac) >>
  drule fuel_outcome_compose >>
  disch_then (qspecl_then [`Q`, `n * Kb`] mp_tac) >>
  impl_tac
  >- (rpt gen_tac >> BETA_TAC >> strip_tac
      >- (qexists_tac `0` >> simp[fuel_outcome_refl]) >>
      first_x_assum (qspec_then `mu t` mp_tac) >> impl_tac >- gvs[] >>
      disch_then (qspec_then `t` mp_tac) >> simp[] >>
      disch_then (qx_choose_then `jt` strip_assume_tac) >>
      qexists_tac `jt` >> simp[] >>
      irule LESS_EQ_TRANS >> qexists_tac `(mu t + 1) * Kb` >>
      simp[LE_MULT_RCANCEL] >> gvs[]) >>
  disch_then (qx_choose_then `jj` strip_assume_tac) >>
  qexists_tac `jj` >> simp[] >>
  `(n + 1) * Kb = Kb + n * Kb` by simp[RIGHT_ADD_DISTRIB] >> decide_tac
QED

(* ===== Variables ===== *)

Theorem vars_kept_refl[simp]:
  vars_kept N Wv s s
Proof
  simp[vars_kept_def]
QED

Theorem vars_kept_trans:
  vars_kept N Wv s t /\ vars_kept N Wv t u ==> vars_kept N Wv s u
Proof
  simp[vars_kept_def]
QED

Theorem vars_kept_mono:
  vars_kept N Wv s t /\ Wv SUBSET Wv' ==> vars_kept N Wv' s t
Proof
  rw[vars_kept_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem var_below_fresh:
  N <= n ==> ~var_below N (STRING #"%" (toString n))
Proof
  rw[var_below_def] >> metis_tac[]
QED

Theorem vars_kept_fresh:
  vars_kept N (STRING #"%" (toString n) INSERT Wv) s t /\ N <= n ==>
  vars_kept N Wv s t
Proof
  rw[vars_kept_def] >> first_x_assum irule >> simp[] >>
  metis_tac[var_below_fresh]
QED

(* ===== The judgment ===== *)

Theorem frag_fuel_mono:
  frag_fuel Wv L E st st' Kb /\ Wv SUBSET Wv' /\ L' SUBSET L /\ E SUBSET E' /\
  Kb <= Kb' ==>
  frag_fuel Wv' L' E' st st' Kb'
Proof
  simp[frag_fuel_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
  `?j. j <= Kb /\
       fuel_outcome G ctx fn s j
         (\t. vars_kept N Wv s t /\
              (at_point st' t \/ (t.vs_current_bb IN E /\ t.vs_inst_idx = 0)))` by
    (first_x_assum irule >> fs[SUBSET_DEF]) >>
  qexists_tac `j` >> simp[] >>
  irule fuel_outcome_weaken >> goal_assum (drule_at Any) >>
  simp[] >> rpt strip_tac >> fs[SUBSET_DEF] >>
  metis_tac[vars_kept_mono, SUBSET_DEF]
QED

Theorem fuel_ok_mono:
  fuel_ok Wv L E m /\ Wv SUBSET Wv' /\ L' SUBSET L /\ E SUBSET E' ==>
  fuel_ok Wv' L' E' m
Proof
  rw[fuel_ok_def] >> first_x_assum drule >> rw[] >>
  qexists_tac `Kb` >> irule frag_fuel_mono >> qexistsl_tac [`E`,`Kb`,`L`,`Wv`] >> simp[]
QED

Theorem fuel_ok_return:
  !x. fuel_ok Wv {} E (comp_return x)
Proof
  rw[fuel_ok_def, comp_return_def, cs_extends_refl] >>
  qexists_tac `0` >> rw[frag_fuel_def] >>
  simp[] >> irule fuel_outcome_refl >> simp[]
QED

Theorem frag_fuel_seq:
  !Wv L1 L2 E1 E2 E st mid st' K1 K2.
    frag_fuel Wv L1 E1 st mid K1 /\ frag_fuel Wv L2 E2 mid st' K2 /\
    cs_extends st mid /\ cs_extends mid st' /\
    st.cs_next_var <= mid.cs_next_var /\
    E1 SUBSET E UNION L2 /\ E2 SUBSET E ==>
    frag_fuel Wv (L1 UNION L2) E st st' (K1 + K2)
Proof
  rpt strip_tac >> PURE_REWRITE_TAC[frag_fuel_def] >> rpt gen_tac >>
  disch_then (CONJUNCTS_THEN assume_tac) >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  `fn_has_code st mid fn /\ fn_has_code mid st' fn` by
    metis_tac[fn_has_code_split] >>
  `N <= mid.cs_next_var` by decide_tac >>
  `!t. at_point mid t \/ (t.vs_current_bb IN L2 /\ t.vs_inst_idx = 0) ==>
       ?j2. j2 <= K2 /\
            fuel_outcome G ctx fn t j2
              (\u. vars_kept N Wv t u /\
                   (at_point st' u \/ (u.vs_current_bb IN E /\ u.vs_inst_idx = 0)))` by
    (gen_tac >> disch_tac >>
     qpat_x_assum `frag_fuel Wv L2 E2 mid st' K2`
       (mp_tac o SIMP_RULE std_ss [frag_fuel_def]) >>
     disch_then (qspecl_then [`G`, `N`, `ctx`, `fn`, `t`] mp_tac) >>
     impl_tac >- simp[] >>
     disch_then (qx_choose_then `jt` strip_assume_tac) >>
     qexists_tac `jt` >> simp[] >>
     irule fuel_outcome_weaken >> goal_assum (drule_at Any) >>
     simp[] >> rpt strip_tac >> fs[SUBSET_DEF]) >>
  `!t. at_point st t \/ (t.vs_current_bb IN L1 /\ t.vs_inst_idx = 0) ==>
       ?j. j <= K1 + K2 /\
           fuel_outcome G ctx fn t j
             (\u. vars_kept N Wv t u /\
                  (at_point st' u \/ (u.vs_current_bb IN E /\ u.vs_inst_idx = 0)))` by
    (gen_tac >> disch_tac >>
     qpat_x_assum `frag_fuel Wv L1 E1 st mid K1`
       (mp_tac o SIMP_RULE std_ss [frag_fuel_def]) >>
     disch_then (qspecl_then [`G`, `N`, `ctx`, `fn`, `t`] mp_tac) >>
     impl_tac >- simp[] >>
     disch_then (qx_choose_then `j1` strip_assume_tac) >>
     drule fuel_outcome_compose >>
     disch_then (qspecl_then
       [`\u. vars_kept N Wv t u /\
             (at_point st' u \/ (u.vs_current_bb IN E /\ u.vs_inst_idx = 0))`,
        `K2`] mp_tac) >>
     impl_tac
     >- (qx_gen_tac `u` >> BETA_TAC >> disch_then (CONJUNCTS_THEN assume_tac) >>
         Cases_on `at_point mid u \/ (u.vs_current_bb IN L2 /\ u.vs_inst_idx = 0)`
         >- (qpat_x_assum `!t. at_point mid t \/ _ ==> _`
               (qspec_then `u` mp_tac) >>
             impl_tac >- simp[] >>
             disch_then (qx_choose_then `j2` strip_assume_tac) >>
             qexists_tac `j2` >> simp[] >>
             irule fuel_outcome_weaken >> goal_assum (drule_at Any) >>
             simp[] >> metis_tac[vars_kept_trans]) >>
         qexists_tac `0` >> simp[] >> irule fuel_outcome_refl >> simp[] >>
         fs[SUBSET_DEF] >> metis_tac[]) >>
     disch_then (qx_choose_then `jj` strip_assume_tac) >>
     qexists_tac `jj` >> simp[]) >>
  qpat_x_assum `at_point st s \/ _` mp_tac >> rewrite_tac[IN_UNION] >>
  disch_then (DISJ_CASES_THEN2 assume_tac
    (CONJUNCTS_THEN2 (DISJ_CASES_THEN assume_tac) assume_tac))
  >- (qpat_x_assum `!t. at_point st t \/ _ ==> _` (qspec_then `s` mp_tac) >>
      impl_tac >- simp[] >> disch_then ACCEPT_TAC)
  >- (qpat_x_assum `!t. at_point st t \/ _ ==> _` (qspec_then `s` mp_tac) >>
      impl_tac >- simp[] >> disch_then ACCEPT_TAC) >>
  qpat_x_assum `!t. at_point mid t \/ _ ==> _` (qspec_then `s` mp_tac) >>
  impl_tac >- simp[] >>
  disch_then (qx_choose_then `j2` strip_assume_tac) >>
  qexists_tac `j2` >> simp[]
QED

Theorem fuel_ok_bind:
  !m f Wv L1 L2 E1 E2 E.
    fuel_ok Wv L1 E1 m /\ (!a. fuel_ok Wv L2 E2 (f a)) /\
    E1 SUBSET E UNION L2 /\ E2 SUBSET E ==>
    fuel_ok Wv (L1 UNION L2) E (comp_bind m f)
Proof
  rpt strip_tac >> simp[fuel_ok_def, comp_bind_def] >> rpt gen_tac >>
  Cases_on `m st` >> rename1 `m st = (a, mid)` >> simp[] >> strip_tac >>
  `cs_extends st mid /\ st.cs_next_var <= mid.cs_next_var /\
   (cs_no_phi st ==> cs_no_phi mid) /\ ?K1. frag_fuel Wv L1 E1 st mid K1` by
    metis_tac[fuel_ok_def] >>
  `cs_extends mid st' /\ mid.cs_next_var <= st'.cs_next_var /\
   (cs_no_phi mid ==> cs_no_phi st') /\ ?K2. frag_fuel Wv L2 E2 mid st' K2` by
    metis_tac[fuel_ok_def] >>
  rpt conj_tac
  >- metis_tac[cs_extends_trans]
  >- decide_tac
  >- metis_tac[] >>
  qexists_tac `K1 + K2` >> metis_tac[frag_fuel_seq]
QED

Theorem fuel_ok_ignore_bind:
  !m f Wv L1 L2 E1 E2 E.
    fuel_ok Wv L1 E1 m /\ fuel_ok Wv L2 E2 f /\
    E1 SUBSET E UNION L2 /\ E2 SUBSET E ==>
    fuel_ok Wv (L1 UNION L2) E (comp_ignore_bind m f)
Proof
  rw[comp_ignore_bind_def] >> irule fuel_ok_bind >> simp[] >> metis_tac[]
QED

(* A fresh variable may be written by the code after it. *)
Theorem fuel_ok_fresh_var:
  !f Wv L E.
    (!x. fuel_ok (x INSERT Wv) L E (f x)) ==>
    fuel_ok Wv L E (comp_bind fresh_var f)
Proof
  rpt strip_tac >> simp[fuel_ok_def, comp_bind_def, fresh_var_def] >>
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `mid = st with cs_next_var := st.cs_next_var + 1` >>
  first_x_assum (qspec_then `STRING #"%" (toString st.cs_next_var)` mp_tac) >>
  simp[fuel_ok_def] >> disch_then drule >> strip_tac >>
  `mid.cs_blocks = st.cs_blocks /\ mid.cs_current_bb = st.cs_current_bb /\
   mid.cs_current_insts = st.cs_current_insts /\
   mid.cs_next_var = st.cs_next_var + 1` by simp[Abbr `mid`] >>
  rpt conj_tac
  >- fs[cs_extends_def]
  >- decide_tac
  >- fs[cs_no_phi_def] >>
  qexists_tac `Kb` >> simp[frag_fuel_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `frag_fuel _ _ _ mid st' Kb`
    (mp_tac o SIMP_RULE std_ss [frag_fuel_def]) >>
  disch_then (qspecl_then [`G`, `N`, `ctx`, `fn`, `s`] mp_tac) >>
  (impl_tac >- fs[at_point_def, fn_has_code_def, emitted_blocks_def]) >>
  strip_tac >> qexists_tac `j` >> simp[] >>
  irule fuel_outcome_weaken >> goal_assum (drule_at Any) >> rw[] >>
  irule vars_kept_fresh >> qexists_tac `st.cs_next_var` >> simp[]
QED

(* Actions that emit no code. *)
Theorem fuel_ok_no_code:
  !m Wv E.
    (!st x st'. m st = (x, st') ==>
       st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
       st'.cs_current_insts = st.cs_current_insts /\
       st.cs_next_var <= st'.cs_next_var) ==>
    fuel_ok Wv {} E m
Proof
  rw[fuel_ok_def] >> first_x_assum drule >> strip_tac >>
  `cs_extends st st'` by (simp[cs_extends_def] >> qexists_tac `[]` >> simp[]) >>
  `cs_no_phi st ==> cs_no_phi st'` by fs[cs_no_phi_def] >>
  simp[] >> qexists_tac `0` >> rw[frag_fuel_def] >> simp[] >>
  irule fuel_outcome_refl >> fs[at_point_def]
QED

Theorem fuel_ok_prims:
  (!Wv E. fuel_ok Wv {} E fresh_id) /\
  (!Wv E sfx. fuel_ok Wv {} E (fresh_label sfx)) /\
  (!Wv E. fuel_ok Wv {} E comp_get)
Proof
  rpt conj_tac >> rpt gen_tac >> irule fuel_ok_no_code >>
  simp[fresh_id_def, fresh_label_def, comp_get_def]
QED

Theorem emit_frag_inst[local]:
  fn_has_code st (st with cs_current_insts := st.cs_current_insts ++ [inst]) fn /\
  at_point st s ==>
  ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
       get_instruction bb s.vs_inst_idx = SOME inst
Proof
  rw[at_point_def] >>
  drule_then (qspec_then `[inst]` mp_tac) fn_has_code_same_block >>
  simp[] >> strip_tac >> qexists_tac `bb` >> simp[] >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[]
QED

(* A non-terminator whose outputs may be written. *)
Theorem fuel_ok_emit:
  !inst Wv E.
    ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> PHI /\
    (!x. MEM x inst.inst_outputs ==> x IN Wv) ==>
    fuel_ok Wv {} E (emit inst)
Proof
  rpt strip_tac >> simp[fuel_ok_def, emit_def] >> rpt gen_tac >> strip_tac >>
  gvs[] >> rpt conj_tac
  >- (simp[cs_extends_def] >> qexists_tac `[]` >> simp[])
  >- fs[cs_no_phi_def] >>
  qexists_tac `0` >> rw[frag_fuel_def] >>
  drule_all emit_frag_inst >> strip_tac >>
  drule_then (qspecl_then [`s`, `bb`, `inst`] mp_tac) run_from_nonterm_stable >>
  simp[] >> strip_tac
  >- (simp[fuel_outcome_def] >> disj1_tac >>
      qexists_tac `s1 with vs_inst_idx := SUC s.vs_inst_idx` >>
      fs[at_point_def, vars_kept_def, lookup_var_def] >> rw[] >>
      first_x_assum irule >> metis_tac[]) >>
  simp[fuel_outcome_def]
QED

Theorem fuel_ok_emit_jmp:
  !inst lbl Wv E.
    inst.inst_opcode = JMP /\ inst.inst_operands = [Label lbl] /\ lbl IN E ==>
    fuel_ok Wv {} E (emit inst)
Proof
  rpt strip_tac >> simp[fuel_ok_def, emit_def] >> rpt gen_tac >> strip_tac >>
  gvs[] >> rpt conj_tac
  >- (simp[cs_extends_def] >> qexists_tac `[]` >> simp[])
  >- fs[cs_no_phi_def] >>
  qexists_tac `1` >> rw[frag_fuel_def] >>
  drule_all emit_frag_inst >> strip_tac >>
  qexists_tac `1` >> simp[] >> irule fuel_outcome_jump >>
  simp[is_terminator_def, step_inst_base_opcode_eqs] >>
  qexists_tac `lbl` >> simp[jump_to_def, vars_kept_def, lookup_var_def]
QED

Theorem fuel_ok_emit_jnz:
  !inst c l1 l2 Wv E.
    inst.inst_opcode = JNZ /\ inst.inst_operands = [c; Label l1; Label l2] /\
    l1 IN E /\ l2 IN E ==>
    fuel_ok Wv {} E (emit inst)
Proof
  rpt strip_tac >> simp[fuel_ok_def, emit_def] >> rpt gen_tac >> strip_tac >>
  gvs[] >> rpt conj_tac
  >- (simp[cs_extends_def] >> qexists_tac `[]` >> simp[])
  >- fs[cs_no_phi_def] >>
  qexists_tac `1` >> rw[frag_fuel_def] >>
  drule_all emit_frag_inst >> strip_tac >>
  qexists_tac `1` >> simp[] >>
  Cases_on `eval_operand c s`
  >- (simp[fuel_outcome_def] >> disj2_tac >> rpt strip_tac >>
      simp[run_from_def, Once exec_block_def, step_inst_non_invoke,
           step_inst_base_opcode_eqs] >>
      simp[Once exec_block_def, step_inst_non_invoke,
           step_inst_base_opcode_eqs]) >>
  irule fuel_outcome_jump >>
  simp[is_terminator_def, step_inst_base_opcode_eqs] >>
  rename1 `eval_operand c s = SOME w` >>
  qexists_tac `if w <> 0w then l1 else l2` >>
  rw[] >> simp[jump_to_def, vars_kept_def, lookup_var_def]
QED

(* A terminator that never continues the run. *)
Theorem fuel_ok_emit_halt:
  !inst Wv E.
    is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
    (!s s'. step_inst_base inst s = OK s' ==> s'.vs_halted) ==>
    fuel_ok Wv {} E (emit inst)
Proof
  rpt strip_tac >> simp[fuel_ok_def, emit_def] >> rpt gen_tac >> strip_tac >>
  gvs[] >> rpt conj_tac
  >- (simp[cs_extends_def] >> qexists_tac `[]` >> simp[])
  >- (rw[cs_no_phi_def] >> CCONTR_TAC >> fs[is_terminator_def]) >>
  qexists_tac `0` >> rw[frag_fuel_def] >>
  drule_all emit_frag_inst >> strip_tac >>
  simp[fuel_outcome_def] >> disj2_tac >> rpt strip_tac >>
  simp[run_from_def, Once exec_block_def, step_inst_non_invoke] >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
  simp[step_inst_non_invoke] >>
  Cases_on `step_inst_base inst s` >> simp[] >> res_tac >> simp[]
QED

Theorem fuel_ok_new_block:
  !lbl Wv E. fuel_ok Wv {lbl} E (new_block lbl)
Proof
  rpt strip_tac >> simp[fuel_ok_def] >> rpt gen_tac >> strip_tac >>
  `cs_extends st st'` by metis_tac[cs_extends_new_block] >>
  gvs[new_block_def] >> rpt conj_tac
  >- fs[cs_no_phi_def] >>
  qexists_tac `0` >> rw[frag_fuel_def]
  >- (qmatch_asmsub_abbrev_tac `fn_has_code st st2 fn` >>
      `new_block lbl st = (st.cs_current_bb, st2)` by
        simp[new_block_def, Abbr `st2`] >>
      drule_all fn_has_code_new_block >> strip_tac >>
      simp[fuel_outcome_def] >> disj2_tac >>
      fs[at_point_def] >>
      simp[run_from_def, Once exec_block_def, get_instruction_def] >>
      simp[Once exec_block_def, get_instruction_def]) >>
  simp[] >> irule fuel_outcome_refl >> simp[at_point_def]
QED

(* ===== Functions ===== *)

(* A function whose body is a fragment with no exits, after whose end the
   run no longer depends on fuel, is fuel_stable. *)
Theorem fuel_stable_of_frag:
  !Wv L st st' Kb G ctx fn.
    frag_fuel Wv L {} st st' Kb /\ no_phi_fn fn /\ fn_has_code st st' fn /\
    callees_stable G ctx fn /\ fn.fn_blocks <> [] /\
    (HD fn.fn_blocks).bb_label = st.cs_current_bb /\ st.cs_current_insts = [] /\
    (!t f. at_point st' t /\ G <= f ==> run_from f ctx fn t = run_from G ctx fn t) ==>
    fuel_stable (G + Kb + 1) ctx fn
Proof
  rpt strip_tac >> simp[fuel_stable_def] >> rpt strip_tac >>
  `!g. run_blocks (SUC g) ctx fn s = run_from g ctx fn s` by
    (gen_tac >> Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
     >- simp[Once run_blocks_def, run_from_def] >>
     rename1 `lookup_block _ _ = SOME bb` >>
     `phi_prefix_length bb.bb_instructions = 0` by
       (drule lookup_block_MEM >> fs[no_phi_fn_def, EVERY_MEM]) >>
     drule_all run_blocks_run_from_no_phi >> simp[] >> disch_then kall_tac >>
     `s with vs_inst_idx := 0 = s` by
       simp[venomStateTheory.venom_state_component_equality] >>
     simp[]) >>
  `?f'. f = SUC f'` by (Cases_on `f` >> fs[]) >>
  `G + (Kb + 1) = SUC (G + Kb)` by decide_tac >>
  gvs[] >>
  qpat_x_assum `frag_fuel _ _ _ _ _ _` (mp_tac o SIMP_RULE std_ss [frag_fuel_def]) >>
  disch_then (qspecl_then [`G`, `0`, `ctx`, `fn`, `s`] mp_tac) >>
  simp[at_point_def] >> strip_tac >>
  `run_blocks (G + (Kb + 1)) ctx fn s = run_from (G + Kb) ctx fn s` by
    (`G + (Kb + 1) = SUC (G + Kb)` by decide_tac >> metis_tac[]) >>
  fs[fuel_outcome_def]
  >- (`at_point st' t` by simp[at_point_def] >>
      `run_from f' ctx fn s = run_from (f' - j) ctx fn t` by
        (`f' - j + j = f' /\ G <= f' - j` by decide_tac >> metis_tac[]) >>
      `run_from (G + Kb) ctx fn s = run_from (G + Kb - j) ctx fn t` by
        (`G + Kb - j + j = G + Kb /\ G <= G + Kb - j` by decide_tac >> metis_tac[]) >>
      `G <= f' - j /\ G <= G + Kb - j` by decide_tac >>
      metis_tac[]) >>
  `run_from f' ctx fn s = run_from (G + j) ctx fn s` by
    (`f' - j + j = f' /\ G <= f' - j` by decide_tac >> metis_tac[]) >>
  `run_from (G + Kb) ctx fn s = run_from (G + j) ctx fn s` by
    (`G + Kb - j + j = G + Kb /\ G <= G + Kb - j` by decide_tac >> metis_tac[]) >>
  simp[]
QED

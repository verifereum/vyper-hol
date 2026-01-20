(*
 * Vyper Program Logic - Core Definitions
 *
 * Defines Hoare triples and separation logic primitives for reasoning
 * about Vyper source programs.
 *
 * TOP-LEVEL:
 *   - vyper_triple: basic Hoare triple {P} ss {Q}
 *   - vyper_spec: general spec with ok/return/exception postconditions
 *   - state_star: separating conjunction for contract storage
 *   - storage_at: assertion about a storage slot
 *
 * Helper:
 *   - Various assertion combinators
 *)

Theory vyperTriples

Ancestors
  vyperInterpreter

(* ===== Basic Hoare Triple ===== *)

(* A triple {P} ss {Q} holds if:
   - Starting from any state satisfying P
   - Executing ss in context cx
   - Either succeeds normally with Q holding on final state
   - Or returns a value with Q holding on final state
   - Exceptions/errors mean the triple doesn't hold *)

Definition vyper_triple_def:
  vyper_triple (P : evaluation_state -> bool) cx ss (Q : evaluation_state -> bool) <=>
    !st. P st ==>
      case eval_stmts cx ss st of
      | (INL (), st') => Q st'
      | (INR (ReturnException v), st') => Q st'
      | _ => F
End

(* ===== General Specification ===== *)

(* More flexible: separate postconditions for different outcomes *)

Definition vyper_spec_def:
  vyper_spec P cx ss Q_ok Q_ret Q_exn <=>
    !st. P st ==>
      case eval_stmts cx ss st of
      | (INL (), st') => Q_ok st'
      | (INR (ReturnException v), st') => Q_ret v st'
      | (INR (AssertException s), st') => Q_exn s st'
      | (INR BreakException, st') => F  (* shouldn't escape *)
      | (INR ContinueException, st') => F
      | (INR (Error s), st') => F
End

(* ===== Triple with Invariant ===== *)

(* For reasoning with contract invariants that must be preserved *)

Definition vyper_triple_inv_def:
  vyper_triple_inv (I : evaluation_state -> bool) P cx ss Q <=>
    !st. I st /\ P st ==>
      case eval_stmts cx ss st of
      | (INL (), st') => I st' /\ Q st'
      | (INR (ReturnException v), st') => I st' /\ Q st'
      | _ => F
End

(* ===== Separating Conjunction ===== *)

(* For multi-contract reasoning: P * Q means P and Q hold on disjoint
   portions of the global storage *)

Definition state_star_def:
  state_star P Q st <=>
    ?g1 g2.
      (* Globals are disjoint by address *)
      DISJOINT (set (MAP FST g1)) (set (MAP FST g2)) /\
      (* Together they form the full globals *)
      st.globals = g1 ++ g2 /\
      (* P holds on state with just g1 *)
      P (st with globals := g1) /\
      (* Q holds on state with just g2 *)
      Q (st with globals := g2)
End

Overload "*" = ``state_star``

(* ===== Storage Assertions ===== *)

(* Points-to assertion for a mutable storage slot (num -> toplevel_value)
   addr: contract address
   src_id: source module id (NONE = main contract)
   slot: variable slot number
   tv: toplevel_value at that slot *)
Definition mutable_at_def:
  mutable_at addr src_id slot tv st <=>
    ?gbs mg.
      ALOOKUP st.globals addr = SOME gbs /\
      ALOOKUP gbs src_id = SOME mg /\
      FLOOKUP mg.mutables slot = SOME tv
End

(* Points-to for a value (not HashMap) *)
Definition storage_at_def:
  storage_at addr src_id slot v st <=>
    ?gbs mg.
      ALOOKUP st.globals addr = SOME gbs /\
      ALOOKUP gbs src_id = SOME mg /\
      FLOOKUP mg.mutables slot = SOME (Value v)
End

(* HashMap assertion *)
Definition hashmap_at_def:
  hashmap_at addr src_id slot vt hm st <=>
    ?gbs mg.
      ALOOKUP st.globals addr = SOME gbs /\
      ALOOKUP gbs src_id = SOME mg /\
      FLOOKUP mg.mutables slot = SOME (HashMap vt hm)
End

(* Immutable assertion *)
Definition immutable_at_def:
  immutable_at addr src_id slot v st <=>
    ?gbs mg.
      ALOOKUP st.globals addr = SOME gbs /\
      ALOOKUP gbs src_id = SOME mg /\
      FLOOKUP mg.immutables slot = SOME v
End

(* ===== Pure Assertions ===== *)

(* Lift a pure proposition to a state predicate *)
Definition pure_def:
  pure p st <=> p
End

(* True/False assertions *)
Definition atrue_def:
  atrue st <=> T
End

Definition afalse_def:
  afalse st <=> F
End

(* ===== Assertion Combinators ===== *)

Definition aand_def:
  aand P Q st <=> P st /\ Q st
End

Definition aor_def:
  aor P Q st <=> P st \/ Q st
End

Definition anot_def:
  anot P st <=> ~(P st)
End

Definition aimp_def:
  aimp P Q st <=> P st ==> Q st
End

Definition aexists_def:
  aexists P st <=> ?x. P x st
End

Definition aforall_def:
  aforall P st <=> !x. P x st
End

(* ===== Basic Properties ===== *)

(* Note: state_star_comm would require a set-based formulation of globals,
   not alist. For now we work with the asymmetric version. *)

(* TODO: Reformulate state_star using FDOM-based disjointness for proper
   commutativity. Current alist formulation is order-dependent. *)

(* Triple consequence rule *)
Theorem vyper_triple_consequence:
  !P P' Q Q' cx ss.
    (!st. P' st ==> P st) /\
    (!st. Q st ==> Q' st) /\
    vyper_triple P cx ss Q ==>
    vyper_triple P' cx ss Q'
Proof
  rw[vyper_triple_def] >> rpt strip_tac >>
  first_x_assum drule >> simp[] >>
  strip_tac >> first_x_assum drule >>
  Cases_on `eval_stmts cx ss st` >> Cases_on `q` >> gvs[] >>
  Cases_on `y` >> gvs[]
QED

(* Empty statement list is a no-op *)
Theorem vyper_triple_nil:
  !P cx. vyper_triple P cx [] P
Proof
  rw[vyper_triple_def] >> simp[Once evaluate_def, return_def]
QED

(* ===== Sequence Rules ===== *)

(* Sequence rule for vyper_spec: if first statement completes normally with R,
   then continue with ss. Returns/exceptions from first statement propagate directly. *)
Theorem vyper_spec_seq:
  !P R Q_ok Q_ret Q_exn cx s ss.
    vyper_spec P cx [s] R Q_ret Q_exn /\
    vyper_spec R cx ss Q_ok Q_ret Q_exn ==>
    vyper_spec P cx (s::ss) Q_ok Q_ret Q_exn
Proof
  rw[vyper_spec_def] >> rpt strip_tac >>
  simp[Once evaluate_def, ignore_bind_def, bind_def] >>
  Cases_on `eval_stmt cx s st` >> Cases_on `q` >> simp[] >-
  (* Normal completion: use both specs *)
  (qpat_x_assum `!st. P st ==> _` (drule_then mp_tac) >>
   simp[Once evaluate_def, ignore_bind_def, bind_def,
        Once evaluate_def, return_def]) >>
  (* Exception: use first spec only *)
  qpat_x_assum `!st. P st ==> _` (drule_then mp_tac) >>
  simp[Once evaluate_def, ignore_bind_def, bind_def]
QED

(* Empty spec *)
Theorem vyper_spec_nil:
  !P Q_ret Q_exn cx. vyper_spec P cx [] P Q_ret Q_exn
Proof
  rw[vyper_spec_def] >> simp[Once evaluate_def, return_def]
QED

(* ===== Statement Rules ===== *)

(* Pass is a no-op *)
Theorem vyper_triple_pass:
  !P cx. vyper_triple P cx [Pass] P
Proof
  rw[vyper_triple_def] >>
  simp[Once evaluate_def, ignore_bind_def, bind_def, return_def, Once evaluate_def] >>
  simp[Once evaluate_def, return_def]
QED

(* Return NONE preserves state (postcondition holds via ReturnException clause) *)
Theorem vyper_triple_return_none:
  !P cx. vyper_triple P cx [Return NONE] P
Proof
  rw[vyper_triple_def] >>
  simp[Once evaluate_def, ignore_bind_def, bind_def, raise_def] >>
  simp[Once evaluate_def, raise_def]
QED

(* Assert with true condition is a no-op.
   Precondition: P implies the condition evaluates to true without changing state. *)
Theorem vyper_spec_assert_true:
  !P Q_ret cx e se.
    (!st. P st ==> eval_expr cx e st = (INL (Value (BoolV T)), st)) ==>
    vyper_spec P cx [Assert e se] P Q_ret (\s st. F)
Proof
  rw[vyper_spec_def] >> rpt strip_tac >>
  simp[Once evaluate_def, ignore_bind_def, bind_def] >>
  simp[Once evaluate_def, bind_def] >>
  simp[switch_BoolV_def, return_def] >>
  simp[Once evaluate_def, return_def]
QED

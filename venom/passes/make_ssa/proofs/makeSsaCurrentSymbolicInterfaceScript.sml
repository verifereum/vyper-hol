(* Proof-interface probe only: no compiler-coherence claim. *)
Theory makeSsaCurrentSymbolicInterface
Ancestors makeSsaCurrentStaticDemandProbe list alist arithmetic

Datatype:
  current_symbol = CurrentInitial string | CurrentConstant operand |
                   CurrentOccurrence num num
End

Definition current_symbol_operand_def:
  current_symbol_operand env op =
    case op of Var v => env v | _ => CurrentConstant op
End

(* The occurrence is a dynamic paired-subst index, not a static instruction id.
   Both sides must use the SAME index only for corresponding original writes. *)
Definition current_symbol_expr_def:
  current_symbol_expr env occurrence expr =
    case expr of
      CurrentStaticRead op => current_symbol_operand env op
    | CurrentStaticProduced k => CurrentOccurrence occurrence k
End

Definition current_symbol_inst_def:
  current_symbol_inst env occurrence inst op =
    current_symbol_expr env occurrence (current_static_inst_subst inst op)
End

Definition current_symbol_phi_def:
  current_symbol_phi env p phis op =
    OPTION_MAP (current_symbol_expr env 0) (current_static_phi_subst p phis op)
End

(* Walk substs are independent simultaneous substitutions. They may visit the
   same static block repeatedly. Missing selectors stay NONE, never defaults. *)
Definition current_symbol_walk_def:
  (current_symbol_walk env n [] = env) /\
  (current_symbol_walk env n (subst::substs) =
    current_symbol_walk
      (\v. case subst (Var v) of
             NONE => NONE
           | SOME e => case e of
               CurrentStaticRead (Var u) => env u
             | _ => SOME (current_symbol_expr (\u. CurrentInitial u) n e))
      (SUC n) substs)
End

Theorem current_symbol_empty_walk:
  current_symbol_walk env n [] = env
Proof
  simp[current_symbol_walk_def]
QED

Theorem current_symbol_read:
  current_symbol_expr env n (CurrentStaticRead op) = current_symbol_operand env op
Proof
  simp[current_symbol_expr_def]
QED

Theorem current_symbol_produced_occurrence:
  (current_symbol_expr env n (CurrentStaticProduced k) =
   current_symbol_expr env' m (CurrentStaticProduced j)) <=> n = m /\ k = j
Proof
  simp[current_symbol_expr_def]
QED

Theorem current_symbol_ordinary_transfer:
  current_static_inst_subst inst op = e ==>
  current_symbol_inst env n inst op = current_symbol_expr env n e
Proof
  simp[current_symbol_inst_def]
QED

Theorem current_symbol_phi_transfer:
  current_static_phi_subst p phis op = SOME (CurrentStaticRead rhs) ==>
  current_symbol_phi env p phis op = SOME (current_symbol_operand env rhs)
Proof
  simp[current_symbol_phi_def, current_symbol_expr_def]
QED

(* Crucially rhs is interpreted using env, NOT the batch's output env.
   This also applies when rhs is itself an output spelling. *)
Theorem current_symbol_phi_selected:
  ALOOKUP (MAP (\j. (HD j.inst_outputs, resolve_phi p j.inst_operands)) phis) v =
    SOME (SOME rhs) ==>
  current_symbol_phi env p phis (Var v) = SOME (current_symbol_operand env rhs)
Proof
  simp[current_symbol_phi_def, current_static_phi_subst_def,
       current_symbol_expr_def]
QED

Theorem current_symbol_walk_read_snapshot:
  subst (Var v) = SOME (CurrentStaticRead (Var u)) ==>
  current_symbol_walk env n [subst] v = env u
Proof
  simp[current_symbol_walk_def]
QED

Theorem current_symbol_walk_write:
  subst (Var v) = SOME (CurrentStaticProduced k) ==>
  current_symbol_walk env n [subst] v = SOME (CurrentOccurrence n k)
Proof
  simp[current_symbol_walk_def, current_symbol_expr_def]
QED

(* A repeated visit to the SAME static write has a new dynamic origin.
   This is universal in the initial environment, instruction and output. *)
Theorem current_symbol_repeated_write:
  subst (Var v) = SOME (CurrentStaticProduced k) ==>
  current_symbol_walk env n [subst;subst] v = SOME (CurrentOccurrence (SUC n) k) /\
  current_symbol_walk env n [subst;subst] v <>
    current_symbol_walk env n [subst] v
Proof
  simp[current_symbol_walk_def, current_symbol_expr_def]
QED

Theorem current_symbol_walk_append:
  !prefix env n suffix.
  current_symbol_walk env n (prefix ++ suffix) =
  current_symbol_walk (current_symbol_walk env n prefix)
    (n + LENGTH prefix) suffix
Proof
  Induct >> simp[current_symbol_walk_def, ADD_CLAUSES]
QED

(* Universal simultaneous-snapshot test, rather than a compiler fixture. *)
Theorem current_symbol_parallel_swap:
  subst (Var x) = SOME (CurrentStaticRead (Var y)) /\
  subst (Var y) = SOME (CurrentStaticRead (Var x)) ==>
  current_symbol_walk env n [subst] x = env y /\
  current_symbol_walk env n [subst] y = env x
Proof
  simp[current_symbol_walk_def]
QED

(* Equality inversion needs freshness relative to the incoming environment.
   Arbitrary symbolic environments can already contain the produced atom. *)
Theorem current_symbol_fresh_read_not_produced:
  (!v k. env v <> CurrentOccurrence n k) ==>
  current_symbol_expr env n (CurrentStaticRead op) <>
    current_symbol_expr env n (CurrentStaticProduced j)
Proof
  Cases_on `op` >> simp[current_symbol_expr_def, current_symbol_operand_def]
QED

Theorem current_symbol_initial_fresh:
  CurrentInitial v <> CurrentOccurrence n k
Proof
  simp[]
QED

(* Checked falsification of equality inversion WITHOUT generation bounds. *)
Theorem current_symbol_unbounded_alias:
  current_symbol_expr (\v. CurrentOccurrence n k) n
    (CurrentStaticRead (Var x)) =
  current_symbol_expr (\v. CurrentOccurrence n k) n
    (CurrentStaticProduced k)
Proof
  simp[current_symbol_expr_def, current_symbol_operand_def]
QED

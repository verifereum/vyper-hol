Theory algebraicOptRelationProofs
Ancestors
  algebraicOptIszeroPreservationProofs algebraicOptLocalProofs
  venomFnScheduleRunner stateFrame venomState
Libs
  finite_mapTheory

(* Original ISZERO outputs stay exact even when their uses are all truthy:
   chain shortening can expose them at later value-sensitive consumers.
   Inputs with no original producer also stay exact. *)
Definition ao_main_exact_def:
  ao_main_exact fn x <=>
    ~(?inst. MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs) \/
    (?inst. MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs /\
       (inst.inst_opcode = ISZERO \/
        ~ao_all_truthy (dfg_build_function fn) inst))
End

(* NONE is not identified with SOME 0w. *)
Definition ao_main_lookup_def:
  ao_main_lookup exact (a:bytes32 option) b <=>
    if exact then a = b
    else (a = NONE /\ b = NONE) \/
         ?u v. a = SOME u /\ b = SOME v /\ (u = 0w <=> v = 0w)
End

(* Lookup observations only. Frame and control must be tracked separately.
   V will be the source function's IR variables, not supply-generated vars. *)
Definition ao_main_observations_def:
  ao_main_observations fn V s t <=>
    !x. x IN V ==>
      ao_main_lookup (ao_main_exact fn x) (lookup_var x s) (lookup_var x t)
End

Theorem ao_main_lookup_refl[simp]:
  ao_main_lookup exact a a
Proof
  Cases_on `exact` >> Cases_on `a` >> simp[ao_main_lookup_def]
QED

Theorem ao_main_lookup_some[simp]:
  ao_main_lookup exact (SOME u) (SOME v) <=>
    if exact then u = v else (u = 0w <=> v = 0w)
Proof
  Cases_on `exact` >> simp[ao_main_lookup_def]
QED

Theorem ao_main_lookup_defined:
  ao_main_lookup exact a b ==> (a = NONE <=> b = NONE)
Proof
  Cases_on `exact` >> Cases_on `a` >> Cases_on `b` >>
  simp[ao_main_lookup_def]
QED

Theorem ao_main_observations_init:
  (!inst x. MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs ==>
     lookup_var x s = NONE) ==>
  ao_main_observations fn V s s
Proof
  simp[ao_main_observations_def]
QED

Theorem ao_main_observations_update:
  ao_main_observations fn V s t /\
  (out IN V ==> ao_main_lookup (ao_main_exact fn out) (SOME u) (SOME v)) ==>
  ao_main_observations fn V (update_var out u s) (update_var out v t)
Proof
  simp[ao_main_observations_def, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE] >>
  rpt strip_tac >> Cases_on `x = out` >> gvs[]
QED

Theorem ao_main_observations_fresh:
  ao_main_observations fn V s t /\ fresh NOTIN V ==>
  ao_main_observations fn V s (update_var fresh w t)
Proof
  simp[ao_main_observations_def, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE] >>
  rpt strip_tac >> `x <> fresh` by metis_tac[] >> simp[]
QED

Theorem ao_main_exact_iszero:
  MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs /\
  inst.inst_opcode = ISZERO ==> ao_main_exact fn x
Proof
  simp[ao_main_exact_def] >> metis_tac[]
QED

Theorem ao_main_observations_iszero:
  ao_main_observations fn V s t /\
  inst.inst_opcode = ISZERO /\ inst.inst_operands = [op] /\
  inst.inst_outputs = [out] /\ eval_operand op s = SOME u /\
  eval_operand op t = SOME v /\ (u = 0w <=> v = 0w) ==>
  ?word.
    step_inst fuel ctx inst s = OK (update_var out word s) /\
    (!inst'. MEM inst' (ao_transform_inst dfg ra lbl idx targets fr inst) ==>
      step_inst fuel ctx inst' t = OK (update_var out word t)) /\
    ao_main_observations fn V (update_var out word s) (update_var out word t)
Proof
  strip_tac >> drule_all ao_transform_iszero_step_exact >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
  qexists_tac `word` >> simp[] >>
  irule ao_main_observations_update >> simp[]
QED

(* Frame preservation for variable writes is already frame_update_var.
   Control correspondence (including unequal indices after insertion), label
   lookup agreement and simultaneous selected-PHI reads are separate premises;
   none follows merely from ao_main_observations. *)

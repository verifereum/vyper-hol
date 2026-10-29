(* ABI projections, unwrap and staging only observe the arena. Capture and
   write are deliberately absent; they have distinct lifetime/frame APIs. *)
Theory vyperAbiReadOnly
Ancestors
  pair list option vyperState vyperAbiOperand vyperAbiFrame
  vyperStatePreservation vyperStorageBackend

Definition abi_readonly_def:
  abi_readonly f <=> !st. SND (f st) = st
End

Theorem abi_readonly_result:
  abi_readonly f <=> !st res rt. f st = (res,rt) ==> rt = st
Proof
  simp[abi_readonly_def] >> eq_tac >> rpt strip_tac
  >- (first_x_assum (qspec_then `st` mp_tac) >> simp[]) >>
  first_x_assum (qspecl_then [`st`,`FST (f st)`,`SND (f st)`] mp_tac) >> simp[]
QED

Theorem abi_readonly_bind:
  abi_readonly f /\ (!v. abi_readonly (g v)) ==> abi_readonly (vyperState$bind f g)
Proof
  simp[abi_readonly_def, bind_def] >> rpt strip_tac >>
  Cases_on `f st` >> Cases_on `q` >> gvs[] >>
  first_x_assum (qspec_then `st` mp_tac) >> simp[] >> strip_tac >> gvs[]
QED

Theorem abi_readonly_leaves[local]:
  abi_readonly (vyperState$return x) /\ abi_readonly (vyperState$raise e) /\
  abi_readonly (λs. vyperState$return (g s) s) /\ abi_readonly (check b msg) /\
  abi_readonly (lift_option opt msg) /\ abi_readonly (lift_option_type opt msg) /\
  abi_readonly (lift_sum rs) /\
  abi_readonly (read_storage_slot cx tr slot tv) /\
  abi_readonly (lookup_global cx src id) /\ abi_readonly (materialise cx top) /\
  abi_readonly (read_abi_operand cx arg) /\
  abi_readonly (check_abi_projection cx arg tv sub)
Proof
  simp[abi_readonly_result] >> rpt strip_tac >>
  TRY (simp[return_def] >> NO_TAC) >>
  FIRST [drule return_state, drule raise_state, drule check_state,
    drule lift_option_state, drule lift_option_type_state, drule lift_sum_state,
    drule read_storage_slot_state, drule lookup_global_state,
    drule materialise_state, drule read_abi_operand_state,
    drule check_abi_projection_state] >> simp[]
QED

local
  val leaves = CONJUNCTS abi_readonly_leaves;
in
  val READONLY_TAC = rpt (FIRST [FIRST (map MATCH_ACCEPT_TAC leaves),
    first_assum MATCH_ACCEPT_TAC,
    MATCH_MP_TAC abi_readonly_bind >> conj_tac,
    CONV_TAC (RAND_CONV BETA_CONV),
    CONV_TAC (RAND_CONV (REWR_CONV ignore_bind_def)),
    CHANGED_TAC (simp_tac (srw_ss()) [LET_THM, pairTheory.UNCURRY]),
    gen_tac,
    CHANGED_TAC (fn (asl,w) => simp_tac (srw_ss())
      (map ASSUME (List.filter (not o is_forall) asl)) (asl,w)),
    BasicProvers.PURE_TOP_CASE_TAC]);
end;

Theorem abi_readonly_primitives:
  abi_readonly (read_abi_operand cx arg) /\
  abi_readonly (unwrap_abi_operand cx arg) /\
  abi_readonly (stage_abi_operands cx args) /\
  abi_readonly (check_abi_projection cx arg tv sub) /\
  abi_readonly (project_abi_operand cx arg sub) /\
  abi_readonly (subscript_abi_operand cx tv arg index) /\
  abi_readonly (attribute_abi_operand cx arg id) /\
  abi_readonly (project_abi_path cx arg subs) /\
  abi_readonly (abi_pop_pointer cx arg)
Proof
  `!cx arg. abi_readonly (unwrap_abi_operand cx arg)` by
    (rpt gen_tac >> Cases_on `arg` >>
     simp_tac bool_ss [unwrap_abi_operand_def] >> READONLY_TAC) >>
  `!args cx. abi_readonly (stage_abi_operands cx args)` by
    (Induct >> gen_tac >> simp_tac bool_ss [stage_abi_operands_def] >> READONLY_TAC) >>
  `!cx arg sub. abi_readonly (project_abi_operand cx arg sub)` by
    (rpt gen_tac >> simp_tac bool_ss [oneline project_abi_operand_def] >> READONLY_TAC) >>
  `!cx tv arg index. abi_readonly (subscript_abi_operand cx tv arg index)` by
    (rpt gen_tac >> Cases_on `arg` >>
     simp_tac bool_ss [subscript_abi_operand_def] >> READONLY_TAC) >>
  `!cx arg id. abi_readonly (attribute_abi_operand cx arg id)` by
    (rpt gen_tac >> Cases_on `arg` >>
     simp_tac bool_ss [attribute_abi_operand_def] >> READONLY_TAC) >>
  `!subs cx arg. abi_readonly (project_abi_path cx arg subs)` by
    (Induct >> rpt gen_tac >> simp_tac bool_ss [project_abi_path_def] >> READONLY_TAC) >>
  `!cx arg. abi_readonly (abi_pop_pointer cx arg)` by
    (rpt gen_tac >> simp_tac bool_ss [abi_pop_pointer_def] >> READONLY_TAC) >>
  simp[] >> rpt conj_tac >> READONLY_TAC
QED

Theorem abi_readonly_states:
  (read_abi_operand cx arg st = (res,rt) ==> rt = st) /\
  (unwrap_abi_operand cx arg st = (res',rt) ==> rt = st) /\
  (stage_abi_operands cx args st = (res'',rt) ==> rt = st) /\
  (check_abi_projection cx arg tv sub st = (res''',rt) ==> rt = st) /\
  (project_abi_operand cx arg sub st = (res',rt) ==> rt = st) /\
  (subscript_abi_operand cx tv arg index st = (res',rt) ==> rt = st) /\
  (attribute_abi_operand cx arg id st = (res',rt) ==> rt = st) /\
  (project_abi_path cx arg subs st = (res',rt) ==> rt = st) /\
  (abi_pop_pointer cx arg st = (res',rt) ==> rt = st)
Proof
  metis_tac[abi_readonly_primitives, abi_readonly_result]
QED

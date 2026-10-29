(* ABI primitives may change either backing arena, but no other state field.
   The relation parameter exposes this fact to scopes, outcomes and log frames. *)
Theory vyperAbiFrame
Ancestors
  list pair option vyperState vyperStorageBackend
  vyperAbiOperand vyperAbiMemoryProps vyperStatePreservation
  vyperCallOutcomeFrame

Theorem state_rel_frame_pure:
  (!s. R s s) /\ (!s r t. f s = (r,t) ==> t = s) ==>
  state_rel_frame R f
Proof
  simp[state_rel_frame_result] >> metis_tac[]
QED

Theorem state_rel_frame_finally:
  (!s t u. R s t /\ R t u ==> R s u) /\
  state_rel_frame R f /\ state_rel_frame R g ==>
  state_rel_frame R (finally f g)
Proof
  simp[state_rel_frame_def, finally_def] >> rpt strip_tac >>
  Cases_on `f st` >> Cases_on `g r` >> Cases_on `q'` >> gvs[] >>
  qpat_x_assum `!st. R st (SND (f st))` (qspec_then `st` mp_tac) >>
  qpat_x_assum `!st. R st (SND (g st))` (qspec_then `r` mp_tac) >>
  Cases_on `q` >> simp[ignore_bind_def, bind_def, return_def, raise_def] >>
  metis_tac[]
QED

Theorem abi_memory_update[local]:
  st with abi_memory updated_by f = st with abi_memory := f st.abi_memory
Proof
  simp[evaluation_state_component_equality]
QED

Theorem abi_immutables_update[local]:
  st with abi_immutables updated_by f = st with abi_immutables := f st.abi_immutables
Proof
  simp[evaluation_state_component_equality]
QED

Theorem abi_frame_leaves[local]:
  (!s mem. R s (s with abi_memory := mem)) /\
  (!s mem. R s (s with abi_immutables := mem)) ==>
  state_rel_frame R (vyperState$return x) /\ state_rel_frame R (vyperState$raise e) /\
  state_rel_frame R (lift_option opt msg) /\
  state_rel_frame R (lift_option_type opt msg) /\
  state_rel_frame R (lift_sum rs) /\
  state_rel_frame R (check b msg) /\
  state_rel_frame R get_scopes /\
  state_rel_frame R (read_storage_slot cx tr slot tv) /\
  state_rel_frame R (get_storage_backend cx tr) /\
  state_rel_frame R (lookup_global cx src id) /\
  state_rel_frame R (get_immutables cx src) /\
  state_rel_frame R (materialise cx top) /\
  state_rel_frame R (capture_abi_memory cx id tv v) /\
  state_rel_frame R (capture_abi_immutable cx src id tv v) /\
  state_rel_frame R (write_abi_memory cx id tv v subs ao) /\
  state_rel_frame R (write_abi_immutables cx src id tv v subs ao) /\
  state_rel_frame R mark_abi_memory /\
  state_rel_frame R mark_abi_captures /\
  state_rel_frame R (release_abi_memory mark) /\
  state_rel_frame R (λs. vyperState$return (g s) s)
Proof
  strip_tac >>
  `!s. R s s` by
    (gen_tac >> qpat_x_assum `!s mem. R s (s with abi_memory := mem)`
      (qspecl_then [`s`,`s.abi_memory`] mp_tac) >> simp[]) >>
  rpt conj_tac >>
  TRY (irule state_rel_frame_pure >> simp[] >> rpt strip_tac >>
    FIRST [drule return_state, drule raise_state, drule lift_option_state,
      drule lift_option_type_state, drule lift_sum_state, drule check_state,
      drule read_storage_slot_state, drule get_storage_backend_state,
      drule lookup_global_state, drule get_immutables_state, drule materialise_state] >> simp[] >> NO_TAC) >>
  simp[state_rel_frame_def, get_scopes_def, return_def,
    capture_abi_memory_def, capture_abi_immutable_def, write_abi_memory_def,
    write_abi_immutables_def, mark_abi_memory_def, mark_abi_captures_def,
    release_abi_memory_def] >>
  rpt gen_tac >> rpt (CASE_TAC >> simp[return_def, raise_def]) >>
  once_rewrite_tac [abi_memory_update, abi_immutables_update] >>
  first_assum MATCH_ACCEPT_TAC
QED

local
  val mem = ASSUME ``!s mem. R s (s with abi_memory := mem)``;
  val imms = ASSUME ``!s mem. R s (s with abi_immutables := mem)``;
  val leaves = CONJUNCTS (MATCH_MP abi_frame_leaves (CONJ mem imms));
  val net = List.foldl (fn (th,n) => Net.insert
    (concl th, MATCH_ACCEPT_TAC th) n) Net.empty leaves;
in
  val ABI_FRAME_STEP = FIRST [
    FIRST (map MATCH_ACCEPT_TAC leaves),
    first_assum MATCH_ACCEPT_TAC,
    MATCH_MP_TAC state_rel_frame_bind_guarded >> conj_tac >-
      first_assum MATCH_ACCEPT_TAC >> conj_tac,
    CONV_TAC (RAND_CONV BETA_CONV),
    CONV_TAC (RAND_CONV (REWR_CONV ignore_bind_def)),
    CHANGED_TAC (simp_tac (srw_ss()) [LET_THM, pairTheory.UNCURRY, pairTheory.pair_case_thm]),
    gen_tac, strip_tac,
    CHANGED_TAC (fn (asl,w) => simp_tac (srw_ss())
      (map ASSUME (List.filter (not o is_forall) asl)) (asl,w)),
    BasicProvers.PURE_TOP_CASE_TAC];
  val ABI_FRAME_TAC = rpt ABI_FRAME_STEP;
end;

Theorem read_abi_operand_state:
  read_abi_operand cx arg st = (res,rt) ==> rt = st
Proof
  Cases_on `arg` >>
  simp[read_abi_operand_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  FIRST [drule_all read_storage_slot_state, drule_all lift_option_state] >> simp[]
QED

Theorem check_abi_projection_state:
  check_abi_projection cx arg tv sub st = (res,rt) ==> rt = st
Proof
  Cases_on `tv` >> Cases_on `sub` >>
  TRY (rename1 `ValueSubscript index` >> Cases_on `index`) >>
  TRY (rename1 `ArrayTV elem bound` >> Cases_on `bound`) >>
  simp[check_abi_projection_def, return_def, check_def, assert_def] >>
  Cases_on `arg` >>
  simp[ignore_bind_def, bind_def, check_def, assert_def, return_def, raise_def,
       AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  imp_res_tac get_storage_backend_state >> gvs[]
QED

Theorem state_rel_frame_abi_primitives:
  (!s t u. R s t /\ R t u ==> R s u) /\
  (!s mem. R s (s with abi_memory := mem)) /\
  (!s mem. R s (s with abi_immutables := mem)) ==>
  state_rel_frame R (read_abi_operand cx arg) /\
  state_rel_frame R (unwrap_abi_operand cx arg) /\
  state_rel_frame R (stage_abi_operands cx args) /\
  state_rel_frame R (lookup_abi_local cx id) /\
  state_rel_frame R (lookup_abi_immutable cx src id) /\
  state_rel_frame R (lookup_abi_global cx src id) /\
  state_rel_frame R (check_abi_projection cx arg tv sub) /\
  state_rel_frame R (project_abi_operand cx arg sub) /\
  state_rel_frame R (subscript_abi_operand cx tv arg index) /\
  state_rel_frame R (attribute_abi_operand cx arg id) /\
  state_rel_frame R (project_abi_path cx arg subs) /\
  state_rel_frame R (abi_target_operand cx loc subs) /\
  state_rel_frame R (abi_pop_pointer cx arg) /\
  state_rel_frame R (capture_abi_memory cx id tv v) /\
  state_rel_frame R (capture_abi_immutable cx src id tv v) /\
  state_rel_frame R (write_abi_memory cx id tv v subs ao) /\
  state_rel_frame R (write_abi_immutables cx src id tv v subs ao) /\
  state_rel_frame R mark_abi_memory /\
  state_rel_frame R (release_abi_memory mark) /\
  state_rel_frame R mark_abi_captures /\
  state_rel_frame R (release_abi_captures marks)
Proof
  strip_tac >>
  `!s. R s s` by
    (gen_tac >> qpat_x_assum `!s mem. R s (s with abi_memory := mem)`
      (qspecl_then [`s`,`s.abi_memory`] mp_tac) >> simp[]) >>
  `!cx arg. state_rel_frame R (read_abi_operand cx arg)` by
    (rpt gen_tac >> irule state_rel_frame_pure >>
     simp[] >> metis_tac[read_abi_operand_state]) >>
  `!cx arg. state_rel_frame R (unwrap_abi_operand cx arg)` by
    (rpt gen_tac >> Cases_on `arg` >>
     simp_tac bool_ss [unwrap_abi_operand_def] >> ABI_FRAME_TAC) >>
  `!args cx. state_rel_frame R (stage_abi_operands cx args)` by
    (Induct >> gen_tac >> simp_tac bool_ss [stage_abi_operands_def] >> ABI_FRAME_TAC) >>
  `!cx id. state_rel_frame R (lookup_abi_local cx id)` by
    (rpt gen_tac >> simp_tac bool_ss [lookup_abi_local_def] >> ABI_FRAME_TAC) >>
  `!cx src id. state_rel_frame R (lookup_abi_immutable cx src id)` by
    (rpt gen_tac >> simp_tac bool_ss [lookup_abi_immutable_def] >> ABI_FRAME_TAC) >>
  `!cx src id. state_rel_frame R (lookup_abi_global cx src id)` by
    (rpt gen_tac >> simp_tac bool_ss [lookup_abi_global_def] >>
     ntac 8 (TRY ABI_FRAME_STEP) >> ntac 8 (TRY ABI_FRAME_STEP) >> ABI_FRAME_TAC) >>
  `!cx arg tv sub. state_rel_frame R (check_abi_projection cx arg tv sub)` by
    (rpt gen_tac >> irule state_rel_frame_pure >>
     simp[] >> metis_tac[check_abi_projection_state]) >>
  `!cx arg sub. state_rel_frame R (project_abi_operand cx arg sub)` by
    (rpt gen_tac >> simp_tac bool_ss [oneline project_abi_operand_def] >> ABI_FRAME_TAC) >>
  `!cx tv arg index. state_rel_frame R (subscript_abi_operand cx tv arg index)` by
    (rpt gen_tac >> Cases_on `arg` >>
     simp_tac bool_ss [subscript_abi_operand_def] >> ABI_FRAME_TAC) >>
  `!cx arg id. state_rel_frame R (attribute_abi_operand cx arg id)` by
    (rpt gen_tac >> Cases_on `arg` >>
     simp_tac bool_ss [attribute_abi_operand_def] >> ABI_FRAME_TAC) >>
  `!subs cx arg. state_rel_frame R (project_abi_path cx arg subs)` by
    (Induct >> rpt gen_tac >> simp_tac bool_ss [project_abi_path_def] >> ABI_FRAME_TAC) >>
  `!cx loc subs. state_rel_frame R (abi_target_operand cx loc subs)` by
    (rpt gen_tac >> Cases_on `loc` >> Cases_on `subs` >>
     simp_tac bool_ss [abi_target_operand_def] >> ABI_FRAME_TAC) >>
  `!cx arg. state_rel_frame R (abi_pop_pointer cx arg)` by
    (rpt gen_tac >> simp_tac bool_ss [abi_pop_pointer_def] >> ABI_FRAME_TAC) >>
  `!marks. state_rel_frame R (release_abi_captures marks)` by
    (simp[state_rel_frame_def, release_abi_captures_def, return_def] >>
     rpt gen_tac >>
     qpat_x_assum `!s t u. _` irule >>
     qexists_tac `st with abi_memory := TAKE (FST marks) st.abi_memory` >>
     conj_tac >- first_assum MATCH_ACCEPT_TAC >>
     qpat_x_assum `!s mem. R s (s with abi_immutables := mem)`
       (qspecl_then [`st with abi_memory := TAKE (FST marks) st.abi_memory`,
         `TAKE (SND marks) st.abi_immutables`] mp_tac) >> simp[]) >>
  simp[] >> rpt conj_tac >> ABI_FRAME_TAC
QED

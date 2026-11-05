Theory makeSsaCurrentCleanupOrigins
Ancestors
  makeSsaCurrentCleanupRuntime makeSsaCurrentPhiOrigins
  makeSsaCurrentJointRuntime venomInst venomExecSemantics venomState
  stateFrame list alist option

Definition current_cleanup_origin_step_def:
  current_cleanup_origin_step
    (V : (num # string # num # num) -> bytes32 option) inst M =
    if inst.inst_opcode = NOP then SOME M
    else if inst.inst_opcode = ASSIGN then
      case (inst.inst_operands, inst.inst_outputs) of
        ([Var src], [dst]) =>
          (case ALOOKUP M src of
             NONE => NONE
           | SOME origin => if IS_SOME (V origin) then SOME ((dst,origin)::M) else NONE)
      | _ => NONE
    else NONE
End

Definition current_cleanup_origins_def:
  current_cleanup_origins V [] M = SOME M /\
  current_cleanup_origins V (inst::rest) M =
    case current_cleanup_origin_step V inst M of
      NONE => NONE
    | SOME next => current_cleanup_origins V rest next
End

Theorem current_cleanup_origin_step_correspondence:
  current_cleanup_shape inst /\ current_origin_realizes V M st ==>
  case current_cleanup_origin_step V inst M of
    NONE => step_inst_base inst st = Error "undefined operand"
  | SOME N => ?ready. step_inst_base inst st = OK ready /\
      current_origin_realizes V N ready /\
      ready.vs_current_bb = st.vs_current_bb /\ ready.vs_prev_bb = st.vs_prev_bb
Proof
  simp[current_cleanup_shape_def] >> rpt strip_tac
  >- simp[current_cleanup_origin_step_def, current_cleanup_nop_step] >>
  drule_all current_cleanup_assign_step >>
  disch_then (qspec_then `st` assume_tac) >>
  `lookup_var src st = case ALOOKUP M src of NONE => NONE | SOME origin => V origin`
    by fs[current_origin_realizes_def] >>
  Cases_on `ALOOKUP M src` >> simp[current_cleanup_origin_step_def] >>
  Cases_on `V x` >> simp[] >>
  conj_tac >- (irule current_origin_realizes_write >> simp[]) >>
  simp[update_var_def]
QED

Theorem current_cleanup_origins_correspondence:
  !copies M st.
  EVERY current_cleanup_shape copies /\ current_origin_realizes V M st ==>
  case current_cleanup_origins V copies M of
    NONE => current_copies_run copies st = Error "undefined operand"
  | SOME N => ?ready. current_copies_run copies st = OK ready /\
      current_origin_realizes V N ready /\
      ready.vs_current_bb = st.vs_current_bb /\ ready.vs_prev_bb = st.vs_prev_bb
Proof
  Induct >- simp[current_cleanup_origins_def, current_copies_run_def] >>
  rpt gen_tac >> strip_tac >> fs[EVERY_DEF] >>
  drule_all current_cleanup_origin_step_correspondence >>
  Cases_on `current_cleanup_origin_step V h M` >> simp[]
  >- (strip_tac >> simp[current_cleanup_origins_def, current_copies_run_def]) >>
  strip_tac >>
  first_x_assum (drule_at Any) >>
  Cases_on `current_cleanup_origins V copies x` >>
  simp[current_cleanup_origins_def, current_copies_run_def] >> metis_tac[]
QED

Theorem current_cleanup_origins_success:
  EVERY current_cleanup_shape copies /\ current_origin_realizes V M st /\
  current_cleanup_origins V copies M = SOME N ==>
  ?ready. current_copies_run copies st = OK ready /\
    current_origin_realizes V N ready /\
    execution_frame ready = execution_frame st /\
    ready.vs_current_bb = st.vs_current_bb /\ ready.vs_prev_bb = st.vs_prev_bb
Proof
  strip_tac >> drule_all current_cleanup_origins_correspondence >>
  simp[] >> strip_tac >> qexists `ready` >>
  drule_all current_copies_run_frame >> simp[]
QED

Theorem current_cleanup_origins_reflect:
  EVERY current_cleanup_shape copies /\ current_origin_realizes V M st /\
  current_copies_run copies st = OK ready ==>
  ?N. current_cleanup_origins V copies M = SOME N /\
    current_origin_realizes V N ready
Proof
  strip_tac >> drule_all current_cleanup_origins_correspondence >>
  Cases_on `current_cleanup_origins V copies M` >> simp[] >>
  strip_tac >> gvs[]
QED

Theorem current_cleanup_origins_failure:
  EVERY current_cleanup_shape copies /\ current_origin_realizes V M st ==>
  (current_cleanup_origins V copies M = NONE <=>
    current_copies_run copies st = Error "undefined operand")
Proof
  strip_tac >> drule_all current_cleanup_origins_correspondence >>
  Cases_on `current_cleanup_origins V copies M` >> simp[] >>
  strip_tac >> simp[]
QED

(* Chained reads see earlier copies, unlike the parallel PHI boundary. *)
Theorem current_cleanup_origins_chain_regression:
  IS_SOME (V origin) ==>
  current_cleanup_origins V
    [mk_inst 0 ASSIGN [Var "a"] ["x"];
     mk_inst 1 ASSIGN [Var "x"] ["y"]] [("a",origin)] =
    SOME [("y",origin); ("x",origin); ("a",origin)]
Proof
  simp[current_cleanup_origins_def, current_cleanup_origin_step_def, mk_inst_def]
QED

Theorem current_cleanup_origins_repeat_regression:
  IS_SOME (V first) /\ IS_SOME (V second) ==>
  current_cleanup_origins V
    [mk_inst 0 ASSIGN [Var "a"] ["x"];
     mk_inst 1 ASSIGN [Var "b"] ["x"]] [("a",first); ("b",second)] =
    SOME [("x",second); ("x",first); ("a",first); ("b",second)] /\
  ALOOKUP [("x",second); ("x",first); ("a",first); ("b",second)] "x" = SOME second
Proof
  simp[current_cleanup_origins_def, current_cleanup_origin_step_def, mk_inst_def]
QED

Theorem current_cleanup_origins_unvalued_regression:
  V origin = NONE ==>
  current_cleanup_origins V [mk_inst 0 ASSIGN [Var "a"] ["x"]]
    [("a",origin)] = NONE
Proof
  simp[current_cleanup_origins_def, current_cleanup_origin_step_def, mk_inst_def]
QED

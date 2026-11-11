Theory lowerDloadPtrJointReachable
Ancestors o1PassContract lowerDloadPtrPhase lowerDloadPtrJointEntry lowerDloadPtrJointBlock
  lowerDloadPtrJointCall lowerDloadPtrJointReturn lowerDloadPtrJointDispatch
  lowerDloadPtrRawReachable lowerDloadPtrStatic ptrDiscipline irSupply venomInst passSharedDefs list rich_list pred_set finite_map

(* ML-only abbreviation: the JointDispatch invariant with its guard true. *)
val normal = ``\ds PH H un g j t.
  ?cs PG G tn f i s q emitted n pfuel t0 H0 un0 fs.
    frame_reachable vs C cs PG G tn f i s /\
    dload_boundary_core lo fs
      (set (fn_ir_vars f) DIFF {v | retpc_var f v})
      (MAP (\c. set (fn_ir_vars c.cf_fn) DIFF {v | retpc_var c.cf_fn v}) cs)
      PG PH G H0 tn un0 s t0 cs ds /\
    dload_control_match q f g s t0 i emitted 0 /\
    dload_prefix_match pfuel C' PH emitted n t0 H0 un0 t H un /\
    dload_control_match q f g s t i emitted n /\ j = EL n emitted /\
    (!v. v IN set (fn_ir_vars f) ==>
      (lookup_var v s = NONE <=> lookup_var v t0 = NONE)) /\
    FDOM G SUBSET fn_pv P f /\
    (!k b sz. k < LENGTH PG /\ EL k PG = SOME (b,sz) ==> k IN P f.fn_name) /\
    (!c. MEM c cs ==> FDOM c.cf_prov SUBSET fn_pv P c.cf_fn) /\
    (!c k b sz. MEM c cs /\ k < LENGTH c.cf_params /\
      EL k c.cf_params = SOME (b,sz) ==> k IN P c.cf_fn.fn_name) /\
    LENGTH fs = SUC (LENGTH cs) /\ LENGTH cs = LENGTH ds /\
    (!k. k < LENGTH fs ==>
      (EL k fs).dr_scratch =
        FDOM (EL k (t0::MAP (\d. d.cf_state) ds)).vs_allocas DIFF
        {id | ?ci. MEM ci (fn_insts (EL k (f::MAP (\c. c.cf_fn) cs))) /\
                   ci.inst_id = id}) /\
    ir_supply_covers_fn q f /\
    (?q'. lower_dload_function_supply q f = (g,q')) /\
    (!k. k < LENGTH cs ==>
      let c = EL k cs; d = EL k ds in
      dload_live_layout lo c.cf_state.vs_alloca_next d.cf_state.vs_alloca_next
        (DROP (SUC k) fs) /\
      dload_equal_environment c.cf_state d.cf_state /\
      c.cf_state.vs_call_ctx.cc_address = s.vs_call_ctx.cc_address /\
      c.cf_inst = d.cf_inst /\
      (!a. a IN set (fn_ir_vars c.cf_fn) ==>
        (lookup_var a c.cf_state = NONE <=> lookup_var a d.cf_state = NONE)) /\
      (?qc. ir_supply_covers_fn qc c.cf_fn /\
        (?qc'. lower_dload_function_supply qc c.cf_fn = (d.cf_fn,qc')) /\
        dload_control_match qc c.cf_fn d.cf_fn c.cf_state d.cf_state
          c.cf_inst [c.cf_inst] 0))``;

val joint = ``\ds PH H un g j t.
  (^normal) ds PH H un g j t \/ dload_terminal_mode lo P vs C ds H un g j t``;

Theorem dload_joint_reachable_if_next:
  !vs C' ds PH H un g j t.
  frame_reachable vs C' ds PH H un g j t ==>
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
  dead_wf D /\ o1_ctx_shape C /\ o1_run_state_ok vs /\
  o1_src_inv D C vs /\ callee_first names C.ctx_functions /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  (!ds PH H un g j t next t1 fuel.
    frame_reachable vs C' ds PH H un g j t /\
    (^joint) ds PH H un g j t /\
    active_inst g j t /\ ~is_terminator j.inst_opcode /\ j.inst_opcode <> INVOKE /\
    step_inst fuel C' j t = OK t1 /\
    active_inst g next (t1 with vs_inst_idx := SUC t.vs_inst_idx) ==>
    (^joint) ds PH (step_prov PH H j t1) (step_taint j t t1 un) g next
      (t1 with vs_inst_idx := SUC t.vs_inst_idx)) ==>
  (^joint) ds PH H un g j t
Proof
  ho_match_mp_tac frame_reachable_strongind >> rpt conj_tac
  >- suspend "entry"
  >- suspend "next"
  >- suspend "block"
  >- suspend "call"
  >> suspend "return"
QED

Resume dload_joint_reachable_if_next[entry]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  qpat_x_assum `!ds PH H un g j t next t1 fuel. _` kall_tac >>
  CONV_TAC (REDEPTH_CONV BETA_CONV) >> disj1_tac >>
  drule_all dload_joint_entry >> simp[]
QED

Resume dload_joint_reachable_if_next[next]:
  rpt gen_tac >> qabbrev_tac `J = ^joint` >>
  strip_tac >> strip_tac >>
  qpat_x_assum `_ ==> _` (drule_all_then assume_tac) >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Resume dload_joint_reachable_if_next[block]:
  rpt gen_tac >> qabbrev_tac `J = ^joint` >>
  strip_tac >> strip_tac >>
  qpat_x_assum `_ ==> _` (drule_all_then assume_tac) >>
  qpat_x_assum `!ds PH H un g j t next t1 fuel. _` kall_tac >>
  unabbrev_all_tac >> CONV_TAC (REDEPTH_CONV BETA_CONV) >>
  rule_assum_tac (CONV_RULE (REDEPTH_CONV BETA_CONV)) >>
  drule_at (Pat `step_inst _ _ _ _ = _`) dload_joint_block_closed >>
  disch_then drule_all >> simp[]
QED

Resume dload_joint_reachable_if_next[call]:
  rpt gen_tac >> qabbrev_tac `J = ^joint` >>
  strip_tac >> strip_tac >>
  qpat_x_assum `_ ==> _` (drule_all_then assume_tac) >>
  qpat_x_assum `!ds PH H un g j t next t1 fuel. _` kall_tac >>
  unabbrev_all_tac >> CONV_TAC (REDEPTH_CONV BETA_CONV) >>
  rule_assum_tac (CONV_RULE (REDEPTH_CONV BETA_CONV)) >>
  drule_at (Pat `decode_invoke _ = _`) dload_joint_call_closed >>
  disch_then drule_all >> simp[]
QED

Resume dload_joint_reachable_if_next[return]:
  rpt gen_tac >> qabbrev_tac `J = ^joint` >>
  strip_tac >> strip_tac >>
  qpat_x_assum `_ ==> _` (drule_all_then assume_tac) >>
  qpat_x_assum `!ds PH H un g j t next t1 fuel. _` kall_tac >>
  unabbrev_all_tac >> CONV_TAC (REDEPTH_CONV BETA_CONV) >>
  rule_assum_tac (CONV_RULE (REDEPTH_CONV BETA_CONV)) >>
  drule_at (Pat `step_inst _ _ _ _ = _`) dload_joint_return_closed >>
  disch_then drule_all >> simp[]
QED

Finalise dload_joint_reachable_if_next

val _ = if null (hyp dload_joint_reachable_if_next) then ()
  else raise Fail "joint reachable if next: nonempty hypotheses";

Theorem dload_target_reachable_labels:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
  o1_ctx_shape C /\ frame_reachable vs C' ds PH H un g j t ==>
  ALL_DISTINCT (fn_labels g)
Proof
  strip_tac >> drule_all lower_dload_stage_labels_distinct >>
  drule frame_reachable_functions_member >> simp[EVERY_MEM] >> metis_tac[]
QED

Theorem dload_joint_reachable:
  !vs C' ds PH H un g j t.
  frame_reachable vs C' ds PH H un g j t ==>
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
  dead_wf D /\ o1_ctx_shape C /\ o1_run_state_ok vs /\
  o1_src_inv D C vs /\ callee_first names C.ctx_functions /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY (fn_ptr_ok P) C.ctx_functions ==>
  (^joint) ds PH H un g j t
Proof
  rpt gen_tac >> strip_tac >> strip_tac >>
  drule dload_joint_reachable_if_next >>
  disch_then irule >>
  reverse conj_tac >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  `ALL_DISTINCT (fn_labels g')` by (irule dload_target_reachable_labels >> metis_tac[]) >>
  CONV_TAC (REDEPTH_CONV BETA_CONV) >>
  irule (SRULE [] dload_joint_next) >>
  simp[] >>
  conj_tac >- (qexists_tac `fuel` >> simp[]) >>
  qpat_x_assum `(\ds PH H un g j t. _) _ _ _ _ _ _ _` mp_tac >>
  CONV_TAC (REDEPTH_CONV BETA_CONV) >> simp[] >>
  disch_then kall_tac >> metis_tac[]
QED

val _ = List.app (fn th => if null (hyp th) then ()
  else raise Fail "unconditional joint reachability: nonempty hypotheses")
  [frame_reachable_functions_member, lower_dload_stage_labels_distinct,
   dload_target_reachable_labels, dload_joint_reachable];

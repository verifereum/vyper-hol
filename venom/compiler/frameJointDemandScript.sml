Theory frameJointDemand
Ancestors
  frameJointTrace frameJointTransition frameOriginHistory finiteByteDemand
  ptrDiscipline venomExecSemantics contextCodegenRel list pred_set arithmetic

(* Expanded operational footprints, not a memory-preservation theorem.
   Calls enter with no atomic whole-callee write: nested edges account for it.
   Allocation initialization and external effects need separate treatment. *)
Definition joint_reads_def:
  joint_reads (JointConfig stk PG G tn fn inst s oms om hs h) =
    range_bytes (source_memory_read_ranges inst s)
End

Definition joint_writes_def:
  joint_writes (JointConfig stk PG G tn fn inst s oms om hs h) ev =
    case ev of
      SOME (OriginOrdinary fuel post) => range_bytes (step_writes inst s post)
    | SOME (OriginBlock fuel post) => range_bytes (step_writes inst s post)
    | SOME (OriginResume fuel callee rinst rs ret send post) =>
        range_bytes (step_writes rinst rs send)
    | _ => {}
End

Theorem joint_writes_ordinary:
  joint_writes (JointConfig stk PG G tn fn inst s oms om hs h)
    (SOME (OriginOrdinary fuel post)) = range_bytes (step_writes inst s post)
Proof
  simp[joint_writes_def]
QED

Theorem joint_writes_block:
  joint_writes (JointConfig stk PG G tn fn inst s oms om hs h)
    (SOME (OriginBlock fuel post)) = range_bytes (step_writes inst s post)
Proof
  simp[joint_writes_def]
QED

Theorem joint_writes_call:
  joint_writes q NONE = {}
Proof
  Cases_on `q` >> simp[joint_writes_def]
QED

Theorem joint_transition_call_reads:
  joint_transition ctx q NONE q' ==> joint_reads q = {}
Proof
  Cases_on `q` >> simp[joint_transition_call_iff] >> rpt strip_tac >>
  simp[joint_reads_def, source_memory_read_ranges_def, range_bytes_def]
QED

Theorem joint_transition_resume_footprints:
  joint_transition ctx q (SOME (OriginResume fuel fn rinst s ret send post)) q' ==>
  joint_reads q = range_bytes (source_memory_read_ranges rinst s) /\
  joint_writes q (SOME (OriginResume fuel fn rinst s ret send post)) =
    range_bytes (step_writes rinst s send)
Proof
  simp[joint_transition_return] >> rpt strip_tac >>
  gvs[joint_reads_def, joint_writes_def]
QED

(* The last configuration contributes its reads only. The finite-demand
   definition never inspects the write at the horizon itself. *)
Definition joint_byte_demand_def:
  joint_byte_demand q0 es qs n N byte <=>
    finite_byte_demand (\i. joint_reads (EL i (q0::qs)))
      (\i. joint_writes (EL i (q0::qs)) (EL i es)) n N byte
End

Theorem joint_byte_demand_endpoint:
  joint_trace vs0 ctx q0 es qs q /\ N <= LENGTH es ==>
  (joint_byte_demand q0 es qs N N byte <=> byte IN joint_reads (EL N (q0::qs)))
Proof
  simp[joint_byte_demand_def, finite_byte_demand_endpoint]
QED

Theorem joint_byte_demand_unfold:
  joint_trace vs0 ctx q0 es qs q /\ n < N /\ N <= LENGTH es ==>
  (joint_byte_demand q0 es qs n N byte <=>
   byte IN joint_reads (EL n (q0::qs)) \/
   (byte NOTIN joint_writes (EL n (q0::qs)) (EL n es) /\
    joint_byte_demand q0 es qs (SUC n) N byte))
Proof
  simp[joint_byte_demand_def, finite_byte_demand_unfold]
QED

Theorem joint_byte_demand_strict_witness:
  joint_trace vs0 ctx q0 es qs q /\ (n:num) < j /\ j <= N /\ N <= LENGTH es /\
  byte IN joint_reads (EL j (q0::qs)) /\
  (!k. n <= k /\ k < j ==>
    byte NOTIN joint_writes (EL k (q0::qs)) (EL k es)) ==>
  byte NOTIN joint_writes (EL n (q0::qs)) (EL n es)
Proof
  rpt strip_tac >> qpat_x_assum `!k. _` (qspec_then `n` mp_tac) >> simp[]
QED

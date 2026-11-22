(* A cut is the supplied chronological prefix strictly before one visit.
   In particular the empty prefix is a cut before the first instruction;
   the selected visit need not execute. Keep the native call/visit keys on
   both sides of a split, including while an INVOKE is still pending. *)
Theory entryCreateBodyCut
Ancestors
  dftGasFromListTraceDefs venomRunBounded gasOutcomeFull gasSummaryCompose
  gasSummary fragGasMode fragGasPath vyperStorageTrace vyperInterpreter vyperState list

Definition create_cut_marks_def:
  create_cut_marks explicit (visits : list_visit list) =
    MAP (\(_,fnc,inst,_). (fnc.fn_name,inst.inst_id) IN explicit)
      (FILTER (\(_,_,inst,_). inst.inst_opcode = GAS) visits)
End

Theorem create_cut_marks_append[simp]:
  create_cut_marks explicit (left ++ right) =
    create_cut_marks explicit left ++ create_cut_marks explicit right
Proof
  simp[create_cut_marks_def, FILTER_APPEND_DISTRIB]
QED

Theorem create_cut_marks_nil[simp]:
  create_cut_marks explicit [] = []
Proof
  simp[create_cut_marks_def]
QED

(* Entering a pending call does not consume a GAS read. The callee's GAS
   visits are already in the prefix and must not be counted a second time. *)
Theorem create_cut_marks_invoke:
  inst.inst_opcode = INVOKE ==>
  create_cut_marks explicit ((key,fnc,inst,s)::visits) =
  create_cut_marks explicit visits
Proof
  simp[create_cut_marks_def]
QED

Definition create_cut_failure_def:
  create_cut_failure tops res <=>
    res = INR (Error (RuntimeError "create initcode too large")) \/
    ?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err
End

(* Compiler-specific scoping is supplied at application: the theorem using
   this judgment ties the given prefix and visit to its body/frame entry.
   Do not replace the given visit by an existential run of the same code. *)
Definition create_body_cut_def:
  create_body_cut explicit tops cx st0 source (es,s) (before,hit : list_visit) <=>
    (case hit of (_,_,inst,t) => ~inst_create_size_ok inst t) ==>
    !H tail res ee.
      source (es with gas_obs :=
        gas_explicit (create_cut_marks explicit before) s.vs_gas_readings ++ tail) =
        (res,ee) /\ valid_horizon cx st0 H ee.storage_trace ==>
      create_cut_failure tops res
End

(* A bind propagates a size failure or exemption from the left without
   running its continuation. The source result types may differ. *)
Theorem create_cut_bind_left:
  create_body_cut explicit tops cx st0 source (es,s) (before,hit) /\
  (!v. storage_trace_frame (next v)) ==>
  create_body_cut explicit tops cx st0 (bind source next) (es,s) (before,hit)
Proof
  rw[create_body_cut_def] >> fs[bind_def] >>
  Cases_on `source (es with gas_obs :=
    gas_explicit (create_cut_marks explicit before) s.vs_gas_readings ++ tail)` >>
  qmatch_asmsub_rename_tac `source _ = (result,mid)` >>
  Cases_on `result` >> gvs[]
  >- (`?obs. ee.storage_trace = mid.storage_trace ++ obs` by
        metis_tac[storage_trace_frame_prefix] >>
      `valid_horizon cx st0 H mid.storage_trace` by metis_tac[valid_horizon_append] >>
      res_tac >> fs[create_cut_failure_def]) >>
  res_tac >> fs[create_cut_failure_def]
QED

(* A completed left evaluation provides the source equation for an
   arbitrary GAS tail at the actual split. A successful arm supplies one
   ghost pair satisfying the post at every valid horizon of that endpoint. *)
Definition create_cut_bind_split_def:
  create_cut_bind_split explicit tops cx st0 (ctx,fnc) source next (es,s)
      Q (left,right,hit) <=>
    ?t r mid.
      gas_marked_exec F (ctx,fnc) source (es,s)
        (create_cut_marks explicit left) r mid (OK t) /\
      (create_cut_failure tops r \/
       ?v G tn. r = INL v /\
         (!H. valid_horizon cx st0 H mid.storage_trace ==> Q H v mid G tn t) /\
         (!H. valid_horizon cx st0 H mid.storage_trace /\ Q H v mid G tn t ==>
           create_body_cut explicit tops cx st0 (next v) (mid,t) (right,hit)))
End

Theorem create_cut_bind_right:
  (!v. storage_trace_frame (next v)) /\
  create_cut_bind_split explicit tops cx st0 (ctx,fnc) source next (es,s)
    Q (left,right,hit) ==>
  create_body_cut explicit tops cx st0 (bind source next) (es,s) (left ++ right,hit)
Proof
  simp[create_cut_bind_split_def, gas_marked_exec_def, gas_marked_path_def] >>
  strip_tac >> drule gas_explicit_append_path >> strip_tac >>
  rw[create_body_cut_def] >>
  qpat_x_assum `bind _ _ _ = _` mp_tac >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[bind_def]
  >- (strip_tac >> gvs[create_cut_failure_def] >> metis_tac[]) >>
  strip_tac >> gvs[] >>
  `storage_trace_frame (next v)` by simp[] >>
  `?obs. ee.storage_trace = mid.storage_trace ++ obs` by
    (drule_all storage_trace_frame_prefix >> simp[]) >>
  `valid_horizon cx st0 H mid.storage_trace` by metis_tac[valid_horizon_append] >>
  fs[create_body_cut_def] >> metis_tac[]
QED

Theorem create_cut_bind:
  (!v. storage_trace_frame (next v)) /\
  (create_body_cut explicit tops cx st0 source (es,s) (before,hit) \/
   ?left right. before = left ++ right /\
     create_cut_bind_split explicit tops cx st0 (ctx,fnc) source next (es,s)
       Q (left,right,hit)) ==>
  create_body_cut explicit tops cx st0 (bind source next) (es,s) (before,hit)
Proof
  strip_tac
  >- (irule create_cut_bind_left >> simp[]) >>
  metis_tac[create_cut_bind_right]
QED

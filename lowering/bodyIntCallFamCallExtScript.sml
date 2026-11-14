(* Seam 2 joint induction, a family leaf of the call step: every other call target (external calls and send; the rest are not supported_expr). *)
Theory bodyIntCallFamCallExt
Ancestors
  bodyIntCallJointContract

Theorem intcall_extcall_step:
  (!e'. expr_size e' < expr_size e ==>
        intcall_expr_producer fp e' /\ intcall_forced_producer fp e' /\
        intcall_map_producer fp e') /\
  (?a tgt args dflt. e = Call a tgt args dflt /\ !nsid. tgt <> IntCall nsid) ==>
  intcall_expr_producer fp e /\ intcall_map_producer fp e
Proof
  rpt strip_tac
  >- (gvs[] >>
      Cases_on `supported_expr fp.jc_tops (Call a tgt args dflt)`
      >- (drule intcall_supported_call_forms >> strip_tac >> gvs[]
          >- (irule intcall_extcall_expr_step >> simp[]) >>
          irule intcall_send_expr_step >> simp[]) >>
      simp[intcall_expr_producer_def])
  >> irule intcall_effect_map_producer >> metis_tac[]
QED

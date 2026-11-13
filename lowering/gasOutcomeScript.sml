(* Every path selects its gas marks before the finite observation horizon.
   Invalid source traces and exempt source executions need no final target post. *)
Theory gasOutcome
Ancestors
  gasSummary gasExemptCert gasStorage vyperState

Definition gas_outcome_def:
  gas_outcome memory tops p cx st0 source (es,s0) Q R <=>
    ?marks.
      gas_bad_storage_at cx st0 source es s0 marks \/
      gas_summary_at memory p marks source (es,s0)
        (\res ee t. !H. valid_horizon cx st0 H ee.storage_trace ==>
          Q H res ee t)
        (\res ee r. !H. valid_horizon cx st0 H ee.storage_trace ==>
          R H res ee r) \/
      ?err ee leaf finish.
        gas_exempt_cert memory tops p (ignore_bind source (return ()))
          (es,s0) marks (err,ee) (leaf,finish)
End

(* Completed executions retain their full posts. Exempt executions retain
   a concrete source origin and their actual target call-prefix focus. *)
Theory gasOutcome
Ancestors
  gasSummary gasExemptCert vyperState

Definition gas_outcome_def:
  gas_outcome memory tops p source start Q R <=>
    ?marks.
      gas_summary_at memory p marks source start Q R \/
      ?err ee leaf finish.
        gas_exempt_cert memory tops p (ignore_bind source (return ()))
          start marks (err, ee) (leaf, finish)
End

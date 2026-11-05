Theory o1LowerDloadHypAudit
Ancestors
  o1LowerDloadFreshNext o1LowerDloadAllocationBoundary
  o1LowerDloadJointAllocation o1LowerDloadPairedAllocation
  o1LowerDloadRepeatedNext o1LowerDloadOrdinaryDispatch o1LowerDloadUnchangedFetch
  o1LowerDloadNonCallContinuation

val _ = List.app (fn (name, th) =>
  (print ("HYP AUDIT " ^ name ^ " count=" ^ Int.toString (length (hyp th)) ^ "\n");
   List.app (fn tm => print (term_to_string tm ^ "\n")) (hyp th)))
  [("lower_dload_paired_alloca_fresh", lower_dload_paired_alloca_fresh),
   ("ld_alloca_fresh", ld_alloca_fresh),
   ("ld_alloca_repeated", ld_alloca_repeated),
   ("ld_joint_alloca_fresh_metadata", ld_joint_alloca_fresh_metadata),
   ("ld_joint_alloca_fresh_next", ld_joint_alloca_fresh_next),
   ("ld_joint_alloca_repeated_next", ld_joint_alloca_repeated_next),
   ("ld_joint_ordinary_next", ld_joint_ordinary_next),
   ("ld_joint_unchanged_fetch", ld_joint_unchanged_fetch),
   ("ld_joint_noncall_continue", ld_joint_noncall_continue)];

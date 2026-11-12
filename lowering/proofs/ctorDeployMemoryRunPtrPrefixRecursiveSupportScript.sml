(* Composition of finite semantic supports of initialized values. *)
Theory ctorDeployMemoryRunPtrPrefixRecursiveSupport
Ancestors
  ctorDeployMemoryRunPtrPrefixCopySupport pred_set

Theorem prefix_support_transport:
  (!mem. (!a. a IN B ==> mem_bytes_at a 1 mem = mem_bytes_at a 1 m) ==>
         P mem) /\
  (!a. a IN B ==> mem_bytes_at a 1 m' = mem_bytes_at a 1 m) ==>
  (!mem. (!a. a IN B ==> mem_bytes_at a 1 mem = mem_bytes_at a 1 m') ==>
         P mem)
Proof
  metis_tac[]
QED

Theorem prefix_support_union:
  FINITE B /\ FINITE C /\ B SUBSET R /\ C SUBSET U /\
  DISJOINT B t /\ DISJOINT C t ==>
  FINITE (B UNION C) /\ B UNION C SUBSET R UNION U /\
  DISJOINT (B UNION C) t
Proof
  simp[SUBSET_DEF, DISJOINT_DEF, EXTENSION] >> metis_tac[]
QED

Theorem prefix_support_taint_mono:
  DISJOINT B t /\ t' SUBSET t ==> DISJOINT B t'
Proof
  simp[SUBSET_DEF, DISJOINT_DEF, EXTENSION] >> metis_tac[]
QED

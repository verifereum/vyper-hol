(* Spatial authorization for protected caller intervals. *)
Theory bodyIntCallResourceSpans
Ancestors
  intCallFrame intCallCallee compileEnv venomState arithmetic

Theorem protected_span_subregion:
  (!a n. P a n ==> regions_disjoint a n b z) /\
  b <= p /\ p + k <= b + z ==>
  !a n. P a n ==> regions_disjoint a n p k
Proof
  simp[regions_disjoint_def] >> rpt strip_tac >>
  first_x_assum drule >> decide_tac
QED

Theorem protected_span_above_frontier:
  (!a n. P a n ==> a + n <= lo) /\ lo <= p ==>
  !a n. P a n ==> regions_disjoint a n p k
Proof
  simp[regions_disjoint_def] >> rpt strip_tac >>
  first_x_assum drule >> decide_tac
QED

Theorem materialization_protected_bytes:
  mat_frame st entry landing /\
  (!a n. P a n ==> a + n <= entry.vs_alloca_next) /\
  (!a n. P a n ==>
    mem_bytes_at a n entry.vs_memory = mem_bytes_at a n origin.vs_memory) ==>
  !a n. P a n ==>
    mem_bytes_at a n landing.vs_memory = mem_bytes_at a n origin.vs_memory
Proof
  rw[mat_frame_def] >> metis_tac[]
QED

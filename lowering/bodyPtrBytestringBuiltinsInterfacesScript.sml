(* Initial interface checks for bytestring pointer cases.
   The uint2str allocation is B+n, not B: its interior result must retain
   a whole B-byte capacity. No new semantic definition is needed. *)
Theory bodyPtrBytestringBuiltinsInterfaces
Ancestors
  arithmetic

Theorem enlarged_buffer_offset_bounds:
  !B n k. 0 < B /\ k <= n ==>
    k < B + n /\ k + B <= B + n
Proof
  decide_tac
QED

Theorem uint2str_result_capacity:
  !B n d. 0 < B ==>
    n - d < B + n /\ (n - d) + B <= B + n
Proof
  rpt gen_tac >> disch_tac >> irule enlarged_buffer_offset_bounds >> simp[]
QED

(* Small integration boundary for the auxiliary bounded-ghost audit. *)
Theory assignBasePtrCapacityProbe
Ancestors bodyPtrDefs words finite_map

Theorem assign_base_ptr_bounded_buffer_offset:
  !cenv e op G s w off.
    (!x b sz. FLOOKUP G x = SOME (b,sz) ==> b + sz <= dimword(:256)) /\
    ptr_buf_ok cenv e op G s /\ eval_operand op s = SOME w /\
    off < type_memory_bytes cenv (lowered_value_type cenv e) ==>
    w2n w + off < dimword(:256)
Proof
  rpt strip_tac >> fs[ptr_buf_ok_def] >>
  `type_memory_bytes cenv (lowered_value_type cenv e) <> 0` by decide_tac >>
  first_x_assum drule_all >> strip_tac >>
  decide_tac
QED

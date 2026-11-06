Theory bodyPtrIntCallRunInvokeAllocator
Ancestors bodyPtrIntCallAllocation allocaFrontierBound

(* step_inst_invoke_alloca_fields already supplies the exact allocator
   equality, so the pointer boundary only packages its invariant consumer. *)
Theorem intcall_invoke_alloc_outside:
  inst.inst_opcode = INVOKE /\ step_inst fuel ctx inst s = OK t /\
  intcall_alloc_outside P s ==>
  intcall_alloc_outside P (t with vs_inst_idx := k)
Proof
  strip_tac >> drule_all step_inst_invoke_alloca_fields >>
  strip_tac >> gvs[intcall_alloc_outside_def] >> metis_tac[]
QED

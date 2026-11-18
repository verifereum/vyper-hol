(* Consumer-facing semantic reads from robust bytestring pointers. *)
Theory bodyPtrSignedConvertBytesRead
Ancestors bodyPtrBopHashFootprint
  representationCleanPtr bodyPtrDefs valueEncoding arithmetic

Theorem ptr_mem_ok_bytes_header_clean:
  !cx ty bs op G tn s tv w.
    ptr_mem_ok cx ty (BytesV bs) op G tn s /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    eval_operand op s = SOME w ==>
    !i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn.t_mem
Proof
  rpt gen_tac >> strip_tac >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory tv (BytesV bs) (w2n w) mem` by gvs[ptr_mem_ok_def] >>
  drule robust_val_in_memory_bytes_clean >> simp[]
QED

Theorem ptr_mem_ok_bytes_window_clean:
  !cx ty bs op G tn s tv w off n.
    ptr_mem_ok cx ty (BytesV bs) op G tn s /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    eval_operand op s = SOME w /\ tv <> BaseTV AddressT /\
    (!k. tv <> BaseTV (BytesT (Fixed k))) /\ off + n <= LENGTH bs ==>
    !i. w2n w + 32 + off <= i /\ i < w2n w + 32 + off + n ==>
        i NOTIN tn.t_mem
Proof
  rpt gen_tac >> strip_tac >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory tv (BytesV bs) (w2n w) mem` by gvs[ptr_mem_ok_def] >>
  drule robust_val_in_memory_bytes_clean >> simp[] >> strip_tac >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED

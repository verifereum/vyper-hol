(* State-level obstruction only: this does not realize a source expression. *)
Theory assignBasePtrPaddingProbe
Ancestors assignBasePtrLiteralGhost assignBasePtrMcopyTransport bodyPtrDefs
  valueEncoding valueEncodingProps venomState venomExecSemantics venomInst
  ptrDiscipline words list pred_set loweringPosts venomMemProps

Theorem assign_base_ptr_short_bytes_padding_robust:
  !mem. mem_agree_outside {63} (REPLICATE 31 (0w:word8) ++ [1w] ++ REPLICATE 32 0w) mem ==>
    val_in_memory (BaseTV (BytesT (Dynamic 32))) (BytesV [0w]) 0 mem
Proof
  rpt strip_tac >> irule assign_base_ptr_clean_footprint_robust >>
  conj_tac >- (simp[val_wf_def, type_memory_size_def] >> EVAL_TAC) >>
  qexistsl_tac [`REPLICATE 31 (0w:word8) ++ [1w] ++ REPLICATE 32 0w`, `33`, `{63}`] >>
  simp[val_footprint_def, val_in_memory_def] >> EVAL_TAC >>
  simp[dimindex_256] >> EVAL_TAC
QED

Theorem assign_base_ptr_short_bytes_padding_copy:
  !s tn.
    tn.t_mem = {63} ==>
    191 IN (step_taint (mk_inst 0 MCOPY [Lit 128w; Lit 0w; Lit 64w] [])
      s (mcopy 128 0 64 s) tn).t_mem /\ 191 NOTIN tn.t_mem
Proof
  rpt strip_tac >>
  `!i. i < 64 ==>
    (128+i IN (step_taint (mk_inst 0 MCOPY [Lit 128w; Lit 0w; Lit 64w] [])
      s (mcopy 128 0 64 s) tn).t_mem <=> i IN tn.t_mem)` by
    (rpt strip_tac >> irule (SRULE [dimword_def, dimindex_256] (Q.INST [`a` |-> `0w`, `b` |-> `128w`, `n` |-> `64w`]
      (SPEC_ALL (cj 1 assign_base_mcopy_taint_window)))) >>
     simp[eval_operand_def]) >>
  first_x_assum (qspec_then `63` mp_tac) >> gvs[]
QED

(* Header [0,32) and payload byte 32 are clean, yet the rounded copy
   propagates padding byte 63 into a previously clean destination byte 191.
   For a Bytes[32] local at 128, 191 is protected by ghost_kept (it is not
   a dynarray length byte). Full expression and statement hypotheses are
   intentionally not claimed by this state-level diagnostic. *)
Theorem assign_base_ptr_padding_frame_obstruction:
  ?s tn.
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory (BaseTV (BytesT (Dynamic 32))) (BytesV [0w]) 0 mem) /\
    191 IN (step_taint (mk_inst 0 MCOPY [Lit 128w; Lit 0w; Lit 64w] [])
      s (mcopy 128 0 64 s) tn).t_mem /\ 191 NOTIN tn.t_mem
Proof
  qexistsl_tac [
    `(ARB:venom_state) with vs_memory :=
      REPLICATE 31 (0w:word8) ++ [1w] ++ REPLICATE 32 0w`,
    `(ARB:taint) with t_mem := {63}`] >>
  conj_tac >- simp[assign_base_ptr_short_bytes_padding_robust] >>
  irule assign_base_ptr_short_bytes_padding_copy >> simp[]
QED

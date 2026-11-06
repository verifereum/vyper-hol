(* Memory-safe failure forwarding: the copy/revert pair is exempt. *)
Theory bodyMemRawCallRevert
Ancestors
  fragExecMem exprSimRawCallCalldata loweringHalt emitHelper compileEnv
  venomExecSemantics venomState venomInst

Theorem raw_call_failure_tail_mem:
  emit_void RETURNDATACOPY [dst;Lit 0w;sz] sa = ((),sb) /\
  emit_inst REVERT [dst;sz] [] sb = ((),sc) /\
  eval_operand dst s = SOME addr /\
  eval_operand sz s = SOME (n2w (LENGTH s.vs_returndata)) /\
  LENGTH s.vs_returndata < dimword (:256) /\
  (!t. t.vs_returndata = s.vs_returndata ==> R (Abort Revert_abort t)) ==>
  frag_exec_mem ctx sa sc (\t. t = s) Q R
Proof
  strip_tac >>
  `sc.cs_current_bb = sa.cs_current_bb /\
   sc.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id RETURNDATACOPY [dst;Lit 0w;sz] [];
      mk_inst sb.cs_next_id REVERT [dst;sz] []]` by
    (gvs[emit_void_def, emit_inst_def, comp_bind_def, fresh_id_def,
         emit_def, comp_ignore_bind_def, comp_return_def]) >>
  irule revert_forward_frag_mem >> conj_tac >- simp[] >>
  qexistsl_tac [`sa.cs_next_id`, `sb.cs_next_id`, `dst`, `sz`] >>
  simp[] >> disj2_tac >>
  qexists_tac `write_memory_with_expansion (w2n addr) s.vs_returndata s` >>
  qexistsl_tac [`Revert_abort`,
    `revert_state (set_returndata s.vs_returndata
       (write_memory_with_expansion (w2n addr) s.vs_returndata s with
        vs_inst_idx := SUC s.vs_inst_idx))`] >>
  conj_tac
  >- (irule (cj 1 raw_call_revert_copy) >> simp[]) >>
  conj_tac
  >- (qspec_then `s with vs_inst_idx := SUC s.vs_inst_idx` mp_tac
        (cj 2 raw_call_revert_copy) >>
      simp[write_memory_with_expansion_def, eval_operand_def, lookup_var_def] >>
      Cases_on `dst` >> Cases_on `sz` >>
      gvs[eval_operand_def, lookup_var_def]) >>
  first_x_assum irule >>
  simp[revert_state_def, set_returndata_def]
QED

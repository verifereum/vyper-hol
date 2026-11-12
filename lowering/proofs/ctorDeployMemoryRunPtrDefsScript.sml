(* The constructor frame's pointer invariant at the boundaries of its body,
 * in the deployment's dead bytes D = deploy_dead and bound lo = imm_len:
 * storage and transient storage tainted only in D's bytes; the immutables
 * fixed region [0, imm_len) tainted only on the bytes the immutables
 * section leaves dead (imm_section_dead of the region's current bytes),
 * which the epilogue copies to the returned section where D.d_ret marks
 * them dead; the region's base variable imm untainted and no pointer; and
 * every ALLOCA site, and the frontier, at or above imm_len.
 * TOP-LEVEL: deploy_ptr_inv.
 *)
Theory ctorDeployMemoryRunPtrDefs
Ancestors
  ctorDeployDefs ptrDiscipline valueEncoding

Definition deploy_ptr_inv_def:
  deploy_ptr_inv tops runtime_bc am tx (imm : operand) G tn
    (s : venom_state) <=>
    tn.t_stor SUBSET
      (deploy_dead tops runtime_bc am tx).d_stor s.vs_call_ctx.cc_address
        (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
    tn.t_trans SUBSET
      (deploy_dead tops runtime_bc am tx).d_trans s.vs_call_ctx.cc_address
        (s.vs_transient s.vs_call_ctx.cc_address) /\
    (!i. i < imm_len tops /\ i IN tn.t_mem ==>
         imm_section_dead tops (mem_bytes_at 0 (imm_len tops) s.vs_memory) i) /\
    (!x. imm = Var x ==> FLOOKUP G x = NONE /\ op_taint tn (Var x) = {}) /\
    allocas_from (imm_len tops) s /\ imm_len tops <= s.vs_alloca_next
End

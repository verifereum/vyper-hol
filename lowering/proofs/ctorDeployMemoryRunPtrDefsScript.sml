(* The constructor frame's pointer invariant at the boundaries of its body,
 * in the deployment's dead bytes D = deploy_dead and bound lo = imm_len:
 * storage and transient storage tainted only in D's bytes; the immutables
 * fixed region [0, imm_len) tainted only on the bytes the immutables
 * section leaves dead (imm_section_dead of the region's current bytes),
 * which the epilogue copies to the returned section where D.d_ret marks
 * them dead; the region's base variable imm untainted and no pointer; and
 * every ALLOCA site, and the frontier, at or above imm_len.
 * TOP-LEVEL: deploy_ptr_inv; ghost_inv_at_deploy_ptr_inv, the body's
 * (D, lo) ghost invariant at deploy's (deploy_dead, imm_len) implies it.
 *)
Theory ctorDeployMemoryRunPtrDefs
Ancestors
  ctorDeployDefs bodyPtrDefs ptrDiscipline valueEncoding compileEnv
  vyperContext vyperInterpreter vyperState vyperStorageLayoutSafety e2eDeployDefs

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

Theorem storage_dead_in_deploy:
  !cx d tr st j b.
    storage_dead (cx with in_deploy := d) tr st j b <=> storage_dead cx tr st j b
Proof
  rpt gen_tac >>
  `!mid n subs. declared_storage_region (cx with in_deploy := d) mid n subs =
                declared_storage_region cx mid n subs` by
    simp[declared_storage_region_def, get_module_code_def, get_tenv_def,
         lookup_var_slot_from_layout_def] >>
  simp[storage_dead_def]
QED

(* The body's ghost invariant at deploy's dead bytes and bound carries
   deploy_ptr_inv: the fixed region's base is ce_imm_alloca when the region
   is non-empty, and the literal 0 otherwise. *)
Theorem ghost_inv_at_deploy_ptr_inv:
  !tops runtime_bc am tx d cenv cx es G tn s imm.
    ghost_inv_at (deploy_dead tops runtime_bc am tx) (imm_len tops) d cenv cx
      es G tn s /\
    cx_tops cx = tops /\
    (imm_len tops <> 0 ==> cenv.ce_imm_alloca = SOME imm) /\
    (imm_len tops = 0 ==> imm = Lit 0w) ==>
    deploy_ptr_inv tops runtime_bc am tx imm G tn s
Proof
  rw[ghost_inv_at_def, stor_taint_ok_at_def, deploy_ptr_inv_def] >>
  Cases_on `imm_len tops = 0` >> gvs[]
QED

(* The runtime dead bytes of the deploy context lie in deploy's. *)
Theorem dead_sub_cx_dead_deploy_dead:
  !tops runtime_bc am tx.
    dead_sub (cx_dead (deploy_evaluation_context tops am tx))
      (deploy_dead tops runtime_bc am tx)
Proof
  rw[dead_sub_def, cx_dead_def, deploy_dead_def, deploy_evaluation_context_def,
     storage_dead_in_deploy] >>
  simp[initial_evaluation_context_def]
QED

(* The memory, pointer and DLOAD invariants of a lowered unit whose run
 * starts with its alloca frontier at k rather than 0: the deployment unit
 * starts it above the immutables region, which it addresses as a fixed
 * region at offset 0.
 *
 * alloca_frontier_inv_from k is allocaFrontierBound's alloca_frontier_inv
 * with the budget raised by k, and is proved closed the same way.  The
 * other theorems take a unit that passed lowering_context_ok, with its
 * entry function, and give the S3 conjuncts the O1 pipeline's source
 * invariant asks for (o1_src_inv), from the run facts the unit's own
 * proofs provide: a memory-safe run, a pointer-safe run, and the
 * frontier's headroom.
 *
 * TOP-LEVEL:
 *   alloca_frontier_inv_from, alloca_frontier_inv_from_closed,
 *   alloca_frontier_inv_from_entry
 *   lowered_unit_raw_memory_ok_from, lowered_unit_dload_headroom_ok_from,
 *   lowered_unit_dload_offset_ok, lowered_unit_ptr_taint
 *   lowered_unit_entry_facts -- what lowering_context_ok gives the entry
 *   deploy_unit_run_entry -- the deployment unit's entry, at frontier
 *     imm_len
 *)
Theory ctorDeployMemoryFrontier
Ancestors
  allocaFrontierBound allocaBudgetProps contextCodegenRel
  contextCodegenRelProps fcgPostorder fcgCorrectnessProof fcgDefs
  vyperCompiler venomWf venomExecSemantics venomInst venomState
  memSafeRun ptrSafeRun ptrOkCheck ptrDiscipline unitMemInv
  unitTransformDefs lowerDloadDefs ctorDeployDefs deployUnitProducers
  o1PassContract loweredUnitMemoryFrontier
  finite_map list pred_set relation arithmetic


(* ===== The deployment unit ===== *)

(* The deployment unit passed lowering_context_ok, its entry is __deploy,
   and its run starts with the alloca frontier at imm_len. *)
Theorem deploy_unit_run_entry:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan es vs.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    gas_variant vs (deploy_entry_state prog cplan tops es)
    ==>
    lowering_context_ok dunit.cu_context /\
    dunit.cu_context.ctx_entry = SOME "__deploy" /\
    vs.vs_alloca_next = imm_len tops /\
    ?fn lbl. lookup_function "__deploy" dunit.cu_context.ctx_functions =
               SOME fn /\
             fn_entry_label fn = SOME lbl
Proof
  rpt gen_tac >> strip_tac >>
  `lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit` by
    fs[deploy_phases_def] >>
  drule lower_vyper_deploy_unit_context_ok >> strip_tac >>
  drule lower_vyper_deploy_unit_entry >> strip_tac >>
  drule_all lowered_unit_entry_facts >> strip_tac >>
  simp[] >>
  qpat_x_assum `gas_variant _ _` mp_tac >> simp[gas_variant_def] >>
  disch_then (mp_tac o AP_TERM ``\s:venom_state. s.vs_alloca_next``) >>
  simp[deploy_entry_state_def]
QED

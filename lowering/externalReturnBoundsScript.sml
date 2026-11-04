Theory externalReturnBounds
Ancestors
  stmtSimReturn exprSim allocaFootprint exprLoweringProps venomMemDefs
  compileEnv

(* Zero-footprint values need no readable region.  Every nonempty expression
   value is instead backed by an allocation or a live local region. *)
Theorem expr_val_at_frontier:
  stmt_state_rel ctx func cenv cx es s /\
  expr_val_at cenv cx ty sa sb es v op s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty ==>
  ?w. eval_operand op s = SOME w /\
      (val_footprint tv v = 0 \/
       w2n w + val_footprint tv v <= s.vs_alloca_next)
Proof
  rpt strip_tac >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_val_at_def] >> strip_tac >>
  qexists_tac `w` >> simp[]
  >- (gvs[stmt_state_rel_def, alloca_inv_def, alloca_next_valid_def] >>
      first_x_assum drule >> decide_tac)
  >- (gvs[stmt_state_rel_def, state_rel_def, local_region_def] >>
      drule_all local_ptr_below_frontier >> strip_tac >> gvs[] >>
      decide_tac)
QED

Theorem stmt_state_rel_alloca_site:
  stmt_state_rel ctx func cenv cx es s /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_operands = [Lit (n2w n)] /\ n < dimword (:256) ==>
  ?b. FLOOKUP (abi_builtin_allocate_state inst.inst_id n s).vs_allocas
        inst.inst_id = SOME (b,n)
Proof
  rpt strip_tac >> simp[alloca_site_cases] >>
  Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
  >- simp[] >>
  PairCases_on `x` >>
  gvs[stmt_state_rel_def] >>
  first_x_assum drule_all >> simp[]
QED

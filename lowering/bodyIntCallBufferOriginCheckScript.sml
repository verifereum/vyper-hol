Theory bodyIntCallBufferOriginCheck
Ancestors
  exprLoweringProps compileEnv venomMemDefs venomState vyperState
  vyperValue vyperAST valueEncoding finite_map

(* Interface diagnostic, not a counterexample to the complete seam.
   A map key not owned by an ALLOCA may alias an initialized immutable. *)
Theorem unowned_allocation_immutable_alias:
  (!inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA ==>
          inst.inst_id <> 7) ==>
  let ce' = ce with <| ce_is_ctor := T; ce_module := NONE;
             ce_module_vars := FEMPTY |+ ((NONE,"imm"), ImmutableLoc 0);
             ce_vars := FEMPTY |>;
      es' = es with <| scopes := [];
              immutables := [(cx.txn.target,
                [(NONE,FEMPTY |+ ("imm",(BaseTV BoolT,BoolV T)))])] |>;
      s' = s with <| vs_allocas := FEMPTY |+ (7,(0,32));
                     vs_alloca_next := 32 |>
  in
    immutable_alloca_sep func ce' cx es' s' /\ alloca_inv s' /\
    FLOOKUP s'.vs_allocas 7 = SOME (0,32) /\
    ~compileEnv$regions_disjoint 0 32 0 (type_memory_size (BaseTV BoolT))
Proof
  strip_tac >>
  simp[immutable_alloca_sep_def, local_region_def, lookup_scopes_def,
       alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
       get_source_immutables_def, FLOOKUP_UPDATE, AllCaseEqs(),
       type_memory_size_def, compileEnvTheory.regions_disjoint_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  res_tac >> gvs[]
QED

(* Prospective cursor sites may be fresh or registered already. *)
Theory extRetCursorResourcePtr
Ancestors
  allocationPtr allocaSiteResource abiBuiltinAllocation codegenRel exprLoweringProps
  stmtSimDefs venomMemDefs venomState venomInst compileEnv
  words finite_map arithmetic

Theorem return_cursor_allocation_resources:
  stmt_state_rel ctx fn cenv cx es s /\
  MEM (mk_inst cid ALLOCA [Lit 32w] [out]) (fn_insts fn) /\
  FLOOKUP s.vs_allocas did = SOME (b,n) /\ did <> cid /\ 0 < n /\ used <= n ==>
  ?cursor.
    FLOOKUP (abi_builtin_allocate_state cid 32 s).vs_allocas cid =
      SOME (cursor,32) /\ cursor+32 < dimword(:256) /\
    (cursor+32 <= b \/ b+used <= cursor)
Proof
  strip_tac >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  `32 < dimword(:256)` by (simp[dimword_def] >> decide_tac) >>
  Cases_on `FLOOKUP s.vs_allocas cid`
  >- (drule_all stmt_state_rel_alloca_fresh_bound >> strip_tac >>
      drule_all alloca_site_registered_below >> strip_tac >>
      qexists_tac `s.vs_alloca_next` >>
      simp[abi_builtin_allocate_state_def, FLOOKUP_UPDATE] >> decide_tac) >>
  rename1 `FLOOKUP s.vs_allocas cid = SOME site` >> PairCases_on `site` >>
  drule_all stmt_state_rel_alloca_site_bound >> strip_tac >>
  `venomMemDefs$regions_disjoint (b,n) (site0,site1)` by
    (irule alloca_site_registered_disjoint >> metis_tac[]) >>
  qexists_tac `site0` >>
  gvs[abi_builtin_allocate_state_def, venomMemDefsTheory.regions_disjoint_def] >>
  decide_tac
QED

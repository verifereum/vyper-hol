(* Tagged getters and their linked ABI signatures. *)
Theory defaultDispatchModsGetter
Ancestors
  compileUnit entryDispatchProps publicGetterProps vyperTypeContractGetter
  vyperGetter compileVyper vyperABIEntries vyperTypeContract list pair
Libs
  BasicProvers

(* Changing the root of a getter changes its expression, not its parameters. *)
Theorem build_getter_args_root_irrelevant[local]:
  !e kt vt n e'.
    FST (build_getter e kt vt n) = FST (build_getter e' kt vt n)
Proof
  recInduct build_getter_ind >> rpt strip_tac >>
  simp[SimpLHS, Once build_getter_def] >>
  simp[SimpRHS, Once build_getter_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >> metis_tac[FST]
QED

Theorem tagged_getter_source_tuple:
  !src top mut nr rr name args dflts ret body.
    public_getter_src src top = SOME (mut,nr,rr,name,args,dflts,ret,body) <=>
    rr = F /\ is_public_getter_decl name top /\
    external_getter_tuple src top = SOME (mut,nr,args,dflts,ret,body)
Proof
  rpt gen_tac >> Cases_on `top` >>
  simp[public_getter_src_def, is_public_getter_decl_def, external_getter_tuple_def] >>
  Cases_on `v` >>
  simp[public_getter_src_def, is_public_getter_decl_def, external_getter_tuple_def] >>
  rpt CASE_TAC >> simp[getter_def] >>
  rpt (pairarg_tac >> gvs[]) >> metis_tac[]
QED

Theorem tagged_getter_decl_signature:
  !src top m n r name a ds ret b.
    public_getter_src src top = SOME (m,n,r,name,a,ds,ret,b) ==>
    abi_decl_signatures top = [(name,MAP SND a)]
Proof
  rpt gen_tac >> Cases_on `top` >> simp[public_getter_src_def] >> Cases_on `v` >>
  simp[public_getter_src_def] >> rpt CASE_TAC >> simp[getter_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[]
  >- (Cases_on `ret` >> gvs[abi_decl_signatures_def, abi_array_getter_args_def,
                            vyperASTTheory.is_ArrayT_def]) >>
  irule public_getter_signature >>
  simp[public_getter_def, getter_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  metis_tac[build_getter_args_root_irrelevant, FST]
QED

Theorem tagged_getter_name_key:
  public_getter_src src top = SOME g ==>
  MEM (src,fn_decl_name g) (external_name_keys_toplevel src top)
Proof
  PairCases_on `g` >> simp[tagged_getter_source_tuple, fn_decl_name_def] >>
  Cases_on `top` >> simp[is_public_getter_decl_def] >> Cases_on `v` >>
  simp[is_public_getter_decl_def, external_name_keys_toplevel_def]
QED

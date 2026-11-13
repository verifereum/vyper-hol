(* Public getter ABI signatures and default-argument shape. *)
Theory publicGetterProps
Ancestors
  compileVyper vyperABIEntries vyperGetter list
Libs
  BasicProvers

Theorem build_getter_arg_types_projection[local]:
  !e kt vt n.
    MAP SND (FST (build_getter e kt vt n)) = kt :: abi_getter_args vt
Proof
  recInduct build_getter_ind >> rpt strip_tac >>
  simp[Once build_getter_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
  gvs[abi_getter_args_def] >>
  Cases_on `vt` >> gvs[vyperASTTheory.is_ArrayT_def, vyperASTTheory.ArrayT_type_def,
                         abi_array_getter_args_def]
QED

Theorem build_getter_arg_types[local]:
  !e kt vt n args ret exp.
    build_getter e kt vt n = (args,ret,exp) ==>
    MAP SND args = kt :: abi_getter_args vt
Proof
  metis_tac[build_getter_arg_types_projection, pairTheory.FST]
QED

Theorem public_getter_signature:
  !top m nr rr name args ds ret body.
    public_getter top = SOME (m,nr,rr,name,args,ds,ret,body) ==>
    abi_decl_signatures top = [(name,MAP SND args)]
Proof
  Cases >> simp[public_getter_def]
  >- (rename1 `VariableDecl vis mut id ty slot` >> Cases_on `vis` >>
      simp[public_getter_def] >> Cases_on `ty` >>
      simp[vyperASTTheory.is_ArrayT_def, abi_decl_signatures_def, abi_array_getter_args_def,
           public_getter_def, vyperASTTheory.ArrayT_type_def, getter_def] >>
      rpt gen_tac >> rpt (pairarg_tac >> gvs[]) >>
      strip_tac >> gvs[] >>
      imp_res_tac build_getter_arg_types >> gvs[abi_getter_args_def]) >>
  rename1 `HashMapDecl vis tr id kt vt slot` >> Cases_on `vis` >>
  simp[public_getter_def, getter_def] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[]) >>
  strip_tac >> gvs[abi_decl_signatures_def] >>
  imp_res_tac build_getter_arg_types >> gvs[]
QED

Theorem public_getter_defaults:
  !top mut nr rr name args dflts ret body.
    public_getter top = SOME (mut,nr,rr,name,args,dflts,ret,body) ==>
    dflts = []
Proof
  Cases_on `top` >> simp[public_getter_def] >> rpt gen_tac >>
  Cases_on `v` >> simp[public_getter_def, getter_def] >>
  rpt CASE_TAC >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  strip_tac >> gvs[]
QED

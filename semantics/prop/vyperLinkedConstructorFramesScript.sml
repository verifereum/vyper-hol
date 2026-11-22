(* Frame declared constant cells through the checked deployment entry. *)
Theory vyperLinkedConstructorFrames
Ancestors
  list alist vyperState vyperContext vyperInterpreter vyperTypeContract
  vyperTypeConstantCells vyperTypeCallGraph vyperDeployLiveClosure
  vyperLinkedConstructorGuards vyperProtectedLiveFrame

Theorem checked_deploy_constructor_frames:
  check_contract T cx.layouts cx.txn.target mods = SOME art /\
  cx.in_deploy /\ ALOOKUP cx.sources cx.txn.target = SOME mods /\
  ALOOKUP mods NONE = SOME main /\
  lookup_function NONE fn Deploy main = SOME (mut,nr,args,ds,ret,b) /\
  declared_constant mods sid nm ==>
  (!n st r st'. eval_exprs cx (DROP n ds) st = (r,st') ==>
    lookup_immutable cx st' sid nm = lookup_immutable cx st sid nm) /\
  (!st r st'. eval_stmts cx b st = (r,st') ==>
    lookup_immutable cx st' sid nm = lookup_immutable cx st sid nm)
Proof
  strip_tac >>
  `(!src ts f vis m nr raw args ds rt body.
      MEM (src,ts) mods /\ module_allocated cx.layouts cx.txn.target src ts /\
      MEM (FunctionDecl vis m nr raw f args ds rt body) ts ==>
      MEM (src,f) (live_functions cx.layouts cx.txn.target mods)) /\
   (!k c. MEM k (live_functions cx.layouts cx.txn.target mods) /\
      MEM (k,c) (contract_call_edges mods) ==>
      MEM c (live_functions cx.layouts cx.txn.target mods))` by
    (irule deploy_live_functions_closed) >>
  gvs[] >> drule_all checked_deploy_constructor_guards >> strip_tac >>
  mp_tac (Q.INST [`P` |-> `\k. MEM k (live_functions cx.layouts cx.txn.target mods)`]
    live_protected_evaluation_frames) >>
  simp[get_module_code_def] >>
  (impl_tac >- gvs[]) >> strip_tac >>
  conj_tac >> rpt gen_tac >> strip_tac >> gvs[] >> metis_tac[]
QED

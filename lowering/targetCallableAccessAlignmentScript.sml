Theory targetCallableAccessAlignment
Ancestors
  targetIndexAccessClosure supportedNames supportedProgram bodySim
  vyperInterpreter vyperSubscriptOverlap vyperTypeContractStaticMaps
  list externalBodyFrame

Theorem find_function_unique_member[local]:
  !ts vis mut nr raw fn args dflts ret stmts.
  ALL_DISTINCT (supported_function_names ts) /\
  MEM (FunctionDecl vis mut nr raw fn args dflts ret stmts) ts ==>
  find_function fn ts = SOME (dflts,stmts)
Proof
  Induct >> simp[supported_function_names_def, find_function_def] >>
  rpt gen_tac >> Cases_on `h` >>
  simp[supported_function_names_def, find_function_def] >>
  rpt strip_tac >> gvs[] >>
  metis_tac[supported_function_names_mem]
QED

Theorem lookup_callable_find_function:
  ALL_DISTINCT (supported_function_names ts) /\
  lookup_callable_function F fn ts = SOME (mut,nr,args,dflts,ret,stmts) ==>
  find_function fn ts = SOME (dflts,stmts)
Proof
  strip_tac >> drule lookup_callable_function_F_SOME_MEM >> strip_tac >>
  irule find_function_unique_member >> metis_tac[]
QED

Theorem callable_function_access_member:
  ALL_DISTINCT (supported_function_names ts) /\
  lookup_callable_function F fn ts = SOME (mut,nr,args,dflts,ret,stmts) /\
  ALOOKUP mods src = SOME ts /\
  (!ref. a <> ReadAcc (LocalRef ref) /\ a <> WriteAcc (LocalRef ref)) /\
  MEM a (accesses_exprs dflts ++ accesses_stmts stmts) ==>
  MEM a (function_accesses mods (src,fn))
Proof
  strip_tac >> drule_all lookup_callable_find_function >> strip_tac >>
  simp[function_accesses_def, callee_state_access_preserved]
QED

Theorem body_inv_callable_find_function:
  body_inv tops ctx cenv cx /\ get_module_code cx src = SOME ts /\
  lookup_callable_function F fn ts = SOME (mut,nr,args,dflts,ret,stmts) ==>
  find_function fn ts = SOME (dflts,stmts)
Proof
  strip_tac >>
  `ts = tops` by (fs[body_inv_def] >> metis_tac[optionTheory.SOME_11]) >> gvs[] >>
  irule lookup_callable_find_function >>
  reverse conj_tac >- metis_tac[] >>
  gvs[body_inv_def, supportedProgramTheory.supported_program_def,
      supported_declaration_names_def]
QED

Theorem body_inv_callable_access_member:
  body_inv tops ctx cenv cx /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  ALOOKUP mods src = SOME ts /\
  lookup_callable_function F fn ts = SOME (mut,nr,args,dflts,ret,stmts) /\
  (!ref. a <> ReadAcc (LocalRef ref) /\ a <> WriteAcc (LocalRef ref)) /\
  MEM a (accesses_exprs dflts ++ accesses_stmts stmts) ==>
  MEM a (function_accesses mods (src,fn))
Proof
  strip_tac >>
  `get_module_code cx src = SOME ts` by
    simp[vyperContextTheory.get_module_code_def] >>
  drule_all body_inv_callable_find_function >> strip_tac >>
  simp[function_accesses_def, callee_state_access_preserved]
QED

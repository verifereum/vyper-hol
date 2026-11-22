(* Static write and call guards for the deploy entry and its live callees. *)
Theory vyperLinkedConstructorGuards
Ancestors
  list rich_list alist vyperAST vyperStorage vyperInterpreter vyperTypeSystem
  vyperTypeContract vyperTypeContractStaticMaps vyperTypeContractContext
  vyperTypeCallGraph vyperTypeCallGraphSoundness vyperTypeConstantCells
  vyperRuntimeWriteSafety vyperCheckedConstantWrites vyperReadOnlyEval

val live = ``live_functions
  (layouts : ('a # (storage_layout # storage_layout)) list) addr mods``;
val reached = ``\k. MEM k ^live``;
val guard = ``runtime_write_root (\s id. (s,id) <> (sid,nm))``;
val edges_closed = ``!k c. MEM k ^live /\
  MEM (k,c) (contract_call_edges mods) ==> MEM c ^live``;

Theorem live_decl_guards[local]:
  check_contract T layouts addr mods = SOME art /\
  declared_constant mods sid nm /\ ^edges_closed /\
  MEM (src,fn) ^live /\ ALOOKUP mods src = SOME ts /\
  MEM (FunctionDecl vis mut nr raw fn args ds rt b) ts ==>
  EVERY (expr_writes_ok ^guard) ds /\ stmts_writes_ok ^guard b /\
  EVERY ^reached (function_int_calls ds b)
Proof
  strip_tac >>
  `function_live layouts addr mods ^live (src,fn)` by simp[function_live_def] >>
  drule_all checked_live_decl_constant_writes >> strip_tac >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  first_x_assum irule >> qexists_tac `(src,fn)` >> simp[] >>
  irule contract_call_edges_function >> metis_tac[ALOOKUP_MEM]
QED

Theorem checked_deploy_constructor_guards:
  check_contract T layouts addr mods = SOME art /\
  ALOOKUP mods NONE = SOME main /\
  lookup_function NONE entry Deploy main = SOME (em,en,ea,eds,ert,eb) /\
  declared_constant mods sid nm /\
  (!src ts fn vis mut nr raw args ds ret body.
     MEM (src,ts) mods /\ module_allocated layouts addr src ts /\
     MEM (FunctionDecl vis mut nr raw fn args ds ret body) ts ==>
     MEM (src,fn) ^live) /\ ^edges_closed ==>
  (!src fn ts mut nr args ds rt b.
     MEM (src,fn) ^live /\ ALOOKUP mods src = SOME ts /\
     lookup_callable_function T fn ts = SOME (mut,nr,args,ds,rt,b) ==>
     EVERY (expr_writes_ok ^guard) ds /\ stmts_writes_ok ^guard b /\
     EVERY ^reached (function_int_calls ds b)) /\
  (!n. EVERY (expr_writes_ok ^guard) (DROP n eds) /\
       EVERY ^reached (int_calls_exprs (DROP n eds))) /\
  stmts_writes_ok ^guard eb /\ EVERY ^reached (int_calls_stmts eb)
Proof
  strip_tac >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule lookup_callable_function_T_SOME_cases >> strip_tac
      >- (drule_all live_decl_guards >> simp[])
      >- gvs[stmt_writes_ok_def, function_int_calls_def,
             int_calls_expr_def, int_calls_stmt_def] >>
      drule_all live_decl_guards >> simp[]) >>
  `EVERY (expr_writes_ok ^guard) eds /\ stmts_writes_ok ^guard eb /\
   EVERY ^reached (function_int_calls eds eb)` by
    (drule lookup_function_Deploy_SOME_cases >> strip_tac
     >- gvs[stmt_writes_ok_def, function_int_calls_def,
            int_calls_expr_def, int_calls_stmt_def] >>
     `module_allocated layouts addr NONE main` by
       (drule_all check_contract_main_module_allocated >> simp[]) >>
     `MEM (NONE,entry) ^live` by metis_tac[ALOOKUP_MEM] >>
     drule_all live_decl_guards >> simp[]) >>
  gvs[function_int_calls_def, EVERY_APPEND,
      int_calls_exprs_FLAT_MAP, EVERY_FLAT, EVERY_MAP] >>
  simp[EVERY_DROP]
QED

(* Checked constructor and callable syntax cannot mutate Constant cells. *)
Theory vyperCheckedConstantWrites
Ancestors
  list pair option finite_map alist vyperAST vyperTypeSystem
  vyperTypeContract vyperTypeContractStaticMaps vyperTypeContractContext
  vyperTypeConstantCells vyperCheckedRuntimeWriteSafety vyperRuntimeWriteSafety
  vyperInterpreter vyperTypeCallStackSoundness

Theorem checked_constant_write_roots[local]:
  check_contract mode layouts addr mods = SOME art /\
  ALOOKUP mods src = SOME ts ==>
  (!sid id ty. FLOOKUP art.cta_bare_global_assignable (sid,id) = SOME ty ==>
    sid = src ==> ~(?vis e typ slot. MEM (VariableDecl vis (Constant e) id typ slot) ts)) /\
  (!sid id vt. FLOOKUP art.cta_toplevel_vtypes (sid,id) = SOME vt /\
    FLOOKUP art.cta_bare_globals (sid,id) = NONE ==>
    sid = src ==> ~(?vis e typ slot. MEM (VariableDecl vis (Constant e) id typ slot) ts))
Proof
  rpt gen_tac >> strip_tac >>
  drule check_contract_artifact_fields >> strip_tac >>
  drule check_contract_runtime_namespaces >> strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))` by
    (irule contract_namespaces_ok_module_toplevel_vtype_keys >>
     goal_assum (drule_at Any) >> metis_tac[ALOOKUP_MEM]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> strip_tac >> gvs[] >>
      drule_all build_contract_type_artifact_bare_global_assignable_sound >>
      strip_tac >> gvs[] >> strip_tac >>
      metis_tac[module_immutable_constant_names_distinct]) >>
  rpt gen_tac >> strip_tac >> strip_tac >> fs[] >> rpt strip_tac >>
  drule check_contract_nonsig_maps >> strip_tac >>
  `FLOOKUP (build_contract_type_artifact F mods).cta_bare_globals (src,id) = SOME typ` by
    (irule build_contract_type_artifact_bare_globals_complete >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  gvs[]
QED

Theorem checked_function_constant_writes[local]:
  !layouts addr mods art src ts vis mut nr raw fn args dflts ret body.
  check_contract T layouts addr mods = SOME art /\
  ALOOKUP mods src = SOME ts /\
  module_allocated layouts addr src ts /\
  MEM (FunctionDecl vis mut nr raw fn args dflts ret body) ts ==>
  EVERY (expr_writes_ok (runtime_write_root
    (\sid id. sid = src ==> ~(?vis e ty slot.
      MEM (VariableDecl vis (Constant e) id ty slot) ts)))) dflts /\
  stmts_writes_ok (runtime_write_root
    (\sid id. sid = src ==> ~(?vis e ty slot.
      MEM (VariableDecl vis (Constant e) id ty slot) ts))) body
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `MEM (FunctionDecl _ _ _ _ _ _ _ _ bod) ts` >>
  drule_all checked_constant_write_roots >> strip_tac >>
  `check_function_body layouts addr mods art src vis mut nr args dflts ret bod` suffices_by
    (strip_tac >> drule check_function_body_write_roots >>
     disch_then irule >> simp[] >> metis_tac[]) >>
  drule_all module_allocated_function_live >> strip_tac >>
  qpat_x_assum `check_contract _ _ _ _ = _` mp_tac >>
  simp[check_contract_def] >> strip_tac >> gvs[] >>
  qpat_x_assum `EVERY _ mods` mp_tac >> simp[EVERY_MEM] >>
  disch_then (qspec_then `(src,ts)` mp_tac) >>
  impl_tac >- metis_tac[ALOOKUP_MEM] >>
  simp[check_module_def, EVERY_MEM] >> strip_tac >>
  qpat_x_assum `!x. MEM x ts ==> check_toplevel_body _ _ _ _ _ _ _ x`
    (qspec_then `FunctionDecl vis mut nr raw fn args dflts ret bod` mp_tac) >>
  simp[check_toplevel_body_def, check_function_body_in_mode_def, function_live_def]
QED

Theorem checked_singleton_constant_callable_writes:
  check_contract T layouts addr [(NONE,tops)] = SOME art ==>
  !deploy sid fn ts mut nr args dflts ret body.
    ALOOKUP [(NONE,tops)] sid = SOME ts /\
    lookup_callable_function deploy fn ts = SOME (mut,nr,args,dflts,ret,body) ==>
    EVERY (expr_writes_ok (runtime_write_root
      (\sid id. sid = NONE ==> ~(?vis e ty slot.
        MEM (VariableDecl vis (Constant e) id ty slot) tops)))) dflts /\
    stmts_writes_ok (runtime_write_root
      (\sid id. sid = NONE ==> ~(?vis e ty slot.
        MEM (VariableDecl vis (Constant e) id ty slot) tops))) body
Proof
  strip_tac >> rpt gen_tac >>
  Cases_on `sid` >> simp[] >> strip_tac >> gvs[] >>
  rename1 `lookup_callable_function deploy fn tops = SOME (mut,nr,args,dflts,ret,bod)` >>
  Cases_on `dflts = [] /\ bod = []` >- gvs[stmt_writes_ok_def] >>
  `?vis fm nr raw args ret.
     MEM (FunctionDecl vis fm nr raw fn args dflts ret bod) tops` by
    metis_tac[lookup_callable_function_SOME_decompose] >>
  irule (SRULE [] checked_function_constant_writes) >>
  conj_tac >- metis_tac[] >>
  goal_assum (drule_at Any) >> simp[] >>
  irule check_contract_main_module_allocated >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem checked_singleton_constructor_constant_writes:
  !layouts addr tops art fn mut nr args dflts ret body.
  check_contract T layouts addr [(NONE,tops)] = SOME art /\
  lookup_function NONE fn Deploy tops = SOME (mut,nr,args,dflts,ret,body) ==>
  EVERY (expr_writes_ok (runtime_write_root
    (\sid id. sid = NONE ==> ~(?vis e ty slot.
      MEM (VariableDecl vis (Constant e) id ty slot) tops)))) dflts /\
  stmts_writes_ok (runtime_write_root
    (\sid id. sid = NONE ==> ~(?vis e ty slot.
      MEM (VariableDecl vis (Constant e) id ty slot) tops))) body
Proof
  rpt gen_tac >> strip_tac >> drule lookup_function_Deploy_SOME_cases >> strip_tac
  >- gvs[stmt_writes_ok_def] >> simp[] >>
  irule (SRULE [] checked_function_constant_writes) >>
  conj_tac >- metis_tac[] >>
  qexistsl [`addr`,`art`,`layouts`,`[(NONE,tops)]`] >> simp[] >>
  irule check_contract_main_module_allocated >>
  goal_assum (drule_at Any) >> simp[]
QED

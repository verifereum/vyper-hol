(* Constant-free modules do not evaluate initialisers.  Keep the merges:
   merging an empty map need not be the identity on an abstract machine. *)
Theory selfCodeFreeConstants
Ancestors
  vyperInterpreter supportedProgram supportedDecls list

Theorem constants_env_trace_no_constants:
  !ts. (!vis e id ty slot.
          ~MEM (VariableDecl vis (Constant e) id ty slot) ts) ==>
    constants_env_trace cx am addr sid ts acc = (SOME acc, [])
Proof
  Induct >- simp[constants_env_trace_def] >>
  Cases_on `h` >> simp[constants_env_trace_def] >>
  rename1 `VariableDecl vis mut id ty slot` >>
  Cases_on `mut` >> simp[constants_env_trace_def] >> metis_tac[]
QED

Theorem constants_env_no_constants:
  !ts. (!vis e id ty slot.
          ~MEM (VariableDecl vis (Constant e) id ty slot) ts) ==>
    constants_env cx am addr sid ts acc = SOME acc
Proof
  simp[constants_env_def, constants_env_trace_no_constants]
QED

Theorem supported_program_no_constants:
  supported_program tops ==>
  !vis e id ty slot. ~MEM (VariableDecl vis (Constant e) id ty slot) tops
Proof
  simp[supported_program_def, supported_declaration_headers_def,
       EVERY_MEM] >> metis_tac[supported_constants_rejected]
QED

Theorem evaluate_module_constants_trace_no_constants_cong:
  !mods am. (!sid ts vis e id ty slot.
    MEM (sid,ts) mods ==>
    ~MEM (VariableDecl vis (Constant e) id ty slot) ts) ==>
    evaluate_module_constants_trace cx1 am addr mods =
    evaluate_module_constants_trace cx2 am addr mods
Proof
  Induct >- simp[evaluate_module_constants_trace_def] >>
  Cases_on `h` >> rpt strip_tac >>
  rename1 `(sid,ts)` >>
  `!vis e id ty slot.
     ~MEM (VariableDecl vis (Constant e) id ty slot) ts`
    by metis_tac[MEM] >>
  simp[evaluate_module_constants_trace_def, constants_env_trace_no_constants] >>
  AP_TERM_TAC >> first_x_assum irule >> metis_tac[MEM]
QED

Theorem evaluate_module_constants_no_constants_cong:
  !mods am. (!sid ts vis e id ty slot.
    MEM (sid,ts) mods ==>
    ~MEM (VariableDecl vis (Constant e) id ty slot) ts) ==>
    evaluate_module_constants cx1 am addr mods =
    evaluate_module_constants cx2 am addr mods
Proof
  rpt strip_tac >>
  simp[evaluate_module_constants_def] >> AP_TERM_TAC >>
  irule evaluate_module_constants_trace_no_constants_cong >> first_assum ACCEPT_TAC
QED

Theorem evaluate_all_constants_no_constants_cong:
  (!sid ts vis e id ty slot.
    MEM (sid,ts) mods ==>
    ~MEM (VariableDecl vis (Constant e) id ty slot) ts) ==>
  evaluate_all_constants cx1 am addr mods =
  evaluate_all_constants cx2 am addr mods
Proof
  strip_tac >> simp[evaluate_all_constants_def] >>
  irule evaluate_module_constants_no_constants_cong >>
  metis_tac[MEM_constants_order]
QED

Theorem supported_program_constants_context_cong:
  supported_program tops ==>
  evaluate_all_constants cx1 am addr [(NONE,tops)] =
  evaluate_all_constants cx2 am addr [(NONE,tops)]
Proof
  strip_tac >> irule evaluate_all_constants_no_constants_cong >>
  simp[] >> metis_tac[supported_program_no_constants]
QED

Theorem supported_program_constants_trace_context_cong:
  supported_program tops ==>
  evaluate_module_constants_trace cx1 am addr (constants_order [(NONE,tops)]) =
  evaluate_module_constants_trace cx2 am addr (constants_order [(NONE,tops)])
Proof
  strip_tac >> irule evaluate_module_constants_trace_no_constants_cong >>
  metis_tac[MEM_constants_order, MEM, supported_program_no_constants,
            pairTheory.PAIR_EQ, optionTheory.SOME_11]
QED

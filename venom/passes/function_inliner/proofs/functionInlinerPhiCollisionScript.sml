(* Frozen-contract probe: a dangling PHI predecessor shadows the return label. *)
Theory functionInlinerPhiCollision
Ancestors
  functionInlinerCallWitness functionInlinerContract functionInlinerDefs
  unitShapeDefs callLayoutDefs venomInst venomWf venomState venomExecSemantics
  o1PassContract passSimulationDefs venomExecProofs ptrDiscipline
  fcgDefs finite_map list relation words
Libs wordsLib

Definition phi_collision_main_def:
  phi_collision_main = mk_raw_function "main"
    [<| bb_label := "main"; bb_instructions :=
       [instruction 0 ASSIGN [Lit 0w] ["wrong"];
        instruction 1 ASSIGN [Lit 1w] ["right"];
        instruction 2 INVOKE [Label "add1"; Lit 41w] ["answer"];
        instruction 3 JMP [Label "join"] []] |>;
     <| bb_label := "join"; bb_instructions :=
       [instruction 4 PHI
          [Label (return_block_label (inline_prefix 0) 0); Var "wrong";
           Label "main"; Var "right"] ["choice"];
        instruction 5 JNZ [Var "choice"; Label "good"; Label "bad"] []] |>;
     <| bb_label := "good"; bb_instructions := [instruction 6 STOP [] []] |>;
     <| bb_label := "bad"; bb_instructions :=
        [instruction 7 REVERT [Lit 0w; Lit 0w] []] |>]
End

Definition phi_collision_ctx_def:
  phi_collision_ctx = mk_venom_context
    [phi_collision_main; inliner_witness_callee] (SOME "main")
End

Theorem phi_collision_retpc[local]:
  !x. ~retpc_var phi_collision_main x
Proof
  simp[retpc_var_def] >> irule copy_phi_var_no_seed >>
  simp[phi_collision_main_def, mk_raw_function_def,
       fn_insts_def, fn_insts_blocks_def] >> rpt strip_tac >> gvs[]
QED

Theorem phi_collision_opaque[local]:
  opaque_use_ok phi_collision_main /\ retpc_shape_ok phi_collision_main
Proof
  `!x. ~retpc_var (reachable_fn phi_collision_main) x` by
    metis_tac[reachable_retpc_var, phi_collision_retpc] >>
  simp[opaque_use_ok_def, retpc_shape_ok_def, phi_collision_retpc,
       retpc_use_ok_def] >>
  `!i. MEM i (fn_insts phi_collision_main) ==>
       i.inst_opcode <> RET /\ i.inst_opcode <> RETFMP /\ i.inst_opcode <> DRET` by
    (EVAL_TAC >> rpt strip_tac >> gvs[]) >>
  gen_tac >> Cases_on `inst.inst_opcode = PHI` >> simp[] >>
  metis_tac[reachable_fn_insts_nonphi]
QED

Theorem phi_collision_callees[local]:
  !name. fcg_get_callees (fcg_analyze phi_collision_ctx) name =
    if name = "main" then ["add1"] else []
Proof
  gen_tac >> EVAL_TAC >> rw[]
QED

Theorem phi_collision_input_ok:
  inliner_input_ok phi_collision_ctx
Proof
  mp_tac inliner_witness_input_ok >>
  simp[inliner_input_ok_def, inliner_witness_context_def,
       mk_venom_context_def] >> strip_tac >>
  simp[inliner_input_ok_def, phi_collision_callees,
       phi_collision_ctx_def, mk_venom_context_def, phi_collision_opaque,
       GSYM RIGHT_EXISTS_AND_THM] >>
  qexists_tac `\name. if name = "main" then 1n else 0` >>
  EVAL_TAC >> rw[] >> EVAL_TAC >> gvs[fn_insts_blocks_def]
QED

Theorem phi_collision_source_halts:
  case run_context 20 phi_collision_ctx (init_venom_state "main") of
    Halt s => T | _ => F
Proof
  EVAL_TAC
QED

Theorem phi_collision_target_aborts:
  case run_context 20 (function_inliner_ctx 0 phi_collision_ctx)
       (init_venom_state "main") of
    Abort a s => T | _ => F
Proof
  EVAL_TAC
QED

Theorem phi_collision_target_never_halts:
  !fuel u. run_context fuel (function_inliner_ctx 0 phi_collision_ctx)
             (init_venom_state "main") <> Halt u
Proof
  `!n m C s r. run_context n C s = r /\ (!e. r <> Error e) /\ n <= m ==>
      run_context m C s = r` by
    (simp[run_context_def, run_function_def] >> rpt gen_tac >>
     Cases_on `C.ctx_entry` >> simp[] >>
     Cases_on `lookup_function x C.ctx_functions` >> simp[] >>
     Cases_on `fn_entry_label x'` >> simp[] >>
     metis_tac[cj 3 venomExecProofsTheory.fuel_mono]) >>
  mp_tac phi_collision_target_aborts >>
  Cases_on `run_context 20 (function_inliner_ctx 0 phi_collision_ctx)
                 (init_venom_state "main")` >> simp[] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  `run_context (fuel + 20) (function_inliner_ctx 0 phi_collision_ctx)
       (init_venom_state "main") = Halt u` by
    (first_assum irule >> simp[] >> qexists_tac `fuel` >> simp[]) >>
  `run_context (fuel + 20) (function_inliner_ctx 0 phi_collision_ctx)
       (init_venom_state "main") = Abort a v` by
    (first_assum irule >> simp[] >> qexists_tac `20` >> simp[]) >>
  qpat_x_assum `run_context (fuel + 20) _ _ = Halt u` mp_tac >> simp[]
QED

Theorem phi_collision_not_ctx_sim:
  !D. ~ctx_sim D phi_collision_ctx (function_inliner_ctx 0 phi_collision_ctx)
          (init_venom_state "main") (init_venom_state "main")
Proof
  gen_tac >> simp[ctx_sim_def] >> qexists_tac `20` >>
  mp_tac phi_collision_source_halts >>
  Cases_on `run_context 20 phi_collision_ctx (init_venom_state "main")` >>
  simp[terminates_def] >> rpt strip_tac >>
  Cases_on `run_context fuel' (function_inliner_ctx 0 phi_collision_ctx)
                 (init_venom_state "main")` >>
  gvs[dead_result_rel_def, phi_collision_target_never_halts]
QED

Theorem phi_collision_frozen_counterexample:
  !D. inliner_input_ok phi_collision_ctx /\
      (init_venom_state "main").vs_labels = FEMPTY /\
      ~(init_venom_state "main").vs_halted /\
      ~ctx_sim D phi_collision_ctx (function_inliner_ctx 0 phi_collision_ctx)
        (init_venom_state "main") (init_venom_state "main")
Proof
  simp[phi_collision_input_ok, phi_collision_not_ctx_sim] >> EVAL_TAC
QED

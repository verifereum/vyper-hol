Theory functionInlinerPtrWitness
Ancestors
  functionInlinerContract functionInlinerPtrCheck functionInlinerShapeCheck
  functionInlinerDefs
  ptrOkCheck ptrDiscipline
  pointerConfinedDefs unitShapeDefs memLocDefs vyperCompiler venomExecSemantics
  venomInst venomWf venomState defsReachCheck list pred_set
Libs
  finite_mapLib wordsLib

Definition witness_block_def:
  witness_block label insts =
    <| bb_label := label; bb_instructions := insts |>
End

(* The only store in the positive variant still has one root after binding
   the arguments. The PHI remains in both variants. *)
Definition witness_join_helper_def:
  witness_join_helper access =
    mk_raw_function "helper"
      [witness_block "helper"
         [mk_inst 10 PARAM [Lit 0w] ["x"];
          mk_inst 11 PARAM [Lit 1w] ["y"];
          mk_inst 12 RETPC_PARAM [Lit 2w] ["pc"];
          mk_inst 13 CALLDATASIZE [] ["choose"];
          mk_inst 14 JNZ [Var "choose"; Label "left"; Label "right"] []];
       witness_block "left" [mk_inst 15 JMP [Label "join"] []];
       witness_block "right" [mk_inst 16 JMP [Label "join"] []];
       witness_block "join"
         [mk_inst 17 PHI [Label "left"; Var "x"; Label "right"; Var "y"]
            ["joined"];
          access;
          mk_inst 19 RET [Var "pc"] []]]
End

Definition witness_join_ctx_def:
  witness_join_ctx arg access =
    mk_venom_context
      [mk_raw_function "caller"
         [witness_block "caller"
            [mk_inst 0 PARAM [Lit 0w] ["other"];
             mk_inst 1 ALLOCA [Lit 32w] ["local"];
             mk_inst 2 INVOKE [Label "helper"; arg; Var "other"] [];
             mk_inst 3 STOP [] []]];
       witness_join_helper access]
      (SOME "caller")
End

Definition witness_param_list_def:
  witness_param_list name =
    if name = "caller" then [0] else if name = "helper" then [0;1] else []
End

Definition witness_static_ptr_check_def:
  witness_static_ptr_check PL C =
    EVERY (fn_ptr_ok_check PL) C.ctx_functions
End

Theorem witness_static_ptr_check_sound[local]:
  witness_static_ptr_check PL C ==>
  EVERY (fn_ptr_ok (\nm. set (PL nm))) C.ctx_functions
Proof
  simp[witness_static_ptr_check_def, EVERY_MEM] >>
  metis_tac[fn_ptr_ok_check_sound]
QED

Theorem inliner_single_root_store_witness:
  access = mk_inst 18 MSTORE [Var "x"; Lit 7w] [] /\
  C = witness_join_ctx (Var "local") access /\
  out = function_inliner_ctx 0 C ==>
  inline_ptr_ok (\nm. set (ctx_ptr_param_list C nm)) (ctx_write_param_set C) C /\
  EVERY (fn_ptr_ok (\nm. set (ctx_ptr_param_list C nm))) C.ctx_functions /\
  inline_ptr_ok (\nm. set (ctx_ptr_param_list out nm)) (ctx_write_param_set out)
    out /\
  EVERY (fn_ptr_ok (\nm. set (ctx_ptr_param_list out nm))) out.ctx_functions
Proof
  rpt gen_tac >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  rpt conj_tac >>
  TRY (irule inline_ptr_ok_check_sound >> EVAL_TAC) >>
  irule witness_static_ptr_check_sound >> EVAL_TAC
QED

Theorem inliner_pointer_argument_witness:
  access = mk_inst 18 MLOAD [Var "joined"] ["value"] /\
  C = witness_join_ctx (Var "local") access /\
  out = function_inliner_ctx 0 C ==>
  inline_ptr_ok (\nm. set (ctx_ptr_param_list C nm)) (ctx_write_param_set C) C /\
  EVERY (fn_ptr_ok (\nm. set (ctx_ptr_param_list C nm))) C.ctx_functions /\
  inline_ptr_ok (\nm. set (ctx_ptr_param_list out nm)) (ctx_write_param_set out)
    out /\
  EVERY (fn_ptr_ok (\nm. set (ctx_ptr_param_list out nm))) out.ctx_functions
Proof
  rpt gen_tac >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  rpt conj_tac >>
  TRY (irule inline_ptr_ok_check_sound >> EVAL_TAC) >>
  irule witness_static_ptr_check_sound >> EVAL_TAC
QED

Definition witness_join_out_def:
  witness_join_out arg access =
    HD (function_inliner_ctx 0 (witness_join_ctx arg access)).ctx_functions
End

(* Restates the second conjunct of ptrOkCheck's local ptr_roots_lists;
   it goes away when that theory exports it. *)
Theorem witness_alloca_roots_list:
  alloca_roots fn = set (opcode_root_list ALLOCA fn)
Proof
  simp[EXTENSION, alloca_roots_def, opcode_root_list_def, MEM_FLAT, MEM_MAP,
       PULL_EXISTS] >>
  gen_tac >> eq_tac >> rpt strip_tac >> rename1 `MEM inst (fn_insts fn)`
  >- (qexists_tac `inst` >> simp[]) >>
  Cases_on `inst.inst_opcode = ALLOCA` >> Cases_on `inst_output inst` >>
  gvs[] >> qexists_tac `inst` >> simp[]
QED

Theorem witness_closure_member:
  OPTION_MAP (MEM v) (pv_closure fn roots) = SOME ok ==>
  (v IN pointer_derived_vars fn (set roots) <=> ok)
Proof
  Cases_on `pv_closure fn roots` >> simp[] >>
  imp_res_tac pv_closure_set >> simp[]
QED

Theorem witness_mixed_write_refutes_fn_ptr_ok:
  MEM inst (fn_insts fn) /\ mem_write_ops inst = SOME ops /\
  ops.iao_ofst = Var v /\
  v IN pointer_derived_vars fn (alloca_roots fn) /\
  v IN pointer_derived_vars fn (ptr_roots P fn DIFF alloca_roots fn) ==>
  ~fn_ptr_ok P fn
Proof
  rw[fn_ptr_ok_def] >> metis_tac[]
QED

Theorem inliner_mixed_root_store_rejected:
  access = mk_inst 18 MSTORE [Var "joined"; Lit 7w] [] /\
  C = witness_join_ctx (Var "local") access /\
  fn = witness_join_out (Var "local") access ==>
  EVERY (fn_ptr_ok (\nm. set (witness_param_list nm))) C.ctx_functions /\
  ~inline_ptr_ok_check C /\
  ~fn_ptr_ok (\nm. set (witness_param_list nm)) fn
Proof
  rpt gen_tac >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  conj_tac >- (irule witness_static_ptr_check_sound >> EVAL_TAC) >>
  conj_tac >- EVAL_TAC >>
  qabbrev_tac `fn = witness_join_out (Var "local")
                         (mk_inst 18 MSTORE [Var "joined"; Lit 7w] [])` >>
  `alloca_roots fn = set ["local"]` by
    (simp_tac std_ss [witness_alloca_roots_list, Abbr `fn`] >> EVAL_TAC) >>
  `ptr_roots (\nm. set (witness_param_list nm)) fn = set ["local";"other"]` by
    (simp_tac std_ss [GSYM inline_root_list_set, Abbr `fn`] >> EVAL_TAC) >>
  `ptr_roots (\nm. set (witness_param_list nm)) fn DIFF alloca_roots fn =
    set ["other"]` by fs[] >>
  `OPTION_MAP (MEM "inl0_joined") (pv_closure fn ["local"]) = SOME T /\
   OPTION_MAP (MEM "inl0_joined") (pv_closure fn ["other"]) = SOME T` by
    (unabbrev_all_tac >> EVAL_TAC) >>
  `"inl0_joined" IN pointer_derived_vars fn (set ["local"]) /\
   "inl0_joined" IN pointer_derived_vars fn (set ["other"])` by
    metis_tac[witness_closure_member] >>
  irule witness_mixed_write_refutes_fn_ptr_ok >>
  qexistsl_tac [`EL 12 (fn_insts fn)`, `THE (mem_write_ops (EL 12 (fn_insts fn)))`,
                `"inl0_joined"`] >>
  asm_simp_tac std_ss [] >> unabbrev_all_tac >> EVAL_TAC
QED

Theorem witness_mixed_phi_refutes_fn_ptr_ok[local]:
  MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
  inst.inst_opcode = PHI /\
  MEM (Var x) inst.inst_operands /\ MEM (Var y) inst.inst_operands /\
  x IN pointer_derived_vars fn (ptr_roots P fn) /\
  y NOTIN pointer_derived_vars fn (ptr_roots P fn) ==>
  ~fn_ptr_ok P fn
Proof
  rw[fn_ptr_ok_def, phi_pv_all_var_def] >> metis_tac[]
QED

Theorem inliner_literal_pointer_argument_rejected:
  access = mk_inst 18 MLOAD [Var "joined"] ["value"] /\
  C = witness_join_ctx (Lit 0w) access /\
  fn = witness_join_out (Lit 0w) access ==>
  EVERY (fn_ptr_ok (\nm. set (witness_param_list nm))) C.ctx_functions /\
  ~inline_ptr_ok_check C /\
  ~fn_ptr_ok (\nm. set (witness_param_list nm)) fn
Proof
  rpt gen_tac >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  conj_tac >- (irule witness_static_ptr_check_sound >> EVAL_TAC) >>
  conj_tac >- EVAL_TAC >>
  qabbrev_tac `fn = witness_join_out (Lit 0w)
                         (mk_inst 18 MLOAD [Var "joined"] ["value"])` >>
  `ptr_roots (\nm. set (witness_param_list nm)) fn = set ["local";"other"]` by
    (simp_tac std_ss [GSYM inline_root_list_set, Abbr `fn`] >> EVAL_TAC) >>
  `OPTION_MAP (MEM "inl0_y") (pv_closure fn ["local";"other"]) = SOME T /\
   OPTION_MAP (MEM "inl0_x") (pv_closure fn ["local";"other"]) = SOME F` by
    (unabbrev_all_tac >> EVAL_TAC) >>
  `"inl0_y" IN pointer_derived_vars fn (set ["local";"other"]) /\
   "inl0_x" NOTIN pointer_derived_vars fn (set ["local";"other"])` by
    metis_tac[witness_closure_member] >>
  irule witness_mixed_phi_refutes_fn_ptr_ok >>
  qexistsl_tac [`LAST fn.fn_blocks`, `HD (LAST fn.fn_blocks).bb_instructions`,
                `"inl0_y"`, `"inl0_x"`] >>
  asm_simp_tac std_ss [] >> unabbrev_all_tac >> EVAL_TAC
QED

Definition witness_alloc_ctx_def:
  witness_alloc_ctx returns =
    mk_venom_context
      [mk_raw_function "entry"
         [witness_block "entry"
            [mk_inst 0 ALLOCA [Lit 32w] ["dst"];
             mk_inst 1 ASSIGN [Lit 2w] ["left"];
             mk_inst 2 JMP [Label "loop"] []];
          witness_block "loop"
            [mk_inst 3 INVOKE [Label "allocate"; Var "dst"] [];
             mk_inst 4 SUB [Var "left"; Lit 1w] ["left"];
             mk_inst 5 JNZ [Var "left"; Label "loop"; Label "done"] []];
          witness_block "done" [mk_inst 6 STOP [] []]];
       mk_raw_function "allocate"
         [witness_block "allocate"
            [mk_inst 10 PARAM [Lit 0w] ["output"];
             mk_inst 11 RETPC_PARAM [Lit 1w] ["pc"];
             mk_inst 12 ALLOCA [Lit 32w] ["local"];
             mk_inst 13 DALLOCA [Lit 32w] ["dynamic"];
             mk_inst 14 MSTORE [Var "local"; Lit 1w] [];
             mk_inst 15 MSTORE [Var "dynamic"; Lit 2w] [];
             mk_inst 16 MSTORE [Var "output"; Lit 3w] [];
             if returns then mk_inst 17 RET [Var "pc"] []
             else mk_inst 17 REVERT [Lit 0w; Lit 0w] []]]]
      (SOME "entry")
End

Theorem inliner_dalloca_input_witness:
  C = witness_alloc_ctx T /\
  s = (init_venom_state "entry") with
    <| vs_fmp := 256w; vs_initial_fmp := 256w; vs_call_entry_fmp := 256w |> ==>
  lowering_context_ok C /\ inliner_input_guard C /\ inline_ptr_ok_check C /\
  ctx_has_dalloca C /\
  LENGTH (FILTER (\i. i.inst_opcode = DALLOCA)
    (FLAT (MAP fn_insts (function_inliner_ctx 0 C).ctx_functions))) = 1 /\
  (case run_context 16 C s of
     Halt s' => s'.vs_fmp = 256w /\ s'.vs_alloca_next = 32
   | _ => F) /\
  (case run_context 16 (function_inliner_ctx 0 C) s of
     Halt s' => s'.vs_fmp = 320w /\ s'.vs_alloca_next = 64
   | _ => F)
Proof
  rpt gen_tac >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  conj_tac >- EVAL_TAC >> conj_tac
  >- (rewrite_tac[inliner_input_guard_def] >> conj_tac
      >- (match_mp_tac rfp_self_contained_check_guard >> EVAL_TAC) >>
      EVAL_TAC) >>
  EVAL_TAC
QED

Theorem witness_reachable_ptr_sound[local]:
  wf_function fn /\ EVERY (\i. i.inst_opcode <> PHI) (fn_insts fn) /\
  fn_ptr_ok_check (K []) fn /\
  fn_ptr_ok_check (K []) (fn_reachable_blocks fn) ==>
  fn_ptr_ok (\nm. {}) fn /\ fn_ptr_ok (\nm. {}) (reachable_fn fn)
Proof
  strip_tac >>
  `reachable_fn fn = fn_reachable_blocks fn` by
    metis_tac[fn_reachable_blocks_reachable_fn] >>
  qpat_x_assum `fn_ptr_ok_check (K []) fn`
    (mp_tac o MATCH_MP fn_ptr_ok_check_sound) >>
  qpat_x_assum `fn_ptr_ok_check (K []) (fn_reachable_blocks fn)`
    (mp_tac o MATCH_MP fn_ptr_ok_check_sound) >>
  simp[]
QED

Theorem inliner_reverting_callee_witness:
  C = witness_alloc_ctx F /\
  C' = function_inliner_ctx 0 C ==>
  lowering_context_ok C /\ inline_ptr_ok_check C /\
  EVERY (\fn. EVERY (\i. i.inst_opcode <> RET) (fn_insts fn))
    C.ctx_functions /\
  EVERY (\fn. fn_ptr_ok (\nm. {}) fn /\ fn_ptr_ok (\nm. {}) (reachable_fn fn) /\
                fn_defs_reach_uses fn /\
                LENGTH (fn_reachable_blocks fn).fn_blocks < LENGTH fn.fn_blocks)
    C'.ctx_functions
Proof
  rpt gen_tac >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  `EVERY (\fn. (wf_function fn /\ EVERY (\i. i.inst_opcode <> PHI) (fn_insts fn) /\
                fn_ptr_ok_check (K []) fn /\
                fn_ptr_ok_check (K []) (fn_reachable_blocks fn)) /\
               fn_defs_reach_uses_check fn /\
               LENGTH (fn_reachable_blocks fn).fn_blocks < LENGTH fn.fn_blocks)
      (function_inliner_ctx 0 (witness_alloc_ctx F)).ctx_functions` by EVAL_TAC >>
  simp_tac std_ss [EVERY_MEM] >> qx_gen_tac `fn` >> strip_tac >>
  qpat_x_assum `EVERY _ _` (mp_tac o ONCE_REWRITE_RULE[EVERY_MEM]) >>
  disch_then (drule_then (strip_assume_tac o BETA_RULE)) >>
  `fn_ptr_ok (\nm. {}) fn /\ fn_ptr_ok (\nm. {}) (reachable_fn fn)` by
    (irule witness_reachable_ptr_sound >> simp[]) >>
  simp[] >> metis_tac[fn_defs_reach_uses_check_sound]
QED

(* The CFG admits the bypass even though the condition is always true.
   The bypass uses "alias" without a definition once the continuation dies. *)
Definition witness_reverting_comparison_ctx_def:
  witness_reverting_comparison_ctx =
    mk_venom_context
      [mk_raw_function "entry"
         [witness_block "entry"
            [mk_inst 0 ALLOCA [Lit 32w] ["ptr"];
             mk_inst 1 JNZ [Lit 1w; Label "site"; Label "done"] []];
          witness_block "site"
            [mk_inst 2 INVOKE [Label "reverter"] [];
             mk_inst 3 ASSIGN [Var "ptr"] ["alias"];
             mk_inst 4 JMP [Label "done"] []];
          witness_block "done"
            [mk_inst 5 EQ [Var "ptr"; Var "alias"] ["same"];
             mk_inst 6 STOP [] []]];
       mk_raw_function "reverter"
         [witness_block "reverter"
            [mk_inst 10 RETPC_PARAM [Lit 0w] ["pc"];
             mk_inst 11 REVERT [Lit 0w; Lit 0w] []]]]
      (SOME "entry")
End

Theorem inliner_revert_pruning_comparison_witness:
  C = witness_reverting_comparison_ctx /\
  fn = HD (function_inliner_ctx 0 C).ctx_functions ==>
  ptr_ok_check C /\ inline_ptr_ok_check C /\
  ~fn_defs_reach_uses_check (HD C.ctx_functions) /\
  fn_ptr_ok_check (K []) fn /\
  ~fn_ptr_ok_check (K []) (fn_reachable_blocks fn)
Proof
  rpt gen_tac >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  EVAL_TAC
QED

Theorem witness_mixed_eq_refutes_fn_ptr_ok:
  MEM inst (fn_insts fn) /\ inst.inst_opcode = EQ /\
  inst.inst_operands = [Var x; Var y] /\
  x IN fn_pv P fn /\ y NOTIN fn_pv P fn ==>
  ~fn_ptr_ok P fn
Proof
  strip_tac >> CCONTR_TAC >> fs[fn_ptr_ok_def] >>
  qpat_x_assum `!i. MEM i _ ==> _` (drule_then strip_assume_tac) >>
  qpat_x_assum `ptr_use_ok _ _ _` mp_tac >>
  simp[ptr_use_ok_def, is_pointer_preserving_op_def, mem_read_ops_def,
       mem_write_ops_def] >>
  metis_tac[]
QED

Theorem inliner_revert_pruning_breaks_ptr_ok:
  C = function_inliner_ctx 0 witness_reverting_comparison_ctx ==>
  ~fn_ptr_ok (\nm. set ((K []) nm)) (reachable_fn (HD C.ctx_functions))
Proof
  rpt gen_tac >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  qabbrev_tac `out = HD (function_inliner_ctx 0
                             witness_reverting_comparison_ctx).ctx_functions` >>
  `wf_function out /\ EVERY (\i. i.inst_opcode <> PHI) (fn_insts out)` by
    (unabbrev_all_tac >> EVAL_TAC) >>
  `reachable_fn out = fn_reachable_blocks out` by
    metis_tac[fn_reachable_blocks_reachable_fn] >>
  asm_simp_tac std_ss [] >>
  qabbrev_tac `fn = fn_reachable_blocks out` >>
  `ptr_roots (\nm. set ((K []) nm)) fn = set ["ptr"]` by
    (simp_tac std_ss [GSYM inline_root_list_set, Abbr `fn`, Abbr `out`] >>
     EVAL_TAC) >>
  `OPTION_MAP (MEM "ptr") (pv_closure fn ["ptr"]) = SOME T /\
   OPTION_MAP (MEM "alias") (pv_closure fn ["ptr"]) = SOME F` by
    (unabbrev_all_tac >> EVAL_TAC) >>
  `"ptr" IN pointer_derived_vars fn (set ["ptr"]) /\
   "alias" NOTIN pointer_derived_vars fn (set ["ptr"])` by
    metis_tac[witness_closure_member] >>
  irule witness_mixed_eq_refutes_fn_ptr_ok >>
  qexistsl_tac [`EL 3 (fn_insts fn)`,
                `"ptr"`, `"alias"`] >>
  fs[fn_pv_def] >> unabbrev_all_tac >> EVAL_TAC
QED

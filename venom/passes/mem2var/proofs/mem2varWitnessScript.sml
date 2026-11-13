(* Concrete witnesses for the pointer-use and size cases in Mem2Var. *)
Theory mem2varWitness
Ancestors
  mem2varDefs mem2varCorrectness mem2varInvariant
  venomInst venomState venomExecSemantics finite_map words byte list
  vfmTypes
  ptrDiscipline unitTransformDefs venomWf memSafeRun allocaFrontierBound ptrSafeRun ptrOkCheck
Libs
  finite_mapLib wordsLib

val () = computeLib.upd_compset add_finite_map_compset;

Definition m2v_witness_single_def:
  m2v_witness_single size_op uses = mk_raw_function "main"
    [<| bb_label := "entry"; bb_instructions :=
      mk_inst 0 ALLOCA [size_op] ["p"] :: uses |>]
End

Theorem pointer_value_and_size_kept:
  m2v_transform_function_checked
    (m2v_witness_single (Lit 32w)
      [mk_inst 1 MSTORE [Lit 64w; Var "p"] [];
       mk_inst 2 STOP [] []]) =
    SOME (m2v_witness_single (Lit 32w)
      [mk_inst 1 MSTORE [Lit 64w; Var "p"] [];
       mk_inst 2 STOP [] []]) /\
  m2v_transform_function_checked
    (m2v_witness_single (Lit 32w)
      [mk_inst 1 MSTORE [Var "p"; Lit 7w] [];
       mk_inst 2 RETURN [Lit 64w; Var "p"] []]) =
    SOME (m2v_witness_single (Lit 32w)
      [mk_inst 1 MSTORE [Var "p"; Lit 7w] [];
       mk_inst 2 RETURN [Lit 64w; Var "p"] []])
Proof
  EVAL_TAC
QED

Theorem dynamic_size_kept:
  m2v_transform_function_checked
    (m2v_witness_single (Var "n")
      [mk_inst 1 MSTORE [Var "p"; Lit 7w] [];
       mk_inst 2 STOP [] []]) =
    SOME (m2v_witness_single (Var "n")
      [mk_inst 1 MSTORE [Var "p"; Lit 7w] [];
       mk_inst 2 STOP [] []])
Proof
  EVAL_TAC
QED

Theorem undersized_store_fails:
  m2v_transform_function_checked
    (m2v_witness_single (Lit 16w)
      [mk_inst 1 MSTORE [Var "p"; Lit 7w] [];
       mk_inst 2 RETURN [Var "p"; Lit 16w] []]) = NONE
Proof
  EVAL_TAC
QED

Theorem undersized_read_only_kept:
  m2v_transform_function_checked
    (m2v_witness_single (Lit 16w)
      [mk_inst 1 MLOAD [Var "p"] ["x"];
       mk_inst 2 STOP [] []]) =
    SOME (m2v_witness_single (Lit 16w)
      [mk_inst 1 MLOAD [Var "p"] ["x"];
       mk_inst 2 STOP [] []])
Proof
  EVAL_TAC
QED

Theorem oversized_candidate_kept:
  m2v_transform_function_checked
    (m2v_witness_single (Lit 64w)
      [mk_inst 1 MSTORE [Var "p"; Lit 7w] [];
       mk_inst 2 RETURN [Var "p"; Lit 64w] []]) =
    SOME (m2v_witness_single (Lit 64w)
      [mk_inst 1 MSTORE [Var "p"; Lit 7w] [];
       mk_inst 2 RETURN [Var "p"; Lit 64w] []])
Proof
  EVAL_TAC
QED

Definition m2v_witness_counter_def:
  m2v_witness_counter = mk_raw_function "main"
    [<| bb_label := "entry"; bb_instructions :=
      [mk_inst 0 ALLOCA [Lit 32w] ["p"];
       mk_inst 1 MLOAD [Var "p"] ["x"];
       mk_inst 2 ALLOCA [Lit 32w] ["q"];
       mk_inst 3 MSTORE [Var "q"; Lit 7w] [];
       mk_inst 4 STOP [] []] |>]
End

Theorem read_only_advances_counter:
  m2v_promo_list m2v_witness_counter = [("q", "alloca_q_1", 32)]
Proof
  EVAL_TAC
QED

Definition m2v_witness_access_def:
  m2v_witness_access = mk_raw_function "main"
    [<| bb_label := "entry"; bb_instructions :=
      [mk_inst 0 ALLOCA [Lit 32w] ["p"];
       mk_inst 1 ALLOCA [Lit 64w] ["q"];
       mk_inst 2 ADD [Var "q"; Lit 0w] ["r"];
       mk_inst 3 MSTORE [Var "p"; Lit 7w] [];
       mk_inst 4 MSTORE [Var "q"; Lit 9w] [];
       mk_inst 5 MLOAD [Var "p"] ["x"];
       mk_inst 6 MLOAD [Var "r"] ["y"];
       mk_inst 7 RETURN [Var "p"; Lit 32w] []] |>]
End

Definition m2v_witness_run_def:
  m2v_witness_run fn = run_function 2 (mk_venom_context [fn] (SOME "main"))
    fn (init_venom_state "entry")
End

Definition m2v_witness_observe_def:
  m2v_witness_observe res =
    case res of
      Halt s => SOME (s.vs_returndata, lookup_var "x" s,
                      lookup_var "y" s, mload 32 s)
    | _ => NONE
End

Theorem promotion_with_unrelated_derived_access:
  m2v_promo_list m2v_witness_access = [("p", "alloca_p_0", 32)] /\
  m2v_transform_function_checked m2v_witness_access =
    SOME (m2v_transform_function_raw m2v_witness_access) /\
  m2v_witness_observe (m2v_witness_run m2v_witness_access) =
    SOME (REPLICATE 31 (0w : word8) ++ [7w], SOME 7w, SOME 9w, 9w) /\
  m2v_witness_observe
    (m2v_witness_run (m2v_transform_function_raw m2v_witness_access)) =
    SOME (REPLICATE 31 (0w : word8) ++ [7w], SOME 7w, SOME 9w, 9w)
Proof
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- (EVAL_TAC >> simp[set_byte_bit_field_insert, byte_index_def] >> EVAL_TAC) >>
  EVAL_TAC >> simp[set_byte_bit_field_insert, byte_index_def] >> EVAL_TAC
QED

Definition m2v_witness_escape_def:
  m2v_witness_escape = mk_raw_function "main"
    [<| bb_label := "entry"; bb_instructions :=
      [mk_inst 0 ALLOCA [Lit 32w] ["p"];
       mk_inst 1 ALLOCA [Lit 32w] ["q"];
       mk_inst 2 MSTORE [Var "p"; Lit 7w] [];
       mk_inst 3 MSTORE [Var "q"; Var "p"] [];
       mk_inst 4 MLOAD [Var "q"] ["r"];
       mk_inst 5 MLOAD [Var "r"] ["x"];
       mk_inst 6 STOP [] []] |>]
End

Theorem escaping_pointer_store_retained:
  m2v_promo_list m2v_witness_escape = [("q", "alloca_q_0", 32)] /\
  (case m2v_witness_run (m2v_transform_function_raw m2v_witness_escape) of
     Halt s => lookup_var "x" s = SOME 7w
   | _ => F)
Proof
  conj_tac >- EVAL_TAC >>
  EVAL_TAC >> simp[set_byte_bit_field_insert, byte_index_def] >> EVAL_TAC
QED

Theorem m2v_witness_mem_safe[local]:
  mem_safe_blocks 2
    (mk_venom_context [m2v_witness_access] (SOME "main"))
    m2v_witness_access (init_venom_state "entry")
Proof
  EVAL_TAC >> simp[set_byte_bit_field_insert, byte_index_def] >> EVAL_TAC
QED

Theorem m2v_witness_blocks_no_error[local]:
  !e. run_blocks 2
    (mk_venom_context [m2v_witness_access] (SOME "main"))
    m2v_witness_access (init_venom_state "entry") <> Error e
Proof
  EVAL_TAC >> simp[set_byte_bit_field_insert, byte_index_def] >> EVAL_TAC
QED

Theorem m2v_witness_frontier_structure[local]:
  ctx_inst_ids_distinct
    (mk_venom_context [m2v_witness_access] (SOME "main")) /\
  ctx_wf (mk_venom_context [m2v_witness_access] (SOME "main")) /\
  wf_invoke_targets
    (mk_venom_context [m2v_witness_access] (SOME "main")) /\
  reachable_call_graph_acyclic
    (mk_venom_context [m2v_witness_access] (SOME "main")) /\
  unit_alloca_budget
    (mk_venom_context [m2v_witness_access] (SOME "main")) < dimword (:256)
Proof
  EVAL_TAC
QED

Theorem m2v_witness_raw_memory[local]:
  raw_unit_memory_ok
    (mk_venom_context [m2v_witness_access] (SOME "main"))
    (init_venom_state "entry")
Proof
  irule mem_safe_raw_unit_memory_ok >>
  conj_tac >- EVAL_TAC >>
  qexistsl_tac [`alloca_frontier_inv`, `m2v_witness_access`, `"entry"`, `"main"`] >>
  conj_tac
  >- (simp[init_venom_state_def] >>
      metis_tac[mem_safe_blocks_all_fuel, m2v_witness_mem_safe,
                m2v_witness_blocks_no_error, init_venom_state_def]) >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac
  >- (rpt strip_tac >> irule alloca_frontier_inv_bound >>
      metis_tac[m2v_witness_frontier_structure]) >>
  conj_tac
  >- (irule alloca_frontier_inv_closed >>
      metis_tac[m2v_witness_frontier_structure]) >>
  irule alloca_frontier_inv_entry >>
  simp[m2v_witness_frontier_structure, init_venom_state_def] >>
  qexists_tac `"main"` >> EVAL_TAC
QED

Theorem m2v_witness_ptr_safe[local]:
  ptr_safe_blocks
    <| d_stor := (\a s. UNIV); d_trans := (\a s. UNIV);
       d_imm := (\s. UNIV); d_ret := (\r. UNIV) |>
    0 2 (mk_venom_context [m2v_witness_access] (SOME "main"))
    m2v_witness_access [] FEMPTY entry_taint (init_venom_state "entry")
Proof
  EVAL_TAC >> simp[set_byte_bit_field_insert, byte_index_def] >> EVAL_TAC >>
  rpt conj_tac >> simp[] >> rpt gen_tac >>
  Cases_on `op` >> simp[] >> rw[] >> gvs[]
QED

Theorem m2v_witness_ptr_structure[local]:
  EVERY (fn_ptr_ok (\nm. {}))
    (mk_venom_context [m2v_witness_access] (SOME "main")).ctx_functions /\
  EVERY (\f. fn_ptr_ok (\nm. {}) (reachable_fn f))
    (mk_venom_context [m2v_witness_access] (SOME "main")).ctx_functions
Proof
  `wf_function m2v_witness_access` by (EVAL_TAC >> rw[] >> gvs[]) >>
  `EVERY (\i. i.inst_opcode <> PHI) (fn_insts m2v_witness_access)` by EVAL_TAC >>
  simp[mk_venom_context_def] >>
  drule_all fn_reachable_blocks_reachable_fn >> disch_then (SUBST1_TAC o SYM) >>
  conj_tac >>
  mp_tac (Q.SPEC `\nm. []` fn_ptr_ok_check_sound) >> simp[] >>
  disch_then irule >> EVAL_TAC
QED

Theorem m2v_witness_pointer_discipline[local]:
  ptr_discipline 0
    (mk_venom_context [m2v_witness_access] (SOME "main"))
    (init_venom_state "entry")
Proof
  irule (cj 1 ptr_safe_ptr_discipline) >>
  simp[init_venom_state_def] >>
  reverse conj_tac
  >- (conj_tac >- EVAL_TAC >>
      qexists_tac `\nm. {}` >> metis_tac[m2v_witness_ptr_structure]) >>
  qexistsl_tac [
    `<| d_stor := (\a s. UNIV); d_trans := (\a s. UNIV);
        d_imm := (\s. UNIV); d_ret := (\r. UNIV) |>`,
    `m2v_witness_access`, `"entry"`, `"main"`] >>
  reverse conj_tac
  >- (rpt conj_tac >> EVAL_TAC) >>
  metis_tac[ptr_safe_blocks_all_fuel, m2v_witness_ptr_safe,
            m2v_witness_blocks_no_error, init_venom_state_def]
QED

Theorem m2v_witness_stores_dominate[local]:
  m2v_stores_dominate_loads m2v_witness_access "p"
Proof
  EVAL_TAC >> rw[] >> gvs[] >>
  (qexists_tac `mk_inst 3 MSTORE [Var "p"; Lit 7w] []` >>
   simp[mk_inst_def] >> conj_tac
   >- (rpt strip_tac >> Cases_on `path` >> gvs[]) >>
   qexists_tac `3`)
  >- (qexists_tac `5` >> EVAL_TAC) >>
  qexists_tac `7` >> EVAL_TAC
QED

(* This successful promotion also meets the full source entry contract;
   the unrelated allocation is accessed through an ADD-derived pointer. *)
Theorem m2v_witness_entry_contract:
  wf_function m2v_witness_access /\ fn_inst_wf m2v_witness_access /\
  wf_ssa m2v_witness_access /\
  o1_initial_state_ok (init_venom_state "entry") /\
  ptr_discipline 0
    (mk_venom_context [m2v_witness_access] (SOME "main"))
    (init_venom_state "entry") /\
  raw_unit_memory_ok
    (mk_venom_context [m2v_witness_access] (SOME "main"))
    (init_venom_state "entry") /\
  m2v_promotable_wf m2v_witness_access /\
  m2v_fresh_names_disjoint m2v_witness_access /\
  m2v_return_size_bounded m2v_witness_access /\
  EVERY (\inst. inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> MEMTOP)
    (fn_insts m2v_witness_access) /\
  m2v_transform_function_checked m2v_witness_access =
    SOME (m2v_transform_function_raw m2v_witness_access)
Proof
  conj_tac >- (EVAL_TAC >> rw[] >> gvs[]) >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- (EVAL_TAC >> rw[] >> gvs[]) >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- ACCEPT_TAC m2v_witness_pointer_discipline >>
  conj_tac >- ACCEPT_TAC m2v_witness_raw_memory >>
  conj_tac >-
    (rw[m2v_promotable_wf_def] >>
     qpat_x_assum `MEM inst (fn_insts _)` (mp_tac o CONV_RULE EVAL) >>
     strip_tac >> gvs[] >> ACCEPT_TAC m2v_witness_stores_dominate) >>
  conj_tac >- (EVAL_TAC >> rw[] >> gvs[] >> EVAL_TAC) >>
  conj_tac >- (EVAL_TAC >> rw[] >> gvs[] >> EVAL_TAC) >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  metis_tac[promotion_with_unrelated_derived_access]
QED

(* Instantiate the checked function theorem with the same successful
   promotion fixture, keeping its nonpromoted allocation observable. *)
Theorem m2v_witness_function_contract:
  !fuel.
    (?e. run_function fuel
      (mk_venom_context [m2v_witness_access] (SOME "main"))
      m2v_witness_access (init_venom_state "entry") = Error e) \/
    lift_result
      (m2v_public_rel m2v_witness_access)
      (m2v_public_rel m2v_witness_access)
      (m2v_public_rel m2v_witness_access)
      (run_function fuel
        (mk_venom_context [m2v_witness_access] (SOME "main"))
        m2v_witness_access (init_venom_state "entry"))
      (run_function fuel
        (mk_venom_context [m2v_witness_access] (SOME "main"))
        (m2v_transform_function_raw m2v_witness_access)
        (init_venom_state "entry"))
Proof
  gen_tac >>
  `lookup_function "main"
     (mk_venom_context [m2v_witness_access] (SOME "main")).ctx_functions =
   SOME m2v_witness_access` by EVAL_TAC >>
  mp_tac (Q.SPECL
    [`fuel`, `mk_venom_context [m2v_witness_access] (SOME "main")`,
     `"main"`, `m2v_witness_access`, `init_venom_state "entry"`,
     `m2v_transform_function_raw m2v_witness_access`]
    m2v_transform_function_correct) >>
  assume_tac m2v_witness_entry_contract >>
  fs[EVERY_MEM, mk_venom_context_def, lookup_function_def, init_venom_state_def]
QED

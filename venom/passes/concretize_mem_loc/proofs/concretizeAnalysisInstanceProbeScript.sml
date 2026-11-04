(* Bounded diagnostics, not a stage counterexample. *)
Theory concretizeAnalysisInstanceProbe
Ancestors
  concretizeAnalysisWriteSafety concretizeAnalysisBoundary
  concretizeMemLocDefs concretizePtrReadCoverage frameOriginUpdates
  venomExecSemantics venomState venomInst ptrDiscipline words finite_map
  pointerConfinedDefs pointerClosure pred_set venomWf memLocDefs venomMemProps
Libs wordsLib

Definition aip_alloc_def:
  aip_alloc = mk_inst 1 ALLOCA [Lit 32w] ["a"]
End

Definition aip_store_def:
  aip_store = mk_inst 2 MSTORE [Var "a"; Lit 9w] []
End

Definition aip_cached_def:
  aip_cached = (init_venom_state "loop") with
    <| vs_allocas := FEMPTY |+ (1,(256,32)); vs_alloca_next := 288 |>
End

Theorem aip_second_visit_cached:
  exec_alloca aip_alloc aip_cached 32w =
    OK (update_var "a" 256w aip_cached) /\
  origin_out [] FEMPTY aip_alloc (update_var "a" 256w aip_cached) =
    SOME (OriginLocal 1,(256,32))
Proof
  EVAL_TAC
QED

Definition aip_bp_def:
  aip_bp = SND (bp_handle_inst FEMPTY aip_alloc)
End

Theorem aip_static_kill:
  bp_get_ptrs aip_bp "a" = [Ptr (Allocation 1) (SOME 0)] /\
  find_base_allocas_opt aip_bp (inst_write_op aip_store) = [Allocation 1] /\
  ptr_ml_can_kill (Allocation 1) aip_bp (K (SOME 32)) aip_store
Proof
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  rewrite_tac[ptr_ml_can_kill_def] >> qexists_tac `32` >> EVAL_TAC
QED

Theorem aip_cached_write_range:
  source_memory_write_ranges aip_store (update_var "a" 256w aip_cached) =
    [(256,32)]
Proof
  EVAL_TAC
QED

Theorem aip_param_has_no_local_base:
  bp_get_ptrs
    (SND (bp_handle_inst aip_bp (mk_inst 3 PARAM [Lit 0w] ["p"]))) "p" = [] /\
  origin_out [SOME (256,32)] FEMPTY (mk_inst 3 PARAM [Lit 0w] ["p"])
    aip_cached = SOME (OriginParameter 0,(256,32)) /\
  ~ptr_ml_can_kill (Allocation 1) aip_bp (K (SOME 32))
    (mk_inst 4 MSTORE [Var "p"; Lit 9w] [])
Proof
  EVAL_TAC >> simp[]
QED

(* Mixed Incoming/Local PHI: BP ignores PARAM, but the frozen syntactic
   root-disjointness condition rejects a store through the merge. *)
Definition aip_mixed_def:
  aip_mixed = mk_raw_function "mixed"
    [<| bb_label := "entry"; bb_instructions :=
      [mk_inst 1 ALLOCA [Lit 32w] ["a"];
       mk_inst 3 PARAM [Lit 0w] ["p"];
       mk_inst 4 JNZ [Lit 1w; Label "left"; Label "right"] []] |>;
     <| bb_label := "left"; bb_instructions :=
      [mk_inst 5 JMP [Label "join"] []] |>;
     <| bb_label := "right"; bb_instructions :=
      [mk_inst 6 JMP [Label "join"] []] |>;
     <| bb_label := "join"; bb_instructions :=
      [mk_inst 7 PHI [Label "left"; Var "a"; Label "right"; Var "p"] ["v"];
       mk_inst 8 MSTORE [Var "v"; Lit 9w] [];
       mk_inst 9 STOP [] []] |>]
End

Theorem aip_mixed_bp:
  find_base_allocas
    (bp_analyze_fuel (concretize_memloc_fuel aip_mixed)
       (cfg_analyze aip_mixed) aip_mixed) (Var "v") = [Allocation 1]
Proof
  EVAL_TAC >> simp[]
QED

Theorem aip_mixed_roots:
  "v" IN pointer_derived_vars aip_mixed (alloca_roots aip_mixed) /\
  "v" IN pointer_derived_vars aip_mixed
    (ptr_roots (K {0}) aip_mixed DIFF alloca_roots aip_mixed)
Proof
  `alloca_roots aip_mixed = {"a"}` by
    simp[alloca_roots_def, aip_mixed_def, fn_insts_def, fn_insts_blocks_def,
         mk_raw_function_def, mk_inst_def, inst_output_def, EXTENSION, SF DNF_ss] >>
  `ptr_roots (K {0}) aip_mixed = {"a"; "p"}` by
    simp[ptr_roots_def, aip_mixed_def, fn_insts_def, fn_insts_blocks_def,
         mk_raw_function_def, mk_inst_def, inst_output_def, EXTENSION, SF DNF_ss] >>
  simp[] >> EVAL_TAC >> conj_tac >>
  simp[Once WhileTheory.OWHILE_THM] >>
  simp[Once WhileTheory.OWHILE_THM] >> simp[Once WhileTheory.OWHILE_THM]
QED

Theorem aip_mixed_rejected:
  ~fn_ptr_ok (K {0}) aip_mixed
Proof
  `MEM (mk_inst 8 MSTORE [Var "v"; Lit 9w] []) (fn_insts aip_mixed)` by
    simp[aip_mixed_def, fn_insts_def, fn_insts_blocks_def,
         mk_raw_function_def, mk_inst_def] >>
  strip_tac >>
  mp_tac aip_mixed_roots >> strip_tac >>
  gvs[fn_ptr_ok_def] >>
  qpat_x_assum `!inst ops v. _ ==> _`
    (qspec_then `mk_inst 8 MSTORE [Var "v"; Lit 9w] []` mp_tac) >>
  simp[mem_write_ops_def, mk_inst_def]
QED

(* On the second loop visit old is the previous visit's a.  ALLOCA a is
   cached, so the full store overwrites precisely the old site's bytes. *)
Definition aip_loop_def:
  aip_loop = mk_raw_function "loop_fn"
    [<| bb_label := "entry"; bb_instructions :=
      [mk_inst 10 ALLOCA [Lit 32w] ["seed"];
       mk_inst 11 JMP [Label "loop"] []] |>;
     <| bb_label := "loop"; bb_instructions :=
      [mk_inst 12 PHI [Label "entry"; Var "seed"; Label "loop"; Var "a"] ["old"];
       aip_alloc; aip_store;
       mk_inst 13 MLOAD [Var "old"] ["result"];
       mk_inst 14 JNZ [Lit 1w; Label "loop"; Label "exit"] []] |>;
     <| bb_label := "exit"; bb_instructions := [mk_inst 15 STOP [] []] |>]
End

Theorem aip_loop_ssa:
  ssa_form aip_loop
Proof
  EVAL_TAC >> simp[]
QED

Theorem aip_loop_bases:
  find_base_allocas
    (bp_analyze_fuel (concretize_memloc_fuel aip_loop)
       (cfg_analyze aip_loop) aip_loop) (Var "old") = [Allocation 1; Allocation 10]
Proof
  EVAL_TAC >> simp[]
QED

Theorem aip_loop_old_origin:
  phi_prov (SOME "loop") (FEMPTY |+ ("a",(256,32)))
    (mk_inst 12 PHI [Label "entry"; Var "seed"; Label "loop"; Var "a"] ["old"]) =
    SOME (256,32) /\
  origin_phi (SOME "loop") (FEMPTY |+ ("a",(OriginLocal 1,(256,32))))
    (mk_inst 12 PHI [Label "entry"; Var "seed"; Label "loop"; Var "a"] ["old"]) =
    SOME (OriginLocal 1,(256,32))
Proof
  EVAL_TAC
QED

Theorem aip_loop_definite_assignment:
  fn_defs_reach_uses aip_loop
Proof
  simp[fn_defs_reach_uses_def, aip_loop_def, aip_alloc_def, aip_store_def,
       mk_raw_function_def, mk_inst_def, phi_pairs_def, SF DNF_ss] >>
  simp[def_on_all_paths_def] >> rpt strip_tac >> disj2_tac
  >- (qexists_tac `0` >> EVAL_TAC)
  >- (qexists_tac `1` >> EVAL_TAC)
  >- (qexists_tac `1` >> EVAL_TAC >> qexists_tac `2` >> EVAL_TAC) >>
  qexists_tac `0` >> EVAL_TAC >> qexists_tac `3` >> EVAL_TAC
QED

Theorem aip_loop_ptr_ok:
  fn_ptr_ok (K {}) aip_loop
Proof
  `alloca_roots aip_loop = {"seed"; "a"}` by
    simp[alloca_roots_def, aip_loop_def, aip_alloc_def, aip_store_def,
         fn_insts_def, fn_insts_blocks_def, mk_raw_function_def, mk_inst_def,
         inst_output_def, EXTENSION, SF DNF_ss] >>
  `ptr_roots (K {}) aip_loop = {"seed"; "a"}` by
    simp[ptr_roots_def, aip_loop_def, aip_alloc_def, aip_store_def,
         fn_insts_def, fn_insts_blocks_def, mk_raw_function_def, mk_inst_def,
         inst_output_def, EXTENSION, SF DNF_ss] >>
  `{"seed"; "a"} SUBSET pointer_derived_vars aip_loop (ptr_roots (K {}) aip_loop)` by
    metis_tac[pointer_derived_vars_roots, FINITE_INSERT, FINITE_EMPTY] >>
  `pointer_derived_vars aip_loop {} = {}` by
    (EVAL_TAC >> simp[Once WhileTheory.OWHILE_THM] >>
     simp[Once WhileTheory.OWHILE_THM]) >>
  simp[fn_ptr_ok_def] >>
  conj_tac >- simp[aip_loop_def, mk_raw_function_def] >>
  conj_tac >-
    (simp[ptr_use_ok_def, aip_loop_def, aip_alloc_def, aip_store_def,
          fn_insts_def, fn_insts_blocks_def, mk_raw_function_def, mk_inst_def,
          is_pointer_preserving_op_def, mem_write_ops_def, mem_read_ops_def] >>
     rpt strip_tac >> gvs[is_pointer_preserving_op_def]) >>
  conj_tac >-
    (simp[affine_pointer_ops_def, aip_loop_def, aip_alloc_def, aip_store_def,
          mk_raw_function_def, mk_inst_def] >> rpt strip_tac >> gvs[]) >>
  gvs[SUBSET_DEF] >>
  simp[phi_pv_all_var_def, aip_loop_def, aip_alloc_def, aip_store_def,
       mk_raw_function_def, mk_inst_def] >> rpt strip_tac >>
  gvs[aip_loop_def, aip_alloc_def, aip_store_def, mk_raw_function_def, mk_inst_def]
QED

Theorem aip_cached_no_fresh_bytes:
  new_site_bytes aip_cached (update_var "a" 256w aip_cached) = {}
Proof
  simp[new_site_bytes_def, aip_cached_def, update_var_def, EXTENSION,
       FLOOKUP_DEF, SF DNF_ss] >> EVAL_TAC >> simp[]
QED

Theorem aip_old_read_after_full_store:
  mload 256 (mstore 256 9w aip_cached) = 9w
Proof
  simp[mload_mstore_same]
QED

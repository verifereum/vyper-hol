(* Small actual-code projection keeps calibration consumers independent of
   runtime packaging. No semantic invariant is introduced. *)
Theory bodyPtrWordBuiltinsAbsCalibration
Ancestors bodyPtrWordBuiltinsAbsRuntime bodyPtrWordBuiltinsComparison
  ptrSafeRun
Libs finite_mapLib intReduce wordsLib

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset intReduce.add_int_compset
val () = computeLib.upd_compset (fn cs =>
  (computeLib.scrub_const cs ``compile_expr``;
   computeLib.scrub_const cs ``compile_builtin_dispatch``;
   computeLib.scrub_const cs ``compile_type_builtin_dispatch``;
   computeLib.add_thms
     [exprLoweringTheory.compile_expr_component_eq,
      exprLoweringTheory.compile_builtin_dispatch_component_eq,
      exprLoweringTheory.compile_type_builtin_dispatch_component_eq] cs))

Theorem word_abs_runtime_prefix:
  TAKE 4 (DROP 11 (EL 4 word_abs_runtime_func.fn_blocks).bb_instructions) =
    [mk_inst 21 MLOAD [Var "%11"] ["%14"];
     mk_inst 22 SUB [Lit 0w; Var "%14"] ["%15"];
     mk_inst 23 SLT [Var "%14"; Lit 0w] ["%16"];
     mk_inst 24 EQ [Var "%14"; Var "%15"] ["%17"]]
Proof
  rewrite_tac[word_abs_runtime_func_def, word_abs_runtime_unit_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``package_external_fn``, ``run_lowering``, ``build_selectors``,
     ``package_fallback_fn``, ``fn_allocs_ok``, ``word_abs_runtime_expr``]) >>
  pure_rewrite_tac [compileVyperTheory.set_external_package_target_all,
    compileVyperTheory.set_fallback_package_target_all,
    GSYM word_abs_runtime_tops_def, GSYM word_abs_runtime_source_def,
    word_abs_runtime_package, word_abs_runtime_allocs, word_abs_runtime_fallback,
    word_abs_runtime_posargs, word_abs_runtime_mincds] >>
  simp[compileVyperTheory.external_return_buffer_ok_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``function_selector``, ``calldata_method_id``, ``vyper_to_abi_types``]) >>
  simp[listTheory.INDEX_FIND_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``function_selector``, ``calldata_method_id``, ``vyper_to_abi_types``])
QED

(* Concrete intermediate states name the four bounded execution stages;
   next_inst is explicit because step_inst itself does not advance the PC. *)
Definition word_abs_cal_s1_def:
  word_abs_cal_s1 = next_inst (update_var "%14" 1w word_abs_runtime_s0)
End
Definition word_abs_cal_s2_def:
  word_abs_cal_s2 = next_inst (update_var "%15" (-1w) word_abs_cal_s1)
End
Definition word_abs_cal_s3_def:
  word_abs_cal_s3 = next_inst (update_var "%16" 0w word_abs_cal_s2)
End
Definition word_abs_cal_s4_def:
  word_abs_cal_s4 = next_inst (update_var "%17" 0w word_abs_cal_s3)
End

Theorem word_abs_cal_step21:
  step_inst fuel ctx (mk_inst 21 MLOAD [Var "%11"] ["%14"])
    word_abs_runtime_s0 = OK (update_var "%14" 1w word_abs_runtime_s0)
Proof
  EVAL_TAC
QED

Theorem word_abs_cal_step22:
  step_inst fuel ctx (mk_inst 22 SUB [Lit 0w; Var "%14"] ["%15"])
    word_abs_cal_s1 = OK (update_var "%15" (-1w) word_abs_cal_s1)
Proof
  EVAL_TAC
QED

Theorem word_abs_cal_step23:
  step_inst fuel ctx (mk_inst 23 SLT [Var "%14"; Lit 0w] ["%16"])
    word_abs_cal_s2 = OK (update_var "%16" 0w word_abs_cal_s2)
Proof
  EVAL_TAC
QED

Theorem word_abs_cal_step24:
  step_inst fuel ctx (mk_inst 24 EQ [Var "%14"; Var "%15"] ["%17"])
    word_abs_cal_s3 = OK (update_var "%17" 0w word_abs_cal_s3)
Proof
  EVAL_TAC
QED

Theorem word_abs_cal_indices:
  word_abs_runtime_s0.vs_inst_idx = 11 /\
  word_abs_cal_s1.vs_inst_idx = 12 /\ word_abs_cal_s2.vs_inst_idx = 13 /\
  word_abs_cal_s3.vs_inst_idx = 14 /\ word_abs_cal_s4.vs_inst_idx = 15
Proof
  EVAL_TAC
QED

(* Ghost stages are concrete fixture abbreviations, not safety assumptions. *)
Definition word_abs_cal_G1_def:
  word_abs_cal_G1 PG G = step_prov PG G
    (mk_inst 21 MLOAD [Var "%11"] ["%14"]) word_abs_cal_s1
End
Definition word_abs_cal_G2_def:
  word_abs_cal_G2 PG G = step_prov PG (word_abs_cal_G1 PG G)
    (mk_inst 22 SUB [Lit 0w; Var "%14"] ["%15"]) word_abs_cal_s2
End
Definition word_abs_cal_G3_def:
  word_abs_cal_G3 PG G = step_prov PG (word_abs_cal_G2 PG G)
    (mk_inst 23 SLT [Var "%14"; Lit 0w] ["%16"]) word_abs_cal_s3
End

Theorem word_abs_cal_load_clears:
  FLOOKUP (word_abs_cal_G1 PG G) "%14" = NONE
Proof
  simp[word_abs_cal_G1_def, ptrDisciplineTheory.step_prov_def,
    ptrDisciplineTheory.out_prov_def, ptrDisciplineTheory.set_prov_def,
    venomInstTheory.mk_inst_def, finite_mapTheory.FLOOKUP_DRESTRICT]
QED

Theorem word_abs_cal_sub_clears:
  FLOOKUP (word_abs_cal_G2 PG G) "%14" = NONE /\
  FLOOKUP (word_abs_cal_G2 PG G) "%15" = NONE
Proof
  simp[word_abs_cal_G2_def, ptrDisciplineTheory.step_prov_def,
    ptrDisciplineTheory.out_prov_def, ptrDisciplineTheory.set_prov_def,
    ptrDisciplineTheory.first_prov_def, ptrDisciplineTheory.op_prov_def,
    venomInstTheory.mk_inst_def, word_abs_cal_load_clears,
    finite_mapTheory.FLOOKUP_DRESTRICT]
QED

Theorem word_abs_cal_eq_access:
  access_ok lo (word_abs_cal_G3 PG G) fn
    (mk_inst 24 EQ [Var "%14"; Var "%15"] ["%17"]) s
Proof
  irule (iffRL access_ok_eq_vars) >>
  simp[venomInstTheory.mk_inst_def, word_abs_cal_G3_def,
    ptrDisciplineTheory.step_prov_def, ptrDisciplineTheory.out_prov_def,
    ptrDisciplineTheory.set_prov_def, finite_mapTheory.FDOM_DRESTRICT,
    finite_mapTheory.FLOOKUP_DRESTRICT] >>
  disj1_tac >> mp_tac word_abs_cal_sub_clears >>
  simp[finite_mapTheory.FLOOKUP_DEF] >> metis_tac[optionTheory.NOT_SOME_NONE]
QED

(* Keep taint stages explicit: storing an empty taint set is not the same
   finite map as omitting that variable binding. *)
Definition word_abs_cal_t1_def:
  word_abs_cal_t1 = step_taint (mk_inst 21 MLOAD [Var "%11"] ["%14"])
    word_abs_runtime_s0 (update_var "%14" 1w word_abs_runtime_s0) entry_taint
End
Definition word_abs_cal_t2_def:
  word_abs_cal_t2 = step_taint (mk_inst 22 SUB [Lit 0w; Var "%14"] ["%15"])
    word_abs_cal_s1 (update_var "%15" (-1w) word_abs_cal_s1) word_abs_cal_t1
End
Definition word_abs_cal_t3_def:
  word_abs_cal_t3 = step_taint (mk_inst 23 SLT [Var "%14"; Lit 0w] ["%16"])
    word_abs_cal_s2 (update_var "%16" 0w word_abs_cal_s2) word_abs_cal_t2
End

Theorem word_abs_cal_ghost21:
  ghost_step fuel ctx PG G entry_taint
    (mk_inst 21 MLOAD [Var "%11"] ["%14"]) word_abs_runtime_s0 =
    (word_abs_cal_G1 PG G, word_abs_cal_t1)
Proof
  simp[Once ghost_step_def, word_abs_cal_step21, venomInstTheory.mk_inst_def,
    word_abs_cal_G1_def, word_abs_cal_t1_def,
    ptrDisciplineTheory.step_prov_def, ptrDisciplineTheory.out_prov_def]
QED

Theorem word_abs_cal_ghost22:
  ghost_step fuel ctx PG (word_abs_cal_G1 PG G) word_abs_cal_t1
    (mk_inst 22 SUB [Lit 0w; Var "%14"] ["%15"]) word_abs_cal_s1 =
    (word_abs_cal_G2 PG G, word_abs_cal_t2)
Proof
  simp[Once ghost_step_def, word_abs_cal_step22, venomInstTheory.mk_inst_def,
    word_abs_cal_G2_def, word_abs_cal_t2_def,
    ptrDisciplineTheory.step_prov_def, ptrDisciplineTheory.out_prov_def]
QED

Theorem word_abs_cal_ghost23:
  ghost_step fuel ctx PG (word_abs_cal_G2 PG G) word_abs_cal_t2
    (mk_inst 23 SLT [Var "%14"; Lit 0w] ["%16"]) word_abs_cal_s2 =
    (word_abs_cal_G3 PG G, word_abs_cal_t3)
Proof
  simp[Once ghost_step_def, word_abs_cal_step23, venomInstTheory.mk_inst_def,
    word_abs_cal_G3_def, word_abs_cal_t3_def,
    ptrDisciplineTheory.step_prov_def, ptrDisciplineTheory.out_prov_def]
QED

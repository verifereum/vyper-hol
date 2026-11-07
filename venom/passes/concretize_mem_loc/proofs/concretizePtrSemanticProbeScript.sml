(* Local semantic-interface probes; these are not full stage counterexamples. *)
Theory concretizePtrSemanticProbe
Ancestors
  concretizePtrReadCoverage concretizeMemLocDefs venomWf ptrDiscipline
  pointerConfinedDefs venomInst pointerClosure
Libs wordsLib

Definition ptr_sem_diamond_def:
  ptr_sem_diamond = mk_raw_function "diamond"
    [<| bb_label := "entry"; bb_instructions :=
      [mk_inst 301 ALLOCA [Lit (32w:256 word)] ["a"];
       mk_inst 302 ALLOCA [Lit 32w] ["b"];
       mk_inst 303 JNZ [Lit 1w; Label "left"; Label "right"] []] |>;
     <| bb_label := "left"; bb_instructions :=
      [mk_inst 304 JMP [Label "join"] []] |>;
     <| bb_label := "right"; bb_instructions :=
      [mk_inst 305 JMP [Label "join"] []] |>;
     <| bb_label := "join"; bb_instructions :=
      [mk_inst 306 PHI [Label "left"; Var "a"; Label "right"; Var "b"] ["p"];
       mk_inst 307 MSTORE [Var "p"; Lit 7w] [];
       mk_inst 308 STOP [] []] |>]
End

Definition ptr_sem_bp_def:
  ptr_sem_bp fn = bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn
End

Theorem ptr_sem_diamond_bases:
  find_base_allocas (ptr_sem_bp ptr_sem_diamond) (Var "p") =
    [Allocation 301; Allocation 302]
Proof
  EVAL_TAC >> simp[]
QED

Theorem ptr_sem_diamond_no_kill:
  ~ptr_ml_can_kill (Allocation 301) (ptr_sem_bp ptr_sem_diamond)
     (\a. SOME 32) (mk_inst 307 MSTORE [Var "p"; Lit 7w] []) /\
  ~ptr_ml_can_kill (Allocation 302) (ptr_sem_bp ptr_sem_diamond)
     (\a. SOME 32) (mk_inst 307 MSTORE [Var "p"; Lit 7w] [])
Proof
  EVAL_TAC >> simp[]
QED

Theorem ptr_sem_diamond_ssa:
  ssa_form ptr_sem_diamond
Proof
  EVAL_TAC >> simp[]
QED

Definition ptr_sem_derived_def:
  ptr_sem_derived delta = mk_raw_function "derived"
    [<| bb_label := "entry"; bb_instructions :=
      [mk_inst 311 ALLOCA [Lit (32w:256 word)] ["a"];
       mk_inst 312 ADD [Var "a"; Lit delta] ["p"];
       mk_inst 313 MSTORE [Var "p"; Lit 7w] [];
       mk_inst 314 STOP [] []] |>]
End

Theorem ptr_sem_derived_kill:
  ptr_ml_can_kill (Allocation 311) (ptr_sem_bp (ptr_sem_derived 0w))
    (\a. SOME 32) (mk_inst 313 MSTORE [Var "p"; Lit 7w] []) /\
  ptr_ml_can_kill (Allocation 311) (ptr_sem_bp (ptr_sem_derived 1w))
    (\a. SOME 32) (mk_inst 313 MSTORE [Var "p"; Lit 7w] [])
Proof
  conj_tac >> rewrite_tac[ptr_ml_can_kill_def] >>
  qexists_tac `32` >> EVAL_TAC
QED

Definition ptr_sem_state_def:
  ptr_sem_state p = (init_venom_state "entry") with
    vs_vars := FEMPTY |+ ("p",p)
End

Theorem ptr_sem_derived_write_ranges:
  source_memory_write_ranges (mk_inst 313 MSTORE [Var "p"; Lit 7w] [])
    (ptr_sem_state 64w) = [(64,32)] /\
  source_memory_write_ranges (mk_inst 313 MSTORE [Var "p"; Lit 7w] [])
    (ptr_sem_state 65w) = [(65,32)]
Proof
  EVAL_TAC
QED

Theorem ptr_sem_derived_containment:
  ((64:num) <= 64 /\ (64:num) + 32 <= 64 + 32) /\
  ~((64:num) <= 65 /\ (65:num) + 32 <= 64 + 32)
Proof
  EVAL_TAC
QED

Definition ptr_sem_fresh_def:
  ptr_sem_fresh = mk_raw_function "fresh"
    [<| bb_label := "entry"; bb_instructions :=
      [mk_inst 321 ALLOCA [Lit (32w:256 word)] ["a"];
       mk_inst 322 ALLOCA [Lit 32w] ["b"];
       mk_inst 323 ALLOCA [Lit 32w] ["c"];
       mk_inst 324 MLOAD [Var "a"] ["x"];
       mk_inst 325 MSTORE [Var "b"; Var "x"] [];
       mk_inst 326 MSTORE [Var "c"; Lit 7w] [];
       mk_inst 327 MLOAD [Var "c"] ["y"];
       mk_inst 328 STOP [] []] |>]
End

Theorem ptr_sem_fresh_read_bases:
  find_base_allocas (ptr_sem_bp ptr_sem_fresh) (Var "a") = [Allocation 321] /\
  find_base_allocas (ptr_sem_bp ptr_sem_fresh) (Var "c") = [Allocation 323]
Proof
  EVAL_TAC
QED

Theorem ptr_sem_fresh_ssa:
  ssa_form ptr_sem_fresh
Proof
  EVAL_TAC
QED

Definition ptr_sem_ls_def:
  ptr_sem_ls fn = context_mem_livesets (concretize_memloc_fuel fn)
    (mk_venom_context [fn] (SOME fn.fn_name)) fn (ptr_sem_bp fn) (cfg_analyze fn)
End

Theorem ptr_sem_fresh_read_covered:
  MEM ("entry",3)
    (case FLOOKUP (ptr_sem_ls ptr_sem_fresh) (Allocation 321) of
       NONE => [] | SOME xs => xs)
Proof
  EVAL_TAC
QED

Theorem ptr_sem_fresh_no_write_mark:
  FLOOKUP (ml_mark_stores_live (ptr_sem_bp ptr_sem_fresh) ptr_sem_fresh FEMPTY)
    (Allocation 321) = NONE
Proof
  EVAL_TAC
QED

Theorem ptr_sem_derived_provenance:
  step_prov [] (FEMPTY |+ ("a",(64,32)))
    (mk_inst 312 ADD [Var "a"; Lit 1w] ["p"])
    (ptr_sem_state 65w) =
    FEMPTY |+ ("a",(64,32)) |+ ("p",(64,32))
Proof
  EVAL_TAC
QED

Theorem ptr_sem_derived_bad_access:
  ~access_ok 0 (FEMPTY |+ ("p",(64,32))) (ptr_sem_derived 1w)
    (mk_inst 313 MSTORE [Var "p"; Lit 7w] []) (ptr_sem_state 65w)
Proof
  EVAL_TAC >> simp[]
QED

Theorem ptr_sem_derived_good_access:
  access_ok 0 (FEMPTY |+ ("p",(64,32))) (ptr_sem_derived 0w)
    (mk_inst 313 MSTORE [Var "p"; Lit 7w] []) (ptr_sem_state 64w)
Proof
  EVAL_TAC >> simp[]
QED

Theorem ptr_sem_affine:
  affine_pointer_ops ptr_sem_diamond roots /\
  affine_pointer_ops (ptr_sem_derived delta) roots /\
  affine_pointer_ops ptr_sem_fresh roots
Proof
  simp[affine_pointer_ops_def, ptr_sem_diamond_def, ptr_sem_derived_def,
       ptr_sem_fresh_def, mk_raw_function_def, mk_inst_def] >> rpt strip_tac >> gvs[]
QED

Theorem ptr_sem_phi_free:
  phi_pv_all_var (ptr_sem_derived delta) roots /\
  phi_pv_all_var ptr_sem_fresh roots
Proof
  simp[phi_pv_all_var_def, ptr_sem_derived_def, ptr_sem_fresh_def,
       mk_raw_function_def, mk_inst_def] >> rpt strip_tac >> gvs[]
QED

Theorem ptr_sem_derived_live:
  MEM ("entry",2)
    (case FLOOKUP (ptr_sem_ls (ptr_sem_derived 0w)) (Allocation 311) of
       NONE => [] | SOME xs => xs)
Proof
  EVAL_TAC
QED

Theorem ptr_sem_diamond_live:
  MEM ("join",1)
    (case FLOOKUP (ptr_sem_ls ptr_sem_diamond) (Allocation 301) of
       NONE => [] | SOME xs => xs) /\
  MEM ("join",1)
    (case FLOOKUP (ptr_sem_ls ptr_sem_diamond) (Allocation 302) of
       NONE => [] | SOME xs => xs)
Proof
  EVAL_TAC
QED

(* The three allocated sites occupy [64,96), [96,128), [128,160).
   These snapshots isolate the ghost read/copy/write interface; reachability
   of the snapshots remains a separate premise, not certified by this probe. *)
Definition ptr_sem_fresh_state_def:
  ptr_sem_fresh_state = (init_venom_state "entry") with
    <| vs_vars := FEMPTY |+ ("a",64w) |+ ("b",96w) |+ ("c",128w) |+
                         ("x",0w);
       vs_allocas := FEMPTY |+ (321,(64,32)) |+ (322,(96,32)) |+ (323,(128,32)) |>
End

Definition ptr_sem_fresh_taint_def:
  ptr_sem_fresh_taint = entry_taint with t_mem := {i | 64 <= i /\ i < 160}
End

Theorem ptr_sem_fresh_ranges:
  source_memory_read_ranges (mk_inst 324 MLOAD [Var "a"] ["x"])
    ptr_sem_fresh_state = [(64,32)] /\
  source_memory_write_ranges (mk_inst 325 MSTORE [Var "b"; Var "x"] [])
    ptr_sem_fresh_state = [(96,32)] /\
  source_memory_read_ranges (mk_inst 327 MLOAD [Var "c"] ["y"])
    ptr_sem_fresh_state = [(128,32)]
Proof
  EVAL_TAC
QED

Definition ptr_sem_after_read_def:
  ptr_sem_after_read = step_taint (mk_inst 324 MLOAD [Var "a"] ["x"])
    ptr_sem_fresh_state ptr_sem_fresh_state ptr_sem_fresh_taint
End

Definition ptr_sem_after_copy_def:
  ptr_sem_after_copy = step_taint (mk_inst 325 MSTORE [Var "b"; Var "x"] [])
    ptr_sem_fresh_state ptr_sem_fresh_state ptr_sem_after_read
End

Definition ptr_sem_after_init_def:
  ptr_sem_after_init = step_taint (mk_inst 326 MSTORE [Var "c"; Lit 7w] [])
    ptr_sem_fresh_state ptr_sem_fresh_state ptr_sem_after_copy
End

Theorem ptr_sem_fresh_tainted_copy:
  0 IN op_taint ptr_sem_after_read (Var "x") /\
  31 IN op_taint ptr_sem_after_read (Var "x") /\
  96 IN ptr_sem_after_copy.t_mem /\
  127 IN ptr_sem_after_copy.t_mem /\
  128 NOTIN ptr_sem_after_init.t_mem /\
  159 NOTIN ptr_sem_after_init.t_mem
Proof
  EVAL_TAC >> simp[]
QED

Theorem ptr_sem_separate_read_untainted:
  out_taint ptr_sem_after_init (mk_inst 327 MLOAD [Var "c"] ["y"])
    ptr_sem_fresh_state = {}
Proof
  EVAL_TAC >> simp[pred_setTheory.EXTENSION] >> decide_tac
QED

Theorem ptr_sem_diamond_phi:
  phi_pv_all_var ptr_sem_diamond (alloca_roots ptr_sem_diamond)
Proof
  `alloca_roots ptr_sem_diamond = {"a"; "b"}` by
    simp[alloca_roots_def, ptr_sem_diamond_def, fn_insts_def, fn_insts_blocks_def,
         mk_raw_function_def, mk_inst_def, inst_output_def,
         pred_setTheory.EXTENSION, SF DNF_ss] >>
  `{"a"; "b"} SUBSET pointer_derived_vars ptr_sem_diamond
      (alloca_roots ptr_sem_diamond)` by
    metis_tac[pointer_derived_vars_roots, pred_setTheory.FINITE_INSERT,
              pred_setTheory.FINITE_EMPTY] >>
  gvs[pred_setTheory.SUBSET_DEF] >>
  simp[phi_pv_all_var_def, ptr_sem_diamond_def, mk_raw_function_def,
       mk_inst_def] >> rpt strip_tac >>
  gvs[ptr_sem_diamond_def, mk_raw_function_def, mk_inst_def]
QED

Theorem ptr_sem_single_block_definite_assignment:
  fn_defs_reach_uses (ptr_sem_derived delta) /\
  fn_defs_reach_uses ptr_sem_fresh
Proof
  simp[fn_defs_reach_uses_def, ptr_sem_derived_def, ptr_sem_fresh_def,
       mk_raw_function_def, mk_inst_def] >> rpt strip_tac >> gvs[] >>
  simp[def_on_all_paths_def] >> rpt strip_tac >> disj2_tac >>
  ntac 16 (simp[Once arithmeticTheory.EXISTS_NUM])
QED

Theorem ptr_sem_fresh_copy_permitted:
  taint_ok ptr_sem_fresh ptr_sem_after_read
    (mk_inst 325 MSTORE [Var "b"; Var "x"] []) ptr_sem_fresh_state
Proof
  simp[taint_ok_def, mk_inst_def, op_taint_def,
       ptr_sem_after_read_def, step_taint_def, set_var_taint_def] >>
  EVAL_TAC >> rpt strip_tac >> gvs[]
QED

(* Probe report / remaining general obligations.

   The checked examples do NOT establish frame_reachable for the snapshots,
   nor ptr_discipline for their whole contexts.  In particular no example
   here is claimed to refute a frozen stage theorem.

   Admissibility mapping:
   - SSA is checked for diamond/fresh; derived has distinct outputs a,p.
   - affine_pointer_ops is checked for all three (arbitrary roots).
   - phi_pv_all_var is checked for diamond's alloca roots and vacuously
     for derived/fresh; there are no PARAM/DALLOCA roots in these fixtures.
   - fn_defs_reach_uses is checked for derived/fresh.  Diamond still needs
     a path argument: both a,b are defined in entry, which every path to
     either predecessor traverses; p is defined before the join store.
     The ordinary-use and PHI-edge eliminators in
     concretizeAnalysisPathDefinitions describe exactly these obligations.
   - Whole-context ptr_use_ok, frame reachability and access_ok at every
     step remain proof obligations, not assumed consequences of SSA.
     The shifted derived full-word write is explicitly rejected by access_ok.
   - Fresh tainted read/copy and independent initialization are tested via
     actual step_taint/out_taint.  Snapshot reachability must be supplied
     separately; these computations do not claim an execution trace theorem.

   Required universal interface (NOT proved by these examples):
   For admissible source fn and reachable (inst,s,G), production bp result
   bp, allocation key A and actual allocated site (b,sz), if
       ptr_ml_can_kill A bp alloc_sizes inst
   then the write-address provenance denotes A's currently active runtime
   site, and the write range is exactly (b,sz).
   This requires an identity theorem for singleton base sets, using SSA,
   definite assignment and the mixed-root write exclusion in fn_ptr_ok;
   access_ok alone only gives containment in whichever site G names.
   The extent argument additionally uses the kill's size equality and
   access_ok containment (hence displacement zero), not just may-alias.
   This interface must be adjusted for in_revert_forward: access_ok's range
   containment is intentionally exempt there.  Do not assert the unconditional
   exact-overwrite conclusion on exempt steps; retain that guard or prove
   those steps irrelevant to the untainted-read demand invariant.
*)


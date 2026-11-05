Theory bodyPtrPopBulkCopy
Ancestors
  bodyPtrPopRegionInvariant bodyPtrDefs stmtLowering vyperCompiler
  ptrSafeRun fragExec valueEncoding venomExecSemantics
  list valueEncodingProofs venomMemProofs vyperValue venomState finite_map
  ptrDiscipline compileEnv pred_set pair

(* Concrete fixtures expose the compiler-generated aggregate-copy branch.
   They define no alternative safety predicate or execution semantics. *)
Definition pop_bulk_ty_def:
  pop_bulk_ty = TupleT [ArrayT (ArrayT (BaseT (UintT 256)) (Dynamic 1)) (Dynamic 1)]
End

Definition pop_bulk_tv_def:
  pop_bulk_tv = TupleTV [ArrayTV (ArrayTV (BaseTV (UintT 256)) (Dynamic 1)) (Dynamic 1)]
End

Definition pop_bulk_compiled_def:
  pop_bulk_compiled = SND (compile_assign_value ARB (Lit 0w) LocStorage
    (Var "%src") F (SOME LocMemory) pop_bulk_ty pop_bulk_ty NONE 96
    (initial_compile_state "entry"))
End

Theorem pop_bulk_compiler_branch:
  pop_bulk_compiled = SND (compile_memory_to_storage (Var "%src") (Lit 0w) 3
    (initial_compile_state "entry"))
Proof
  EVAL_TAC
QED

Definition pop_bulk_fn_def:
  pop_bulk_fn = mk_raw_function "entry"
    (REVERSE pop_bulk_compiled.cs_blocks ++
     [<| bb_label := pop_bulk_compiled.cs_current_bb;
         bb_instructions := pop_bulk_compiled.cs_current_insts ++
                            [mk_inst 100 STOP [] []] |>])
End

Definition pop_bulk_start_def:
  pop_bulk_start = update_var "%src" 0w
    (mstore 32 7w (init_venom_state "entry"))
End

Theorem pop_bulk_exec:
  ?s. run_from 10 (mk_venom_context [] NONE) pop_bulk_fn pop_bulk_start = Halt s /\
      sload 0w s = 0w /\ sload 1w s = 7w
Proof
  CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV pop_bulk_fn_def THENC EVAL)) >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``run_blocks``]) >>
  simp[SF wordsLib.SIZES_ss] >>
  once_rewrite_tac[run_blocks_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``run_blocks``]) >>
  once_rewrite_tac[run_blocks_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``run_blocks``]) >>
  once_rewrite_tac[run_blocks_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``run_blocks``]) >>
  once_rewrite_tac[run_blocks_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``run_blocks``]) >>
  once_rewrite_tac[run_blocks_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``run_blocks``]) >>
  once_rewrite_tac[run_blocks_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``run_blocks``]) >>
  once_rewrite_tac[run_blocks_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``run_blocks``]) >>
  once_rewrite_tac[run_blocks_def] >>
  EVAL_TAC >> simp[] >> EVAL_TAC
QED

Definition pop_bulk_taint_def:
  pop_bulk_taint = entry_taint with t_mem := {63}
End

Theorem pop_bulk_taint_imported:
  (SND (ghost_run 10 (mk_venom_context [] NONE) pop_bulk_fn []
    FEMPTY pop_bulk_taint pop_bulk_start)).t_stor = {(1w,31)}
Proof
  CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV pop_bulk_fn_def THENC EVAL)) >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``ghost_blocks``]) >>
  simp[SF wordsLib.SIZES_ss] >>
  once_rewrite_tac[ghost_blocks_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``ghost_blocks``]) >>
  once_rewrite_tac[ghost_blocks_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``ghost_blocks``]) >>
  once_rewrite_tac[ghost_blocks_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``ghost_blocks``]) >>
  once_rewrite_tac[ghost_blocks_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``ghost_blocks``]) >>
  once_rewrite_tac[ghost_blocks_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``ghost_blocks``]) >>
  once_rewrite_tac[ghost_blocks_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``ghost_blocks``]) >>
  once_rewrite_tac[ghost_blocks_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``ghost_blocks``]) >>
  once_rewrite_tac[ghost_blocks_def] >> EVAL_TAC >>
  simp[SUBSET_DEF, FORALL_PROD]
QED

Theorem pop_bulk_header_robust:
  !mem. mem_agree_outside {63} pop_bulk_start.vs_memory mem ==>
    val_in_memory pop_bulk_tv (ArrayV (TupleV [ArrayV (DynArrayV [])])) 0 mem
Proof
  rpt strip_tac >>
  simp[pop_bulk_tv_def, val_in_memory_def] >>
  `mem_bytes_at 0 32 mem = mem_bytes_at 0 32 pop_bulk_start.vs_memory` by
    (irule LIST_EQ >> simp[] >> rpt strip_tac >> rename1 `j < 32` >>
     `mem_bytes_at j 1 pop_bulk_start.vs_memory = mem_bytes_at j 1 mem` by
       (fs[mem_agree_outside_def] >> first_x_assum irule >> simp[]) >>
     qpat_x_assum `mem_bytes_at _ 1 _ = mem_bytes_at _ 1 _` mp_tac >>
     simp[LIST_EQ_REWRITE, EL_mem_bytes_at]) >>
  `mem_word_at 0 mem = mem_word_at 0 pop_bulk_start.vs_memory` by
    asm_simp_tac bool_ss [mem_word_at_def, GSYM mem_bytes_at_def] >>
  simp[] >> EVAL_TAC >> simp[SF wordsLib.SIZES_ss] >> EVAL_TAC
QED

Theorem pop_bulk_rhs_ptr_mem:
  !cx. ptr_mem_ok cx pop_bulk_ty
    (ArrayV (TupleV [ArrayV (DynArrayV [])])) (Var "%src")
    (FEMPTY |+ ("%src", (0,96))) pop_bulk_taint pop_bulk_start
Proof
  gen_tac >> rewrite_tac[ptr_mem_ok_def] >> rpt gen_tac >> strip_tac >>
  gvs[pop_bulk_ty_def, evaluate_type_def, pop_bulk_start_def,
      eval_operand_def, update_var_def, lookup_var_def, init_venom_state_def,
      type_slot_size_def, pop_bulk_taint_def, FLOOKUP_UPDATE] >>
  conj_tac
  >- (gen_tac >> strip_tac >>
      mp_tac (Q.SPEC `mem` pop_bulk_header_robust) >>
      gvs[pop_bulk_start_def, pop_bulk_tv_def, update_var_def, init_venom_state_def]) >>
  EVAL_TAC
QED

Theorem pop_bulk_observer_before:
  !st. pop_region_taint_ok st 1
    (ArrayTV (BaseTV (UintT 256)) (Dynamic 1)) pop_bulk_taint.t_stor
Proof
  simp[pop_region_taint_ok_def, pop_bulk_taint_def, entry_taint_def]
QED

Theorem pop_bulk_observer_after:
  !st. ~pop_region_taint_ok st 1
    (ArrayTV (BaseTV (UintT 256)) (Dynamic 1))
    (SND (ghost_run 10 (mk_venom_context [] NONE) pop_bulk_fn []
      FEMPTY pop_bulk_taint pop_bulk_start)).t_stor
Proof
  gen_tac >> rewrite_tac[pop_region_taint_ok_def] >> strip_tac >>
  first_x_assum (qspecl_then [`1w`, `31`] mp_tac) >>
  simp[pop_bulk_taint_imported, type_slot_size_def, dead_bytes_def]
QED

Theorem pop_bulk_rhs_ptr_val:
  !cx. ptr_val_ok cx pop_bulk_ty
    (ArrayV (TupleV [ArrayV (DynArrayV [])])) (Var "%src")
    (FEMPTY |+ ("%src", (0,96))) pop_bulk_taint pop_bulk_start
Proof
  simp[ptr_val_ok_def, pop_bulk_rhs_ptr_mem, pop_bulk_taint_def,
       op_taint_def, entry_taint_def, FLOOKUP_DEF]
QED

Theorem pop_bulk_rhs_ptr_buf:
  !cenv e. lowered_value_type cenv e = pop_bulk_ty ==>
    ptr_buf_ok cenv e (Var "%src")
      (FEMPTY |+ ("%src", (0,96))) pop_bulk_start
Proof
  rpt strip_tac >> simp[ptr_buf_ok_def, pop_bulk_start_def,
    eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  EVAL_TAC
QED

(* This is the global root's deadness, not source apply_writes agreement.
   In contrast pop_bulk_observer_after observes the saved child at base 1. *)
Theorem pop_bulk_import_globally_dead:
  !st. lookup_storage 0w st = 0w ==>
    dead_bytes st 0 pop_bulk_tv 1 31
Proof
  simp[pop_bulk_tv_def, dead_bytes_def, type_slot_size_def]
QED

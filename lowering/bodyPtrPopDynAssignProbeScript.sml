Theory bodyPtrPopDynAssignProbe
Ancestors
  bodyPtrPopBulkCopy stmtLowering vyperCompiler ptrSafeRun
  venomExecSemantics finite_map ptrDiscipline

(* Diagnostic fixture for the proposed three-DynArray source assignment.
   Unlike the tuple bulk-copy fixture, Assign supplies dynarray_info. *)
Definition pop_dyn_assign_ty_def:
  pop_dyn_assign_ty = ArrayT
    (ArrayT (ArrayT (BaseT (UintT 256)) (Dynamic 1)) (Dynamic 1)) (Dynamic 1)
End

Theorem pop_dyn_assign_layout:
  !cenv. type_memory_bytes cenv pop_dyn_assign_ty = 128 /\
    (case pop_dyn_assign_ty of
       ArrayT elem_ty (Dynamic n) =>
         SOME ((type_memory_bytes cenv elem_ty + 31) DIV 32,
               type_memory_bytes cenv elem_ty)
     | _ => NONE) = SOME (3,96)
Proof
  gen_tac >> EVAL_TAC
QED

Definition pop_dyn_assign_compiled_def:
  pop_dyn_assign_compiled = SND (compile_assign_value ARB (Lit 0w) LocStorage
    (Var "%src") F (SOME LocMemory) pop_dyn_assign_ty pop_dyn_assign_ty
    (SOME (3,96)) 128 (initial_compile_state "entry"))
End

Theorem pop_dyn_assign_branch:
  pop_dyn_assign_compiled = SND (compile_dynarray_to_storage
    (Var "%src") (Lit 0w) 3 96 F (initial_compile_state "entry"))
Proof
  EVAL_TAC
QED

Definition pop_dyn_assign_fn_def:
  pop_dyn_assign_fn = mk_raw_function "entry"
    (REVERSE pop_dyn_assign_compiled.cs_blocks ++
     [<| bb_label := pop_dyn_assign_compiled.cs_current_bb;
         bb_instructions := pop_dyn_assign_compiled.cs_current_insts ++
                            [mk_inst 100 STOP [] []] |>])
End

Theorem pop_dyn_assign_empty_exec:
  ?s. run_from 10 (mk_venom_context [] NONE) pop_dyn_assign_fn pop_bulk_start = Halt s /\
      sload 0w s = 0w /\ sload 1w s = 0w
Proof
  CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV pop_dyn_assign_fn_def THENC EVAL)) >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``run_blocks``]) >>
  simp[SF wordsLib.SIZES_ss] >>
  once_rewrite_tac[run_blocks_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``run_blocks``]) >>
  once_rewrite_tac[run_blocks_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``run_blocks``]) >>
  once_rewrite_tac[run_blocks_def] >> EVAL_TAC >> simp[] >> EVAL_TAC
QED

Theorem pop_dyn_assign_empty_taint:
  (SND (ghost_run 10 (mk_venom_context [] NONE) pop_dyn_assign_fn []
    FEMPTY pop_bulk_taint pop_bulk_start)).t_stor = {}
Proof
  CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV pop_dyn_assign_fn_def THENC EVAL)) >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``ghost_blocks``]) >>
  simp[SF wordsLib.SIZES_ss] >>
  once_rewrite_tac[ghost_blocks_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``ghost_blocks``]) >>
  once_rewrite_tac[ghost_blocks_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``ghost_blocks``]) >>
  once_rewrite_tac[ghost_blocks_def] >> EVAL_TAC >>
  simp[]
QED

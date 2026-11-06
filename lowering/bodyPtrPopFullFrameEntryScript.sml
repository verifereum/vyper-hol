Theory bodyPtrPopFullFrameEntry
Ancestors
  bodyPtrPopFullFrameRuntime bodyPtrPopFullFrameGas bodyPtrPopFullFrameProbe
  bodyPtrDefs ptrDiscipline venomState exprLoweringProps

(* The prefix ALLOCA at id 9 produced %6 at base zero with size 32.
   Naming its provenance keeps the concrete entry certificate readable. *)
Definition pop_full_frame_G_def:
  pop_full_frame_G = FEMPTY |+ ("%6",(0,32))
End

Theorem pop_full_frame_ghost_inv:
  ghost_inv NONE pop_full_frame_body_env pop_full_frame_cx pop_full_frame_es
    pop_full_frame_G entry_taint pop_full_frame_ss
Proof
  simp[ghost_inv_def, pop_full_frame_vars, return_buf_ptr_def,
       pop_full_frame_return_buf, pop_full_frame_specials,
       op_taint_def, entry_taint_def, stor_taint_ok_def]
QED

Theorem pop_full_frame_no_dalloca:
  ~ctx_has_dalloca pop_full_frame_context
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, vyperValueTheory.type_slot_size_def] >>
  EVAL_TAC
QED

Theorem pop_full_frame_pc:
  ~pop_full_frame_ss.vs_halted /\
  pop_full_frame_ss.vs_current_bb = pop_full_frame_start.cs_current_bb /\
  pop_full_frame_ss.vs_inst_idx = LENGTH pop_full_frame_start.cs_current_insts
Proof
  EVAL_TAC
QED

Theorem pop_full_frame_compile_expr:
  compile_expr pop_full_frame_body_env (BaseT (UintT 256))
    pop_full_frame_expr pop_full_frame_start =
    (FST pop_full_frame_compiled, SND pop_full_frame_compiled)
Proof
  simp[pop_full_frame_compiled_def]
QED

(* Exactly the antecedents of expr_vv_sim_ptr, in their original order. *)
Theorem pop_full_frame_vv_entry:
  compile_expr pop_full_frame_body_env (BaseT (UintT 256))
    pop_full_frame_expr pop_full_frame_start =
    (FST pop_full_frame_compiled, SND pop_full_frame_compiled) /\
  fn_has_code pop_full_frame_start (SND pop_full_frame_compiled) pop_full_frame_fn /\
  fn_inst_ids_distinct pop_full_frame_fn /\
  local_ptrs_reserved pop_full_frame_body_env pop_full_frame_start /\
  ~ctx_has_dalloca pop_full_frame_context /\
  ~pop_full_frame_body_env.ce_is_ctor /\
  (!x sz. pop_full_frame_body_env.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at pop_full_frame_start x) /\
  (!x sz. pop_full_frame_body_env.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at pop_full_frame_start x) /\
  gas_admissible (eval_expr pop_full_frame_cx pop_full_frame_expr)
    expr_vv_res_ok pop_full_frame_es /\
  stmt_state_rel pop_full_frame_context pop_full_frame_fn pop_full_frame_body_env
    pop_full_frame_cx pop_full_frame_es pop_full_frame_ss /\
  ghost_inv NONE pop_full_frame_body_env pop_full_frame_cx pop_full_frame_es
    pop_full_frame_G entry_taint pop_full_frame_ss /\
  ~pop_full_frame_ss.vs_halted /\
  pop_full_frame_ss.vs_current_bb = pop_full_frame_start.cs_current_bb /\
  pop_full_frame_ss.vs_inst_idx = LENGTH pop_full_frame_start.cs_current_insts
Proof
  simp[pop_full_frame_compile_expr, pop_full_frame_fragment, pop_full_frame_ids,
       pop_full_frame_reservations, pop_full_frame_no_dalloca,
       pop_full_frame_vv_gas_admissible, pop_full_frame_stmt_state_rel,
       pop_full_frame_ghost_inv, pop_full_frame_pc] >>
  metis_tac[pop_full_frame_reservations]
QED

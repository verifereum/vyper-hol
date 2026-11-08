Theory bodyPtrBytestringBuiltinsSignedFrame
Ancestors
  bodyPtrBytestringBuiltinsSignedTailProbe bodyPtrBytestringBuiltinsRuntime
  bodySim vyperTypeInvariants bodyPtrBytestringBuiltinsPtrFrame
  bodyPtrBytestringBuiltinsSliceGuardFrame

(* One coherent source fixture; all other environment fields retain the
   checked empty-module frame. A named local cannot alias numbered temporaries. *)
Definition signed_frame_env_def:
  signed_frame_env = order_ptr_env with
    <|ce_vars := FEMPTY |+ ("b", PtrVar (Var "b_ptr") 64);
      ce_var_type := (\n. if n = "b" then SOME (BaseT (BytesT (Dynamic 1))) else NONE)|>
End

Definition signed_frame_tenv_def:
  signed_frame_tenv = order_ptr_tenv with
    <|var_types := FEMPTY |+ ("b", BaseT (BytesT (Dynamic 1)));
      var_assignable := FEMPTY |+ ("b", T)|>
End

Definition signed_frame_scopes_def:
  signed_frame_scopes = [FEMPTY |+ ("b", <|assignable := T;
    type := BaseTV (BytesT (Dynamic 1)); value := BytesV []; popped := []|>)]
End

Definition signed_frame_source_def:
  signed_frame_source = order_ptr_source with scopes := signed_frame_scopes
End

Definition signed_frame_expr_def:
  signed_frame_expr = Builtin (BaseT (BytesT (Dynamic 1))) (Slice 1)
    [slice_guard_source; signed_tail; Literal (BaseT (UintT 256)) (IntL 1)]
End

Theorem signed_frame_body_inv:
  body_inv [] order_frame_unit.cu_context signed_frame_env order_runtime_cx
Proof
  mp_tac order_runtime_body_inv >> simp[body_inv_def, signed_frame_env_def] >>
  metis_tac[]
QED

Theorem signed_frame_typed:
  well_typed_expr signed_frame_tenv signed_frame_expr
Proof
  simp[signed_frame_expr_def] >> irule signed_tail_slice_typed >>
  simp[signed_frame_tenv_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem signed_frame_env_consistent:
  env_consistent signed_frame_tenv order_runtime_cx signed_frame_source
Proof
  simp[env_consistent_def, env_scopes_consistent_def,
       env_context_consistent_def, env_immutables_consistent_def,
       signed_frame_tenv_def, signed_frame_source_def, signed_frame_scopes_def,
       order_ptr_tenv_def, vyperStateTheory.lookup_scopes_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  EVAL_TAC >> simp[finite_mapTheory.FUNION_FEMPTY_1] >>
  rw[] >> gvs[AllCaseEqs()] >> EVAL_TAC >> simp[wordsTheory.dimword_def]
QED

Theorem signed_frame_sim_inv:
  exprSimHypsDefs$expr_sim_inv signed_frame_env order_runtime_cx
    signed_frame_tenv signed_frame_source
Proof
  simp[exprSimHypsDefsTheory.expr_sim_inv_def, signed_frame_env_consistent,
       signed_frame_env_def, signed_frame_tenv_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  EVAL_TAC >> rw[] >> gvs[AllCaseEqs(), vyperStateTheory.lookup_flag_def] >>
  EVAL_TAC >> simp[wordsTheory.dimword_def, finite_mapTheory.FUNION_FEMPTY_1] >>
  fs[vyperInterpreterTheory.lookup_function_def]
QED

Theorem signed_frame_static:
  byte_widths_expr signed_frame_expr /\
  alloc_limits_expr cenv signed_frame_expr /\
  int_calls_expr signed_frame_expr = [] /\ ~expr_has_evm_run signed_frame_expr
Proof
  simp[signed_frame_expr_def, signed_tail_def,
       bodyPtrBytestringBuiltinsSliceGuardFixtureTheory.slice_guard_source_def,
       allocLimitsTheory.alloc_limits_expr_def,
       exprLoweringTheory.is_extcode_def, exprLoweringTheory.extcode_addr_expr_def] >>
  EVAL_TAC >> simp[wordsTheory.dimword_def]
QED

Theorem signed_frame_body_pre:
  exprSimHypsDefs$expr_body_pre signed_frame_env order_runtime_cx
    signed_frame_tenv signed_frame_expr signed_frame_source
Proof
  simp[exprSimHypsDefsTheory.expr_body_pre_def, signed_frame_sim_inv,
       signed_frame_typed, signed_frame_static, order_runtime_call_safety] >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  simp[order_runtime_cx_def, order_ptr_cx_def,
       bodyPtrBytestringBuiltinsSourceFrameTheory.order_frame_cx_def,
       gasContextTheory.cx_tops_def, vyperContextTheory.get_tenv_def,
       vyperContextTheory.get_module_code_def] >> EVAL_TAC >> simp[]
QED

(* The local is a caller-owned buffer below the allocation frontier, so no
   invented prior instruction id is required in the running frame. *)
Definition signed_frame_start_def:
  signed_frame_start = order_runtime_start with
    <|vs_vars := FEMPTY |+ ("b_ptr", 0w); vs_memory := REPLICATE 64 0w;
      vs_allocas := FEMPTY; vs_alloca_next := 64; vs_fmp := 64w|>
End

Theorem signed_frame_reserved:
  local_ptrs_reserved signed_frame_env (initial_compile_state "entry")
Proof
  simp[compileEnvTheory.local_ptrs_reserved_def, signed_frame_env_def,
       compileEnvTheory.not_fresh_at_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  EVAL_TAC >> simp[]
QED

Theorem signed_frame_ghost:
  ghost_inv NONE signed_frame_env order_runtime_cx signed_frame_source
    (FEMPTY |+ ("b_ptr", (0,64))) signed_probe_taint signed_frame_start
Proof
  irule signed_empty_local_ghost >>
  simp[signed_frame_source_def, signed_frame_scopes_def,
       signed_frame_env_def, signed_frame_start_def, signed_probe_taint_def,
       ptrDisciplineTheory.entry_taint_def,
       vyperStateTheory.lookup_scopes_def, venomStateTheory.lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  EVAL_TAC >> simp[]
QED

Theorem signed_frame_local_ptrs:
  local_ptrs_rel func signed_frame_env signed_frame_source.scopes signed_frame_start
Proof
  simp[compileEnvTheory.local_ptrs_rel_def, compileEnvTheory.local_region_def,
       signed_frame_env_def, signed_frame_source_def, signed_frame_scopes_def,
       vyperStateTheory.lookup_scopes_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rw[] >> gvs[] >> qexists_tac `0w` >>
  simp[signed_frame_start_def, compileEnvTheory.local_backed_def,
       venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  EVAL_TAC >> simp[wordsTheory.dimword_def]
QED

Theorem signed_frame_state_rel:
  state_rel func signed_frame_env order_runtime_cx signed_frame_source signed_frame_start
Proof
  simp[compileEnvTheory.state_rel_def, signed_frame_local_ptrs,
       signed_frame_start_def, order_runtime_call_context] >>
  EVAL_TAC >> rw[] >> gvs[]
QED

Theorem signed_frame_source_fails:
  !cx es. eval_expr cx signed_frame_expr es =
    (INR (Error (RuntimeError "Div0")), es)
Proof
  rpt gen_tac >> EVAL_TAC >> simp[vyperStateTheory.return_def]
QED

Theorem signed_frame_gas_admissible:
  gas_admissible (bind (eval_expr order_runtime_cx signed_frame_expr)
    (read_result order_runtime_cx)) expr_res_ok signed_frame_source
Proof
  simp[gasContextTheory.gas_admissible_def, signed_frame_source_fails,
       vyperStateTheory.bind_def, exprSimDefsTheory.expr_res_ok_def]
QED

Theorem signed_frame_args:
  builtin_args_length_ok (Slice 1) 3 /\
  body_exprs_ptr_ok order_runtime_cx
    [slice_guard_source; signed_tail; Literal (BaseT (UintT 256)) (IntL 1)]
Proof
  simp[slice_guard_arity, slice_guard_args_ptr_ok]
QED

Theorem signed_frame_entry:
  ~signed_frame_start.vs_halted /\
  signed_frame_start.vs_current_bb = (initial_compile_state "entry").cs_current_bb /\
  signed_frame_start.vs_inst_idx = LENGTH (initial_compile_state "entry").cs_current_insts /\
  ~signed_frame_env.ce_is_ctor /\
  signed_frame_env.ce_return_buf = NONE /\ signed_frame_env.ce_return_pc = NONE
Proof
  EVAL_TAC
QED

Theorem signed_frame_alloca_inv:
  alloca_inv signed_frame_start
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def]
QED

Theorem signed_frame_immutable:
  immutable_alloca_sep func signed_frame_env order_runtime_cx
    signed_frame_source signed_frame_start /\
  immutable_base_zero signed_frame_env signed_frame_start
Proof
  simp[exprLoweringPropsTheory.immutable_alloca_sep_def, signed_frame_entry,
       exprLoweringPropsTheory.immutable_base_zero_alt, signed_frame_env_def] >>
  EVAL_TAC >> simp[]
QED

Theorem signed_frame_alloca_sizes:
  !inst n base sz.
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit n] /\
    FLOOKUP signed_frame_start.vs_allocas inst.inst_id = SOME (base,sz) ==>
    sz = w2n n
Proof
  simp[signed_frame_start_def, finite_mapTheory.FLOOKUP_DEF]
QED

Theorem signed_frame_no_dalloca:
  ~ctx_has_dalloca order_frame_unit.cu_context
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def,
    vyperCompilerTheory.EVERY_fn_insts_blocks]
QED

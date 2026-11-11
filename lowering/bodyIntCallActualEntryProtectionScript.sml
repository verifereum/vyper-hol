(* Protected resources at actual entry, with the installed immutable operand. *)
Theory bodyIntCallActualEntryProtection
Ancestors
  bodyIntCallActualEntryLanding bodyIntCallActualEntryWitness
  bodyIntCallActualEntryResource bodyIntCallActualEntryFields
  intCallCallee intCallFrame loweringPosts compileEnv loweringStateRelDefs exprLoweringProps
  context finite_map list

Theorem internal_entry_landing_allocas_above:
  compile_internal_function_entry ce params has_rb ctor imm_len rt st0 =
    ((ce2,rpc,imm),st1) /\
  fn_has_code st0 st1 func /\ fn_inst_ids_distinct func /\
  setup_callee func args caller = SOME s0 /\
  internal_args_rel ce params env (if has_rb then 1 else 0) args
    caller.vs_alloca_next caller.vs_memory /\
  caller.vs_alloca_next + internal_stack_size ce params < dimword (:256) /\
  run_inst_seq (emitted_insts st0 st1) s0 = OK u ==>
  allocas_above caller.vs_alloca_next u
Proof
  strip_tac >> drule_all internal_entry_landing_resources >> strip_tac >>
  fs[mat_inv_def, allocas_above_def] >> rpt strip_tac >>
  first_x_assum irule >> goal_assum drule
QED

Theorem internal_entry_landing_return_buf:
  compile_internal_function_entry ce params has_rb ctor imm_len rt st0 =
    ((ce2,rpc,imm),st1) /\
  fn_has_code st0 st1 func /\ fn_inst_ids_distinct func /\
  setup_callee func args caller = SOME s0 /\
  internal_args_rel ce params env (if has_rb then 1 else 0) args
    caller.vs_alloca_next caller.vs_memory /\
  caller.vs_alloca_next + internal_stack_size ce params < dimword (:256) /\
  run_inst_seq (emitted_insts st0 st1) s0 = OK u /\
  (has_rb ==> (?off sz. ce.ce_return_buf = SOME (MemLoc off sz)) /\
    w2n (HD args) + capacity <= caller.vs_alloca_next) /\
  (~has_rb ==> ce.ce_return_buf = NONE) ==>
  return_buf_frame (if has_rb then SOME (HD args,capacity) else NONE)
    (ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|>) st1 u
Proof
  strip_tac >> drule_all internal_entry_operand_landing >> strip_tac >>
  drule_all internal_entry_landing_resources >> strip_tac >>
  Cases_on `has_rb`
  >- (gvs[] >>
      fs[return_buf_frame_def, mat_inv_def] >>
      goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
  gvs[] >> drule internal_entry_no_return_buffer >> simp[return_buf_frame_def]
QED

Theorem internal_entry_installed_protection:
  compile_internal_function_entry ce params has_rb ctor imm_len rt st0 =
    ((ce2,rpc,imm),st1) /\
  fn_has_code st0 st1 func /\ fn_inst_ids_distinct func /\
  setup_callee func args caller = SOME s0 /\
  internal_args_rel ce params env (if has_rb then 1 else 0) args
    caller.vs_alloca_next caller.vs_memory /\
  caller.vs_alloca_next + internal_stack_size ce params < dimword (:256) /\
  run_inst_seq (emitted_insts st0 st1) s0 = OK u /\
  (!a k. P a k ==> a + k <= caller.vs_alloca_next) /\
  (!a k. P a k ==>
    mem_bytes_at a k s0.vs_memory = mem_bytes_at a k origin.vs_memory) /\
  (!i off sz. i < LENGTH params /\ ~SND (EL i params) /\
    FLOOKUP ce.ce_vars (FST (EL i params)) = SOME (MemLoc off sz) ==>
    ?b z. staged b z /\
      b <= w2n (EL ((if has_rb then 1 else 0) + i) args) /\
      w2n (EL ((if has_rb then 1 else 0) + i) args) + sz <= b + z) ==>
  (!a k. P a k ==>
    mem_bytes_at a k u.vs_memory = mem_bytes_at a k origin.vs_memory) /\
  (!n p k. local_region
    (ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|>) [env] u n p k ==>
    caller.vs_alloca_next <= p \/
    ?b z. staged b z /\ b <= p /\ p + k <= b + z)
Proof
  strip_tac >> drule_all internal_entry_protected_landing >> strip_tac >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `!n p k. local_region _ _ _ _ _ _ ==> _` mp_tac >>
  simp[local_region_def]
QED

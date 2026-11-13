(* A resource-contract probe, not a counterexample to expression simulation. *)
Theory exprSimAbiEncodeResourceProbe
Ancestors
  exprSimAbiEncodeBoundaryProbe builtinAbi vyperCompiler
  abiDecoderAllocation exprLoweringProps finite_map pred_set words arithmetic
  fcgDefs relation venomMemDefs venomInst list

Definition resource_probe_end_def:
  resource_probe_end = SND (lower_abi_encode F NONE (Var "src")
    AbiPrimWord 32 (initial_compile_state "entry"))
End

Theorem resource_probe_inventory:
  resource_probe_end.cs_next_id = 5 /\
  MAP (\i. (i.inst_id,i.inst_opcode)) resource_probe_end.cs_current_insts =
    [(0,ALLOCA);(1,ADD);(2,MLOAD);(3,MSTORE);(4,MSTORE)]
Proof
  EVAL_TAC
QED

Definition resource_probe_func_def:
  resource_probe_func = (ARB:ir_function) with <|
    fn_name := "probe";
    fn_blocks := emitted_blocks (initial_compile_state "entry") resource_probe_end |>
End

Definition resource_probe_state_def:
  resource_probe_state = (ARB:venom_state) with <|
    vs_allocas := FEMPTY |+ (0,(0,64));
    vs_alloca_next := dimword (:256) - 1 |>
End

Theorem resource_probe_pending:
  pending_alloca_size resource_probe_func resource_probe_state = 0
Proof
  EVAL_TAC
QED

Theorem resource_probe_missing_site:
  first <= 2 /\ 5 <= last ==>
  4 IN abi_decoder_missing first last resource_probe_state
Proof
  simp[abi_decoder_missing_def, abi_decoder_ids_def,
       resource_probe_state_def]
QED

Theorem resource_probe_credit_failure:
  first <= 2 /\ 5 <= last ==>
  ~(32 * CARD (abi_decoder_missing first last resource_probe_state) <=
    pending_alloca_size resource_probe_func resource_probe_state)
Proof
  strip_tac >> drule_all resource_probe_missing_site >> strip_tac >>
  `CARD (abi_decoder_missing first last resource_probe_state) <> 0` by
    (simp[CARD_EQ_0] >> metis_tac[NOT_IN_EMPTY]) >>
  simp[resource_probe_pending]
QED

Theorem resource_probe_no_budget:
  ~(?first last b cap. 0 < first /\ first <= 2 /\ 5 <= last /\
      abi_decoder_budget first last b cap resource_probe_state)
Proof
  strip_tac >> drule_all resource_probe_missing_site >> strip_tac >>
  `CARD (abi_decoder_missing first last resource_probe_state) <> 0` by
    (simp[CARD_EQ_0] >> metis_tac[NOT_IN_EMPTY]) >>
  qpat_x_assum `abi_decoder_budget _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[abi_decoder_budget_def] >> strip_tac >>
  `resource_probe_state.vs_alloca_next = dimword (:256) - 1` by
    simp_tac (srw_ss()) [resource_probe_state_def] >>
  qpat_x_assum `_ + 32 * _ <= _` mp_tac >>
  asm_rewrite_tac[] >> decide_tac
QED

Theorem resource_probe_frontier_room:
  resource_probe_state.vs_alloca_next +
    pending_alloca_size resource_probe_func resource_probe_state < dimword (:256)
Proof
  rewrite_tac[resource_probe_pending] >> EVAL_TAC >> simp[]
QED

Theorem resource_probe_no_invokes:
  !i. MEM i (fn_insts resource_probe_func) ==> i.inst_opcode <> INVOKE
Proof
  EVAL_TAC >> rpt strip_tac >> gvs[]
QED

Definition resource_probe_context_def:
  resource_probe_context = ARB with
    ctx_functions := [resource_probe_func]
End

Theorem resource_probe_no_edges:
  !a b. ~fn_directly_calls resource_probe_context a b
Proof
  simp[fn_directly_calls_def, resource_probe_context_def,
       lookup_function_def, FIND_thm, AllCaseEqs()] >>
  metis_tac[resource_probe_no_invokes]
QED

Theorem resource_probe_no_paths:
  !a b. ~TC (fn_directly_calls resource_probe_context) a b
Proof
  `!a b. TC (fn_directly_calls resource_probe_context) a b ==> F`
    suffices_by metis_tac[] >>
  ho_match_mp_tac TC_INDUCT >> simp[resource_probe_no_edges]
QED

Theorem resource_probe_room:
  alloca_room resource_probe_context resource_probe_func resource_probe_state
Proof
  simp[alloca_room_def, resource_probe_no_paths, resource_probe_context_def,
       lookup_function_def, FIND_thm, resource_probe_frontier_room]
QED

Theorem resource_probe_alloca_inv:
  alloca_inv resource_probe_state
Proof
  EVAL_TAC >> rpt strip_tac >> gvs[] >> simp[dimword_def]
QED

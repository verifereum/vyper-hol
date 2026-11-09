(* Scratch safety requires the recorded allocation to have size 32. *)
Theory bodyMemBiKeccakScratch
Ancestors
  context list exprSimAlloc bodyMemBiKeccakSuffix allocaFootprint builtinHashing emitHelper
  emitHelperProps exprLoweringProps fragExecMem instMemFrontier compileEnv loweringStateRelDefs
  venomInst abiBuiltinAllocation venomState venomExecSemantics venomMemDefs words finite_map

Theorem keccak_fixed_site_mem_ok:
  compile_keccak256_bytesm x m sa = (op,sb) /\ m <= 32 /\
  (!v. x = Var v ==> not_fresh_at sa v) /\
  eval_operand x s = SOME w /\ alloca_next_valid s /\
  FLOOKUP (abi_builtin_allocate_state sa.cs_next_id 32 s).vs_allocas
    sa.cs_next_id = SOME (p,32) /\
  p + 32 < dimword (:256) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  simp[compile_keccak256_bytesm_def, compile_alloc_buffer_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emit_op_def, emit_void_def, fresh_id_def, fresh_var_def, emit_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `!k. LENGTH sa.cs_current_insts - (LENGTH sa.cs_current_insts + k) = 0`
    by decide_tac >>
  qpat_x_assum `_ with <| cs_next_var := _; cs_next_id := _;
      cs_current_insts := _ |> = sb` (SUBST1_TAC o SYM) >>
  simp[emitted_insts_def, DROP_APPEND] >>
  `32 < dimword (:256)` by simp[dimword_def] >>
  drule_all step_alloca_site >>
  disch_then (qspec_then `STRING #"%" (toString sa.cs_next_var)` assume_tac) >>
  drule_all alloca_site_frontier >> strip_tac >>
  simp[run_inst_seq_mem_ok_cons] >>
  conj_tac >- (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  `eval_operand x
    (update_var (STRING #"%" (toString sa.cs_next_var)) (n2w p)
      (abi_builtin_allocate_state sa.cs_next_id 32 s)) = SOME w` by
    (irule eval_operand_update_other_local >> simp[] >>
     rpt strip_tac >> first_x_assum drule >> simp[not_fresh_at_def]) >>
  `p < dimword (:256)` by decide_tac >>
  `eval_operand (Var (STRING #"%" (toString sa.cs_next_var)))
    (update_var (STRING #"%" (toString sa.cs_next_var)) (n2w p)
      (abi_builtin_allocate_state sa.cs_next_id 32 s)) = SOME (n2w p)` by
    simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `p + 32 <= (update_var (STRING #"%" (toString sa.cs_next_var)) (n2w p)
    (abi_builtin_allocate_state sa.cs_next_id 32 s)).vs_alloca_next` by
    simp[update_var_def] >>
  qpat_assum `eval_operand (Var _) _ = SOME (n2w p)`
    (mp_then (Pos hd) mp_tac scratch_mstore_mem_ok) >>
  disch_then (qspecl_then [`sa.cs_next_id + 1`, `x`, `w`] mp_tac) >>
  simp[] >> strip_tac >>
  simp[run_inst_seq_mem_ok_last, below_frontier_SHA3] >>
  `m < dimword (:256)` by decide_tac >>
  simp[eval_operand_def] >> disj2_tac >> decide_tac
QED

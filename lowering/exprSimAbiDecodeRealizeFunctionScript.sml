Theory exprSimAbiDecodeRealizeFunction
Ancestors
  exprSimAbiDecodeRealizeFootprint exprSimAbiDecodeRealizeSource
  exprLoweringProps exprLowering vyperCompiler venomInst venomWf
  fcgDefs compileEnv list finite_map

Definition abi_decode_realize_final_def:
  abi_decode_realize_final ce k entry =
    SND (compile_expr ce (expr_type (abi_decode_realize_expr k))
      (abi_decode_realize_expr k) (initial_compile_state entry))
End

(* No terminator is required by expr_vv_sim's fn_has_code antecedent.
   Keep the last block open at precisely the compiler's end cursor. *)
Definition abi_decode_realize_function_def:
  abi_decode_realize_function ce k entry =
    let st = abi_decode_realize_final ce k entry in
    mk_raw_function entry (REVERSE st.cs_blocks ++
      [<|bb_label := st.cs_current_bb; bb_instructions := st.cs_current_insts|>])
End

Definition abi_decode_realize_context_def:
  abi_decode_realize_context ce k entry =
    mk_venom_context [abi_decode_realize_function ce k entry] (SOME entry)
End

Theorem abi_decode_realize_blocks_flat[local]:
  !bs. fn_insts_blocks bs = FLAT (MAP (\b. b.bb_instructions) bs)
Proof
  Induct >> simp[fn_insts_blocks_def]
QED

Theorem abi_decode_realize_function_code:
  fn_insts (abi_decode_realize_function ce k entry) =
    abi_decode_realize_code (abi_decode_realize_final ce k entry)
Proof
  simp[abi_decode_realize_function_def, fn_insts_def, abi_decode_realize_blocks_flat,
       mk_raw_function_def, abi_decode_realize_code_def]
QED

Theorem abi_decode_realize_function_charge:
  abi_decode_realize_alloc_charge (fn_insts (abi_decode_realize_function ce k entry)) = 128
Proof
  simp[abi_decode_realize_function_code, abi_decode_realize_final_def,
       abi_decode_realize_expr_charge]
QED

Theorem abi_decode_realize_function_no_dynamic_or_invoke:
  MEM i (fn_insts (abi_decode_realize_function ce k entry)) ==>
  i.inst_opcode <> DALLOCA /\ i.inst_opcode <> INVOKE
Proof
  simp[abi_decode_realize_function_code, abi_decode_realize_final_def] >>
  metis_tac[abi_decode_realize_expr_no_dynamic_or_invoke]
QED

Theorem abi_decode_realize_function_lookup:
  lookup_function (abi_decode_realize_function ce k entry).fn_name
    (abi_decode_realize_context ce k entry).ctx_functions =
  SOME (abi_decode_realize_function ce k entry)
Proof
  simp[abi_decode_realize_context_def, mk_venom_context_def,
       lookup_function_def, FIND_thm]
QED

Theorem abi_decode_realize_alloca_size_eq[local]:
  alloca_lit_size = alloca_size
Proof
  simp[FUN_EQ_THM, alloca_lit_size_def, alloca_size_def]
QED

Theorem abi_decode_realize_function_frame:
  unit_alloca_frame (abi_decode_realize_context ce k entry) = 128
Proof
  simp[unit_alloca_frame_def, abi_decode_realize_context_def, mk_venom_context_def] >>
  mp_tac abi_decode_realize_function_charge >>
  simp[abi_decode_realize_alloc_charge_def, abi_decode_realize_alloca_size_eq]
QED

Theorem abi_decode_realize_function_pending_bound:
  pending_alloca_size (abi_decode_realize_function ce k entry) ss <= 128
Proof
  mp_tac pending_alloca_size_le_frame >>
  disch_then (qspecl_then [`abi_decode_realize_context ce k entry`,
    `abi_decode_realize_function ce k entry`, `ss`] mp_tac) >>
  simp[abi_decode_realize_context_def, mk_venom_context_def,
       abi_decode_realize_function_frame]
QED

Theorem abi_decode_realize_function_pending_empty:
  ss.vs_allocas = FEMPTY ==>
  pending_alloca_size (abi_decode_realize_function ce k entry) ss = 128
Proof
  strip_tac >> simp[pending_alloca_size_def] >>
  mp_tac abi_decode_realize_function_charge >>
  simp[abi_decode_realize_alloc_charge_def, abi_decode_realize_alloca_size_eq]
QED

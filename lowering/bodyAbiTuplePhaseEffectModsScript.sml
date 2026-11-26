(* Introduce a linked row effect at the actual endpoint of one window phase. *)
Theory bodyAbiTuplePhaseEffectMods
Ancestors
  bodyAbiTupleBufferStateMods abiEncoderWindowPhase abiEncoderWindowContract
  exprSimAbiEncodeExecFrame exprLoweringProps compileEnv loweringStateRelDefs
  ptrDiscipline venomState venomInst finite_map pred_set list

Theorem abi_tuple_phase_effect_mods:
  ci_mono a c /\ window_phase ctx func a c ids outs u v /\
  abi_encode_exec_frame func u v /\
  (!x. not_fresh_at a x ==>
    FLOOKUP Gv x = FLOOKUP Gu x /\ op_taint tv (Var x) = op_taint tu (Var x)) /\
  tv.t_stor = tu.t_stor /\ tv.t_trans = tu.t_trans /\ tv.t_imm = tu.t_imm /\
  shared NOTIN ids /\
  EVERY (\(b,n). pbase+dst_offset <= b /\ b+n <= pbase+capacity) outs /\
  (cursor_site IN ids ==>
    cursor_site < c.cs_next_id /\ ?slot. FLOOKUP v.vs_allocas cursor_site = SOME (slot,32)) /\
  (!aid. aid IN ids ==>
    (aid <> cursor_site ==> a.cs_next_id <= aid /\ aid < c.cs_next_id) /\
    ?inst x. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id = aid /\ inst.inst_outputs = [x] /\ not_local_ptr ce ee.scopes x) /\
  (!i. EVERY (\(b,n). i < b \/ b+n <= i) outs /\
    (!aid b n. aid IN ids /\ FLOOKUP v.vs_allocas aid = SOME (b,n) ==>
      i < b \/ b+n <= i) /\ i IN tv.t_mem ==> i IN tu.t_mem) ==>
  abi_tuple_row_effects_mods ce ee func shared pbase capacity dst_offset cursor_site
    a u Gu tu c v Gv tv
Proof
  strip_tac >>
  drule window_phase_resources >> strip_tac >>
  drule window_phase_effect >> strip_tac >>
  pure_rewrite_tac[abi_tuple_row_effects_mods_def] >>
  asm_rewrite_tac[] >>
  conj_tac
  >- (rpt strip_tac >> metis_tac[window_phase_vars]) >>
  qexistsl_tac [`ids`, `outs`] >> asm_rewrite_tac[]
QED

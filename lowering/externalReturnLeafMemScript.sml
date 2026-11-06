Theory externalReturnLeafMem
Ancestors
  externalReturnBounds entryHaltMem rawReturnMem fragExecMem bodyMemoryDefs
  stmtSimDefs stmtSimProps loweringPosts exprSimDefs exprSimProps compileEnv stmtLowering rawReturnValue loweringHalt
  fragExec venomExecSemantics venomInst venomMemDefs allocaFootprint
  exprLoweringProps

(* A raw suffix consumes the expression value directly, with no assumption
   about a fresh allocation site or declared bytestring capacity. *)
Theorem external_return_raw_value_mem:
  compile_external_return (SOME op) prim T ei msz F nkey ut iv st =
    (x, st') /\
  (!y. op = Var y ==> not_fresh_at st y) /\
  stmt_state_rel ctx func cenv cx es s /\
  expr_val_at cenv cx ty sa st es v op s /\
  expr_val_rel cx ty v op s /\ is_bytestring_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v ==>
  frag_exec_mem ctx st st' (\t. t = s) (\t. F)
    (\r. ?ss. r = Halt ss)
Proof
  strip_tac >> drule_all expr_val_at_raw_frontier >> strip_tac >>
  irule compile_external_return_raw_unlock_frag_mem >>
  goal_assum (drule_at (Pat `compile_external_return _ _ _ _ _ _ _ _ _ _ = _`)) >>
  qexistsl_tac [`bs`, `p`] >> gvs[]
QED

Theorem return_first_inst_mem[local]:
  fn_has_code st st' func /\ st'.cs_current_bb = st.cs_current_bb /\
  st'.cs_current_insts = st.cs_current_insts ++ inst::tail ==>
  MEM inst (fn_insts func)
Proof
  strip_tac >> drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH st.cs_current_insts) = SOME inst` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  irule lookup_block_fn_insts >> goal_assum drule >>
  gvs[get_instruction_def] >> metis_tac[listTheory.EL_MEM]
QED

Theorem external_return_word_value_mem:
  compile_external_return (SOME op) T F ei msz F nkey ut iv st =
    (x, st') /\ fn_has_code st st' func /\
  (!y. op = Var y ==> not_fresh_at st y) /\
  stmt_state_rel ctx func cenv cx es s /\ eval_operand op s = SOME w ==>
  frag_exec_mem ctx st st' (\t. t = s) (\t. F) (\r. ?ss. r = Halt ss)
Proof
  strip_tac >>
  `?buf. ~not_fresh_at st buf /\
    st'.cs_current_bb = st.cs_current_bb /\
    st'.cs_current_insts = st.cs_current_insts ++
      [mk_inst st.cs_next_id ALLOCA [Lit 32w] [buf];
       mk_inst (st.cs_next_id + 1) MSTORE [Var buf; op] [];
       mk_inst (st.cs_next_id + 2) RETURN [Var buf; Lit 32w] []]` by
    (irule compile_external_return_word_parts >> goal_assum drule >> simp[]) >>
  `MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w] [buf]) (fn_insts func)` by
    (irule return_first_inst_mem >> goal_assum drule >> simp[] >> metis_tac[]) >>
  `?b. FLOOKUP (abi_builtin_allocate_state st.cs_next_id 32 s).vs_allocas
       st.cs_next_id = SOME (b,32)` by
    (drule stmt_state_rel_alloca_site >> disch_then drule >>
     simp[mk_inst_def, wordsTheory.dimword_def]) >>
  irule compile_external_return_word_frag_mem >>
  goal_assum (drule_at (Pat `compile_external_return _ _ _ _ _ _ _ _ _ _ = _`)) >>
  qexists_tac `w` >> gvs[stmt_state_rel_def, alloca_inv_def]
QED

Theorem external_return_static_value_mem:
  compile_external_return (SOME op) F F (AbiCopy m) msz F nkey ut iv st =
    (x, st') /\ fn_has_code st st' func /\
  (!y. op = Var y ==> not_fresh_at st y) /\
  m <= msz /\ msz < dimword (:256) /\
  stmt_state_rel ctx func cenv cx es s /\
  expr_val_at cenv cx ty sa st es v op s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  val_footprint tv v = m ==>
  frag_exec_mem ctx st st' (\t. t = s) (\t. F) (\r. ?ss. r = Halt ss)
Proof
  strip_tac >>
  drule compile_external_return_copy_parts >> simp[] >> strip_tac >>
  `MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w msz)] [buf])
       (fn_insts func)` by
    (irule return_first_inst_mem >> goal_assum drule >> simp[] >> metis_tac[]) >>
  `?b. FLOOKUP (abi_builtin_allocate_state st.cs_next_id msz s).vs_allocas
       st.cs_next_id = SOME (b,msz)` by
    (drule stmt_state_rel_alloca_site >> disch_then drule >>
     simp[mk_inst_def]) >>
  drule_all expr_val_at_frontier >> strip_tac >>
  irule compile_external_return_copy_frag_mem >>
  goal_assum (drule_at (Pat `compile_external_return _ _ _ _ _ _ _ _ _ _ = _`)) >>
  gvs[stmt_state_rel_def, alloca_inv_def] >> metis_tac[]
QED

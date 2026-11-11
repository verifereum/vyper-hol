Theory externalReturnBounds
Ancestors
  stmtSimReturn exprSimDefs exprSimProps loweringPosts allocaFootprint exprLoweringProps venomMemDefs
  compileEnv loweringStateRelDefs rawReturnValue valueCopyBytes vyperTyping vyperValue bodySim
  compileVyper entryStateRel

(* Zero-footprint values need no readable region.  Every nonempty expression
   value is instead backed by an allocation or a live local region. *)
Theorem expr_val_at_frontier:
  stmt_state_rel ctx func cenv cx es s /\
  expr_val_at cenv cx ty sa sb es v op s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty ==>
  ?w. eval_operand op s = SOME w /\
      (val_footprint tv v = 0 \/
       w2n w + val_footprint tv v <= s.vs_alloca_next)
Proof
  rpt strip_tac >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_val_at_def] >> strip_tac >>
  qexists_tac `w` >> simp[]
  >- (gvs[stmt_state_rel_def, alloca_inv_def, alloca_next_valid_def] >>
      first_x_assum drule >> decide_tac)
  >- (gvs[stmt_state_rel_def, state_rel_def, local_region_def] >>
      drule_all local_ptr_below_frontier >> strip_tac >> gvs[] >>
      decide_tac)
QED

Theorem stmt_state_rel_alloca_site:
  stmt_state_rel ctx func cenv cx es s /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_operands = [Lit (n2w n)] /\ n < dimword (:256) ==>
  ?b. FLOOKUP (abi_builtin_allocate_state inst.inst_id n s).vs_allocas
        inst.inst_id = SOME (b,n)
Proof
  rpt strip_tac >> simp[alloca_site_cases] >>
  Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
  >- simp[] >>
  PairCases_on `x` >>
  gvs[stmt_state_rel_def] >>
  first_x_assum drule_all >> simp[]
QED

Theorem expr_val_at_raw_frontier:
  stmt_state_rel ctx func cenv cx es s /\
  expr_val_at cenv cx ty sa sb es v op s /\
  expr_val_rel cx ty v op s /\
  is_bytestring_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v ==>
  ?p bs. eval_operand op s = SOME p /\
    raw_return_bytes v = SOME bs /\ LENGTH bs < dimword (:256) /\
    mload (w2n p) s = n2w (LENGTH bs) /\
    read_memory (w2n (p + 32w)) (LENGTH bs) s = bs /\
    w2n p + 32 <= s.vs_alloca_next /\
    (LENGTH bs = 0 \/
     w2n (p + 32w) + LENGTH bs <= s.vs_alloca_next)
Proof
  rpt strip_tac >>
  `~is_word_type ty` by metis_tac[is_bytestring_word_type] >>
  `0 < val_footprint tv v` by
    (drule_all bytestring_type_value >> strip_tac >> Cases_on `v` >>
     gvs[value_has_type_def, val_footprint_def]) >>
  drule_all expr_val_at_frontier >> strip_tac >> gvs[] >>
  `val_in_memory tv v (w2n w) s.vs_memory` by
    gvs[expr_val_rel_def] >>
  `w2n w + val_footprint tv v < dimword (:256)` by
    metis_tac[exprSimTypedAllocTheory.expr_val_at_bound] >>
  `w2n w + val_footprint tv v <= dimword (:256)` by decide_tac >>
  drule_all raw_return_value_read >> strip_tac >>
  `val_footprint tv v = 32 + LENGTH bs` by
    (drule_all bytestring_type_value >> strip_tac >> Cases_on `v` >>
     gvs[value_has_type_def, raw_return_bytes_def, val_footprint_def,
         string_to_bytes_def]) >>
  qexists_tac `bs` >> gvs[] >>
  `w2n w + w2n (32w:256 word) < dimword (:256)` by
    (simp[] >> decide_tac) >>
  drule wordsTheory.w2n_add_2 >> simp[] >> decide_tac
QED

Theorem return_buffer_ok_same_frame:
  same_frame cenv c /\ return_buffer_ok cenv ==> return_buffer_ok c
Proof
  simp[same_frame_def, compile_env_component_equality, return_buffer_ok_def]
QED

Theorem return_buffer_ok_register_positional_args:
  compile_register_positional_args cenv args off st = (c, st') /\
  return_buffer_ok cenv ==> return_buffer_ok c
Proof
  strip_tac >> drule compile_register_positional_args_cenv >> strip_tac >>
  qpat_x_assum `c = _` SUBST1_TAC >> gvs[return_buffer_ok_def]
QED

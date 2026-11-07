Theory bodyPtrPopPlaceBoundary
Ancestors bodyPtrPopMaterialization bodyPtrPopAllocationBoundary
  bodyPtrPopCompilerBoundary bodyPtrPopArithmeticBoundary bodyPtrPopPowBoundary
  venomInst list
  exprLowering compileEnv emitHelper

Theorem pop_compile_mapping_subscript_boundary:
  pop_comp_boundary sa /\ compile_mapping_subscript base_op key sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_mapping_subscript_def, comp_ignore_bind_def] >> rpt strip_tac >>
  rpt (drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST [drule_at (Pat `compile_alloc_buffer _ _ = _`) pop_compile_alloc_buffer_boundary,
         drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary,
         drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary] >> simp[]
QED

Theorem pop_compile_keccak256_key_boundary:
  pop_comp_boundary sa /\ compile_keccak256_key key fixed sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `fixed` >> simp[compile_keccak256_key_def, comp_ignore_bind_def] >>
  rpt strip_tac >>
  rpt (drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST [drule_at (Pat `compile_alloc_buffer _ _ = _`) pop_compile_alloc_buffer_boundary,
         drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary,
         drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary] >> simp[]
QED

Theorem pop_compile_tuple_subscript_boundary:
  pop_comp_boundary sa /\ compile_tuple_subscript base_op off sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_tuple_subscript_def] >> strip_tac >>
  drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[]
QED

Theorem pop_array_subscript_suffix_boundary:
  pop_comp_boundary sa /\
  (do is_neg <- (if signed then emit_op SLT [idx; Lit 0w]
                else return (Lit 0w));
      is_oob <- emit_op LT [idx; len];
      not_oob <- emit_op ISZERO [is_oob];
      invalid <- emit_op OR [is_neg; not_oob];
      valid <- emit_op ISZERO [invalid];
      emit_void ASSERT [valid];
      data_ptr <- (if dynamic then emit_op ADD [base_op; Lit (n2w ws)]
                   else return base_op);
      offset <- emit_op MUL [idx; Lit (n2w esz)];
      emit_op ADD [data_ptr; offset] od) sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `signed` >> Cases_on `dynamic` >>
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[pop_comp_boundary_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  irule pop_no_sub_finished_template >> simp[mk_inst_def]
QED

Theorem pop_compile_array_subscript_boundary:
  (!s v t. pop_comp_boundary s /\ loader base_op s = (v,t) ==>
    pop_comp_boundary t) /\ pop_comp_boundary sa /\
  compile_array_subscript base_op idx dynamic static_count ws esz signed loader sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_array_subscript_def] >> rpt strip_tac >>
  drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac
  >- (Cases_on `dynamic` >> simp[comp_return_def] >> rpt strip_tac >>
      gvs[] >> first_x_assum drule_all >> simp[]) >>
  rpt strip_tac >> drule_all pop_array_subscript_suffix_boundary >> simp[]
QED

Theorem pop_compile_attribute_boundary:
  (!aty s v t. pop_comp_boundary s /\ cfn cenv aty base_e s = (v,t) ==>
    pop_comp_boundary t) /\ pop_comp_boundary sa /\
  compile_attribute cfn cenv rt ty base_e fld sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_attribute_def] >> rpt strip_tac >>
  drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >> first_x_assum drule_all >> simp[]) >>
  rpt strip_tac >>
  drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >> drule_at (Pat `emit_op _ _ _ = _`)
        pop_emit_op_boundary >> simp[]) >>
  rpt strip_tac >> gvs[comp_return_def]
QED


(*
 * compile_expr keeps its block open: the emit and lowering primitives
 *
 * "Open" means ~block_is_terminated: the current block's last
 * instruction is not a terminator (new_block starts an empty one).
 *
 * TOP-LEVEL:
 *   emit_nonterminator_open, emit_op_nonterminator_open, new_block_open
 *                         — the emit steps that leave a block open
 *   compile_*_open        — names, literals, environment variables,
 *                           comparisons, safe arithmetic, binops, clamps,
 *                           subscripts, attributes, IfExp and pop
 *)

Theory exprOpenPrimitives
Ancestors
  exprLowering compileEnv emitHelper venomInst list rich_list finite_map context builtinSimple

Theorem emit_nonterminator_open:
  !inst sa u sb.
    emit inst sa = (u,sb) /\ ~is_terminator inst.inst_opcode ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> simp[emit_def] >> strip_tac >>
  Cases_on `sa.cs_current_insts` >>
  gvs[block_is_terminated_def, LAST_APPEND, LAST_CONS_cond]
QED

Theorem new_block_open:
  !label sa u sb.
    new_block label sa = (u,sb) ==> ~block_is_terminated sb
Proof
  simp[new_block_def, block_is_terminated_def]
QED

Theorem emit_op_nonterminator_open:
  !opc args sa v sb.
    emit_op opc args sa = (v,sb) /\ ~is_terminator opc ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >>
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def,
       fresh_id_def, fresh_var_def, emit_def, comp_return_def] >> strip_tac >>
  Cases_on `sa.cs_current_insts` >>
  gvs[block_is_terminated_def, LAST_APPEND, LAST_CONS_cond, mk_inst_def]
QED

Theorem compile_attribute_open:
  !cfn cenv ret_ty ty base_e field sa vv sb.
    compile_attribute cfn cenv ret_ty ty base_e field sa = (vv,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >>
  simp[compile_attribute_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  drule emit_op_nonterminator_open >> simp[is_terminator_def]
QED

Theorem compile_ifexp_open:
  !cfn bfn tfn cenv ty ann c a b sa vv sb.
    compile_expr_body cfn bfn tfn cenv ty (IfExp ann c a b) sa = (vv,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> simp[compile_expr_body_def] >>
  rpt (pairarg_tac >> simp[]) >>
  strip_tac >> gvs[AllCaseEqs()] >>
  drule new_block_open >> simp[]
QED

Theorem compile_tuple_subscript_open:
  !base offset sa v sb.
    compile_tuple_subscript base offset sa = (v,sb) ==>
    ~block_is_terminated sb
Proof
  rpt strip_tac >> gvs[compile_tuple_subscript_def] >>
  drule emit_op_nonterminator_open >> simp[is_terminator_def]
QED

Theorem compile_array_subscript_open:
  !base idx dyn count scale size signed load sa v sb.
    compile_array_subscript base idx dyn count scale size signed load sa = (v,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> simp[compile_array_subscript_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  drule emit_op_nonterminator_open >> simp[is_terminator_def]
QED

Theorem compile_dynarray_pop_open:
  !base scale size load store sa v sb.
    compile_dynarray_pop base scale size load store sa = (v,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >>
  simp[compile_dynarray_pop_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  drule emit_op_nonterminator_open >> simp[is_terminator_def]
QED

Theorem compile_mapping_subscript_open:
  !base key sa v sb.
    compile_mapping_subscript base key sa = (v,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >>
  simp[compile_mapping_subscript_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  drule emit_op_nonterminator_open >> simp[is_terminator_def]
QED

Theorem compile_name_vv_open:
  !cenv ty id sa vv sb.
    (?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar p sz)) \/
    (?off sz. FLOOKUP cenv.ce_vars id = SOME (MemLoc off sz)) ==>
    ~block_is_terminated sa /\ compile_name_vv cenv ty id sa = (vv,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> strip_tac >>
  simp[compile_name_vv_def, comp_return_def] >> rpt strip_tac >> gvs[]
QED

Theorem compile_acc_open:
  !cfn cenv e item sa v sb.
    item <> Code /\ item <> Address /\
    compile_acc cfn cenv e item sa = (v,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> Cases_on `item` >> simp[compile_acc_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  drule emit_op_nonterminator_open >> simp[is_terminator_def]
QED

Theorem compile_ptr_load_open:
  !ctor loc op sa v sb.
    compile_ptr_load ctor loc op sa = (v,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> Cases_on `ctor` >> Cases_on `loc` >>
  simp[compile_ptr_load_def] >> strip_tac >>
  drule emit_op_nonterminator_open >> simp[is_terminator_def]
QED

Theorem compile_alloc_buffer_open:
  !size sa buf sb.
    compile_alloc_buffer size sa = (buf,sb) ==> ~block_is_terminated sb
Proof
  rpt gen_tac >> simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  drule emit_op_nonterminator_open >> simp[is_terminator_def]
QED

Theorem compile_env_var_open:
  !item sa v sb.
    compile_env_var item sa = (v,sb) ==> ~block_is_terminated sb
Proof
  rpt gen_tac >> Cases_on `item` >>
  simp[compile_env_var_def, comp_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  drule emit_op_nonterminator_open >> simp[is_terminator_def]
QED

Theorem compile_compare_open:
  !op x y ty sa v sb.
    (op = Lt \/ op = Gt \/ op = Eq \/ op = NotEq \/ op = LtE \/ op = GtE) /\
    compile_compare op x y ty sa = (v,sb) ==> ~block_is_terminated sb
Proof
  rpt gen_tac >> strip_tac >>
  gvs[compile_compare_def] >>
  Cases_on `is_uint256 ty` >> Cases_on `sa.cs_current_insts` >>
  gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def,
      fresh_id_def, fresh_var_def, emit_def, comp_return_def,
      mk_inst_def, block_is_terminated_def, LAST_APPEND,
      LAST_CONS_cond, is_terminator_def]
QED

Theorem emit_void_terminated:
  !opc args sa v sb.
    emit_void opc args sa = (v,sb) ==>
    (block_is_terminated sb <=> is_terminator opc)
Proof
  rpt gen_tac >>
  simp[emit_void_def, comp_bind_def, comp_ignore_bind_def,
       fresh_id_def, emit_def, comp_return_def] >> strip_tac >>
  Cases_on `sa.cs_current_insts` >>
  gvs[block_is_terminated_def, LAST_APPEND, LAST_CONS_cond, mk_inst_def]
QED

Theorem compile_store_byte_chunks_open:
  !ptr bs off sa u sb.
    ~block_is_terminated sa /\
    compile_store_byte_chunks ptr bs off sa = (u,sb) ==>
    ~block_is_terminated sb
Proof
  recInduct compile_store_byte_chunks_ind >>
  conj_tac >- simp[compile_store_byte_chunks_def, comp_return_def] >>
  rpt gen_tac >> disch_tac >> rpt gen_tac >> strip_tac >>
  gvs[Once compile_store_byte_chunks_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  first_x_assum irule >> goal_assum (drule_at Any) >>
  drule emit_void_terminated >> simp[is_terminator_def]
QED

Theorem compile_bytelike_literal_open:
  !bs maxlen sa buf sb.
    compile_bytelike_literal bs maxlen sa = (buf,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >>
  simp[compile_bytelike_literal_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  irule compile_store_byte_chunks_open >> goal_assum (drule_at Any) >>
  drule emit_void_terminated >> simp[is_terminator_def]
QED

Theorem compile_literal_vv_open:
  !ty lit sa vv sb.
    ~block_is_terminated sa /\ compile_literal_vv ty lit sa = (vv,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> Cases_on `lit` >>
  simp[oneline compile_literal_vv_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[]) >>
  simp[comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  imp_res_tac compile_bytelike_literal_open
QED

Theorem compile_clamp_open:
  !op ty sa u sb.
    compile_clamp op ty sa = (u,sb) ==> ~block_is_terminated sb
Proof
  rpt gen_tac >> Cases_on `is_signed_type ty` >>
  simp[compile_clamp_def, comp_bind_def] >>
  rpt (pairarg_tac >> simp[comp_bind_def]) >> strip_tac >>
  drule emit_void_terminated >> simp[is_terminator_def]
QED

Theorem clamp_and_return_open:
  !op ty sa v sb.
    clamp_and_return op ty sa = (v,sb) ==> ~block_is_terminated sb
Proof
  rpt gen_tac >>
  simp[clamp_and_return_def, comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule compile_clamp_open >> simp[]
QED

Theorem wrap_truncate_open:
  !op ty sa v sb.
    ~block_is_terminated sa /\ wrap_truncate op ty sa = (v,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> Cases_on `type_bits ty < 256`
  >- (Cases_on `is_signed_type ty` >> simp[wrap_truncate_def] >>
      strip_tac >> drule emit_op_nonterminator_open >> simp[is_terminator_def]) >>
  simp[wrap_truncate_def, comp_return_def] >> strip_tac >> gvs[]
QED

Theorem compile_safe_add_open:
  !x y ty sa v sb.
    compile_safe_add x y ty sa = (v,sb) ==> ~block_is_terminated sb
Proof
  rpt gen_tac >> Cases_on `type_bits ty < 256`
  >- (simp[compile_safe_add_def, comp_bind_def] >>
      pairarg_tac >> simp[] >> strip_tac >>
      drule clamp_and_return_open >> simp[]) >>
  Cases_on `is_signed_type ty` >>
  simp[compile_safe_add_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  drule emit_void_terminated >> simp[is_terminator_def]
QED

Theorem compile_safe_sub_open:
  !x y ty sa v sb.
    compile_safe_sub x y ty sa = (v,sb) ==> ~block_is_terminated sb
Proof
  rpt gen_tac >> Cases_on `type_bits ty < 256`
  >- (simp[compile_safe_sub_def, comp_bind_def] >>
      pairarg_tac >> simp[] >> strip_tac >>
      drule clamp_and_return_open >> simp[]) >>
  Cases_on `is_signed_type ty` >>
  simp[compile_safe_sub_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  drule emit_void_terminated >> simp[is_terminator_def]
QED

Theorem compile_safe_decimal_div_open:
  !x y divisor ty sa v sb.
    compile_safe_decimal_div x y divisor ty sa = (v,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >>
  simp[compile_safe_decimal_div_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  drule clamp_and_return_open >> simp[]
QED

Theorem compile_safe_mod_open:
  !x y ty sa v sb.
    compile_safe_mod x y ty sa = (v,sb) ==> ~block_is_terminated sb
Proof
  rpt gen_tac >> Cases_on `is_signed_type ty` >>
  simp[compile_safe_mod_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  drule emit_op_nonterminator_open >> simp[is_terminator_def]
QED

Theorem compile_safe_div_open:
  !x y ty sa v sb.
    compile_safe_div x y ty sa = (v,sb) ==> ~block_is_terminated sb
Proof
  rpt gen_tac >> Cases_on `is_signed_type ty`
  >- (Cases_on `type_bits ty = 256`
      >- (simp[compile_safe_div_def, comp_bind_def, comp_ignore_bind_def,
               comp_return_def] >>
          rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
          drule emit_void_terminated >> simp[is_terminator_def]) >>
      Cases_on `type_bits ty < 256`
      >- (simp[compile_safe_div_def, comp_bind_def, comp_ignore_bind_def] >>
          rpt (pairarg_tac >> simp[]) >> strip_tac >>
          drule clamp_and_return_open >> simp[]) >>
      simp[compile_safe_div_def, comp_bind_def, comp_ignore_bind_def,
           comp_return_def] >>
      rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
      drule emit_op_nonterminator_open >> simp[is_terminator_def]) >>
  simp[compile_safe_div_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  drule emit_op_nonterminator_open >> simp[is_terminator_def]
QED

Theorem compile_mul_overflow_check_open:
  !x y res signed bits sa u sb.
    compile_mul_overflow_check x y res signed bits sa = (u,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >>
  simp[compile_mul_overflow_check_def, comp_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  drule emit_void_terminated >> simp[is_terminator_def]
QED

Theorem compile_safe_mul_open:
  !x y ty sa v sb.
    compile_safe_mul x y ty sa = (v,sb) ==> ~block_is_terminated sb
Proof
  rpt gen_tac >> Cases_on `type_bits ty < 256 \/ is_decimal_type ty`
  >- (simp[compile_safe_mul_def, comp_bind_def, comp_ignore_bind_def] >>
      rpt (pairarg_tac >> simp[]) >> strip_tac >>
      drule clamp_and_return_open >> simp[]) >>
  `~is_decimal_type ty /\ 128 < type_bits ty` by (gvs[] >> decide_tac) >>
  simp[compile_safe_mul_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  drule compile_mul_overflow_check_open >> simp[]
QED

Theorem compile_safe_pow_open:
  !x y ty blit elit sa v sb.
    compile_safe_pow x y ty blit elit sa = (v,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> Cases_on `blit`
  >- (Cases_on `elit`
      >- (simp[compile_safe_pow_def, comp_bind_def, comp_ignore_bind_def,
               comp_return_def] >>
          rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
          drule compile_clamp_open >> simp[]) >>
      simp[compile_safe_pow_def] >> rpt IF_CASES_TAC >>
      simp[comp_bind_def, comp_ignore_bind_def] >>
      rpt (pairarg_tac >> simp[]) >> strip_tac >>
      drule emit_op_nonterminator_open >> simp[is_terminator_def]) >>
  simp[compile_safe_pow_def] >> IF_CASES_TAC >>
  simp[comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  drule emit_op_nonterminator_open >> simp[is_terminator_def]
QED

Theorem compile_select_open:
  !cond a b sa v sb.
    compile_select cond a b sa = (v,sb) ==> ~block_is_terminated sb
Proof
  rpt gen_tac >> simp[compile_select_def, comp_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  drule emit_op_nonterminator_open >> simp[is_terminator_def]
QED

Theorem compile_binop_open:
  !op x y ty blit elit sa v sb.
    op <> ExpMod /\ compile_binop op x y ty blit elit sa = (v,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> Cases_on `op` >> simp[compile_binop_def] >>
  rpt IF_CASES_TAC >> simp[comp_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  FIRST [drule compile_safe_add_open,
         drule compile_safe_sub_open,
         drule compile_safe_mul_open,
         drule compile_safe_div_open,
         drule compile_safe_decimal_div_open,
         drule compile_safe_mod_open,
         drule compile_safe_pow_open,
         drule compile_select_open,
         drule_at Any compile_compare_open,
         drule_at Any wrap_truncate_open,
         drule emit_op_nonterminator_open] >>
  simp[is_terminator_def] >>
  drule emit_op_nonterminator_open >> simp[is_terminator_def]
QED

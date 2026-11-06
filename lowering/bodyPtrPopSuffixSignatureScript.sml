Theory bodyPtrPopSuffixSignature
Ancestors
  bodyPtrPopTargetFactor fragExec exprLowering emitHelper compileEnv list
  venomInst context rich_list

(* An explicit instruction window, rather than opcode membership: identities
   and operands are needed to compare this suffix with other producers. *)
Theorem pop_storage_suffix_shape:
  compile_dynarray_pop hdr 1 esz ctor imm
    (if tr then LocTransient else LocStorage) sa = (r,sb) ==>
  ?x0 x1 x2 x3 x4 x5 x6.
    r = Var x6 /\ sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts ++
      [mk_inst sa.cs_next_id (if tr then TLOAD else SLOAD) [hdr] [x0];
       mk_inst (sa.cs_next_id+1) ISZERO [Var x0] [x1];
       mk_inst (sa.cs_next_id+2) ISZERO [Var x1] [x2];
       mk_inst (sa.cs_next_id+3) ASSERT [Var x2] [];
       mk_inst (sa.cs_next_id+4) SUB [Var x0; Lit 1w] [x3];
       mk_inst (sa.cs_next_id+5) (if tr then TSTORE else SSTORE)
         [hdr; Var x3] [];
       mk_inst (sa.cs_next_id+6) ADD [hdr; Lit 1w] [x4];
       mk_inst (sa.cs_next_id+7) MUL [Var x3; Lit (n2w esz)] [x5];
       mk_inst (sa.cs_next_id+8) ADD [Var x4; Var x5] [x6]]
Proof
  Cases_on `tr` >>
  simp[compile_dynarray_pop_def, compile_ptr_load_def, compile_ptr_store_def,
       emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[mk_inst_def]
QED

Theorem pop_storage_suffix_fn_window:
  compile_dynarray_pop hdr 1 esz ctor imm
    (if tr then LocTransient else LocStorage) sa = (r,sb) /\
  fn_has_code si sb fn ==>
  ?bb tail x0 x1 x2 x3 x4 x5 x6.
    lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
    r = Var x6 /\
    bb.bb_instructions = sa.cs_current_insts ++
      [mk_inst sa.cs_next_id (if tr then TLOAD else SLOAD) [hdr] [x0];
       mk_inst (sa.cs_next_id+1) ISZERO [Var x0] [x1];
       mk_inst (sa.cs_next_id+2) ISZERO [Var x1] [x2];
       mk_inst (sa.cs_next_id+3) ASSERT [Var x2] [];
       mk_inst (sa.cs_next_id+4) SUB [Var x0; Lit 1w] [x3];
       mk_inst (sa.cs_next_id+5) (if tr then TSTORE else SSTORE)
         [hdr; Var x3] [];
       mk_inst (sa.cs_next_id+6) ADD [hdr; Lit 1w] [x4];
       mk_inst (sa.cs_next_id+7) MUL [Var x3; Lit (n2w esz)] [x5];
       mk_inst (sa.cs_next_id+8) ADD [Var x4; Var x5] [x6]] ++ tail
Proof
  strip_tac >> drule pop_storage_suffix_shape >> strip_tac >>
  gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
  metis_tac[APPEND_ASSOC]
QED

Theorem pop_target_attribute_address:
  compile_get_target_ptr cfn ce (AttributeTarget bt fld) sa = ((op,loc,pt),sb) ==>
  ?x. op = Var x
Proof
  Cases_on `compile_get_target_ptr cfn ce bt sa` >> PairCases_on `q` >>
  simp[Once compile_get_target_ptr_def, comp_bind_def, emit_op_def,
       comp_return_def, comp_ignore_bind_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[]
QED

Theorem pop_mapping_subscript_address:
  compile_mapping_subscript base_op key sa = (op,sb) ==> ?x. op = Var x
Proof
  simp[compile_mapping_subscript_def, comp_bind_def] >>
  pairarg_tac >>
  simp[emit_void_def, emit_op_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_var_def, fresh_id_def, emit_def] >> strip_tac >> gvs[]
QED

Theorem pop_array_subscript_address:
  compile_array_subscript base_op idx dyn cnt ws esz sgn loader sa = (op,sb) ==>
  ?x. op = Var x
Proof
  simp[compile_array_subscript_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  simp[comp_ignore_bind_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> pairarg_tac >>
  simp[emit_op_def, comp_ignore_bind_def, comp_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def] >> strip_tac >> gvs[]
QED

(* Even absent/unsupported descriptors use the checked-array fallback, whose
   final ADD returns a variable. No successful source evaluation is assumed. *)
Theorem pop_target_subscript_address:
  compile_get_target_ptr cfn ce (SubscriptTarget bt idx) sa = ((op,loc,pt),sb) ==>
  ?x. op = Var x
Proof
  Cases_on `compile_get_target_ptr cfn ce bt sa` >> PairCases_on `q` >>
  Cases_on `q2` >>
  simp[Once compile_get_target_ptr_def, comp_bind_def]
  >- (pairarg_tac >> simp[] >> pairarg_tac >>
      simp[comp_return_def] >> strip_tac >> gvs[] >>
      metis_tac[pop_array_subscript_address]) >>
  Cases_on `x` >> simp[comp_bind_def]
  >- (pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
      pairarg_tac >> simp[comp_return_def] >> strip_tac >> gvs[] >>
      metis_tac[pop_mapping_subscript_address]) >>
  pairarg_tac >> simp[] >> pairarg_tac >>
  simp[comp_return_def] >> strip_tac >> gvs[] >>
  metis_tac[pop_array_subscript_address]
QED

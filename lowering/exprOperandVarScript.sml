(*
 * The operand compile_expr hands out, for any type (#636)
 *
 * Composing an expression's fragment with code that runs after it needs
 * its operand to survive.  compile_lower_value_var proves that, for every
 * expression, the operand lower_value compile_expr returns is a literal or
 * a variable already handed out (not_fresh_at), given local_ptrs_reserved.
 * exprWordOperand proves the same for word types without the reservation
 * hypothesis.
 *
 * TOP-LEVEL:
 *   compile_lower_value_var — as above, for lower_value compile_expr
 *   compiler_compile_var — the same for compile_expr and both builtin
 *     dispatchers
 *   compiler_unwrap_value_var — the same for unwrap_value
 *   compiler_ci_mono_reserved — ci_mono keeps local_ptrs_reserved
 *   compiler_make_tuple_result, compiler_make_array_elems_result — the
 *     aggregate fillers return the buffer they were given
 *
 * Helpers: the compiler_counter_* lemmas (cs_next_var only grows), the
 *   compiler_*_var lemmas, one per case of compile_expr_body and the
 *   builtin dispatchers, and the compiler_*_reserved_cong lemmas.
 *)
Theory exprOperandVar
Ancestors
  list rich_list exprSafeOperand exprSafeOperandBuiltins exprLoweringProps
  freshWrites compileEnv emitHelper emitHelperProps context exprLowering
  exprCallBounds vyperAST

(* Reservation constrains Var pointers, without excluding labels. *)
Theorem environment_var_not_fresh:
  local_ptrs_reserved cenv sa /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
  not_fresh_at sa p
Proof
  rw[local_ptrs_reserved_def] >> metis_tac[]
QED

(* Counter projection: independent of instruction and block structure. *)
Theorem compiler_counter_return:
  s.cs_next_var <= (SND (comp_return a s)).cs_next_var
Proof
  simp[comp_return_def]
QED

Theorem compiler_counter_bind:
  (!s. s.cs_next_var <= (SND (m s)).cs_next_var) /\
  (!a s. s.cs_next_var <= (SND (f a s)).cs_next_var) ==>
  !s. s.cs_next_var <= (SND (comp_bind m f s)).cs_next_var
Proof
  strip_tac >> gen_tac >> Cases_on `m s` >>
  simp[comp_bind_def] >> metis_tac[pairTheory.SND, arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem compiler_counter_ignore_bind:
  (!s. s.cs_next_var <= (SND (m s)).cs_next_var) /\
  (!s. s.cs_next_var <= (SND (n s)).cs_next_var) ==>
  !s. s.cs_next_var <= (SND (comp_ignore_bind m n s)).cs_next_var
Proof
  simp[comp_ignore_bind_def] >> strip_tac >>
  irule compiler_counter_bind >> simp[]
QED

Theorem compiler_counter_primitives:
  (!s. s.cs_next_var <= (SND (fresh_var s)).cs_next_var) /\
  (!s. s.cs_next_var <= (SND (fresh_id s)).cs_next_var) /\
  (!p s. s.cs_next_var <= (SND (fresh_label p s)).cs_next_var) /\
  (!i s. s.cs_next_var <= (SND (emit i s)).cs_next_var) /\
  (!l s. s.cs_next_var <= (SND (new_block l s)).cs_next_var)
Proof
  simp[fresh_var_def, fresh_id_def, fresh_label_def, emit_def, new_block_def]
QED

Theorem compiler_counter_emit:
  (!opc args s. s.cs_next_var <= (SND (emit_op opc args s)).cs_next_var) /\
  (!opc args s. s.cs_next_var <= (SND (emit_void opc args s)).cs_next_var) /\
  (!opc args outs s.
    s.cs_next_var <= (SND (emit_inst opc args outs s)).cs_next_var)
Proof
  metis_tac[ci_mono_emit_op, ci_mono_emit_void, ci_mono_emit_inst, ci_mono_def]
QED

Theorem compiler_counter_ptr_load:
  s.cs_next_var <=
    (SND (compile_ptr_load ctor loc ptr_op s)).cs_next_var
Proof
  Cases_on `ctor` >> Cases_on `loc` >>
  simp[contextTheory.compile_ptr_load_def, compiler_counter_emit]
QED

Theorem compiler_counter_ptr_store:
  s.cs_next_var <=
    (SND (compile_ptr_store ctor loc ptr_op v s)).cs_next_var
Proof
  Cases_on `ctor` >> Cases_on `loc` >>
  simp[contextTheory.compile_ptr_store_def, compiler_counter_emit]
QED

Theorem compiler_counter_word_copy:
  s.cs_next_var <=
    (SND (compile_word_copy_loop src dst n load_loc store_loc ctor s)).cs_next_var
Proof
  qid_spec_tac `s` >>
  Cases_on `word_scale load_loc = 1` >>
  Cases_on `word_scale store_loc = 1` >>
  simp[contextTheory.compile_word_copy_loop_def, comp_ignore_bind_def] >>
  rpt gen_tac >>
  rpt (irule compiler_counter_bind >> conj_tac >> rpt gen_tac >> BETA_TAC) >>
  simp[compiler_counter_primitives, compiler_counter_return,
       compiler_counter_emit, compiler_counter_ptr_load,
       compiler_counter_ptr_store]
QED

Theorem compiler_counter_copy_wrappers:
  (!src dst n s. s.cs_next_var <=
     (SND (compile_storage_to_memory src dst n s)).cs_next_var) /\
  (!src dst n s. s.cs_next_var <=
     (SND (compile_transient_to_memory src dst n s)).cs_next_var) /\
  (!src dst n s. s.cs_next_var <=
     (SND (compile_code_to_memory src dst n s)).cs_next_var)
Proof
  simp[contextTheory.compile_storage_to_memory_def,
       contextTheory.compile_transient_to_memory_def,
       contextTheory.compile_code_to_memory_def, compiler_counter_word_copy] >>
  rpt gen_tac >> IF_CASES_TAC >>
  simp[compiler_counter_word_copy, compiler_counter_return,
       compiler_counter_bind, compiler_counter_ignore_bind]
QED

Theorem compiler_alloc_buffer_var:
  compile_alloc_buffer n sa = (buf,sb) ==>
  !x. buf.buf_operand = Var x ==> not_fresh_at sb x
Proof
  Cases_on `emit_op ALLOCA [Lit (n2w n)] sa` >>
  simp[contextTheory.compile_alloc_buffer_def, comp_bind_def,
       comp_return_def] >> rpt strip_tac >> gvs[] >>
  drule exprSafeOperandTheory.emit_op_safe_operand >>
  simp[exprSafeOperandTheory.safe_operand_def]
QED

Theorem compiler_var_prefix:
  (!a sa op sb. f a sa = (op,sb) ==>
     !x. op = Var x ==> not_fresh_at sb x) ==>
  !sa op sb. comp_bind m f sa = (op,sb) ==>
     !x. op = Var x ==> not_fresh_at sb x
Proof
  strip_tac >> rpt gen_tac >> Cases_on `m sa` >>
  simp[comp_bind_def] >> metis_tac[]
QED

(* The three allocate-and-copy cases of compile_ensure_in_memory. *)
val allocated_memory_var_tac =
  Cases_on `compile_alloc_buffer bytes sa` >>
  rename1 `compile_alloc_buffer bytes sa = (buf,sm)` >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  Cases_on `wc = 1` >> simp[] >>
  pairarg_tac >> gvs[] >> rpt strip_tac >> gvs[] >>
  drule compiler_alloc_buffer_var >> disch_then (qspec_then `x` mp_tac) >>
  simp[] >> strip_tac >>
  qpat_x_assum `_ sm = ((),_)` mp_tac >>
  qmatch_goalsub_abbrev_tac `copy sm` >> strip_tac >>
  `!s. s.cs_next_var <= (SND (copy s)).cs_next_var` by
    simp[Abbr `copy`, compiler_counter_bind, compiler_counter_ignore_bind,
         compiler_counter_emit, compiler_counter_return, compiler_counter_copy_wrappers] >>
  irule freshWritesTheory.not_fresh_at_mono >> qexists `sm` >>
  metis_tac[pairTheory.SND];

Theorem compiler_ensure_memory_var:
  compile_ensure_in_memory p loc bytes wc ctor sa = (op,sb) /\
  (!x. p = Var x ==> not_fresh_at sa x) ==>
  !x. op = Var x ==> not_fresh_at sb x
Proof
  Cases_on `loc` >> simp[contextTheory.compile_ensure_in_memory_def]
  >- (simp[comp_return_def] >> metis_tac[])
  >- allocated_memory_var_tac
  >- allocated_memory_var_tac
  >- allocated_memory_var_tac >>
  Cases_on `emit_op CALLDATALOAD [p] sa` >>
  rename1 `emit_op CALLDATALOAD [p] sa = (len,sl)` >>
  Cases_on `compile_alloc_buffer (bytes + 32) sl` >>
  rename1 `compile_alloc_buffer (bytes + 32) sl = (buf,sm)` >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >> rpt strip_tac >> gvs[] >>
  ntac 3 (pairarg_tac >> gvs[]) >>
  drule compiler_alloc_buffer_var >> disch_then (qspec_then `x` mp_tac) >>
  simp[] >> strip_tac >>
  irule freshWritesTheory.not_fresh_at_mono >> qexists `sm` >>
  metis_tac[compiler_counter_emit, pairTheory.SND, arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem compiler_unwrap_value_var:
  unwrap_value cenv vv sa = (op,sb) /\
  (case vv of
     StackValue ty v => (!x. v = Var x ==> not_fresh_at sa x)
   | LocatedValue ty p => (!x. p.ptr_operand = Var x ==> not_fresh_at sa x)) ==>
  !x. op = Var x ==> not_fresh_at sb x
Proof
  Cases_on `vv` >> simp[unwrap_value_def, comp_return_def]
  >- metis_tac[] >>
  IF_CASES_TAC
  >- (strip_tac >> drule exprSafeOperandTheory.compile_ptr_load_safe_operand >>
      simp[exprSafeOperandTheory.safe_operand_def]) >>
  rename1 `p.ptr_location` >> Cases_on `p.ptr_location` >>
  simp[comp_return_def] >> metis_tac[compiler_ensure_memory_var]
QED

Theorem compiler_lower_value_var:
  lower_value cfn cenv ty e sa = (op,sb) /\
  (!vv sm. cfn cenv ty e sa = (vv,sm) ==>
     !x. vv_operand vv = Var x ==> not_fresh_at sm x) ==>
  !x. op = Var x ==> not_fresh_at sb x
Proof
  simp[lower_value_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
  drule_at (Pos hd) compiler_unwrap_value_var >>
  Cases_on `vv` >> gvs[contextTheory.vv_operand_def] >> metis_tac[]
QED

Theorem compiler_name_var:
  compile_name_vv cenv ty id sa = (vv,sb) /\
  local_ptrs_reserved cenv sa ==>
  !x. vv_operand vv = Var x ==> not_fresh_at sb x
Proof
  simp[compile_name_vv_def] >>
  Cases_on `FLOOKUP cenv.ce_vars id` >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >-
    (rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
     gvs[contextTheory.vv_operand_def]) >>
  rename1 `SOME loc` >> Cases_on `loc` >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
  gvs[contextTheory.vv_operand_def, contextTheory.mk_ptr_def] >>
  metis_tac[environment_var_not_fresh]
QED

(* Counter transport across opaque compiler continuations. *)
Theorem compiler_ci_mono_not_fresh:
  ci_mono sa sb /\ not_fresh_at sa x ==> not_fresh_at sb x
Proof
  simp[ci_mono_def] >> metis_tac[freshWritesTheory.not_fresh_at_mono]
QED

Theorem compiler_lower_abi_encode_var:
  lower_abi_encode ensure mid src info maxlen sa = (op,sb) ==>
  !x. op = Var x ==> not_fresh_at sb x
Proof
  simp[builtinAbiTheory.lower_abi_encode_def, LET_THM,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
  drule compiler_alloc_buffer_var >> strip_tac >>
  irule freshWritesTheory.not_fresh_at_mono >>
  rename1 `compile_alloc_buffer _ sa = (buf,sm)` >>
  qexists `sm` >> reverse conj_tac >- metis_tac[] >>
  Cases_on `mid` >> gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rename1 `compile_abi_encode_to_buf data_ptr src info se = (encoded_len,sf)` >>
  `se.cs_next_var <= sf.cs_next_var` by
    (qspec_then `se` mp_tac (Q.SPECL [`data_ptr`, `src`, `info`]
      (cj 2 ci_mono_compile_abi_encode)) >> simp[ci_mono_def]) >>
  gvs[emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def]
QED

Theorem compiler_lower_abi_decode_var:
  lower_abi_decode data info amin amax outsz sa = (op,sb) ==>
  !x. op = Var x ==> not_fresh_at sb x
Proof
  simp[builtinAbiTheory.lower_abi_decode_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
  drule compiler_alloc_buffer_var >> strip_tac >>
  irule freshWritesTheory.not_fresh_at_mono >>
  rename1 `compile_alloc_buffer _ _ = (buf,sm)` >>
  qexists `sm` >> reverse conj_tac >- metis_tac[] >>
  rename1 `compile_abi_decode_to_buf _ _ _ _ info se = ((),sf)` >>
  `se.cs_next_var <= sf.cs_next_var` by
    metis_tac[cj 1 ci_mono_compile_abi_decode, ci_mono_def, pairTheory.SND] >>
  qpat_x_assum `emit_op ADD _ sm = _` mp_tac >>
  simp[emit_op_def, fresh_var_def, fresh_id_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  strip_tac >> gvs[]
QED

(* Aggregate filling returns its supplied buffer, never a child operand. *)
Theorem compiler_make_array_elems_result:
  !es idx sa op sb.
    compile_make_array_elems cfn cenv es et sz lw buf idx sa = (op,sb) ==>
    op = buf
Proof
  Induct >> simp[Once compile_make_array_elems_def, LET_THM,
                 comp_return_def] >>
  rpt gen_tac >>
  simp[Once compile_make_array_elems_def, LET_THM,
       comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> metis_tac[]
QED

Theorem compiler_make_tuple_result:
  !es off sa op sb.
    compile_make_tuple cfn cenv es buf off sa = (op,sb) ==> op = buf
Proof
  Induct >> simp[Once compile_make_tuple_def, LET_THM, comp_return_def] >>
  rpt gen_tac >>
  simp[Once compile_make_tuple_def, LET_THM,
       comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> metis_tac[]
QED

Theorem compiler_struct_lit_result:
  !fields off sa op sb.
    compile_struct_lit cfn cenv ty fields buf off sa = (op,sb) ==> op = buf
Proof
  Induct >> simp[Once compile_struct_lit_def, LET_THM, comp_return_def] >>
  Cases_on `h` >> rpt gen_tac >>
  simp[Once compile_struct_lit_def, LET_THM,
       comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> metis_tac[]
QED

Theorem compiler_make_array_result:
  compile_make_array cfn cenv es et sz lw buf sa = (op,sb) ==> op = buf
Proof
  simp[compile_make_array_def, comp_ignore_bind_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> metis_tac[compiler_make_array_elems_result]
QED

Theorem compiler_aggregate_buffer_var:
  (!ce ty e s. ci_mono s (SND (cfn ce ty e s))) ==>
  (!sa sb op es et sz lw buf.
    compile_make_array cfn cenv es et sz lw buf sa = (op,sb) /\
    (!x. buf = Var x ==> not_fresh_at sa x) ==>
    !x. op = Var x ==> not_fresh_at sb x) /\
  (!sa sb op es off buf.
    compile_make_tuple cfn cenv es buf off sa = (op,sb) /\
    (!x. buf = Var x ==> not_fresh_at sa x) ==>
    !x. op = Var x ==> not_fresh_at sb x) /\
  (!sa sb op fields ty off buf.
    compile_struct_lit cfn cenv ty fields buf off sa = (op,sb) /\
    (!x. buf = Var x ==> not_fresh_at sa x) ==>
    !x. op = Var x ==> not_fresh_at sb x)
Proof
  strip_tac >> rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (drule ci_mono_compile_make_array_cfn >> strip_tac >>
      `op = buf` by metis_tac[compiler_make_array_result] >>
      metis_tac[compiler_ci_mono_not_fresh, pairTheory.SND])
  >- (drule ci_mono_compile_make_tuple_cfn >> strip_tac >>
      `op = buf` by metis_tac[compiler_make_tuple_result] >>
      metis_tac[compiler_ci_mono_not_fresh, pairTheory.SND]) >>
  drule ci_mono_compile_struct_lit_cfn >> strip_tac >>
  `op = buf` by metis_tac[compiler_struct_lit_result] >>
  metis_tac[compiler_ci_mono_not_fresh, pairTheory.SND]
QED

Theorem compiler_acc_var:
  (!s op s'. lower_value cfn cenv (BaseT AddressT) e s = (op,s') ==>
     !x. op = Var x ==> not_fresh_at s' x) /\
  compile_acc cfn cenv e acc sa = (op,sb) ==>
  !x. op = Var x ==> not_fresh_at sb x
Proof
  Cases_on `acc` >> simp[compile_acc_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
  metis_tac[exprSafeOperandTheory.emit_op_safe_operand,
            exprSafeOperandTheory.safe_operand_def]
QED

Theorem compiler_ifexp_var:
  (!ce ty e s. ci_mono s (SND (cfn ce ty e s))) /\
  compile_expr_body cfn bfn tfn cenv ty (IfExp ann cond te ee) sa = (vv,sb) ==>
  !x. vv_operand vv = Var x ==> not_fresh_at sb x
Proof
  strip_tac >>
  `!ce ty e s. ci_mono s (SND (lower_value cfn ce ty e s))` by
    metis_tac[ci_mono_lower_value_cfn] >>
  qpat_x_assum `compile_expr_body _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_expr_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  Cases_on `is_word_type ann` >>
  simp[vyperASTTheory.expr_type_def,
       contextTheory.vv_operand_def, contextTheory.mk_ptr_def] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `!ce ty e s. ci_mono s (SND (cfn ce ty e s))` kall_tac >>
  qpat_x_assum `lower_value _ _ _ cond _ = _` kall_tac >>
  gvs[fresh_var_def, fresh_id_def, fresh_label_def, emit_inst_def, emit_def,
      new_block_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
      contextTheory.vv_operand_def, contextTheory.mk_ptr_def] >>
  qmatch_asmsub_abbrev_tac `lower_value cfn cenv ty te sthen` >>
  qmatch_asmsub_abbrev_tac `lower_value cfn cenv ty ee selse` >>
  `sthen.cs_next_var <= st8.cs_next_var` by
    metis_tac[ci_mono_def, pairTheory.SND] >>
  `selse.cs_next_var <= st12.cs_next_var` by
    metis_tac[ci_mono_def, pairTheory.SND] >>
  gvs[Abbr `sthen`, Abbr `selse`, compileEnvTheory.not_fresh_at_def,
      ASCIInumbersTheory.toString_11]
QED

(* The existing safe-input theorem handles Lit and Var. Labels need only a
   Var-result bound: conversions may legitimately return the input label. *)
Theorem compiler_type_convert_label_var[local]:
  compile_type_convert (Label lab) conv sa = (op,sb) ==>
  !x. op = Var x ==> not_fresh_at sb x
Proof
  Cases_on `conv` >>
  simp[compile_type_convert_def, load_bytestring_as_word_def,
       contextTheory.compile_alloc_buffer_def, emit_op_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def, LET_THM] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  rpt (IF_CASES_TAC >>
       simp[comp_bind_def, comp_ignore_bind_def, comp_return_def,
            fresh_id_def, fresh_var_def, emit_def]) >>
  rpt strip_tac >> gvs[] >>
  gvs[compileEnvTheory.not_fresh_at_def, ASCIInumbersTheory.toString_11]
QED

Theorem compiler_type_convert_var:
  (!x. v = Var x ==> not_fresh_at sa x) /\
  compile_type_convert v conv sa = (op,sb) ==>
  !x. op = Var x ==> not_fresh_at sb x
Proof
  Cases_on `v`
  >- (strip_tac >>
      rename1 `compile_type_convert (Lit n) conv sa = (op,sb)` >>
      `exprSafeOperand$safe_operand sa (Lit n)` by
        simp[exprSafeOperandTheory.safe_operand_def] >>
      drule_all exprSafeOperandTheory.compile_type_convert_safe_input >>
      Cases_on `op` >> simp[exprSafeOperandTheory.safe_operand_def])
  >- (strip_tac >>
      rename1 `compile_type_convert (Var name) conv sa = (op,sb)` >>
      `exprSafeOperand$safe_operand sa (Var name)` by
        simp[exprSafeOperandTheory.safe_operand_def] >>
      drule_all exprSafeOperandTheory.compile_type_convert_safe_input >>
      Cases_on `op` >> simp[exprSafeOperandTheory.safe_operand_def]) >>
  metis_tac[compiler_type_convert_label_var]
QED

Theorem compiler_empty_complex_var:
  compile_builtin_empty_complex n bs sa = (op,sb) ==>
  !x. op = Var x ==> not_fresh_at sb x
Proof
  simp[builtinSimpleTheory.compile_builtin_empty_complex_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  Cases_on `bs` >> simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
  drule compiler_alloc_buffer_var >> strip_tac >>
  irule freshWritesTheory.not_fresh_at_mono >>
  rename1 `compile_alloc_buffer _ sa = (buf,sm)` >>
  qexists `sm` >> reverse conj_tac >- metis_tac[]
  >- metis_tac[compiler_counter_emit, pairTheory.SND] >>
  metis_tac[ci_mono_compile_zero_words, ci_mono_def, pairTheory.SND]
QED

Theorem compiler_type_builtin_var:
  (!ce ty e s vv s'. cfn ce ty e s = (vv,s') ==>
     !x. vv_operand vv = Var x ==> not_fresh_at s' x) /\
  compile_type_builtin_dispatch_body cfn cenv vt ty tb rt args sa = (vv,sb) ==>
  !x. vv_operand vv = Var x ==> not_fresh_at sb x
Proof
  strip_tac >>
  `!ce ty e s op s'. lower_value cfn ce ty e s = (op,s') ==>
     !x. op = Var x ==> not_fresh_at s' x` by
    metis_tac[compiler_lower_value_var] >>
  qpat_x_assum `compile_type_builtin_dispatch_body _ _ _ _ _ _ _ _ = _` mp_tac >>
  Cases_on `tb` >>
  simp[compile_type_builtin_dispatch_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[])
  >~ [`compile_builtin_empty_complex _ _ _ = _`] >-
    (Cases_on `is_word_type rt` >>
     simp[contextTheory.mk_ptr_def] >> rpt strip_tac >>
     gvs[contextTheory.vv_operand_def] >>
     metis_tac[compiler_empty_complex_var])
  >~ [`compile_type_convert _ _ _`] >-
    (Cases_on `rt` >> simp[] >>
     qmatch_goalsub_abbrev_tac `as_stack_val vt result` >>
     Cases_on `result` >> gvs[as_stack_val_def, markerTheory.Abbrev_def] >>
     rpt strip_tac >>
     gvs[contextTheory.vv_operand_def] >>
     `!x. v = Var x ==> not_fresh_at st1 x` by metis_tac[] >>
     metis_tac[compiler_type_convert_var])
  >~ [`lower_abi_encode _ _ _ _ _ _`] >-
    (Cases_on `is_word_type (expr_type (HD args))` >> simp[] >>
     qmatch_goalsub_abbrev_tac `as_ptr_val vt LocMemory result` >>
     Cases_on `result` >> gvs[as_ptr_val_def, markerTheory.Abbrev_def] >>
     rpt strip_tac >> gvs[contextTheory.vv_operand_def, contextTheory.mk_ptr_def] >>
     qpat_x_assum `_ = lower_abi_encode _ _ _ _ _ _` (mp_tac o SYM) >>
     strip_tac >> drule compiler_lower_abi_encode_var >> simp[])
  >~ [`lower_abi_decode _ _ _ _ _ _`] >-
    (qmatch_goalsub_abbrev_tac `as_ptr_val vt LocMemory result` >>
     Cases_on `result` >> gvs[as_ptr_val_def, markerTheory.Abbrev_def] >>
     rpt strip_tac >> gvs[contextTheory.vv_operand_def, contextTheory.mk_ptr_def] >>
     metis_tac[compiler_lower_abi_decode_var])
  >~ [`compile_clamp_extract32 _ _ _`] >-
    (qmatch_goalsub_abbrev_tac `as_stack_val vt result` >>
     Cases_on `result` >> gvs[as_stack_val_def, markerTheory.Abbrev_def] >>
     rpt strip_tac >> gvs[contextTheory.vv_operand_def] >>
     drule exprSafeOperandBuiltinsTheory.compile_extract32_safe_operand >> strip_tac >>
     qpat_x_assum `_ = compile_clamp_extract32 _ _ _` (assume_tac o SYM) >>
     drule_all exprSafeOperandBuiltinsTheory.compile_clamp_extract32_safe_operand >>
     simp[exprSafeOperandTheory.safe_operand_def]) >>
  rpt strip_tac >> gvs[contextTheory.vv_operand_def]
QED

Theorem compiler_attribute_var:
  compile_attribute cfn cenv rt ty e fld sa = (vv,sb) ==>
  !x. vv_operand vv = Var x ==> not_fresh_at sb x
Proof
  simp[compile_attribute_def, LET_THM, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
  gvs[contextTheory.vv_operand_def, contextTheory.mk_ptr_def] >>
  drule exprSafeOperandTheory.emit_op_safe_operand >>
  simp[exprSafeOperandTheory.safe_operand_def]
QED

Theorem compiler_subscript_ops_var:
  (compile_tuple_subscript base_op off sa = (op,sb) ==>
   !x. op = Var x ==> not_fresh_at sb x) /\
  (compile_mapping_subscript base_op key sa = (op,sb) ==>
   !x. op = Var x ==> not_fresh_at sb x) /\
  (compile_array_subscript base_op idx dyn nitems ws elem_sz is_signed opc sa = (op,sb) ==>
   !x. op = Var x ==> not_fresh_at sb x)
Proof
  rpt conj_tac >>
  simp[compile_tuple_subscript_def, compile_mapping_subscript_def,
       compile_array_subscript_def, LET_THM, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
  drule exprSafeOperandTheory.emit_op_safe_operand >>
  simp[exprSafeOperandTheory.safe_operand_def]
QED

Theorem compiler_subscript_var:
  compile_subscript cfn cenv rt ty e idx sa = (vv,sb) ==>
  !x. vv_operand vv = Var x ==> not_fresh_at sb x
Proof
  simp[compile_subscript_def, LET_THM] >>
  qmatch_goalsub_abbrev_tac `cenv.ce_is_hashmap name` >>
  Cases_on `cenv.ce_is_hashmap name` >> simp[comp_bind_def, comp_return_def]
  >- (rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
      gvs[contextTheory.vv_operand_def, contextTheory.mk_ptr_def] >>
      metis_tac[compiler_subscript_ops_var]) >>
  Cases_on `cenv.ce_var_type name` >> simp[comp_bind_def, comp_return_def]
  >- (rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
      gvs[contextTheory.vv_operand_def, contextTheory.mk_ptr_def] >>
      metis_tac[compiler_subscript_ops_var]) >>
  rename1 `cenv.ce_var_type name = SOME vt` >> Cases_on `vt` >>
  simp[comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
  gvs[contextTheory.vv_operand_def, contextTheory.mk_ptr_def] >>
  metis_tac[compiler_subscript_ops_var]
QED

Theorem compiler_dynarray_pop_var:
  compile_dynarray_pop base_op ws elem_sz load_opc store_opc sa = (op,sb) ==>
  !x. op = Var x ==> not_fresh_at sb x
Proof
  simp[compile_dynarray_pop_def, LET_THM, comp_bind_def,
       comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
  drule exprSafeOperandTheory.emit_op_safe_operand >>
  simp[exprSafeOperandTheory.safe_operand_def]
QED

Theorem compiler_default_return_result:
  compile_default_return_path cenv rt dt buf result def addr skip amin amax info sa =
    (op,sb) ==> op = result
Proof
  simp[compile_default_return_path_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> simp[]
QED

Theorem compiler_default_return_var:
  (!x. result = Var x ==> not_fresh_at sa x) /\
  compile_default_return_path cenv rt dt buf result def addr skip amin amax info sa =
    (op,sb) ==> !x. op = Var x ==> not_fresh_at sb x
Proof
  strip_tac >> drule compiler_default_return_result >> strip_tac >>
  rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
  qexists `sa` >> reverse conj_tac >- metis_tac[] >>
  metis_tac[ci_mono_compile_default_return_path, ci_mono_def, pairTheory.SND]
QED

Theorem compiler_external_call_var:
  compile_external_call_kwargs cenv addr vals tys memsz abisz mid retsz minsz outsz
    static value gas skip hasdef def rt dt enc_info dec_info sa = (op,sb) ==>
  !x. op = Var x ==> not_fresh_at sb x
Proof
  simp[compile_external_call_kwargs_def, LET_THM, comp_ignore_bind_def] >>
  map_every qid_spec_tac [`sb`, `op`, `sa`] >>
  rpt (ho_match_mp_tac compiler_var_prefix >> gen_tac >> simp[LET_THM]) >>
  Cases_on `retsz = 0` >-
    simp[comp_return_def] >>
  Cases_on `hasdef` >> simp[comp_bind_def, comp_return_def] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[]) >> rpt strip_tac
  >~ [`compile_default_return_path _ _ _ _ _ _ _ _ _ _ _ _ = _`] >-
    (drule compiler_alloc_buffer_var >> strip_tac >>
     drule_all compiler_default_return_var >> simp[]) >>
  drule compiler_alloc_buffer_var >> strip_tac >>
  irule freshWritesTheory.not_fresh_at_mono >>
  rename1 `compile_alloc_buffer _ sa = (buf,sm)` >>
  qexists `sm` >> reverse conj_tac >- metis_tac[] >>
  metis_tac[ci_mono_compile_return_value_decode,
            cj 1 ci_mono_compile_abi_decode, ci_mono_def, pairTheory.SND,
            arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem compiler_internal_call_var:
  compile_call cfn cenv rt ty (IntCall fid) args default_ret sa = (vv,sb) ==>
  !x. vv_operand vv = Var x ==> not_fresh_at sb x
Proof
  simp[compile_call_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  Cases_on `returns_count > 0` >> Cases_on `return_buf_size > 0` >>
  gvs[] >> rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
  gvs[contextTheory.vv_operand_def, contextTheory.base_ptr_def] >>
  drule compiler_alloc_buffer_var >> strip_tac >>
  rename1 `compile_alloc_buffer _ _ = (buf,sm)` >>
  irule freshWritesTheory.not_fresh_at_mono >>
  qexists `sm` >> reverse conj_tac >- metis_tac[] >>
  rename1 `compile_stage_intcall_args _ _ _ _ sm = (ops,sn)` >>
  `sm.cs_next_var <= sn.cs_next_var` by
    metis_tac[ci_mono_compile_stage_intcall_args, ci_mono_def, pairTheory.SND]
  >>~- ([`store_multi_results _ _ _ _ = _`],
     rename1 `emit_multi_op _ _ _ sn = (results,se)` >>
     `sn.cs_next_var <= se.cs_next_var` by
       metis_tac[ci_mono_emit_multi_op, ci_mono_def, pairTheory.SND] >>
     `se.cs_next_var <= sb.cs_next_var` by
       metis_tac[ci_mono_store_multi_results, ci_mono_def, pairTheory.SND] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `sn.cs_next_var <= sb.cs_next_var` by
    metis_tac[compiler_counter_emit, pairTheory.SND] >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem compiler_raw_call_var:
  compile_raw_call dest data_ptr data_len gas value ct maxout rof sa = (op,sb) ==>
  !x. op = Var x ==> not_fresh_at sb x
Proof
  Cases_on `maxout = 0` >-
    (gvs[] >> strip_tac >>
     drule exprSafeOperandBuiltinsTheory.compile_raw_call_zero_safe_operand >>
     simp[exprSafeOperandTheory.safe_operand_def]) >>
  Cases_on `rof` >> Cases_on `ct` >>
  simp[builtinSystemTheory.compile_raw_call_def, LET_THM,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def]) >>
  rpt strip_tac >> gvs[]
  >>~- ([`emit_op SUB _ _ = (Var x,_)`],
    rename1 `emit_op SUB _ _ = (Var x,sm)` >>
    `not_fresh_at sm x` by
      metis_tac[exprSafeOperandTheory.emit_op_safe_operand,
                exprSafeOperandTheory.safe_operand_def] >>
    irule freshWritesTheory.not_fresh_at_mono >> qexists `sm` >>
    reverse conj_tac >- simp[] >>
    metis_tac[compiler_counter_emit, pairTheory.SND]) >>
  rename1 `buf.buf_operand = Var x` >>
  qpat_assum `compile_alloc_buffer _ _ = (buf,_)`
    (mp_then Any strip_assume_tac compiler_alloc_buffer_var) >>
  rename1 `compile_alloc_buffer _ _ = (buf,sm)` >>
  irule freshWritesTheory.not_fresh_at_mono >> qexists `sm` >>
  reverse conj_tac >- metis_tac[] >>
  metis_tac[compiler_counter_emit, pairTheory.SND, arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem compiler_call_var:
  compile_call cfn cenv rt ty target args default_ret sa = (vv,sb) ==>
  !x. vv_operand vv = Var x ==> not_fresh_at sb x
Proof
  Cases_on `target`
  >~ [`compile_call _ _ _ _ (IntCall _) _ _ _`] >-
    metis_tac[compiler_internal_call_var]
  >~ [`compile_call _ _ _ _ (ExtCall _ _ _ _) _ _ _`] >-
    (rename1 `ExtCall _ _ p _` >> PairCases_on `p` >>
     Cases_on `args` >> simp[compile_call_def, LET_THM] >>
     rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
     gvs[contextTheory.vv_operand_def] >>
     drule compiler_external_call_var >> strip_tac >>
     qpat_x_assum `(if _ then _ else _) = (vv,sb)` mp_tac >>
     IF_CASES_TAC >> simp[] >> strip_tac >>
     gvs[contextTheory.vv_operand_def, contextTheory.mk_ptr_def])
  >~ [`compile_call _ _ _ _ (RawCallCalldataTarget _) _ _ _`] >-
    suspend "rawcalldata"
  >~ [`compile_call _ _ _ _ (Send _) _ _ _`] >-
    suspend "send" >>
  simp[compile_call_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
  gvs[contextTheory.vv_operand_def]
QED

Resume compiler_call_var[rawcalldata]:
  namedCases_on `args` ["", "addr_e rest"] >-
    (simp[compile_call_def] >> pairarg_tac >> rpt strip_tac >>
     gvs[contextTheory.vv_operand_def]) >>
  namedCases_on `rest` ["", "value_e remaining"] >-
    (simp[compile_call_def] >> pairarg_tac >> rpt strip_tac >>
     gvs[contextTheory.vv_operand_def]) >>
  Cases_on `remaining` >>
  simp[compile_call_def, LET_THM, contextTheory.vv_operand_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
  gvs[contextTheory.vv_operand_def] >>
  drule compiler_raw_call_var >> strip_tac >>
  qpat_x_assum `(if _ then _ else _) = (vv,sb)` mp_tac >>
  IF_CASES_TAC >> simp[] >> strip_tac >>
  gvs[contextTheory.vv_operand_def, contextTheory.mk_ptr_def]
QED

Resume compiler_call_var[send]:
  namedCases_on `args` ["", "addr_e rest"] >-
    (simp[compile_call_def] >> pairarg_tac >> rpt strip_tac >>
     gvs[contextTheory.vv_operand_def]) >>
  namedCases_on `rest` ["", "value_e remaining"] >-
    (simp[compile_call_def] >> pairarg_tac >> rpt strip_tac >>
     gvs[contextTheory.vv_operand_def]) >>
  Cases_on `LENGTH remaining = if b then 1 else 0` >>
  simp[compile_call_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
  gvs[contextTheory.vv_operand_def]
QED

Finalise compiler_call_var

Theorem compiler_bytelike_literal_var:
  compile_bytelike_literal bytes maxlen sa = (buf,sb) ==>
  !x. buf.buf_operand = Var x ==> not_fresh_at sb x
Proof
  simp[compile_bytelike_literal_def, LET_THM, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
  drule compiler_alloc_buffer_var >> strip_tac >>
  rename1 `compile_alloc_buffer _ sa = (buf,sm)` >>
  qmatch_goalsub_rename_tac `not_fresh_at sf x` >>
  irule freshWritesTheory.not_fresh_at_mono >> qexists `sm` >>
  reverse conj_tac >- metis_tac[] >>
  rename1 `emit_void MSTORE _ sm = ((),sn)` >>
  `sm.cs_next_var <= sn.cs_next_var` by
    metis_tac[compiler_counter_emit, pairTheory.SND] >>
  `sn.cs_next_var <= sf.cs_next_var` by
    metis_tac[ci_mono_compile_store_byte_chunks, ci_mono_def, pairTheory.SND] >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem compiler_literal_var:
  compile_literal_vv ty lit sa = (vv,sb) ==>
  !x. vv_operand vv = Var x ==> not_fresh_at sb x
Proof
  Cases_on `lit`
  >~ [`compile_literal_vv ty (BoolL b)`] >-
    (Cases_on `b` >> simp[compile_literal_vv_def, comp_return_def] >>
     rpt strip_tac >> gvs[contextTheory.vv_operand_def]) >>
  simp[compile_literal_vv_def, comp_return_def] >>
  rpt CASE_TAC >>
  simp[comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rpt strip_tac >> gvs[contextTheory.vv_operand_def, contextTheory.base_ptr_def] >>
  metis_tac[compiler_bytelike_literal_var]
QED

Theorem compiler_ec_points_var:
  (!sa op sb. compile_ecadd_points p1 p2 sa = (op,sb) ==>
     !x. op = Var x ==> not_fresh_at sb x) /\
  (!sa op sb. compile_ecmul_point p scalar sa = (op,sb) ==>
     !x. op = Var x ==> not_fresh_at sb x)
Proof
  conj_tac >>
  simp[builtinMiscTheory.compile_ecadd_points_def,
       builtinMiscTheory.compile_ecmul_point_def,
       contextTheory.compile_alloc_buffer_def, emit_op_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[] >>
  gvs[compileEnvTheory.not_fresh_at_def, ASCIInumbersTheory.toString_11]
QED

Theorem compiler_method_id_runtime_var:
  compile_method_id_runtime ty v fixed sa = (op,sb) ==>
  !x. op = Var x ==> not_fresh_at sb x
Proof
  Cases_on `fixed`
  >- (strip_tac >>
      drule exprSafeOperandBuiltinsTheory.compile_method_id_word_safe_operand >>
      rpt strip_tac >> gvs[exprSafeOperandTheory.safe_operand_def]) >>
  simp[builtinHashingTheory.compile_method_id_runtime_def] >>
  qid_spec_tac `sb` >> qid_spec_tac `op` >> qid_spec_tac `sa` >>
  ho_match_mp_tac compiler_var_prefix >> gen_tac >>
  simp[contextTheory.compile_alloc_buffer_def, emit_op_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[] >>
  gvs[compileEnvTheory.not_fresh_at_def, ASCIInumbersTheory.toString_11]
QED

Theorem compiler_slice_var:
  (!sa op sb. compile_slice_data len data start sz n sa = (op,sb) ==>
     !x. op = Var x ==> not_fresh_at sb x) /\
  (!sa op sb. compile_slice_memory src start sz n sa = (op,sb) ==>
     !x. op = Var x ==> not_fresh_at sb x) /\
  (!sa op sb. compile_slice_calldata start sz n sa = (op,sb) ==>
     !x. op = Var x ==> not_fresh_at sb x) /\
  (!sa op sb. compile_slice_code start sz n sa = (op,sb) ==>
     !x. op = Var x ==> not_fresh_at sb x) /\
  (!sa op sb. compile_slice_out_buf n sa = ((buf,data),sb) ==>
     !x. buf = Var x ==> not_fresh_at sb x) /\
  (!sa op sb. (!x. buf = Var x ==> not_fresh_at sa x) /\
     compile_slice_extcode addr start sz buf data sa = (op,sb) ==>
     !x. op = Var x ==> not_fresh_at sb x)
Proof
  rpt conj_tac >>
  simp[builtinBytesTheory.compile_slice_data_def,
       builtinBytesTheory.compile_slice_memory_def,
       builtinBytesTheory.compile_slice_calldata_def,
       builtinBytesTheory.compile_slice_code_def,
       builtinBytesTheory.compile_slice_out_buf_def,
       builtinBytesTheory.compile_slice_extcode_def,
       builtinBytesTheory.compile_bytestring_src_def,
       builtinBytesTheory.compile_assert_slice_bounds_def,
       contextTheory.compile_alloc_buffer_def, emit_op_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[] >>
  gvs[compileEnvTheory.not_fresh_at_def, ASCIInumbersTheory.toString_11]
QED

Theorem compiler_uint2str_var:
  compile_uint2str v nd n sa = (op,sb) ==>
  !x. op = Var x ==> not_fresh_at sb x
Proof
  simp[builtinStringsTheory.compile_uint2str_def,
       contextTheory.compile_alloc_buffer_def, emit_op_def, emit_void_def,
       emit_inst_def, new_block_def, fresh_label_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[] >>
  gvs[compileEnvTheory.not_fresh_at_def, ASCIInumbersTheory.toString_11]
QED

Theorem compiler_as_wei_value_var:
  (!x. v = Var x ==> not_fresh_at sa x) ==>
  (!op sb. compile_as_wei_value_int v scale signed sa = (op,sb) ==>
     !x. op = Var x ==> not_fresh_at sb x) /\
  (!op sb. compile_as_wei_value_decimal v scale divisor sa = (op,sb) ==>
     !x. op = Var x ==> not_fresh_at sb x)
Proof
  strip_tac >> Cases_on `signed` >> conj_tac >>
  simp[builtinMiscTheory.compile_as_wei_value_int_def,
       builtinMiscTheory.compile_as_wei_value_decimal_def] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  simp[emit_op_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[] >>
  gvs[compileEnvTheory.not_fresh_at_def, ASCIInumbersTheory.toString_11]
QED

Theorem compiler_concat_var:
  (!ce ty e s. ci_mono s (SND (cfn ce ty e s))) /\
  compile_builtin_dispatch_body cfn cenv rt ty (Concat n) args sa = (vv,sb) ==>
  !x. vv_operand vv = Var x ==> not_fresh_at sb x
Proof
  strip_tac >>
  qpat_x_assum `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_builtin_dispatch_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
  gvs[contextTheory.vv_operand_def, contextTheory.base_ptr_def] >>
  drule compiler_alloc_buffer_var >> strip_tac >>
  irule freshWritesTheory.not_fresh_at_mono >>
  rename1 `compile_alloc_buffer _ sa = (buf,sm)` >> qexists `sm` >>
  reverse conj_tac >- metis_tac[] >>
  rename1 `emit_op ADD _ sm = (_,sn)` >>
  rename1 `compile_concat _ _ _ _ _ _ sn = (_,sk)` >>
  `sm.cs_next_var <= sn.cs_next_var` by
    metis_tac[compiler_counter_emit, pairTheory.SND] >>
  `sn.cs_next_var <= sk.cs_next_var` by
    metis_tac[ci_mono_compile_concat_cfn, ci_mono_def, pairTheory.SND] >>
  `sk.cs_next_var <= sb.cs_next_var` by
    metis_tac[compiler_counter_emit, pairTheory.SND] >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

(* Both value wrappers expose the same Var-only result obligation. *)
fun builtin_result_var_tac pat =
  rpt (pairarg_tac >> gvs[]) >>
  qmatch_goalsub_abbrev_tac pat >>
  Cases_on `result` >>
  gvs[as_stack_val_def, as_ptr_val_def, markerTheory.Abbrev_def] >>
  rpt strip_tac >>
  gvs[contextTheory.vv_operand_def, contextTheory.mk_ptr_def];

val builtin_stack_var_tac = builtin_result_var_tac `as_stack_val _ result`;
val builtin_ptr_var_tac = builtin_result_var_tac `as_ptr_val _ LocMemory result`;

Theorem compiler_builtin_var:
  (!ce ty e s. ci_mono s (SND (cfn ce ty e s))) /\
  (!ce ty e s vv s'. cfn ce ty e s = (vv,s') ==>
     !x. vv_operand vv = Var x ==> not_fresh_at s' x) /\
  compile_builtin_dispatch_body cfn cenv rt ty bi args sa = (vv,sb) ==>
  !x. vv_operand vv = Var x ==> not_fresh_at sb x
Proof
  strip_tac >>
  `!ce ty e s op s'. lower_value cfn ce ty e s = (op,s') ==>
     !x. op = Var x ==> not_fresh_at s' x` by
    metis_tac[compiler_lower_value_var] >>
  qpat_x_assum `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _` mp_tac >>
  Cases_on `bi`
  >~ [`compile_builtin_dispatch_body _ _ _ _ (Bop _) _ _`] >- suspend "bop"
  >~ [`compile_builtin_dispatch_body _ _ _ _ (Concat _) _ _`] >-
    (rpt strip_tac >> metis_tac[compiler_concat_var])
  >~ [`compile_builtin_dispatch_body _ _ _ _ (Slice _) _ _`] >- suspend "slice"
  >~ [`compile_builtin_dispatch_body _ _ _ _ (MakeArray _ _) _ _`] >- suspend "array"
  >~ [`compile_builtin_dispatch_body _ _ _ _ MethodId _ _`] >- suspend "method"
  >~ [`compile_builtin_dispatch_body _ _ _ _ (AsWeiValue _) _ _`] >- suspend "wei" >>
  simp[compile_builtin_dispatch_body_def, LET_THM]
  >~ [`compile_acc _ _ _ _ _`] >-
    (builtin_stack_var_tac >> metis_tac[compiler_acc_var])
  >~ [`compile_keccak256_bytes _ _`] >- suspend "keccak"
  >~ [`compile_sha256_bytes _ _`] >- suspend "sha"
  >~ [`compile_slice_calldata _ _ _ _`] >- suspend "calldata"
  >~ [`compile_builtin_len _ _ _ _`] >- suspend "len"
  >~ [`compile_ecadd_points _ _ _`] >- suspend "ecadd"
  >~ [`compile_ecmul_point _ _ _`] >- suspend "ecmul"
  >~ [`compile_uint2str _ _ _ _`] >- suspend "uint2str"
  >~ [`compile_invert _ _ _ _`] >-
    (Cases_on `expr_type (HD args) = BaseT BoolT` >> simp[] >> builtin_stack_var_tac >>
     metis_tac[exprSafeOperandTheory.compile_invert_safe_operand,
               exprSafeOperandTheory.emit_op_safe_operand,
               exprSafeOperandTheory.safe_operand_def])
  >~ [`compile_neg _ _ _`] >-
    (builtin_stack_var_tac >>
     metis_tac[exprSafeOperandTheory.compile_neg_safe_operand,
               exprSafeOperandTheory.safe_operand_def])
  >~ [`compile_builtin_abs _ _`] >-
    (builtin_stack_var_tac >>
     metis_tac[exprSafeOperandBuiltinsTheory.compile_builtin_abs_safe_operand,
               exprSafeOperandTheory.safe_operand_def])
  >~ [`compile_env_var _ _`] >-
    (builtin_stack_var_tac >>
     metis_tac[exprSafeOperandBuiltinsTheory.compile_env_var_safe_operand,
               exprSafeOperandTheory.safe_operand_def])
  >~ [`compile_builtin_calldatasize _`] >-
    (builtin_stack_var_tac >>
     metis_tac[exprSafeOperandBuiltinsTheory.compile_builtin_calldatasize_safe_operand,
               exprSafeOperandTheory.safe_operand_def])
  >~ [`compile_blockhash _ _`] >-
    (builtin_stack_var_tac >>
     metis_tac[exprSafeOperandBuiltinsTheory.compile_blockhash_safe_operand,
               exprSafeOperandTheory.safe_operand_def])
  >~ [`compile_blobhash _ _`] >-
    (builtin_stack_var_tac >>
     metis_tac[exprSafeOperandBuiltinsTheory.compile_blobhash_safe_operand,
               exprSafeOperandTheory.safe_operand_def])
  >~ [`compile_addmod _ _ _ _`] >-
    (builtin_stack_var_tac >>
     metis_tac[exprSafeOperandTheory.compile_addmod_safe_operand,
               exprSafeOperandTheory.safe_operand_def])
  >~ [`compile_mulmod _ _ _ _`] >-
    (builtin_stack_var_tac >>
     metis_tac[exprSafeOperandTheory.compile_mulmod_safe_operand,
               exprSafeOperandTheory.safe_operand_def])
  >~ [`compile_ceil _ _ _`] >-
    (builtin_stack_var_tac >>
     metis_tac[exprSafeOperandBuiltinsTheory.compile_ceil_safe_operand,
               exprSafeOperandTheory.safe_operand_def])
  >~ [`compile_floor _ _ _`] >-
    (builtin_stack_var_tac >>
     metis_tac[exprSafeOperandBuiltinsTheory.compile_floor_safe_operand,
               exprSafeOperandTheory.safe_operand_def])
  >~ [`compile_pow_mod256 _ _ _`] >-
    (builtin_stack_var_tac >>
     metis_tac[exprSafeOperandTheory.compile_pow_mod256_safe_operand,
               exprSafeOperandTheory.safe_operand_def]) >>
  builtin_stack_var_tac >>
  metis_tac[exprSafeOperandBuiltinsTheory.compile_ecrecover_safe_operand,
            exprSafeOperandTheory.safe_operand_def]
QED

Resume compiler_builtin_var[bop]:
  simp[compile_builtin_dispatch_body_def, LET_THM] >>
  IF_CASES_TAC
  >- (Cases_on `HD (TL args)` >> simp[]
      >~ [`HD (TL args) = Builtin ann bi es`] >-
        (Cases_on `bi` >> simp[] >>
         rpt (pairarg_tac >> gvs[]) >>
         rpt (IF_CASES_TAC >> simp[]) >> builtin_stack_var_tac >>
         metis_tac[exprSafeOperandBuiltinsTheory.compile_list_membership_in_safe_operand,
                   exprSafeOperandBuiltinsTheory.compile_list_membership_notin_safe_operand,
                   exprSafeOperandBuiltinsTheory.compile_var_array_membership_safe_operand,
                   exprSafeOperandTheory.safe_operand_def]) >>
      builtin_stack_var_tac >>
      metis_tac[exprSafeOperandBuiltinsTheory.compile_var_array_membership_safe_operand,
                exprSafeOperandTheory.safe_operand_def]) >>
  IF_CASES_TAC
  >- (rpt (pairarg_tac >> gvs[]) >>
      rpt (IF_CASES_TAC >> simp[]) >> builtin_stack_var_tac >>
      metis_tac[exprSafeOperandTheory.emit_op_safe_operand,
                exprSafeOperandTheory.safe_operand_def]) >>
  builtin_stack_var_tac >>
  metis_tac[exprSafeOperandTheory.compile_binop_safe_operand,
            exprSafeOperandTheory.safe_operand_def]
QED
Resume compiler_builtin_var[slice]:
  simp[compile_builtin_dispatch_body_def, LET_THM] >>
  IF_CASES_TAC
  >- (builtin_ptr_var_tac >> metis_tac[compiler_slice_var]) >>
  IF_CASES_TAC
  >- (builtin_ptr_var_tac >> metis_tac[compiler_slice_var]) >>
  IF_CASES_TAC
  >- (builtin_ptr_var_tac >>
      `!x. out_buf = Var x ==> not_fresh_at st4 x` by
        metis_tac[compiler_slice_var] >>
      metis_tac[compiler_slice_var]) >>
  rpt (pairarg_tac >> gvs[]) >>
  IF_CASES_TAC >> builtin_ptr_var_tac >>
  metis_tac[compiler_slice_var]
QED
Resume compiler_builtin_var[array]:
  Cases_on `o'` >> simp[compile_builtin_dispatch_body_def, LET_THM] >>
  builtin_ptr_var_tac >>
  `!x. buf_op_alloc.buf_operand = Var x ==> not_fresh_at st2 x` by
    metis_tac[compiler_alloc_buffer_var] >>
  metis_tac[compiler_aggregate_buffer_var]
QED
Resume compiler_builtin_var[method]:
  Cases_on `method_id_literal (HD args)` >>
  simp[compile_builtin_dispatch_body_def, LET_THM]
  >- (rpt (pairarg_tac >> gvs[]) >>
      IF_CASES_TAC
      >- (builtin_stack_var_tac >> metis_tac[compiler_method_id_runtime_var]) >>
      builtin_ptr_var_tac >> metis_tac[compiler_method_id_runtime_var]) >>
  metis_tac[compiler_literal_var]
QED
Resume compiler_builtin_var[wei]:
  simp[compile_builtin_dispatch_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> IF_CASES_TAC >>
  builtin_stack_var_tac >>
  `!x. v = Var x ==> not_fresh_at st1 x` by metis_tac[] >>
  metis_tac[compiler_as_wei_value_var]
QED
Resume compiler_builtin_var[keccak]:
  IF_CASES_TAC
  >- (builtin_stack_var_tac >>
      metis_tac[exprSafeOperandBuiltinsTheory.compile_keccak256_bytes_safe_operand,
                exprSafeOperandTheory.safe_operand_def]) >>
  rpt CASE_TAC >> simp[] >> builtin_stack_var_tac >>
  metis_tac[exprSafeOperandBuiltinsTheory.compile_keccak256_bytesm_safe_operand,
            exprSafeOperandBuiltinsTheory.compile_keccak256_word_safe_operand,
            exprSafeOperandTheory.safe_operand_def]
QED
Resume compiler_builtin_var[sha]:
  IF_CASES_TAC
  >- (builtin_stack_var_tac >>
      metis_tac[exprSafeOperandBuiltinsTheory.compile_sha256_bytes_safe_operand,
                exprSafeOperandTheory.safe_operand_def]) >>
  rpt CASE_TAC >> simp[] >> builtin_stack_var_tac >>
  metis_tac[exprSafeOperandBuiltinsTheory.compile_sha256_bytesm_safe_operand,
            exprSafeOperandBuiltinsTheory.compile_sha256_word_safe_operand,
            exprSafeOperandTheory.safe_operand_def]
QED
Resume compiler_builtin_var[calldata]:
  builtin_ptr_var_tac >> metis_tac[compiler_slice_var]
QED
Resume compiler_builtin_var[len]:
  IF_CASES_TAC >> builtin_stack_var_tac >>
  metis_tac[exprSafeOperandBuiltinsTheory.compile_builtin_len_safe_operand,
            exprSafeOperandBuiltinsTheory.compile_builtin_calldatasize_safe_operand,
            exprSafeOperandTheory.safe_operand_def]
QED
Resume compiler_builtin_var[ecadd]:
  builtin_ptr_var_tac >> metis_tac[compiler_ec_points_var]
QED
Resume compiler_builtin_var[ecmul]:
  builtin_ptr_var_tac >> metis_tac[compiler_ec_points_var]
QED
Resume compiler_builtin_var[uint2str]:
  builtin_ptr_var_tac >> metis_tac[compiler_uint2str_var]
QED

Finalise compiler_builtin_var

Theorem compiler_modular_names_var:
  (!sa vv sb.
     compile_addmod_names ce rt aty a bty b mty m sa = (vv,sb) ==>
     !x. vv_operand vv = Var x ==> not_fresh_at sb x) /\
  (!sa vv sb.
     compile_mulmod_names ce rt aty a bty b mty m sa = (vv,sb) ==>
     !x. vv_operand vv = Var x ==> not_fresh_at sb x) /\
  (!sa vv sb.
     compile_powmod256_names ce rt aty a bty b sa = (vv,sb) ==>
     !x. vv_operand vv = Var x ==> not_fresh_at sb x)
Proof
  rpt conj_tac >> rpt gen_tac >>
  simp[compile_addmod_names_def, compile_mulmod_names_def,
       compile_powmod256_names_def, LET_THM] >>
  builtin_stack_var_tac >>
  metis_tac[exprSafeOperandTheory.compile_addmod_safe_operand,
            exprSafeOperandTheory.compile_mulmod_safe_operand,
            exprSafeOperandTheory.compile_pow_mod256_safe_operand,
            exprSafeOperandTheory.safe_operand_def]
QED

(* Reservation is an invariant of monotone compiler continuations. *)
Theorem compiler_ci_mono_reserved:
  ci_mono sa sb /\ local_ptrs_reserved ce sa ==>
  local_ptrs_reserved ce sb
Proof
  metis_tac[local_ptrs_reserved_next_var, ci_mono_def]
QED

Theorem compiler_guarded_callback_ci_mono:
  (!ce ty e s. ci_mono s (SND (f ce ty e s))) ==>
  !ce ty e s.
    ci_mono s (SND ((\ce ty e s.
      if local_ptrs_reserved ce s then f ce ty e s
      else (StackValue ty (Lit 0w),s)) ce ty e s))
Proof
  rpt strip_tac >> simp[] >> IF_CASES_TAC >>
  simp[ci_mono_def, cs_extends_refl]
QED

Theorem compiler_guarded_callback_var:
  (!ce ty e s vv sb. local_ptrs_reserved ce s /\
    f ce ty e s = (vv,sb) ==>
    !x. vv_operand vv = Var x ==> not_fresh_at sb x) ==>
  !ce ty e s vv sb.
    (\ce ty e s. if local_ptrs_reserved ce s then f ce ty e s
      else (StackValue ty (Lit 0w),s)) ce ty e s = (vv,sb) ==>
    !x. vv_operand vv = Var x ==> not_fresh_at sb x
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> simp[] >>
  IF_CASES_TAC >- metis_tac[] >>
  simp[contextTheory.vv_operand_def] >> rpt strip_tac >>
  gvs[contextTheory.vv_operand_def]
QED

(* Equality at reachable callback entries is sufficient for sequencing. *)
Theorem compiler_lower_value_reserved_cong:
  (!ty e s. local_ptrs_reserved ce s ==> f ce ty e s = g ce ty e s) /\
  local_ptrs_reserved ce sa ==>
  lower_value f ce ty e sa = lower_value g ce ty e sa
Proof
  simp[lower_value_def, comp_bind_def]
QED

Theorem compiler_multi_vvs_reserved_cong:
  (!ce ty e s. ci_mono s (SND (f ce ty e s))) /\
  (!ty e s. local_ptrs_reserved ce s ==> f ce ty e s = g ce ty e s) ==>
  !es sa. local_ptrs_reserved ce sa ==>
    compile_multi_vvs f ce es sa = compile_multi_vvs g ce es sa
Proof
  strip_tac >> Induct >> simp[compile_multi_vvs_def, comp_return_def] >>
  rpt strip_tac >> simp[comp_bind_def] >>
  `f ce (expr_type h) h sa = g ce (expr_type h) h sa` by simp[] >>
  asm_rewrite_tac[] >>
  Cases_on `g ce (expr_type h) h sa` >> simp[] >>
  `local_ptrs_reserved ce r` by
    (irule compiler_ci_mono_reserved >> qexists `sa` >>
     metis_tac[pairTheory.SND]) >>
  simp[]
QED

Theorem compiler_multi_exprs_reserved_cong:
  (!ce ty e s. ci_mono s (SND (f ce ty e s))) /\
  (!ty e s. local_ptrs_reserved ce s ==> f ce ty e s = g ce ty e s) ==>
  !es sa. local_ptrs_reserved ce sa ==>
    compile_multi_exprs f ce es sa = compile_multi_exprs g ce es sa
Proof
  strip_tac >> Induct >> simp[compile_multi_exprs_def, comp_return_def] >>
  rpt strip_tac >>
  `lower_value f ce (expr_type h) h sa =
   lower_value g ce (expr_type h) h sa` by
    (irule compiler_lower_value_reserved_cong >> simp[]) >>
  simp[comp_bind_def] >> asm_rewrite_tac[] >>
  Cases_on `lower_value g ce (expr_type h) h sa` >> simp[] >>
  `local_ptrs_reserved ce r` by
    (irule compiler_ci_mono_reserved >> qexists `sa` >>
     metis_tac[ci_mono_lower_value_cfn, pairTheory.SND]) >>
  simp[]
QED

Theorem compiler_reserved_bind_cong:
  (!s. local_ptrs_reserved ce s ==> a s = b s) /\
  (!s. ci_mono s (SND (a s))) /\
  (!v s. local_ptrs_reserved ce s ==> k v s = l v s) /\
  local_ptrs_reserved ce sa ==>
  comp_bind a k sa = comp_bind b l sa
Proof
  rpt strip_tac >> simp[comp_bind_def] >>
  `a sa = b sa` by simp[] >> asm_rewrite_tac[] >>
  Cases_on `b sa` >> simp[] >>
  rename1 `b sa = (v,sb)` >>
  `local_ptrs_reserved ce sb` by
    (irule compiler_ci_mono_reserved >> qexists `sa` >>
     metis_tac[pairTheory.SND]) >>
  simp[]
QED

Theorem compiler_reserved_ignore_bind_cong:
  (!s. local_ptrs_reserved ce s ==> a s = b s) /\
  (!s. ci_mono s (SND (a s))) /\
  (!s. local_ptrs_reserved ce s ==> k s = l s) /\
  local_ptrs_reserved ce sa ==>
  comp_ignore_bind a k sa = comp_ignore_bind b l sa
Proof
  simp[comp_ignore_bind_def] >> strip_tac >>
  irule compiler_reserved_bind_cong >> simp[] >> metis_tac[]
QED

Theorem compiler_make_tuple_reserved_cong:
  (!ce ty e s. ci_mono s (SND (f ce ty e s))) /\
  (!ty e s. local_ptrs_reserved ce s ==> f ce ty e s = g ce ty e s) ==>
  !es buf off sa. local_ptrs_reserved ce sa ==>
    compile_make_tuple f ce es buf off sa =
    compile_make_tuple g ce es buf off sa
Proof
  strip_tac >> Induct >- simp[compile_make_tuple_def] >>
  rpt gen_tac >> strip_tac >> simp[compile_make_tuple_def] >>
  irule compiler_reserved_bind_cong >> simp[] >> qexists `ce` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  irule compiler_reserved_bind_cong >> simp[ci_mono_emit_op] >>
  qexists `ce` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  irule compiler_reserved_bind_cong >> simp[ci_mono_unwrap_value] >>
  qexists `ce` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  irule compiler_reserved_ignore_bind_cong >>
  simp[ci_mono_compile_store_memory] >> qexists `ce` >> simp[]
QED

Theorem compiler_make_array_elems_reserved_cong:
  (!ce ty e s. ci_mono s (SND (f ce ty e s))) /\
  (!ty e s. local_ptrs_reserved ce s ==> f ce ty e s = g ce ty e s) ==>
  !es ty sz lw buf idx sa. local_ptrs_reserved ce sa ==>
    compile_make_array_elems f ce es ty sz lw buf idx sa =
    compile_make_array_elems g ce es ty sz lw buf idx sa
Proof
  strip_tac >> Induct >- simp[compile_make_array_elems_def] >>
  rpt gen_tac >> strip_tac >> simp[compile_make_array_elems_def] >>
  irule compiler_reserved_bind_cong >> simp[] >> qexists `ce` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  irule compiler_reserved_bind_cong >> simp[ci_mono_emit_op] >>
  qexists `ce` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  irule compiler_reserved_bind_cong >> simp[ci_mono_unwrap_value] >>
  qexists `ce` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  irule compiler_reserved_ignore_bind_cong >>
  simp[ci_mono_compile_store_memory] >> qexists `ce` >> simp[]
QED

Theorem compiler_make_array_reserved_cong:
  (!ce ty e s. ci_mono s (SND (f ce ty e s))) /\
  (!ty e s. local_ptrs_reserved ce s ==> f ce ty e s = g ce ty e s) /\
  local_ptrs_reserved ce sa ==>
  compile_make_array f ce es ty sz lw buf sa =
  compile_make_array g ce es ty sz lw buf sa
Proof
  strip_tac >> simp[compile_make_array_def] >>
  irule compiler_reserved_ignore_bind_cong >>
  conj_tac >- (gen_tac >> Cases_on `lw`
    >- simp[ci_mono_emit_void] >>
    simp[comp_return_def, ci_mono_def, cs_extends_refl]) >>
  qexists `ce` >> simp[] >>
  metis_tac[compiler_make_array_elems_reserved_cong]
QED

Theorem compiler_struct_lit_reserved_cong:
  (!ce ty e s. ci_mono s (SND (f ce ty e s))) /\
  (!ty e s. local_ptrs_reserved ce s ==> f ce ty e s = g ce ty e s) ==>
  !fields ty buf off sa. local_ptrs_reserved ce sa ==>
    compile_struct_lit f ce ty fields buf off sa =
    compile_struct_lit g ce ty fields buf off sa
Proof
  strip_tac >> Induct >- simp[compile_struct_lit_def] >>
  rpt gen_tac >> strip_tac >> PairCases_on `h` >>
  simp[compile_struct_lit_def] >>
  irule compiler_reserved_bind_cong >> simp[] >> qexists `ce` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  irule compiler_reserved_bind_cong >> simp[ci_mono_emit_op] >>
  qexists `ce` >> simp[] >> rpt gen_tac >> strip_tac >>
  irule compiler_reserved_bind_cong >> simp[ci_mono_unwrap_value] >>
  qexists `ce` >> simp[] >> rpt gen_tac >> strip_tac >>
  irule compiler_reserved_ignore_bind_cong >>
  simp[ci_mono_compile_store_memory] >> qexists `ce` >> simp[]
QED

Theorem compiler_concat_reserved_cong:
  (!ce ty e s. ci_mono s (SND (f ce ty e s))) /\
  (!ty e s. local_ptrs_reserved ce s ==> f ce ty e s = g ce ty e s) ==>
  !es dp infos off sa. local_ptrs_reserved ce sa ==>
    compile_concat f ce es dp infos off sa =
    compile_concat g ce es dp infos off sa
Proof
  strip_tac >> Induct >- simp[compile_concat_def] >>
  rpt gen_tac >> strip_tac >> Cases_on `infos`
  >- simp[compile_concat_def] >>
  rename1 `compile_concat f ce (e::es) dp (info::rest) off sa` >>
  PairCases_on `info` >>
  simp[compile_concat_def] >> IF_CASES_TAC >> simp[] >>
  irule compiler_reserved_bind_cong >>
  simp[ci_mono_lower_value_cfn] >> qexists `ce` >>
  simp[compiler_lower_value_reserved_cong] >>
  rpt gen_tac >> strip_tac >>
  rpt (irule compiler_reserved_bind_cong >> simp[ci_mono_emit_op] >>
       qexists `ce` >> simp[] >> rpt gen_tac >> strip_tac) >>
  irule compiler_reserved_ignore_bind_cong >> simp[ci_mono_emit_void] >>
  qexists `ce` >> simp[] >> rpt gen_tac >> strip_tac >>
  irule compiler_reserved_bind_cong >> simp[ci_mono_emit_op] >>
  qexists `ce` >> simp[]
QED

Theorem compiler_attribute_reserved_cong:
  (!ty e s. local_ptrs_reserved ce s ==> f ce ty e s = g ce ty e s) /\
  local_ptrs_reserved ce sa ==>
  compile_attribute f ce rt ty e fld sa = compile_attribute g ce rt ty e fld sa
Proof
  simp[compile_attribute_def, comp_bind_def]
QED

Theorem compiler_acc_reserved_cong:
  (!ty e s. local_ptrs_reserved ce s ==> f ce ty e s = g ce ty e s) /\
  local_ptrs_reserved ce sa ==>
  compile_acc f ce e item sa = compile_acc g ce e item sa
Proof
  strip_tac >>
  `!ty. lower_value f ce ty e sa = lower_value g ce ty e sa` by
    (gen_tac >> irule compiler_lower_value_reserved_cong >> simp[]) >>
  Cases_on `item` >> simp[compile_acc_def]
QED

Theorem compiler_subscript_reserved_cong:
  (!ce ty e s. ci_mono s (SND (f ce ty e s))) /\
  (!ty e s. local_ptrs_reserved ce s ==> f ce ty e s = g ce ty e s) /\
  local_ptrs_reserved ce sa ==>
  compile_subscript f ce rt ty base_e idx sa =
  compile_subscript g ce rt ty base_e idx sa
Proof
  strip_tac >> simp[compile_subscript_def] >>
  qmatch_goalsub_abbrev_tac `ce.ce_is_hashmap vn` >>
  IF_CASES_TAC >> simp[]
  >- (irule compiler_reserved_bind_cong >> simp[ci_mono_lower_value_cfn] >>
      qexists `ce` >> simp[compiler_lower_value_reserved_cong]) >>
  Cases_on `ce.ce_var_type vn` >> simp[]
  >- (irule compiler_reserved_bind_cong >> simp[] >> qexists `ce` >> simp[] >>
      rpt gen_tac >> strip_tac >>
      simp[comp_bind_def, comp_return_def] >>
      AP_TERM_TAC >> irule compiler_lower_value_reserved_cong >> simp[]) >>
  rename1 `SOME bty` >> Cases_on `bty` >> simp[] >>
  irule compiler_reserved_bind_cong >> simp[] >> qexists `ce` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  simp[comp_bind_def, comp_return_def] >>
  AP_TERM_TAC >> irule compiler_lower_value_reserved_cong >> simp[]
QED

Theorem compiler_ext_call_kwarg_reserved_cong:
  (!ty e s. local_ptrs_reserved ce s ==> f ce ty e s = g ce ty e s) /\
  local_ptrs_reserved ce sa ==>
  compile_ext_call_kwarg f ce rt k e sa = compile_ext_call_kwarg g ce rt k e sa
Proof
  strip_tac >> simp[compile_ext_call_kwarg_def] >>
  IF_CASES_TAC >> simp[comp_bind_def] >>
  AP_TERM_TAC >> irule compiler_lower_value_reserved_cong >> simp[]
QED

Theorem compiler_ext_call_kwargs_reserved_cong:
  (!ce ty e s. ci_mono s (SND (f ce ty e s))) /\
  (!ty e s. local_ptrs_reserved ce s ==> f ce ty e s = g ce ty e s) ==>
  !ks es rt sa. local_ptrs_reserved ce sa ==>
    compile_ext_call_kwargs f ce rt ks es sa =
    compile_ext_call_kwargs g ce rt ks es sa
Proof
  strip_tac >> Induct >> Cases_on `es` >>
  simp[compile_ext_call_kwargs_def] >> rpt gen_tac >> strip_tac >>
  irule compiler_reserved_bind_cong >> simp[ci_mono_compile_ext_call_kwarg] >>
  qexists `ce` >> simp[compiler_ext_call_kwarg_reserved_cong] >>
  rpt gen_tac >> strip_tac >> rename1 `local_ptrs_reserved ce sb` >>
  `!es rt. compile_ext_call_kwargs f ce rt ks es sb =
               compile_ext_call_kwargs g ce rt ks es sb` by simp[] >>
  Cases_on `v` >> simp[comp_bind_def]
QED

Theorem compiler_intcall_reserved_cong:
  (!ce ty e s. ci_mono s (SND (f ce ty e s))) /\
  (!ty e s. local_ptrs_reserved ce s ==> f ce ty e s = g ce ty e s) /\
  local_ptrs_reserved ce sa ==>
  compile_call f ce rt ty (IntCall id) args dr sa =
  compile_call g ce rt ty (IntCall id) args dr sa
Proof
  strip_tac >>
  `compile_multi_vvs f ce args sa = compile_multi_vvs g ce args sa` by
    (irule compiler_multi_vvs_reserved_cong >> simp[]) >>
  simp[compile_call_def]
QED

Theorem compiler_extcall_reserved_cong:
  (!ce ty e s. ci_mono s (SND (f ce ty e s))) /\
  (!ty e s. local_ptrs_reserved ce s ==> f ce ty e s = g ce ty e s) /\
  local_ptrs_reserved ce sa ==>
  compile_call f ce rt ty (ExtCall static skip (name,ats,rt') opts) args dr sa =
  compile_call g ce rt ty (ExtCall static skip (name,ats,rt') opts) args dr sa
Proof
  strip_tac >> Cases_on `args` >- simp[compile_call_def] >>
  rename1 `addr_e::args` >>
  `lower_value f ce (BaseT AddressT) addr_e sa =
   lower_value g ce (BaseT AddressT) addr_e sa` by
    (irule compiler_lower_value_reserved_cong >> simp[]) >>
  Cases_on `lower_value f ce (BaseT AddressT) addr_e sa` >>
  rename1 `lower_value f _ _ _ _ = (addr,sb)` >>
  `local_ptrs_reserved ce sb` by
    (irule compiler_ci_mono_reserved >> qexists `sa` >>
     metis_tac[ci_mono_lower_value_cfn, pairTheory.SND]) >>
  `compile_multi_vvs f ce (TAKE (LENGTH ats) args) sb =
   compile_multi_vvs g ce (TAKE (LENGTH ats) args) sb` by
    (irule compiler_multi_vvs_reserved_cong >> simp[]) >>
  Cases_on `compile_multi_vvs f ce (TAKE (LENGTH ats) args) sb` >>
  rename1 `compile_multi_vvs f _ _ _ = (vals,sc)` >>
  `local_ptrs_reserved ce sc` by
    (irule compiler_ci_mono_reserved >> qexists `sb` >>
     metis_tac[ci_mono_compile_multi_vvs, pairTheory.SND]) >>
  `compile_ext_call_kwargs f ce rt' opts (DROP (LENGTH ats) args) sc =
   compile_ext_call_kwargs g ce rt' opts (DROP (LENGTH ats) args) sc` by
    (irule compiler_ext_call_kwargs_reserved_cong >> simp[]) >>
  qpat_x_assum `(addr,sb) = _` (assume_tac o SYM) >>
  qpat_x_assum `(vals,sc) = _` (assume_tac o SYM) >>
  simp[compile_call_def, LET_THM]
QED

Theorem compiler_send_reserved_cong:
  (!ce ty e s. ci_mono s (SND (f ce ty e s))) /\
  (!ty e s. local_ptrs_reserved ce s ==> f ce ty e s = g ce ty e s) /\
  local_ptrs_reserved ce sa ==>
  compile_call f ce rt ty (Send has_gas) args dr sa =
  compile_call g ce rt ty (Send has_gas) args dr sa
Proof
  strip_tac >> Cases_on `args` >- simp[compile_call_def] >>
  rename1 `addr_e::args` >> Cases_on `args` >- simp[compile_call_def] >>
  rename1 `addr_e::val_e::gas_es` >>
  Cases_on `LENGTH gas_es = if has_gas then 1 else 0`
  >- ( `lower_value f ce (BaseT AddressT) addr_e sa =
        lower_value g ce (BaseT AddressT) addr_e sa` by
         (irule compiler_lower_value_reserved_cong >> simp[]) >>
       Cases_on `lower_value f ce (BaseT AddressT) addr_e sa` >>
       rename1 `lower_value f _ _ _ _ = (addr,sb)` >>
       `local_ptrs_reserved ce sb` by
         (irule compiler_ci_mono_reserved >> qexists `sa` >>
          metis_tac[ci_mono_lower_value_cfn, pairTheory.SND]) >>
       `lower_value f ce (BaseT (UintT 256)) val_e sb =
        lower_value g ce (BaseT (UintT 256)) val_e sb` by
         (irule compiler_lower_value_reserved_cong >> simp[]) >>
       Cases_on `lower_value f ce (BaseT (UintT 256)) val_e sb` >>
       rename1 `lower_value f _ _ _ _ = (value,sc)` >>
       `local_ptrs_reserved ce sc` by
         (irule compiler_ci_mono_reserved >> qexists `sb` >>
          metis_tac[ci_mono_lower_value_cfn, pairTheory.SND]) >>
       `!e ty. lower_value f ce ty e sc = lower_value g ce ty e sc` by
         (rpt gen_tac >> irule compiler_lower_value_reserved_cong >> simp[]) >>
       qpat_x_assum `(addr,sb) = _` (assume_tac o SYM) >>
       qpat_x_assum `(value,sc) = _` (assume_tac o SYM) >>
       Cases_on `gas_es` >- simp[compile_call_def] >>
       rename1 `LENGTH (gas_e::rest) = _` >>
       Cases_on `rest` >> simp[compile_call_def]) >>
  simp[compile_call_def]
QED

Theorem compiler_raw_call_calldata_reserved_cong:
  (!ce ty e s. ci_mono s (SND (f ce ty e s))) /\
  (!ty e s. local_ptrs_reserved ce s ==> f ce ty e s = g ce ty e s) /\
  local_ptrs_reserved ce sa ==>
  compile_call f ce rt ty (RawCallCalldataTarget rcf) args dr sa =
  compile_call g ce rt ty (RawCallCalldataTarget rcf) args dr sa
Proof
  strip_tac >> Cases_on `args` >- simp[compile_call_def] >>
  rename1 `addr_e::args` >> Cases_on `args` >- simp[compile_call_def] >>
  rename1 `addr_e::value_e::tail` >> Cases_on `tail`
  >- (`lower_value f ce (BaseT AddressT) addr_e sa =
       lower_value g ce (BaseT AddressT) addr_e sa` by
        (irule compiler_lower_value_reserved_cong >> simp[]) >>
      Cases_on `lower_value f ce (BaseT AddressT) addr_e sa` >>
      rename1 `lower_value f _ _ _ _ = (addr,sb)` >>
      `local_ptrs_reserved ce sb` by
        (irule compiler_ci_mono_reserved >> qexists `sa` >>
         metis_tac[ci_mono_lower_value_cfn, pairTheory.SND]) >>
      Cases_on `compile_msg_data_to_memory sb` >>
      rename1 `compile_msg_data_to_memory sb = (data,sc)` >>
      `local_ptrs_reserved ce sc` by
        (irule compiler_ci_mono_reserved >> qexists `sb` >>
         metis_tac[ci_mono_compile_msg_data_to_memory, pairTheory.SND]) >>
      `lower_value f ce (BaseT (UintT 256)) value_e sc =
       lower_value g ce (BaseT (UintT 256)) value_e sc` by
        (irule compiler_lower_value_reserved_cong >> simp[]) >>
      qpat_x_assum `(addr,sb) = _` (assume_tac o SYM) >>
      Cases_on `data` >> simp[compile_call_def]) >>
  simp[compile_call_def]
QED

Theorem compiler_call_reserved_cong:
  (!ce ty e s. ci_mono s (SND (f ce ty e s))) /\
  (!ty e s. local_ptrs_reserved ce s ==> f ce ty e s = g ce ty e s) /\
  local_ptrs_reserved ce sa ==>
  compile_call f ce rt ty target args dr sa =
  compile_call g ce rt ty target args dr sa
Proof
  strip_tac >> Cases_on `target` >>
  FIRST [irule compiler_intcall_reserved_cong >> simp[],
         irule compiler_send_reserved_cong >> simp[],
         irule compiler_raw_call_calldata_reserved_cong >> simp[],
         rename1 `ExtCall _ _ signature _` >> PairCases_on `signature` >>
           irule compiler_extcall_reserved_cong >> simp[],
         simp[compile_call_def]]
QED

Theorem compiler_type_builtin_reserved_cong:
  (!ce ty e s. ci_mono s (SND (f ce ty e s))) /\
  (!ty e s. local_ptrs_reserved ce s ==> f ce ty e s = g ce ty e s) /\
  local_ptrs_reserved ce sa ==>
  compile_type_builtin_dispatch_body f ce vt ty tb rt args sa =
  compile_type_builtin_dispatch_body g ce vt ty tb rt args sa
Proof
  strip_tac >>
  `!ty e. lower_value f ce ty e sa = lower_value g ce ty e sa` by
    (rpt gen_tac >> irule compiler_lower_value_reserved_cong >> simp[]) >>
  Cases_on `tb` >>
  simp[compile_type_builtin_dispatch_body_def, LET_THM]
  >- (Cases_on `lower_value g ce (expr_type (HD args)) (HD args) sa` >>
      simp[] >> rename1 `lower_value g ce _ _ sa = (v,sb)` >>
      `local_ptrs_reserved ce sb` by
        (irule compiler_ci_mono_reserved >> qexists `sa` >>
         metis_tac[ci_mono_lower_value_cfn, pairTheory.SND]) >>
      AP_TERM_TAC >> irule compiler_lower_value_reserved_cong >> simp[]) >>
  simp[]
QED

(* Advance one explicit callback let, transporting reservation from its
   newly introduced computation equation. *)
val compiler_reserved_pair_tac =
  pairarg_tac >>
  FIRST [qpat_assum `!ty e s v sb. _ /\ lower_value _ _ _ _ _ = _ ==> _`
           (fn rule => pop_assum (fn eq => assume_tac eq >>
             mp_then Any mp_tac rule eq)),
         qpat_assum `!ty e s v sb. _ /\ g _ _ _ _ = _ ==> _`
           (fn rule => pop_assum (fn eq => assume_tac eq >>
             mp_then Any mp_tac rule eq)),
         qpat_assum `!s v op sb. _ /\ unwrap_value _ _ _ = _ ==> _`
           (fn rule => pop_assum (fn eq => assume_tac eq >>
             mp_then Any mp_tac rule eq))] >>
  (impl_tac >- simp[]) >> strip_tac >> gvs[];

Theorem compiler_builtin_reserved_cong:
  (!ce ty e s. ci_mono s (SND (f ce ty e s))) /\
  (!ty e s. local_ptrs_reserved ce s ==> f ce ty e s = g ce ty e s) /\
  local_ptrs_reserved ce sa ==>
  compile_builtin_dispatch_body f ce rt ty bi args sa =
  compile_builtin_dispatch_body g ce rt ty bi args sa
Proof
  strip_tac >>
  `!ty e s. local_ptrs_reserved ce s ==>
     lower_value f ce ty e s = lower_value g ce ty e s` by
    (rpt strip_tac >> irule compiler_lower_value_reserved_cong >> simp[]) >>
  `!ty e s v sb. local_ptrs_reserved ce s /\
     lower_value g ce ty e s = (v,sb) ==> local_ptrs_reserved ce sb` by
    (rpt strip_tac >> irule compiler_ci_mono_reserved >> qexists `s` >>
     metis_tac[ci_mono_lower_value_cfn, pairTheory.SND]) >>
  `!ty e s v sb. local_ptrs_reserved ce s /\
     g ce ty e s = (v,sb) ==> local_ptrs_reserved ce sb` by
    (rpt strip_tac >> irule compiler_ci_mono_reserved >> qexists `s` >>
     metis_tac[pairTheory.SND]) >>
  `!s v op sb. local_ptrs_reserved ce s /\
     unwrap_value ce v s = (op,sb) ==> local_ptrs_reserved ce sb` by
    (rpt strip_tac >> irule compiler_ci_mono_reserved >> qexists `s` >>
     metis_tac[ci_mono_unwrap_value, pairTheory.SND]) >>
  Cases_on `bi`
  >~ [`Bop _`] >- suspend "bop"
  >~ [`Slice _`] >- suspend "slice"
  >~ [`MakeArray _ _`] >- suspend "array"
  >~ [`Concat _`] >- suspend "concat" >>
  simp[compile_builtin_dispatch_body_def, LET_THM]
  >~ [`compile_acc _ _ _ _ _`] >-
    (AP_TERM_TAC >> irule compiler_acc_reserved_cong >> simp[]) >>
  rpt compiler_reserved_pair_tac
QED

Resume compiler_builtin_reserved_cong[bop]:
  simp[compile_builtin_dispatch_body_def, LET_THM] >>
  IF_CASES_TAC >> simp[]
  >- (compiler_reserved_pair_tac >>
      Cases_on `HD (TL args)` >> simp[] >>
      rename1 `Builtin _ b _` >> Cases_on `b` >> simp[] >>
      AP_TERM_TAC >> irule compiler_multi_exprs_reserved_cong >> simp[]) >>
  IF_CASES_TAC >> simp[] >> rpt compiler_reserved_pair_tac
QED

Resume compiler_builtin_reserved_cong[concat]:
  rename1 `Concat maxlen` >>
  simp[compile_builtin_dispatch_body_def, LET_THM] >>
  Cases_on `compile_alloc_buffer (32 * ((maxlen + 31) DIV 32) + 32) sa` >>
  simp[] >> rename1 `compile_alloc_buffer _ sa = (alloc,sb)` >>
  `local_ptrs_reserved ce sb` by
    (irule compiler_ci_mono_reserved >> qexists `sa` >>
     metis_tac[ci_mono_compile_alloc_buffer, pairTheory.SND]) >>
  Cases_on `emit_op ADD [alloc.buf_operand; Lit 32w] sb` >> simp[] >>
  rename1 `emit_op ADD _ sb = (dp,sc)` >>
  `local_ptrs_reserved ce sc` by
    (irule compiler_ci_mono_reserved >> qexists `sb` >>
     metis_tac[ci_mono_emit_op, pairTheory.SND]) >>
  `!infos off. compile_concat f ce args dp infos off sc =
              compile_concat g ce args dp infos off sc` by
    (rpt gen_tac >> irule compiler_concat_reserved_cong >> simp[]) >>
  simp[]
QED

Resume compiler_builtin_reserved_cong[array]:
  rename1 `MakeArray opt bnd` >> Cases_on `opt` >>
  simp[compile_builtin_dispatch_body_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  rename1 `compile_alloc_buffer _ sa = (alloc,sb)` >>
  `local_ptrs_reserved ce sb` by
    (irule compiler_ci_mono_reserved >> qexists `sa` >>
     metis_tac[ci_mono_compile_alloc_buffer, pairTheory.SND]) >>
  AP_TERM_TAC >>
  FIRST [irule compiler_make_tuple_reserved_cong >> simp[],
         irule compiler_make_array_reserved_cong >> simp[]]
QED

Resume compiler_builtin_reserved_cong[slice]:
  simp[compile_builtin_dispatch_body_def, LET_THM] >>
  IF_CASES_TAC >> simp[]
  >- rpt compiler_reserved_pair_tac >>
  IF_CASES_TAC >> simp[]
  >- rpt compiler_reserved_pair_tac >>
  IF_CASES_TAC >> simp[]
  >- rpt compiler_reserved_pair_tac >>
  compiler_reserved_pair_tac >> IF_CASES_TAC >> simp[]
  >- (pairarg_tac >> gvs[] >>
      rename1 `compile_bytestring_src _ st1 = (_,st2)` >>
      `local_ptrs_reserved ce st2` by
        (irule compiler_ci_mono_reserved >> qexists `st1` >>
         metis_tac[ci_mono_compile_bytestring_src, pairTheory.SND]) >>
      simp[] >> rpt compiler_reserved_pair_tac) >>
  rpt compiler_reserved_pair_tac
QED

Finalise compiler_builtin_reserved_cong

(* Paired-let syntax boundary for the existing monadic congruence rule. *)
Theorem compiler_reserved_pair_cong:
  (!s. local_ptrs_reserved ce s ==> a s = b s) /\
  (!s. ci_mono s (SND (a s))) /\
  (!v s. local_ptrs_reserved ce s ==> k v s = l v s) /\
  local_ptrs_reserved ce sa ==>
  (UNCURRY k (a sa) : 'b # compile_state) = UNCURRY l (b sa)
Proof
  strip_tac >>
  `comp_bind a k sa = comp_bind b l sa` by
    (irule compiler_reserved_bind_cong >> metis_tac[]) >>
  Cases_on `a sa` >> Cases_on `b sa` >>
  gvs[comp_bind_def, LET_THM, pairTheory.UNCURRY_DEF]
QED

Theorem compiler_expr_body_reserved_cong:
  (!ce ty e s. ci_mono s (SND (f ce ty e s))) /\
  (!ty e s. local_ptrs_reserved ce s ==> f ce ty e s = g ce ty e s) /\
  (!rt ty bi args s. local_ptrs_reserved ce s ==>
     bf ce rt ty bi args s = bg ce rt ty bi args s) /\
  (!vt ty tb rt args s. local_ptrs_reserved ce s ==>
     tf ce vt ty tb rt args s = tg ce vt ty tb rt args s) /\
  local_ptrs_reserved ce sa ==>
  compile_expr_body f bf tf ce ty e sa = compile_expr_body g bg tg ce ty e sa
Proof
  strip_tac >> Cases_on `e`
  >~ [`IfExp _ _ _ _`] >- suspend "ifexp"
  >~ [`Builtin _ _ _`] >- suspend "builtin"
  >~ [`StructLit _ _ _`] >- suspend "struct" >>
  simp[compile_expr_body_def, LET_THM]
  >~ [`compile_subscript _ _ _ _ _ _ _`] >-
    (irule compiler_subscript_reserved_cong >> simp[])
  >~ [`compile_attribute _ _ _ _ _ _ _`] >-
    (irule compiler_attribute_reserved_cong >> simp[]) >>
  irule compiler_call_reserved_cong >> simp[]
QED

Resume compiler_expr_body_reserved_cong[builtin]:
  rename1 `Builtin ann bi args` >>
  `!rt ty. bf ce rt ty bi args sa = bg ce rt ty bi args sa` by simp[] >>
  Cases_on `bi` >> simp[compile_expr_body_def, LET_THM]
QED

Resume compiler_expr_body_reserved_cong[struct]:
  simp[compile_expr_body_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  rename1 `compile_alloc_buffer _ sa = (alloc,sb)` >>
  `local_ptrs_reserved ce sb` by
    (irule compiler_ci_mono_reserved >> qexists `sa` >>
     metis_tac[ci_mono_compile_alloc_buffer, pairTheory.SND]) >>
  `!ty fields off. compile_struct_lit f ce ty fields alloc.buf_operand off sb =
                   compile_struct_lit g ce ty fields alloc.buf_operand off sb` by
    (rpt gen_tac >> irule compiler_struct_lit_reserved_cong >> simp[]) >>
  simp[]
QED

Resume compiler_expr_body_reserved_cong[ifexp]:
  rename1 `IfExp ann cond te ee` >>
  `!ty e s. local_ptrs_reserved ce s ==>
     lower_value f ce ty e s = lower_value g ce ty e s` by
    (rpt strip_tac >> irule compiler_lower_value_reserved_cong >> simp[]) >>
  `!ty e s. local_ptrs_reserved ce s ==>
     ci_mono s (SND (lower_value g ce ty e s))` by
    (rpt strip_tac >> metis_tac[ci_mono_lower_value_cfn]) >>
  qpat_x_assum `!rt ty bi args s. _ ==> bf _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `!vt ty tb rt args s. _ ==> tf _ _ _ _ _ _ _ = _` kall_tac >>
  simp[NoAsms, compile_expr_body_def, LET_THM] >>
  rpt (ho_match_mp_tac compiler_reserved_pair_cong >>
       (conj_tac >- simp[]) >>
       (conj_tac >- simp[ci_mono_lower_value_cfn, ci_mono_fresh_var,
                         ci_mono_fresh_label, ci_mono_new_block, ci_mono_emit_inst]) >>
       (reverse conj_tac >- simp[]) >>
       rpt gen_tac >> disch_tac) >>
  simp[]
QED

Finalise compiler_expr_body_reserved_cong

(* Guard erasure is an interface consequence, not a second body induction. *)
Theorem compiler_guarded_builtin_body:
  (!ce ty e s. ci_mono s (SND (f ce ty e s))) /\
  local_ptrs_reserved ce sa ==>
  compile_builtin_dispatch_body
    (\ce ty e s. if local_ptrs_reserved ce s then f ce ty e s
      else (StackValue ty (Lit 0w),s)) ce rt ty bi args sa =
  compile_builtin_dispatch_body f ce rt ty bi args sa
Proof
  strip_tac >> sym_tac >> irule compiler_builtin_reserved_cong >> simp[]
QED

Theorem compiler_guarded_type_builtin_body:
  (!ce ty e s. ci_mono s (SND (f ce ty e s))) /\
  local_ptrs_reserved ce sa ==>
  compile_type_builtin_dispatch_body
    (\ce ty e s. if local_ptrs_reserved ce s then f ce ty e s
      else (StackValue ty (Lit 0w),s)) ce vt ty tb rt args sa =
  compile_type_builtin_dispatch_body f ce vt ty tb rt args sa
Proof
  strip_tac >> sym_tac >> irule compiler_type_builtin_reserved_cong >> simp[]
QED

Theorem compiler_guarded_expr_body:
  (!ce ty e s. ci_mono s (SND (f ce ty e s))) /\
  local_ptrs_reserved ce sa ==>
  compile_expr_body
    (\ce ty e s. if local_ptrs_reserved ce s then f ce ty e s
      else (StackValue ty (Lit 0w),s)) bf tf ce ty e sa =
  compile_expr_body f bf tf ce ty e sa
Proof
  strip_tac >> sym_tac >> irule compiler_expr_body_reserved_cong >> simp[]
QED

val hash_case_lift_thms =
  let val tys = [``:'a list``, ``:expr``]
      fun constant ty = Prim_rec.prove_case_const_thm
        {case_def = TypeBase.case_def_of ty,
         nchotomy = TypeBase.nchotomy_of ty}
  in map TypeBase.case_rand_of tys @ map constant tys end;

Theorem compiler_pair_var:
  (!vv sb. r = (vv,sb) ==>
    !x. vv_operand vv = Var x ==> not_fresh_at sb x) <=>
  (!x. vv_operand (FST r) = Var x ==> not_fresh_at (SND r) x)
Proof
  Cases_on `r` >> simp[]
QED

Theorem compiler_expr_builtin_pred:
  !P. (!rt ty es. P (bf ce rt ty bi es sa)) /\
  (!rt aty a bty b mty m. P (compile_addmod_names ce rt aty a bty b mty m sa)) /\
  (!rt aty a bty b mty m. P (compile_mulmod_names ce rt aty a bty b mty m sa)) /\
  (!rt aty a bty b. P (compile_powmod256_names ce rt aty a bty b sa)) ==>
  P (compile_expr_body f bf tf ce ty (Builtin ann bi args) sa)
Proof
  gen_tac >> strip_tac >> Cases_on `bi` >>
  simp([compile_expr_body_def, LET_THM] @ hash_case_lift_thms)
QED

Theorem compiler_expr_builtin_var:
  (!rt ty es vv sb. bf ce rt ty bi es sa = (vv,sb) ==>
    !x. vv_operand vv = Var x ==> not_fresh_at sb x) ==>
  !vv sb. compile_expr_body f bf tf ce ty (Builtin ann bi args) sa = (vv,sb) ==>
    !x. vv_operand vv = Var x ==> not_fresh_at sb x
Proof
  simp[compiler_pair_var] >> strip_tac >>
  qspec_then `\r. !x. vv_operand (FST r) = Var x ==> not_fresh_at (SND r) x`
    mp_tac compiler_expr_builtin_pred >>
  simp[] >> impl_tac >-
    (rpt conj_tac >>
     rewrite_tac[GSYM compiler_pair_var] >>
     metis_tac[compiler_modular_names_var]) >> simp[]
QED

Theorem compiler_compile_var:
  (!ce ty e sa vv sb. compile_expr ce ty e sa = (vv,sb) /\
    local_ptrs_reserved ce sa ==>
    !x. vv_operand vv = Var x ==> not_fresh_at sb x) /\
  (!ce rt ty bi args sa vv sb.
    compile_builtin_dispatch ce rt ty bi args sa = (vv,sb) /\
    local_ptrs_reserved ce sa ==>
    !x. vv_operand vv = Var x ==> not_fresh_at sb x) /\
  (!ce vt ty tb rt args sa vv sb.
    compile_type_builtin_dispatch ce vt ty tb rt args sa = (vv,sb) /\
    local_ptrs_reserved ce sa ==>
    !x. vv_operand vv = Var x ==> not_fresh_at sb x)
Proof
  ho_match_mp_tac compile_expr_ind >> conj_tac
  >- suspend "expr" >> conj_tac
  >- suspend "builtin" >> suspend "type_builtin"
QED

Resume compiler_compile_var[builtin]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_builtin_dispatch _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_expr_raw_def] >>
  qmatch_goalsub_abbrev_tac `compile_builtin_dispatch_body f` >>
  `!ce ty e s. ci_mono s (SND (f ce ty e s))` by
    (simp[Abbr `f`, ci_mono_expr_child_callback, cj 1 compile_expr_ci_mono]) >>
  `!ce ty e s vv sb. local_ptrs_reserved ce s /\ f ce ty e s = (vv,sb) ==>
     !x. vv_operand vv = Var x ==> not_fresh_at sb x` by
    (simp[Abbr `f`, exprCallBoundsTheory.expr_child_callback_def] >>
     rpt gen_tac >> IF_CASES_TAC >- metis_tac[] >>
     simp[exprCallBoundsTheory.invalid_expr_call_def, LET_THM] >>
     pairarg_tac >> rpt strip_tac >> gvs[contextTheory.vv_operand_def]) >>
  qabbrev_tac `cb_result = compile_builtin_dispatch_body f ce rt ty bi args sa` >>
  qabbrev_tac `gf = \ce ty e s. if local_ptrs_reserved ce s then f ce ty e s
    else (StackValue ty (Lit 0w),s)` >>
  `!ce ty e s. ci_mono s (SND (gf ce ty e s))` by
    (simp[Abbr `gf`] >> metis_tac[compiler_guarded_callback_ci_mono]) >>
  `!ce ty e s vv sb. gf ce ty e s = (vv,sb) ==>
     !x. vv_operand vv = Var x ==> not_fresh_at sb x` by
    (drule compiler_guarded_callback_var >> simp[Abbr `gf`] >> metis_tac[]) >>
  `cb_result = compile_builtin_dispatch_body gf ce rt ty bi args sa` by
    (simp[Abbr `cb_result`, Abbr `gf`] >> sym_tac >>
     irule compiler_guarded_builtin_body >> simp[]) >>
  simp[] >> strip_tac >>
  qpat_x_assum `compile_builtin_dispatch_body gf _ _ _ _ _ _ = _`
    (mp_then Any mp_tac compiler_builtin_var) >> simp[] >> metis_tac[]
QED

Resume compiler_compile_var[type_builtin]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_type_builtin_dispatch _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_expr_raw_def] >>
  qmatch_goalsub_abbrev_tac `compile_type_builtin_dispatch_body f` >>
  `!ce ty e s. ci_mono s (SND (f ce ty e s))` by
    (simp[Abbr `f`, ci_mono_expr_child_callback, cj 1 compile_expr_ci_mono]) >>
  `!ce ty e s vv sb. local_ptrs_reserved ce s /\ f ce ty e s = (vv,sb) ==>
     !x. vv_operand vv = Var x ==> not_fresh_at sb x` by
    (simp[Abbr `f`, exprCallBoundsTheory.expr_child_callback_def] >>
     rpt gen_tac >> IF_CASES_TAC >- metis_tac[] >>
     simp[exprCallBoundsTheory.invalid_expr_call_def, LET_THM] >>
     pairarg_tac >> rpt strip_tac >> gvs[contextTheory.vv_operand_def]) >>
  qabbrev_tac `cb_result = compile_type_builtin_dispatch_body f ce vt ty tb rt args sa` >>
  qabbrev_tac `gf = \ce ty e s. if local_ptrs_reserved ce s then f ce ty e s
    else (StackValue ty (Lit 0w),s)` >>
  `!ce ty e s. ci_mono s (SND (gf ce ty e s))` by
    (simp[Abbr `gf`] >> metis_tac[compiler_guarded_callback_ci_mono]) >>
  `!ce ty e s vv sb. gf ce ty e s = (vv,sb) ==>
     !x. vv_operand vv = Var x ==> not_fresh_at sb x` by
    (drule compiler_guarded_callback_var >> simp[Abbr `gf`] >> metis_tac[]) >>
  `cb_result = compile_type_builtin_dispatch_body gf ce vt ty tb rt args sa` by
    (simp[Abbr `cb_result`, Abbr `gf`] >> sym_tac >>
     irule compiler_guarded_type_builtin_body >> simp[]) >>
  simp[] >> strip_tac >>
  qpat_x_assum `compile_type_builtin_dispatch_body gf _ _ _ _ _ _ _ = _`
    (mp_then Any mp_tac compiler_type_builtin_var) >> simp[] >> metis_tac[]
QED

Resume compiler_compile_var[expr]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[Once compile_expr_raw_def] >>
  qmatch_goalsub_abbrev_tac `compile_expr_body f bf tf` >>
  `!ce ty e s. ci_mono s (SND (f ce ty e s))` by
    (simp[Abbr `f`, ci_mono_expr_child_callback, cj 1 compile_expr_ci_mono]) >>
  `!ce ty e s vv sb. local_ptrs_reserved ce s /\ f ce ty e s = (vv,sb) ==>
     !x. vv_operand vv = Var x ==> not_fresh_at sb x` by
    (simp[Abbr `f`, exprCallBoundsTheory.expr_child_callback_def] >>
     rpt gen_tac >> IF_CASES_TAC >- metis_tac[] >>
     simp[exprCallBoundsTheory.invalid_expr_call_def, LET_THM] >>
     pairarg_tac >> rpt strip_tac >> gvs[contextTheory.vv_operand_def]) >>
  `!ce rt ty bi args s vv sb. local_ptrs_reserved ce s /\
     bf ce rt ty bi args s = (vv,sb) ==>
     !x. vv_operand vv = Var x ==> not_fresh_at sb x` by
    (simp[Abbr `bf`, exprCallBoundsTheory.builtin_child_callback_def] >>
     rpt gen_tac >> IF_CASES_TAC >- metis_tac[] >>
     simp[exprCallBoundsTheory.invalid_expr_call_def, LET_THM] >>
     pairarg_tac >> rpt strip_tac >> gvs[contextTheory.vv_operand_def]) >>
  `!ce vt ty tb rt args s vv sb. local_ptrs_reserved ce s /\
     tf ce vt ty tb rt args s = (vv,sb) ==>
     !x. vv_operand vv = Var x ==> not_fresh_at sb x` by
    (simp[Abbr `tf`, exprCallBoundsTheory.type_child_callback_def] >>
     rpt gen_tac >> IF_CASES_TAC >- metis_tac[] >>
     simp[exprCallBoundsTheory.invalid_expr_call_def, LET_THM] >>
     pairarg_tac >> rpt strip_tac >> gvs[contextTheory.vv_operand_def]) >>
  qabbrev_tac `gf = \ce ty e s. if local_ptrs_reserved ce s then f ce ty e s
    else (StackValue ty (Lit 0w),s)` >>
  `!ce ty e s. ci_mono s (SND (gf ce ty e s))` by
    (simp[Abbr `gf`] >> metis_tac[compiler_guarded_callback_ci_mono]) >>
  `!ce ty e s vv sb. gf ce ty e s = (vv,sb) ==>
     !x. vv_operand vv = Var x ==> not_fresh_at sb x` by
    (drule compiler_guarded_callback_var >> simp[Abbr `gf`] >> metis_tac[]) >>
  `compile_expr_body f bf tf ce ty e sa = compile_expr_body gf bf tf ce ty e sa` by
    (simp[Abbr `gf`] >> sym_tac >> irule compiler_guarded_expr_body >> simp[]) >>
  simp[] >>
  qpat_x_assum `!e' ce ty sa. _ ==> _` kall_tac >>
  qpat_x_assum `!args ce rt ty bi sa. _ ==> _` kall_tac >>
  qpat_x_assum `!args ce vt ty tb rt sa. _ ==> _` kall_tac >>
  rpt (qpat_x_assum `Abbrev _` kall_tac) >>
  qpat_x_assum `compile_expr_body f _ _ _ _ _ _ = _` kall_tac >>
  Cases_on `e`
  >~ [`IfExp _ _ _ _`] >-
    (strip_tac >> qpat_x_assum `compile_expr_body _ _ _ _ _ _ _ = _`
       (mp_then Any mp_tac compiler_ifexp_var) >> simp[]) 
  >~ [`Builtin _ _ _`] >- suspend "expr_builtin"
  >~ [`TypeBuiltin _ _ _ _`] >-
    (simp[compile_expr_body_def, LET_THM] >> metis_tac[])
  >~ [`StructLit _ _ _`] >- suspend "expr_struct"
  >~ [`TopLevelName _ _`] >- suspend "expr_toplevel"
  >~ [`Pop _ _`] >- suspend "expr_pop" >>
  simp[compile_expr_body_def, LET_THM]
  >~ [`compile_name_vv _ _ _ _ = _`] >- metis_tac[compiler_name_var]
  >~ [`compile_literal_vv _ _ _ = _`] >- metis_tac[compiler_literal_var]
  >~ [`compile_subscript _ _ _ _ _ _ _ = _`] >- metis_tac[compiler_subscript_var]
  >~ [`compile_attribute _ _ _ _ _ _ _ = _`] >- metis_tac[compiler_attribute_var]
  >~ [`compile_call _ _ _ _ _ _ _ _ = _`] >- metis_tac[compiler_call_var] >>
  rpt strip_tac >> gvs[contextTheory.vv_operand_def]
QED

Resume compiler_compile_var[expr_builtin]:
  match_mp_tac compiler_expr_builtin_var >> metis_tac[]
QED

Resume compiler_compile_var[expr_toplevel]:
  rename1 `TopLevelName ann name` >>
  simp[compile_expr_body_def, LET_THM] >>
  Cases_on `FLOOKUP ce.ce_vars (module_var_key name)` >>
  simp[LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  rpt strip_tac >> gvs[contextTheory.vv_operand_def, contextTheory.mk_ptr_def] >>
  rename1 `FLOOKUP ce.ce_vars (module_var_key name) = SOME loc` >>
  Cases_on `loc` >> gvs[contextTheory.vv_operand_def]
QED

Resume compiler_compile_var[expr_struct]:
  simp[compile_expr_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  rpt strip_tac >> gvs[contextTheory.vv_operand_def] >>
  gvs[contextTheory.base_ptr_def] >>
  drule compiler_alloc_buffer_var >> strip_tac >>
  drule ci_mono_compile_struct_lit_cfn >> strip_tac >>
  metis_tac[compiler_ci_mono_not_fresh, pairTheory.SND]
QED

Resume compiler_compile_var[expr_pop]:
  simp[compile_expr_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  rpt strip_tac >> gvs[contextTheory.vv_operand_def, contextTheory.mk_ptr_def] >>
  metis_tac[compiler_dynarray_pop_var]
QED

Finalise compiler_compile_var

Theorem compile_lower_value_var:
  lower_value compile_expr ce ty e sa = (op,sb) /\
  local_ptrs_reserved ce sa ==>
  !x. op = Var x ==> not_fresh_at sb x
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule_at (Pos hd) compiler_lower_value_var >>
  metis_tac[compiler_compile_var]
QED

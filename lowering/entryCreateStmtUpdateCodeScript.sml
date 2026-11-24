(* Static branch confinement for statement writes, including nested copies. *)
Theory entryCreateStmtUpdateCode
Ancestors
  stmtLowering exprLowering context builtinMath builtinSimple exprBopLowering
  createSizeOperandCode createSizeConcreteSnapshots createSizeTypedCopyCode
  createSizeCutCode createSizeCutOpens createSizeLocationCode
  compileEnv emitHelper venomInst vyperAST finite_map arithmetic list pair pred_set

val emit_cuts = [create_cut_code_emit_inst, create_cut_code_emit_op,
  create_cut_code_emit_void, create_cut_targets_def];

fun cut_updates extra =
  let val clean = simp (extra @ emit_cuts @ [LET_THM,comp_ignore_bind_def])
  in clean >> rpt (FIRST [match_mp_tac create_cut_code_bind_uniform >>
      conj_tac >> rpt gen_tac >> BETA_TAC,
      conj_tac, IF_CASES_TAC, BasicProvers.TOP_CASE_TAC] >> clean)
  end;

Theorem update_ptr_word_cut[simp]:
  create_cut_code E a (SND (compile_ptr_load ctor imm loc p a)) /\
  create_cut_code E a (SND (compile_ptr_store ctor imm loc p v a))
Proof
  Cases_on `loc` >>
  cut_updates [compile_ptr_load_def, compile_ptr_store_def,
               compile_imm_load_word_def, compile_imm_store_word_def]
QED

Theorem update_array_subscript_cut:
  (!p a. create_cut_code {} a (SND (load p a))) ==>
  !a. create_cut_code {} a
      (SND (compile_array_subscript p i dyn cnt ws sz signed load a))
Proof
  strip_tac >> gen_tac >> cut_updates [compile_array_subscript_def]
QED

Theorem update_target_ptr_cut[simp]:
  !tgt ce a. create_cut_code {} a (SND (compile_get_target_ptr compile_expr ce tgt a))
Proof
  gen_tac >> measureInduct_on `base_assignment_target_size tgt` >>
  Cases_on `tgt` >> rpt gen_tac >> simp_tac std_ss [Once compile_get_target_ptr_def] >>
  cut_updates [GSYM AND_IMP_INTRO, update_array_subscript_cut,
    compile_tuple_subscript_def, compile_mapping_subscript_def,
    compile_keccak256_key_def, create_alloc_buffer_cut_code, create_operand_cut_code]
QED

Theorem update_imm_store_cut[local,simp]:
  create_cut_code E a (SND (compile_imm_store_word imm p v a))
Proof
  cut_updates [compile_imm_store_word_def]
QED

Theorem update_offset_cut[local,simp]:
  create_cut_code E a (SND (compile_lit_byte_offset p n a))
Proof
  Cases_on `p` >> cut_updates [compile_lit_byte_offset_def]
QED

Theorem update_imm_words_cut[local,simp]:
  !n off a. create_cut_code E a (SND (compile_imm_store_words imm src dst n off a))
Proof
  Induct >> rpt gen_tac >> cut_updates [compile_imm_store_words_def]
QED

val copy_cuts = [compile_bytestring_word_count_def, compile_word_copy_loop_def,
  compile_word_copy_loop_op_def, create_word_copy_cut_code];

Theorem update_imm_bytes_cut[local,simp]:
  create_cut_code {} a (SND (compile_store_immutable_bytestring imm src dst a))
Proof
  cut_updates (compile_store_immutable_bytestring_def :: copy_cuts)
QED

Theorem update_open_debt[local]:
  (!v s. create_cut_code E s (SND (k v s)) /\
    owed DELETE lbl SUBSET set (added_labels s (SND (k v s)))) ==>
  create_cut_code E a (SND (comp_bind (new_block lbl) k a)) /\
  owed SUBSET set (added_labels a (SND (comp_bind (new_block lbl) k a)))
Proof
  strip_tac >> Cases_on `new_block lbl a` >> simp[comp_bind_def] >>
  rename1 `new_block lbl a = (q,r)` >>
  `create_cut_code E a r /\ {lbl} SUBSET set (added_labels a r)` by
    metis_tac[create_cut_opens_new_block] >>
  `create_cut_code E a (SND (k q r)) /\
   ({lbl} UNION (owed DELETE lbl)) SUBSET set (added_labels a (SND (k q r)))` by
    (irule create_cut_opens_join >> qexists_tac `r` >> simp[]) >>
  fs[SUBSET_DEF] >> metis_tac[]
QED

Theorem update_jnz_cut[local,simp]:
  l IN E /\ r IN E ==>
  create_cut_code E a (SND (emit_inst JNZ [c;Label l;Label r] [] a))
Proof
  Cases_on `c` >> simp[create_cut_code_emit_inst,create_cut_targets_def, DISJ_IMP_THM]
QED

Theorem update_sloop_cut[local]:
  (!src dst a. create_cut_code {} a (SND (store src dst a))) ==>
  create_cut_code {} a
    (SND ((do h <- fresh_label "dyn_cond";
              b <- fresh_label "dyn_body";
              x <- fresh_label "dyn_exit";
              ctr <- fresh_var;
              emit_inst ASSIGN [Lit 0w] [ctr];
              emit_inst JMP [Label h] [];
              new_block h;
              lt <- emit_op LT [Var ctr; count_op];
              done <- emit_op ISZERO [lt];
              emit_inst JNZ [done; Label x; Label b] [];
              new_block b;
              soff <- emit_op MUL [Var ctr; Lit (n2w msz)];
              sp <- emit_op ADD [src; soff];
              doff <- emit_op MUL [Var ctr; Lit (n2w wsz)];
              dp <- emit_op ADD [dst; doff];
              store sp dp;
              next <- emit_op ADD [Var ctr; Lit 1w];
              emit_inst ASSIGN [next] [ctr];
              emit_inst JMP [Label h] [];
              new_block x;
              return () od) a))
Proof
  strip_tac >> simp[comp_ignore_bind_def] >>
  map_every (fn l => match_mp_tac create_cut_code_bind_all >>
    (conj_tac >- simp[]) >> qx_gen_tac l >> gen_tac >> BETA_TAC) [`h`,`b`,`x`,`ctr`] >>
  match_mp_tac create_cut_code_bind_all >> (conj_tac >- simp[create_cut_code_emit_inst,create_cut_targets_def]) >>
  rpt gen_tac >> BETA_TAC >>
  `!h b x a z. create_cut_code {h;b;x} a z /\
    {h;b;x} SUBSET set (added_labels a z) ==> create_cut_code {} a z` by
    metis_tac[create_cut_code_close, UNION_EMPTY] >>
  first_x_assum (qspecl_then [`h`,`b`,`x`] match_mp_tac) >>
  suspend "loop"
QED

Resume update_sloop_cut[loop]:
  rpt (FIRST
    [match_mp_tac update_open_debt >> rpt gen_tac >> BETA_TAC,
     match_mp_tac create_cut_opens_bind_keep >>
      (conj_tac >- (rpt gen_tac >> cut_updates [create_cut_code_widen_empty])) >>
      rpt gen_tac >> BETA_TAC]) >>
  simp[SUBSET_DEF, comp_return_def] >> metis_tac[]
QED
Finalise update_sloop_cut[local]

Theorem update_slot_cuts[local]:
  (!ce src dst ty tr a. create_cut_code {} a (SND (compile_store_slots ce src dst ty tr a))) /\
  (!ce src dst rows so doff tr a. create_cut_code {} a
      (SND (compile_store_slots_members ce src dst rows so doff tr a))) /\
  (!ce src dst ty n tr a. create_cut_code {} a
      (SND (compile_copy_elements_to_slots ce src dst ty n tr a)))
Proof
  ho_match_mp_tac compile_store_slots_ind >> reverse (rpt conj_tac) >>
  rpt strip_tac >> simp_tac std_ss [Once compile_store_slots_def, LET_THM]
  >- (simp_tac std_ss [comp_ignore_bind_def] >>
      ho_match_mp_tac (SIMP_RULE std_ss [comp_ignore_bind_def] update_sloop_cut) >>
      rpt gen_tac >> simp[]) >>
  cut_updates (copy_cuts @ [compile_memory_to_storage_def, compile_memory_to_transient_def]) >>
  gvs[] >> metis_tac[]
QED

Theorem update_assign_value_cut[local,simp]:
  create_cut_code {} a
    (SND (compile_assign_value ce dst loc v prim sloc dt st n a))
Proof
  Cases_on `loc` >>
  cut_updates [compile_assign_value_def, create_alloc_buffer_cut_code,
    create_cut_copy_memory, create_store_memory_cut_code,
    create_store_memory_typed_cut_code, update_slot_cuts]
QED

Theorem update_dynarray_append_cut[local,simp]:
  create_cut_code {} a (SND (compile_dynarray_append ce dst v ws n dt st cap prim loc a))
Proof
  cut_updates [compile_dynarray_append_def, create_store_memory_cut_code, update_slot_cuts]
QED

Theorem update_store_at_loc_cut[local,simp]:
  create_cut_code E a (SND (compile_store_at_loc imm dst v loc a))
Proof
  Cases_on `loc` >- cut_updates [compile_store_at_loc_def] >>
  rename1 `compile_store_at_loc imm dst v (SOME l)` >>
  Cases_on `l` >> cut_updates [compile_store_at_loc_def]
QED

Theorem update_tuple_load_cut[local,simp]:
  !tys off a. create_cut_code E a (SND (compile_tuple_load_all ce p tys off a))
Proof
  Induct >> rpt gen_tac >> cut_updates [compile_tuple_load_all_def, compile_load_memory_def]
QED

Theorem update_tuple_store_cut[local,simp]:
  !tys tgts vals a. create_cut_code {}
    a (SND (compile_tuple_store_all ce tys tgts vals a))
Proof
  Induct >> Cases_on `tgts` >> Cases_on `vals` >> rpt gen_tac >>
  simp[compile_tuple_store_all_def] >>
  rename1 `compile_tuple_store_all _ (_::_) (tgt_head::_) (_::_) _` >>
  Cases_on `tgt_head` >> cut_updates [compile_tuple_store_all_def]
QED

Theorem update_tuple_unpack_cut[local,simp]:
  create_cut_code {} a (SND (compile_tuple_unpack ce ty stage tgts src a))
Proof
  cut_updates [compile_tuple_unpack_def, create_alloc_buffer_cut_code]
QED

Theorem update_local_alloca_cut[local,simp]:
  create_cut_code E a (SND (emit_local_alloca ce id a))
Proof
  cut_updates [emit_local_alloca_def]
QED

Theorem update_binop_cut[local,simp]:
  create_cut_code E a (SND (compile_binop bop x y ty bl el a))
Proof
  Cases_on `bop` >>
  cut_updates [compile_binop_def, compile_safe_add_def, compile_safe_sub_def,
    compile_safe_mul_def, compile_safe_div_def, compile_safe_decimal_div_def,
    compile_safe_mod_def, compile_safe_pow_def, compile_mul_overflow_check_def,
    compile_compare_def, wrap_truncate_def, compile_select_def,
    clamp_and_return_def, compile_clamp_def, UNCURRY_VAR]
QED

Theorem stmt_update_cut_code_cases:
  (!ce lc ty id vtyp e a.
    create_cut_code {} a (SND (compile_stmt ce lc ty (AnnAssign id vtyp e) a))) /\
  (!ce lc ty bt e a.
    create_cut_code {} a (SND (compile_stmt ce lc ty (Assign (BaseTarget bt) e) a))) /\
  (!ce lc ty tgts e a.
    create_cut_code {} a (SND (compile_stmt ce lc ty (Assign (TupleTarget tgts) e) a))) /\
  (!ce lc ty vtyp bt bop e a.
    create_cut_code {} a (SND (compile_stmt ce lc ty (AugAssign vtyp bt bop e) a))) /\
  (!ce lc ty bt e a.
    create_cut_code {} a (SND (compile_stmt ce lc ty (Append bt e) a)))
Proof
  rpt conj_tac >> rpt gen_tac >> simp_tac std_ss [Once compile_stmt_def] >>
  cut_updates [create_operand_cut_code, create_unwrap_cut_code,
    create_vv_snapshot_cut_code, create_alloc_buffer_cut_code, create_store_memory_cut_code,
    fragFuelTheory.comp_bind_return]
QED

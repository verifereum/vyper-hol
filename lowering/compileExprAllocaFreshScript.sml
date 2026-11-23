(* Generated instruction IDs and allocation outputs for expression lowering.
   The variable-counter lower bound stays fixed across a composition. *)
Theory compileExprAllocaFresh
Ancestors
  compilerInstructionSuffix abiEncoderProps loweringShapeDefs loweringStateRelDefs
  exprLoweringProps exprLowering exprOperandVar exprCallBounds
  compileEnv compilerFirstEmission emitHelper context venomInst
  builtinAbi builtinBytes builtinCreate builtinHashing builtinMath builtinMisc
  builtinSimple builtinStrings builtinSystem abiEncoder exprBopLowering
  fragExec list rich_list arithmetic
Libs
  BasicProvers monadsyntax

Definition alloca_suffix_def[local]:
  alloca_suffix floor a b <=>
    ci_mono a b /\
    (!id. id IN frag_ids a b ==> ?i. MEM i (added_insts a b) /\ i.inst_id = id) /\
    EVERY (\i. i.inst_opcode = ALLOCA ==>
      i.inst_id IN frag_ids a b /\
      !p. MEM p i.inst_outputs ==> ?n. floor <= n /\ p = STRING #"%" (toString n))
      (added_insts a b)
End

Theorem alloca_suffix_refl[local]:
  alloca_suffix floor a a
Proof
  simp[alloca_suffix_def, ci_mono_refl, frag_ids_def, added_insts_def]
QED

Theorem alloca_suffix_trans[local]:
  alloca_suffix floor a b /\ alloca_suffix floor b c ==> alloca_suffix floor a c
Proof
  simp_tac bool_ss [alloca_suffix_def] >> strip_tac >>
  `ci_mono a c` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
  `cs_extends a b /\ cs_extends b c` by fs[ci_mono_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (metis_tac[added_insts_coverage_append]) >>
  drule_all added_insts_append >> disch_then SUBST1_TAC >>
  fs[EVERY_APPEND, EVERY_MEM] >> rpt strip_tac >>
  fs[MEM_APPEND, frag_ids_def, ci_mono_def] >> metis_tac[LESS_EQ_TRANS, LESS_LESS_EQ_TRANS]
QED

Theorem alloca_suffix_bind[local]:
  (!a. alloca_suffix floor a (SND (m a))) /\
  (!v a. alloca_suffix floor a (SND (k v a))) ==>
  alloca_suffix floor s (SND (comp_bind m k s))
Proof
  strip_tac >> Cases_on `m s` >> rename1 `m s = (v,b)` >>
  `alloca_suffix floor s b` by metis_tac[pairTheory.SND] >>
  simp[comp_bind_def] >>
  irule alloca_suffix_trans >> qexists_tac `b` >> simp[]
QED

Theorem alloca_suffix_ignore_bind[local]:
  (!a. alloca_suffix floor a (SND (m a))) /\
  (!a. alloca_suffix floor a (SND (k a))) ==>
  alloca_suffix floor s (SND (comp_ignore_bind m k s))
Proof
  simp[comp_ignore_bind_def] >> strip_tac >>
  irule alloca_suffix_bind >> simp[]
QED

Theorem alloca_suffix_bind_floor[local]:
  (!a. floor <= a.cs_next_var ==> alloca_suffix floor a (SND (m a))) /\
  (!v a. floor <= a.cs_next_var ==> alloca_suffix floor a (SND (k v a))) /\
  floor <= s.cs_next_var ==>
  alloca_suffix floor s (SND (comp_bind m k s))
Proof
  strip_tac >> Cases_on `m s` >> rename1 `m s = (v,b)` >>
  `alloca_suffix floor s b` by metis_tac[pairTheory.SND] >>
  `floor <= b.cs_next_var` by
    (fs[alloca_suffix_def, ci_mono_def] >> decide_tac) >>
  simp[comp_bind_def] >>
  irule alloca_suffix_trans >> qexists_tac `b` >> simp[]
QED

Theorem alloca_suffix_ignore_floor[local]:
  (!a. floor <= a.cs_next_var ==> alloca_suffix floor a (SND (m a))) /\
  (!a. floor <= a.cs_next_var ==> alloca_suffix floor a (SND (k a))) /\
  floor <= s.cs_next_var ==>
  alloca_suffix floor s (SND (comp_ignore_bind m k s))
Proof
  simp[comp_ignore_bind_def] >> strip_tac >>
  irule alloca_suffix_bind_floor >> simp[]
QED

Theorem alloca_suffix_return[local,simp]:
  alloca_suffix floor a (SND (comp_return v a))
Proof
  simp[comp_return_def, alloca_suffix_refl]
QED

Theorem alloca_suffix_fresh_var[local,simp]:
  alloca_suffix floor a (SND (fresh_var a))
Proof
  `state_insts (SND (fresh_var a)) = state_insts a` by
    simp[fresh_var_def, state_insts_def, all_blocks_def] >>
  simp[alloca_suffix_def, ci_mono_fresh_var, added_insts_def] >>
  simp[fresh_var_def, frag_ids_def]
QED

Theorem alloca_suffix_fresh_label[local,simp]:
  alloca_suffix floor a (SND (fresh_label tag a))
Proof
  Cases_on `fresh_label tag a` >>
  drule added_insts_fresh_label >> simp[alloca_suffix_def, frag_ids_def]
QED

Theorem alloca_suffix_new_block[local,simp]:
  alloca_suffix floor a (SND (new_block lbl a))
Proof
  Cases_on `new_block lbl a` >>
  drule added_insts_new_block >> simp[alloca_suffix_def, frag_ids_def]
QED

Theorem alloca_suffix_emit_inst[local]:
  (opc = ALLOCA ==> !p. MEM p outs ==> ?n. floor <= n /\
    p = STRING #"%" (toString n)) ==>
  alloca_suffix floor a (SND (emit_inst opc ops outs a))
Proof
  strip_tac >> Cases_on `emit_inst opc ops outs a` >>
  drule added_insts_emit_inst >> simp[alloca_suffix_def, frag_ids_def, mk_inst_def]
QED

Theorem alloca_suffix_emit_void[local,simp]:
  alloca_suffix floor a (SND (emit_void opc ops a))
Proof
  Cases_on `emit_void opc ops a` >>
  drule added_insts_emit_void >> simp[alloca_suffix_def, frag_ids_def, mk_inst_def]
QED

Theorem alloca_suffix_emit_op[local]:
  floor <= a.cs_next_var ==> alloca_suffix floor a (SND (emit_op opc ops a))
Proof
  strip_tac >> Cases_on `emit_op opc ops a` >>
  drule added_insts_emit_op >> strip_tac >>
  simp[alloca_suffix_def, frag_ids_def, mk_inst_def] >>
  fs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]
QED

Theorem alloca_suffix_pair_bind_floor[local]:
  (!a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (mf a))) /\
  (!v a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (mg v a))) /\
  k <= a.cs_next_var ==>
  alloca_suffix k a
    (SND (UNCURRY mg (mf a)))
Proof
  strip_tac >>
  `UNCURRY mg (mf a) = comp_bind mf mg a` by
    simp[comp_bind_def, pairTheory.UNCURRY] >>
  simp[] >> irule alloca_suffix_bind_floor >> simp[]
QED

Theorem alloca_suffix_imm_load[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_imm_load_word ctor imm off a))
Proof
  strip_tac >> Cases_on `ctor` >> Cases_on `imm` >>
  simp[compile_imm_load_word_def, alloca_suffix_emit_op] >>
  irule alloca_suffix_bind_floor >> simp[alloca_suffix_emit_op]
QED

Theorem alloca_suffix_ptr_load[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_ptr_load ctor imm loc op a))
Proof
  Cases_on `loc` >>
  simp[compile_ptr_load_def, alloca_suffix_emit_op, alloca_suffix_imm_load]
QED

Theorem alloca_suffix_alloc_buffer[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_alloc_buffer sz a))
Proof
  strip_tac >> rewrite_tac[compile_alloc_buffer_def] >>
  irule alloca_suffix_bind_floor >>
  simp[alloca_suffix_emit_op, alloca_suffix_return]
QED

Theorem alloca_suffix_imm_store[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_imm_store_word imm off v a))
Proof
  strip_tac >> Cases_on `imm` >>
  simp[compile_imm_store_word_def, alloca_suffix_emit_void] >>
  irule alloca_suffix_bind_floor >>
  simp[alloca_suffix_emit_op, alloca_suffix_emit_void]
QED

Theorem alloca_suffix_ptr_store[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_ptr_store ctor imm loc dst v a))
Proof
  Cases_on `loc` >> Cases_on `ctor` >>
  simp[compile_ptr_store_def, alloca_suffix_emit_void, alloca_suffix_imm_store]
QED

Theorem alloca_suffix_word_copy_loop[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a
    (SND (compile_word_copy_loop src dst wc ll sl ctor a))
Proof
  strip_tac >> Cases_on `word_scale ll = 1` >>
  Cases_on `word_scale sl = 1` >>
  simp[compile_word_copy_loop_def, compile_word_copy_loop_op_def,
       compile_word_copy_loop_base_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_fresh_label, alloca_suffix_fresh_var,
            alloca_suffix_new_block, alloca_suffix_emit_inst,
            alloca_suffix_emit_op, alloca_suffix_ptr_load,
            alloca_suffix_ptr_store]) >>
  simp[alloca_suffix_new_block]
QED

Theorem alloca_suffix_storage_to_memory[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_storage_to_memory src dst wc a))
Proof
  simp[compile_storage_to_memory_def, alloca_suffix_word_copy_loop]
QED

Theorem alloca_suffix_transient_to_memory[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_transient_to_memory src dst wc a))
Proof
  simp[compile_transient_to_memory_def, alloca_suffix_word_copy_loop]
QED

Theorem alloca_suffix_lit_byte_offset[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_lit_byte_offset op off a))
Proof
  Cases_on `off = 0` >> Cases_on `op` >>
  simp[compile_lit_byte_offset_def, alloca_suffix_return, alloca_suffix_emit_op]
QED

Theorem alloca_suffix_imm_copy[local]:
  !n off a. k <= a.cs_next_var ==>
  alloca_suffix k a
    (SND (compile_imm_copy_to_memory ctor imm src dst n off a))
Proof
  Induct >> simp[compile_imm_copy_to_memory_def, alloca_suffix_return] >>
  rpt strip_tac >> rewrite_tac[comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_lit_byte_offset, alloca_suffix_imm_load,
            alloca_suffix_emit_void])
QED

Theorem alloca_suffix_ensure_in_memory[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a
    (SND (compile_ensure_in_memory op loc bytes wc ctor imm a))
Proof
  strip_tac >> Cases_on `loc` >> Cases_on `wc = 1` >>
  simp[compile_ensure_in_memory_def, comp_ignore_bind_def,
       alloca_suffix_return] >>
  rpt (rpt strip_tac >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_alloc_buffer, alloca_suffix_emit_op,
            alloca_suffix_emit_void, alloca_suffix_storage_to_memory,
            alloca_suffix_transient_to_memory, alloca_suffix_imm_copy,
            alloca_suffix_return])
QED

Theorem alloca_suffix_unwrap_value[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (unwrap_value cenv vv a))
Proof
  Cases_on `vv` >> simp[unwrap_value_def, alloca_suffix_return] >>
  rename1 `is_word_type ty` >> Cases_on `is_word_type ty`
  >- simp[alloca_suffix_ptr_load] >>
  Cases_on `p.ptr_location` >>
  simp[alloca_suffix_return, alloca_suffix_ensure_in_memory]
QED

Theorem alloca_suffix_lower_value[local]:
  (!a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (cfn cenv ty e a))) ==>
  !a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (lower_value cfn cenv ty e a))
Proof
  rpt strip_tac >> rewrite_tac[lower_value_def] >>
  irule alloca_suffix_bind_floor >> simp[alloca_suffix_unwrap_value]
QED

Theorem alloca_suffix_bytestring_len[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_bytestring_copy_len op a))
Proof
  strip_tac >> simp[compile_bytestring_copy_len_def] >>
  rpt (rpt strip_tac >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_op])
QED

Theorem alloca_suffix_store_bytestring[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_store_bytestring op dst a))
Proof
  strip_tac >> rewrite_tac[compile_store_bytestring_def] >>
  irule alloca_suffix_bind_floor >>
  simp[alloca_suffix_bytestring_len, alloca_suffix_emit_void]
QED

Theorem alloca_suffix_abi_bytes_clamp[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_abi_bytes_clamp op n a))
Proof
  strip_tac >> simp[compile_abi_bytes_clamp_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_op, alloca_suffix_emit_void])
QED

Theorem alloca_suffix_abi_int_clamp[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_abi_int_clamp op bits sg a))
Proof
  strip_tac >> Cases_on `sg` >> simp[compile_abi_int_clamp_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_op, alloca_suffix_emit_void])
QED

Theorem alloca_suffix_encode_static[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_abi_encode_static dst src a))
Proof
  strip_tac >> simp[compile_abi_encode_static_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_op, alloca_suffix_emit_void,
            alloca_suffix_return])
QED

Theorem alloca_suffix_encode_static_info[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_abi_encode_static_info dst src info a))
Proof
  strip_tac >> Cases_on `info` >>
  simp[compile_abi_encode_static_info_def, alloca_suffix_encode_static,
       alloca_suffix_return, comp_ignore_bind_def] >>
  irule alloca_suffix_bind_floor >>
  simp[alloca_suffix_emit_void, alloca_suffix_return]
QED

Theorem alloca_suffix_with_byte_offset[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_with_byte_offset op off a))
Proof
  Cases_on `off = 0` >>
  simp[compile_with_byte_offset_def, alloca_suffix_return, alloca_suffix_emit_op]
QED

Theorem alloca_suffix_copy_memory[local]:
  alloca_suffix k a (SND (compile_copy_memory dst src sz a))
Proof
  Cases_on `sz` >>
  simp[compile_copy_memory_def, alloca_suffix_return, alloca_suffix_emit_void]
QED

Theorem alloca_suffix_copy_memory_dynamic[local]:
  alloca_suffix k a (SND (compile_copy_memory_dynamic dst src len a))
Proof
  simp[compile_copy_memory_dynamic_def, alloca_suffix_emit_void]
QED

Theorem alloca_suffix_typed_memory_family[local]:
  (!cenv dst dst_ty src src_ty k a.
    k <= a.cs_next_var ==>
    alloca_suffix k a
      (SND (compile_store_memory_typed cenv dst dst_ty src src_ty a))) /\
  (!cenv dst src dst_tys src_tys dst_off src_off k a.
    k <= a.cs_next_var ==>
    alloca_suffix k a
      (SND (compile_typed_copy_fields cenv dst src dst_tys src_tys dst_off src_off a))) /\
  (!cenv dst dst_ty src src_ty count k a.
    k <= a.cs_next_var ==>
    alloca_suffix k a
      (SND (compile_copy_sarray_typed cenv dst dst_ty src src_ty count a))) /\
  (!cenv dst dst_ty cap src src_ty k a.
    k <= a.cs_next_var ==>
    alloca_suffix k a
      (SND (compile_copy_dynarray_typed cenv dst dst_ty cap src src_ty a))) /\
  (!cenv dst src dst_fields src_fields dst_off src_off k a.
    k <= a.cs_next_var ==>
    alloca_suffix k a
      (SND (compile_struct_typed_copy cenv dst src dst_fields src_fields dst_off src_off a)))
Proof
  ho_match_mp_tac compile_store_memory_typed_ind >> rpt conj_tac
  >- suspend "dispatch"
  >- simp[Once compile_store_memory_typed_def, alloca_suffix_return]
  >- simp[Once compile_store_memory_typed_def, alloca_suffix_return]
  >- suspend "fields_cons"
  >- suspend "sarray"
  >- suspend "dynarray"
  >- simp[Once compile_store_memory_typed_def, alloca_suffix_return]
  >> suspend "struct_cons"
QED

Resume alloca_suffix_typed_memory_family[dispatch]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `is_word_type dst_ty`
  >- (simp[Once compile_store_memory_typed_def] >>
      irule alloca_suffix_bind_floor >>
      simp[alloca_suffix_emit_op, alloca_suffix_emit_void]) >>
  Cases_on `is_bytestring_type dst_ty /\ is_bytestring_type src_ty`
  >- simp[Once compile_store_memory_typed_def, alloca_suffix_store_bytestring] >>
  Cases_on `acyclic_struct_metadata cenv.ce_struct_fields`
  >- (Cases_on `dst_ty` >> Cases_on `src_ty` >>
      gvs[] >>
      simp[Once compile_store_memory_typed_def, alloca_suffix_copy_memory]
      >>~- ([`case b' of Fixed _ => _ | Dynamic _ => _`],
             Cases_on `b` >> Cases_on `b'` >> gvs[alloca_suffix_copy_memory]) >>
      first_x_assum irule >> simp[]) >>
  simp[Once compile_store_memory_typed_def, alloca_suffix_emit_void]
QED

Resume alloca_suffix_typed_memory_family[fields_cons]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  simp[Once compile_store_memory_typed_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_with_byte_offset])
QED

Resume alloca_suffix_typed_memory_family[sarray]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `type_memory_bytes cenv dst_ty = type_memory_bytes cenv src_ty /\
            ~is_abi_dynamic cenv.ce_struct_fields dst_ty` >> gvs[] >>
  simp[Once compile_store_memory_typed_def, comp_ignore_bind_def,
       alloca_suffix_copy_memory] >> IF_CASES_TAC >> gvs[] >>
  rpt (rpt strip_tac >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_fresh_label, alloca_suffix_fresh_var,
            alloca_suffix_emit_inst, alloca_suffix_new_block,
            alloca_suffix_emit_op, alloca_suffix_return])
QED

Resume alloca_suffix_typed_memory_family[dynarray]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `dst_ty = src_ty` >> gvs[] >>
  simp[Once compile_store_memory_typed_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_fresh_label, alloca_suffix_fresh_var,
            alloca_suffix_emit_inst, alloca_suffix_new_block,
            alloca_suffix_emit_op, alloca_suffix_emit_void,
            alloca_suffix_copy_memory_dynamic, alloca_suffix_return])
QED

Resume alloca_suffix_typed_memory_family[struct_cons]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `ALOOKUP src_fields name`
  >- (gvs[] >> simp[Once compile_store_memory_typed_def, comp_ignore_bind_def] >>
      rpt (rpt strip_tac >> irule alloca_suffix_bind_floor >>
           simp[alloca_suffix_with_byte_offset])) >>
  rename1 `ALOOKUP src_fields name = SOME p` >> PairCases_on `p` >>
  gvs[] >> simp[Once compile_store_memory_typed_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_with_byte_offset])
QED
Finalise alloca_suffix_typed_memory_family[local]

Theorem alloca_suffix_store_memory_typed[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a
    (SND (compile_store_memory_typed cenv dst dst_ty src src_ty a))
Proof
  strip_tac >> irule (cj 1 alloca_suffix_typed_memory_family) >> simp[]
QED

Theorem compile_store_memory_typed_added_id:
  compile_store_memory_typed ce dst dt src st a = ((),b) /\
  id IN frag_ids a b ==>
  ?j. MEM j (added_insts a b) /\ j.inst_id = id
Proof
  strip_tac >>
  `alloca_suffix 0 a (SND (compile_store_memory_typed ce dst dt src st a))` by
    simp[alloca_suffix_store_memory_typed] >>
  qpat_x_assum `alloca_suffix _ _ _` mp_tac >>
  asm_simp_tac bool_ss [pairTheory.SND, alloca_suffix_def] >>
  metis_tac[]
QED

Theorem alloca_suffix_store_memory[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a
    (SND (compile_store_memory cenv src dst dst_ty src_ty a))
Proof
  strip_tac >> rewrite_tac[compile_store_memory_def] >>
  rpt IF_CASES_TAC >>
  simp[alloca_suffix_emit_void, alloca_suffix_store_bytestring,
       alloca_suffix_store_memory_typed, alloca_suffix_copy_memory]
QED

Theorem alloca_suffix_ifexp_arm[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_ifexp_arm cenv rt at vv a))
Proof
  strip_tac >> simp[compile_ifexp_arm_def, comp_ignore_bind_def] >> IF_CASES_TAC >>
  simp[alloca_suffix_unwrap_value] >>
  rpt (rpt strip_tac >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_alloc_buffer, alloca_suffix_unwrap_value,
            alloca_suffix_store_memory, alloca_suffix_return])
QED

Theorem alloca_suffix_expr_ifexp[local]:
  (!ce ty e a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (cfn ce ty e a))) /\
  k <= a.cs_next_var ==>
  alloca_suffix k a
    (SND (compile_expr_body cfn bfn tfn ce ty (IfExp ann cond te ee) a))
Proof
  strip_tac >> simp[compile_expr_body_def] >>
  rpt (ho_match_mp_tac alloca_suffix_pair_bind_floor >>
       simp[alloca_suffix_lower_value, alloca_suffix_fresh_var,
            alloca_suffix_fresh_label, alloca_suffix_emit_inst,
            alloca_suffix_new_block, alloca_suffix_ifexp_arm] >>
       rpt strip_tac) >>
  IF_CASES_TAC >> simp[alloca_suffix_refl]
QED

Theorem alloca_suffix_struct_lit_all[local]:
  (!ce ty e a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (cfn ce ty e a))) ==>
  !fs ty buf off a. k <= a.cs_next_var ==>
    alloca_suffix k a
      (SND (compile_struct_lit cfn cenv ty fs buf off a))
Proof
  strip_tac >> Induct >> simp[compile_struct_lit_def, alloca_suffix_return] >>
  gen_tac >> PairCases_on `h` >> simp[compile_struct_lit_def] >>
  rpt strip_tac >> rewrite_tac[comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_op, alloca_suffix_unwrap_value,
            alloca_suffix_store_memory, alloca_suffix_return])
QED

Theorem alloca_suffix_expr_struct[local]:
  (!ce ty e a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (cfn ce ty e a))) /\
  k <= a.cs_next_var ==>
  alloca_suffix k a
    (SND (compile_expr_body cfn bfn tfn ce ty (StructLit ann nm fs) a))
Proof
  strip_tac >> simp[compile_expr_body_def] >>
  rpt (ho_match_mp_tac alloca_suffix_pair_bind_floor >>
       simp[alloca_suffix_alloc_buffer, alloca_suffix_struct_lit_all,
            alloca_suffix_refl] >> rpt strip_tac) >>
  simp[alloca_suffix_refl]
QED

Theorem alloca_suffix_array_subscript[local]:
  (!op a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (loader op a))) /\
  k <= a.cs_next_var ==>
  alloca_suffix k a
    (SND (compile_array_subscript base_op idx dyn static_n ws sz signed loader a))
Proof
  strip_tac >> Cases_on `dyn` >> Cases_on `signed` >>
  simp[compile_array_subscript_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_return, alloca_suffix_emit_op,
            alloca_suffix_emit_void])
QED

Theorem alloca_suffix_mapping_subscript[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_mapping_subscript op key a))
Proof
  strip_tac >> simp[compile_mapping_subscript_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_alloc_buffer, alloca_suffix_emit_op,
            alloca_suffix_emit_void])
QED

Theorem alloca_suffix_keccak_key[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_keccak256_key op b a))
Proof
  strip_tac >> Cases_on `b` >>
  simp[compile_keccak256_key_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_alloc_buffer, alloca_suffix_emit_op,
            alloca_suffix_emit_void])
QED

Theorem alloca_suffix_get_target_ptr_all[local]:
  (!ce ty e a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (cfn ce ty e a))) ==>
  !bt a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (compile_get_target_ptr cfn cenv bt a))
Proof
  strip_tac >> measureInduct_on `base_assignment_target_size bt` >>
  Cases_on `bt` >> rpt strip_tac >>
  simp[Once compile_get_target_ptr_def]
  >- (rename1 `FLOOKUP cenv.ce_vars id` >>
      Cases_on `FLOOKUP cenv.ce_vars id` >> simp[alloca_suffix_return] >>
      rename1 `FLOOKUP cenv.ce_vars id = SOME vl` >>
      Cases_on `vl` >> simp[alloca_suffix_return])
  >- (rename1 `FLOOKUP cenv.ce_module_vars nsid` >>
      Cases_on `FLOOKUP cenv.ce_module_vars nsid` >> simp[alloca_suffix_return] >>
      rename1 `FLOOKUP cenv.ce_module_vars nsid = SOME vl` >>
      Cases_on `vl` >> simp[alloca_suffix_return]) >>
  irule alloca_suffix_bind_floor >> reverse conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> simp[]) >>
  simp[pairTheory.FORALL_PROD] >>
  map_every qx_gen_tac [`bop`, `locopt`, `ptopt`, `a'`] >> strip_tac
  >~ [`emit_op ADD _`]
  >- (rpt (rpt strip_tac >> irule alloca_suffix_bind_floor >>
           simp[alloca_suffix_emit_op, alloca_suffix_return])) >>
  namedCases_on `ptopt` ["", "pt"] >> simp[]
  >- (rpt (rpt strip_tac >> irule alloca_suffix_bind_floor >>
           simp[alloca_suffix_lower_value, alloca_suffix_array_subscript,
                alloca_suffix_ptr_load, alloca_suffix_return])) >>
  Cases_on `pt` >> simp[]
  >- (rpt (rpt strip_tac >> irule alloca_suffix_bind_floor >>
           simp[alloca_suffix_lower_value, alloca_suffix_mapping_subscript,
                alloca_suffix_return]) >>
      IF_CASES_TAC >> simp[alloca_suffix_keccak_key, alloca_suffix_return] >>
      rpt (rpt strip_tac >> irule alloca_suffix_bind_floor >>
           simp[alloca_suffix_mapping_subscript, alloca_suffix_return])) >>
  rpt (rpt strip_tac >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_lower_value, alloca_suffix_array_subscript,
            alloca_suffix_ptr_load, alloca_suffix_return])
QED

Theorem alloca_suffix_dynarray_pop[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a
    (SND (compile_dynarray_pop bop ws sz ctor imm loc a))
Proof
  strip_tac >> simp[compile_dynarray_pop_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_ptr_load, alloca_suffix_ptr_store,
            alloca_suffix_emit_op, alloca_suffix_emit_void])
QED

Theorem alloca_suffix_expr_pop[local]:
  (!ce ty e a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (cfn ce ty e a))) /\
  k <= a.cs_next_var ==>
  alloca_suffix k a
    (SND (compile_expr_body cfn bfn tfn ce ty (Pop ann target) a))
Proof
  strip_tac >> simp[compile_expr_body_def] >>
  rpt (ho_match_mp_tac alloca_suffix_pair_bind_floor >>
       simp[alloca_suffix_get_target_ptr_all, alloca_suffix_dynarray_pop,
            pairTheory.FORALL_PROD, alloca_suffix_refl] >>
       rpt strip_tac) >>
  simp[alloca_suffix_refl]
QED

Theorem alloca_suffix_name_vv[local]:
  alloca_suffix k a (SND (compile_name_vv ce ty id a))
Proof
  simp[compile_name_vv_def] >>
  Cases_on `FLOOKUP ce.ce_vars id` >> simp[alloca_suffix_return]
  >- (irule alloca_suffix_ignore_bind >>
      simp[alloca_suffix_return] >> irule alloca_suffix_emit_inst >> simp[]) >>
  rename1 `SOME vl` >> Cases_on `vl` >> simp[alloca_suffix_return] >>
  irule alloca_suffix_ignore_bind >>
  simp[alloca_suffix_return] >> irule alloca_suffix_emit_inst >> simp[]
QED

Theorem alloca_suffix_addmod[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_addmod x y z a))
Proof
  strip_tac >> simp[compile_addmod_def, comp_ignore_bind_def] >>
  irule alloca_suffix_bind_floor >>
  simp[alloca_suffix_emit_op, alloca_suffix_emit_void]
QED

Theorem alloca_suffix_addmod_names[local]:
  k <= st.cs_next_var ==>
  alloca_suffix k st
    (SND (compile_addmod_names ce rt aty a bty b mty m st))
Proof
  strip_tac >> simp[compile_addmod_names_def] >>
  rpt (irule alloca_suffix_pair_bind_floor >>
       simp[alloca_suffix_name_vv, alloca_suffix_unwrap_value,
            as_stack_val_pair, alloca_suffix_addmod] >> rpt strip_tac)
QED

Theorem alloca_suffix_mulmod[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_mulmod x y z a))
Proof
  strip_tac >> simp[compile_mulmod_def, comp_ignore_bind_def] >>
  irule alloca_suffix_bind_floor >>
  simp[alloca_suffix_emit_op, alloca_suffix_emit_void]
QED

Theorem alloca_suffix_mulmod_names[local]:
  k <= st.cs_next_var ==>
  alloca_suffix k st
    (SND (compile_mulmod_names ce rt aty a bty b mty m st))
Proof
  strip_tac >> simp[compile_mulmod_names_def] >>
  rpt (irule alloca_suffix_pair_bind_floor >>
       simp[alloca_suffix_name_vv, alloca_suffix_unwrap_value,
            as_stack_val_pair, alloca_suffix_mulmod] >> rpt strip_tac)
QED

Theorem alloca_suffix_pow_mod256[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_pow_mod256 x y a))
Proof
  simp[compile_pow_mod256_def, alloca_suffix_emit_op]
QED

Theorem alloca_suffix_powmod256_names[local]:
  k <= st.cs_next_var ==>
  alloca_suffix k st
    (SND (compile_powmod256_names ce rt aty a bty b st))
Proof
  strip_tac >> simp[compile_powmod256_names_def] >>
  rpt (irule alloca_suffix_pair_bind_floor >>
       simp[alloca_suffix_name_vv, alloca_suffix_unwrap_value,
            as_stack_val_pair, alloca_suffix_pow_mod256] >> rpt strip_tac)
QED

Theorem alloca_suffix_expr_builtin[local]:
  (!ce rt ty bi es a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (bfn ce rt ty bi es a))) /\
  k <= a.cs_next_var ==>
  alloca_suffix k a
    (SND (compile_expr_body cfn bfn tfn ce ty (Builtin ann bi es) a))
Proof
  strip_tac >>
  irule (BETA_RULE (Q.SPEC `\p. alloca_suffix k a (SND p)`
           compiler_expr_builtin_pred)) >>
  simp[alloca_suffix_addmod_names, alloca_suffix_mulmod_names,
       alloca_suffix_powmod256_names]
QED

Theorem alloca_suffix_store_byte_chunks[local]:
  !p bs off k a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (compile_store_byte_chunks p bs off a))
Proof
  ho_match_mp_tac compile_store_byte_chunks_ind >> rpt conj_tac >>
  rpt strip_tac >> simp[Once compile_store_byte_chunks_def, comp_ignore_bind_def,
                         alloca_suffix_return] >>
  rpt (rpt strip_tac >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_op, alloca_suffix_emit_void,
            alloca_suffix_return]) >> gvs[]
QED

Theorem alloca_suffix_bytelike_literal[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_bytelike_literal bs n a))
Proof
  strip_tac >> simp[compile_bytelike_literal_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_alloc_buffer, alloca_suffix_emit_void,
            alloca_suffix_store_byte_chunks, alloca_suffix_return])
QED

Theorem alloca_suffix_literal_vv[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_literal_vv ty lit a))
Proof
  strip_tac >> Cases_on `lit` >> simp[compile_literal_vv_def, alloca_suffix_return]
  >- (rename1 `BoolL b` >> Cases_on `b` >>
      simp[compile_literal_vv_def, alloca_suffix_return])
  >- (Cases_on `ty` >> simp[compile_literal_vv_def] >>
      irule alloca_suffix_bind_floor >>
      simp[alloca_suffix_bytelike_literal, alloca_suffix_return])
  >- (Cases_on `ty` >> simp[compile_literal_vv_def, alloca_suffix_return] >>
      rename1 `BaseT bt` >> Cases_on `bt` >>
      simp[compile_literal_vv_def, alloca_suffix_return] >>
      rename1 `BytesT bnd` >> Cases_on `bnd` >>
      simp[compile_literal_vv_def, alloca_suffix_return] >>
      irule alloca_suffix_bind_floor >>
      simp[alloca_suffix_bytelike_literal, alloca_suffix_return]) >>
  irule alloca_suffix_bind_floor >>
  simp[alloca_suffix_bytelike_literal, alloca_suffix_return]
QED

Theorem alloca_suffix_attribute_all[local]:
  (!ce ty e a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (cfn ce ty e a))) /\
  k <= a.cs_next_var ==>
  alloca_suffix k a
    (SND (compile_attribute cfn cenv rt ty e fld a))
Proof
  strip_tac >> simp[compile_attribute_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_op, alloca_suffix_return])
QED

Theorem alloca_suffix_materialize_vv[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_materialize_vv cenv ty vv a))
Proof
  strip_tac >> simp[compile_materialize_vv_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_alloc_buffer, alloca_suffix_unwrap_value,
            alloca_suffix_store_memory, alloca_suffix_return])
QED

Theorem alloca_suffix_snapshot_vv[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_snapshot_vv cenv copy vv a))
Proof
  strip_tac >> rw[compile_snapshot_vv_def, alloca_suffix_return] >>
  irule alloca_suffix_bind_floor >>
  simp[alloca_suffix_unwrap_value, alloca_suffix_materialize_vv,
       alloca_suffix_return]
QED

Theorem compile_snapshot_vv_added_id:
  compile_snapshot_vv ce copy vv a = (saved,b) /\ id IN frag_ids a b ==>
  ?j. MEM j (added_insts a b) /\ j.inst_id = id
Proof
  strip_tac >>
  `alloca_suffix 0 a (SND (compile_snapshot_vv ce copy vv a))` by
    simp[alloca_suffix_snapshot_vv] >>
  qpat_x_assum `alloca_suffix _ _ _` mp_tac >>
  asm_simp_tac bool_ss [pairTheory.SND, alloca_suffix_def] >>
  metis_tac[]
QED

Theorem alloca_suffix_subscript_all[local]:
  (!ce ty e a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (cfn ce ty e a))) /\
  k <= a.cs_next_var ==>
  alloca_suffix k a
    (SND (compile_subscript cfn cenv rt ty be ie a))
Proof
  strip_tac >> simp[compile_subscript_def] >>
  irule alloca_suffix_bind_floor >> simp[] >>
  rpt strip_tac >> irule alloca_suffix_bind_floor >>
  simp[alloca_suffix_snapshot_vv, alloca_suffix_return, COND_RATOR,
       COND_RAND] >>
  rpt strip_tac >> Cases_on `place_type cenv be`
  >- (simp[] >>
      rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
           simp[alloca_suffix_lower_value, alloca_suffix_mapping_subscript,
                alloca_suffix_snapshot_vv, alloca_suffix_keccak_key,
                alloca_suffix_return]) >>
      rpt strip_tac >> IF_CASES_TAC >>
      simp[alloca_suffix_keccak_key, alloca_suffix_return] >>
      rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
           simp[alloca_suffix_mapping_subscript,
                alloca_suffix_keccak_key, alloca_suffix_return])) >>
  rename1 `ValPT bt` >> Cases_on `bt` >>
  simp[compile_tuple_subscript_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_op, alloca_suffix_return,
            alloca_suffix_lower_value, alloca_suffix_array_subscript,
            alloca_suffix_ptr_load])
QED

Theorem alloca_stage_memory[local]:
  compile_stage_intcall_args cfn ce (e::es) (F::flags) (ty::tys) =
    do vv <- cfn ce (expr_type e) e;
       buf <- compile_alloc_buffer (MAX 32 (type_memory_bytes ce ty));
       op <- unwrap_value ce vv;
       compile_store_memory ce op buf.buf_operand ty (vv_type vv);
       rest <- compile_stage_intcall_args cfn ce es flags tys;
       return (buf.buf_operand::rest)
    od
Proof
  `(case ty of BaseT (BytesT (Dynamic _)) => T
      | BaseT (StringT _) => T | _ => F) = is_bytestring_type ty` by
    (Cases_on `ty` >> simp[is_bytestring_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> simp[is_bytestring_type_def] >>
     rename1 `BytesT sz` >> Cases_on `sz` >> simp[is_bytestring_type_def]) >>
  `!src dst. comp_ignore_bind (compile_store_bytestring src dst) (comp_return ()) =
     compile_store_bytestring src dst` by
    (rw[FUN_EQ_THM, comp_ignore_bind_def, comp_bind_def, comp_return_def,
        pairTheory.UNCURRY] >>
     metis_tac[pairTheory.PAIR, oneTheory.one]) >>
  simp[compile_stage_intcall_args_def, compile_store_memory_def]
QED

Theorem alloca_suffix_stage_intcall_args[local]:
  (!ce ty e a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (cfn ce ty e a))) ==>
  !cenv es flags tys a. k <= a.cs_next_var ==>
    alloca_suffix k a
      (SND (compile_stage_intcall_args cfn cenv es flags tys a))
Proof
  strip_tac >> Induct_on `es` >-
    simp[compile_stage_intcall_args_def, alloca_suffix_return] >>
  rpt gen_tac >> strip_tac >>
  namedCases_on `flags` ["", "flag fs"] >>
  namedCases_on `tys` ["", "ty ts"] >>
  TRY (Cases_on `flag`) >>
  simp[alloca_stage_memory] >>
  simp[compile_stage_intcall_args_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> irule alloca_suffix_bind_floor >>
       asm_simp_tac (srw_ss())
         [alloca_suffix_unwrap_value, alloca_suffix_alloc_buffer,
          alloca_suffix_store_memory, alloca_suffix_return])
QED

Theorem alloca_suffix_fresh_vars[local]:
  !n a. alloca_suffix k a (SND (fresh_vars n a))
Proof
  Induct >> simp[fresh_vars_def, alloca_suffix_return] >> gen_tac >>
  irule alloca_suffix_bind >>
  simp[alloca_suffix_fresh_var] >> rpt gen_tac >>
  irule alloca_suffix_bind >> simp[alloca_suffix_return]
QED

Theorem alloca_suffix_emit_multi_op[local]:
  opc <> ALLOCA /\ k <= a.cs_next_var ==>
  alloca_suffix k a (SND (emit_multi_op opc ops n a))
Proof
  strip_tac >> simp[emit_multi_op_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_fresh_vars, alloca_suffix_emit_inst,
            alloca_suffix_return])
QED

Theorem alloca_suffix_store_multi_results[local]:
  !ops off a. k <= a.cs_next_var ==>
  alloca_suffix k a (SND (store_multi_results buf ops off a))
Proof
  Induct >> simp[store_multi_results_def, alloca_suffix_return] >>
  rpt strip_tac >> simp[comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_op, alloca_suffix_emit_void])
QED

Theorem alloca_suffix_call_internal[local]:
  (!ce ty e a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (cfn ce ty e a))) /\
  k <= a.cs_next_var ==>
  alloca_suffix k a
    (SND (compile_call cfn ce rt ty (IntCall fid) es dflt a))
Proof
  strip_tac >> Cases_on `ce.ce_func_info (nsid_to_string fid)` >>
  rename1 `(_, finfo)` >> PairCases_on `finfo` >>
  simp[compile_call_def] >> rpt IF_CASES_TAC >> simp[] >>
  PURE_REWRITE_TAC [compilerFirstEmissionTheory.state_pair_let_bind] >>
  rpt (rpt strip_tac >> rpt CASE_TAC >>
       irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_alloc_buffer, alloca_suffix_stage_intcall_args,
            alloca_suffix_emit_multi_op, alloca_suffix_emit_void,
            alloca_suffix_emit_op, alloca_suffix_store_multi_results,
            alloca_suffix_refl]) >>
  rpt strip_tac >> rpt CASE_TAC >> simp[alloca_suffix_refl]
QED

Theorem alloca_suffix_ext_call_args[local]:
  (!ce ty e a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (cfn ce ty e a))) ==>
  !tys es a. k <= a.cs_next_var ==>
    alloca_suffix k a
      (SND (compile_ext_call_args cfn cenv kw_es tys es a))
Proof
  strip_tac >> Induct >> Cases_on `es` >>
  simp[compile_ext_call_args_def, alloca_suffix_return] >>
  rpt (rpt strip_tac >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_snapshot_vv, alloca_suffix_return])
QED

Theorem alloca_suffix_ext_call_kwarg[local]:
  (!ce ty e a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (cfn ce ty e a))) ==>
  !cenv rt kw e a. k <= a.cs_next_var ==>
    alloca_suffix k a
      (SND (compile_ext_call_kwarg cfn cenv rt kw e a))
Proof
  rpt strip_tac >> simp[compile_ext_call_kwarg_def] >>
  IF_CASES_TAC >> simp[] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_materialize_vv, alloca_suffix_lower_value,
            alloca_suffix_return])
QED

Theorem alloca_suffix_ext_call_kwargs[local]:
  (!ce ty e a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (cfn ce ty e a))) ==>
  !ks es a. k <= a.cs_next_var ==>
    alloca_suffix k a
      (SND (compile_ext_call_kwargs cfn cenv rt ks es a))
Proof
  strip_tac >> Induct >> Cases_on `es` >>
  simp[compile_ext_call_kwargs_def, alloca_suffix_return] >>
  rpt strip_tac >> irule alloca_suffix_bind_floor >>
  simp[alloca_suffix_ext_call_kwarg, pairTheory.FORALL_PROD] >>
  rpt strip_tac >> irule alloca_suffix_bind_floor >>
  simp[pairTheory.FORALL_PROD, alloca_suffix_return]
QED

Theorem alloca_suffix_encode_static_loop[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a
    (SND (compile_abi_encode_dyn_static_loop dst src info asz msz len a))
Proof
  strip_tac >> simp[compile_abi_encode_dyn_static_loop_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_alloc_buffer, alloca_suffix_emit_op,
            alloca_suffix_emit_void, alloca_suffix_emit_inst,
            alloca_suffix_fresh_label, alloca_suffix_new_block,
            alloca_suffix_encode_static_info])
QED

Theorem alloca_suffix_encode_family[local]:
  (!dst cp info dyn off dp k a. k <= a.cs_next_var ==>
    alloca_suffix k a
      (SND (compile_abi_encode_child dst cp info dyn off dp a))) /\
  (!dst src info k a. k <= a.cs_next_var ==>
    alloca_suffix k a
      (SND (compile_abi_encode_to_buf dst src info a))) /\
  (!dst src elems so ho dp k a. k <= a.cs_next_var ==>
    alloca_suffix k a
      (SND (compile_abi_encode_complex_elems dst src elems so ho dp a))) /\
  (!dst src info asz msz len k a. k <= a.cs_next_var ==>
    alloca_suffix k a
      (SND (compile_abi_encode_dyn_loop dst src info asz msz len a)))
Proof
  ho_match_mp_tac compile_abi_encode_child_ind >> rpt conj_tac
  >- suspend "child"
  >- simp[Once compile_abi_encode_child_def, alloca_suffix_encode_static]
  >- suspend "bytestring"
  >- suspend "copy"
  >- suspend "dynarray"
  >- simp[Once compile_abi_encode_child_def, alloca_suffix_return]
  >- suspend "complex"
  >- simp[Once compile_abi_encode_child_def, alloca_suffix_return]
  >- suspend "elems"
  >> suspend "loop"
QED

Resume alloca_suffix_encode_family[child]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `dyn` >> gvs[] >>
  simp[Once compile_abi_encode_child_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_op, alloca_suffix_emit_void,
            alloca_suffix_return])
QED

Resume alloca_suffix_encode_family[bytestring]:
  rpt gen_tac >> strip_tac >>
  simp[Once compile_abi_encode_child_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_op, alloca_suffix_emit_void])
QED

Resume alloca_suffix_encode_family[copy]:
  rpt gen_tac >> strip_tac >>
  simp[Once compile_abi_encode_child_def, comp_ignore_bind_def] >>
  irule alloca_suffix_bind_floor >>
  simp[alloca_suffix_emit_void, alloca_suffix_return]
QED

Resume alloca_suffix_encode_family[dynarray]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[] >> Cases_on `elem_is_dyn` >> gvs[] >>
  simp[Once compile_abi_encode_child_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_alloc_buffer, alloca_suffix_emit_op,
            alloca_suffix_emit_void, alloca_suffix_encode_static_loop])
QED

Resume alloca_suffix_encode_family[complex]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gvs[] >>
  simp[Once compile_abi_encode_child_def, comp_ignore_bind_def] >>
  IF_CASES_TAC >> gvs[] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_alloc_buffer, alloca_suffix_emit_op,
            alloca_suffix_emit_void, alloca_suffix_return])
QED

Resume alloca_suffix_encode_family[elems]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gvs[] >>
  simp[Once compile_abi_encode_child_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_op, arithmeticTheory.ADD_COMM])
QED

Resume alloca_suffix_encode_family[loop]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gvs[] >>
  simp[Once compile_abi_encode_child_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_alloc_buffer, alloca_suffix_emit_op,
            alloca_suffix_emit_void, alloca_suffix_emit_inst,
            alloca_suffix_fresh_label, alloca_suffix_new_block])
QED
Finalise alloca_suffix_encode_family[local]

Theorem alloca_suffix_extcodesize_check[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_extcodesize_check addr a))
Proof
  strip_tac >> simp[compile_extcodesize_check_def, comp_ignore_bind_def] >>
  irule alloca_suffix_bind_floor >>
  simp[alloca_suffix_emit_op, alloca_suffix_emit_void]
QED

Theorem alloca_suffix_select[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_select c x y a))
Proof
  strip_tac >> simp[compile_select_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_op])
QED

Theorem alloca_suffix_return_value_decode[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_return_value_decode lo hi a))
Proof
  strip_tac >> simp[compile_return_value_decode_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_op, alloca_suffix_emit_void,
            alloca_suffix_select])
QED

Theorem alloca_suffix_abi_clamp[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_abi_clamp_basetype op ci a))
Proof
  strip_tac >> Cases_on `ci` >>
  simp[compile_abi_clamp_basetype_def, alloca_suffix_abi_int_clamp,
       alloca_suffix_abi_bytes_clamp, alloca_suffix_return] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_op, alloca_suffix_emit_void])
QED

Theorem alloca_suffix_dec_addr[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_abi_dec_addr bop pos a))
Proof
  strip_tac >> simp[compile_abi_dec_addr_def] >>
  IF_CASES_TAC >> simp[alloca_suffix_emit_op, alloca_suffix_return]
QED

Theorem alloca_suffix_decode_copy[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a
    (SND ((case opc of
       CALLDATALOAD => emit_void CALLDATACOPY [dst; src; sz]
     | DLOAD => emit_void DLOADBYTES [dst; src; sz]
     | _ => emit_void MCOPY [dst; src; sz]) a))
Proof
  Cases_on `opc` >> simp[alloca_suffix_emit_void]
QED

Theorem alloca_suffix_decode_range[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_abi_decode_range_check lo hi lim a))
Proof
  strip_tac >> simp[compile_abi_decode_range_check_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_op, alloca_suffix_emit_void])
QED

Theorem alloca_suffix_decode_dyn_elem_ptr[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a
    (SND (compile_abi_decode_dyn_elem_ptr opc bop es sd hi asz a))
Proof
  strip_tac >> Cases_on `hi = Lit 0w` >>
  simp[compile_abi_decode_dyn_elem_ptr_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_dec_addr, alloca_suffix_decode_range,
            alloca_suffix_emit_op, alloca_suffix_emit_void,
            alloca_suffix_return])
QED

Theorem alloca_suffix_decode_static[local]:
  (!v a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (clamp v a))) /\
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_abi_decode_static src dst opc clamp a))
Proof
  strip_tac >> simp[compile_abi_decode_static_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_op, alloca_suffix_emit_void])
QED

Theorem alloca_suffix_getelemptr_abi[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a
    (SND (compile_getelemptr_abi src dyn off opc bop hi a))
Proof
  strip_tac >> Cases_on `dyn` >> Cases_on `hi = Lit 0w` >>
  simp[compile_getelemptr_abi_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_dec_addr, alloca_suffix_emit_op,
            alloca_suffix_emit_void, alloca_suffix_return])
QED

Theorem alloca_suffix_decode_family[local]:
  (!dst src opc bop hi info k a. k <= a.cs_next_var ==>
    alloca_suffix k a
      (SND (compile_abi_decode_to_buf dst src opc bop hi info a))) /\
  (!dst src opc bop hi elems ao vo k a. k <= a.cs_next_var ==>
    alloca_suffix k a
      (SND (compile_abi_decode_complex_elems dst src opc bop hi elems ao vo a))) /\
  (!dst src opc bop hi info asz msz ip cnt k a. k <= a.cs_next_var ==>
    alloca_suffix k a
      (SND (compile_abi_decode_dyn_loop dst src opc bop hi info asz msz ip cnt a)))
Proof
  ho_match_mp_tac compile_abi_decode_to_buf_ind >> rpt conj_tac
  >- suspend "prim"
  >- suspend "bytes"
  >- suspend "dyn"
  >- suspend "complex"
  >- simp[Once compile_abi_decode_to_buf_def, alloca_suffix_return]
  >- suspend "elems"
  >> suspend "loop"
QED

Resume alloca_suffix_decode_family[prim]:
  rpt gen_tac >> strip_tac >>
  simp[Once compile_abi_decode_to_buf_def] >>
  irule alloca_suffix_bind_floor >>
  simp[alloca_suffix_dec_addr, alloca_suffix_decode_static,
       alloca_suffix_abi_clamp]
QED

Resume alloca_suffix_decode_family[bytes]:
  rpt gen_tac >> strip_tac >> Cases_on `hi = Lit 0w` >>
  Cases_on `bop = Lit 0w` >>
  simp[Once compile_abi_decode_to_buf_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_decode_copy, alloca_suffix_dec_addr, alloca_suffix_decode_range,
            alloca_suffix_emit_op, alloca_suffix_emit_void,
            alloca_suffix_return])
QED

Resume alloca_suffix_decode_family[dyn]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `hi = Lit 0w` >>
  rename1 `DecDynArray info asz msz dynb maxn` >>
  Cases_on `~dynb /\ ~dec_info_needs_clamp info` >>
  gvs[] >>
  simp[Once compile_abi_decode_to_buf_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_decode_copy, alloca_suffix_dec_addr, alloca_suffix_decode_range,
            alloca_suffix_alloc_buffer, alloca_suffix_emit_op,
            alloca_suffix_emit_void, alloca_suffix_return])
QED

Resume alloca_suffix_decode_family[complex]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `hi = Lit 0w` >> gvs[] >>
  simp[Once compile_abi_decode_to_buf_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_decode_range, alloca_suffix_emit_op])
QED

Resume alloca_suffix_decode_family[elems]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gvs[] >>
  simp[Once compile_abi_decode_to_buf_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_getelemptr_abi, alloca_suffix_emit_op])
QED

Resume alloca_suffix_decode_family[loop]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gvs[] >>
  Cases_on `dec_info_needs_offset info` >>
  simp[Once compile_abi_decode_to_buf_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_dec_addr, alloca_suffix_decode_dyn_elem_ptr,
            alloca_suffix_emit_op, alloca_suffix_emit_void,
            alloca_suffix_emit_inst, alloca_suffix_fresh_label,
            alloca_suffix_new_block, alloca_suffix_return])
QED
Finalise alloca_suffix_decode_family[local]

Theorem alloca_suffix_default_return_path[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a
    (SND (compile_default_return_path ce rt dt buf res dv addr skip lo hi info a))
Proof
  strip_tac >> Cases_on `skip` >>
  simp[compile_default_return_path_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_op, alloca_suffix_emit_void,
            alloca_suffix_emit_inst, alloca_suffix_fresh_label,
            alloca_suffix_new_block, alloca_suffix_store_memory,
            alloca_suffix_extcodesize_check, alloca_suffix_return_value_decode,
            cj 1 alloca_suffix_decode_family, alloca_suffix_return])
QED

Theorem alloca_suffix_abi_encode_value_rows[local]:
  !rows off a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (compile_abi_encode_value_rows ce dst cursor off rows a))
Proof
  Induct >> simp[compile_abi_encode_value_rows_def, alloca_suffix_return] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >> strip_tac >>
  simp[compile_abi_encode_value_rows_def, LET_THM, comp_ignore_bind_def] >>
  Cases_on `is_abi_dynamic ce.ce_struct_fields h1` >> simp[comp_bind_assoc] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_op, alloca_suffix_emit_void, alloca_suffix_unwrap_value,
            alloca_suffix_store_memory, cj 2 alloca_suffix_encode_family])
QED

Theorem alloca_suffix_abi_encode_values[local]:
  k <= a.cs_next_var ==>
    alloca_suffix k a (SND (compile_abi_encode_values_to_buf ce dst rows a))
Proof
  strip_tac >> simp[compile_abi_encode_values_to_buf_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_alloc_buffer, alloca_suffix_emit_void, alloca_suffix_emit_op,
            alloca_suffix_abi_encode_value_rows])
QED

Theorem alloca_suffix_external_call_kwargs[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a
    (SND (compile_external_call_kwargs ce addr vs ts asz mid rsz
            lo rms static cv gas skip hd dv rt dt dinfo a))
Proof
  strip_tac >>
  simp[compile_external_call_kwargs_def, comp_ignore_bind_def] >>
  irule alloca_suffix_bind_floor >> simp[alloca_suffix_alloc_buffer] >>
  rpt strip_tac >> irule alloca_suffix_bind_floor >>
  simp[alloca_suffix_emit_void] >>
  rpt strip_tac >> irule alloca_suffix_bind_floor >> simp[] >> reverse conj_tac
  >- (rpt strip_tac >> IF_CASES_TAC >> simp[alloca_suffix_return] >>
      rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
           simp[alloca_suffix_abi_encode_values, alloca_suffix_emit_op])) >>
  rpt strip_tac >> irule alloca_suffix_bind_floor >>
  simp[alloca_suffix_emit_op] >>
  rpt strip_tac >> irule alloca_suffix_bind_floor >> simp[] >> reverse conj_tac
  >- (rpt strip_tac >> IF_CASES_TAC >>
      simp[alloca_suffix_extcodesize_check, alloca_suffix_return]) >>
  rpt strip_tac >> irule alloca_suffix_bind_floor >> simp[] >> reverse conj_tac
  >- (rpt strip_tac >> IF_CASES_TAC >> simp[alloca_suffix_emit_op]) >>
  rpt (rpt strip_tac >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_op, alloca_suffix_emit_void,
            alloca_suffix_emit_inst, alloca_suffix_fresh_label,
            alloca_suffix_new_block, alloca_suffix_alloc_buffer]) >>
  rpt strip_tac >> Cases_on `rt = NoneT` >> Cases_on `hd` >>
  simp[alloca_suffix_return] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_alloc_buffer, alloca_suffix_default_return_path,
            alloca_suffix_return_value_decode,
            cj 1 alloca_suffix_decode_family, alloca_suffix_return])
QED

Theorem alloca_suffix_call_external[local]:
  (!ce ty e a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (cfn ce ty e a))) /\
  k <= a.cs_next_var ==>
  alloca_suffix k a
    (SND (compile_call cfn ce rt ty (ExtCall sta skip sig opts) es dflt a))
Proof
  strip_tac >> PairCases_on `sig` >> Cases_on `es` >>
  simp[compile_call_def, alloca_suffix_emit_inst] >>
  rpt (ho_match_mp_tac alloca_suffix_pair_bind_floor >>
       simp[alloca_suffix_emit_inst, alloca_suffix_refl,
            alloca_suffix_lower_value,
            alloca_suffix_ext_call_args,
            alloca_suffix_ext_call_kwargs,
            pairTheory.FORALL_PROD] >> rpt strip_tac >> simp[]) >>
  rename1 `case default_opt of NONE => (F,Lit 0w,_) | SOME (d,dt) => (T,d,dt)` >>
  Cases_on `default_opt`
  >- (simp[] >>
      qmatch_goalsub_rename_tac `case gas_opt of NONE => emit_op GAS [] _ | SOME g => (g,_)` >>
      Cases_on `gas_opt` >> simp[] >>
      rpt (ho_match_mp_tac alloca_suffix_pair_bind_floor >>
           simp[alloca_suffix_emit_op, alloca_suffix_external_call_kwargs] >>
           rpt strip_tac >> simp[]) >>
      IF_CASES_TAC >> simp[alloca_suffix_refl]) >>
  rename1 `SOME dp` >> PairCases_on `dp` >> simp[] >>
  qmatch_goalsub_rename_tac `case gas_opt of NONE => emit_op GAS [] _ | SOME g => (g,_)` >>
  Cases_on `gas_opt` >> simp[] >>
  rpt (ho_match_mp_tac alloca_suffix_pair_bind_floor >>
       simp[alloca_suffix_emit_op, alloca_suffix_external_call_kwargs] >>
       rpt strip_tac >> simp[]) >>
  IF_CASES_TAC >> simp[alloca_suffix_refl]
QED

Theorem alloca_suffix_raw_call_outbuf[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_raw_call_outbuf n a))
Proof
  strip_tac >> simp[compile_raw_call_outbuf_def] >>
  IF_CASES_TAC >> simp[] >>
  rpt (rpt strip_tac >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_alloc_buffer, alloca_suffix_emit_op,
            alloca_suffix_return])
QED

Theorem alloca_suffix_raw_call_finish[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a
    (SND (compile_raw_call_finish dest dp dl gas value ct n rof ov op a))
Proof
  strip_tac >> Cases_on `ct` >> Cases_on `rof` >>
  Cases_on `n > 0` >>
  simp[compile_raw_call_finish_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_op, alloca_suffix_emit_inst,
            alloca_suffix_emit_void, alloca_suffix_fresh_label,
            alloca_suffix_new_block, alloca_suffix_alloc_buffer,
            alloca_suffix_select, alloca_suffix_return])
QED

Theorem alloca_suffix_call_raw[local]:
  (!ce ty e a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (cfn ce ty e a))) /\
  k <= a.cs_next_var ==>
  alloca_suffix k a
    (SND (compile_call cfn ce rt ty (RawCallTarget rcf) es dflt a))
Proof
  strip_tac >> namedCases_on `es` ["", "addr_e rest"]
  >- (simp[compile_call_def] >> ho_match_mp_tac alloca_suffix_pair_bind_floor >>
      simp[alloca_suffix_emit_inst, alloca_suffix_refl]) >>
  Cases_on `rest` >> simp[compile_call_def] >>
  rpt (ho_match_mp_tac alloca_suffix_pair_bind_floor >>
       simp[alloca_suffix_emit_inst, alloca_suffix_refl,
            alloca_suffix_lower_value, alloca_suffix_emit_op,
            alloca_suffix_ext_call_kwargs,
            pairTheory.FORALL_PROD] >> rpt strip_tac >> simp[]) >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[alloca_suffix_emit_op,
       alloca_suffix_raw_call_outbuf, alloca_suffix_raw_call_finish,
       alloca_suffix_refl, pairTheory.FORALL_PROD] >>
       rpt (ho_match_mp_tac alloca_suffix_pair_bind_floor >>
            simp[alloca_suffix_raw_call_outbuf, alloca_suffix_raw_call_finish,
                 alloca_suffix_emit_op, pairTheory.FORALL_PROD] >>
            rpt strip_tac >> simp[alloca_suffix_refl])) >>
  simp[alloca_suffix_raw_call_outbuf]
QED

Theorem alloca_suffix_alloc_dynamic[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_alloc_dynamic sz a))
Proof
  simp[compile_alloc_dynamic_def, alloca_suffix_emit_op]
QED

Theorem alloca_suffix_msg_data_to_memory[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_msg_data_to_memory a))
Proof
  strip_tac >> simp[compile_msg_data_to_memory_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_op, alloca_suffix_alloc_dynamic,
            alloca_suffix_emit_void, alloca_suffix_return])
QED

Theorem alloca_suffix_call_calldata[local]:
  (!ce ty e a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (cfn ce ty e a))) /\
  k <= a.cs_next_var ==>
  alloca_suffix k a
    (SND (compile_call cfn ce rt ty (RawCallCalldataTarget rcf) es dflt a))
Proof
  strip_tac >> Cases_on `es` >> simp[compile_call_def] >>
  rpt (ho_match_mp_tac alloca_suffix_pair_bind_floor >>
       simp[alloca_suffix_emit_inst, alloca_suffix_refl,
            alloca_suffix_lower_value,
            alloca_suffix_ext_call_kwargs,
            pairTheory.FORALL_PROD] >> rpt strip_tac >> simp[]) >>
  simp[alloca_suffix_raw_call_outbuf, alloca_suffix_raw_call_finish,
       alloca_suffix_msg_data_to_memory, alloca_suffix_emit_void] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[alloca_suffix_emit_op,
       alloca_suffix_raw_call_outbuf, alloca_suffix_raw_call_finish,
       alloca_suffix_msg_data_to_memory, alloca_suffix_emit_void,
       alloca_suffix_refl, pairTheory.FORALL_PROD] >>
       rpt (ho_match_mp_tac alloca_suffix_pair_bind_floor >>
            simp[alloca_suffix_raw_call_outbuf, alloca_suffix_raw_call_finish,
                 alloca_suffix_msg_data_to_memory, alloca_suffix_emit_void,
                 alloca_suffix_emit_op, pairTheory.FORALL_PROD] >>
            rpt strip_tac >> simp[alloca_suffix_refl])) >>
  simp[alloca_suffix_raw_call_outbuf, alloca_suffix_msg_data_to_memory,
       alloca_suffix_emit_void, alloca_suffix_raw_call_finish]

QED

Theorem alloca_suffix_call_send[local]:
  (!ce ty e a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (cfn ce ty e a))) /\
  k <= a.cs_next_var ==>
  alloca_suffix k a
    (SND (compile_call cfn ce rt ty (Send hg) es dflt a))
Proof
  strip_tac >> namedCases_on `es` ["", "addr rest"] >>
  simp[compile_call_def] >>
  rpt (ho_match_mp_tac alloca_suffix_pair_bind_floor >>
       simp[alloca_suffix_emit_inst, alloca_suffix_refl] >>
       rpt strip_tac) >>
  Cases_on `rest` >> simp[] >> rpt IF_CASES_TAC >> simp[] >>
  rpt (ho_match_mp_tac alloca_suffix_pair_bind_floor >>
       simp[alloca_suffix_emit_inst, alloca_suffix_lower_value,
            alloca_suffix_emit_op, alloca_suffix_emit_void,
            alloca_suffix_refl] >> rpt strip_tac >> simp[]) >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[] >>
       rpt (ho_match_mp_tac alloca_suffix_pair_bind_floor >>
            simp[alloca_suffix_lower_value, alloca_suffix_emit_op,
                 alloca_suffix_emit_void, alloca_suffix_refl] >>
            rpt strip_tac >> simp[])) >>
  simp[alloca_suffix_refl, alloca_suffix_lower_value]
QED

Theorem alloca_suffix_multi_exprs_floor[local]:
  (!ce ty e a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (cfn ce ty e a))) ==>
  !es a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (compile_multi_exprs cfn cenv es a))
Proof
  strip_tac >> Induct >> simp[compile_multi_exprs_def, alloca_suffix_return] >>
  rpt strip_tac >> irule alloca_suffix_bind_floor >> conj_tac
  >- (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
      simp[alloca_suffix_return]) >>
  simp[] >> rpt strip_tac >> irule alloca_suffix_lower_value >> simp[]
QED

Theorem alloca_suffix_call_log[local]:
  (!ce ty e a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (cfn ce ty e a))) /\
  k <= a.cs_next_var ==>
  alloca_suffix k a
    (SND (compile_call cfn ce rt ty RawLog es dflt a))
Proof
  strip_tac >> namedCases_on `es` ["", "topics rest"] >>
  simp[compile_call_def] >>
  rpt (ho_match_mp_tac alloca_suffix_pair_bind_floor >>
       simp[alloca_suffix_emit_inst, alloca_suffix_refl] >>
       rpt strip_tac) >>
  namedCases_on `rest` ["", "data tail"]
  >- (simp[] >> ho_match_mp_tac alloca_suffix_pair_bind_floor >>
      simp[alloca_suffix_emit_inst, alloca_suffix_refl]) >>
  simp[] >> Cases_on `tail` >> simp[] >>
  rpt (ho_match_mp_tac alloca_suffix_pair_bind_floor >>
       simp[alloca_suffix_emit_inst, alloca_suffix_multi_exprs_floor,
            alloca_suffix_refl] >> rpt strip_tac) >>
  IF_CASES_TAC >> simp[] >>
  rpt (ho_match_mp_tac alloca_suffix_pair_bind_floor >>
       simp[alloca_suffix_alloc_buffer, alloca_suffix_lower_value,
            alloca_suffix_emit_void, alloca_suffix_emit_op,
            alloca_suffix_emit_inst, alloca_suffix_refl] >>
       rpt strip_tac >> simp[]) >>
  simp[alloca_suffix_lower_value, alloca_suffix_refl]
QED

Theorem alloca_suffix_raw_revert[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_raw_revert dp a))
Proof
  strip_tac >> simp[compile_raw_revert_def] >>
  rpt (rpt strip_tac >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_op, alloca_suffix_emit_inst])
QED

Theorem alloca_suffix_call_revert[local]:
  (!ce ty e a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (cfn ce ty e a))) /\
  k <= a.cs_next_var ==>
  alloca_suffix k a
    (SND (compile_call cfn ce rt ty RawRevert es dflt a))
Proof
  strip_tac >> namedCases_on `es` ["", "data rest"] >>
  simp[compile_call_def] >>
  rpt (ho_match_mp_tac alloca_suffix_pair_bind_floor >>
       simp[alloca_suffix_emit_inst, alloca_suffix_refl] >>
       rpt strip_tac) >>
  Cases_on `rest` >> simp[] >>
  rpt (ho_match_mp_tac alloca_suffix_pair_bind_floor >>
       simp[alloca_suffix_lower_value, alloca_suffix_raw_revert,
            alloca_suffix_emit_inst, alloca_suffix_refl] >>
       rpt strip_tac >> simp[]) >>
  simp[alloca_suffix_lower_value, alloca_suffix_refl]
QED

Theorem alloca_suffix_call_selfdestruct[local]:
  (!ce ty e a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (cfn ce ty e a))) /\
  k <= a.cs_next_var ==>
  alloca_suffix k a
    (SND (compile_call cfn ce rt ty SelfDestructTarget es dflt a))
Proof
  strip_tac >> namedCases_on `es` ["", "to_e rest"] >>
  TRY (Cases_on `rest`) >> simp[compile_call_def] >>
  rpt (ho_match_mp_tac alloca_suffix_pair_bind_floor >>
       gs[alloca_suffix_lower_value, alloca_suffix_emit_inst,
          alloca_suffix_emit_void, alloca_suffix_refl,
          builtinSystemTheory.compile_selfdestruct_def] >>
       rpt strip_tac)
QED

Theorem alloca_suffix_slot_to_memory[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a
    (SND (compile_slot_to_memory src dst n loc a))
Proof
  simp[compile_slot_to_memory_def, alloca_suffix_word_copy_loop]
QED

Theorem alloca_suffix_create_snapshot[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_create_snapshot ce vv ty a))
Proof
  strip_tac >> simp[compile_create_snapshot_def, comp_ignore_bind_def] >>
  irule alloca_suffix_bind_floor >> simp[alloca_suffix_alloc_buffer] >>
  Cases_on `vv_location vv` >> simp[]
  >- (rpt (rpt strip_tac >> irule alloca_suffix_bind_floor >>
           simp[alloca_suffix_emit_op, alloca_suffix_copy_memory_dynamic,
                alloca_suffix_return])) >>
  rename1 `vv_location vv = SOME loc` >> Cases_on `loc` >> simp[] >>
  rpt (rpt strip_tac >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_op, alloca_suffix_copy_memory_dynamic,
            alloca_suffix_slot_to_memory, alloca_suffix_imm_copy,
            alloca_suffix_return])
QED

val alloca_suffix_create_tac = fn helpers => rpt (FIRST [
  CHANGED_TAC (simp ([LET_THM, pairTheory.FORALL_PROD, pairTheory.UNCURRY_DEF,
    alloca_suffix_emit_op, alloca_suffix_emit_void, alloca_suffix_emit_inst,
    alloca_suffix_alloc_buffer, alloca_suffix_fresh_label, alloca_suffix_new_block,
    alloca_suffix_return, alloca_suffix_lower_value, alloca_suffix_unwrap_value,
    alloca_suffix_snapshot_vv, alloca_suffix_abi_encode_values,
    alloca_suffix_copy_memory_dynamic] @ helpers)),
  gen_tac, DISCH_TAC, conj_tac,
  ho_match_mp_tac alloca_suffix_bind_floor,
  ho_match_mp_tac alloca_suffix_ignore_floor,
  IF_CASES_TAC, BasicProvers.CASE_TAC]);

Theorem alloca_suffix_create_ctor_args[local]:
  (!ce ty e a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (cfn ce ty e a))) ==>
  !ce args a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (compile_create_ctor_args cfn ce args a))
Proof
  strip_tac >> Induct_on `args` >>
  simp[Once compile_create_ctor_args_def] >>
  alloca_suffix_create_tac []
QED

Theorem alloca_suffix_create_salt[local]:
  (!ce ty e a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (cfn ce ty e a))) ==>
  !ce salt a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (compile_create_salt cfn ce salt a))
Proof
  strip_tac >> rpt gen_tac >> Cases_on `salt` >>
  simp[compile_create_salt_def, alloca_suffix_return] >>
  strip_tac >> irule alloca_suffix_bind_floor >>
  simp[alloca_suffix_lower_value, alloca_suffix_return]
QED

Theorem alloca_suffix_check_create_result[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_check_create_result res rof a))
Proof
  strip_tac >> Cases_on `rof` >>
  simp[compile_check_create_result_def, comp_ignore_bind_def, alloca_suffix_return] >>
  rpt (rpt strip_tac >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_fresh_label, alloca_suffix_emit_inst,
            alloca_suffix_new_block, alloca_suffix_emit_op,
            alloca_suffix_alloc_buffer, alloca_suffix_emit_void,
            alloca_suffix_return])
QED

Theorem alloca_suffix_create_dispatch[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a
    (SND (compile_create_dispatch codep cl cv salt rof a))
Proof
  strip_tac >> Cases_on `salt` >> simp[compile_create_dispatch_def] >>
  irule alloca_suffix_bind_floor >>
  simp[alloca_suffix_emit_op, alloca_suffix_check_create_result]
QED

Theorem alloca_suffix_raw_create[local]:
  (!ce ty e a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (cfn ce ty e a))) ==>
  !ce be ve es salt rof a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (compile_raw_create cfn ce be ve es salt rof a))
Proof
  strip_tac >> simp[compile_raw_create_def] >>
  alloca_suffix_create_tac [alloca_suffix_create_snapshot, alloca_suffix_create_ctor_args,
    alloca_suffix_create_salt, alloca_suffix_create_dispatch]
QED

Theorem alloca_suffix_create_proxy_buf[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_create_proxy_buf target a))
Proof
  strip_tac >> simp[compile_create_proxy_buf_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_alloc_buffer, alloca_suffix_emit_void,
            alloca_suffix_emit_op, alloca_suffix_return])
QED

Theorem alloca_suffix_create_copy[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_create_copy target cv salt rof a))
Proof
  strip_tac >> Cases_on `salt` >> Cases_on `rof` >>
  simp[compile_create_copy_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_op, alloca_suffix_emit_void,
            alloca_suffix_alloc_dynamic, alloca_suffix_return,
            alloca_suffix_check_create_result])
QED

Theorem alloca_suffix_create_blueprint_check[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_create_blueprint_check is_lit target off a))
Proof
  Cases_on `is_lit` >> simp[compile_create_blueprint_check_def] >>
  alloca_suffix_create_tac []
QED

Theorem alloca_suffix_create_blueprint_args[local]:
  (!ce ty e a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (cfn ce ty e a))) ==>
  !ce raw later_es es a. k <= a.cs_next_var ==>
    alloca_suffix k a
      (SND (compile_create_blueprint_args cfn ce raw later_es es a))
Proof
  strip_tac >> simp[compile_create_blueprint_args_def] >>
  alloca_suffix_create_tac [alloca_suffix_create_ctor_args]
QED

Theorem alloca_suffix_create_blueprint_append[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a
    (SND (compile_create_blueprint_append target cv salt off sz ap al rof a))
Proof
  strip_tac >> Cases_on `salt` >> Cases_on `rof` >> Cases_on `al = Lit 0w` >>
  simp[compile_create_blueprint_append_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_op, alloca_suffix_emit_void,
            alloca_suffix_alloc_dynamic, alloca_suffix_copy_memory_dynamic,
            alloca_suffix_return, alloca_suffix_check_create_result])
QED

Theorem alloca_suffix_create_call[local]:
  (!ce ty e a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (cfn ce ty e a))) ==>
  !ce ck hs rof es a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (compile_create_call cfn ce ck hs rof es a))
Proof
  strip_tac >> rpt gen_tac >> Cases_on `ck` >>
  simp[compile_create_call_def] >>
  alloca_suffix_create_tac [alloca_suffix_raw_create, alloca_suffix_create_proxy_buf,
    alloca_suffix_create_salt, alloca_suffix_create_dispatch, alloca_suffix_create_copy,
    alloca_suffix_create_blueprint_check, alloca_suffix_create_blueprint_args,
    alloca_suffix_create_blueprint_append]
QED

Theorem alloca_suffix_call_create[local]:
  (!ce ty e a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (cfn ce ty e a))) /\
  k <= a.cs_next_var ==>
  alloca_suffix k a
    (SND (compile_call cfn ce rt ty (CreateTarget ck hs rof extra) es dflt a))
Proof
  strip_tac >> simp[compile_call_def] >>
  Cases_on `compile_create_call cfn ce ck hs rof es a` >>
  simp[as_stack_val_def] >>
  metis_tac[alloca_suffix_create_call, pairTheory.SND]
QED

Theorem alloca_suffix_call[local]:
  (!ce ty e a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (cfn ce ty e a))) ==>
  !ce rt ty target es dflt a. k <= a.cs_next_var ==>
    alloca_suffix k a
      (SND (compile_call cfn ce rt ty target es dflt a))
Proof
  strip_tac >> rpt gen_tac >> Cases_on `target` >>
  simp[alloca_suffix_call_internal, alloca_suffix_call_external,
       alloca_suffix_call_raw, alloca_suffix_call_calldata,
       alloca_suffix_call_send, alloca_suffix_call_log,
       alloca_suffix_call_revert, alloca_suffix_call_selfdestruct,
       alloca_suffix_call_create]
QED

Theorem alloca_suffix_expr_body[local]:
  (!ce ty e a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (cfn ce ty e a))) /\
  (!ce rt ty bi es a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (bfn ce rt ty bi es a))) /\
  (!ce vt ty tb rt es a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (tfn ce vt ty tb rt es a))) ==>
  !ce ty e a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (compile_expr_body cfn bfn tfn ce ty e a))
Proof
  strip_tac >> rpt gen_tac >> Cases_on `e` >>
  simp[alloca_suffix_expr_ifexp, alloca_suffix_expr_struct,
       alloca_suffix_expr_pop, alloca_suffix_expr_builtin] >>
  simp[compile_expr_body_def, alloca_suffix_literal_vv,
       alloca_suffix_name_vv, alloca_suffix_attribute_all,
       alloca_suffix_subscript_all, alloca_suffix_call,
       alloca_suffix_refl] >>
  strip_tac >> rename1 `FLOOKUP ce.ce_module_vars nsid` >>
  Cases_on `FLOOKUP ce.ce_module_vars nsid` >> simp[alloca_suffix_refl]
  >- (ho_match_mp_tac alloca_suffix_pair_bind_floor >>
      simp[alloca_suffix_emit_inst, alloca_suffix_refl]) >>
  rename1 `SOME vl` >> Cases_on `vl` >>
  simp[alloca_suffix_refl] >>
  ho_match_mp_tac alloca_suffix_pair_bind_floor >>
  simp[alloca_suffix_emit_inst, alloca_suffix_refl]
QED

Theorem alloca_suffix_invalid_expr_call[local]:
  alloca_suffix k a (SND (invalid_expr_call ty a))
Proof
  simp[invalid_expr_call_def, pairTheory.UNCURRY] >>
  irule alloca_suffix_emit_inst >> simp[]
QED

Theorem alloca_suffix_expr_callback_all[local]:
  (!ce ty e a. expr_size e + cenv_defaults_size ce < bound /\
    k <= a.cs_next_var ==>
    alloca_suffix k a (SND (cfn ce ty e a))) ==>
  !ce ty e a. k <= a.cs_next_var ==>
    alloca_suffix k a
      (SND (expr_child_callback bound cfn ce ty e a))
Proof
  rpt strip_tac >> simp[expr_child_callback_def] >> IF_CASES_TAC >>
  simp[alloca_suffix_invalid_expr_call] >> first_x_assum irule >> simp[]
QED

Theorem alloca_suffix_builtin_callback_all[local]:
  (!ce rt ty bi es a. list_size expr_size es + cenv_defaults_size ce < bound /\
    k <= a.cs_next_var ==>
    alloca_suffix k a (SND (dispatch ce rt ty bi es a))) ==>
  !ce rt ty bi es a. k <= a.cs_next_var ==>
    alloca_suffix k a
      (SND (builtin_child_callback bound dispatch ce rt ty bi es a))
Proof
  rpt strip_tac >> simp[builtin_child_callback_def] >> IF_CASES_TAC >>
  simp[alloca_suffix_invalid_expr_call] >> first_x_assum irule >> simp[]
QED

Theorem alloca_suffix_type_callback_all[local]:
  (!ce vt ty tb rt es a. list_size expr_size es + cenv_defaults_size ce < bound /\
    k <= a.cs_next_var ==>
    alloca_suffix k a (SND (dispatch ce vt ty tb rt es a))) ==>
  !ce vt ty tb rt es a. k <= a.cs_next_var ==>
    alloca_suffix k a
      (SND (type_child_callback bound dispatch ce vt ty tb rt es a))
Proof
  rpt strip_tac >> simp[type_child_callback_def] >> IF_CASES_TAC >>
  simp[alloca_suffix_invalid_expr_call] >> first_x_assum irule >> simp[]
QED

Theorem alloca_suffix_bytestring_hash[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_bytestring_hash p a))
Proof
  strip_tac >> simp[compile_bytestring_hash_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_op])
QED

Theorem alloca_suffix_clamp[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_clamp v ty a))
Proof
  strip_tac >> Cases_on `type_bounds ty` >> simp[compile_clamp_def] >>
  Cases_on `is_signed_type ty` >> simp[] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_op, alloca_suffix_emit_void])
QED

Theorem alloca_suffix_clamp_return[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (clamp_and_return v ty a))
Proof
  strip_tac >> simp[clamp_and_return_def, comp_ignore_bind_def] >>
  irule alloca_suffix_bind_floor >>
  simp[alloca_suffix_clamp, alloca_suffix_return]
QED

Theorem alloca_suffix_safe_add[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_safe_add x y ty a))
Proof
  strip_tac >> Cases_on `type_bits ty < 256` >> Cases_on `is_signed_type ty` >>
  simp[compile_safe_add_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_op, alloca_suffix_emit_void,
            alloca_suffix_clamp_return, alloca_suffix_return])
QED

Theorem alloca_suffix_safe_sub[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_safe_sub x y ty a))
Proof
  strip_tac >> Cases_on `type_bits ty < 256` >> Cases_on `is_signed_type ty` >>
  simp[compile_safe_sub_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_op, alloca_suffix_emit_void,
            alloca_suffix_clamp_return, alloca_suffix_return])
QED

Theorem alloca_suffix_mul_check[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_mul_overflow_check x y res sg bits a))
Proof
  strip_tac >> Cases_on `sg /\ bits = 256` >>
  simp[compile_mul_overflow_check_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_op, alloca_suffix_emit_void,
            alloca_suffix_return])
QED

Theorem alloca_suffix_safe_mul[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_safe_mul x y ty a))
Proof
  strip_tac >> Cases_on `type_bits ty > 128` >>
  Cases_on `is_decimal_type ty` >> Cases_on `type_bits ty < 256` >>
  simp[compile_safe_mul_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_op, alloca_suffix_mul_check,
            alloca_suffix_clamp_return, alloca_suffix_return])
QED

Theorem alloca_suffix_safe_div[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_safe_div x y ty a))
Proof
  strip_tac >> Cases_on `is_signed_type ty` >>
  Cases_on `type_bits ty = 256` >> Cases_on `type_bits ty < 256` >>
  simp[compile_safe_div_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_op, alloca_suffix_emit_void,
            alloca_suffix_clamp_return, alloca_suffix_return])
QED

Theorem alloca_suffix_safe_decimal_div[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_safe_decimal_div x y dv ty a))
Proof
  strip_tac >> simp[compile_safe_decimal_div_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_op, alloca_suffix_emit_void,
            alloca_suffix_clamp_return])
QED

Theorem alloca_suffix_safe_mod[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_safe_mod x y ty a))
Proof
  strip_tac >> Cases_on `is_signed_type ty` >>
  simp[compile_safe_mod_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_op, alloca_suffix_emit_void])
QED

Theorem alloca_suffix_safe_pow[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_safe_pow x y ty bl el a))
Proof
  strip_tac >> Cases_on `bl` >> Cases_on `el` >>
  simp[compile_safe_pow_def, comp_ignore_bind_def] >>
  rpt IF_CASES_TAC >> simp[] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_op, alloca_suffix_emit_void,
            alloca_suffix_clamp, alloca_suffix_return])
QED

Theorem alloca_suffix_compare[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_compare op x y ty a))
Proof
  strip_tac >> Cases_on `op` >> Cases_on `is_uint256 ty` >>
  simp[compile_compare_def, comp_ignore_bind_def, alloca_suffix_emit_op] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_op, alloca_suffix_emit_inst,
            alloca_suffix_return])
QED

Theorem alloca_suffix_wrap_truncate[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (wrap_truncate v ty a))
Proof
  strip_tac >> Cases_on `type_bits ty < 256` >> Cases_on `is_signed_type ty` >>
  simp[wrap_truncate_def, alloca_suffix_emit_op, alloca_suffix_return]
QED

Theorem alloca_suffix_binop[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_binop op x y ty bl el a))
Proof
  strip_tac >> Cases_on `op` >> Cases_on `is_signed_type ty` >>
  Cases_on `is_decimal_type ty` >> Cases_on `is_uint256 ty` >>
  simp[compile_binop_def, comp_ignore_bind_def, alloca_suffix_safe_add,
       alloca_suffix_safe_sub, alloca_suffix_safe_mul,
       alloca_suffix_safe_div, alloca_suffix_safe_decimal_div,
       alloca_suffix_safe_mod, alloca_suffix_safe_pow,
       alloca_suffix_compare, alloca_suffix_emit_op] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_op, alloca_suffix_emit_inst,
            alloca_suffix_wrap_truncate, alloca_suffix_select,
            alloca_suffix_return])
QED

Theorem intcall_make_array_case_pred[local]:
  !P ordinary special e.
    P ordinary /\
    (!ann et bnd elems. e = Builtin ann (MakeArray et bnd) elems ==>
      P (special elems)) ==>
    P (case e of Builtin _ (MakeArray _ _) elems => special elems
       | _ => ordinary)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `e` >> simp[] >>
  rename1 `Builtin ann bi es` >> Cases_on `bi` >> simp[]
QED

Theorem alloca_suffix_membership_loop[local]:
  (!v a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (loader v a))) /\
  k <= a.cs_next_var ==>
  alloca_suffix k a
    (SND (compile_array_membership_loop needle arr len sz off loader bound_opt isin a))
Proof
  strip_tac >> Cases_on `bound_opt` >> Cases_on `off > 0` >> Cases_on `isin` >>
  simp[compile_array_membership_loop_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_op, alloca_suffix_emit_inst,
            alloca_suffix_new_block, alloca_suffix_fresh_var,
            alloca_suffix_fresh_label, alloca_suffix_return])
QED

Theorem alloca_suffix_var_membership[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a
    (SND (compile_var_array_membership cenv needle vv ty isin a))
Proof
  strip_tac >> Cases_on `ty` >>
  simp[compile_var_array_membership_def, comp_ignore_bind_def,
       alloca_suffix_membership_loop, alloca_suffix_ptr_load,
       alloca_suffix_return] >>
  rpt (rpt strip_tac >>
       simp[alloca_suffix_return, alloca_suffix_ptr_load,
            alloca_suffix_membership_loop, alloca_suffix_emit_op,
            alloca_suffix_emit_inst] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_membership_loop, alloca_suffix_ptr_load,
            alloca_suffix_emit_op, alloca_suffix_emit_inst,
            alloca_suffix_return]) >>
  rename1 `case bnd of Fixed _ => _ | Dynamic _ => _` >>
  Cases_on `bnd` >> simp[] >>
  rpt (rpt strip_tac >>
       simp[alloca_suffix_return, alloca_suffix_ptr_load,
            alloca_suffix_membership_loop, alloca_suffix_emit_op,
            alloca_suffix_emit_inst] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_membership_loop, alloca_suffix_ptr_load,
            alloca_suffix_emit_op, alloca_suffix_emit_inst,
            alloca_suffix_return])
QED

Theorem alloca_suffix_membership_callback[local]:
  (!ce ty e a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (cfn ce ty e a))) /\
  k <= a.cs_next_var ==>
  alloca_suffix k a
    (SND ((\(vv,b). as_stack_val rt
      (compile_var_array_membership ce needle vv rhs_ty is_in b))
      (cfn ce rhs_ty e a)))
Proof
  strip_tac >> ho_match_mp_tac alloca_suffix_pair_bind_floor >>
  simp[exprBopLoweringTheory.as_stack_val_pair, alloca_suffix_var_membership]
QED

Theorem alloca_suffix_membership_eqs[local]:
  !es needle k a. k <= a.cs_next_var ==>
  alloca_suffix k a (SND (emit_membership_eqs needle es a))
Proof
  Induct >> rpt strip_tac >>
  fs[emit_membership_eqs_def, alloca_suffix_return] >>
  irule alloca_suffix_bind_floor >> fs[alloca_suffix_emit_op] >>
  rpt strip_tac >> irule alloca_suffix_bind_floor >>
  fs[alloca_suffix_return]
QED

Theorem alloca_suffix_fold_membership_or[local]:
  !cs acc k a. k <= a.cs_next_var ==>
  alloca_suffix k a (SND (fold_membership_or acc cs a))
Proof
  Induct >> rpt strip_tac >>
  fs[fold_membership_or_def, alloca_suffix_return] >>
  irule alloca_suffix_bind_floor >> fs[alloca_suffix_emit_op]
QED

Theorem alloca_suffix_membership_in[local]:
  !needle es k a. k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_list_membership_in needle es a))
Proof
  rpt strip_tac >> simp[compile_list_membership_in_def] >>
  irule alloca_suffix_bind_floor >>
  fs[alloca_suffix_membership_eqs] >>
  rpt strip_tac >> Cases_on `v` >>
  fs[alloca_suffix_return, alloca_suffix_fold_membership_or]
QED

Theorem alloca_suffix_fold_membership_and[local]:
  !cs acc k a. k <= a.cs_next_var ==>
  alloca_suffix k a (SND (fold_membership_and acc cs a))
Proof
  Induct >> rpt strip_tac >>
  fs[fold_membership_and_def, alloca_suffix_return] >>
  irule alloca_suffix_bind_floor >> fs[alloca_suffix_emit_op] >>
  rpt strip_tac >> irule alloca_suffix_bind_floor >>
  fs[alloca_suffix_emit_op]
QED

Theorem alloca_suffix_membership_notin[local]:
  !needle es k a. k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_list_membership_notin needle es a))
Proof
  rpt strip_tac >> simp[compile_list_membership_notin_def] >>
  irule alloca_suffix_bind_floor >>
  fs[alloca_suffix_membership_eqs] >>
  rpt strip_tac >> Cases_on `v` >>
  fs[alloca_suffix_return] >>
  irule alloca_suffix_bind_floor >>
  fs[alloca_suffix_emit_op, alloca_suffix_fold_membership_and]
QED

Theorem alloca_suffix_membership_list_callback[local]:
  (!ce ty e a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (cfn ce ty e a))) /\
  k <= a.cs_next_var ==>
  alloca_suffix k a
    (SND ((\(ops,b). if is_in then
      as_stack_val rt (compile_list_membership_in needle ops b) else
      as_stack_val rt (compile_list_membership_notin needle ops b))
      (compile_multi_exprs cfn ce es a)))
Proof
  strip_tac >> ho_match_mp_tac alloca_suffix_pair_bind_floor >>
  simp[alloca_suffix_multi_exprs_floor] >> rpt strip_tac >>
  IF_CASES_TAC >> simp[exprBopLoweringTheory.as_stack_val_pair,
    alloca_suffix_membership_in, alloca_suffix_membership_notin]
QED

Theorem alloca_suffix_builtin_bop[local]:
  (!ce ty e a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (cfn ce ty e a))) /\
  k <= a.cs_next_var ==>
  alloca_suffix k a
    (SND (compile_builtin_dispatch_body cfn ce rt ty (Bop bop) es a))
Proof
  strip_tac >> simp[compile_builtin_dispatch_body_def] >>
  rpt IF_CASES_TAC >>
  rpt (ho_match_mp_tac alloca_suffix_pair_bind_floor >>
       simp[alloca_suffix_lower_value, alloca_suffix_bytestring_hash,
            alloca_suffix_emit_op, alloca_suffix_binop] >> rpt strip_tac)
  >- (rename1 `alloca_suffix k mid (SND _)` >>
      ho_match_mp_tac (BETA_RULE (Q.ISPEC `\p. alloca_suffix k mid (SND p)`
               intcall_make_array_case_pred)) >>
      conj_tac
      >- (irule alloca_suffix_membership_callback >> simp[]) >>
      rpt strip_tac >> irule alloca_suffix_membership_list_callback >> simp[]) >>
  simp[exprBopLoweringTheory.as_stack_val_pair, alloca_suffix_binop,
       alloca_suffix_emit_op] >>
  TRY (BasicProvers.TOP_CASE_TAC >> simp[alloca_suffix_refl] >>
       rpt (ho_match_mp_tac alloca_suffix_pair_bind_floor >>
            simp[alloca_suffix_lower_value, alloca_suffix_bytestring_hash] >>
            rpt strip_tac) >> NO_TAC) >>
  IF_CASES_TAC >> simp[alloca_suffix_emit_op] >>
  ho_match_mp_tac alloca_suffix_pair_bind_floor >>
  simp[alloca_suffix_emit_op]
QED

Theorem alloca_suffix_bytestring_src[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_bytestring_src p a))
Proof
  strip_tac >> simp[compile_bytestring_src_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_op, alloca_suffix_return])
QED

Theorem alloca_suffix_slice_out_buf[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_slice_out_buf sz a))
Proof
  strip_tac >> simp[compile_slice_out_buf_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_alloc_buffer, alloca_suffix_emit_op,
            alloca_suffix_return])
QED

Theorem alloca_suffix_assert_slice_bounds[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_assert_slice_bounds x n len a))
Proof
  strip_tac >> simp[compile_assert_slice_bounds_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_op, alloca_suffix_emit_void])
QED

Theorem alloca_suffix_slice_calldata[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_slice_calldata x n sz a))
Proof
  strip_tac >> simp[compile_slice_calldata_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_slice_out_buf, alloca_suffix_assert_slice_bounds,
            alloca_suffix_emit_op, alloca_suffix_emit_void,
            alloca_suffix_return, pairTheory.FORALL_PROD])
QED

Theorem alloca_suffix_slice_code[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_slice_code x n sz a))
Proof
  strip_tac >> simp[compile_slice_code_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_slice_out_buf, alloca_suffix_assert_slice_bounds,
            alloca_suffix_emit_op, alloca_suffix_emit_void,
            alloca_suffix_return, pairTheory.FORALL_PROD])
QED

Theorem alloca_suffix_slice_extcode[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_slice_extcode addr x n sz a))
Proof
  strip_tac >> simp[compile_slice_extcode_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_slice_out_buf, alloca_suffix_assert_slice_bounds,
            alloca_suffix_emit_op, alloca_suffix_emit_void,
            alloca_suffix_return, pairTheory.FORALL_PROD])
QED

Theorem alloca_suffix_slice_data[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_slice_data len p x n sz a))
Proof
  strip_tac >> simp[compile_slice_data_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_assert_slice_bounds, alloca_suffix_alloc_buffer,
            alloca_suffix_emit_op, alloca_suffix_emit_void,
            alloca_suffix_return])
QED

Theorem alloca_suffix_builtin_slice[local]:
  (!ce ty e a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (cfn ce ty e a))) /\
  k <= a.cs_next_var ==>
  alloca_suffix k a
    (SND (compile_builtin_dispatch_body cfn ce rt ty (Slice n) es a))
Proof
  strip_tac >> simp[compile_builtin_dispatch_body_def] >>
  rpt IF_CASES_TAC >>
  pure_rewrite_tac[oneline as_ptr_val_def, pairTheory.pair_CASE_UNCURRY,
                   combinTheory.C_DEF] >>
  rpt (ho_match_mp_tac alloca_suffix_pair_bind_floor >>
       simp[alloca_suffix_lower_value, alloca_suffix_bytestring_src,
            alloca_suffix_slice_calldata, alloca_suffix_slice_code,
            alloca_suffix_slice_extcode, alloca_suffix_slice_data,
            alloca_suffix_slice_out_buf, alloca_suffix_alloc_buffer,
            alloca_suffix_emit_void, pairTheory.FORALL_PROD,
            alloca_suffix_refl] >> rpt strip_tac) >>
  simp[alloca_suffix_slice_calldata, alloca_suffix_slice_code,
       alloca_suffix_slice_extcode, alloca_suffix_slice_data,
       alloca_suffix_refl] >>
  IF_CASES_TAC >>
  rpt (ho_match_mp_tac alloca_suffix_pair_bind_floor >>
       simp[alloca_suffix_lower_value, alloca_suffix_bytestring_src,
            alloca_suffix_alloc_buffer, alloca_suffix_emit_void,
            pairTheory.FORALL_PROD] >> rpt strip_tac) >>
  simp[alloca_suffix_slice_data, alloca_suffix_refl]
QED

Theorem alloca_suffix_keccak256_bytes[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_keccak256_bytes p a))
Proof
  strip_tac >> simp[compile_keccak256_bytes_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_op])
QED

Theorem alloca_suffix_sha256_bytes[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_sha256_bytes p a))
Proof
  strip_tac >> simp[compile_sha256_bytes_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_alloc_buffer, alloca_suffix_return,
            alloca_suffix_emit_void, alloca_suffix_emit_op])
QED

Theorem intcall_fixed_bytes_case_pred[local]:
  !P ordinary special ty.
    P ordinary /\ (!m. P (special m)) ==>
    P (case ty of BaseT (BytesT (Fixed m)) => special m | _ => ordinary)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `ty` >> simp[] >>
  TOP_CASE_TAC >> simp[] >> TOP_CASE_TAC >> simp[]
QED

Theorem alloca_suffix_keccak256_word[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_keccak256_word v a))
Proof
  strip_tac >> simp[compile_keccak256_word_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_alloc_buffer, alloca_suffix_return,
            alloca_suffix_emit_void, alloca_suffix_emit_op])
QED

Theorem alloca_suffix_keccak256_bytesm[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_keccak256_bytesm v m a))
Proof
  strip_tac >> simp[compile_keccak256_bytesm_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_alloc_buffer, alloca_suffix_return,
            alloca_suffix_emit_void, alloca_suffix_emit_op])
QED

Theorem alloca_suffix_sha256_word[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_sha256_word v a))
Proof
  strip_tac >> simp[compile_sha256_word_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_alloc_buffer, alloca_suffix_return,
            alloca_suffix_emit_void, alloca_suffix_emit_op])
QED

Theorem alloca_suffix_sha256_bytesm[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_sha256_bytesm v m a))
Proof
  strip_tac >> simp[compile_sha256_bytesm_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_alloc_buffer, alloca_suffix_return,
            alloca_suffix_emit_void, alloca_suffix_emit_op])
QED

Theorem alloca_suffix_builtin_hash[local]:
  (!ce ty e a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (cfn ce ty e a))) /\
  (bi = Keccak256 \/ bi = Sha256) /\ k <= a.cs_next_var ==>
  alloca_suffix k a
    (SND (compile_builtin_dispatch_body cfn ce rt ty bi es a))
Proof
  strip_tac >> gvs[compile_builtin_dispatch_body_def] >>
  (IF_CASES_TAC
   >- (simp[exprBopLoweringTheory.as_stack_val_pair] >>
       ho_match_mp_tac alloca_suffix_pair_bind_floor >>
       simp[alloca_suffix_lower_value, alloca_suffix_keccak256_bytes,
            alloca_suffix_sha256_bytes])) >>
  ho_match_mp_tac (BETA_RULE (Q.ISPEC
    `\p. alloca_suffix k a (SND p)`
    intcall_fixed_bytes_case_pred)) >> conj_tac >> rpt gen_tac >>
  simp[exprBopLoweringTheory.as_stack_val_pair] >>
  ho_match_mp_tac alloca_suffix_pair_bind_floor >>
  simp[alloca_suffix_lower_value, alloca_suffix_keccak256_bytes,
       alloca_suffix_keccak256_word, alloca_suffix_keccak256_bytesm,
       alloca_suffix_sha256_bytes, alloca_suffix_sha256_word,
       alloca_suffix_sha256_bytesm]
QED

Theorem alloca_suffix_concat_all[local]:
  (!ce ty e a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (cfn ce ty e a))) ==>
  !es dp infos off a. k <= a.cs_next_var ==>
    alloca_suffix k a
      (SND (compile_concat cfn cenv es dp infos off a))
Proof
  strip_tac >> Induct >> simp[compile_concat_def, alloca_suffix_return] >>
  rpt gen_tac >> Cases_on `infos` >>
  simp[compile_concat_def, alloca_suffix_return] >>
  rename1 `compile_concat cfn cenv _ _ (info::infos') _` >>
  PairCases_on `info` >>
  rpt strip_tac >> simp[compile_concat_def, comp_ignore_bind_def] >>
  IF_CASES_TAC >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_op, alloca_suffix_emit_void,
            alloca_suffix_lower_value])
QED

Theorem alloca_suffix_acc_all[local]:
  (!ce ty e a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (cfn ce ty e a))) /\
  k <= a.cs_next_var ==>
  alloca_suffix k a
    (SND (compile_acc cfn cenv e ak a))
Proof
  strip_tac >> Cases_on `ak` >> Cases_on `is_self_addr e` >>
  simp[compile_acc_def, alloca_suffix_lower_value,
       alloca_suffix_emit_inst] >>
  TRY (rpt (irule alloca_suffix_pair_bind_floor >>
            simp[alloca_suffix_emit_op, alloca_suffix_lower_value] >>
            rpt strip_tac >> simp[alloca_suffix_refl,
                                  alloca_suffix_emit_inst])) >>
  simp[alloca_suffix_emit_op]
QED

Theorem alloca_suffix_env_var[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_env_var ev a))
Proof
  strip_tac >> Cases_on `ev` >>
  simp[compile_env_var_def, alloca_suffix_emit_op] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_op])
QED

Theorem alloca_suffix_neg[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_neg v ty a))
Proof
  strip_tac >> Cases_on `type_bounds ty` >>
  simp[compile_neg_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_op, alloca_suffix_emit_void])
QED

Theorem alloca_suffix_abs[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_builtin_abs v a))
Proof
  strip_tac >> simp[compile_builtin_abs_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_op, alloca_suffix_emit_void,
            alloca_suffix_select])
QED

Theorem alloca_suffix_builtin_calldatasize[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_builtin_calldatasize a))
Proof
  simp[compile_builtin_calldatasize_def, alloca_suffix_emit_op]
QED

Theorem alloca_suffix_builtin_len[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_builtin_len ctor imm p loc a))
Proof
  simp[compile_builtin_len_def, alloca_suffix_ptr_load]
QED

Theorem alloca_suffix_blockhash[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_blockhash n a))
Proof
  strip_tac >> simp[compile_blockhash_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_op, alloca_suffix_emit_void])
QED

Theorem alloca_suffix_blobhash[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_blobhash n a))
Proof
  simp[compile_blobhash_def, alloca_suffix_emit_op]
QED

Theorem alloca_suffix_ceil[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_ceil v dv a))
Proof
  strip_tac >> simp[compile_ceil_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_op, alloca_suffix_select])
QED

Theorem alloca_suffix_floor[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_floor v dv a))
Proof
  strip_tac >> simp[compile_floor_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_op, alloca_suffix_select])
QED

Theorem alloca_suffix_ecrecover[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_ecrecover h v r s a))
Proof
  strip_tac >> simp[compile_ecrecover_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_alloc_buffer, alloca_suffix_return,
            alloca_suffix_emit_void, alloca_suffix_emit_op])
QED

Theorem alloca_suffix_ecadd_points[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_ecadd_points p q a))
Proof
  strip_tac >> simp[compile_ecadd_points_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_alloc_buffer, alloca_suffix_return,
            alloca_suffix_emit_void, alloca_suffix_emit_op])
QED

Theorem alloca_suffix_ecmul_point[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_ecmul_point p s a))
Proof
  strip_tac >> simp[compile_ecmul_point_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_alloc_buffer, alloca_suffix_return,
            alloca_suffix_emit_void, alloca_suffix_emit_op])
QED

Theorem alloca_suffix_uint2str[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_uint2str v digits sz a))
Proof
  strip_tac >> simp[compile_uint2str_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_alloc_buffer, alloca_suffix_return,
            alloca_suffix_emit_op, alloca_suffix_emit_void,
            alloca_suffix_emit_inst, alloca_suffix_fresh_var,
            alloca_suffix_fresh_label, alloca_suffix_new_block])
QED

Theorem alloca_suffix_invert[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_invert v ty cenv a))
Proof
  Cases_on `ty` >> simp[compile_invert_def, alloca_suffix_emit_op]
QED

Theorem alloca_suffix_wei_int[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_as_wei_value_int v scale sg a))
Proof
  strip_tac >> Cases_on `scale = 1` >> Cases_on `sg` >>
  simp[compile_as_wei_value_int_def, comp_ignore_bind_def, alloca_suffix_return] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_op, alloca_suffix_emit_void,
            alloca_suffix_return])
QED

Theorem alloca_suffix_wei_decimal[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_as_wei_value_decimal v scale dv a))
Proof
  strip_tac >> Cases_on `scale = 1` >>
  simp[compile_as_wei_value_decimal_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_op, alloca_suffix_emit_void])
QED

Theorem alloca_suffix_make_tuple_all[local]:
  (!ce ty e a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (cfn ce ty e a))) ==>
  !es tys buf off a. k <= a.cs_next_var ==>
    alloca_suffix k a
      (SND (compile_make_tuple cfn cenv es tys buf off a))
Proof
  strip_tac >> Induct >> simp[compile_make_tuple_def, alloca_suffix_return] >>
  rpt strip_tac >> Cases_on `tys` >>
  simp[compile_make_tuple_def, alloca_suffix_return] >>
  rewrite_tac[comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_op, alloca_suffix_unwrap_value,
            alloca_suffix_store_memory, alloca_suffix_return])
QED

Theorem alloca_suffix_make_array_elems_all[local]:
  (!ce ty e a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (cfn ce ty e a))) ==>
  !es et sz hl buf idx a. k <= a.cs_next_var ==>
    alloca_suffix k a
      (SND (compile_make_array_elems cfn cenv es et sz hl buf idx a))
Proof
  strip_tac >> Induct >> simp[compile_make_array_elems_def, alloca_suffix_return] >>
  rpt strip_tac >> rewrite_tac[comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_op, alloca_suffix_unwrap_value,
            alloca_suffix_store_memory, alloca_suffix_return])
QED

Theorem alloca_suffix_make_array_all[local]:
  (!ce ty e a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (cfn ce ty e a))) /\
  k <= a.cs_next_var ==>
  alloca_suffix k a
    (SND (compile_make_array cfn cenv es et sz hl buf a))
Proof
  strip_tac >> Cases_on `hl` >>
  simp[compile_make_array_def, comp_ignore_bind_def] >>
  irule alloca_suffix_bind_floor >>
  simp[alloca_suffix_emit_void, alloca_suffix_return,
       alloca_suffix_make_array_elems_all]
QED

Theorem alloca_suffix_method_id_hash[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_method_id_hash ty v a))
Proof
  Cases_on `ty` >> simp[compile_method_id_hash_def,
    alloca_suffix_keccak256_bytes] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[compile_method_id_hash_def, alloca_suffix_keccak256_bytes] >>
  rename1 `BytesT bnd` >> Cases_on `bnd` >>
  simp[compile_method_id_hash_def, alloca_suffix_keccak256_bytes,
       alloca_suffix_keccak256_bytesm]
QED

Theorem alloca_suffix_method_id_runtime[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_method_id_runtime ty v b a))
Proof
  strip_tac >> Cases_on `b` >>
  simp[compile_method_id_runtime_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_method_id_hash, alloca_suffix_alloc_buffer,
            alloca_suffix_return, alloca_suffix_emit_void,
            alloca_suffix_emit_op])
QED

Theorem alloca_suffix_builtin_body[local]:
  (!ce ty e a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (cfn ce ty e a))) ==>
  !ce rt ty bi es a. k <= a.cs_next_var ==>
    alloca_suffix k a
      (SND (compile_builtin_dispatch_body cfn ce rt ty bi es a))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >> Cases_on `bi` >>
  simp[alloca_suffix_builtin_bop, alloca_suffix_builtin_slice,
       alloca_suffix_builtin_hash] >>
  simp[compile_builtin_dispatch_body_def,
       exprBopLoweringTheory.as_stack_val_pair] >>
  pure_rewrite_tac[oneline as_ptr_val_def, pairTheory.pair_CASE_UNCURRY,
                   combinTheory.C_DEF] >>
  rpt (ho_match_mp_tac alloca_suffix_pair_bind_floor >>
       simp[alloca_suffix_lower_value, alloca_suffix_unwrap_value,
            alloca_suffix_alloc_buffer, alloca_suffix_emit_op,
            alloca_suffix_emit_void, alloca_suffix_concat_all,
            alloca_suffix_acc_all, alloca_suffix_env_var,
            alloca_suffix_neg, alloca_suffix_abs,
            alloca_suffix_builtin_calldatasize, alloca_suffix_builtin_len,
            alloca_suffix_slice_calldata, alloca_suffix_blockhash,
            alloca_suffix_blobhash, alloca_suffix_addmod,
            alloca_suffix_mulmod, alloca_suffix_ceil, alloca_suffix_floor,
            alloca_suffix_pow_mod256, alloca_suffix_ecrecover,
            alloca_suffix_ecadd_points, alloca_suffix_ecmul_point,
            alloca_suffix_uint2str, pairTheory.FORALL_PROD] >> rpt strip_tac) >>
  simp[alloca_suffix_builtin_calldatasize, alloca_suffix_refl]
  >- (IF_CASES_TAC >> simp[alloca_suffix_emit_op, alloca_suffix_invert])
  >- (IF_CASES_TAC >> simp[alloca_suffix_wei_int, alloca_suffix_wei_decimal])
  >- (TOP_CASE_TAC >> simp[] >>
      ho_match_mp_tac alloca_suffix_pair_bind_floor >>
      simp[alloca_suffix_alloc_buffer] >> rpt strip_tac >>
      simp[pairTheory.ELIM_UNCURRY, alloca_suffix_make_tuple_all,
           alloca_suffix_make_array_all]) >>
  simp[alloca_suffix_env_var, alloca_suffix_acc_all] >>
  Cases_on `method_id_literal (HD es)` >> simp[alloca_suffix_literal_vv] >>
  ho_match_mp_tac alloca_suffix_pair_bind_floor >>
  simp[alloca_suffix_lower_value] >> rpt strip_tac >>
  IF_CASES_TAC >> simp[pairTheory.ELIM_UNCURRY, alloca_suffix_method_id_runtime]
QED

Theorem alloca_suffix_bytestring_widen_copy[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_bytestring_widen_copy dst v src a))
Proof
  strip_tac >> simp[compile_bytestring_widen_copy_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_alloc_buffer, alloca_suffix_copy_memory,
            alloca_suffix_return])
QED

Theorem alloca_suffix_int_clamp[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_int_clamp sg bits v a))
Proof
  strip_tac >> Cases_on `sg` >>
  simp[compile_int_clamp_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_op, alloca_suffix_emit_void,
            alloca_suffix_return])
QED

Theorem alloca_suffix_load_bytestring_as_word[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (load_bytestring_as_word v opc a))
Proof
  strip_tac >> Cases_on `opc = SAR` >>
  simp[load_bytestring_as_word_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_op, alloca_suffix_return])
QED

Theorem alloca_suffix_type_convert[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_type_convert v cv a))
Proof
  strip_tac >> Cases_on `cv` >>
  simp[compile_type_convert_def, comp_ignore_bind_def,
       alloca_suffix_emit_op, alloca_suffix_return] >>
  rpt IF_CASES_TAC >> simp[] >>
  rpt (simp[pairTheory.FORALL_PROD] >> rpt strip_tac >> simp[pairTheory.FORALL_PROD,
            alloca_suffix_emit_op, alloca_suffix_emit_void,
            alloca_suffix_return, alloca_suffix_int_clamp,
            alloca_suffix_load_bytestring_as_word] >>
       rpt IF_CASES_TAC >>
       simp[alloca_suffix_emit_op, alloca_suffix_emit_void,
            alloca_suffix_return, alloca_suffix_int_clamp,
            alloca_suffix_load_bytestring_as_word] >>
       irule alloca_suffix_bind_floor)
QED

Theorem alloca_suffix_type_convert_branch[local]:
  (!ce ty e a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (cfn ce ty e a))) /\
  k <= a.cs_next_var ==>
  alloca_suffix k a
    (SND (compile_type_builtin_dispatch_body cfn ce vt ty Convert rt es a))
Proof
  strip_tac >> simp[compile_type_builtin_dispatch_body_def] >>
  ho_match_mp_tac alloca_suffix_pair_bind_floor >>
  simp[alloca_suffix_lower_value] >> rpt strip_tac >>
  rpt IF_CASES_TAC >> Cases_on `rt` >>
  simp[alloca_suffix_refl, exprBopLoweringTheory.as_ptr_val_pair,
       exprBopLoweringTheory.as_stack_val_pair,
       alloca_suffix_bytestring_widen_copy, alloca_suffix_type_convert]
QED

Theorem alloca_suffix_extract32_load[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_extract32_load len p x a))
Proof
  strip_tac >> simp[compile_extract32_load_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_assert_slice_bounds, alloca_suffix_emit_op])
QED

Theorem alloca_suffix_clamp_basetype[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_clamp_basetype v ty a))
Proof
  strip_tac >> Cases_on `ty` >>
  simp[compile_clamp_basetype_def, alloca_suffix_return] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[compile_clamp_basetype_def, alloca_suffix_return] >>
  rpt IF_CASES_TAC >>
  simp[compile_clamp_basetype_def, alloca_suffix_clamp_return,
       alloca_suffix_return, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_op, alloca_suffix_emit_void,
            alloca_suffix_return]) >>
  rename1 `BytesT bnd` >> Cases_on `bnd` >>
  simp[compile_clamp_basetype_def, alloca_suffix_return, comp_ignore_bind_def] >>
  rpt IF_CASES_TAC >> simp[alloca_suffix_return] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_op, alloca_suffix_emit_void,
            alloca_suffix_return])
QED

Theorem alloca_suffix_type_extract_branch[local]:
  (!ce ty e a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (cfn ce ty e a))) /\
  k <= a.cs_next_var ==>
  alloca_suffix k a
    (SND (compile_type_builtin_dispatch_body cfn ce vt ty Extract32 rt es a))
Proof
  strip_tac >> simp[compile_type_builtin_dispatch_body_def] >>
  rpt (ho_match_mp_tac alloca_suffix_pair_bind_floor >>
       simp[alloca_suffix_lower_value, alloca_suffix_bytestring_src,
            alloca_suffix_extract32_load, alloca_suffix_clamp_basetype,
            exprBopLoweringTheory.as_stack_val_pair, pairTheory.FORALL_PROD] >>
       rpt strip_tac) >>
  simp[alloca_suffix_lower_value, alloca_suffix_bytestring_src,
       alloca_suffix_extract32_load, alloca_suffix_clamp_basetype]
QED

Theorem alloca_suffix_abi_encode_args_all[local]:
  (!ce ty e a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (cfn ce ty e a))) ==>
  !es a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (compile_abi_encode_args cfn cenv es a))
Proof
  simp[compile_abi_encode_args_def, alloca_suffix_ext_call_args]
QED

Theorem alloca_suffix_abi_encode_payload[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_abi_encode_payload cenv single vs tys dst a))
Proof
  strip_tac >> Cases_on `single` >>
  simp[compile_abi_encode_payload_def, alloca_suffix_abi_encode_values] >>
  irule alloca_suffix_bind_floor >> simp[alloca_suffix_unwrap_value] >>
  gen_tac >> Cases_on `is_word_type (HD tys)` >>
  simp[alloca_suffix_abi_encode_values, cj 2 alloca_suffix_encode_family,
       comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_void, alloca_suffix_return])
QED

Theorem alloca_suffix_lower_abi_encode[local]:
  (!dst a. k <= a.cs_next_var ==> alloca_suffix k a (SND (encode dst a))) /\
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (lower_abi_encode mid maxlen encode a))
Proof
  strip_tac >> Cases_on `mid` >>
  simp[lower_abi_encode_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_alloc_buffer, alloca_suffix_return,
            alloca_suffix_emit_op, alloca_suffix_emit_void])
QED

Theorem alloca_suffix_type_encode_branch[local]:
  (!ce ty e a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (cfn ce ty e a))) /\
  k <= a.cs_next_var ==>
  alloca_suffix k a
    (SND (compile_type_builtin_dispatch_body cfn ce vt ty (AbiEncode ensure mid) rt es a))
Proof
  strip_tac >> simp[compile_type_builtin_dispatch_body_def] >>
  pure_rewrite_tac[oneline as_ptr_val_def, pairTheory.pair_CASE_UNCURRY,
                   combinTheory.C_DEF] >>
  rpt (ho_match_mp_tac alloca_suffix_pair_bind_floor >>
       simp[alloca_suffix_abi_encode_args_all, alloca_suffix_abi_encode_payload,
            alloca_suffix_lower_abi_encode, alloca_suffix_refl] >>
       rpt strip_tac) >>
  simp[alloca_suffix_abi_encode_args_all, alloca_suffix_abi_encode_payload,
       alloca_suffix_lower_abi_encode, alloca_suffix_refl]
QED

Theorem alloca_suffix_lower_abi_decode[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a
    (SND (lower_abi_decode data info lo hi sz a))
Proof
  strip_tac >> Cases_on `lo = hi` >>
  simp[lower_abi_decode_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_alloc_buffer, alloca_suffix_return,
            alloca_suffix_emit_op, alloca_suffix_emit_void,
            cj 1 alloca_suffix_decode_family])
QED

Theorem alloca_suffix_type_decode_branch[local]:
  (!ce ty e a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (cfn ce ty e a))) /\
  k <= a.cs_next_var ==>
  alloca_suffix k a
    (SND (compile_type_builtin_dispatch_body cfn ce vt ty (AbiDecode uw) rt es a))
Proof
  strip_tac >> simp[compile_type_builtin_dispatch_body_def] >>
  pure_rewrite_tac[oneline as_ptr_val_def, pairTheory.pair_CASE_UNCURRY,
                   combinTheory.C_DEF] >>
  rpt (ho_match_mp_tac alloca_suffix_pair_bind_floor >>
       simp[alloca_suffix_unwrap_value, alloca_suffix_lower_abi_decode,
            alloca_suffix_refl] >> rpt strip_tac) >>
  simp[alloca_suffix_refl]
QED

Theorem alloca_suffix_zero_words[local]:
  !n p k a. k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_zero_words p n a))
Proof
  Induct >> simp[compile_zero_words_def, alloca_suffix_return,
                comp_ignore_bind_def] >> rpt strip_tac >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_emit_op, alloca_suffix_emit_void])
QED

Theorem alloca_suffix_builtin_empty_complex[local]:
  k <= a.cs_next_var ==>
  alloca_suffix k a (SND (compile_builtin_empty_complex sz bs a))
Proof
  strip_tac >> Cases_on `bs` >>
  simp[compile_builtin_empty_complex_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule alloca_suffix_bind_floor >>
       simp[alloca_suffix_alloc_buffer, alloca_suffix_return,
            alloca_suffix_zero_words, alloca_suffix_emit_void])
QED

Theorem alloca_suffix_type_builtin_body[local]:
  (!ce ty e a. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (cfn ce ty e a))) ==>
  !ce vt ty tb rt es a. k <= a.cs_next_var ==>
    alloca_suffix k a
      (SND (compile_type_builtin_dispatch_body cfn ce vt ty tb rt es a))
Proof
  strip_tac >> rpt gen_tac >> Cases_on `tb` >>
  simp[alloca_suffix_type_convert_branch, alloca_suffix_type_extract_branch,
       alloca_suffix_type_encode_branch, alloca_suffix_type_decode_branch] >>
  simp[compile_type_builtin_dispatch_body_def, alloca_suffix_refl] >>
  strip_tac >> rpt IF_CASES_TAC >>
  simp[pairTheory.ELIM_UNCURRY, alloca_suffix_builtin_empty_complex,
       alloca_suffix_refl]
QED

Theorem alloca_suffix_compile_size[local]:
  !n.
    (!ce ty e a k. expr_size e + cenv_defaults_size ce = n /\
      k <= a.cs_next_var ==>
      alloca_suffix k a (SND (compile_expr ce ty e a))) /\
    (!ce rt ty bi es a k. list_size expr_size es + cenv_defaults_size ce = n /\
      k <= a.cs_next_var ==>
      alloca_suffix k a
        (SND (compile_builtin_dispatch ce rt ty bi es a))) /\
    (!ce vt ty tb rt es a k. list_size expr_size es + cenv_defaults_size ce = n /\
      k <= a.cs_next_var ==>
      alloca_suffix k a
        (SND (compile_type_builtin_dispatch ce vt ty tb rt es a)))
Proof
  completeInduct_on `n` >> conj_tac
  >- (rpt strip_tac >> once_rewrite_tac[compile_expr_raw_def] >>
      irule alloca_suffix_expr_body >> simp[Excl "expr_child_callback_def", Excl "builtin_child_callback_def",
           Excl "type_child_callback_def"] >> rpt conj_tac
      >- simp[alloca_suffix_expr_callback_all]
      >- simp[alloca_suffix_builtin_callback_all] >>
      simp[alloca_suffix_type_callback_all]) >>
  conj_tac
  >- (rpt strip_tac >> once_rewrite_tac[compile_expr_raw_def] >>
      irule alloca_suffix_builtin_body >> simp[Excl "expr_child_callback_def", Excl "builtin_child_callback_def",
           Excl "type_child_callback_def"] >>
      simp[alloca_suffix_expr_callback_all]) >>
  rpt strip_tac >> once_rewrite_tac[compile_expr_raw_def] >> simp[Excl "expr_child_callback_def", Excl "builtin_child_callback_def",
           Excl "type_child_callback_def"] >>
  irule alloca_suffix_type_builtin_body >> simp[Excl "expr_child_callback_def", Excl "builtin_child_callback_def",
           Excl "type_child_callback_def"] >>
  simp[alloca_suffix_expr_callback_all]
QED

Theorem alloca_suffix_compile_expr[local]:
  !ce ty e a k. k <= a.cs_next_var ==>
    alloca_suffix k a (SND (compile_expr ce ty e a))
Proof
  metis_tac[alloca_suffix_compile_size]
QED

Theorem compile_expr_alloca_fresh:
  compile_expr cenv ty expr sa = (value,sm) ==>
  ci_mono sa sm /\
  (!id. id IN frag_ids sa sm ==>
    ?inst. MEM inst (added_insts sa sm) /\ inst.inst_id = id) /\
  EVERY (\inst. inst.inst_opcode = ALLOCA ==>
    inst.inst_id IN frag_ids sa sm /\
    !p. MEM p inst.inst_outputs ==> ~not_fresh_at sa p)
    (added_insts sa sm)
Proof
  strip_tac >>
  qspecl_then [`cenv`,`ty`,`expr`,`sa`,`sa.cs_next_var`] mp_tac
    alloca_suffix_compile_expr >>
  simp[alloca_suffix_def] >> strip_tac >>
  fs[EVERY_MEM, not_fresh_at_def] >>
  metis_tac[]
QED

Theorem lower_value_alloca_ids:
  ci_mono sa (SND (lower_value compile_expr ce ty e sa)) /\
  EVERY (\i. i.inst_opcode = ALLOCA ==>
    i.inst_id < (SND (lower_value compile_expr ce ty e sa)).cs_next_id)
    (added_insts sa (SND (lower_value compile_expr ce ty e sa)))
Proof
  `alloca_suffix sa.cs_next_var sa (SND (lower_value compile_expr ce ty e sa))` by
    (irule alloca_suffix_lower_value >> simp[alloca_suffix_compile_expr]) >>
  fs[alloca_suffix_def, EVERY_MEM, frag_ids_def] >> metis_tac[]
QED

Theorem store_bytestring_alloca_ids:
  ci_mono sa (SND (compile_store_bytestring src dst sa)) /\
  EVERY (\i. i.inst_opcode = ALLOCA ==>
    i.inst_id < (SND (compile_store_bytestring src dst sa)).cs_next_id)
    (added_insts sa (SND (compile_store_bytestring src dst sa)))
Proof
  `alloca_suffix sa.cs_next_var sa (SND (compile_store_bytestring src dst sa))` by
    simp[alloca_suffix_store_bytestring] >>
  fs[alloca_suffix_def, EVERY_MEM, frag_ids_def] >> metis_tac[]
QED

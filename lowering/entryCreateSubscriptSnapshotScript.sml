(* The copied base only allocates, unwraps and stores at the same type. *)
Theory entryCreateSubscriptSnapshot
Ancestors
  createSizeConcreteSnapshots entryCreateEffectFocus compilerInstructionSuffix
  exprSimAbiGasBridge exprLoweringProps exprLowering loweringShapeDefs
  context emitHelper compileEnv fragExec list rich_list pair venomInst bodySim

Definition snapshot_admin_def:
  snapshot_admin i <=> ~MEM i.inst_opcode [INVOKE; CREATE; CREATE2]
End

Definition snapshot_admin_compile_def:
  snapshot_admin_compile m <=> !s.
    ci_mono s (SND (m s)) /\ EVERY snapshot_admin (added_insts s (SND (m s)))
End

Theorem snapshot_admin_bind[local]:
  snapshot_admin_compile m /\ (!v. snapshot_admin_compile (k v)) ==>
  snapshot_admin_compile (comp_bind m k)
Proof
  simp[snapshot_admin_compile_def] >> strip_tac >>
  irule added_insts_bind_every >> simp[]
QED

Theorem snapshot_admin_ignore[local]:
  snapshot_admin_compile m /\ snapshot_admin_compile k ==>
  snapshot_admin_compile (comp_ignore_bind m k)
Proof
  simp[snapshot_admin_compile_def] >> strip_tac >>
  irule added_insts_ignore_every >> simp[]
QED

Theorem snapshot_admin_primitives[local,simp]:
  (~MEM opc [INVOKE; CREATE; CREATE2] ==> snapshot_admin_compile (emit_op opc ops)) /\
  (~MEM opc [INVOKE; CREATE; CREATE2] ==> snapshot_admin_compile (emit_inst opc ops outs)) /\
  (~MEM opc [INVOKE; CREATE; CREATE2] ==> snapshot_admin_compile (emit_void opc ops)) /\
  snapshot_admin_compile (compile_alloc_buffer n) /\
  snapshot_admin_compile (new_block l) /\
  snapshot_admin_compile (fresh_label tag) /\
  snapshot_admin_compile fresh_var /\
  snapshot_admin_compile (comp_return v)
Proof
  pure_rewrite_tac[snapshot_admin_compile_def] >> rpt conj_tac
  >- (strip_tac >> gen_tac >> Cases_on `emit_op opc ops s` >>
      drule added_insts_emit_op >> strip_tac >> fs[snapshot_admin_def,mk_inst_def])
  >- (strip_tac >> gen_tac >> Cases_on `emit_inst opc ops outs s` >>
      drule added_insts_emit_inst >> strip_tac >> fs[snapshot_admin_def,mk_inst_def])
  >- (strip_tac >> gen_tac >> Cases_on `emit_void opc ops s` >>
      drule added_insts_emit_void >> strip_tac >> fs[snapshot_admin_def,mk_inst_def])
  >- (gen_tac >> Cases_on `compile_alloc_buffer n s` >>
      drule added_insts_allocate >> strip_tac >> fs[snapshot_admin_def,mk_inst_def])
  >- (gen_tac >> Cases_on `new_block l s` >> drule added_insts_new_block >> simp[])
  >- (gen_tac >> Cases_on `fresh_label tag s` >> drule added_insts_fresh_label >> simp[])
  >- simp[ci_mono_fresh_var, fresh_var_def, added_insts_def,
          state_insts_def, all_blocks_def, DROP_APPEND, DROP_LENGTH_TOO_LONG] >>
  simp[added_insts_return_every]
QED

fun snapshot_steps defs =
  rpt (FIRST [CHANGED_TAC (simp defs), gen_tac,
              irule snapshot_admin_bind, irule snapshot_admin_ignore,
              conj_tac, IF_CASES_TAC]);

Theorem snapshot_admin_location_ops[local,simp]:
  snapshot_admin_compile (compile_imm_load_word ctor imm op) /\
  snapshot_admin_compile (compile_imm_store_word imm op v) /\
  snapshot_admin_compile (compile_lit_byte_offset op n)
Proof
  Cases_on `imm` >> Cases_on `ctor` >> Cases_on `op` >>
  snapshot_steps [compile_imm_load_word_def, compile_imm_store_word_def,
                  compile_lit_byte_offset_def]
QED

Theorem snapshot_admin_ptr_ops[local,simp]:
  snapshot_admin_compile (compile_ptr_load ctor imm loc op) /\
  snapshot_admin_compile (compile_ptr_store ctor imm loc op v)
Proof
  Cases_on `loc` >> Cases_on `ctor` >>
  snapshot_steps [compile_ptr_load_def, compile_ptr_store_def]
QED

Theorem snapshot_admin_word_loop[local,simp]:
  snapshot_admin_compile
    (compile_word_copy_loop_base src dst count_op ll sl ctor imm)
Proof
  snapshot_steps [compile_word_copy_loop_base_def, LET_DEF]
QED

Theorem snapshot_admin_imm_copy[local,simp]:
  !n off. snapshot_admin_compile (compile_imm_copy_to_memory ctor imm src dst n off)
Proof
  Induct >> snapshot_steps [compile_imm_copy_to_memory_def]
QED

Theorem snapshot_admin_ensure[local,simp]:
  snapshot_admin_compile (compile_ensure_in_memory op loc bytes n ctor imm)
Proof
  Cases_on `loc` >> snapshot_steps
    [compile_ensure_in_memory_def, LET_DEF, compile_storage_to_memory_def,
     compile_transient_to_memory_def, compile_word_copy_loop_def,
     compile_word_copy_loop_op_def]
QED

Theorem snapshot_admin_unwrap[local,simp]:
  snapshot_admin_compile (unwrap_value ce vv)
Proof
  Cases_on `vv` >> simp[unwrap_value_def] >>
  Cases_on `p.ptr_location` >> simp[] >> IF_CASES_TAC >> simp[]
QED

Theorem snapshot_admin_copy_memory[local,simp]:
  snapshot_admin_compile (compile_copy_memory dst src n)
Proof
  Cases_on `n` >> simp[compile_copy_memory_def]
QED

Theorem snapshot_admin_array[local]:
  vv_type vv = ArrayT et bd ==>
  snapshot_admin_compile (compile_snapshot_vv ce T vv)
Proof
  strip_tac >>
  snapshot_steps [compile_snapshot_vv_def, compile_materialize_vv_def,
                  is_word_type_def, is_bytestring_type_def, LET_DEF,
                  compile_store_memory_def, compile_copy_memory_def]
QED

Theorem snapshot_added_insts_cover[local]:
  cs_extends a b /\ MEM i (frag_code a b) ==> MEM i (added_insts a b)
Proof
  strip_tac >> qpat_x_assum `cs_extends a b` mp_tac >>
  simp[cs_extends_def, rich_listTheory.IS_PREFIX_APPEND] >> strip_tac >>
  `emitted_blocks a b = new` by metis_tac[emitted_blocks_append] >>
  Cases_on `new = []`
  >- gvs[frag_code_def, emitted_insts_def, added_insts_def,
         state_insts_def, all_blocks_def, DROP_APPEND, DROP_LENGTH_TOO_LONG] >>
  `REVERSE new = LAST new :: REVERSE (FRONT new)` by
    metis_tac[APPEND_FRONT_LAST, REVERSE_APPEND, REVERSE_DEF, APPEND] >>
  `?l. (LAST new).bb_instructions = a.cs_current_insts ++ l` by fs[] >>
  qpat_x_assum `MEM i (frag_code a b)` mp_tac >>
  simp[added_insts_def, state_insts_def, all_blocks_def, REVERSE_APPEND,
       FLAT_APPEND, MAP_APPEND, DROP_APPEND, DROP_LENGTH_TOO_LONG, NULL_EQ,
       frag_code_def, MEM_FLAT, MEM_MAP, MEM_REVERSE,
       DECIDE ``a - (b + a) = 0n``, DECIDE ``a - (b + (c + a)) = 0n``] >>
  simp[MEM_FLAT, MEM_MAP, MEM_REVERSE]
QED

Theorem subscript_snapshot_opcode_inventory:
  compile_snapshot_vv ce T bvv sm = (cvv,sc) /\ vv_type bvv = ArrayT et bd ==>
  create_cut_code {} sm sc /\ EVERY snapshot_admin (frag_code sm sc)
Proof
  strip_tac >> conj_tac
  >- (qpat_assum `compile_snapshot_vv _ _ _ _ = _`
        (fn th => mp_tac (Q.INST [`ce` |-> `ce`, `copy` |-> `T`,
                                 `a` |-> `sm`, `vv` |-> `bvv`]
           create_vv_snapshot_cut_code) >> simp[th])) >>
  drule snapshot_admin_array >> simp[snapshot_admin_compile_def] >>
  disch_then (qspecl_then [`ce`, `sm`] mp_tac) >> simp[] >>
  simp[EVERY_MEM, ci_mono_def] >> metis_tac[snapshot_added_insts_cover]
QED

Theorem subscript_snapshot_visit_inventory:
  compile_snapshot_vv ce T bvv sm = (cvv,sc) /\ vv_type bvv = ArrayT et bd /\
  body_inv tops ctx ce cx /\ MEM func ctx.ctx_functions /\
  fn_has_code sm sc func ==>
  create_operand_cut sm sc explicit ctx func tops cx st0 source (es,s)
Proof
  strip_tac >> drule_all subscript_snapshot_opcode_inventory >> strip_tac >>
  irule create_effect_suffix_cut >> fs[snapshot_admin_def, EVERY_MEM] >> metis_tac[]
QED

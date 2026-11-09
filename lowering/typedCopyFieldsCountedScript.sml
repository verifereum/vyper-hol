Theory typedCopyFieldsCounted
Ancestors
  typedCopyLoopCounted placeMemoryFieldsForward placeMemoryCopyEffect
  bodyDeclMemoryCounted bodyDeclMemoryCore fragGasPathMem fragExecMem fragExec
  instMemFrontier exprLoweringProps emitHelper emitHelperProps compileEnv context
  venomState venomInst list rich_list arithmetic

Theorem typed_memory_fields_addresses_mem_ok[local]:
  (do dp <- compile_with_byte_offset dst doff;
      sp <- compile_with_byte_offset src soff;
      comp_return (dp,sp)
   od) sa = ((dp,sp),sb) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  Cases_on `doff = 0` >> Cases_on `soff = 0` >>
  simp[compile_with_byte_offset_def, emit_op_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[] >> irule run_inst_seq_mem_ok_every >>
  pure_rewrite_tac[emitted_insts_def, GSYM APPEND_ASSOC] >>
  simp[DROP_APPEND1, mk_inst_def, below_frontier_no_ranges]
QED

Theorem typed_memory_fields_addresses_path_mem:
  (do dp <- compile_with_byte_offset dst doff;
      sp <- compile_with_byte_offset src soff;
      comp_return (dp,sp)
   od) sa = ((dp,sp),sb) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\ alloca_history func t /\
      eval_operand dp t = SOME (dw + n2w doff) /\
      eval_operand sp t = SOME (sw + n2w soff) /\
      (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all typed_memory_fields_addresses_sequence >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule typed_memory_fields_addresses_mem_ok >> goal_assum (drule_at Any)) >>
  `EVERY (\j. j.inst_opcode <> GAS /\ j.inst_opcode <> INVOKE /\
      ~is_terminator j.inst_opcode) (emitted_insts sa sb)` by fs[EVERY_MEM] >>
  `gas_path_mem ctx func s 0
     (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule body_decl_zero_gas_path >> simp[] >> qexists `sa` >> simp[]) >>
  `alloca_history func (u with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule body_store_memory_history >> simp[] >> qexistsl [`s`, `sa`] >> simp[]) >>
  qexists `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  gvs[venom_state_component_equality, eval_operand_def, lookup_var_def, same_blocks_def]
QED

Theorem typed_memory_fields_path_mem_induction:
  !dts sts doff soff sa sb s.
  LENGTH dts = LENGTH sts /\
  compile_typed_copy_fields cenv dst src dts sts doff soff sa = ((),sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\ P dts sts doff soff sa s /\
  (!dt dr st sr a b u dx sx.
    LENGTH dr = LENGTH sr /\
    (do dp <- compile_with_byte_offset dst dx;
        sp <- compile_with_byte_offset src sx;
        compile_store_memory_typed cenv dp dt sp st
     od) a = ((),b) /\
    fn_has_code a b func /\ ~u.vs_halted /\ P (dt::dr) (st::sr) dx sx a u ==>
    ?v. gas_path_mem ctx func u 0 (OK v) /\ ~v.vs_halted /\
        P dr sr (dx + type_memory_bytes cenv dt)
          (sx + type_memory_bytes cenv st) b v) ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\ ~t.vs_halted /\
      P [] [] (doff + SUM (MAP (type_memory_bytes cenv) dts))
        (soff + SUM (MAP (type_memory_bytes cenv) sts)) sb t
Proof
  Induct
  >- (Cases_on `sts` >> simp[cj 2 compile_store_memory_typed_def, comp_return_def] >>
      rpt strip_tac >> gvs[] >> qexists `s` >> simp[gas_path_mem_rules]) >>
  pop_assum (mk_asm "ih") >>
  Cases_on `sts` >> simp[] >> rpt strip_tac >>
  rename1 `compile_typed_copy_fields cenv dst src (dt::dts) (st::sts) doff soff sa = ((),sb)` >>
  drule typed_memory_fields_cons_compile >> strip_tac >>
  `cs_extends sa c` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa c func /\ fn_has_code c sb func` by metis_tac[fn_has_code_split] >>
  `?u. gas_path_mem ctx func s 0 (OK u) /\ ~u.vs_halted /\
       P dts sts (doff + type_memory_bytes cenv dt)
         (soff + type_memory_bytes cenv st) c u` by
    (first_assum irule >> simp[] >> qexists `sa` >>
     simp[comp_bind_def, comp_ignore_bind_def]) >>
  asm_x "ih" drule_all >> strip_tac >>
  rename1 `gas_path_mem ctx func u 0 (OK result)` >>
  qexists `result` >> conj_tac
  >- (`gas_path_mem ctx func s (0 + 0) (OK result)` by
        (irule gas_path_mem_then >> qexists `u` >> simp[]) >> gvs[]) >>
  simp[] >> qpat_x_assum `P [] [] _ _ _ _` mp_tac >>
  rpt (pop_assum kall_tac) >>
  simp_tac bool_ss [AC ADD_ASSOC ADD_COMM]
QED

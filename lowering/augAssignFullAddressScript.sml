(* Literal slot additions choose their concrete and ghost endpoint before the horizon. *)
Theory augAssignFullAddress
Ancestors
  typedCopyOriginPtrBase augAssignPtrStorageAddress ptrSafetyTransport
  fragGasOriginPtr ptrDiscipline ptrSafeRun codegenRel contextCodegenRel
  unitTransformDefs instMemFrontier memSafeRun
  bodyPtrDefs sourceUnitExecution accountsRelProps
  emitHelper emitHelperProps compileEnv loweringStateRelDefs
  venomExecSemantics venomInst venomState finite_map list pred_set

Theorem literal_slot_add_origin_ptr:
  emit_op ADD [Lit lhs_word; Lit rhs_word] sa = (Var out,sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t G' tn'.
    t = update_var out (lhs_word + rhs_word)
          (s with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    (!D lo. allocas_from lo s ==>
      gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')) /\
    op_prov G' (Var out) = NONE /\ op_taint tn' (Var out) = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP G' p = FLOOKUP G p /\
      op_taint tn' (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `LENGTH sb.cs_current_insts = SUC s.vs_inst_idx` by simp[] >>
  `!p. not_fresh_at sa p ==> p <> out` by
    (rpt strip_tac >> gvs[not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id ADD [Lit lhs_word; Lit rhs_word] [out]` >>
  qabbrev_tac `u = update_var out (lhs_word + rhs_word) s` >>
  qexistsl_tac [`u with vs_inst_idx := LENGTH sb.cs_current_insts`,
    `step_prov PG G inst u`, `step_taint inst s u tn`] >>
  conj_tac >- simp[Abbr `u`, update_var_def] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      mp_tac (Q.INST
        [`opc` |-> `ADD`, `left` |-> `Lit lhs_word`, `right` |-> `Lit rhs_word`,
         `x` |-> `lhs_word`, `y` |-> `rhs_word`, `w` |-> `lhs_word + rhs_word`,
         `a` |-> `sa`, `op` |-> `Var out`, `b` |-> `sb`, `func` |-> `func`,
         `s` |-> `s`, `D` |-> `D`, `lo` |-> `lo`, `ctx` |-> `ctx`,
         `G` |-> `G`, `tn` |-> `tn`, `PG` |-> `PG`, `explicit` |-> `explicit`,
         `off` |-> `0`, `len` |-> `0`] typed_copy_origin_ptr_binop_path) >>
      impl_tac >- simp[eval_operand_def, op_taint_def] >>
      strip_tac >> gvs[Abbr `inst`, Abbr `u`, arithmeticTheory.ADD1]) >>
  `new_site_bytes s u = {}` by
    simp[Abbr `u`, new_site_bytes_def, update_var_def, FLOOKUP_DEF,
         EXTENSION, SF CONJ_ss] >>
  simp[Abbr `inst`, step_taint_def, set_var_taint_def, adopt_reset_def,
       imm_taint_def, mk_inst_def, source_memory_write_ranges_def,
       step_writes_def, step_prov_def, set_prov_def, out_prov_def, first_prov_def,
       out_taint_def, eval_operand_def, op_prov_def, op_taint_def,
       mem_taint_def, store_taint_def, range_bytes_def, written_taint_def,
       Abbr `u`, update_var_def, lookup_var_def, FLOOKUP_DRESTRICT,
       FLOOKUP_UPDATE] >>
  rpt strip_tac >> `p <> out` by metis_tac[] >>
  gvs[FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]
QED

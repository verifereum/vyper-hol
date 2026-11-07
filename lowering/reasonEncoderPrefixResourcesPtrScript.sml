(* Source-independent Error(string) prefix: no read of the reason occurs here. *)
Theory reasonEncoderPrefixResourcesPtr
Ancestors
  normalizationAllocationPathPtr reasonSelectorResourcesPtr reasonCodeOffsetPtr
  reasonPrefixPtr exprLoweringProps context compileEnv emitHelper emitHelperProps
  bodyPtrDefs loweringPosts fragGasPathPtr venomState venomInst finite_map words
  ptrDiscipline

Theorem reason_encoder_prefix_resources_path_ptr:
  compile_alloc_buffer n cc = (buf,c1) /\ fn_has_code cc c1 func /\
  emit_void MSTORE [buf.buf_operand; Lit 0x08c379a0w] c1 = ((),c2) /\
  emit_op ADD [buf.buf_operand; Lit 32w] c2 = (payload,c3) /\
  compile_alloc_buffer m c3 = (tuple,c4) /\ fn_has_code c3 c4 func /\
  fn_has_code c1 c2 func /\ fn_has_code c2 c3 func /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv cc /\
  fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = cc.cs_current_bb /\
  s.vs_inst_idx = LENGTH cc.cs_current_insts /\ ~s.vs_halted /\
  32 <= n /\ n < dimword(:256) /\ m < dimword(:256) ==>
  ?t out x out2 b b2 Gf tnf.
    buf.buf_operand = Var out /\ payload = Var x /\ tuple.buf_operand = Var out2 /\
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK t) /\
    t.vs_current_bb = c4.cs_current_bb /\
    t.vs_inst_idx = LENGTH c4.cs_current_insts /\ ~t.vs_halted /\
    stmt_state_rel ctx func cenv cx es t /\ local_ptrs_reserved cenv c4 /\
    lookup_var out t = SOME (n2w b) /\ lookup_var x t = SOME (n2w b+32w) /\
    lookup_var out2 t = SOME (n2w b2) /\ b+n < dimword(:256) /\
    b2+m < dimword(:256) /\
    ptr_covers Gf tnf out t n /\ ptr_covers Gf tnf x t (n-32) /\
    ptr_covers Gf tnf out2 t m /\
    FLOOKUP t.vs_allocas c3.cs_next_id = SOME (b2,m) /\
    MEM (mk_inst c3.cs_next_id ALLOCA [Lit (n2w m)] [out2]) (fn_insts func) /\
    not_local_ptr cenv es.scopes out2 /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!old. not_fresh_at cc old ==>
      lookup_var old t = lookup_var old s /\ FLOOKUP Gf old = FLOOKUP G old /\
      op_taint tnf (Var old) = op_taint tn (Var old)) /\
    (!old k. not_fresh_at cc old /\ ptr_covers G tn old s k ==>
      ptr_covers Gf tnf old t k) /\
    t.vs_labels = s.vs_labels /\
    (!src. (!p. src = Var p ==> not_fresh_at cc p) ==>
      eval_operand src t = eval_operand src s /\
      op_prov Gf src = op_prov G src /\ op_taint tnf src = op_taint tn src) /\
    (!ty tv a. ~cenv.ce_is_ctor /\ immutable_holds cenv cx ty tv a es s ==>
      immutable_holds cenv cx ty tv a es t)
Proof
  strip_tac >>
  drule_all normalization_alloc_buffer_path_ptr >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] strip_assume_tac) >>
  drule code_offset_emit_var >> strip_tac >> gvs[] >>
  `not_fresh_at c3 root /\ not_fresh_at c3 out /\
   (!old. not_fresh_at c1 old ==> not_fresh_at c3 old)` by suspend "freshness" >>
  `?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
     FLOOKUP u.vs_allocas inst.inst_id = SOME (b,n)` by
    (qexists_tac `mk_inst cc.cs_next_id ALLOCA [Lit (n2w n)] [root]` >>
     simp[mk_inst_def]) >>
  drule_all reason_selector_payload_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  drule_all normalization_alloc_buffer_path_ptr >>
  disch_then (qspecl_then [`tnf`, `PG`, `Gf`, `D`] strip_assume_tac) >>
  qexistsl_tac [`u'`, `root'`, `b`, `b'`, `G1'`, `tn1'`] >>
  asm_rewrite_tac[] >> rpt conj_tac
  >- suspend "path"
  >- suspend "outer_value"
  >- suspend "payload_value"
  >- suspend "outer_cover"
  >- suspend "payload_cover"
  >- suspend "tuple_local"
  >- suspend "allocas"
  >- suspend "metadata"
  >- suspend "coverage"
  >- suspend "operand"
  >> suspend "immutable"
QED

Resume reason_encoder_prefix_resources_path_ptr[freshness]:
  gvs[emit_void_def, emit_op_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, fresh_var_def, fresh_id_def, emit_def, not_fresh_at_def] >>
  metis_tac[arithmeticTheory.LESS_EQ_REFL, arithmeticTheory.LESS_EQ_TRANS,
    arithmeticTheory.LESS_EQ_ADD]
QED
Resume reason_encoder_prefix_resources_path_ptr[path]:
  drule_all gas_path_ptr_then >> simp[] >> strip_tac >>
  qpat_assum `gas_path_ptr _ _ _ _ _ G tn s _ G1 tn1 _`
    (mp_then Any mp_tac gas_path_ptr_then) >>
  disch_then drule >> simp[]
QED
Resume reason_encoder_prefix_resources_path_ptr[outer_value]:
  metis_tac[]
QED
Resume reason_encoder_prefix_resources_path_ptr[payload_value]:
  metis_tac[]
QED
Resume reason_encoder_prefix_resources_path_ptr[outer_cover]:
  metis_tac[]
QED
Resume reason_encoder_prefix_resources_path_ptr[payload_cover]:
  metis_tac[]
QED
Resume reason_encoder_prefix_resources_path_ptr[tuple_local]:
  `root' = STRING #"%" (toString c3.cs_next_var)` by
    (qpat_x_assum `compile_alloc_buffer m c3 = _` mp_tac >>
     simp[compile_alloc_buffer_def, emit_op_def, fresh_var_def, comp_bind_def,
       comp_return_def, comp_ignore_bind_def, fresh_id_def, emit_def] >>
     strip_tac >> gvs[]) >>
  asm_rewrite_tac[] >> irule local_ptrs_reserved_fresh >>
  qexists_tac `c3` >> simp[]
QED
Resume reason_encoder_prefix_resources_path_ptr[allocas]:
  metis_tac[]
QED
Resume reason_encoder_prefix_resources_path_ptr[metadata]:
  metis_tac[]
QED
Resume reason_encoder_prefix_resources_path_ptr[coverage]:
  metis_tac[]
QED
Resume reason_encoder_prefix_resources_path_ptr[immutable]:
  rpt strip_tac >>
  qpat_x_assum `immutable_holds _ _ _ _ _ _ s` mp_tac >>
  simp[immutable_holds_def]
QED
Resume reason_encoder_prefix_resources_path_ptr[operand]:
  Cases_on `src` >> simp[eval_operand_def, op_prov_def, op_taint_def] >>
  rpt strip_tac >> metis_tac[]
QED
Finalise reason_encoder_prefix_resources_path_ptr

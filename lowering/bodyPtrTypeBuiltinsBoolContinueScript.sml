(* Bytes-to-Bool continuation boundaries: the shared loader and pure Bool suffix. *)
Theory bodyPtrTypeBuiltinsBoolContinue
Ancestors bodyPtrTypeBuiltinsUintContinue bodyPtrTypeBuiltinsUintCounted
  bodyPtrTypeBuiltinsBool bodyPtrTypeBuiltinsIszero bodyPtrTypeBuiltinsUnsignedSemantics
  exprLowering exprLoweringProps emitHelperProps builtinConvertPrefix
  fragExec venomExecSemantics venomInst venomState ptrDiscipline finite_map opcodeClass
  vyperTypeSystem vyperValueOperation exprSimConvert compileEnv loweringShapeDefs
  fragGasPathPtr

Theorem bytes_bool_convert_parts:
  compile_type_convert x (mk_convert_op (BaseT (BytesT (Dynamic n)))
    (BaseT BoolT)) sa = (out,sb) ==>
  ?word bits sm.
    load_bytestring_as_word x SHR sa = ((word,bits),sm) /\
    compile_type_convert word ConvToBool sm = (out,sb) /\
    inst_extends sa sm /\ inst_extends sm sb
Proof
  simp[mk_convert_op_def, is_bytestring_type_def] >>
  simp_tac pure_ss [compile_type_convert_def, comp_bind_def, comp_return_def,
                   LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  gvs[comp_bind_def, comp_return_def] >>
  metis_tac[inst_extends_load_bytestring_as_word, inst_extends_emit_op,
            inst_extends_trans]
QED

Theorem convert_bool_run_actual:
  compile_type_convert x ConvToBool sa = (out,sb) /\
  eval_operand x s = SOME w ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      eval_operand out t = SOME (bool_to_word (w <> 0w)) /\
      (t with vs_vars := s.vs_vars) = s /\
      (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s)
Proof
  strip_tac >> drule convert_bool_code >> strip_tac >>
  `step_inst_base (mk_inst sa.cs_next_id ISZERO [x] [a]) s =
     OK (update_var a (bool_to_word (w = 0w)) s)` by
    (irule step_ISZERO >> simp[]) >>
  `step_inst_base (mk_inst (sa.cs_next_id+1) ISZERO [Var a] [b])
      (update_var a (bool_to_word (w = 0w)) s) =
     OK (update_var b (bool_to_word (bool_to_word (w = 0w) = 0w))
       (update_var a (bool_to_word (w = 0w)) s))` by
    (irule step_ISZERO >>
     simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `run_inst_seq (emitted_insts sa sb) s =
     OK (update_var b (bool_to_word (bool_to_word (w = 0w) = 0w))
       (update_var a (bool_to_word (w = 0w)) s))` by
    simp[run_inst_seq_def] >>
  drule_all convert_bool_runtime_frame >> strip_tac >>
  goal_assum (drule_at Any) >> simp[] >>
  simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  Cases_on `w = 0w` >> simp[bool_to_word_def]
QED

Theorem convert_bool_no_abort:
  compile_type_convert x ConvToBool sa = (out,sb) ==>
  run_inst_seq (emitted_insts sa sb) s <> Abort err t
Proof
  strip_tac >> drule convert_bool_code >> strip_tac >>
  simp[run_inst_seq_def, AllCaseEqs()] >> rpt strip_tac >>
  drule step_inst_base_abort_opcodes >> simp[mk_inst_def]
QED

Theorem bytes_bool_no_abort:
  compile_type_convert (Var src) (mk_convert_op (BaseT (BytesT (Dynamic n)))
    (BaseT BoolT)) sa = (out,sb) /\ not_fresh_at sa src ==>
  run_inst_seq (emitted_insts sa sb) s <> Abort err t
Proof
  strip_tac >> drule bytes_bool_convert_parts >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  drule_all unsigned_loader_no_abort >> strip_tac >>
  drule convert_bool_no_abort >> strip_tac >>
  simp[bodyPtrTypeBuiltinsScalarComposeTheory.scalar_seq_append_abort_iff] >>
  metis_tac[]
QED

Theorem zero_bool_continuation:
  expr_post ctx func cenv cx e es sa s1 s0 (ee with gas_obs := []) v1 x t0 /\
  t0.vs_current_bb = s1.cs_current_bb /\
  t0.vs_inst_idx = LENGTH s1.cs_current_insts /\ ~t0.vs_halted /\
  expr_type e = BaseT (BytesT (Dynamic n)) /\ v1 = BytesV [] /\
  ghost_inv d cenv cx (ee with gas_obs := []) G tn t0 /\
  ghost_kept cenv es sa G0 tn0 s0 G tn ==>
  gas_summary_ptr_at (cx_dead cx) (ctx,func) PG []
    (\vs. (convert_result cx (expr_type e) (BaseT BoolT) v1,vs))
    (ee with gas_obs := [],t0,G,tn)
    (\res fin H th ss. ?v. res = INL v /\
      expr_post ctx func cenv cx
        (TypeBuiltin (BaseT BoolT) Convert (BaseT BoolT) [e])
        es sa s1 s0 fin v (Lit 0w) ss /\
      ss.vs_current_bb = s1.cs_current_bb /\
      ss.vs_inst_idx = LENGTH s1.cs_current_insts /\
      ghost_inv d cenv cx fin H th ss /\
      ptr_val_ok cx (BaseT BoolT) v (Lit 0w) H th ss /\
      ghost_kept cenv es sa G0 tn0 s0 H th)
    (\res fin gt out. expr_exit res out)
Proof
  strip_tac >> gvs[] >>
  simp[convert_result_def, evaluate_convert_from_def, evaluate_convert_def] >>
  simp[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL (BoolV F)`,`ee`,`G`,`tn`,`OK t0`] >>
  simp[gas_path_ptr_rules, bodyPtrTypeBuiltinsLiteralPostTheory.ptr_val_ok_word_literal,
       is_word_type_def] >>
  irule zero_convert_child_post >>
  simp[is_word_type_def, vyperValueTheory.evaluate_type_def,
       valueEncodingTheory.typed_val_to_w256_def,
       valueEncodingTheory.val_to_w256_def, bool_to_word_def] >>
  goal_assum (drule_at Any)
QED

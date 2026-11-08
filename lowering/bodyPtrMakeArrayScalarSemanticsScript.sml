(* Typed semantics are kept separate from counted pointer edges and ghost frames. *)
Theory bodyPtrMakeArrayScalarSemantics
Ancestors
  bodyPtrMakeArrayScalarDispatch bodyPtrMakeArrayEmission exprSimUnwrap
  exprSimUnwrapProps exprSimProps loweringPosts venomExecSemantics venomInst
  venomState valueEncodingProps vyperState vyperInterpreter context compileEnv valueCopyBytes

Theorem scalar_located_load_step:
  vv_post ctx fn ce cx e es sa sm s0 es' tv (LocatedValue t p) s /\
  read_result cx tv es' = (INL v,es') /\
  is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME ty /\ ~ce.ce_is_ctor /\
  ((p.ptr_location = LocMemory /\ opc = MLOAD) \/
   (p.ptr_location = LocStorage /\ opc = SLOAD) \/
   (p.ptr_location = LocTransient /\ opc = TLOAD) \/
   (p.ptr_location = LocCode /\ opc = DLOAD)) ==>
  ?a. eval_operand p.ptr_operand s = SOME a /\
    step_inst_base (mk_inst id opc [p.ptr_operand] [tmp]) s =
      OK (update_var tmp (typed_val_to_w256 ty v) s)
Proof
  strip_tac >>
  `vv_post ctx fn ce cx e es sa sm s0 es' (Value v) (LocatedValue t p) s`
    by metis_tac[vv_post_read_result] >>
  qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ tv _ _` kall_tac >>
  gvs[vv_post_def, vv_holds_def] >>
  gvs[read_result_def, return_def] >>
  (reverse (Cases_on `p.ptr_location = LocCode`)
   >- (imp_res_tac storage_holds_load >> gvs[] >>
       simp[Once step_inst_base_def, mk_inst_def, exec_read1_def,
            GSYM mem_word_at_eq_mload])) >>
  gvs[] >> drule_all immutable_holds_dload >> strip_tac >> gvs[] >>
  drule step_DLOAD >> simp[]
QED

Theorem scalar_unwrap_typed_instruction:
  vv_post ctx fn ce cx e es sa sm s0 es' tv (LocatedValue t p) s /\
  read_result cx tv es' = (INL v,es') /\
  is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME ty /\ ~ce.ce_is_ctor /\
  unwrap_value ce (LocatedValue t p) sm = (op,sb) /\
  fn_has_code sm sb fn /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?opc tmp bb a.
    op = Var tmp /\
    ((p.ptr_location = LocMemory /\ opc = MLOAD) \/
     (p.ptr_location = LocStorage /\ opc = SLOAD) \/
     (p.ptr_location = LocTransient /\ opc = TLOAD) \/
     (p.ptr_location = LocCode /\ opc = DLOAD)) /\
    eval_operand p.ptr_operand s = SOME a /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst sm.cs_next_id opc [p.ptr_operand] [tmp]) /\
    step_inst_base (mk_inst sm.cs_next_id opc [p.ptr_operand] [tmp]) s =
      OK (update_var tmp (typed_val_to_w256 ty v) s) /\
    s.vs_current_bb = sb.cs_current_bb /\
    SUC s.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at sm x ==> x <> tmp)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `post_value_type ce e = expr_type e` by
    (irule post_value_type_word >> first_assum ACCEPT_TAC) >>
  `t = expr_type e` by
    (gvs[vv_post_def, vv_holds_def] >>
     imp_res_tac valueCopyBytesTheory.is_bytestring_word_type >> gvs[]) >>
  `is_word_type t` by simp[] >>
  drule_all scalar_unwrap_emits_load >> strip_tac >>
  `emit_op opc [p.ptr_operand] sm = (op,sb)` by metis_tac[] >>
  drule_all emit_op_fetch_boundary >> strip_tac >>
  qexistsl_tac [`opc`, `tmp`, `bb`] >> simp[] >>
  simp[not_fresh_at_def] >>
  irule scalar_located_load_step >> metis_tac[]
QED

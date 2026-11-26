Theory bodyConvertScalarRevertOrigin
Ancestors
  bodyFullConvertScalarRun bodyFullConvertScalarCertificate instIdxIndep
  exprSimConvert exprLowering exprLoweringProps fragGasOriginPtr
  compileEnv vyperAST vyperInterpreter vyperTypeSystem venomState

(* Keep the physical abort and the origin-path endpoint tied to the same run. *)
Theorem scalar_convert_revert_origin:
  valid_conversion src dst /\ ~is_bytestring_type src /\
  evaluate_type (get_tenv cx) src = SOME tv /\
  evaluate_type (get_tenv cx) dst = SOME tout /\ value_has_type tv v /\
  (!name n. dst = FlagT name /\ FLOOKUP (get_tenv cx) name = SOME (FlagArgs n) ==>
    cenv.ce_flag_n_members (nsid_to_string name) = n) /\
  compile_type_convert x (case dst of FlagT name =>
    ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
    | _ => mk_convert_op src dst) sa = (out,sb) /\
  eval_operand x s = SOME (typed_val_to_w256 tv v) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  convert_result cx src dst v = INR exc /\
  (!a u. run_inst_seq (emitted_insts sa sb) s = Abort a u ==> a = Revert_abort) ==>
  ?msg u Gf tnf. exc = Error (RuntimeError msg) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
      (Abort Revert_abort u,Gf,tnf))
Proof
  strip_tac >>
  drule_all scalar_convert_typed_run >> strip_tac >>
  qpat_x_assum `!exc. convert_result _ _ _ _ = INR exc ==> _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `!a u. run_inst_seq _ _ = Abort a u ==> _`
    (drule_then SUBST_ALL_TAC) >>
  drule_at (Pat `run_inst_seq _ _ = _`) scalar_convert_run_origin >>
  disch_then (drule_all o SRULE []) >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  rename1 `run_inst_seq _ _ = Abort Revert_abort t` >>
  qexistsl_tac [`msg`,`t with vs_inst_idx := j`,`H`,`th`] >>
  fs[exec_result_map_def]
QED

(* Flag suffix success does not depend on stale bindings of fresh variables. *)
Theory bodyPtrBopInFlagRobust
Ancestors bodyPtrBopInFlagInterface exprBopFlag freshWrites varsExt
  compileEnv fragGasFresh loweringSlice valueEncoding list appendStorageStageTransportPtr

Theorem membership_flag_source_run_robust:
  (bop = In \/ bop = NotIn) /\
  value_has_type (FlagTV m) v1 /\ value_has_type (FlagTV m) v2 /\ m <= 256 /\
  compile_binop bop x y ty bl el sa = (op,sb) /\
  eval_operand x s = SOME (val_to_w256 v1) /\
  eval_operand y s = SOME (val_to_w256 v2) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  (!z. y = Var z ==> not_fresh_at sa z) /\
  expr_res_ok (bop_result cx ann bop tys v1 v2 es) ==>
  ?v t. bop_result cx ann bop tys v1 v2 es = INL v /\ word_value v /\
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (val_to_w256 v)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?v t. bop_result cx ann bop tys v1 v2 es = INL v /\ word_value v /\
    run_inst_seq (emitted_insts sa sb) (drop_fresh sa s) = OK t /\
    eval_operand op t = SOME (val_to_w256 v)` by
    (irule membership_flag_source_run >> simp[fresh_vars_wrt_drop_fresh] >>
     `?bl' el' ty' x' y'. compile_binop bop x' y' ty' bl' el' sa = (op,sb) /\
        eval_operand x' (drop_fresh sa s) = SOME (val_to_w256 v1) /\
        eval_operand y' (drop_fresh sa s) = SOME (val_to_w256 v2)` by
       (qexistsl_tac [`bl`, `el`, `ty`, `x`, `y`] >>
        gvs[eval_operand_drop_fresh]) >> metis_tac[]) >>
  `straight_fresh (compile_binop bop x y ty bl el)` by
    metis_tac[straight_fresh_flag_in] >>
  `writes_fresh sa (emitted_insts sa sb)` by metis_tac[straight_fresh_def] >>
  `vars_ext_result (run_inst_seq (emitted_insts sa sb) (drop_fresh sa s))
                   (run_inst_seq (emitted_insts sa sb) s)` by
    (irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh] >>
     drule writes_fresh_path_opcodes >> simp[EVERY_MEM]) >>
  gvs[vars_ext_result_def] >> metis_tac[vars_ext_eval_operand]
QED

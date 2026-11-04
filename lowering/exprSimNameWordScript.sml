(* Counted simulation for a word local. *)
Theory exprSimNameWord
Ancestors
  exprSimProps
  exprSimDefs exprSimStack exprSimValues
  loweringPosts
  list rich_list finite_map pred_set
  fragExec varsExt loweringSlice localPtrsProps venomMemDefs
  exprLowering emitHelper emitHelperProps exprLoweringProps compileEnv
  vyperInterpreter vyperState vyperValueOperation vyperContext
  valueEncoding valueEncodingProofs vyperTypeSystem
  venomExecSemantics venomInst venomState
  vyperLookupStorage vyperStorageBackend

Theorem compile_name_word_sim:
  !ctx func cenv cx ty ann id es p sz entry.
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    is_word_type ann /\
    lookup_scopes id es.scopes = SOME entry /\ word_value entry.value ==>
    expr_sim ctx func cenv cx ty (Name ann id) es
Proof
  rpt strip_tac >> irule expr_sim_values >>
  drule_then (qspecl_then [`cx`, `ann`] assume_tac) eval_name_word >>
  simp[] >> rpt strip_tac >> gvs[] >>
  drule_all lower_value_name_word >> strip_tac >>
  irule frag_exec_conseq >>
  drule emit_op_frag >>
  disch_then (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es`, `s0`,
                           `val_to_w256 entry.value`, `\r. F`] mp_tac) >>
  impl_tac
  >- (simp[is_terminator_def] >> strip_tac >>
      drule_all step_name_word >> simp[]) >>
  strip_tac >> first_x_assum (irule_at Any) >> rpt strip_tac >>
  gvs[expr_post_def, expr_val_rel_def, expr_val_at_def,
      vyperASTTheory.expr_type_def,
      typed_val_to_w256_word_value, locals_kept_mem]
QED

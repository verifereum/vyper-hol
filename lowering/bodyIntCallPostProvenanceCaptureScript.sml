(* Compiler boundary for a subscript whose base_e is captured before its index. *)
Theory bodyIntCallPostProvenanceCapture
Ancestors exprLowering vyperInterpreter compileEnv

Theorem copies_subscript_base_source:
  cenv.ce_modules =
    (case ALOOKUP cx.sources cx.txn.target of NONE => [] | SOME mods => mods) ==>
  (copies_subscript_base cenv base_e idx <=> subscript_reads_base cx base_e idx)
Proof
  simp[copies_subscript_base_def, subscript_reads_base_def]
QED

Theorem compile_subscript_capture_array:
  copies_subscript_base cenv base_e idx /\
  place_type cenv base_e = ValPT (ArrayT elem len) ==>
  (compile_subscript cfn cenv ret_ty ty base_e idx sa = (vv,sb) <=>
   ?vv0 s1 saved s2 index s3 ptr loc.
     cfn cenv ty base_e sa = (vv0,s1) /\
     compile_snapshot_vv cenv T vv0 s1 = (saved,s2) /\
     loc = (case vv_location saved of SOME l => l | NONE => LocMemory) /\
     lower_value cfn cenv ty idx s2 = (index,s3) /\
     compile_array_subscript (vv_operand saved) index
       (case len of Fixed n => F | _ => T)
       (case len of Fixed n => n | _ => 0)
       (word_scale loc) (elem_size_in_location cenv loc elem)
       (is_signed_type (expr_type idx))
       (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc) s3 = (ptr,sb) /\
     vv = LocatedValue ret_ty (mk_ptr ptr loc))
Proof
  strip_tac >>
  Cases_on `cfn cenv ty base_e sa` >>
  rename1 `cfn cenv ty base_e sa = (vv0,s1)` >>
  Cases_on `compile_snapshot_vv cenv T vv0 s1` >>
  rename1 `compile_snapshot_vv cenv T vv0 s1 = (saved,s2)` >>
  Cases_on `lower_value cfn cenv ty idx s2` >>
  simp[compile_subscript_def, comp_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> gvs[] >> metis_tac[]
QED

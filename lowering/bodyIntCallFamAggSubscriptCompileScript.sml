(* Compiler cuts used by the joint mapping producer. *)
Theory bodyIntCallFamAggSubscriptCompile
Ancestors
  exprSimMapKey exprSimSubscriptMap exprLoweringProps fragExec compileEnv

Theorem intcall_mapping_compile_cuts:
  compile_expr ce ty obj sa = (bvv,sm) /\
  lower_value compile_expr ce (expr_type idx) idx sm = (key,sn) /\
  (if is_bytestring_type kt then compile_keccak256_key key F sn
   else (key,sn)) = (hashed,sp) /\
  compile_mapping_subscript (vv_operand bvv) hashed sp = (op,sb) /\
  fn_has_code sa sb func ==>
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id <= sn.cs_next_id /\
  fn_has_code sa sm func /\ fn_has_code sm sn func /\
  fn_has_code sn sp func /\ fn_has_code sp sb func
Proof
  strip_tac >>
  `cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var /\
   sa.cs_next_id <= sm.cs_next_id` by
    (drule (cj 1 compile_expr_grows) >> simp[]) >>
  `cs_extends sm sn /\ sm.cs_next_var <= sn.cs_next_var /\
   sm.cs_next_id <= sn.cs_next_id` by
    (drule (cj 2 compile_expr_grows) >> simp[]) >>
  `cs_extends sn sp` by
    (Cases_on `is_bytestring_type kt`
     >- (qpat_x_assum `(if _ then _ else _) = _` mp_tac >> simp[] >>
         strip_tac >> qspecl_then [`key`, `F`, `sn`] mp_tac
           ci_mono_compile_keccak256_key >> simp[ci_mono_def]) >>
     gvs[] >> simp[cs_extends_refl]) >>
  `cs_extends sp sb` by
    (qspecl_then [`vv_operand bvv`, `hashed`, `sp`] mp_tac
       ci_mono_compile_mapping_subscript >> simp[ci_mono_def]) >>
  `cs_extends sn sb /\ cs_extends sm sb` by
    metis_tac[cs_extends_trans] >>
  metis_tac[fn_has_code_split]
QED

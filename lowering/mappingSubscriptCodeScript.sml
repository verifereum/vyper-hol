(* Shared compiler decomposition for mapping subscripts. *)
Theory mappingSubscriptCode
Ancestors
  exprSimMapKey exprLoweringProps exprOperandVar
  freshWrites fragExec loweringStateRelDefs compileEnv context

Theorem mapping_subscript_code_parts:
  compile_expr cenv ty (Subscript ann obj idx) sa = (vv,sb) /\
  place_type cenv obj = MapPT kt vt /\ fn_has_code sa sb func /\
  local_ptrs_reserved cenv sa ==>
  ?bvv sm key sn hashed sp slot.
    compile_expr cenv ty obj sa = (bvv,sm) /\
    lower_value compile_expr cenv (expr_type idx) idx sm = (key,sn) /\
    (if is_bytestring_type kt then compile_keccak256_key key F sn
     else (key,sn)) = (hashed,sp) /\
    compile_mapping_subscript (vv_operand bvv) hashed sp = (slot,sb) /\
    vv = LocatedValue ann (mk_ptr slot
      (case vv_location bvv of SOME loc => loc | NONE => LocMemory)) /\
    cs_extends sa sm /\ cs_extends sm sn /\ cs_extends sn sb /\
    sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
    sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id <= sn.cs_next_id /\
    fn_has_code sa sm func /\ fn_has_code sm sn func /\
    fn_has_code sn sb func /\ fn_has_code sp sb func /\
    local_ptrs_reserved cenv sm
Proof
  strip_tac >> drule_all compile_expr_mapping_subscript_parts >> strip_tac >>
  `cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var /\
   sa.cs_next_id <= sm.cs_next_id` by
    (drule (cj 1 compile_expr_grows) >> simp[]) >>
  `cs_extends sm sn /\ sm.cs_next_var <= sn.cs_next_var /\
   sm.cs_next_id <= sn.cs_next_id` by
    (drule (cj 2 compile_expr_grows) >> simp[]) >>
  `cs_extends sn sp` by
    (Cases_on `is_bytestring_type kt`
     >- (qpat_x_assum `(if _ then _ else _) = _` mp_tac >> simp[] >> strip_tac >>
         qspecl_then [`key`, `F`, `sn`] mp_tac
           ci_mono_compile_keccak256_key >> simp[ci_mono_def]) >>
     fs[] >> simp[cs_extends_refl]) >>
  `cs_extends sp sb` by
    (qspecl_then [`vv_operand bvv`, `hashed`, `sp`] mp_tac
       ci_mono_compile_mapping_subscript >> simp[ci_mono_def]) >>
  `cs_extends sn sb /\ cs_extends sm sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa sm func /\ fn_has_code sm sn func /\
   fn_has_code sn sb func /\ fn_has_code sp sb func` by
    metis_tac[fn_has_code_split] >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> simp[]) >>
  qexistsl_tac [`bvv`, `sm`, `key`, `sn`, `hashed`, `sp`, `slot`] >> simp[]
QED

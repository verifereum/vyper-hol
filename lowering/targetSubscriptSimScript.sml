(* Compiler boundary for subscript assignment places. *)
Theory targetSubscriptSim
Ancestors
  targetPlaceSim exprNoPopScopes exprLowering emitHelper compileEnv
  vyperAST pair
Libs
  pairLib

Theorem compile_get_target_ptr_subscript:
  !cfn cenv bt idx sa r sb.
    compile_get_target_ptr cfn cenv (SubscriptTarget bt idx) sa = (r,sb) ==>
    ?rb sm ix sn.
      compile_get_target_ptr cfn cenv bt sa = (rb,sm) /\
      lower_value cfn cenv (expr_type idx) idx sm = (ix,sn) /\
      (case SND (SND rb) of
         SOME (MapPT kt vt) =>
           ?kh sk dst.
             (if is_bytestring_type kt then compile_keccak256_key ix F
              else comp_return ix) sn = (kh,sk) /\
             compile_mapping_subscript (FST rb) kh sk = (dst,sb) /\
             r = (dst,FST (SND rb),SOME (value_type_place vt))
       | _ =>
           let loc = case FST (SND rb) of SOME l => l | NONE => LocMemory in
           let dyn = case SND (SND rb) of
                       SOME (ValPT (ArrayT _ (Dynamic _))) => T | _ => F in
           let ety = case SND (SND rb) of
                       SOME (ValPT (ArrayT t _)) => t | _ => BaseT (UintT 256) in
           let count = case SND (SND rb) of
                       SOME (ValPT (ArrayT _ (Fixed n))) => n | _ => 0 in
           ?dst.
             compile_array_subscript (FST rb) ix dyn count (word_scale loc)
               (elem_size_in_location cenv loc ety) (is_signed_type (expr_type idx))
               (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc) sn = (dst,sb) /\
             r = (dst,FST (SND rb),SOME (ValPT ety)))
Proof
  rpt gen_tac >>
  simp[Once compile_get_target_ptr_def, comp_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  rename1 `compile_get_target_ptr cfn cenv bt sa = (rb,sm)` >>
  Cases_on `SND (SND rb)`
  >- (gvs[comp_bind_def, comp_return_def] >>
      rpt (pairarg_tac >> gvs[]) >> metis_tac[]) >>
  rename1 `SND (SND rb) = SOME pt` >> Cases_on `pt` >>
  gvs[comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> metis_tac[]
QED

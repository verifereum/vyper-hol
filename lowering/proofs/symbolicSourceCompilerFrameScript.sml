Theory symbolicSourceCompilerFrame
Ancestors
  runtimeSymSrcDataFrame deploySymSrcBlockFrame abiEncoder exprLowering
  exprCallBounds compileEnv emitHelper

(* The ghost index retains the original data sections or block suffix while
   the compiler state changes. Equal results select the same bind continuation. *)
Definition compiler_preserves_def:
  compiler_preserves (R : 'g -> compile_state -> compile_state -> bool)
      (m : 'a compiler) <=>
    !g s t. R g s t ==> FST (m s) = FST (m t) /\
      R g (SND (m s)) (SND (m t))
End

Theorem compiler_preserves_runtime:
  compiler_preserves (\data s t. s = t /\ s.cs_data_sections = data) m <=>
  runtime_data_frame m
Proof
  simp[compiler_preserves_def, runtime_data_frame_def] >> metis_tac[]
QED

Theorem compiler_preserves_deploy:
  compiler_preserves (\blocks s t. t = s with cs_blocks := s.cs_blocks ++ blocks) m <=>
  deploy_blocks_frame m
Proof
  simp[compiler_preserves_def, deploy_blocks_frame_def] >>
  eq_tac >> strip_tac >> rpt gen_tac
  >- (strip_tac >> first_x_assum (qspecl_then [`B`,`s`] mp_tac) >>
      simp[] >> Cases_on `m (s with cs_blocks := s.cs_blocks ++ B)` >> simp[]) >>
  Cases_on `m s` >>
  first_x_assum drule_all >> simp[]
QED

Theorem compiler_preserves_return[simp]:
  compiler_preserves R (comp_return x)
Proof
  simp[compiler_preserves_def, comp_return_def]
QED

Theorem compiler_preserves_bind:
  compiler_preserves R m /\ (!x. compiler_preserves R (k x)) ==>
  compiler_preserves R (comp_bind m k)
Proof
  simp[compiler_preserves_def, comp_bind_def, pairTheory.ELIM_UNCURRY] >>
  metis_tac[]
QED

Theorem compiler_preserves_abi_encode:
  (!opc ops. compiler_preserves R (emit_op opc ops)) /\
  (!opc ops. compiler_preserves R (emit_void opc ops)) /\
  (!opc ops outs. compiler_preserves R (emit_inst opc ops outs)) /\
  (!name. compiler_preserves R (fresh_label name)) /\
  (!label. compiler_preserves R (new_block label)) /\
  (!n. compiler_preserves R (compile_alloc_buffer n)) /\
  (!dst src. compiler_preserves R (compile_abi_encode_static dst src)) /\
  (!dst src info asz msz len. compiler_preserves R
    (compile_abi_encode_dyn_static_loop dst src info asz msz len)) ==>
  (!dst cp ci dyn off dp.
    compiler_preserves R (compile_abi_encode_child dst cp ci dyn off dp)) /\
  (!dst src info.
    compiler_preserves R (compile_abi_encode_to_buf dst src info)) /\
  (!dst src elems so ho dp.
    compiler_preserves R
      (compile_abi_encode_complex_elems dst src elems so ho dp)) /\
  (!dst src ei asz msz len.
    compiler_preserves R (compile_abi_encode_dyn_loop dst src ei asz msz len))
Proof
  strip_tac >> ho_match_mp_tac compile_abi_encode_child_ind >>
  rpt strip_tac >>
  simp[Once compile_abi_encode_child_def, comp_ignore_bind_def] >>
  rpt (irule compiler_preserves_bind >>
       reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >>
  rpt IF_CASES_TAC >>
  simp[arithmeticTheory.ADD_COMM] >>
  rpt (irule compiler_preserves_bind >>
       reverse conj_tac >- simp[comp_ignore_bind_def] >>
       gen_tac >> BETA_TAC) >> simp[comp_ignore_bind_def]
QED

Theorem compiler_preserves_abi_decode:
  (!opc ops. compiler_preserves R (emit_op opc ops)) /\
  (!opc ops. compiler_preserves R (emit_void opc ops)) /\
  (!opc ops outs. compiler_preserves R (emit_inst opc ops outs)) /\
  (!name. compiler_preserves R (fresh_label name)) /\
  (!label. compiler_preserves R (new_block label)) /\
  (!n. compiler_preserves R (compile_alloc_buffer n)) /\
  (!src dst opc clamp. compiler_preserves R
    (compile_abi_decode_static src dst opc (\v. compile_abi_clamp_basetype v clamp))) /\
  (!bop pos. compiler_preserves R (compile_abi_dec_addr bop pos)) /\
  (!start finish hi. compiler_preserves R (compile_abi_decode_range_check start finish hi)) /\
  (!src dyn off opc bop hi. compiler_preserves R (compile_getelemptr_abi src dyn off opc bop hi)) /\
  (!opc bop elem src hi sz. compiler_preserves R
    (compile_abi_decode_dyn_elem_ptr opc bop elem src hi sz)) /\
  (!opc args. compiler_preserves R
    (case opc of CALLDATALOAD => emit_void CALLDATACOPY args
       | DLOAD => emit_void DLOADBYTES args | _ => emit_void MCOPY args)) ==>
  (!dst src opc bop hi info.
    compiler_preserves R (compile_abi_decode_to_buf dst src opc bop hi info)) /\
  (!dst src opc bop hi elems ao vo.
    compiler_preserves R
      (compile_abi_decode_complex_elems dst src opc bop hi elems ao vo)) /\
  (!dst src opc bop hi ei asz msz ip cnt.
    compiler_preserves R
      (compile_abi_decode_dyn_loop dst src opc bop hi ei asz msz ip cnt))
Proof
  strip_tac >> ho_match_mp_tac compile_abi_decode_to_buf_ind >>
  rpt strip_tac >>
  simp[Once compile_abi_decode_to_buf_def, comp_ignore_bind_def] >>
  rpt (irule compiler_preserves_bind >>
       reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >>
  rpt IF_CASES_TAC >>
  rpt (FIRST
    [irule compiler_preserves_bind >>
       reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC,
     CHANGED_TAC (pure_asm_rewrite_tac [COND_CLAUSES, comp_ignore_bind_def]),
     IF_CASES_TAC]) >> simp[arithmeticTheory.ADD_COMM]
QED

Theorem compiler_preserves_expr:
  (!ty. compiler_preserves R (invalid_expr_call ty)) /\
  (!cfn bfn tfn ce ty e.
    (!env arg_ty child. compiler_preserves R (cfn env arg_ty child)) /\
    (!rt arg_ty bi args. compiler_preserves R (bfn ce rt arg_ty bi args)) /\
    (!vt arg_ty tb rt args. compiler_preserves R (tfn ce vt arg_ty tb rt args)) ==>
    compiler_preserves R (compile_expr_body cfn bfn tfn ce ty e)) /\
  (!cfn ce rt ty bi args.
    (!env arg_ty child. compiler_preserves R (cfn env arg_ty child)) ==>
    compiler_preserves R (compile_builtin_dispatch_body cfn ce rt ty bi args)) /\
  (!cfn ce vt ty tb rt args.
    (!env arg_ty child. compiler_preserves R (cfn env arg_ty child)) ==>
    compiler_preserves R (compile_type_builtin_dispatch_body cfn ce vt ty tb rt args)) ==>
  (!ce ty e. compiler_preserves R (compile_expr ce ty e)) /\
  (!ce rt ty bi args. compiler_preserves R (compile_builtin_dispatch ce rt ty bi args)) /\
  (!ce vt ty tb rt args. compiler_preserves R (compile_type_builtin_dispatch ce vt ty tb rt args))
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "invalid") (CONJUNCTS_THEN2
    (mk_asm "expr") (CONJUNCTS_THEN2 (mk_asm "builtin") (mk_asm "type_builtin")))) >>
  rewrite_tac[compiler_preserves_def] >>
  ho_match_mp_tac compile_expr_raw_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >>
  once_rewrite_tac[compile_expr_raw_def] >> BETA_TAC >>
  rpt gen_tac >> strip_tac
  >~ [`compile_expr_body`]
  >- asm "expr" (irule o REWRITE_RULE [compiler_preserves_def])
  >~ [`compile_builtin_dispatch_body`]
  >- asm "builtin" (irule o REWRITE_RULE [compiler_preserves_def])
  >> asm "type_builtin" (irule o REWRITE_RULE [compiler_preserves_def])
  >> rpt conj_tac >> rpt gen_tac >>
  rewrite_tac[expr_child_callback_def, builtin_child_callback_def,
              type_child_callback_def] >> BETA_TAC >> IF_CASES_TAC >>
  asm "invalid" (fn th => simp[REWRITE_RULE [compiler_preserves_def] th])
QED

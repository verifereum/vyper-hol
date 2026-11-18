Theory symbolicSourceCompilerFrame
Ancestors
  abiEncoder exprLowering
  exprCallBounds compileEnv emitHelper list

(* The ghost index retains the original data sections or block suffix while
   the compiler state changes. Equal results select the same bind continuation. *)
Definition symbolic_frame_def:
  symbolic_frame (R : 'g -> compile_state -> compile_state -> bool)
      (m : 'a compiler) <=>
    !s g t. R g s t ==> FST (m s) = FST (m t) /\
      R g (SND (m s)) (SND (m t))
End

Theorem symbolic_frame_return[simp]:
  symbolic_frame R (comp_return x)
Proof
  simp[symbolic_frame_def, comp_return_def]
QED

Theorem symbolic_frame_bind:
  symbolic_frame R m /\ (!x. symbolic_frame R (k x)) ==>
  symbolic_frame R (comp_bind m k)
Proof
  simp[symbolic_frame_def, comp_bind_def, pairTheory.ELIM_UNCURRY] >>
  metis_tac[]
QED

(* Decompose the compiler monad until a primitive or induction
   hypothesis applies. Normalize the branch facts before using the IH. *)
fun abi_frame_tac goal =
  (rpt (FIRST [
    irule symbolic_frame_bind >> conj_tac,
    gen_tac,
    CHANGED_TAC (full_simp_tac bool_ss
      [comp_ignore_bind_def, symbolic_frame_return, EXISTS_DEF, arithmeticTheory.ADD_COMM]),
    IF_CASES_TAC])) goal

Theorem symbolic_frame_abi_encode:
  (!opc ops. symbolic_frame R (emit_op opc ops)) /\
  (!opc ops. symbolic_frame R (emit_void opc ops)) /\
  (!opc ops outs. symbolic_frame R (emit_inst opc ops outs)) /\
  (!name. symbolic_frame R (fresh_label name)) /\
  (!label. symbolic_frame R (new_block label)) /\
  (!n. symbolic_frame R (compile_alloc_buffer n)) /\
  (!dst src. symbolic_frame R (compile_abi_encode_static dst src)) /\
  (!dst src info asz msz len. symbolic_frame R
    (compile_abi_encode_dyn_static_loop dst src info asz msz len)) ==>
  (!dst cp ci dyn off dp.
    symbolic_frame R (compile_abi_encode_child dst cp ci dyn off dp)) /\
  (!dst src info.
    symbolic_frame R (compile_abi_encode_to_buf dst src info)) /\
  (!dst src elems so ho dp.
    symbolic_frame R
      (compile_abi_encode_complex_elems dst src elems so ho dp)) /\
  (!dst src ei asz msz len.
    symbolic_frame R (compile_abi_encode_dyn_loop dst src ei asz msz len))
Proof
  strip_tac >> ho_match_mp_tac compile_abi_encode_child_ind >>
  rpt strip_tac >>
  simp[Once compile_abi_encode_child_def, comp_ignore_bind_def] >>
  abi_frame_tac
QED

Theorem symbolic_frame_abi_decode:
  (!opc ops. symbolic_frame R (emit_op opc ops)) /\
  (!opc ops. symbolic_frame R (emit_void opc ops)) /\
  (!opc ops outs. symbolic_frame R (emit_inst opc ops outs)) /\
  (!name. symbolic_frame R (fresh_label name)) /\
  (!label. symbolic_frame R (new_block label)) /\
  (!n. symbolic_frame R (compile_alloc_buffer n)) /\
  (!src dst opc clamp. symbolic_frame R
    (compile_abi_decode_static src dst opc (\v. compile_abi_clamp_basetype v clamp))) /\
  (!bop pos. symbolic_frame R (compile_abi_dec_addr bop pos)) /\
  (!start finish hi. symbolic_frame R (compile_abi_decode_range_check start finish hi)) /\
  (!src dyn off opc bop hi. symbolic_frame R (compile_getelemptr_abi src dyn off opc bop hi)) /\
  (!opc bop elem src hi sz. symbolic_frame R
    (compile_abi_decode_dyn_elem_ptr opc bop elem src hi sz)) /\
  (!opc args. symbolic_frame R
    (case opc of CALLDATALOAD => emit_void CALLDATACOPY args
       | DLOAD => emit_void DLOADBYTES args | _ => emit_void MCOPY args)) ==>
  (!dst src opc bop hi info.
    symbolic_frame R (compile_abi_decode_to_buf dst src opc bop hi info)) /\
  (!dst src opc bop hi elems ao vo.
    symbolic_frame R
      (compile_abi_decode_complex_elems dst src opc bop hi elems ao vo)) /\
  (!dst src opc bop hi ei asz msz ip cnt.
    symbolic_frame R
      (compile_abi_decode_dyn_loop dst src opc bop hi ei asz msz ip cnt))
Proof
  strip_tac >> ho_match_mp_tac compile_abi_decode_to_buf_ind >>
  rpt strip_tac >>
  simp[Once compile_abi_decode_to_buf_def, comp_ignore_bind_def] >>
  abi_frame_tac
QED

(* The guarded callback selects one recursive branch. Keep only its
   induction hypothesis when solving the pointwise frame. *)
fun callback_frame_tac pattern =
  rpt strip_tac >>
  qpat_x_assum pattern (fn ih =>
    rpt (qpat_x_assum `!x. _` kall_tac) >> metis_tac[ih])

Theorem symbolic_frame_expr:
  (!ty. symbolic_frame R (invalid_expr_call ty)) /\
  (!cfn bfn tfn ce ty e.
    (!env arg_ty child. symbolic_frame R (cfn env arg_ty child)) /\
    (!rt arg_ty bi args. symbolic_frame R (bfn ce rt arg_ty bi args)) /\
    (!vt arg_ty tb rt args. symbolic_frame R (tfn ce vt arg_ty tb rt args)) ==>
    symbolic_frame R (compile_expr_body cfn bfn tfn ce ty e)) /\
  (!cfn ce rt ty bi args.
    (!env arg_ty child. symbolic_frame R (cfn env arg_ty child)) ==>
    symbolic_frame R (compile_builtin_dispatch_body cfn ce rt ty bi args)) /\
  (!cfn ce vt ty tb rt args.
    (!env arg_ty child. symbolic_frame R (cfn env arg_ty child)) ==>
    symbolic_frame R (compile_type_builtin_dispatch_body cfn ce vt ty tb rt args)) ==>
  (!ce ty e. symbolic_frame R (compile_expr ce ty e)) /\
  (!ce rt ty bi args. symbolic_frame R (compile_builtin_dispatch ce rt ty bi args)) /\
  (!ce vt ty tb rt args. symbolic_frame R (compile_type_builtin_dispatch ce vt ty tb rt args))
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "invalid") (CONJUNCTS_THEN2
    (mk_asm "expr") (CONJUNCTS_THEN2 (mk_asm "builtin") (mk_asm "type_builtin")))) >>
  rewrite_tac[symbolic_frame_def] >>
  ho_match_mp_tac compile_expr_raw_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >>
  once_rewrite_tac[compile_expr_raw_def] >> BETA_TAC >>
  rewrite_tac[COND_CLAUSES] >> rpt gen_tac >> strip_tac
  >~ [`compile_expr_body`] >- suspend "expr"
  >~ [`compile_builtin_dispatch_body`] >- suspend "builtin"
  >> suspend "type_builtin"
QED

Resume symbolic_frame_expr[expr]:
  asm "expr" (irule o REWRITE_RULE [symbolic_frame_def]) >>
  rpt conj_tac >> rpt gen_tac >>
  rewrite_tac[expr_child_callback_def, builtin_child_callback_def,
              type_child_callback_def] >> BETA_TAC >> TRY IF_CASES_TAC >>
  asm "invalid" (fn th => asm_simp_tac bool_ss [REWRITE_RULE [symbolic_frame_def] th])
  >~ [`compile_expr`] >- callback_frame_tac
      `!e ce ty s. _ ==> !g t. R g s t ==> _ /\ R g (SND (compile_expr ce ty e s)) _`
   >~ [`compile_builtin_dispatch`] >- callback_frame_tac
      `!args ce rt ty bi s. _ ==> !g t. R g s t ==> _ /\
        R g (SND (compile_builtin_dispatch ce rt ty bi args s)) _`
   >> callback_frame_tac
      `!args ce vt ty tb rt s. _ ==> !g t. R g s t ==> _ /\
        R g (SND (compile_type_builtin_dispatch ce vt ty tb rt args s)) _`
QED

Resume symbolic_frame_expr[builtin]:
  asm "builtin" (irule o REWRITE_RULE [symbolic_frame_def]) >>
  rpt conj_tac >> rpt gen_tac >>
  rewrite_tac[expr_child_callback_def] >> BETA_TAC >> TRY IF_CASES_TAC >>
  asm "invalid" (fn th => asm_simp_tac bool_ss [REWRITE_RULE [symbolic_frame_def] th]) >>
  callback_frame_tac
    `!e ce ty s. _ ==> !g t. R g s t ==> _ /\ R g (SND (compile_expr ce ty e s)) _`
QED

Resume symbolic_frame_expr[type_builtin]:
  asm "type_builtin" (irule o REWRITE_RULE [symbolic_frame_def]) >>
  rpt conj_tac >> rpt gen_tac >>
  rewrite_tac[expr_child_callback_def] >> BETA_TAC >> TRY IF_CASES_TAC >>
  asm "invalid" (fn th => asm_simp_tac bool_ss [REWRITE_RULE [symbolic_frame_def] th]) >>
  callback_frame_tac
    `!e ce ty s. _ ==> !g t. R g s t ==> _ /\ R g (SND (compile_expr ce ty e s)) _`
QED

Finalise symbolic_frame_expr

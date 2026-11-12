(* Fixed-byte result clamp execution, independent of byte-list semantics. *)
Theory bodyMemTbExtract32FixedClamp
Ancestors
  exprLowering exprLoweringProps
  emitHelper emitHelperProps compileEnv venomExecSemantics venomState venomInst words list rich_list

Theorem extract32_fixed_clamp_ok:
  compile_clamp_basetype x (BaseT (BytesT (Fixed m))) sa = (op,sb) /\
  fresh_vars_wrt sa s /\ eval_operand x s = SOME w /\ m <= 32 /\
  w << (8*m) = 0w ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      eval_operand op t = SOME w
Proof
  strip_tac >> Cases_on `m < 32`
  >- (gvs[compile_clamp_basetype_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def, AllCaseEqs()] >>
      `m * 8 < dimword (:256)` by (simp[dimword_def] >> decide_tac) >>
      `eval_operand (Lit (n2w (m*8))) s = SOME (n2w (m*8))` by simp[eval_operand_def] >>
      rpt (pairarg_tac >> gvs[]) >>
      rename1 `emit_void ASSERT [ok] cs'' = ((),sc)` >>
      `?t. run_inst_seq (emitted_insts sa cs') s = OK t /\
           eval_operand shifted t = SOME (w << w2n (n2w (8*m):bytes32)) /\
           fresh_vars_wrt cs' t /\
           (!a v. eval_operand a s = SOME v ==> eval_operand a t = SOME v)` by
        (qspecl_then [`SHL`, `\x y. y << w2n x`]
           (mp_tac o BETA_RULE) emit_op_pure2_correct >>
         disch_then (drule_at (Pat `emit_op`)) >>
         disch_then (qspecl_then [`n2w (8*m)`, `w`, `s`] mp_tac) >>
         simp[IgnAsm `w << _ = _`] >>
         (impl_tac >-
           (qspecl_then [`Lit (n2w (8*m))`, `op`, `n2w (8*m)`, `w`]
              mp_tac step_SHL >> simp[])) >> metis_tac[]) >>
      gvs[wordsTheory.w2n_n2w] >>
      drule_all emit_op_ISZERO_correct >> strip_tac >>
      gvs[bool_to_word_def] >>
      `(1w:bytes32) <> 0w` by simp[] >>
      drule_all emit_void_ASSERT_ok >> strip_tac >>
      imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
      `run_inst_seq (emitted_insts cs' sc) t = OK ss' /\
       sc.cs_current_insts = cs'.cs_current_insts ++ emitted_insts cs' sc` by
        (qspecl_then [`cs'`, `cs''`, `sc`, `t`, `ss'`] mp_tac
           run_inst_seq_chain >> simp[]) >>
      qexists_tac `ss'` >> reverse conj_tac >- metis_tac[] >>
      qspecl_then [`sa`, `cs'`, `sc`, `s`, `t`] mp_tac run_inst_seq_chain >> simp[]) >>
  gvs[compile_clamp_basetype_def, comp_return_def] >>
  simp[emitted_insts_def, run_inst_seq_def]
QED

Theorem extract32_fixed_clamp_revert:
  compile_clamp_basetype x (BaseT (BytesT (Fixed m))) sa = (op,sb) /\
  fresh_vars_wrt sa s /\ eval_operand x s = SOME w /\ m < 32 /\
  w << (8*m) <> 0w ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t
Proof
  strip_tac >>
  gvs[compile_clamp_basetype_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, AllCaseEqs()] >>
  `m * 8 < dimword (:256)` by (simp[dimword_def] >> decide_tac) >>
  `eval_operand (Lit (n2w (8*m))) s = SOME (n2w (8*m))` by simp[eval_operand_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rename1 `emit_void ASSERT [ok] cs'' = ((),sc)` >>
  `?t. run_inst_seq (emitted_insts sa cs') s = OK t /\
       eval_operand shifted t = SOME (w << w2n (n2w (8*m):bytes32)) /\
       fresh_vars_wrt cs' t` by
    (qspecl_then [`SHL`, `\x y. y << w2n x`]
       (mp_tac o BETA_RULE) emit_op_pure2_correct >>
     disch_then (drule_at (Pat `emit_op`)) >>
     disch_then (qspecl_then [`n2w (8*m)`, `w`, `s`] mp_tac) >>
     simp[] >>
     (impl_tac >-
       (qspecl_then [`Lit (n2w (8*m))`, `op`, `n2w (8*m)`, `w`]
          mp_tac step_SHL >> simp[])) >> metis_tac[]) >>
  gvs[wordsTheory.w2n_n2w] >>
  drule_all emit_op_ISZERO_correct >> strip_tac >>
  gvs[bool_to_word_def] >>
  drule_all emit_void_ASSERT_revert >> strip_tac >>
  imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
  `run_inst_seq (emitted_insts cs' sc) t = Abort Revert_abort ss'' /\
   sc.cs_current_insts = cs'.cs_current_insts ++ emitted_insts cs' sc` by
    (qspecl_then [`cs'`, `cs''`, `sc`, `t`, `ss'`] mp_tac
       run_inst_seq_chain >> simp[]) >>
  qexists_tac `ss''` >>
  qspecl_then [`sa`, `cs'`, `sc`, `s`, `t`] mp_tac run_inst_seq_chain >> simp[]
QED

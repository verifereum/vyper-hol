(* Compiler-side register boundaries, independent of loop execution. *)
Theory typedCopyLoopCompilerBoundaryPtr
Ancestors typedCopyLoopLayoutPtr loweringStateRelDefs freshWrites ASCIInumbers

Theorem generated_name_not_fresh_at:
  !st n. not_fresh_at st ("%" ++ toString n) <=> n < st.cs_next_var
Proof
  simp[not_fresh_at_def, toString_11] >> decide_tac
QED

Theorem generated_name_old_separation:
  !sa n p. not_fresh_at sa p /\ sa.cs_next_var <= n ==>
    p <> "%" ++ toString n
Proof
  simp[not_fresh_at_def] >> metis_tac[]
QED

Theorem typed_copy_loop_register_boundaries:
  !ce dty sty sa si se ctr lt done so doff sp dp.
    ctr = "%" ++ toString sa.cs_next_var /\
    lt = "%" ++ toString (sa.cs_next_var + 1) /\
    done = "%" ++ toString (sa.cs_next_var + 2) /\
    so = "%" ++ toString (sa.cs_next_var + 3) /\
    doff = "%" ++ toString (sa.cs_next_var + 4) /\
    sp = "%" ++ toString (sa.cs_next_var + 5) /\
    dp = "%" ++ toString (sa.cs_next_var + 6) /\
    si.cs_next_var = sa.cs_next_var + 7 /\
    compile_store_memory_typed ce (Var dp) dty (Var sp) sty si = ((),se) ==>
    ALL_DISTINCT [ctr;lt;done;so;doff;sp;dp] /\
    (!p. MEM p [ctr;lt;done;so;doff;sp;dp] ==>
      not_fresh_at si p /\ not_fresh_at se p /\
      p <> "%" ++ toString se.cs_next_var) /\
    (!p. not_fresh_at sa p ==>
      ~MEM p [ctr;lt;done;so;doff;sp;dp] /\
      not_fresh_at si p /\ not_fresh_at se p /\
      p <> "%" ++ toString se.cs_next_var)
Proof
  rpt gen_tac >> strip_tac >>
  `si.cs_next_var <= se.cs_next_var` by
    (mp_tac (cj 1 exprLoweringPropsTheory.ci_mono_typed_memory_family) >>
     disch_then (qspecl_then [`ce`, `Var dp`, `dty`, `Var sp`, `sty`, `si`] mp_tac) >>
     asm_rewrite_tac[] >> simp[exprLoweringPropsTheory.ci_mono_def]) >>
  conj_tac >- simp[toString_11] >>
  conj_tac
  >- (simp[] >> rpt strip_tac >>
      gvs[not_fresh_at_def, toString_11] >> decide_tac) >>
  rpt strip_tac
  >- (gvs[] >> qpat_x_assum `not_fresh_at sa p` mp_tac >>
      simp[not_fresh_at_def] >> strip_tac >>
      first_x_assum (qspec_then `sa.cs_next_var + 6` mp_tac) >> simp[]) 
  >- (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[])
  >- (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[])
  >> drule generated_name_old_separation >>
     disch_then (qspec_then `se.cs_next_var` mp_tac) >> simp[]
QED

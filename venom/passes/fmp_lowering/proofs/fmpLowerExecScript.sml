(* Operational boundary for the four-instruction DALLOCA expansion. *)
Theory fmpLowerExec
Ancestors
  fmpLowerDefs fmpAlignment analysisSimDefs venomExecSemantics
  venomInst venomState list words venomLayout

Theorem dalloca_expansion_exec:
  !fuel ctx s size_op sz frontier runner plus31 mask aligned out ai ni mi bi.
    eval_operand size_op s = SOME sz /\
    lookup_var runner s = SOME frontier /\
    ALL_DISTINCT [plus31;mask;aligned;runner;out] ==>
    run_insts fuel ctx
      [mk_inst ai ADD [size_op;Lit 31w] [plus31];
       mk_inst ni NOT [Lit 31w] [mask];
       mk_inst mi AND [Var plus31;Var mask] [aligned];
       mk_inst bi BUMP [Var runner;Var aligned] [out;runner]] s =
    OK (update_var runner (frontier + n2w (ceil32 (w2n sz)))
         (update_var out frontier
           (update_var aligned (n2w (ceil32 (w2n sz)))
             (update_var mask (~31w)
               (update_var plus31 (sz + 31w) s)))))
Proof
  rpt strip_tac >>
  fs[ALL_DISTINCT] >>
  pure_rewrite_tac [run_insts_def] >>
  simp[step_inst_non_invoke, mk_inst_def] >>
  simp[step_inst_base_opcode_eqs,
       exec_pure1_def, exec_pure2_def, eval_operand_def] >>
  fs[lookup_var_def] >>
  simp[lookup_var_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE, dalloca_mask_value]
QED

(* Supply equalities record the actual original-point expansion, rather than
   postulating that a handwritten sequence was produced. IDs do not affect
   straight-line arithmetic execution. *)
Theorem fmp_lower_dalloca_code:
  inst.inst_opcode = DALLOCA /\ inst.inst_operands = [size_op] /\
  inst.inst_outputs = [out] /\ fmp_lower_inst_shape infos c inst /\
  fresh_ir_var supply = (plus31,s1) /\
  fresh_ir_var s1 = (mask,s1a) /\ fresh_ir_var s1a = (aligned,s2) /\
  fresh_inst_id s2 = (ai,s3) /\ fresh_inst_id s3 = (ni,s3a) /\
  fresh_inst_id s3a = (mi,s4) /\ fresh_inst_id s4 = (bi,s5) ==>
  fmp_lower_inst infos c runner supply inst =
    SOME ([mk_inst ai ADD [size_op;Lit 31w] [plus31];
           mk_inst ni NOT [Lit 31w] [mask];
           mk_inst mi AND [Var plus31;Var mask] [aligned];
           mk_inst bi BUMP [Var runner;Var aligned] [out;runner]],s5)
Proof
  strip_tac >> simp[fmp_lower_inst_def]
QED

Theorem fmp_lower_dalloca_exec:
  inst.inst_opcode = DALLOCA /\ inst.inst_operands = [size_op] /\
  inst.inst_outputs = [out] /\ fmp_lower_inst_shape infos c inst /\
  fresh_ir_var supply = (plus31,s1) /\
  fresh_ir_var s1 = (mask,s1a) /\ fresh_ir_var s1a = (aligned,s2) /\
  fresh_inst_id s2 = (ai,s3) /\ fresh_inst_id s3 = (ni,s3a) /\
  fresh_inst_id s3a = (mi,s4) /\ fresh_inst_id s4 = (bi,s5) /\
  fmp_lower_inst infos c runner supply inst = SOME (code,supply') /\
  eval_operand size_op s = SOME sz /\ lookup_var runner s = SOME frontier /\
  ALL_DISTINCT [plus31;mask;aligned;runner;out] ==>
  run_insts fuel ctx code s =
    OK (update_var runner (frontier + n2w (ceil32 (w2n sz)))
         (update_var out frontier
           (update_var aligned (n2w (ceil32 (w2n sz)))
             (update_var mask (~31w)
               (update_var plus31 (sz + 31w) s)))))
Proof
  strip_tac >>
  drule_all fmp_lower_dalloca_code >> strip_tac >> gvs[] >>
  irule dalloca_expansion_exec >> simp[]
QED

Theorem dalloca_expansion_observables:
  eval_operand size_op s = SOME sz /\ lookup_var runner s = SOME s.vs_fmp /\
  ALL_DISTINCT [plus31;mask;aligned;runner;out] /\
  run_insts fuel ctx
      [mk_inst ai ADD [size_op;Lit 31w] [plus31];
       mk_inst ni NOT [Lit 31w] [mask];
       mk_inst mi AND [Var plus31;Var mask] [aligned];
       mk_inst bi BUMP [Var runner;Var aligned] [out;runner]] s = OK low /\
  step_inst_base (mk_inst raw_id DALLOCA [size_op] [out]) s = OK raw ==>
  lookup_var out low = lookup_var out raw /\
  lookup_var runner low = SOME raw.vs_fmp /\
  (!v. ~MEM v [plus31;mask;aligned;runner] ==>
       lookup_var v low = lookup_var v raw) /\
  (low with <|vs_vars := s.vs_vars; vs_fmp := s.vs_fmp|>) =
  (raw with <|vs_vars := s.vs_vars; vs_fmp := s.vs_fmp|>) /\
  (?n. lookup_var aligned low = SOME n /\ w2n n MOD 32 = 0)
Proof
  strip_tac >> drule_all dalloca_expansion_exec >> strip_tac >> gvs[] >>
  gvs[step_inst_base_opcode_eqs, mk_inst_def, eval_operand_def] >>
  fs[ALL_DISTINCT] >>
  simp[lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  qspec_then `sz` mp_tac dalloca_mask_aligned >>
  simp[dalloca_mask_value]
QED

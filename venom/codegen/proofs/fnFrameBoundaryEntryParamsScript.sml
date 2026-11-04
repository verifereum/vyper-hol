Theory fnFrameBoundaryEntryParams
Ancestors
  frameRel frameViewFacts stackPlanGen stackPlanTypes stackModel
  callLayoutDefs venomExecSemantics venomState venomInst list rich_list
  arithmetic words

(* Installing the symbolic parameter names emits no code. *)
Theorem parameter_stack_fold:
  !insts ps.
    FOLDL (\s inst. s with ps_stack :=
      stack_push (Var (HD inst.inst_outputs)) s.ps_stack) ps insts =
    ps with ps_stack := ps.ps_stack ++
      MAP (\inst. Var (HD inst.inst_outputs)) insts
Proof
  Induct >> simp[stack_push_def, SNOC_APPEND] >>
  rpt gen_tac >> rewrite_tac[GSYM APPEND_ASSOC, APPEND]
QED

(* A compact diagnostic family: canonical shape does not bound its length. *)
Theorem canonical_param_genlist:
  !n k names.
    canonical_entry_params_from k
      (GENLIST (\j. mk_inst (k+j) PARAM [Lit (n2w (k+j))]
                       [names (k+j)]) n)
Proof
  Induct >> simp[GENLIST_CONS, canonical_entry_params_from_def,
                param_inst_at_def, mk_inst_def, is_param_opcode_def,
                combinTheory.o_DEF, ADD_CLAUSES] >>
  rpt gen_tac >> first_x_assum (qspecl_then [`SUC k`, `names`] mp_tac) >>
  simp[mk_inst_def, ADD_CLAUSES] >> disch_tac >>
  qmatch_asmsub_abbrev_tac `GENLIST f n` >>
  qmatch_goalsub_abbrev_tac `GENLIST g n` >>
  `f = g` by simp[Abbr `f`, Abbr `g`, FUN_EQ_THM, ADD_COMM] >>
  gvs[]
QED

(* Closed arithmetic discriminator only, NOT a counterexample to the task. *)
Theorem param_index_wrap_discriminator:
  w2n (n2w (dimword (:256)) : 256 word) = 0 /\
  dimword (:256) <> 0
Proof
  simp[w2n_n2w, dimword_def] >> EVAL_TAC
QED

Theorem wrapped_param_reads_first:
  !s id out.
    s.vs_params <> [] ==>
    step_inst_base
      (mk_inst id PARAM [Lit (n2w (dimword (:256)))] [out]) s =
    OK (update_var out (HD s.vs_params) s)
Proof
  rpt gen_tac >> Cases_on `s.vs_params` >>
  simp[step_inst_base_def, mk_inst_def, w2n_n2w]
QED

(* A syntactic data dependency certificate, with a semantic invariant carried
   only across instructions which actually execute successfully. *)
Theory bodyPtrWordBuiltinsScalarSequence
Ancestors fragGasSeqPtr fragExec exprLoweringProps venomExecSemantics
  venomInst venomState list pred_set instIdxIndep

Theorem word_sequence_dependency_cons:
  (!pre i post x. h::xs = pre ++ i::post /\ MEM (Var x) i.inst_operands ==>
      x IN A UNION set (FLAT (MAP (\j. j.inst_outputs) pre))) ==>
  (!x. MEM (Var x) h.inst_operands ==> x IN A) /\
  (!pre i post x. xs = pre ++ i::post /\ MEM (Var x) i.inst_operands ==>
      x IN (A UNION set h.inst_outputs) UNION
        set (FLAT (MAP (\j. j.inst_outputs) pre)))
Proof
  strip_tac >> conj_tac
  >- (rpt strip_tac >>
      first_x_assum (qspecl_then [`[]`, `h`, `xs`, `x`] mp_tac) >> simp[]) >>
  rpt strip_tac >>
  first_x_assum (qspecl_then [`h::pre`, `i`, `post`, `x`] mp_tac) >>
  simp[UNION_ASSOC] >> metis_tac[]
QED

Theorem word_sequence_normal_cursor:
  EVERY (\i. ~is_terminator i.inst_opcode) xs /\
  (!u k. Q u ==> Q (u with vs_inst_idx := k)) /\
  (?n. !t. run_inst_seq xs (s with vs_inst_idx := n) = OK t ==> Q t) ==>
  !t. run_inst_seq xs s = OK t ==> Q t
Proof
  rpt strip_tac >>
  `Q (t with vs_inst_idx := n)` by
    (first_x_assum irule >> simp[run_inst_seq_inst_idx, exec_result_map_def]) >>
  qpat_x_assum `!u k. _` (qspecl_then
    [`t with vs_inst_idx := n`, `t.vs_inst_idx`] mp_tac) >> simp[]
QED

Theorem word_scalar_sequence:
  !xs A G tn s.
  EVERY (\i. ~is_terminator i.inst_opcode) xs /\ P A G tn s /\
  (!B H th u k. P B H th u ==> P B H th (u with vs_inst_idx := k)) /\
  (!pre i post x. xs = pre ++ i::post /\ MEM (Var x) i.inst_operands ==>
      x IN A UNION set (FLAT (MAP (\j. j.inst_outputs) pre))) /\
  (!i B H th u. MEM i xs /\ P B H th u /\
      (!x. MEM (Var x) i.inst_operands ==> x IN B) ==>
      ptr_inst_ok D lo 0 ctx fn H th i u) /\
  (!i B H th u v. MEM i xs /\ P B H th u /\
      (!x. MEM (Var x) i.inst_operands ==> x IN B) /\
      step_inst_base i u = OK v ==>
      P (B UNION set i.inst_outputs) (step_prov PG H i v)
        (step_taint i u v th) v) ==>
  ?H th. inst_seq_ptr D lo ctx fn PG G tn xs s H th /\
    (!t. run_inst_seq xs s = OK t ==>
      P (A UNION set (FLAT (MAP (\i. i.inst_outputs) xs))) H th t)
Proof
  Induct_on `xs`
  >- (simp[inst_seq_ptr_def, run_inst_seq_def] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  drule word_sequence_dependency_cons >> strip_tac >>
  `ptr_inst_ok D lo 0 ctx fn G tn h s` by metis_tac[MEM] >>
  Cases_on `step_inst_base h s` >>
  simp[Once inst_seq_ptr_def, Once run_inst_seq_def] >>
  `P (A UNION set h.inst_outputs) (step_prov PG G h v)
     (step_taint h s v tn) v` by metis_tac[MEM] >>
  qpat_x_assum `!A G tn s. EVERY _ xs /\ _ ==> _` (qspecl_then
    [`A UNION set h.inst_outputs`, `step_prov PG G h v`,
     `step_taint h s v tn`, `v with vs_inst_idx := SUC s.vs_inst_idx`] mp_tac) >>
  impl_tac
  >- (gvs[MEM] >> rpt conj_tac >> rpt gen_tac >> strip_tac >>
      first_x_assum irule >> simp[] >> metis_tac[]) >>
  strip_tac >> qexistsl_tac [`H`, `th`] >> simp[] >>
  ho_match_mp_tac word_sequence_normal_cursor >>
  conj_tac >- gvs[] >> conj_tac >- metis_tac[] >>
  qexists_tac `SUC s.vs_inst_idx` >> gvs[UNION_ASSOC]
QED

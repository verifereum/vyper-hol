(* Proof-only chronological chunks for the custom-error encoder's control flow. *)
Theory stmtSimCustomErrorControl
Ancestors
  compileEnv venomInst venomExecSemantics list rich_list pred_set

Definition ce_prepend_def:
  (ce_prepend p [] = []) /\
  (ce_prepend p ((l,is)::cs) = (l,p ++ is)::cs)
End

Definition ce_block_def:
  ce_block (l,is) = <|bb_label := l; bb_instructions := is|>
End

Definition ce_chunks_def:
  ce_chunks a b C <=>
    C <> [] /\ FST (HD C) = a.cs_current_bb /\
    FST (LAST C) = b.cs_current_bb /\
    b.cs_blocks = REVERSE (MAP ce_block (FRONT (ce_prepend a.cs_current_insts C))) ++
      a.cs_blocks /\
    b.cs_current_insts = SND (LAST (ce_prepend a.cs_current_insts C))
End

Definition ce_splice_def:
  (ce_splice [] B = B) /\
  (ce_splice [x] [] = [x]) /\
  (ce_splice [x] ((l,is)::bs) = (FST x,SND x ++ is)::bs) /\
  (ce_splice (x::y::xs) B = x::ce_splice (y::xs) B)
End

Definition ce_normal_def:
  ce_normal is <=> EVERY (\i. ~is_terminator i.inst_opcode /\
    i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE) is
End

Definition ce_end_def:
  ce_end k is <=> ?pre i. is = pre ++ [i] /\ ce_normal pre /\
    ((?l. i.inst_opcode = JMP /\ i.inst_operands = [Label l] /\ l IN k) \/
     (?cond yes no. i.inst_opcode = JNZ /\
       i.inst_operands = [cond; Label yes; Label no] /\ yes IN k /\ no IN k))
End

Definition ce_revert_def:
  ce_revert is <=> ?pre i. is = pre ++ [i] /\ ce_normal pre /\
    i.inst_opcode = REVERT
End

Definition ce_open_to_def:
  ce_open_to k C <=> C <> [] /\
    EVERY (\c. ce_end (k UNION set (MAP FST (TL C))) (SND c)) (FRONT C) /\
    ce_normal (SND (LAST C))
End

Definition ce_open_def:
  ce_open C <=> ce_open_to {} C
End

Definition ce_closed_def:
  ce_closed C <=> C <> [] /\
    EVERY (\c. ce_end (set (MAP FST (TL C))) (SND c)) (FRONT C) /\
    ce_revert (SND (LAST C))
End

Theorem ce_normal_append[simp]:
  ce_normal (xs ++ ys) <=> ce_normal xs /\ ce_normal ys
Proof
  simp[ce_normal_def, EVERY_APPEND]
QED

Theorem ce_normal_nil[simp]:
  ce_normal []
Proof
  simp[ce_normal_def]
QED

Theorem ce_end_mono:
  !k L xs. ce_end k xs ==> k SUBSET L ==> ce_end L xs
Proof
  rw[ce_end_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem ce_end_prepend:
  !k xs ys. ce_normal xs /\ ce_end k ys ==> ce_end k (xs ++ ys)
Proof
  rw[ce_end_def] >> qexistsl_tac [`xs ++ pre`, `i`] >> simp[APPEND_ASSOC]
QED

Theorem ce_revert_prepend:
  ce_normal xs /\ ce_revert ys ==> ce_revert (xs ++ ys)
Proof
  rw[ce_revert_def] >> qexistsl_tac [`xs ++ pre`, `i`] >> simp[APPEND_ASSOC]
QED

Theorem ce_chunks_singleton:
  ce_chunks a b [(l,is)] <=>
    l = a.cs_current_bb /\ l = b.cs_current_bb /\
    b.cs_blocks = a.cs_blocks /\
    b.cs_current_insts = a.cs_current_insts ++ is
Proof
  simp[ce_chunks_def, ce_prepend_def]
QED

Theorem ce_chunks_return:
  comp_return v a = (out,b) ==> ce_chunks a b [(a.cs_current_bb,[])]
Proof
  simp[comp_return_def, ce_chunks_singleton]
QED

Theorem ce_chunks_cons:
  ce_chunks a b ((l,is)::(m,js)::cs) <=>
    l = a.cs_current_bb /\
    ce_chunks (a with <|cs_current_bb := m; cs_current_insts := [];
      cs_blocks := ce_block (l,a.cs_current_insts ++ is)::a.cs_blocks|>)
      b ((m,js)::cs)
Proof
  Cases_on `cs` >> simp[ce_chunks_def, ce_prepend_def, ce_block_def, FRONT_DEF,
    LAST_DEF, REVERSE_APPEND, APPEND_ASSOC]
QED

Theorem ce_chunks_prepend:
  ce_chunks b c ((l,js)::cs) /\ b.cs_current_bb = a.cs_current_bb /\
  b.cs_blocks = a.cs_blocks /\ b.cs_current_insts = a.cs_current_insts ++ is ==>
  ce_chunks a c ((l,is ++ js)::cs)
Proof
  Cases_on `cs` >> simp[ce_chunks_def, ce_prepend_def, APPEND_ASSOC] >> metis_tac[]
QED

Theorem ce_chunks_splice:
  !A a b B c. ce_chunks a b A /\ ce_chunks b c B ==>
    ce_chunks a c (ce_splice A B)
Proof
  Induct_on `A` >- simp[ce_chunks_def] >>
  Cases_on `h` >> Cases_on `A`
  >- (Cases_on `B` >- simp[ce_chunks_def] >>
      Cases_on `h` >> simp[ce_chunks_singleton, ce_splice_def] >>
      Cases_on `t` >> rpt strip_tac >> gvs[ce_chunks_def, ce_prepend_def, APPEND_ASSOC]) >>
  Cases_on `h` >> simp[ce_chunks_cons, ce_splice_def] >>
  rpt strip_tac >> gvs[] >> first_x_assum drule_all >> strip_tac >>
  qmatch_asmsub_abbrev_tac `ce_chunks mid c D` >>
  Cases_on `D` >- gvs[ce_chunks_def] >> Cases_on `h` >>
  rename1 `ce_chunks mid c ((ll,ii)::rest)` >>
  `ll = mid.cs_current_bb` by (fs[ce_chunks_def]) >>
  fs[Abbr `mid`] >> gvs[ce_chunks_cons]
QED

Theorem ce_splice_append:
  !xs x l is bs.
    ce_splice (xs ++ [x]) ((l,is)::bs) =
      xs ++ (FST x,SND x ++ is)::bs
Proof
  Induct >> simp[ce_splice_def] >> Cases_on `xs` >> simp[ce_splice_def] >> gvs[]
QED

Theorem ce_open_to_mono:
  !k L C. ce_open_to k C /\ k SUBSET L ==> ce_open_to L C
Proof
  rw[ce_open_to_def, EVERY_MEM] >> first_x_assum drule >> strip_tac >>
  qmatch_asmsub_abbrev_tac `ce_end targets (SND c)` >>
  irule ce_end_mono >> qexists_tac `targets` >> simp[] >>
  gvs[Abbr `targets`, SUBSET_DEF] >> metis_tac[]
QED

Theorem ce_splice_labels:
  A <> [] /\ B <> [] ==>
    set (MAP FST (TL (ce_splice A B))) =
      set (MAP FST (TL A)) UNION set (MAP FST (TL B))
Proof
  Cases_on `A` using SNOC_CASES >> simp[] >>
  Cases_on `B` >> simp[] >> Cases_on `h` >>
  simp[SNOC_APPEND, ce_splice_append] >> Cases_on `l` >> simp[] >> SET_TAC[]
QED

Theorem ce_every_end_mono[local]:
  !cs k L. k SUBSET L /\ EVERY (\c. ce_end k (SND c)) cs ==>
    EVERY (\c. ce_end L (SND c)) cs
Proof
  Induct >> simp[] >> metis_tac[ce_end_mono]
QED

Theorem ce_end_union_left[local]:
  !k A B is. ce_end (k UNION A) is ==> ce_end (k UNION (A UNION B)) is
Proof
  rpt strip_tac >> irule ce_end_mono >> qexists_tac `k UNION A` >>
  simp[] >> SET_TAC[]
QED

Theorem ce_end_union_right[local]:
  !k A B is. ce_end (k UNION B) is ==> ce_end (k UNION (A UNION B)) is
Proof
  rpt strip_tac >> irule ce_end_mono >> qexists_tac `k UNION B` >>
  simp[] >> SET_TAC[]
QED

Theorem ce_open_to_splice:
  !k A B. ce_open_to k A /\ ce_open_to k B ==>
    ce_open_to k (ce_splice A B)
Proof
  rpt gen_tac >> strip_tac >>
  `A <> [] /\ B <> []` by fs[ce_open_to_def] >>
  `set (MAP FST (TL (ce_splice A B))) =
    set (MAP FST (TL A)) UNION set (MAP FST (TL B))` by
    metis_tac[ce_splice_labels] >>
  qabbrev_tac `targets = k UNION (set (MAP FST (TL A)) UNION set (MAP FST (TL B)))` >>
  `EVERY (\c. ce_end targets (SND c)) (FRONT A)` by
    (irule ce_every_end_mono >> qexists_tac `k UNION set (MAP FST (TL A))` >>
     conj_tac >- fs[ce_open_to_def] >> simp[Abbr `targets`] >> SET_TAC[]) >>
  `EVERY (\c. ce_end targets (SND c)) (FRONT B)` by
    (irule ce_every_end_mono >> qexists_tac `k UNION set (MAP FST (TL B))` >>
     conj_tac >- fs[ce_open_to_def] >> simp[Abbr `targets`] >> SET_TAC[]) >>
  `ce_normal (SND (LAST A)) /\ ce_normal (SND (LAST B))` by fs[ce_open_to_def] >>
  simp[ce_open_to_def] >>
  `k UNION set (MAP FST (TL (ce_splice A B))) = targets` by simp[Abbr `targets`] >>
  asm_rewrite_tac[] >>
  Cases_on `A` using SNOC_CASES >- gvs[] >>
  Cases_on `B` >- gvs[] >> Cases_on `x` >> Cases_on `h` >>
  gvs[SNOC_APPEND, ce_splice_append, FRONT_APPEND, LAST_APPEND, EVERY_APPEND] >>
  Cases_on `t` >> gvs[FRONT_DEF, LAST_DEF, ce_end_prepend]
QED

Theorem ce_closed_splice:
  ce_open A /\ ce_closed B ==> ce_closed (ce_splice A B)
Proof
  strip_tac >>
  `A <> [] /\ B <> []` by fs[ce_open_def, ce_open_to_def, ce_closed_def] >>
  `set (MAP FST (TL (ce_splice A B))) =
    set (MAP FST (TL A)) UNION set (MAP FST (TL B))` by
    metis_tac[ce_splice_labels] >>
  qabbrev_tac `targets = set (MAP FST (TL A)) UNION set (MAP FST (TL B))` >>
  `EVERY (\c. ce_end targets (SND c)) (FRONT A)` by
    (irule ce_every_end_mono >> qexists_tac `set (MAP FST (TL A))` >>
     conj_tac >- fs[ce_open_def, ce_open_to_def] >>
     simp[Abbr `targets`]) >>
  `EVERY (\c. ce_end targets (SND c)) (FRONT B)` by
    (irule ce_every_end_mono >> qexists_tac `set (MAP FST (TL B))` >>
     conj_tac >- fs[ce_closed_def] >> simp[Abbr `targets`]) >>
  `ce_normal (SND (LAST A)) /\ ce_revert (SND (LAST B))` by
    fs[ce_open_def, ce_open_to_def, ce_closed_def] >>
  simp[ce_closed_def] >>
  `set (MAP FST (TL (ce_splice A B))) = targets` by simp[Abbr `targets`] >>
  asm_rewrite_tac[] >>
  Cases_on `A` using SNOC_CASES >- gvs[] >>
  Cases_on `B` >- gvs[] >> Cases_on `x` >> Cases_on `h` >>
  gvs[SNOC_APPEND, ce_splice_append, FRONT_APPEND, LAST_APPEND, EVERY_APPEND] >>
  Cases_on `t` >> gvs[FRONT_DEF, LAST_DEF, ce_end_prepend, ce_revert_prepend]
QED

Theorem ce_open_singleton[simp]:
  ce_open [(l,is)] <=> ce_normal is
Proof
  simp[ce_open_def, ce_open_to_def]
QED

Theorem ce_open_splice:
  ce_open A /\ ce_open B ==> ce_open (ce_splice A B)
Proof
  simp[ce_open_def, ce_open_to_splice]
QED

Theorem ce_chunks_emit:
  emit i a = ((),b) ==> ce_chunks a b [(a.cs_current_bb,[i])]
Proof
  rw[emit_def, ce_chunks_singleton] >> simp[]
QED

Theorem ce_emit_open:
  emit i a = ((),b) /\ ~is_terminator i.inst_opcode /\
  i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE ==>
  ce_chunks a b [(a.cs_current_bb,[i])] /\ ce_open [(a.cs_current_bb,[i])]
Proof
  rw[emit_def, ce_chunks_singleton, ce_normal_def] >> simp[]
QED

Theorem ce_loop_layout:
  !child start hdr bodylab done hp bp jump branch back.
  ce_open_to {hdr;bodylab;done} child /\ FST (HD child) = bodylab /\
  ce_normal hp /\ ce_normal bp /\
  jump.inst_opcode = JMP /\ jump.inst_operands = [Label hdr] /\
  branch.inst_opcode = JNZ /\
  (?cond. branch.inst_operands = [cond;Label done;Label bodylab]) /\
  back.inst_opcode = JMP /\ back.inst_operands = [Label hdr] ==>
  ce_open ([(start,[jump]);(hdr,hp ++ [branch])] ++
    ce_splice (ce_prepend bp child) [(FST (LAST child),[back]);(done,[])])
Proof
  rpt gen_tac >> strip_tac >>
  `child <> []` by fs[ce_open_to_def] >>
  qabbrev_tac `targets = {hdr;bodylab;done} UNION set (MAP FST (TL child))` >>
  `EVERY (\c. ce_end targets (SND c)) (FRONT child)` by
    fs[ce_open_to_def, Abbr `targets`] >>
  `ce_normal (SND (LAST child))` by fs[ce_open_to_def] >>
  Cases_on `child` using SNOC_CASES >- gvs[] >>
  Cases_on `x` >> rename1 `SNOC (cl,ci) cs` >>
  Cases_on `cs` >> gvs[SNOC_APPEND, ce_prepend_def, ce_splice_append,
    ce_splice_def, ce_open_def, ce_open_to_def, FRONT_APPEND, LAST_APPEND,
    EVERY_APPEND, ce_end_prepend]
  >- (rpt conj_tac >> rw[ce_end_def] >> simp[Abbr `targets`])
  >> Cases_on `h` >>
  Cases_on `t` >>
  gvs[ce_prepend_def, ce_splice_def, ce_splice_append,
    FRONT_APPEND, LAST_APPEND, EVERY_APPEND]
  >- (`targets = {hdr;q;cl;done}` by (simp[Abbr `targets`] >> SET_TAC[]) >>
      gvs[] >> conj_tac >- simp[ce_end_def] >>
      conj_tac >- simp[ce_end_def] >>
      conj_tac >- simp[ce_end_prepend] >> simp[ce_end_def]) >>
  `ce_splice (h::(t' ++ [(cl,ci)])) [(cl,[back]);(done,[])] =
    h::(t' ++ [(cl,ci ++ [back]);(done,[])])` by
    (qspec_then `h::t'` mp_tac ce_splice_append >>
     disch_then (qspecl_then [`(cl,ci)`, `cl`, `[back]`, `[(done,[])]`] mp_tac) >>
     simp[]) >>
  gvs[FRONT_DEF, LAST_DEF, FRONT_APPEND, LAST_APPEND, EVERY_APPEND] >>
  `hdr INSERT q INSERT FST h INSERT set (MAP FST t') UNION {cl;done} = targets` by
    (simp[Abbr `targets`] >> SET_TAC[]) >>
  asm_rewrite_tac[] >>
  conj_tac >- simp[ce_end_def, Abbr `targets`] >>
  conj_tac >- simp[ce_end_def, Abbr `targets`] >>
  simp[ce_end_prepend] >> simp[ce_end_def, Abbr `targets`]
QED

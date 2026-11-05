Theory makeSsaCurrentStaticGraph
Ancestors makeSsaCurrentStaticDemandProbe makeSsaCurrentFinalWriteSlots
  list rich_list alist

Definition current_graph_inst_subst_def:
  current_graph_inst_subst inst op =
    case op of
      Var v => (case ALOOKUP (REVERSE (ZIP (inst.inst_outputs,
                      GENLIST I (LENGTH inst.inst_outputs)))) v of
          NONE => CurrentStaticRead op
        | SOME k => CurrentStaticProduced k)
    | _ => CurrentStaticRead op
End

Theorem current_graph_reverse_zip_absent[local]:
  !xs ys v. LENGTH xs = LENGTH ys /\ ~MEM v xs ==>
    ALOOKUP (REVERSE (ZIP (xs,ys))) v = NONE
Proof
  Induct >> Cases_on `ys` >> simp[] >> rpt strip_tac >>
  simp[REVERSE_DEF, ALOOKUP_APPEND] >> first_x_assum irule >> simp[]
QED

Theorem current_graph_reverse_zip_last[local]:
  !xs ys k v. LENGTH xs = LENGTH ys /\ k < LENGTH xs /\
    EL k xs = v /\
    (!r. k < r /\ r < LENGTH xs ==> EL r xs <> v) ==>
    ALOOKUP (REVERSE (ZIP (xs,ys))) v = SOME (EL k ys)
Proof
  Induct >- simp[] >> Cases_on `ys` >- simp[] >>
  rpt gen_tac >> strip_tac >> Cases_on `k`
  >- (gvs[] >> rename1 `ALOOKUP (REVERSE (ZIP (xs,t)) ++ [(head,value)]) head = SOME value` >>
      `~MEM head xs` by
        (simp[MEM_EL] >> rpt strip_tac >>
         qpat_x_assum `!r. 0 < r /\ _ ==> _` (qspec_then `SUC n` mp_tac) >> simp[]) >>
      simp[REVERSE_DEF, ALOOKUP_APPEND, current_graph_reverse_zip_absent]) >>
  gvs[] >>
  `ALOOKUP (REVERSE (ZIP (xs,t))) (EL n xs) = SOME (EL n t)` by
    (first_x_assum irule >> simp[] >> rpt strip_tac >>
     first_x_assum (qspec_then `SUC r` mp_tac) >> simp[]) >>
  simp[REVERSE_DEF, ALOOKUP_APPEND]
QED

Theorem current_graph_inst_subst_absent:
  ~MEM v inst.inst_outputs ==>
  current_graph_inst_subst inst (Var v) = CurrentStaticRead (Var v)
Proof
  simp[current_graph_inst_subst_def, current_graph_reverse_zip_absent]
QED

Theorem current_graph_inst_subst_last:
  k < LENGTH inst.inst_outputs /\ EL k inst.inst_outputs = v /\
  (!r. k < r /\ r < LENGTH inst.inst_outputs ==> EL r inst.inst_outputs <> v) ==>
  current_graph_inst_subst inst (Var v) = CurrentStaticProduced k
Proof
  strip_tac >>
  `ALOOKUP (REVERSE (ZIP (inst.inst_outputs,
     GENLIST I (LENGTH inst.inst_outputs)))) v = SOME k` by
    (`ALOOKUP (REVERSE (ZIP (inst.inst_outputs,
        GENLIST I (LENGTH inst.inst_outputs)))) v =
        SOME (EL k (GENLIST I (LENGTH inst.inst_outputs)))` suffices_by
          simp[EL_GENLIST] >>
     irule current_graph_reverse_zip_last >> simp[]) >>
  simp[current_graph_inst_subst_def]
QED

Theorem current_graph_inst_subst_final_slots:
  current_table_final_slots table a.inst_outputs b.inst_outputs /\
  MEM (v,n) table ==>
  ((current_graph_inst_subst a (Var v) = CurrentStaticRead (Var v) /\
    current_graph_inst_subst b (Var n) = CurrentStaticRead (Var n)) \/
   ?k. current_graph_inst_subst a (Var v) = CurrentStaticProduced k /\
       current_graph_inst_subst b (Var n) = CurrentStaticProduced k)
Proof
  simp[current_table_final_slots_def] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac
  >- (disj1_tac >> simp[current_graph_inst_subst_absent]) >>
  disj2_tac >> qexists_tac `j` >>
  conj_tac >> irule current_graph_inst_subst_last >> simp[]
QED

Theorem current_graph_inst_subst_duplicate_regression:
  current_graph_inst_subst (current_probe_inst 0 ASSIGN [] ["x";"x"])
    (Var "x") = CurrentStaticProduced 1 /\
  current_static_phi_subst "E"
    [current_probe_inst 0 PHI [Label "E";Var "a"] ["x"];
     current_probe_inst 1 PHI [Label "E";Var "b"] ["x"]]
    (Var "x") = SOME (CurrentStaticRead (Var "a"))
Proof
  EVAL_TAC
QED

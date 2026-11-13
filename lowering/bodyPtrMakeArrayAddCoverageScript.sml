(* Coverage of the actual destination ADD, even when its offset is zero. *)
Theory bodyPtrMakeArrayAddCoverage
Ancestors
  bodyPtrMakeArrayAdd ptrCoverage bodyPtrDefs ptrDiscipline
  venomInst venomState words finite_map

Theorem add_destination_coverage:
  !G tn root s total a base cap off n PG id out.
  ptr_covers G tn root s total /\ lookup_var root s = SOME a /\
  FLOOKUP G root = SOME (base,cap) /\ base + cap <= dimword(:256) /\
  off < total /\ off + n <= total ==>
  ptr_covers
    (step_prov PG G (mk_inst id ADD [Var root; Lit (n2w off)] [out])
      (update_var out (a + n2w off) s))
    (step_taint (mk_inst id ADD [Var root; Lit (n2w off)] [out]) s
      (update_var out (a + n2w off) s) tn)
    out ((update_var out (a + n2w off) s) with
      vs_inst_idx := SUC s.vs_inst_idx) n
Proof
  rpt gen_tac >> strip_tac >> irule ptr_covers_offset >>
  simp[typedCopyPtrTheory.copy_len_binop_ghost_frame] >>
  qpat_assum `ptr_covers _ _ _ _ _` (irule_at Any) >>
  qpat_assum `FLOOKUP G root = _` (irule_at Any) >>
  qexistsl_tac [`a`, `off`] >>
  simp[step_prov_def, set_prov_def, out_prov_def,
       first_prov_def, op_prov_def, mk_inst_def,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

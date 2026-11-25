(* Scalar control edges for the linked Array loop.  The machine path is
   deliberately kept separate from the capture and round contracts. *)
Theory bodyForArrayControlMods
Ancestors
  bodyForArrayHeaderMods bodyForRoundsBindMods bodyFullForArrayRound
  loweringPosts stmtSimProps vyperStorageTrace vyperStorageFootprint
  fragExec venomState venomInst arithmetic words list finite_map

(* The condition register is the length exactly at the empty suffix. *)
Theorem for_array_control_nil_mods:
  for_array_header_mods mods DF lo d ctx func cenv cx env id st0
    (es0,sa,s0,G0,tn0) (em,saExpr,saLen,u,tu) item
    vs (base_op,bw,len_op,idx) cond_lbl Route H [] ee G tn t ==>
  lookup_var idx t = eval_operand len_op t
Proof
  strip_tac >> drule for_array_header_test_mods >> simp[]
QED

(* A nonempty suffix is the strict side of the same word comparison. *)
Theorem for_array_control_cons_mods:
  for_array_header_mods mods DF lo d ctx func cenv cx env id st0
    (es0,sa,s0,G0,tn0) (em,saExpr,saLen,u,tu) item
    vs (base_op,bw,len_op,idx) cond_lbl Route H (a::rs) ee G tn t ==>
  ?k. k < LENGTH vs /\ a = EL k vs /\
      rs = DROP (SUC k) vs /\
      lookup_var idx t = SOME (n2w k) /\
      lookup_var idx t <> eval_operand len_op t
Proof
  strip_tac >>
  qhdtm_x_assum `for_array_header_mods`
    (strip_assume_tac o REWRITE_RULE [for_array_header_mods_def]) >>
  drule for_array_header_cons_mods >> strip_tac >>
  qexists_tac `k` >> simp[] >>
  `k < LENGTH vs` by first_assum ACCEPT_TAC >>
  simp[eval_operand_def,lookup_var_def] >> decide_tac
QED

(* The increment edge writes the next scalar index and leaves all other
   variables unchanged.  The bound is kept explicit for callers which use
   the suffix contract. *)
Theorem for_array_control_increment_mods:
  k < LENGTH vs /\ LENGTH vs < dimword (:256) /\
  lookup_var idx t = SOME (n2w k) ==>
  lookup_var idx (update_var idx (n2w (SUC k)) t) = SOME (n2w (SUC k)) /\
  (!x. x <> idx ==>
       lookup_var x (update_var idx (n2w (SUC k)) t) = lookup_var x t)
Proof
  strip_tac >>
  conj_tac >- simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  rpt gen_tac >> disch_tac >>
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

(* The index contract is re-established after the back-edge. *)
Theorem for_array_control_increment_header_mods:
  for_array_index_mods vs idx (a::rs) t /\
  k < LENGTH vs /\ a = EL k vs /\ rs = DROP (SUC k) vs ==>
  for_array_index_mods vs idx rs
    (update_var idx (n2w (SUC k)) t)
Proof
  strip_tac >>
  simp[for_array_index_mods_def] >>
  qexists_tac `SUC k` >>
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

(* The outer exit post is independent of whether the condition was reached
   from the initial header or from an increment. *)
Theorem for_array_control_done_mods:
  for_array_done_mods DF lo d ctx func cenv cx lctx sa sb es0 s0 G0 tn0
    H ee G tn t ==>
  for_array_outer_frame_mods ctx func cenv sa es0 s0 G0 tn0 ee G tn t
Proof
  strip_tac >> drule for_array_done_outer_mods >> strip_tac >>
  first_assum ACCEPT_TAC
QED

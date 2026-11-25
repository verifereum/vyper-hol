(* Preserve the two saved Slice words across evaluation of the address. *)
Theory bodySliceExternalSavedMods
Ancestors
  bodyFullPostsMods bodyPtrDefs exprBopSimProps loweringPosts loweringShapeDefs
  compileEnv valueEncoding ptrDiscipline

val saved = ``\x y s2 t2 G2 tn2 v1 v2.
  eval_operand x t2 = SOME (val_to_w256 v1) /\
  eval_operand y t2 = SOME (val_to_w256 v2) /\
  op_prov G2 x = NONE /\ op_prov G2 y = NONE /\
  op_taint tn2 x = {} /\ op_taint tn2 y = {} /\
  (!q. x = Var q ==> not_fresh_at s2 q) /\
  (!q. y = Var q ==> not_fresh_at s2 q) /\
  (!l. x <> Label l) /\ (!l. y <> Label l)``;

Triviality slice_external_operand_kept:
  (!q w. not_fresh_at s2 q /\ lookup_var q t2 = SOME w ==>
         lookup_var q z = SOME w) /\
  (!q. not_fresh_at s2 q ==>
       FLOOKUP G3 q = FLOOKUP G2 q /\ op_taint tn3 (Var q) = op_taint tn2 (Var q)) /\
  s2.cs_next_var <= s3.cs_next_var /\
  (!q. op = Var q ==> not_fresh_at s2 q) /\ (!l. op <> Label l) /\
  eval_operand op t2 = SOME w /\ op_prov G2 op = NONE /\ op_taint tn2 op = {} ==>
  eval_operand op z = SOME w /\ op_prov G3 op = NONE /\ op_taint tn3 op = {} /\
  (!q. op = Var q ==> not_fresh_at s3 q)
Proof
  strip_tac >> conj_tac
  >- (irule eval_operand_frame >> simp[] >> qexistsl_tac [`s2`,`t2`] >> simp[]) >>
  `!q. op = Var q ==> not_fresh_at s3 q` by
    (rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
     qexists_tac `s2` >> simp[]) >>
  simp[] >> Cases_on `op` >> fs[op_prov_def,op_taint_def] >>
  first_x_assum (drule_then strip_assume_tac) >> fs[op_taint_def]
QED

Theorem slice_external_saved_mods:
  ^saved x y s2 t2 G2 tn2 v1 v2 /\
  expr_post_mods H ctx func cenv cx addr fin s2 s3 t2 ae av aop z /\
  ghost_kept_at lo cenv fin s2 G2 tn2 t2 G3 tn3 /\
  s2.cs_next_var <= s3.cs_next_var ==>
  ^saved x y s3 z G3 tn3 v1 v2
Proof
  BETA_TAC >> strip_tac >>
  `!q w. not_fresh_at s2 q /\ lookup_var q t2 = SOME w ==>
         lookup_var q z = SOME w` by fs[expr_post_mods_def,expr_post_def] >>
  `!q. not_fresh_at s2 q ==>
       FLOOKUP G3 q = FLOOKUP G2 q /\ op_taint tn3 (Var q) = op_taint tn2 (Var q)` by
    fs[ghost_kept_at_def] >>
  `eval_operand x z = SOME (val_to_w256 v1) /\ op_prov G3 x = NONE /\
   op_taint tn3 x = {} /\ (!q. x = Var q ==> not_fresh_at s3 q)` by
    (irule slice_external_operand_kept >> simp[] >>
     qexistsl_tac [`G2`,`s2`,`t2`,`tn2`] >> simp[]) >>
  `eval_operand y z = SOME (val_to_w256 v2) /\ op_prov G3 y = NONE /\
   op_taint tn3 y = {} /\ (!q. y = Var q ==> not_fresh_at s3 q)` by
    (irule slice_external_operand_kept >> simp[] >>
     qexistsl_tac [`G2`,`s2`,`t2`,`tn2`] >> simp[]) >>
  simp[]
QED

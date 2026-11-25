(* The ordinary membership dispatcher selects either flags or a nonliteral array. *)
Theory bodyMembershipOrdinaryShapeMods
Ancestors
  exprBodyPreProps exprSimHypsDefs compileEnv vyperTypeSystem vyperAST

Theorem membership_ordinary_shape_mods:
  (bop = In \/ bop = NotIn) /\
  is_word_type (expr_type e1) /\
  ((word_value_type (expr_type e1) /\ word_value_type (expr_type e2)) \/
   (!a t n elems. e2 <> Builtin a (MakeArray t n) elems)) /\
  expr_body_pre_mods mods cenv cx env (Builtin ann (Bop bop) [e1;e2]) es ==>
  well_typed_binop ann bop (expr_type e1) (expr_type e2) /\
  ann = BaseT BoolT /\
  ((?fid. expr_type e1 = FlagT fid /\ expr_type e2 = FlagT fid) \/
   (?bd. is_word_type (expr_type e1) /\ expr_type e2 = ArrayT (expr_type e1) bd /\
         (!a t n elems. e2 <> Builtin a (MakeArray t n) elems)))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `well_typed_binop ann bop (expr_type e1) (expr_type e2)` by
    (drule expr_body_pre_mods_well_typed >>
     simp[Once well_typed_expr_def, well_typed_builtin_app_def]) >>
  `ann = BaseT BoolT /\
    ((?fid. expr_type e1 = FlagT fid /\ expr_type e2 = FlagT fid) \/
     (?bd. expr_type e2 = ArrayT (expr_type e1) bd))` by
    (qpat_x_assum `bop = In \/ bop = NotIn`
       (DISJ_CASES_THEN SUBST_ALL_TAC) >>
     qpat_x_assum `well_typed_binop _ _ _ _` mp_tac >>
     pure_rewrite_tac[well_typed_binop_def] >> metis_tac[])
  >- simp[] >>
  `!a t n elems. e2 <> Builtin a (MakeArray t n) elems` by
    (qpat_x_assum `(word_value_type _ /\ word_value_type _) \/ _` strip_assume_tac
     >- (qpat_assum `word_value_type (expr_type e2)`
           (mp_tac o MATCH_MP exprSimSourceTheory.word_value_type_word) >> simp[]) >>
     simp[]) >>
  simp[]
QED

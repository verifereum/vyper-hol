Theory bodyIntCallDefaultSliceOccurrenceAccessMods
Ancestors
  linkedConstAccessSubset
  supportedExprTraverse constSubstMods vyperSubscriptOverlap
  vyperAST alist list rich_list pair option sum

(* Specialize at a recursive child of the constructor at the current cut. *)
fun default_child tag =
  qpat_assum `!y. _` (qspec_then tag mp_tac) >>
  simp[expr_size_def, listTheory.list_size_def,
       basicSizeTheory.pair_size_def, basicSizeTheory.option_size_def] >>
  strip_tac

val split_default_tag =
  qmatch_goalsub_rename_tac `sum_CASE tagged _ _` >> Cases_on `tagged` >> simp[]

(* Use the same descent measure as both recursive traversals. *)
val default_measure_induct =
  measureInduct_on `(\z. case z of
      INL e => expr_size e
    | INR (INL t) => base_assignment_target_size t
    | INR (INR (INL es)) => list_size expr_size es
    | INR (INR (INR (INL opt))) => option_size expr_size opt
    | INR (INR (INR (INR fs))) =>
        list_size (pair_size (list_size char_size) expr_size) fs) x`

val witness_norm =
  simp[supported_expr_exists_def, RIGHT_AND_OVER_OR, LEFT_AND_OVER_OR, EXISTS_OR_THM]

Theorem occurrence_witness_mutual[local]:
  !q (x : expr + (base_assignment_target + (expr list + (expr option + (identifier # expr) list)))).
    case x of
      INL e => supported_expr_exists q e <=>
        ?w. q w /\ supported_expr_exists ($= w) e
    | INR (INL t) => supported_target_exists q t <=>
        ?w. q w /\ supported_target_exists ($= w) t
    | INR (INR (INL es)) => supported_exprs_exists q es <=>
        ?w. q w /\ supported_exprs_exists ($= w) es
    | INR (INR (INR (INL opt))) => supported_opt_exists q opt <=>
        ?w. q w /\ supported_opt_exists ($= w) opt
    | INR (INR (INR (INR fs))) => supported_fields_exists q fs <=>
        ?w. q w /\ supported_fields_exists ($= w) fs
Proof
  rpt gen_tac >>
  default_measure_induct >>
  Cases_on `x` >> simp[]
  >- (rename1 `supported_expr_exists q e <=> _` >>
      Cases_on `e` >>
      witness_norm >>
      FIRST [rename1 `q (IfExp _ c a b) \/ _` >>
               map_every default_child [`INL c`, `INL a`, `INL b`],
             rename1 `q (StructLit _ _ fs) \/ _` >>
               default_child `INR (INR (INR (INR fs)))`,
             rename1 `q (Subscript _ e k) \/ _` >>
               map_every default_child [`INL e`, `INL k`],
             rename1 `q (Attribute _ e _) \/ _` >> default_child `INL e`,
             rename1 `q (Builtin _ _ es) \/ _` >> default_child `INR (INR (INL es))`,
             rename1 `q (TypeBuiltin _ _ _ es) \/ _` >> default_child `INR (INR (INL es))`,
             rename1 `q (Pop _ tgt) \/ _` >> default_child `INR (INL tgt)`,
             rename1 `q (Call _ _ es d) \/ _` >>
               map_every default_child [`INR (INR (INL es))`, `INR (INR (INR (INL d)))`]] >>
      simp[]) >>
  split_default_tag
  >- (rename1 `supported_target_exists q tgt <=> _` >>
      Cases_on `tgt` >> witness_norm
      >- (rename1 `(supported_target_exists q subtarget \/ supported_expr_exists q index) <=> _` >>
          map_every default_child [`INR (INL subtarget)`, `INL index`] >> simp[]) >>
      rename1 `supported_target_exists q subtarget <=> _` >>
      default_child `INR (INL subtarget)` >> simp[]) >>
  split_default_tag
  >- (rename1 `supported_exprs_exists q es <=> _` >>
      Cases_on `es` >> witness_norm >>
      rename1 `(supported_expr_exists q hd \/ supported_exprs_exists q tl) <=> _` >>
      map_every default_child [`INL hd`, `INR (INR (INL tl))`] >> simp[]) >>
  split_default_tag
  >- (rename1 `supported_opt_exists q opt <=> _` >>
      Cases_on `opt` >> simp[supported_expr_exists_def] >>
      rename1 `supported_expr_exists q child <=> _` >>
      default_child `INL child` >> simp[]) >>
  rename1 `supported_fields_exists q fs <=> _` >> Cases_on `fs` >> simp[supported_expr_exists_def] >>
  qmatch_goalsub_rename_tac `supported_fields_exists q (fld::fsrest)` >> Cases_on `fld` >>
  witness_norm >>
  rename1 `(supported_expr_exists q child \/ supported_fields_exists q tail) <=> _` >>
  map_every default_child [`INL child`, `INR (INR (INR (INR tail)))`] >> simp[]
QED

Theorem default_slice_occurrence_witness:
  supported_exprs_exists q ds ==>
  ?e. q e /\ supported_exprs_exists ($= e) ds
Proof
  mp_tac (Q.SPECL [`q`,`INR (INR (INL ds))`] occurrence_witness_mutual) >>
  simp[]
QED

(* At a recursive branch, the stripped premise identifies the actual child. *)
val default_read_child =
  strip_tac >>
  FIRST [rename1 `supported_expr_exists _ child` >> default_child `INL child`,
         rename1 `supported_target_exists _ child` >> default_child `INR (INL child)`,
         rename1 `supported_exprs_exists _ child` >> default_child `INR (INR (INL child))`,
         rename1 `supported_opt_exists _ child` >> default_child `INR (INR (INR (INL child)))`,
         rename1 `supported_fields_exists _ child` >> default_child `INR (INR (INR (INR child)))`] >>
  simp[]

Theorem access_mutual[local]:
  !ann owner id (x : expr + (base_assignment_target + (expr list + (expr option + (identifier # expr) list)))).
    case x of
      INL e =>
        supported_expr_exists ($= (TopLevelName ann (owner,id))) e ==>
        MEM (ReadAcc (StateRef (owner,id))) (accesses_expr e)
    | INR (INL t) =>
        supported_target_exists ($= (TopLevelName ann (owner,id))) t ==>
        MEM (ReadAcc (StateRef (owner,id))) (accesses_target t)
    | INR (INR (INL es)) =>
        supported_exprs_exists ($= (TopLevelName ann (owner,id))) es ==>
        MEM (ReadAcc (StateRef (owner,id))) (accesses_exprs es)
    | INR (INR (INR (INL opt))) =>
        supported_opt_exists ($= (TopLevelName ann (owner,id))) opt ==>
        MEM (ReadAcc (StateRef (owner,id))) (accesses_opt opt)
    | INR (INR (INR (INR fs))) =>
        supported_fields_exists ($= (TopLevelName ann (owner,id))) fs ==>
        MEM (ReadAcc (StateRef (owner,id))) (accesses_named_exprs fs)
Proof
  rpt gen_tac >>
  default_measure_induct >>
  split_default_tag
  >- (rename1 `supported_expr_exists _ e ==> _` >> Cases_on `e` >>
      simp[supported_expr_exists_def, accesses_expr_def, MEM_APPEND] >>
      default_read_child) >>
  split_default_tag
  >- (rename1 `supported_target_exists _ tgt ==> _` >> Cases_on `tgt` >>
      simp[supported_expr_exists_def, accesses_expr_def, MEM_APPEND] >>
      default_read_child) >>
  split_default_tag
  >- (rename1 `supported_exprs_exists _ es ==> _` >> Cases_on `es` >>
      simp[supported_expr_exists_def, accesses_expr_def, MEM_APPEND] >>
      default_read_child) >>
  split_default_tag
  >- (rename1 `supported_opt_exists _ opt ==> _` >> Cases_on `opt` >>
      simp[supported_expr_exists_def, accesses_expr_def] >>
      default_read_child) >>
  rename1 `supported_fields_exists _ fs ==> _` >> Cases_on `fs` >>
  simp[supported_expr_exists_def] >>
  qmatch_goalsub_rename_tac `supported_fields_exists _ (fld::fsrest)` >> Cases_on `fld` >>
  simp[supported_expr_exists_def, accesses_expr_def, MEM_APPEND] >>
  default_read_child
QED

Theorem intcall_default_slice_raw_read_access_mods:
  (!key r. ALOOKUP E key = SOME r ==> accesses_expr r = []) /\
  supported_exprs_exists ($= (TopLevelName ann (owner,id)))
    (DROP n (subst_consts_exprs_mods E dflts)) ==>
  MEM (ReadAcc (StateRef (owner,id))) (accesses_exprs dflts)
Proof
  strip_tac >>
  drule linked_subst_accesses_subset >> strip_tac >>
  first_x_assum irule >>
  mp_tac (Q.SPECL [`ann`,`owner`,`id`,
                  `INR (INR (INL (subst_consts_exprs_mods E dflts)))`] access_mutual) >>
  fs[supported_exprs_exists_every, EXISTS_MEM] >>
  metis_tac[MEM_DROP_IMP]
QED

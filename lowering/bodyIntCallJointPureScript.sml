(* Seam 2 joint induction step: every other non-call expression form. *)
Theory bodyIntCallJointPure
Ancestors
  bodyIntCallJointContract bodyIntCallFamPureAtom bodyIntCallFamPureIfExp
  bodyIntCallFamPureBuiltin

(* L-pure (C1.3.14.3), the same step for every other non-call form: names,
   literals, top-level names, flag members, ternaries, the other builtins
   and type builtins.  Children that are internal calls are covered by the
   smaller-expression premise (supported_pure_expr admits none). *)
Theorem intcall_pure_producer_step:
  (!e'. expr_size e' < expr_size e ==>
        intcall_expr_producer fp e' /\ intcall_forced_producer fp e' /\
        intcall_map_producer fp e') /\
  ~(?a t n args. e = Builtin a (MakeArray t n) args) /\
  ~(?a nm fields. e = StructLit a nm fields) /\
  ~(?a base fld. e = Attribute a base fld) /\
  ~(?a base idx. e = Subscript a base idx) /\
  ~(?a tgt args dflt. e = Call a tgt args dflt) /\
  ~(?a tgt. e = Pop a tgt) ==>
  intcall_expr_producer fp e /\ intcall_map_producer fp e
Proof
  strip_tac >>
  qsuff_tac `((?ty x. e = Name ty x) \/ (?ty n. e = TopLevelName ty n) \/
              (?ty n m. e = FlagMember ty n m) \/ (?ty l. e = Literal ty l) \/
              (?ty c e1 e2. e = IfExp ty c e1 e2)) \/
             ((?a b args. e = Builtin a b args /\ !t n. b <> MakeArray t n) \/
              (?a tb ty args. e = TypeBuiltin a tb ty args))`
  >- (disch_then (DISJ_CASES_THEN assume_tac)
      >- (Cases_on `?ty c e1 e2. e = IfExp ty c e1 e2`
          >- (irule intcall_ifexp_step >> metis_tac[])
          >> irule intcall_pure_atom_step >> gvs[] >> metis_tac[])
      >> irule intcall_pure_builtin_step >> metis_tac[]) >>
  qpat_x_assum `!e'. _` kall_tac >>
  Cases_on `e` >> fs[]
QED

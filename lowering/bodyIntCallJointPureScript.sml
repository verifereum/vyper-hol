(* Seam 2 joint induction step: every other non-call expression form. *)
Theory bodyIntCallJointPure
Ancestors
  bodyIntCallJointContract bodyIntCallJointPurePath bodyIntCallJointPureSourceInv
  bodyIntCallJointPureSuffix bodyIntCallJointPureCont

(* Audit: non-NoneT representations need not occupy any bytes. *)
Theorem pure_empty_tuple_type_probe[local]:
  evaluate_type FEMPTY (TupleT []) = SOME (TupleTV []) /\
  type_memory_size (TupleTV []) = 0
Proof
  EVAL_TAC
QED

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
  cheat
QED

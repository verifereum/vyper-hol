(* Seam 2 joint induction step: aggregate constructors and memory subplaces. *)
Theory bodyIntCallJointAgg
Ancestors
  bodyIntCallJointContract bodyIntCallFamAggTuple bodyIntCallFamAggArray
  bodyIntCallFamAggStruct bodyIntCallFamAggAttribute bodyIntCallFamAggSubscript

(* L-agg (C1.3.14.2.3), a step of the induction on expr_size: tuple
   literals (MakeArray NONE), array literals (MakeArray (SOME _)), struct
   literals, attributes and subscripts (every place_type case: tuple and
   struct literal-index, ValPT array, MapPT), given the producers of every
   smaller expression. *)
Theorem intcall_aggregate_producer_step:
  (!e'. expr_size e' < expr_size e ==>
        intcall_expr_producer fp e' /\ intcall_forced_producer fp e' /\
        intcall_map_producer fp e') /\
  ((?a t n args. e = Builtin a (MakeArray t n) args) \/
   (?a nm fields. e = StructLit a nm fields) \/
   (?a base fld. e = Attribute a base fld) \/
   (?a base idx. e = Subscript a base idx)) ==>
  intcall_expr_producer fp e /\ intcall_map_producer fp e
Proof
  disch_then strip_assume_tac
  >- (Cases_on `t`
      >- (irule intcall_tuple_literal_step >> metis_tac[])
      >> irule intcall_array_literal_step >> metis_tac[])
  >- (irule intcall_struct_literal_step >> metis_tac[])
  >- (irule intcall_attribute_step >> metis_tac[])
  >> irule intcall_subscript_step >> metis_tac[]
QED

(* Guarded String capacity at an ordinary linked Slice source cut. *)
Theory bodySliceStringCapacityMods
Ancestors
  exprSimSliceSource vyperInterpreter vyperState vyperValue vyperTypeSystem
  vyperAST vyperTyping words

Theorem slice_string_capacity_all_tail:
  slice_operands_ok (Slice n) [src;start;len] /\
  expr_type src = BaseT (StringT m) /\
  value_runtime_typed env (expr_type src) (StringV str) /\
  (!tail. eval_exprs cx [src;start;len] (es with gas_obs := tail) =
     (INL [StringV str;IntV (&i);IntV (&k)], ee with gas_obs := tail)) ==>
  (i+k <= LENGTH (MAP (n2w o ORD) str) ==> k <= n)
Proof
  simp[] >> rpt strip_tac >>
  qpat_x_assum `!tail. eval_exprs _ _ _ = _` (qspec_then `[]` assume_tac) >>
  metis_tac[slice_string_capacity]
QED

(* Diagnostic boundary audit: source Values need not be memory-backed.
   In particular immutable pop returns a Value, while its target result
   retains LocCode and the constructor's staged immutable-buffer address. *)
Theory exprSimSubscriptArrayLiveValue
Ancestors
  loweringPosts vyperState

Theorem immutable_pop_success_is_value:
  pop_place cx (ImmutablePlace src id path) es = (INL r,ee) ==>
  ?v. r = Value v
Proof
  simp[pop_place_def, bind_def, ignore_bind_def, return_def,
       lift_option_type_def, lift_sum_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
QED

(* None of these origin clauses frames a Value in the immutable buffer. *)
Theorem code_value_origin_clauses:
  p.ptr_location = LocCode ==>
  vv_at cenv cx (ArrayT et bd) sa sb es (Value v)
    (LocatedValue (ArrayT et bd) p) s /\
  vv_own cenv cx (ArrayT et bd) sa sb es (Value v)
    (LocatedValue (ArrayT et bd) p) s /\
  vv_place_ptr cenv cx es s (Value v)
    (LocatedValue (ArrayT et bd) p)
Proof
  simp[vv_at_def, vv_own_def, vv_place_ptr_def]
QED

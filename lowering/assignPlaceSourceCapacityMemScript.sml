(* Original memory sources need capacity, not exclusive ownership. *)
Theory assignPlaceSourceCapacityMem
Ancestors
  assignPlaceBytestringSourceMem exprSimMemDefs loweringPosts valueCopyBytes
  valueEncodingProps valueEncoding vyperTypeSystem compileEnv venomState context

Theorem assign_original_memory_source_capacity:
  vv_holds cenv cx et raw vv ee s /\
  (lt = et \/ is_bytestring_type et /\ is_bytestring_type lt) /\
  assignable_type (get_tenv cx) et /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  evaluate_type (get_tenv cx) lt = SOME stv /\ value_has_type stv v /\
  vv_store_bound cx et lt ee raw vv s /\
  read_result cx raw ee = (INL v,ee) /\
  ((?vt p. vv = LocatedValue vt p /\ p.ptr_location = LocMemory) \/
   (?vt op. vv = StackValue vt op /\ is_bytestring_type et)) ==>
  ?sw. eval_operand (vv_operand vv) s = SOME sw /\
    val_in_memory stv v (w2n sw) s.vs_memory /\
    w2n sw + type_memory_size stv <= s.vs_alloca_next
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?sw. eval_operand (vv_operand vv) s = SOME sw /\
     val_in_memory etv v (w2n sw) s.vs_memory` by
    (Cases_on `vv` >>
     gvs[vv_holds_def, vv_operand_def, expr_val_rel_def] >>
     metis_tac[is_bytestring_word_type]) >>
  `val_in_memory stv v (w2n sw) s.vs_memory /\
   0 < type_memory_size stv` by
    (Cases_on `lt = et`
     >- (gvs[] >> drule_all assignable_type_slot_size_pos >>
         simp[type_memory_size_slots]) >>
     `is_bytestring_type et /\ is_bytestring_type lt` by metis_tac[] >>
     conj_tac
     >- metis_tac[bytestring_val_in_memory_transfer] >>
     drule_all bytestring_type_value >> strip_tac >>
     gvs[type_memory_size_def]) >>
  `w2n sw + type_memory_size stv <= s.vs_alloca_next` by
    (Cases_on `vv` >>
     gvs[vv_operand_def, vv_store_bound_def] >>
     metis_tac[is_bytestring_word_type]) >>
  qexists_tac `sw` >> simp[]
QED

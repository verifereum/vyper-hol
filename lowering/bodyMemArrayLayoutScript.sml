(* Allocation layout and completed representation for array literals. *)
Theory bodyMemArrayLayout
Ancestors
  exprSimAggregateLayout exprSimAggregateEncoding exprSimAlloc exprLoweringProps
  exprSimHypsDefs fragExec allocLimits valueEncoding vyperAST

Theorem array_body_allocation_layout:
  expr_body_pre ce cx env (Builtin ann (MakeArray (SOME et) bnd) args) st /\
  compile_expr ce ty (Builtin ann (MakeArray (SOME et) bnd) args) sa = (vv,sb) /\
  fn_has_code sa sb func ==>
  ?tv ba sm u.
    ann = ArrayT et bnd /\ vv = LocatedValue ann (mk_ptr u LocMemory) /\
    compile_alloc_buffer (type_memory_bytes ce ann) sa = (ba,sm) /\
    compile_make_array compile_expr ce args et (type_memory_bytes ce et)
      (case bnd of Dynamic _ => T | _ => F) ba.buf_operand sm = (u,sb) /\
    evaluate_type (get_tenv cx) et = SOME tv /\
    evaluate_type (get_tenv cx) ann = SOME (ArrayTV tv bnd) /\
    EVERY (\e. expr_type e = et) args /\
    type_memory_bytes ce et = type_memory_size tv /\
    (if (case bnd of Dynamic _ => T | _ => F) then 32 else 0) +
      LENGTH args * type_memory_size tv <= type_memory_bytes ce ann /\
    type_memory_bytes ce ann < dimword (:256) /\
    ci_mono sa sm /\ ci_mono sm sb /\ cs_extends sa sm /\ cs_extends sm sb /\
    fn_has_code sa sm func /\ fn_has_code sm sb func /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes ce ann))]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)
Proof
  strip_tac >> drule compile_array_literal_inv >> strip_tac >> gvs[] >>
  drule make_array_evaluated_layout >> strip_tac >> gvs[] >>
  `ci_mono sa sm` by metis_tac[ci_mono_compile_alloc_buffer, pairTheory.SND] >>
  `ci_mono sm sb` by
    metis_tac[ci_mono_compile_make_array_cfn, compile_expr_ci_mono, pairTheory.SND] >>
  `cs_extends sa sm /\ cs_extends sm sb` by gvs[ci_mono_def] >>
  drule_all fn_has_code_split >> strip_tac >>
  `type_memory_bytes ce (ArrayT et bnd) < dimword (:256)` by
    (gvs[expr_body_pre_def, alloc_limits_expr_def] >>
     simp[wordsTheory.dimword_def] >> decide_tac) >>
  drule_all buffer_alloc_code >> strip_tac >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem array_from_dense_memory:
  compatible_bound n (LENGTH vs) /\
  elems_in_memory vs (b + (case n of Fixed _ => 0 | Dynamic _ => 32)) tv mem /\
  ((case n of Fixed _ => F | Dynamic _ => T) ==>
    mem_word_at b mem = n2w (LENGTH vs)) ==>
  val_in_memory (ArrayTV tv n) (ArrayV (make_array_value tv n vs)) b mem
Proof
  Cases_on `n`
  >- (simp[vyperValueTheory.compatible_bound_def] >>
      metis_tac[fixed_array_from_dense]) >>
  simp[vyperValueTheory.make_array_value_def, val_in_memory_def]
QED

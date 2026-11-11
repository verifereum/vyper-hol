Theory concretizePtrPrefixRelation
Ancestors
  concretizePtrChronologicalHistory concretizePtrBytes ptrDiscipline
  venomState finite_map words list pred_set

(* The relocation argument is scoped to an activation. Its domain consists
   of source provenance sites, not numerical pointer values. This is the
   value component of the candidate prefix relation; binding relocation to
   owner tables and checked output metadata remains a separate obligation. *)
Definition ptr_prefix_value_def:
  ptr_prefix_value (reloc : (num # num) -> bytes32 option) site mask x y <=>
    case (x,y) of
      (NONE,NONE) => T
    | (SOME w,SOME wt) =>
        (case site of
           NONE => word_agree_except mask w wt
         | SOME (off,sz) =>
             ?pos. reloc (off,sz) = SOME pos /\
               w - n2w off = wt - pos)
    | _ => F
End

Definition ptr_prefix_vars_def:
  ptr_prefix_vars reloc G V (s:venom_state) t <=>
    !v. ptr_prefix_value reloc (FLOOKUP G v)
      (case FLOOKUP V v of NONE => {} | SOME mask => mask)
      (lookup_var v s) (lookup_var v t)
End

(* Demand is a set of current source bytes, not a future execution. Tainted
   bytes are deliberately excluded: freshly allocated contents may differ. *)
Definition ptr_prefix_memory_def:
  ptr_prefix_memory demand reloc tn (s:venom_state) t <=>
    ptr_bytes_agree (demand DIFF tn.t_mem) reloc s.vs_memory t.vs_memory
End

Theorem ptr_prefix_vars_entry:
  ptr_prefix_vars reloc FEMPTY FEMPTY s s
Proof
  simp[ptr_prefix_vars_def, ptr_prefix_value_def] >> gen_tac >>
  Cases_on `lookup_var v s` >> simp[word_agree_except_def]
QED

Theorem ptr_prefix_memory_entry:
  ptr_prefix_memory demand I entry_taint s s
Proof
  simp[ptr_prefix_memory_def, ptr_bytes_agree_def, entry_taint_def]
QED

Theorem ptr_prefix_vars_scalar:
  ptr_prefix_vars reloc G V s t /\ FLOOKUP G v = NONE /\
  lookup_var v s = SOME w ==>
  ?wt. lookup_var v t = SOME wt /\
    word_agree_except
      (case FLOOKUP V v of NONE => {} | SOME mask => mask) w wt
Proof
  simp[ptr_prefix_vars_def] >> rpt strip_tac >>
  first_x_assum (qspec_then `v` mp_tac) >>
  Cases_on `lookup_var v t` >> simp[ptr_prefix_value_def]
QED

Theorem ptr_prefix_value_uninitialized:
  ptr_prefix_value reloc NONE {b | b < 32} (SOME w) (SOME wt)
Proof
  simp[ptr_prefix_value_def, word_agree_except_def]
QED

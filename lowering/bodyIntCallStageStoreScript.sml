(* Physical-capacity specialization for the actual argument staging buffer. *)
Theory bodyIntCallStageStore
Ancestors bodyIntCallTightStore exprSimProps context

Theorem intcall_stage_store_capacity:
  val_wf tv v /\ type_memory_bytes ce ty = type_memory_size tv ==>
  (if is_word_type ty then 32
   else if is_bytestring_type ty then val_store_size tv v
   else type_memory_bytes ce ty) <= MAX 32 (type_memory_bytes ce ty)
Proof
  strip_tac >> drule val_store_size_le >> strip_tac >>
  Cases_on `is_word_type ty` >> simp[] >>
  Cases_on `is_bytestring_type ty` >> simp[] >> decide_tac
QED

Theorem intcall_stage_store_capacity_strict:
  val_wf tv v /\ type_memory_bytes ce ty = type_memory_size tv /\
  MAX 32 (type_memory_bytes ce ty) < dimword (:256) ==>
  (if is_word_type ty then 32
   else if is_bytestring_type ty then val_store_size tv v
   else type_memory_bytes ce ty) < dimword (:256)
Proof
  strip_tac >> drule_all intcall_stage_store_capacity >> decide_tac
QED

Theorem intcall_stage_store_forward:
  compile_store_memory cenv src dst ty ty sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes cenv ty = type_memory_size tv /\
  (if is_word_type ty then sw = typed_val_to_w256 tv v
   else val_in_memory tv v (w2n sw) s.vs_memory) /\
  MAX 32 (type_memory_bytes cenv ty) < dimword (:256) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    val_in_memory tv v (w2n dw) t.vs_memory /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
              vs_inst_idx := s.vs_inst_idx|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
                 FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!a k. a + k <= w2n dw \/ w2n dw + MAX 32 (type_memory_bytes cenv ty) <= a ==>
      mem_bytes_at a k t.vs_memory = mem_bytes_at a k s.vs_memory) /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  drule_all intcall_stage_store_capacity >> strip_tac >>
  drule_all intcall_stage_store_capacity_strict >> strip_tac >>
  drule_all intcall_same_type_store_forward >> simp[]
QED

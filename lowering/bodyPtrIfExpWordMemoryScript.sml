Theory bodyPtrIfExpWordMemory
Ancestors
  bodyPtrDefs representationCleanPtr exprSimProps loweringPosts
  valueEncoding vyperAST vyperTyping vyperValue compileEnv

(* Runtime type evaluation alone does not type the returned value.  NoneV
   has a vacuous robust memory representation even at a word type.  This
   probe is not a counterexample to the frozen IfExp statement: its actual
   expression precondition may supply the missing value_has_type fact. *)
Theorem word_memory_untyped_none_probe[local]:
  is_word_type (BaseT BoolT) /\ val_wf (BaseTV BoolT) NoneV /\
  (!mem. val_in_memory (BaseTV BoolT) NoneV 0 mem) /\
  ~value_has_type (BaseTV BoolT) NoneV /\
  (!mem. mem_agree_outside {0} m mem ==>
         val_in_memory (BaseTV BoolT) NoneV 0 mem) /\
  ~(!i. 0 <= i /\ i < 32 ==> i NOTIN ({0}:num set))
Proof
  EVAL_TAC >> simp[]
QED

Theorem ifexp_typed_word_memory_clean:
  is_word_type t /\ evaluate_type (get_tenv cx) t = SOME tv /\
  value_has_type tv v /\ ptr_mem_ok cx t v op G tn s /\
  eval_operand op s = SOME w ==>
  !i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn.t_mem
Proof
  strip_tac >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     mem_word_at (w2n w) mem = typed_val_to_w256 tv v` by
    (rpt strip_tac >> irule val_in_memory_word_type >>
     gvs[ptr_mem_ok_def] >> metis_tac[]) >>
  drule robust_mem_word_at_clean >> simp[]
QED

Theorem ifexp_typed_word_layout:
  is_word_type t /\ evaluate_type tenv t = SOME tv /\
  value_has_type tv v ==>
  val_footprint tv v = 32 /\ val_store_size tv v = 32
Proof
  strip_tac >>
  `(?n. t = BaseT (UintT n)) \/ (?n. t = BaseT (IntT n)) \/
   t = BaseT BoolT \/ t = BaseT AddressT \/ t = BaseT DecimalT \/
   (?m. t = BaseT (BytesT (Fixed m)) /\ m <= 32) \/ (?n. t = FlagT n)` by
    (Cases_on `t` >> fs[is_word_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> fs[is_word_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >> fs[is_word_type_def]) >>
  gvs[evaluate_type_def, AllCaseEqs()] >> Cases_on `v` >>
  gvs[value_has_type_def, val_footprint_def, val_store_size_def,
      type_memory_size_def]
QED

Theorem ifexp_typed_word_memory_coverage:
  is_word_type t /\ evaluate_type (get_tenv cx) t = SOME tv /\
  value_has_type tv v /\ ptr_mem_ok cx t v op G tn s /\
  eval_operand op s = SOME w ==>
  ?x b sz. op = Var x /\ FLOOKUP G x = SOME (b,sz) /\
           b <= w2n w /\ w2n w + 32 <= b + sz
Proof
  strip_tac >> drule_all ifexp_typed_word_layout >> strip_tac >>
  gvs[ptr_mem_ok_def] >> metis_tac[]
QED

Theorem ifexp_located_word_memory_clean:
  is_word_type t /\ evaluate_type (get_tenv cx) t = SOME tv /\
  value_has_type tv v /\
  ptr_vv_ok cx t raw (LocatedValue t' p) es G tn s /\
  p.ptr_location = LocMemory /\ read_result cx raw es = (INL v,es) /\
  eval_operand p.ptr_operand s = SOME w ==>
  !i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn.t_mem
Proof
  strip_tac >> gvs[ptr_vv_ok_def] >>
  metis_tac[ifexp_typed_word_memory_clean]
QED

Theorem ifexp_located_word_memory_coverage:
  is_word_type t /\ evaluate_type (get_tenv cx) t = SOME tv /\
  value_has_type tv v /\
  ptr_vv_ok cx t raw (LocatedValue t' p) es G tn s /\
  p.ptr_location = LocMemory /\ read_result cx raw es = (INL v,es) /\
  eval_operand p.ptr_operand s = SOME w ==>
  ?x b sz. p.ptr_operand = Var x /\ FLOOKUP G x = SOME (b,sz) /\
           b <= w2n w /\ w2n w + 32 <= b + sz
Proof
  strip_tac >> gvs[ptr_vv_ok_def] >>
  irule ifexp_typed_word_memory_coverage >> metis_tac[]
QED

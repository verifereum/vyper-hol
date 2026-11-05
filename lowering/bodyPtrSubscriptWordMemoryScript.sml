(* Typed word memory representation prepares one constructive MLOAD witness. *)
Theory bodyPtrSubscriptWordMemory
Ancestors
  bodyPtrDefs representationCleanPtr exprSimProps entryDecodeStaticProps
  valueEncoding valueEncodingProps loweringPosts compileEnv vyperTyping vyperValue venomState

Theorem word_memory_footprints:
  is_word_type t /\ evaluate_type tenv t = SOME ty ==>
  val_footprint ty v = 32 /\ val_store_size ty v = 32
Proof
  rpt strip_tac >>
  `(?n. t = BaseT (UintT n)) \/ (?n. t = BaseT (IntT n)) \/
   t = BaseT BoolT \/ t = BaseT AddressT \/ t = BaseT DecimalT \/
   (?m. t = BaseT (BytesT (Fixed m)) /\ m <= 32) \/ (?n. t = FlagT n)` by
    (Cases_on `t` >> fs[is_word_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> fs[is_word_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >> fs[is_word_type_def]) >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  Cases_on `v` >>
  simp[val_footprint_def, val_store_size_def, type_memory_size_def]
QED

Theorem typed_word_memory_prepare:
  is_word_type t /\ evaluate_type (get_tenv cx) t = SOME ty /\
  value_has_type ty v /\ ptr_mem_ok cx t v op G tn s /\
  op_taint tn op = {} /\ eval_operand op s = SOME w ==>
  ?p. op = Var p /\ ptr_covers G tn p s 32 /\
      (!i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn.t_mem) /\
      mload (w2n w) s = typed_val_to_w256 ty v
Proof
  strip_tac >>
  `val_footprint ty v = 32 /\ val_store_size ty v = 32` by
    metis_tac[word_memory_footprints] >>
  `(!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
           val_in_memory ty v (w2n w) mem) /\
   ?p b sz. op = Var p /\ FLOOKUP G p = SOME (b,sz) /\
            b <= w2n w /\ w2n w + 32 <= b + sz` by
    (gvs[ptr_mem_ok_def] >> metis_tac[]) >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         mem_word_at (w2n w) mem = typed_val_to_w256 ty v` by
    metis_tac[val_in_memory_word_type] >>
  `!i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn.t_mem` by
    (drule robust_mem_word_at_clean >> simp[]) >>
  qexists_tac `p` >> simp[] >> conj_tac
  >- (gvs[ptr_covers_def, eval_operand_def] >> metis_tac[]) >>
  simp[GSYM mem_word_at_eq_mload] >>
  first_x_assum irule >> simp[mem_agree_outside_def]
QED

Theorem located_word_memory_prepare:
  is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME ty /\
  value_has_type ty v /\ read_result cx tv ee = (INL v,ee) /\
  p.ptr_location = LocMemory /\
  vv_post ctx func cenv cx e es sa sm s0 ee tv (LocatedValue t p) s /\
  ptr_vv_ok cx (expr_type e) tv (LocatedValue t p) ee G tn s ==>
  ?src w. p.ptr_operand = Var src /\ lookup_var src s = SOME w /\
    ptr_covers G tn src s 32 /\
    (!i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn.t_mem) /\
    mload (w2n w) s = typed_val_to_w256 ty v
Proof
  strip_tac >>
  `?w. eval_operand p.ptr_operand s = SOME w` by
    gvs[vv_post_def, vv_holds_def] >>
  `ptr_mem_ok cx (expr_type e) v p.ptr_operand G tn s /\
   op_taint tn p.ptr_operand = {}` by
    gvs[ptr_vv_ok_def] >>
  drule_all typed_word_memory_prepare >> strip_tac >>
  gvs[eval_operand_def] >> metis_tac[]
QED

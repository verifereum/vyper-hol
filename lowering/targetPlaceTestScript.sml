Theory targetPlaceTest
Ancestors
  stmtLowering exprLowering compileEnv context vyperAST finite_map
Libs
  monadsyntax

Theorem target_bind_return[local]:
  comp_bind (comp_return x) f = f x
Proof
  simp[FUN_EQ_THM, comp_bind_def, comp_return_def]
QED

(* Equations expose the recursive boundary without assuming a root name.
   In particular the key computation is sequenced after the recursive base. *)
Theorem target_map_step:
  compile_get_target_ptr ce bt st = ((op, loc, SOME (MapPT kt vt)), st1) ==>
  compile_get_target_ptr ce (SubscriptTarget bt key) st =
    (do key_op <- lower_value compile_expr ce (expr_type key) key;
        hashed <- (if is_bytestring_type kt then compile_keccak256_key key_op F
                   else return key_op);
        slot <- compile_mapping_subscript op hashed;
        return (slot, loc, SOME (value_type_place vt))
     od) st1
Proof
  simp[Once compile_get_target_ptr_def, comp_bind_def, LET_THM]
QED

Definition target_test_state_def:
  target_test_state = <| cs_next_var := 0; cs_next_label := 0;
    cs_next_id := 0; cs_current_bb := "entry"; cs_current_insts := [];
    cs_blocks := []; cs_data_sections := [] |>
End

(* Leave unused environment fields abstract: these tests depend only on the
   module binding, its descriptor, and the specified layout. *)
Definition target_test_env_def:
  target_test_env ce vt = ce with <|
    ce_vars := FEMPTY |++ [("self.m", TransientLoc 7w)];
    ce_hashmap_info := (\n. if n = "self.m" then
      SOME (T, BaseT (UintT 256), vt) else NONE) |>
End

Theorem target_transient_nonzero:
  compile_get_target_ptr (target_test_env ce vt)
    (TopLevelNameTarget (NONE,"m")) target_test_state =
  ((Lit 7w, SOME LocTransient, SOME (MapPT (BaseT (UintT 256)) vt)),
    target_test_state)
Proof
  EVAL_TAC
QED

Theorem target_nested_map_descriptor:
  SND (SND (FST (compile_get_target_ptr
    (target_test_env ce (HashMapT (BaseT AddressT) (Type (BaseT (UintT 256)))))
    (SubscriptTarget (TopLevelNameTarget (NONE,"m"))
      (Literal (BaseT (UintT 256)) (IntL 3))) target_test_state))) =
  SOME (MapPT (BaseT AddressT) (Type (BaseT (UintT 256))))
Proof
  EVAL_TAC
QED

Theorem target_map_value_descriptor_location:
  let result = compile_get_target_ptr (target_test_env ce (Type t))
    (SubscriptTarget (TopLevelNameTarget (NONE,"m"))
      (Literal (BaseT (UintT 256)) (IntL 3))) target_test_state in
  FST (SND (FST result)) = SOME LocTransient /\
  SND (SND (FST result)) = SOME (ValPT t)
Proof
  EVAL_TAC
QED

(* This equation distinguishes execution order even for effectful keys: the
   entire inner lower_value and hash precede the outer lower_value. *)
Theorem target_nested_key_order:
  compile_get_target_ptr
    (target_test_env ce (HashMapT (BaseT (UintT 256)) (Type t)))
    (SubscriptTarget
      (SubscriptTarget (TopLevelNameTarget (NONE,"m")) inner) outer) =
  (do k1 <- lower_value compile_expr
       (target_test_env ce (HashMapT (BaseT (UintT 256)) (Type t)))
       (expr_type inner) inner;
      p1 <- compile_mapping_subscript (Lit 7w) k1;
      k2 <- lower_value compile_expr
       (target_test_env ce (HashMapT (BaseT (UintT 256)) (Type t)))
       (expr_type outer) outer;
      p2 <- compile_mapping_subscript p1 k2;
      return (p2, SOME LocTransient, SOME (ValPT t))
   od)
Proof
  rewrite_tac[compile_get_target_ptr_def] >>
  simp[target_test_env_def, module_var_key_def, nsid_to_string_def,
       value_type_place_def, is_bytestring_type_def, LET_THM,
       FUPDATE_LIST_THM, FLOOKUP_UPDATE, comp_bind_assoc, target_bind_return]
QED

Theorem target_local_module_collision:
  compile_get_target_ptr
    ((target_test_env ce vt) with <|
      ce_vars := FEMPTY |++ [("self.m", TransientLoc 7w);
                            ("m", MemLoc 96 64)];
      ce_var_type := (\n. SOME (ArrayT (BaseT (UintT 256)) (Fixed 2))) |>)
    (NameTarget "m") st =
  ((Lit 96w, SOME LocMemory,
    SOME (ValPT (ArrayT (BaseT (UintT 256)) (Fixed 2)))), st)
Proof
  EVAL_TAC
QED

Theorem target_bytestring_key_hash:
  compile_get_target_ptr
    ((target_test_env ce (Type t)) with
      ce_hashmap_info := (\n. SOME (T, BaseT (StringT 10), Type t)))
    (SubscriptTarget (TopLevelNameTarget (NONE,"m")) key) =
  (do k <- lower_value compile_expr
        ((target_test_env ce (Type t)) with
          ce_hashmap_info := (\n. SOME (T, BaseT (StringT 10), Type t)))
        (expr_type key) key;
      h <- compile_keccak256_key k F;
      p <- compile_mapping_subscript (Lit 7w) h;
      return (p, SOME LocTransient, SOME (ValPT t))
   od)
Proof
  rewrite_tac[compile_get_target_ptr_def] >>
  simp[target_test_env_def, module_var_key_def, nsid_to_string_def,
       value_type_place_def, is_bytestring_type_def, LET_THM,
       FUPDATE_LIST_THM, FLOOKUP_UPDATE, comp_bind_assoc, target_bind_return]
QED

Theorem target_literal_key[local]:
  lower_value compile_expr ce (expr_type (Literal (BaseT (UintT 256)) (IntL n)))
    (Literal (BaseT (UintT 256)) (IntL n)) = comp_return (Lit (i2w n))
Proof
  simp[FUN_EQ_THM] >> gen_tac >> EVAL_TAC
QED

(* The second subscript of a map-of-array is an array operation, not SHA3. *)
Theorem target_map_array_continuation:
  compile_get_target_ptr
    (target_test_env ce (Type (ArrayT (BaseT (UintT 256)) (Fixed 3))))
    (SubscriptTarget
      (SubscriptTarget (TopLevelNameTarget (NONE,"m"))
        (Literal (BaseT (UintT 256)) (IntL 1)))
      (Literal (BaseT (UintT 256)) (IntL 2))) =
  (do p <- compile_mapping_subscript (Lit 7w) (Lit 1w);
      q <- compile_array_subscript p (Lit 2w) F 3 1 1 F
             (compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca LocTransient);
      return (q, SOME LocTransient, SOME (ValPT (BaseT (UintT 256))))
   od)
Proof
  rewrite_tac[compile_get_target_ptr_def] >>
  simp[target_test_env_def, module_var_key_def, nsid_to_string_def,
       value_type_place_def, is_bytestring_type_def, LET_THM,
       FUPDATE_LIST_THM, FLOOKUP_UPDATE, comp_bind_assoc, target_bind_return,
       target_literal_key, word_scale_def, expr_type_def,
       elem_size_in_location_def, is_signed_type_def,
       is_slot_addressed_def, type_memory_bytes_def, integer_wordTheory.i2w_def]
QED

Definition target_struct_env_def:
  target_struct_env ce = (target_test_env ce (Type (StructT (NONE,"P")))) with
    ce_struct_fields := FEMPTY |+ ("P", [("a", (BaseT (UintT 256), 32));
                                        ("b", (BaseT (UintT 256), 32))])
End

Theorem target_map_struct_continuation:
  compile_get_target_ptr (target_struct_env ce)
    (AttributeTarget
      (SubscriptTarget (TopLevelNameTarget (NONE,"m"))
        (Literal (BaseT (UintT 256)) (IntL 1))) "b") =
  (do p <- compile_mapping_subscript (Lit 7w) (Lit 1w);
      q <- emit_op ADD [p; Lit 1w];
      return (q, SOME LocTransient, SOME (ValPT (BaseT (UintT 256))))
   od)
Proof
  rewrite_tac[compile_get_target_ptr_def] >>
  simp[target_struct_env_def, target_test_env_def, module_var_key_def,
       nsid_to_string_def, value_type_place_def, is_bytestring_type_def,
       LET_THM, FUPDATE_LIST_THM, FLOOKUP_UPDATE,
       comp_bind_assoc, target_bind_return, target_literal_key,
       get_struct_fields_def, struct_field_offset_slots_def,
       integer_wordTheory.i2w_def]
QED

(* Exercise the real scalar store/load consumers after resolving a transient
   map pointer. No blocks may hide persistent operations outside this trace. *)
Definition target_transient_trace_def:
  target_transient_trace ce =
    (do r <- compile_get_target_ptr (target_test_env ce (Type (BaseT (UintT 256))))
          (SubscriptTarget (TopLevelNameTarget (NONE,"m"))
            (Literal (BaseT (UintT 256)) (IntL 3)));
        let loc = (case FST (SND r) of SOME l => l | NONE => LocMemory) in
        do compile_assign_value ce (FST r) loc (Lit 9w) T NONE
             (BaseT (UintT 256)) (BaseT (UintT 256)) NONE 32;
           compile_ptr_load F ce.ce_imm_alloca loc (FST r)
        od
     od) target_test_state
End

Theorem target_transient_trace_opcodes:
  MAP (\i. i.inst_opcode) (SND (target_transient_trace ce)).cs_current_insts =
    [ALLOCA; MSTORE; ADD; MSTORE; SHA3; TSTORE; TLOAD] /\
  (SND (target_transient_trace ce)).cs_blocks = []
Proof
  EVAL_TAC
QED

(* Regression tests must remain kernel-closed, including their dependencies. *)
val () = List.app (fn (name,_) =>
  let
    val th = DB.fetch "targetPlaceTest" name
    val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then ()
    else raise Fail ("targetPlaceTest." ^ name ^ ": not kernel-closed")
  end) (DB.thms "targetPlaceTest");

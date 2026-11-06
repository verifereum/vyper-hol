Theory bodyPtrPopConsumerAlias
Ancestors
  bodyPtrPopFullFrameProbe bodyPtrPopFullFrameExecution bodyPtrPopFullFrameSource
  exprLowering compileEnv venomInst context

(* Bounded alias ledger: keep context/function, runtime, source and start of
   FullFrame fixed.  A direct spelling of the saved child is proposed as
   TopLevelNameTarget nsid with StorageLoc slot, slot = 8w or 9w; its element
   may be a nested dynamic array, as in ConsumerCut.  The compiler's first
   load already distinguishes that child from this root slice. *)
Theorem pop_alias_storage_first_load:
  FLOOKUP ce.ce_module_vars nsid = SOME (StorageLoc slot) /\
  ce.ce_hashmap_info nsid = NONE /\
  ce.ce_module_var_type nsid = SOME (ArrayT elem (Dynamic n)) ==>
  EL 2 (SND (compile_expr ce ann (Pop ann (TopLevelNameTarget nsid))
    pop_full_frame_start)).cs_current_insts =
    mk_inst 10 SLOAD [Lit slot] ["%7"]
Proof
  strip_tac >>
  simp[Once compile_expr_def, compile_get_target_ptr_def,
       compile_dynarray_pop_def, word_scale_def, comp_return_def, comp_bind_def,
       compile_ptr_load_def, compile_ptr_store_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``elem_size_in_location``, ``ce``, ``slot``])
QED

Theorem pop_alias_control_first_load:
  EL 2 (SND pop_full_frame_compiled).cs_current_insts =
    mk_inst 10 SLOAD [Lit 0w] ["%7"]
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, vyperValueTheory.type_slot_size_def] >>
  EVAL_TAC
QED

Theorem pop_alias_storage_slot_forced:
  FLOOKUP ce.ce_module_vars nsid = SOME (StorageLoc slot) /\
  ce.ce_hashmap_info nsid = NONE /\
  ce.ce_module_var_type nsid = SOME (ArrayT elem (Dynamic n)) /\
  SND (compile_expr ce ann (Pop ann (TopLevelNameTarget nsid))
    pop_full_frame_start) = SND pop_full_frame_compiled ==>
  slot = 0w
Proof
  strip_tac >> drule_all pop_alias_storage_first_load >>
  disch_then (qspec_then `ann` mp_tac) >>
  simp[pop_alias_control_first_load, mk_inst_def]
QED

(* A named saved child at slot 8 or 9 therefore fails the compile equation
   at entry (line 299), before body_inv, expr_body_pre, operand judgment,
   code containment, gas, state relation, or ghost constraints could help.
   This says nothing about arbitrary SubscriptTarget-generated prefixes. *)
Theorem pop_alias_saved_slot_excluded:
  FLOOKUP ce.ce_module_vars nsid = SOME (StorageLoc slot) /\
  ce.ce_hashmap_info nsid = NONE /\
  ce.ce_module_var_type nsid = SOME (ArrayT elem (Dynamic n)) /\
  (slot = 8w \/ slot = 9w) ==>
  SND (compile_expr ce ann (Pop ann (TopLevelNameTarget nsid))
    pop_full_frame_start) <> SND pop_full_frame_compiled
Proof
  strip_tac >> strip_tac >> drule_all pop_alias_storage_slot_forced >>
  gvs[]
QED

(* The alternative local spelling cannot directly denote a storage child:
   regardless of local binding it reports memory, code or no location. *)
Theorem pop_alias_name_not_storage:
  FST (SND (FST (compile_get_target_ptr cfn ce (NameTarget id) sa))) <>
    SOME LocStorage
Proof
  simp[compile_get_target_ptr_def] >>
  Cases_on `FLOOKUP ce.ce_vars id` >> simp[comp_return_def] >>
  Cases_on `x` >> simp[comp_return_def]
QED

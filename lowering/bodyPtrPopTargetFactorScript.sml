Theory bodyPtrPopTargetFactor
Ancestors
  bodyPtrPreds exprLowering vyperInterpreter vyperState compileEnv
Libs
  monadsyntax

(* These cuts preserve the source evaluator's exceptional outcomes as well as
   successes.  In particular read_result occurs after the index effects. *)
Theorem pop_target_attribute_cut:
  eval_base_place cx bt s = (INL pv,s1) ==>
  eval_base_place cx (AttributeTarget bt fld) s =
    extend_place cx pv (AttrSubscript fld) s1
Proof
  simp[Once evaluate_def, bind_def]
QED

Theorem pop_target_subscript_cut:
  eval_base_place cx bt s = (INL pv,s1) /\
  eval_expr cx e s1 = (INL tv,s2) /\
  read_result cx tv s2 = (INL v,s3) ==>
  eval_base_place cx (SubscriptTarget bt e) s =
    extend_place cx pv (ValueSubscript v) s3
Proof
  simp[Once evaluate_def, bind_def]
QED

Theorem pop_target_attribute_base_exception:
  eval_base_place cx bt s = (INR ex,s1) ==>
  eval_base_place cx (AttributeTarget bt fld) s = (INR ex,s1)
Proof
  simp[Once evaluate_def, bind_def]
QED

Theorem pop_target_subscript_base_exception:
  eval_base_place cx bt s = (INR ex,s1) ==>
  eval_base_place cx (SubscriptTarget bt e) s = (INR ex,s1)
Proof
  simp[Once evaluate_def, bind_def]
QED

Theorem pop_target_subscript_index_exception:
  eval_base_place cx bt s = (INL pv,s1) /\
  eval_expr cx e s1 = (INR ex,s2) ==>
  eval_base_place cx (SubscriptTarget bt e) s = (INR ex,s2)
Proof
  simp[Once evaluate_def, bind_def]
QED

Theorem pop_target_subscript_read_exception:
  eval_base_place cx bt s = (INL pv,s1) /\
  eval_expr cx e s1 = (INL tv,s2) /\
  read_result cx tv s2 = (INR ex,s3) ==>
  eval_base_place cx (SubscriptTarget bt e) s = (INR ex,s3)
Proof
  simp[Once evaluate_def, bind_def]
QED

(* The operand judgment at the index cut is available, but has no saved-pv
   taint clause.  This ledger does not assert that such a clause follows. *)
Theorem pop_target_index_ptr_premise:
  body_base_target_ptr_ok cx (SubscriptTarget bt e) /\
  eval_base_place cx bt s = (INL pv,s1) ==>
  body_base_target_ptr_ok cx bt /\ body_expr_ptr_ok cx e
Proof
  simp[body_base_target_ptr_ok_def] >> metis_tac[]
QED

(* Compilation is a total state monad: runtime exceptions are not compiler
   outcomes.  Keep the callback arbitrary, unlike target_map_step's concrete
   compile_expr instance. *)
Theorem pop_compile_target_map_cut:
  compile_get_target_ptr cfn ce bt st =
    ((base_op,loc,SOME (MapPT kt vt)),st1) /\
  lower_value cfn ce (expr_type e) e st1 = (key,st2) ==>
  compile_get_target_ptr cfn ce (SubscriptTarget bt e) st =
    (do hashed <- (if is_bytestring_type kt then
                    compile_keccak256_key key F else return key);
        slot <- compile_mapping_subscript base_op hashed;
        return (slot,loc,SOME (value_type_place vt))
     od) st2
Proof
  simp[Once compile_get_target_ptr_def, comp_bind_def, LET_THM]
QED

Theorem pop_compile_target_array_cut:
  compile_get_target_ptr cfn ce bt st =
    ((base_op,loc,SOME (ValPT (ArrayT ty bound))),st1) /\
  lower_value cfn ce (expr_type e) e st1 = (idx,st2) ==>
  compile_get_target_ptr cfn ce (SubscriptTarget bt e) st =
    (do ptr <- compile_array_subscript base_op idx
          (case bound of Dynamic n => T | _ => F)
          (case bound of Fixed n => n | _ => 0)
          (word_scale (case loc of SOME l => l | NONE => LocMemory))
          (elem_size_in_location ce
            (case loc of SOME l => l | NONE => LocMemory) ty)
          (is_signed_type (expr_type e))
          (compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca
            (case loc of SOME l => l | NONE => LocMemory));
        return (ptr,loc,SOME (ValPT ty))
     od) st2
Proof
  Cases_on `bound` >>
  simp[Once compile_get_target_ptr_def, comp_bind_def, LET_THM]
QED

Theorem pop_compile_target_attribute_cut:
  compile_get_target_ptr cfn ce bt st = ((base_op,loc,pt),st1) /\
  fields = get_struct_fields ce.ce_struct_fields
    (case pt of SOME (ValPT (StructT sn)) => nsid_to_string sn | _ => "") /\
  offset = (if loc = SOME LocStorage \/ loc = SOME LocTransient then
              struct_field_offset_slots fields fld
            else struct_field_offset fields fld) ==>
  compile_get_target_ptr cfn ce (AttributeTarget bt fld) st =
    (do ptr <- emit_op ADD [base_op; Lit (n2w offset)];
        return (ptr,loc,
          case ALOOKUP fields fld of SOME (ty,sz) => SOME (ValPT ty)
                                  | NONE => NONE)
     od) st1
Proof
  strip_tac >> Cases_on `loc` >>
  gvs[Once compile_get_target_ptr_def, comp_bind_def, LET_THM] >>
  Cases_on `x` >> simp[]
QED

Theorem pop_target_subscript_success_iff:
  eval_base_place cx (SubscriptTarget bt e) s = (INL out,s4) <=>
  ?pv s1 tv s2 v s3.
    eval_base_place cx bt s = (INL pv,s1) /\
    eval_expr cx e s1 = (INL tv,s2) /\
    read_result cx tv s2 = (INL v,s3) /\
    extend_place cx pv (ValueSubscript v) s3 = (INL out,s4)
Proof
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem pop_target_attribute_success_iff:
  eval_base_place cx (AttributeTarget bt fld) s = (INL out,s2) <=>
  ?pv s1. eval_base_place cx bt s = (INL pv,s1) /\
    extend_place cx pv (AttrSubscript fld) s1 = (INL out,s2)
Proof
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> metis_tac[]
QED

(* Premise ledger: body_base_target_ptr_ok supplies the recursive target and
   the index operand judgment via pop_target_index_ptr_premise.  At each use
   that operand judgment still requires body_inv and expr_body_pre for the
   intermediate source state, not merely the original Pop entry state.
   The compiler cuts retain base_op, loc, and the descriptor across lower_value.
   The array continuation loads a dynamic length at base_op after the index
   effects (compile_array_subscript_def); field selection does no evaluation.
   For storage/transient arrays a captured child can already be globally dead
   at this cut.  Neither expr_body_pre's source typing/call conditions nor the
   index judgment states a local saved-child taint bound.  Deriving that bound
   for real typed writes and INVOKE is the remaining operational obligation.
   These equations make no assertion that endpoint global liveness supplies it. *)

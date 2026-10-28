(* #543 inventory: unconditional source derivations and all-state RETURN-body
   transport in an explicit recursive subdomain, NOT whole-program simulation. *)
Theory sourceMeaningWitnessTest
Ancestors
  sourceMeaningPolicy sourceMeaningProgram sourceMeaningProgramDefs sourceMeaningRuntime
  sourceMeaningStmt sourceMeaningCallDefs sourceMeaningDefs sourceMeaningConst
  sourceModuleFrontendLibTest sourceModuleDecl sourceModuleEnv sourceModuleDefs
  sourceResolveModules sourceResolve sourceSyntax sourceConstEnv sourceConstEval
  sourceConstValue sourceExprDefs vyperInterpreter vyperAST alist list
Libs
  sourceModuleParityLib intLib wordsLib

fun holbuild_extra_deps (_ : string list) = ();
val () = holbuild_extra_deps ["fixtures/check_contract/source_syntax",
  "../lowering/defs/bytecode/folded-value-witnesses.txt",
  "../lowering/defs/bytecode/folded-value-parity-fixtures.txt"];

fun fields expected tm = let val (h,args) = strip_comb tm in
  if fst (dest_const h) = expected then SOME args else NONE end;
fun one expected tm = case fields expected tm of SOME [x] => SOME x | _ => NONE;
fun computed tm = rhs (concl (EVAL tm));
fun ok tm = one "SM_Ok" (computed tm);
fun some tm = one "SOME" (computed tm);
fun map_all f [] = SOME []
  | map_all f (h::t) = case (f h,map_all f t) of
      (SOME x,SOME xs) => SOME (x::xs) | _ => NONE;

(* This proof-producing recursion reads ONLY original syntax and independently
   resolved source values/types. Generated runtime expressions are not inputs. *)
fun derive types scopes table constants ty original = let
  fun relation m = ``source_meaning_source ^types ^scopes ^table ^constants ^ty ^original ^m``
  fun child t e = derive types scopes table constants t e
  val resolution = EVAL ``source_resolve_candidate ^scopes ^table ^original``
  fun run resolved = let
    val value_eq = EVAL ``source_meaning_const ^constants ^resolved``
    val result = rhs (concl value_eq)
    val stage = prove (``source_meaning_stage ^scopes ^table ^constants ^original ^result``,
      simp[source_meaning_stage_def,resolution,value_eq])
    fun dynamic () = let val (head,args) = strip_comb original
      fun unary uop child_original = case child ty child_original of NONE => NONE
        | SOME (m,th) => let val term = ``SM_Unary ^ty ^uop ^m``
          val domain = EVAL ``source_expr_unary_domain ^uop ^ty``
          in if aconv (rhs (concl domain)) T then SOME (term,
            prove (relation term, irule sourceMeaningDefsTheory.unary >> simp[stage,domain,th]))
            else NONE end
      fun binary bop left right =
        if aconv bop ``SCB_LShift`` orelse aconv bop ``SCB_RShift`` then NONE else
        case (child ty left,child ty right) of
          (SOME (l,lt),SOME (r,rt)) => let val term = ``SM_Binary ^ty ^bop ^l ^r``
            val domain = EVAL ``source_expr_binary_domain ^bop ^ty``
            in if aconv (rhs (concl domain)) T then SOME (term,
              prove (relation term, irule sourceMeaningDefsTheory.binary >>
                simp[stage,domain,lt,rt])) else NONE end
        | _ => NONE
      fun names () = case some ``source_expr_path ^original`` of NONE => NONE
        | SOME names => (case some ``source_resolve_name ^scopes ^table ^names`` of
          NONE => NONE | SOME pair => let val (path,kind) = pairSyntax.dest_pair pair
            in if not (aconv kind ``SR_Dynamic``) orelse
              not (aconv (computed ``ALOOKUP ^types ^path``) ``SOME ^ty``) then NONE else
              let val term = ``SM_Name ^ty ^path``
              in SOME (term,prove (relation term,
                irule sourceMeaningDefsTheory.name >>
                simp[stage,EVAL ``source_expr_path ^original``,
                  EVAL ``source_resolve_name ^scopes ^table ^names``,
                  EVAL ``ALOOKUP ^types ^path``])) end end)
      in case (fst (dest_const head),args) of
        ("SX_Unary",[uop,e]) => unary uop e
      | ("SX_Binary",[bop,l,r]) => binary bop l r
      | ("SX_Boolean",[boolop,children]) =>
          if not (aconv ty ``BaseT BoolT``) then NONE else
          (case map_all (child ``BaseT BoolT``) (#1 (listSyntax.dest_list children)) of
            NONE => NONE | SOME results => let
              val ms = listSyntax.mk_list (map #1 results,``:source_meaning``)
              val term = ``source_meaning_boolean ^boolop ^ms``
              in SOME (term,prove (relation term,
                irule sourceMeaningDefsTheory.boolean >> simp (stage :: map #2 results))) end)
      | _ => names () end
    in case one "SC_Value" result of SOME value => let
        val lit_eq = EVAL ``source_const_value_literal ^value``
        in case one "SOME" (rhs (concl lit_eq)) of
          SOME lit => let val term = ``SM_Literal ^ty ^lit`` in SOME (term,
            prove (relation term,irule sourceMeaningDefsTheory.constant >>
              qexists_tac `^value` >> simp[stage,lit_eq])) end
        | NONE => let val term = ``SM_Constant ^ty ^value`` in SOME (term,
            prove (relation term,irule sourceMeaningDefsTheory.aggregate >> simp[stage,lit_eq])) end
        end
      | NONE => if Option.isSome (fields "SC_NotConstant" result) then dynamic () else NONE
    end
  in case one "SOME" (rhs (concl resolution)) of NONE => NONE
    | SOME resolved =>
      if Option.isSome (fields "SCE_Call" resolved) orelse
         Option.isSome (fields "SCE_Unsupported" resolved) then NONE
      else run resolved
  end;

val covered = ref 0;
val missing = ref 0;
val accepted = ref 0;
fun body name ctx declaration = case fields "SD_Function" declaration of
  NONE => ()
| SOME [id,decorators,args,defaults,annotation,original] => let
  val label = stringSyntax.fromHOLstring id
  fun outside why = (missing := !missing + 1;
    print ("SOURCE_MEANING_BODY_REMAINING " ^ name ^ "." ^ label ^ " " ^ why ^ "\n"))
  in case #1 (listSyntax.dest_list original) of
    [stmt] => (case fields "SS_Return" stmt of SOME [option] =>
      (case one "SOME" option of NONE => outside "bare-return"
      | SOME expression => (case (ok ``source_module_args ^ctx ^args``,
          ok ``source_module_return_type ^ctx ^annotation``) of
        (SOME params,SOME ty) => let
          val localctx = computed ``source_module_function_context ^ctx ^id ^args ^params``
          val scopes = computed ``(^localctx).sm_scopes``
          val table = computed ``(^localctx).sm_table``
          val constants = computed ``(^localctx).sm_constants``
          val types = computed ``source_meaning_parameter_types ^ctx ^id ^args ^params``
          in case derive types scopes table constants ty expression of
            NONE => outside "expression-outside-recursive-subdomain"
          | SOME (m,source) => let
              val expr_eq = EVAL ``source_module_expression 80 ^localctx ^ty ^expression``
              in case one "SM_Ok" (rhs (concl expr_eq)) of
                NONE => raise Fail ("previously accepted expression failed: " ^ name)
              | SOME code => let
                  val locals = prove (``source_meaning_locals ^types ^localctx``,
                    rw[source_meaning_locals_def,AllCaseEqs()] >> gvs[] >> EVAL_TAC)
                  val transport = SIMP_RULE (srw_ss()) []
                    (Q.INST [`ctx` |-> `^localctx`] (SPEC_ALL source_meaning_return_transport))
                  val th = MATCH_MP transport (LIST_CONJ [source,locals,expr_eq])
                  val _ = save_thm (name ^ "_" ^ label ^ "_source_expression",source)
                  val _ = save_thm (name ^ "_" ^ label ^ "_source_return_transport",th)
                  in covered := !covered + 1;
                    print ("SOURCE_MEANING_RECURSIVE_RETURN " ^ name ^ "." ^ label ^ "\n") end
              end
          end
      | _ => outside "signature-not-accepted"))
    | _ => outside "body-not-single-return")
  | _ => outside "body-not-single-return" end
| _ => raise Fail "source function syntax arity";

val () = List.app (fn name => let val phase = sourceModuleParityLib.certified_phase name
  in case one "SM_Ok" (rhs (concl phase)) of
    NONE => if name = "method_id_var" then print "SOURCE_MEANING_PIN_REJECT method_id_var\n"
      else raise Fail ("unexpected source rejection " ^ name)
  | SOME retained => let
      val _ = accepted := !accepted + 1
      val _ = save_thm (name ^ "_constant_dependencies_meaning",
        MATCH_MP source_meaning_simple_constants_exist phase)
      val program = sourceModuleParityLib.program name
      val registry = valOf (some ``source_resolve_program_registry ^program [["main"]]``)
      val constants = valOf (one "SCEnv_Resolved"
        (valOf (some ``source_resolve_registry_constants ^registry``)))
      val syntax = List.nth (#2 (strip_comb program),0)
      val trust = sourceModuleParityLib.trust name
      val ctx = computed ``source_module_context ^trust ^registry ^constants ["main"] ^syntax``
      val declarations = #1 (listSyntax.dest_list (hd (#2 (strip_comb syntax))))
      in List.app (body name ctx) declarations end
  end) sourceModuleParityLib.names;
val () = if !accepted = 36 andalso !covered = 21 andalso !missing = 19 then ()
  else raise Fail "source meaning witness coverage changed: review the exact staged boundary";
val () = print ("SOURCE_MEANING_WITNESS_TOTAL constant_dependencies=36 recursive_return_bodies=" ^
  Int.toString (!covered) ^ " remaining_bodies=" ^ Int.toString (!missing) ^ "\n");
val () = sourceModuleParityLib.audit "sourceMeaningWitnessTest";

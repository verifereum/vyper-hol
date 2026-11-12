(* Term-only selectors for the checked induction interface.  These functions
 * select obligations; they never turn an induction premise into a theorem. *)
structure guardSourceSchemaLib =
struct
  open HolKernel boolSyntax

  fun head tm = #Name (dest_thy_const (#1 (strip_comb tm)))

  fun evaluator tm =
    let val (h,args) = strip_comb tm
        val n = head h
    in (List.exists (fn s => s = n)
          ["eval_stmt", "eval_stmts", "eval_iterator", "eval_for",
           "eval_expr", "eval_exprs", "eval_expr_results", "eval_base_place",
           "eval_target_place"] andalso
        length args = (if n = "eval_for" then 6 else 3)) orelse
       (List.exists (fn s => s = n)
          ["assign_tuple_targets", "assign_tuple_target_list"] andalso
        length args = 4)
    end handle HOL_ERR _ => false

  fun outer_evaluator tm =
    let val body = #2 (strip_forall tm)
        val (pre,post) = dest_imp body
        val equations = List.filter
          (fn a => is_eq a andalso evaluator (lhs a)) (strip_conj pre)
    in case equations of
         [eq] => lhs eq
       | [] => outer_evaluator post
       | _ => raise Fail "Ambiguous outer evaluator in induction branch"
    end

  fun label tm =
    let val (h,args) = strip_comb (outer_evaluator tm)
        val n = head h
        val arg = List.nth (args,1)
        fun shape t = if listSyntax.is_nil t then "nil" else "cons"
        fun expr e =
          let val (_,xs) = strip_comb e
          in if head e = "Call" then "Expr_Call_" ^ head (List.nth (xs,1))
             else "Expr_" ^ head e end
        fun stmt s =
          let val (_,xs) = strip_comb s
              val c = head s
          in if c = "Return" then "Return_" ^ head (hd xs)
             else if c = "Raise" then head (hd xs)
             else if c = "Assert" then head (List.nth (xs,1))
             else if c = "Assign" then
               (if head (hd xs) = "BaseTarget" then "Assign_Base" else "Assign_Tuple")
             else c end
    in if n = "eval_stmt" then stmt arg
       else if n = "eval_stmts" then "Stmts_" ^ shape arg
       else if n = "eval_iterator" then "Iterator_" ^ head arg
       else if n = "eval_for" then "For_" ^ shape (List.nth (args,4))
       else if n = "eval_expr" then expr arg
       else if n = "eval_exprs" then "Exprs_" ^ shape arg
       else if n = "eval_expr_results" then "Results_" ^ shape arg
       else if n = "eval_base_place" then "BasePlaceRoot_" ^ head arg
       else if n = "eval_target_place" then "TargetPlace"
       else if n = "assign_tuple_targets" then "TupleStore_" ^ head arg
       else if n = "assign_tuple_target_list" then
         "TupleStores_" ^ shape arg ^ "_" ^ shape (List.nth (args,2))
       else raise Fail ("Unknown evaluator " ^ n)
    end

  fun manifest induction =
    let val body = #2 (strip_forall (concl induction))
        val branches = strip_conj (#1 (dest_imp body))
        val labelled = map (fn tm => (label tm,tm)) branches
        val labels = map #1 labelled
        val _ = if length (mk_set labels) = length labels then ()
                else raise Fail "Duplicate evaluator branch labels"
    in labelled end

  fun branch induction name =
    case List.find (fn (n,_) => n = name) (manifest induction) of
      SOME (_,tm) => tm
    | NONE => raise Fail ("Unknown induction branch " ^ name)

  fun starts prefix s = String.isPrefix prefix s
  fun owner name =
    if starts "Expr_Call_" name then "calls"
    else if List.exists (fn p => starts p name)
      ["Stmts_", "Exprs_", "Results_", "Iterator_", "For_"] orelse
      List.exists (fn n => n = name) ["If", "Expr_IfExp", "For"] then "lists"
    else if List.exists (fn p => starts p name)
      ["Assign_", "TupleStore_", "TupleStores_"] orelse
      List.exists (fn n => n = name)
        ["Append", "Expr_Pop", "AugAssign", "AnnAssign"] then "writes"
    else "values"
end

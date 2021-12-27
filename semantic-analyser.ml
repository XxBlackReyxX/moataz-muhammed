(* semantic-analyser.ml
 * The semantic analysis phase of the compiler
 *
 * Programmer: Mayer Goldberg, 2021
 *)

#use "tag-parser.ml";;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;

type var' = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | ScmConst' of sexpr
  | ScmVar' of var'
  | ScmBox' of var'
  | ScmBoxGet' of var'
  | ScmBoxSet' of var' * expr'
  | ScmIf' of expr' * expr' * expr'
  | ScmSeq' of expr' list
  | ScmSet' of var' * expr'
  | ScmDef' of var' * expr'
  | ScmOr' of expr' list
  | ScmLambdaSimple' of string list * expr'
  | ScmLambdaOpt' of string list * string * expr'
  | ScmApplic' of expr' * (expr' list)
  | ScmApplicTP' of expr' * (expr' list);;


let var_eq v1 v2 =
match v1, v2 with
  | VarFree (name1), VarFree (name2) -> String.equal name1 name2
  | VarBound (name1, major1, minor1), VarBound (name2, major2, minor2) ->
    major1 = major2 && minor1 = minor2 && (String.equal name1 name2)
  | VarParam (name1, index1), VarParam (name2, index2) ->
       index1 = index2 && (String.equal name1 name2)
  | _ -> false

let list_eq eq l1 l2 = (List.length l1) = (List.length l2) && List.for_all2 eq l1 l2;;

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | ScmConst' (sexpr1), ScmConst' (sexpr2) -> sexpr_eq sexpr1 sexpr2
  | ScmVar' (var1), ScmVar' (var2) -> var_eq var1 var2
  | ScmIf' (test1, dit1, dif1), ScmIf' (test2, dit2, dif2) -> (expr'_eq test1 test2) &&
                                            (expr'_eq dit1 dit2) &&
                                              (expr'_eq dif1 dif2)
  | (ScmSeq' (exprs1), ScmSeq' (exprs2) | ScmOr' (exprs1), ScmOr' (exprs2)) ->
        list_eq expr'_eq exprs1 exprs2
  | (ScmSet' (var1, val1), ScmSet' (var2, val2) | ScmDef' (var1, val1), ScmDef' (var2, val2)) ->
        (var_eq var1 var2) && (expr'_eq val1 val2)
  | ScmLambdaSimple' (vars1, body1), ScmLambdaSimple' (vars2, body2) ->
     (list_eq String.equal vars1 vars2) && (expr'_eq body1 body2)
  | ScmLambdaOpt' (vars1, var1, body1), ScmLambdaOpt' (vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (list_eq String.equal vars1 vars2) && (expr'_eq body1 body2)
  | ScmApplic' (e1, args1), ScmApplic' (e2, args2) ->
     (expr'_eq e1 e2) && (list_eq expr'_eq args1 args2)
  | ScmApplicTP' (e1, args1), ScmApplicTP' (e2, args2) ->
      (expr'_eq e1 e2) && (list_eq expr'_eq args1 args2)
  | ScmBox' (v1), ScmBox' (v2) -> var_eq v1 v2
  | ScmBoxGet' (v1), ScmBoxGet' (v2) -> var_eq v1 v2
  | ScmBoxSet' (v1, e1), ScmBoxSet' (v2, e2) -> (var_eq v1 v2) && (expr'_eq e1 e2)
  | _ -> false;;

let unannotate_lexical_address = function
| (VarFree name | VarParam (name, _) | VarBound (name, _, _)) -> ScmVar name

let rec unanalyze expr' =
match expr' with
  | ScmConst' s -> ScmConst(s)
  | ScmVar' var -> unannotate_lexical_address var
  | ScmBox' var -> ScmApplic(ScmVar "box", [unannotate_lexical_address var])
  | ScmBoxGet' var -> unannotate_lexical_address var
  | ScmBoxSet' (var, expr') -> ScmSet (unannotate_lexical_address var, unanalyze expr')
  | ScmIf' (test, dit, dif) -> ScmIf (unanalyze test, unanalyze dit, unanalyze dif)
  | ScmSeq' expr's -> ScmSeq (List.map unanalyze expr's)
  | ScmSet' (var, expr') -> ScmSet (unannotate_lexical_address var, unanalyze expr')
  | ScmDef' (var, expr') -> ScmDef (unannotate_lexical_address var, unanalyze expr')
  | ScmOr' expr's -> ScmOr (List.map unanalyze expr's)
  | ScmLambdaSimple' (params, expr') ->
        ScmLambdaSimple (params, unanalyze expr')
  | ScmLambdaOpt'(params, param, expr') ->
        ScmLambdaOpt (params, param, unanalyze expr')
  | (ScmApplic' (expr', expr's) | ScmApplicTP' (expr', expr's)) ->
        ScmApplic (unanalyze expr', List.map unanalyze expr's);;

let string_of_expr' expr' =
    string_of_expr (unanalyze expr');;

module type SEMANTIC_ANALYSIS = sig
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
  val run_semantics : expr -> expr'
end;; (* end of module type SEMANTIC_ANALYSIS *)

module Semantic_Analysis : SEMANTIC_ANALYSIS = struct

  let rec lookup_in_rib name = function
    | [] -> None
    | name' :: rib ->
       if name = name'
       then Some(0)
       else (match (lookup_in_rib name rib) with
             | None -> None
             | Some minor -> Some (minor + 1));;

  let rec lookup_in_env name = function
    | [] -> None
    | rib :: env ->
       (match (lookup_in_rib name rib) with
        | None ->
           (match (lookup_in_env name env) with
            | None -> None
            | Some(major, minor) -> Some(major + 1, minor))
        | Some minor -> Some(0, minor));;

  let tag_lexical_address_for_var name params env = 
    match (lookup_in_rib name params) with
    | None ->
       (match (lookup_in_env name env) with
        | None -> VarFree name
        | Some(major, minor) -> VarBound(name, major, minor))
    | Some minor -> VarParam(name, minor);;


    (* Helping stuff  ********************************************************************)

    exception X_invalid_expr;;
    exception Var_Not_Here_Param;;
    exception Var_Not_Here_Bound;;
    
    let safe_find pred lst = 
      try Some(List.find pred lst)
      with Not_found -> None;;
    
    let rec range i j = if i > j then [] else i :: (range (i+1) j);;

    let rec search_lst line_env vr n = 
      match line_env with
        | v::rest -> (if v=vr then n else search_lst rest vr (n+1))
        | [] -> raise Var_Not_Here_Param;;
    
    let rec search_bound env vr minor = match env with
    | env::rest -> (try(let major = (search_lst env vr 0) in (minor, major)) 
            with Var_Not_Here_Param -> search_bound rest vr (minor+1))
    | [] -> raise Var_Not_Here_Bound;;

    let check_vars env vr = match env with
    | [] -> VarFree(vr)
    | env::rest -> try VarParam(vr, search_lst env vr 0) 
          with Var_Not_Here_Param -> (try(let (minor, major) = search_bound rest vr 0 
              in VarBound(vr,minor, major))
                with Var_Not_Here_Bound -> VarFree(vr));;

    (* Var Lexical Address *)
    let var_lexical_address params bound x = 
      if (List.mem x params) then 
          let lst = (List.combine params (range 0 ((List.length params) - 1 ))) in
          let (a, b) = (List.find (fun (a,b)-> String.equal x a) lst) in
          ScmVar'(VarParam(a,b)) 
      else 
        let ans = List.combine bound (range 0 ((List.length bound) - 1)) in 
        let ans = safe_find(fun (my_list, layer)-> List.mem x my_list) ans in
        match ans with 
      |Some(my_list, layer) ->  let lst = (List.combine my_list (range 0 ((List.length my_list) - 1 ))) in
                                  let (my_var, index) = (List.find (fun (a,b)-> String.equal x a) lst) in    
                                  ScmVar'(VarBound(my_var, layer, index))
      |None -> ScmVar'(VarFree (x));;
      
    (* Lexical Address *)   
    let rec lexical_address params bound = function 
      | ScmConst(x) -> ScmConst'(x)
      | ScmIf(test,alt,elsee) -> ScmIf'((lexical_address params bound test) , (lexical_address params bound alt),( lexical_address params bound elsee))
      | ScmSeq (lst) -> ScmSeq' (List.map (lexical_address params bound) lst) 
      | ScmSet(ScmVar(expr1),expr2) -> ScmSet'((check_vars (params::bound) expr1), (lexical_address params bound expr2))
      | ScmDef (ScmVar(x), value) -> ScmDef'((check_vars (params::bound) x),(lexical_address params bound value))
      | ScmOr (lst) -> ScmOr' (List.map (lexical_address params bound) lst)
      | ScmLambdaSimple(vars,body) -> ScmLambdaSimple' (vars, (lexical_address vars (params::bound) body))
      | ScmLambdaOpt(vars,variadic,body) -> let param_list =  (List.rev (variadic::(List.rev vars))) in
      ScmLambdaOpt'(vars,variadic, (lexical_address param_list (params::bound) body)) 
      | ScmApplic(rator, rands) -> ScmApplic'((lexical_address params bound rator), (List.map (lexical_address params bound) rands))
      | ScmVar(x)-> (var_lexical_address params bound x) 
      | _ -> raise X_this_should_not_happen;;

      (* Tails *)
      let rec tail_calls tp e = match e with 
      | ScmConst'(x) -> e
      | ScmVar'(x) -> e
      | ScmBox'(x) -> e
      | ScmBoxGet'(x) -> e
      | ScmBoxSet'(x,y) -> e
      | ScmIf'(test,alt,elsee) -> ScmIf' ((tail_calls false test) , (tail_calls tp alt) , (tail_calls tp elsee))
      | ScmDef'(var,value) -> ScmDef' (var , (tail_calls  tp value))
      | ScmOr'(lst) -> let last = (List.hd(List.rev lst)) in
                    let first = (List.rev(List.tl(List.rev lst))) in
                    ScmOr' ((List.map (tail_calls false) first) @ [(tail_calls tp last)])
      | ScmSeq'(lst) -> let last = (List.hd(List.rev lst)) in
                     let first = (List.rev(List.tl(List.rev lst))) in
                     ScmSeq' ((List.map (tail_calls false) first) @ [(tail_calls tp last)])
      | ScmSet'(var,value) -> ScmSet' (var, (tail_calls false value))
      | ScmLambdaSimple'(vars,body) -> ScmLambdaSimple'(vars, (tail_calls true body))
      | ScmLambdaOpt'(vars,variadic,body) -> ScmLambdaOpt'(vars,variadic,(tail_calls true body))
      | ScmApplic'(rand,rator) -> begin match tp with
                                | true -> ScmApplicTP'((tail_calls false rand), (List.map (tail_calls false) rator))
                                | false -> ScmApplic' ((tail_calls false rand), (List.map (tail_calls false) rator)) end
      | ScmApplicTP'(rand,rator) -> raise X_invalid_expr;;

      (* Box *)
      
  (* run this first! *)
  let annotate_lexical_addresses pe = 
    (lexical_address [] [[]] pe);;

    
   (* let rec run pe params env =
      raise X_not_yet_implemented 
   in 
   run pe [] [];; *)

  let rec rdc_rac s =
    match s with
    | [e] -> ([], e)
    | e :: s ->
       let (rdc, rac) = rdc_rac s
       in (e :: rdc, rac)
    | _ -> raise X_this_should_not_happen;;
  
  (* run this second! *)
  let annotate_tail_calls e = (tail_calls false e);;
  (* let annotate_tail_calls pe =
   let rec run pe in_tail =
      raise X_not_yet_implemented 
   in 
   run pe false;; *)

  (* boxing *)

  let find_reads name enclosing_lambda expr = raise X_not_yet_implemented 


  let rec box_set expr = raise X_not_yet_implemented

  let run_semantics expr =
    box_set
      (annotate_tail_calls
         (annotate_lexical_addresses expr))

end;; (* end of module Semantic_Analysis *)

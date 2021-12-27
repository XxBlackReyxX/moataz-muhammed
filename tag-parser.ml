#use "reader.ml";;

type expr =
  | ScmConst of sexpr
  | ScmVar of string
  | ScmIf of expr * expr * expr
  | ScmSeq of expr list
  | ScmSet of expr * expr
  | ScmDef of expr * expr
  | ScmOr of expr list
  | ScmLambdaSimple of string list * expr
  | ScmLambdaOpt of string list * string * expr
  | ScmApplic of expr * (expr list);;

exception X_syntax_error of sexpr * string;;
exception X_reserved_word of string;;
exception X_proper_list_error;;
exception X_not_implemented;;
exception X_my_exception;;


let rec list_to_proper_list = function
| [] -> ScmNil
| hd::[] -> ScmPair (hd, ScmNil)
| hd::tl -> ScmPair (hd, list_to_proper_list tl);;

let rec list_to_improper_list = function
| [] -> raise X_proper_list_error
| hd::[] -> hd
| hd::tl -> ScmPair (hd, list_to_improper_list tl);;

let rec scm_append scm_list sexpr =
match scm_list with
| ScmNil -> sexpr
| ScmPair (car, cdr) -> ScmPair (car, scm_append cdr sexpr)
| _ -> raise (X_syntax_error (scm_list, "Append expects a proper list"))

let rec scm_map f sexpr =
match sexpr with
| ScmNil -> ScmNil
| ScmPair (car, cdr) -> ScmPair (f car, scm_map f cdr)
| _ -> raise (X_syntax_error (sexpr, "Map expects a list"));;

let rec scm_zip f sexpr1 sexpr2 =
match sexpr1, sexpr2 with
| ScmNil, ScmNil -> ScmNil
| ScmPair (car1, cdr1), ScmPair (car2, cdr2) -> ScmPair (f car1 car2, scm_zip f cdr1 cdr2)
| _, _ ->
    let sepxrs = list_to_proper_list [ScmSymbol "sexpr1:"; sexpr1; ScmSymbol "sexpr2:"; sexpr2] in
    raise (X_syntax_error (sepxrs, "Zip expects 2 lists of equal length"));;

let rec scm_list_to_list = function
| ScmPair (hd, tl) -> hd::(scm_list_to_list tl)
| ScmNil -> []
| sexpr -> raise (X_syntax_error (sexpr, "Expected proper list"));;

let rec scm_is_list = function
| ScmPair (hd, tl) -> scm_is_list tl
| ScmNil -> true
| _ -> false

let rec scm_list_length = function
| ScmPair (hd, tl) -> 1 + (scm_list_length tl)
| ScmNil -> 0
| sexpr -> raise (X_syntax_error (sexpr, "Expected proper list"));;

let rec untag expr =
let untag_vars vars = List.map (fun s -> ScmSymbol s) vars in
let untag_tagged_list tag exprs = list_to_proper_list (ScmSymbol tag::(List.map untag exprs)) in

let untag_lambda_opt vars var body =
let vars = match vars with
| [] -> ScmSymbol var
| _ -> list_to_improper_list (untag_vars (vars@[var])) in
list_to_proper_list ([ScmSymbol "lambda"; vars]@body) in

match expr with
| (ScmConst (ScmSymbol(_) as sexpr)
    | ScmConst (ScmNil as sexpr)
    | ScmConst (ScmPair (_, _) as sexpr)) -> list_to_proper_list [ScmSymbol "quote"; sexpr]
| ScmConst s -> s
| ScmVar (name) -> ScmSymbol(name)
| ScmIf (test, dit, ScmConst (ScmVoid)) -> untag_tagged_list "if" [test; dit]
| ScmIf (test, dit, dif) -> untag_tagged_list "if" [test; dit; dif]
| ScmSeq(exprs) -> untag_tagged_list "begin" exprs
| ScmSet (var, value) -> untag_tagged_list "set!" [var; value]
| ScmDef (var, value) -> untag_tagged_list "define" [var; value]
| ScmOr (exprs) -> untag_tagged_list "or" exprs
| ScmLambdaSimple (vars, ScmSeq(body)) ->
    let vars = list_to_proper_list (untag_vars vars) in
    let body = List.map untag body in
    list_to_proper_list ([ScmSymbol "lambda"; vars]@body)
| ScmLambdaSimple (vars, body) ->
    let vars = list_to_proper_list (untag_vars vars) in
    list_to_proper_list ([ScmSymbol "lambda"; vars; untag body])
| ScmLambdaOpt (vars, var, ScmSeq(body)) ->
    let body = List.map untag body in
    untag_lambda_opt vars var body
| ScmLambdaOpt (vars, var, body) ->
    let body = [untag body] in
    untag_lambda_opt vars var body
| ScmApplic(procedure, args) -> list_to_proper_list (List.map untag (procedure::args));;


let rec string_of_expr expr =
string_of_sexpr (untag expr)

let scm_number_eq n1 n2 =
match n1, n2 with
| ScmRational(numerator1, denominator1), ScmRational(numerator2, denominator2) ->
        numerator1 = numerator2 && denominator1 = denominator2
| ScmReal(real1), ScmReal(real2) -> abs_float(real1 -. real2) < 0.001
| _, _ -> false

let rec sexpr_eq s1 s2 =
match s1, s2 with
| (ScmVoid, ScmVoid) | (ScmNil, ScmNil)  -> true
| ScmBoolean(bool1), ScmBoolean(bool2) -> bool1 = bool2
| ScmChar(char1), ScmChar(char2) -> char1 = char2
| ScmString(string1), ScmString(string2) -> String.equal string1 string2
| ScmSymbol(symbol1), ScmSymbol(symbol2) -> String.equal symbol1 symbol2
| ScmNumber(number1), ScmNumber(number2) -> scm_number_eq number1 number2
| ScmVector(sexprs1), ScmVector(sexprs2) -> List.for_all2 sexpr_eq sexprs1 sexprs2
| ScmPair(car1, cdr1), ScmPair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
| _, _ -> false

let rec expr_eq e1 e2 =
  match e1, e2 with
  | ScmConst (sexpr1), ScmConst (sexpr2) -> sexpr_eq sexpr1 sexpr2
  | ScmVar (var1), ScmVar (var2) -> String.equal var1 var2
  | ScmIf (test1, dit1, dif1), ScmIf (test2, dit2, dif2) -> (expr_eq test1 test2) &&
                                            (expr_eq dit1 dit2) &&
                                              (expr_eq dif1 dif2)
  | (ScmSeq(exprs1), ScmSeq(exprs2) | ScmOr (exprs1), ScmOr (exprs2)) ->
        List.for_all2 expr_eq exprs1 exprs2
  | (ScmSet (var1, val1), ScmSet (var2, val2) | ScmDef (var1, val1), ScmDef (var2, val2)) ->
        (expr_eq var1 var2) && (expr_eq val1 val2)
  | ScmLambdaSimple (vars1, body1), ScmLambdaSimple (vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) && (expr_eq body1 body2)
  | ScmLambdaOpt (vars1, var1, body1), ScmLambdaOpt (vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) && (expr_eq body1 body2)
  | ScmApplic (e1, args1), ScmApplic (e2, args2) ->
     (expr_eq e1 e2) && (List.for_all2 expr_eq args1 args2)
  | _ -> false;;

module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
end;; 

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;


   (* Helping Funcs *)

   (* QQ handling *)
   let rec quasi_macro x = 
   match x with
   | ScmNil ->  ScmPair(ScmSymbol("quote"),ScmPair(x,ScmNil))
   | ScmChar a ->  x
   | ScmString a -> x
   | ScmSymbol(a)-> ScmPair(ScmSymbol("quote"),ScmPair(x,ScmNil))
   | ScmPair(ScmSymbol ("unquote"),ScmPair(sexpr,ScmNil)) -> sexpr
   | ScmPair (ScmSymbol "unquote-splicing", c) -> 
     (ScmPair (ScmSymbol "quote", (ScmPair  (ScmPair(ScmSymbol "unquote-splicing", c), ScmNil))))
     
   | ScmVector(a) ->  let pairs = (list_to_proper_list (a)) in
                      (* let run = quasi_macro pairs in *)
                  ScmPair(ScmSymbol "list->vector", quasi_macro pairs)
                   
   | ScmPair((ScmPair((ScmSymbol("unquote-splicing")), (ScmPair(a, ScmNil)))), b) -> 
           (ScmPair((ScmSymbol("append")),(ScmPair(a, (ScmPair((quasi_macro b), ScmNil))))))
   | ScmPair(a, (ScmPair((ScmSymbol("unquote-splicing")), (ScmPair(b, ScmNil))))) ->
           (ScmPair((ScmSymbol("cons")), (ScmPair((quasi_macro a), (ScmPair(b, ScmNil))))))
           
   | ScmPair(a,b) -> ScmPair((ScmSymbol("cons")), (ScmPair((quasi_macro a), (ScmPair((quasi_macro b), ScmNil)))))
   | _ -> ScmNil ;;   


   (* letrec *)

   let rec letrec_macro f x = 
    match x with
    | ScmPair(ScmNil,exprs) -> 
       (ScmPair(ScmSymbol "let",ScmPair(ScmNil,exprs)))
    | ScmPair(args ,body)-> 
    let arglist    = (scm_list_to_list args) in
    let set_args   = List.map (fun (arg) -> ScmPair(ScmSymbol "set!",arg)) arglist in
    let body_list  = (scm_list_to_list body) in 
    let body_list  = List.append set_args body_list in
    let body_pairs = (list_to_proper_list body_list) in
    let args = List.map (fun x -> match x with
                                  | (ScmPair(x,y))->  ScmPair(x,(ScmPair(ScmSymbol("quote"),ScmPair(ScmSymbol("whatever"),ScmNil))))
                                  | _ -> ScmNil) (scm_list_to_list args) in
    let args = (list_to_proper_list args) in
    let sexpr =  (ScmPair(ScmSymbol ("let"), (ScmPair (args, body_pairs))))
    in (f sexpr)
    | _ -> raise X_my_exception  ;; 

    (* Cond *)
    let rec cond_macro = function
    | ScmNil -> ScmNil
    | ScmPair(ScmPair(ScmSymbol "else",rib),_) -> 
      ScmPair (ScmSymbol ("begin"),rib) 

    |ScmPair(ScmPair(x,ScmPair(ScmSymbol("=>"),y)),ScmNil) -> (ScmPair (ScmSymbol "let",
          ScmPair
            (ScmPair (ScmPair (ScmSymbol "value", ScmPair (x, ScmNil)),
              ScmPair
              (ScmPair (ScmSymbol "f",
                ScmPair (ScmPair (ScmSymbol "lambda", ScmPair (ScmNil,y)),
                  ScmNil)),
              ScmNil)),
            ScmPair
            (ScmPair (ScmSymbol "if",
              ScmPair (ScmSymbol "value",
                ScmPair (ScmPair (ScmPair (ScmSymbol "f", ScmNil), ScmPair (ScmSymbol "value", ScmNil)), ScmNil))),
            ScmNil))))

      | ScmPair(ScmPair(x,ScmPair(ScmSymbol("=>"),y)),ribs) -> 
            ScmPair (ScmSymbol "let",
            ScmPair
             (ScmPair (ScmPair (ScmSymbol "value", ScmPair (x, ScmNil)),
               ScmPair
                (ScmPair (ScmSymbol "f",
                  ScmPair (ScmPair (ScmSymbol "lambda", ScmPair (ScmNil, y)),
                   ScmNil)),
                ScmPair
                 (ScmPair (ScmSymbol "rest",
                   ScmPair (ScmPair (ScmSymbol "lambda", ScmPair (ScmNil, ScmPair ((cond_macro ribs), ScmNil))),
                    ScmNil)),
                 ScmNil))),
             ScmPair
              (ScmPair (ScmSymbol "if",
                ScmPair (ScmSymbol "value",
                 ScmPair (ScmPair (ScmPair (ScmSymbol "f", ScmNil), ScmPair (ScmSymbol "value", ScmNil)),
                  ScmPair (ScmPair (ScmSymbol "rest", ScmNil), ScmNil)))),
              ScmNil)))
  
    |ScmPair(ScmPair(test,alt),ScmNil) -> (ScmPair (ScmSymbol "if",ScmPair(test,ScmPair(ScmPair(ScmSymbol("begin"),alt),ScmNil))))

    |ScmPair(ScmPair(test,alt),elsee) -> (ScmPair (ScmSymbol "if",ScmPair(test,ScmPair(ScmPair(ScmSymbol("begin"),alt),ScmPair ((cond_macro elsee), ScmNil)))))
    
    | _ -> raise X_my_exception ;;


  let rec opt_lambda_args_helper args lst = match args with         
  | ScmPair(ScmSymbol(s), rest) -> opt_lambda_args_helper rest (lst@[s])
  | ScmSymbol(after_dot) -> (lst, after_dot)
  |_-> raise X_my_exception;;

  let lambda_opt_args args = opt_lambda_args_helper args [];;

  let rec let_vars rib vars = 
    (List.fold_right (fun cur (vars) ->
      match cur with 
      | ScmPair(var,_) -> ScmPair(var,vars)
      | _ -> raise X_my_exception
      )
      (scm_list_to_list rib) (ScmNil)) ;;

  let rec let_exps rib exps = 
    (List.fold_right (fun cur (exps) ->
      match cur with 
      | ScmPair(_,ScmPair(value,ScmNil)) -> ScmPair(value,exps)
      | (ScmPair(_,(ScmPair(ScmSymbol("quote"),(ScmPair(x,ScmNil)))))) -> ScmPair((ScmPair(ScmSymbol("quote"),(ScmPair(x,ScmNil)))),exps)
      | _ -> raise X_not_implemented
      )
      (scm_list_to_list rib) (ScmNil)) ;;
  

let rec tag_parse_expression sexpr =
let sexpr = macro_expand sexpr in
match sexpr with 
(* 2.1 Constants *)
| ScmNil ->  ScmConst (ScmNil)
| ScmBoolean bol -> if (bol = (true)) then (ScmConst (ScmBoolean true)) else (ScmConst (ScmBoolean false))
| ScmChar ch -> ScmConst (ScmChar ch) 
| ScmNumber (ScmRational (a, b)) -> ScmConst (ScmNumber (ScmRational (a, b)))
| ScmNumber (ScmReal (a)) -> ScmConst (ScmNumber (ScmReal (a)))
| ScmString str -> ScmConst(ScmString str)
| ((ScmPair (ScmSymbol "quote", (ScmPair (ScmSymbol symb, ScmNil))))) -> ScmConst (ScmSymbol symb)
| (ScmPair (ScmSymbol "quote", ScmPair (ScmPair(ScmSymbol "quote", symb) ,ScmNil))) -> ScmConst (ScmPair (ScmSymbol "quote", symb))
| (ScmPair (ScmSymbol "quote", ScmPair (symbs,ScmNil))) -> ScmConst symbs
(* 2.2 Variables *)
| ScmSymbol var -> if (List.mem var reserved_word_list) then raise (X_reserved_word var) else ScmVar var
(* 2.3 Conditionals *)
| (ScmPair (ScmSymbol "if", ScmPair ( a, ScmPair ( b, ScmPair ( c, ScmNil))))) -> ScmIf (tag_parse_expression a, tag_parse_expression b, tag_parse_expression c)
| (ScmPair (ScmSymbol "if", ScmPair ( a, ScmPair ( b, ScmNil)))) -> ScmIf (tag_parse_expression a, tag_parse_expression b, ScmConst ScmVoid)
(* 2.4 disjunctions *)
| (ScmPair (ScmSymbol "or", ScmPair ( a, ScmNil))) -> tag_parse_expression a
| (ScmPair (ScmSymbol "or", ScmNil)) -> ScmConst (ScmBoolean false)
| (ScmPair (ScmSymbol "or", ScmPair (sexpr1,ScmPair (sexpr2,ScmNil)))) -> ScmOr [tag_parse_expression sexpr1; tag_parse_expression sexpr2]
(* 2.5 Lambdas *)

(* Simple lambda  +  Lambda with optional arguments + Variadic *)

| (ScmPair (ScmSymbol "lambda", (ScmPair (vars, exprs)))) -> 
  if(scm_is_list vars)
    (* Simple Lambda *)
    then (
  ScmLambdaSimple(
    (List.map (fun x-> string_of_expr (tag_parse_expression x)) (scm_list_to_list vars))
    , 
    (match exprs with
    | ScmPair(a,ScmNil) -> tag_parse_expression a
    | ScmPair(a,b) -> ScmSeq ((List.map (fun x->  (tag_parse_expression x)) (scm_list_to_list (ScmPair (a,b)))))
    | _ -> ScmConst(ScmNil)
    ))
    )
    (* Optional Lambda *)
      else(
        let (args, last) = lambda_opt_args vars in
        (
          ScmLambdaOpt(
            args
            ,
          last
          ,
          (match exprs with
          | ScmPair(a,ScmNil) -> tag_parse_expression a
          | ScmPair(a,b) -> ScmSeq ((List.map (fun x->  (tag_parse_expression x)) (scm_list_to_list (ScmPair (a,b)))))
          | _ -> ScmConst(ScmNil)
          ))
        )
        )

(* 2.6.2 MIT Define *)
| (ScmPair (ScmSymbol "define",ScmPair (ScmPair(var,args),exprs))) ->
      (
      match var with 
      | ScmSymbol x -> 
        if (List.mem x reserved_word_list) 
        then 
        (raise (X_syntax_error (((ScmPair (ScmSymbol "define",ScmPair (ScmPair(var,args),exprs)))) ,
      "Expected variable on LHS of define")))
      else 
      (ScmDef(tag_parse_expression var , tag_parse_expression ((ScmPair (ScmSymbol "lambda", (ScmPair (args, exprs)))))))
      | _ -> raise (X_syntax_error (((ScmPair (ScmSymbol "define",ScmPair (ScmPair(var,args),exprs)))) ,
      "Expected variable on LHS of define"))
    )

(* 2.6.1 Define *)
| (ScmPair (ScmSymbol "define", ScmPair (symb, ScmPair (exprs, ScmNil)))) -> 
  (match symb with 
| ScmSymbol x -> if (List.mem x reserved_word_list) then 
  (raise (X_syntax_error (((ScmPair (ScmSymbol "define", ScmPair (symb, ScmPair (exprs, ScmNil))))) ,
"Expected variable on LHS of define")))
else ScmDef(tag_parse_expression symb , tag_parse_expression exprs)

| _ -> raise (X_syntax_error (((ScmPair (ScmSymbol "define", ScmPair (symb, ScmPair (exprs, ScmNil))))) ,
"Expected variable on LHS of define")))

(* 2.7 Assignments *)
| (ScmPair (ScmSymbol "set!", ScmPair (symb, ScmPair (expr, ScmNil)))) -> 
    (match symb with 
    | ScmSymbol x -> ScmSet(tag_parse_expression symb , tag_parse_expression expr)
    | _ -> raise (X_syntax_error (((ScmPair (ScmSymbol "set!", ScmPair (symb, ScmPair (expr, ScmNil))))) ,
    "Expected variable on LHS of set!")))

(* 2.8 Applications - deal with lambdas *)

| (ScmPair (var, ScmNil)) -> ScmApplic (tag_parse_expression var, [])

(* 2.9 Sequences - deal with lambdas *)
| (ScmPair (ScmSymbol "begin", exprs)) -> 
  (match exprs with 
  | ScmPair(x,ScmNil) -> tag_parse_expression x
  | ScmPair(a,b) -> 
  ScmSeq (List.map (fun x-> tag_parse_expression x) (scm_list_to_list exprs))
  | _ -> ScmConst ScmNil
  )
| (ScmPair (ScmNil, exprs)) -> 
  (match exprs with 
  | ScmPair(a,ScmNil) -> tag_parse_expression a
  | ScmPair(a,b) -> 
  ScmSeq (List.map (fun x-> tag_parse_expression x) (scm_list_to_list exprs))
  | _ -> ScmConst ScmNil
  )
| (ScmPair (var, exprs)) -> ScmApplic(tag_parse_expression var, (List.map (fun x-> tag_parse_expression x) (scm_list_to_list exprs)))

(* Implement tag parsing here *)
| _ -> raise (X_syntax_error (sexpr, "Sexpr structure not recognized"))


and macro_expand sexpr =
match sexpr with
(* Handle macro expansion patterns here *)

(* And *)
| (ScmPair (ScmSymbol "and",expr)) ->
  (match expr with 
  | ScmNil -> (ScmBoolean true)
  | ScmPair(a,ScmNil) -> macro_expand a
  | ScmPair(a,b) -> (ScmPair (ScmSymbol "if", ScmPair ( a, ScmPair ( macro_expand (ScmPair (ScmSymbol "and",b)), ScmPair ( ScmBoolean false, ScmNil)))))
  | _ -> ScmNil
  )
  (* Cond *)
| (ScmPair (ScmSymbol "cond",expr)) ->
  macro_expand(cond_macro expr)
  
  (* Let *)
| (ScmPair (ScmSymbol "let",expr)) ->
  (match expr with
  | ScmPair(ScmNil,exprs) -> 
    ScmPair (ScmPair (ScmSymbol "lambda", (ScmPair (ScmNil, exprs))), ScmNil)
    
  | ScmPair(args,exprs) ->
    (
      let vars = (let_vars args []) in
      let exps = (let_exps args []) in
      ScmPair (ScmPair (ScmSymbol "lambda", (ScmPair ( 
       vars
        , exprs))), exps)
      )
  | _ -> ScmNil
  )

  (* Let* *)
| (ScmPair (ScmSymbol "let*",expr)) ->
  (match expr with
  | ScmPair(ScmNil,exprs) -> 
    macro_expand (ScmPair (ScmSymbol "let",ScmPair(ScmNil,exprs)))
  
  | ScmPair(ScmPair(var,ScmNil),exprs) -> 
    macro_expand (ScmPair (ScmSymbol "let",ScmPair(ScmPair(var,ScmNil),exprs)))

  | ScmPair(ScmPair(var,var_expr),exprs) ->
    macro_expand (ScmPair (ScmSymbol "let",ScmPair(
      ScmPair(var,ScmNil), ScmPair(ScmPair(ScmSymbol "let*",ScmPair(var_expr,exprs)),ScmNil))))
  | _ -> ScmNil
  )
  (* Letrec *)
  | (ScmPair (ScmSymbol "letrec",expr)) ->
    macro_expand (letrec_macro macro_expand expr)

  (* quasiquote-expressions *)
  | (ScmPair (ScmSymbol "quasiquote",expr)) ->
    (match expr with
    | ScmPair(x,ScmNil) -> macro_expand (quasi_macro x)
    | _ -> ScmNil

    )
| _ -> sexpr
end;; 


(* Cond attempt *)

(* (match expr with 
  
    | ScmPair(ScmPair(rib_var,rib_expr),ScmNil) -> 
    (ScmPair (ScmSymbol "if", ScmPair 
      ( rib_var, ScmPair ( ScmPair(ScmNil,rib_expr), ScmNil))))

  | ScmPair(ScmPair(rib_var,rib_expr),rib2) -> 
    if(rib_var = ScmSymbol "else") 
      then (ScmPair(ScmNil,rib_expr))
  (* Cond-Arrow *)
  (* else if (rib_var = ScmSymbol "=>")
    then (
      (ScmPair (ScmSymbol "let",
      ScmPair
       (ScmPair (ScmPair (ScmSymbol "value", ScmPair (rib_expr, ScmNil)),
         ScmPair
          (ScmPair (ScmSymbol "f",
            ScmPair (ScmPair (ScmSymbol "lambda", ScmPair (ScmNil,rib2)),
             ScmNil)),
          ScmNil)),
       ScmPair
        (ScmPair (ScmSymbol "if",
          ScmPair (ScmSymbol "value",
           ScmPair (ScmPair (ScmPair (ScmSymbol "f", ScmNil), ScmPair (ScmSymbol "value", ScmNil)), ScmNil))),
        ScmNil))))
    ) *)
  (* Cond-else *)
    else
     (ScmPair (ScmSymbol "if", ScmPair 
      ( rib_var, ScmPair ( ScmPair(ScmNil,rib_expr), ScmPair ( ScmPair (ScmSymbol "cond",rib2), ScmNil)))))

  | _ -> ScmNil
    ) *)

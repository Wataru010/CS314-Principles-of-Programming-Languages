open List
open Ast
open ExpressionLibrary

type 'a tree = Leaf | Node of 'a tree * 'a * 'a tree

let rec insert tree x =
  match tree with
  | Leaf -> Node(Leaf, x, Leaf)
  | Node(l, y, r) ->
     if x = y then tree
     else if x < y then Node(insert l x, y, r)
     else Node(l, y, insert r x)

let construct l =
  List.fold_left (fun acc x -> insert acc x) Leaf l

(**********************************)
(* Problem 1: Tree In-order Fold  *)
(**********************************)

let rec fold_inorder f acc t =
  match t with 
  Leaf -> acc
  | Node (Leaf,value,Leaf) -> (f acc value)
  | Node (Leaf,value,right) -> (fold_inorder f (f acc value) right)
  | Node (left,value,Leaf) ->  f (fold_inorder f acc left) value
  | Node (left,value,right) ->  (fold_inorder f (f (fold_inorder f acc left) value) right)


(* fold_inorder (fun acc x -> acc @ [x]) [] (Node (Leaf, 5, Leaf)) = [5];; *)
(* fold_inorder (fun acc x -> acc @ [x]) [] (Node (Node (Leaf, 1, Leaf), 5, Leaf)) = [1; 5];; *)
(* fold_inorder (fun acc x -> acc @ [x]) [] (Node (Leaf, 5, Node (Leaf, 9, Leaf))) = [5; 9];; *)
(* fold_inorder (fun acc x -> acc @ [x]) [] (Node (Node (Node (Leaf, 1, Leaf), 3, Leaf), 5, Node (Node (Leaf, 7, Leaf), 9, Leaf))) = [1; 3; 5; 7; 9];; *)

(**********************************)
(* Problem 2: BST Remove *)
(**********************************)

exception EmptyBranch of string
let rec remove x t =
    (* return a node with min_value in a tree *)
    let rec min tree =
      match tree with
      Leaf -> raise (EmptyBranch "empty branch")
      | Node (Leaf, value, _) -> value
      | Node (left, _, _) -> min left in
    match t with
    Leaf -> Leaf
    | Node (left,value,right) ->
      if x = value then 
        match t with
        Leaf -> Leaf
        | Node (Leaf,value,Leaf) -> Leaf
        | Node (Leaf,value,right) -> right
        | Node (left,value,Leaf) -> left
        | Node (left,value,right) ->
          (* try  *)
            let min_v = min right in
            Node (left,min_v,(remove min_v right))
          (* with EmptyBranch message -> 
            try
              let max_v = max left in
              Node ((remove max_v left),max_v, right)
            with EmptyBranch message -> 
              Leaf
              match right with
              Leaf -> 
                match left with
                Leaf -> Leaf
                | Node (_,_,_) -> left
              | Node (Leaf,_,_) -> right *)
      else if x < value then
        Node ((remove x left), value, right)
      else
        Node (left, value, (remove x right))
  

(* ------ Type definitions for the abstract syntax tree defined in ast.ml ------- *)

(**********************************
    type binop = Add | Sub | Mul

    type expression =
      | Num of float
      | Var
      | Binop of binop * expression * expression
***********************************)



(**********************************
    There are some functions from expressionLibrary that you can use to debug your code.

    `parse: string -> expression` :
        translates a string in infix form (such as `x*x - 3.0*x + 2.5`) into an expression
        (treating `x` as the variable). The parse function parses according to the standard
        order of operations - so `5+x*8` will be read as `5+(x*8)`.
    `to_string: expression -> string` :
        prints expressions in a readable form, using infix notation. This function adds
        parentheses around every binary operation so that the output is completely unambiguous.
    `to_string_wo_paren: expression -> string` :
        prints expressions in a readable form, using infix notation. This function does not
        add any parentheses so it can only be used for expressions in standard forms.
    `make_exp: int -> expression` :
        takes in a length `l` and returns a randomly generated expression of length at most `2l`.
    `rand_exp_str: int -> string` :
        takes in a length `l` and returns a string representation of length at most `2l`.

    For example,

    let _ =
      (* The following code make an expression from a string
         "5*x*x*x + 4*x*x + 3*x + 2 + 1", and then convert the
         expression back to a string, finally it prints out the
         converted string
         *)
      let e = parse ("5*x*x*x + 4*x*x + 3*x + 2 + 1") in
      let s = to_string e in
      print_string (s^"\n")

    let _ =
      (* The following code make a random expression from a string
         and then convert the expression back to a string
         finally it prints out the converted string
         *)
      let e = make_exp 10 in
      let s = to_string e in
      print_string (s^"\n")
***********************************)




(**********************************)
(* Problem 3: Evaluation  *)
(**********************************)

(* evaluate : evaluates an expression for a particular value of x.
*  Example : evaluate (parse "x*x + 3") 2.0 = 7.0 *)
let rec evaluate (e:expression) (x:float) : float =
  match e with
  Num value -> value
  | Var -> x
  | Binop (op, e1, e2) -> 
    match op with
    Add -> (evaluate e1 x) +. (evaluate e2 x)
    | Sub -> (evaluate e1 x) -. (evaluate e2 x)
    | Mul -> (evaluate e1 x) *. (evaluate e2 x)



(**********************************)
(* Problem 4: Derivatives  *)
(**********************************)

let rec derivative (e:expression) : expression =
  match e with
  Num value -> Num (0.0)
  | Var -> Num (1.0)
  | Binop (op, e1, e2) -> 
    match op with
    Add -> Binop (Add, derivative e1, derivative e2)
    | Sub -> Binop (Sub, derivative e1, derivative e2)
    | Mul -> Binop(Add, Binop (Mul, derivative e1, e2), Binop (Mul, e1, derivative e2))


(**********************************)
(* Problem 5: Find Zero  *)
(**********************************)

let find_zero (e:expression) (xn:float) (epsilon:float) (lim:int)
  : float option =
  let rec helper curr_x lim = 
    if lim = 0 then
      None
    else
      let eval_curr_x = (evaluate e curr_x) in
      if (abs_float (eval_curr_x)) < epsilon then
        Some curr_x
      else
        if (evaluate (derivative e) curr_x) <> 0.0 then
          let x_next = curr_x -. ((evaluate e curr_x) /. (evaluate (derivative e) curr_x)) in
          (* print_float x_next; print_string "\n"; *)
          (helper (x_next) (lim-1))
        else
          None
      in (helper xn lim) 

(* let x = (find_zero (parse "2*x*x - x*x*x - 2") (3.0) (1e-3) (50))
let y = match x with
None -> print_float (-1.); print_string "\n";
| Some v -> print_float (v);; *)

(**********************************)
(* Problem 6: Simplification  *)
(**********************************)
  
let simplify (e:expression) : expression =
  let rec reduce exp acc = 
    match exp with
    Num v -> (v, 0)::acc
    | Var -> (1.0,1)::acc
    | Binop (op, e1, e2) -> 
      match op with 
      Add -> 
        let list_e1 = (reduce e1 []) in
        let list_e2 = (reduce e2 []) in
        let add = list_e1@list_e2 in
        (* print_tuple_list add; print_string "\n";  *)
        add; 
      | Sub ->
        let list_e1 = (reduce e1 []) in
        let list_e2 = (reduce e2 []) in
        let sub = list_e1@(List.map (fun (coef, power) -> ((-1.)*.coef, power)) list_e2) in
        (* print_tuple_list sub; print_string "\n";  *)
        sub; 
      | Mul ->
        let list_e1 = (reduce e1 []) in
        let list_e2 = (reduce e2 []) in
        let mul = List.fold_left (fun acc (coef2, power2) -> acc@(List.fold_left (fun acc (coef1, power1) -> acc@[(coef1*.coef2,power1+power2)]) [] list_e1)) [] list_e2 in
        (* print_tuple_list mul; print_string "\n";  *)
        mul;
  in  
  
  let rec combine lst =
    let fun_fold acc term =
      let (coef1, power1) = term in
      if (List.length acc = 0) then
        acc@[term]
      else
        let t_f = List.fold_left (fun t_or_f (coef2, power2) -> if power1 = power2 then true else if t_or_f = true then true else false) false acc in 
        if t_f = true then
          (List.map (fun (coef3, power3) -> if power1 = power3 then (coef1+.coef3, power3) else (coef3, power3)) acc)
        else 
          acc@[term] in
    let curr_list = List.fold_left (fun_fold) [] lst in
    let unsorted_list = List.fold_left (fun acc (coef, power) -> if coef = 0.0 then acc else acc@[(coef, power)]) [] curr_list in (*wipe out term with 0.0 as coefficient*) 
    List.rev(List.sort (fun (c1, p1) (c2, p2) -> p1 - p2) unsorted_list)
  in
  
  let rec construct lst = 
    let rec build_x power = 
      match power with
      1 -> Var
      | _ -> Binop (Mul, Var, build_x (power-1)) in
    let rec build_poly (coef, power) =
      match power with
      0 -> (Num coef)
      | 1 -> (Binop (Mul, Num coef, Var)) 
      | _ -> (Binop (Mul, (Binop (Mul, Num coef, Var)), build_x (power-1))) in
    let list_of_poly = List.map build_poly lst in
    if List.length list_of_poly > 0 then
      List.fold_left (fun acc a-> Binop (Add, acc, a)) (List.hd list_of_poly) (List.tl list_of_poly)
    else
      Num 0.0
  in
  (construct (combine (reduce e [])))


(*****************************************)
(* Problem 7: Automatic Differentiation *)
(*****************************************)

(*

"Forward mode automatic differentiation", has become an
important algorithm (since 2017 or so) in deep learning.
You can read about it in section 3.1 of this paper:
http://jmlr.org/papers/volume18/17-468/17-468.pdf
"Automatic Differentiation in Machine Learning: A Survey"
(and pay particular attention to Table 2 for a worked example).

So, the challenge (which is actually not very difficult) is,
write this function

 let evaluate2 (e: expression) (x: float) : float * float = ...

that computes both e(x) and the first derivative e'(x),
without ever calculating (derivative e).  Like evaluate,
do it by case analysis on the syntax-tree of e.

*)

let rec evaluate2 (e: expression) (x: float) : float * float =
  match e with 
  Num value -> (value, 0.0)
  | Var -> (x, 1.0)
  | Binop (op, e1, e2) ->
    let (eval_e1, deriv_e1) = evaluate2 e1 x in
    let (eval_e2, deriv_e2) = evaluate2 e2 x in
    match op with 
    Add -> (eval_e1 +. eval_e2, deriv_e1 +. deriv_e2)
    | Sub -> (eval_e1 -. eval_e2, deriv_e1 -. deriv_e2)
    | Mul -> (eval_e1 *. eval_e2, deriv_e1*.eval_e2 +. eval_e1*.deriv_e2)

(********)
(* Done *)
(********)

let _ = print_string ("Testing your code ...\n")

let main () =
  let error_count = ref 0 in
  let bonus_count = ref 1 in

 (* Testcases for fold_inorder *)
  let _ =
    try
      assert (fold_inorder (fun acc x -> acc @ [x]) [] (Node (Node (Leaf,1,Leaf), 2, Node (Leaf,3,Leaf))) = [1;2;3]);
      assert (fold_inorder (fun acc x -> acc + x) 0 (Node (Node (Leaf,1,Leaf), 2, Node (Leaf,3,Leaf))) = 6)
    with e -> (error_count := !error_count + 1; print_string ((Printexc.to_string e)^"\n")) in

 (* Testcases for remove *)
  let _ =
    try
      assert (remove 20 (Node (Node (Node (Leaf, 20, Leaf), 30, Node (Leaf, 40, Leaf)), 50, Node (Node (Leaf, 60, Leaf), 70, Node (Leaf, 80, Leaf))))
              = (Node (Node (Leaf,                  30, Node (Leaf, 40, Leaf)), 50, Node (Node (Leaf, 60, Leaf), 70, Node (Leaf, 80, Leaf)))));
      assert (remove 30 (Node (Node (Leaf,                  30, Node (Leaf, 40, Leaf)), 50, Node (Node (Leaf, 60, Leaf), 70, Node (Leaf, 80, Leaf))))
              = (Node (Node (Leaf,                  40, Leaf                 ), 50, Node (Node (Leaf, 60, Leaf), 70, Node (Leaf, 80, Leaf)))));
      assert (remove 50 (Node (Node (Leaf,                  40, Leaf                 ), 50, Node (Node (Leaf, 60, Leaf), 70, Node (Leaf, 80, Leaf))))
              = (Node (Node (Leaf,                  40, Leaf                 ), 60, Node (Leaf,                  70, Node (Leaf, 80, Leaf)))))
    with e -> (error_count := !error_count + 1; print_string ((Printexc.to_string e)^"\n")) in

 (* Testcases for evaluate *)
  let _ =
    try
      assert (evaluate (parse "x*x + 3.0") 2.0 = 7.0)
    with e -> (error_count := !error_count + 1; print_string ((Printexc.to_string e)^"\n")) in

 (* Testcases for derivative *)
  let _ =
    try
      assert (evaluate (derivative (parse "x*x + 3.0")) 2.0 = 4.0);
    with e -> (error_count := !error_count + 1; print_string ((Printexc.to_string e)^"\n")) in

 (* Testcases for zero finding *)
  let _ =
    try
      let e = (parse "2*x*x - x*x*x - 2") in
      let g, epsilon, lim = 3.0, 1e-3, 50 in
      let x = find_zero e g epsilon lim in
      match x with
      | None -> assert false
      | Some x ->
          let eval_result = evaluate e x in
          assert (0. -. epsilon < eval_result && eval_result < epsilon)
    with e -> (error_count := !error_count + 1; print_string ((Printexc.to_string e)^"\n")) in

 (* Testcases for simplify *)
  let _ =
    try
      (*print_string (to_string_wo_paren (simplify (parse "3*x*x + 8*x + 2*x*x - 5 - 5*x")));
       print_string (to_string_wo_paren (simplify (parse "(x-1)*x*(x-5)")));
       print_string (to_string_wo_paren (simplify (parse "x - x")));
      print_string (to_string_wo_paren (simplify (parse "x + x + 0")));
      print_string (to_string_wo_paren (simplify (parse "(x-1)*x*(x-5)*(4*x*x*x-11+66*x)")));*)
      assert (to_string_wo_paren (simplify (parse "3*x*x + 2*x - 5 + 4*x*x - 7*x")) = "7.*x*x+-5.*x+-5.");
      assert (to_string_wo_paren (simplify (parse "3*x*x + 8*x + 2*x*x - 5 - 13*x")) = "5.*x*x+-5.*x+-5.");
      assert (to_string_wo_paren (simplify (parse "(x-1)*x*(x-5)")) = "1.*x*x*x+-6.*x*x+5.*x");
      assert (to_string_wo_paren (simplify (parse "(x-1)*x*(x-5)*(4*x*x*x-11+66*x)")) = "4.*x*x*x*x*x*x+-24.*x*x*x*x*x+86.*x*x*x*x+-407.*x*x*x+396.*x*x+-55.*x");
      assert (to_string_wo_paren (simplify (parse "x - x")) = "0.");
      assert (to_string_wo_paren (simplify (parse "x + x + 0")) = "2.*x");
      assert (to_string_wo_paren (simplify (parse "0")) = "0.")
    with e -> (error_count := !error_count + 1; print_string ((Printexc.to_string e)^"\n")) in

 (* Testcases for evaluate2 *)
  let _ =
    try
      assert (evaluate2 (parse "x*x + 3") 2.0 = (7.0, 4.0))
    with e -> (bonus_count := !bonus_count - 1; print_string ((Printexc.to_string e)^"\n")) in

  if !error_count = 0 then Printf.printf ("Passed all testcases.\n")
  else Printf.printf ("%d out of 6 programming questions are incorrect.\n") (!error_count);

  if !bonus_count = 0 then Printf.printf ("The bonus problem is not solved.\n")
  else Printf.printf ("The bonus problem is solved.\n")

let _ = main()

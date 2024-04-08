open List

(******************************)
(*** For debugging purposes ***)
(******************************)

(* print out an integer list *)
let rec print_int_list lst =
  match lst with
  | [] -> ()
  | [x] -> print_int x; print_newline ()
  | x :: xs -> print_int x; print_string "; "; print_int_list xs

(* print out a string list *)
let rec print_string_list lst =
  match lst with
  | [] -> ()
  | [x] -> print_string x; print_newline ()
  | x :: xs -> print_string x; print_string "; "; print_string_list xs

(* print out a list of integer lists *)
let print_int_list_list lst =
  List.iter print_int_list lst

(* print out a list of string lists *)
let print_string_list_list lst =
  List.iter print_string_list lst


(***********************)
(* Problem 1: cond_dup *)
(***********************)

let rec cond_dup l f =
  (* Could done with fold, figure that out later *)
  match l with
  [] -> []
  | (h::t) -> 
    if f h = true then
      h::h::(cond_dup t f)
    else
      h::(cond_dup t f)

  (* let helper f acc h = 
    if f h = true then
      h::h::acc
    else
      h::acc
  in
  let rec fold helper f acc l = 
    match l with
    [] -> []
    | h::t -> fold f helper (helper f acc h) t 
  in 
  fold (helper) ([]) (l) *)
  

(**********************)
(* Problem 2: n_times *)
(**********************)

let rec n_times (f, n, v) =
  if n = 0 then
    v 
  else
    n_times (f, n-1, (f v))

(**********************)
(* Problem 3: zipwith *)
(**********************)

let rec zipwith f l1 l2 =
  let rec func f l1 l2 acc = 
    match (l1, l2) with
    ([], []) -> []
    | (h::t, []) -> acc
    | ([], h::t) -> acc
    | (h1::t1, h2::t2) -> func (f) (t1) (t2) ((f h1 h2)::acc)
  in List.rev(func f l1 l2 [])

(**********************)
(* Problem 4: buckets *)
(**********************)

let buckets p l =
  let list = List.map (fun a->[a]) l in
  let helper acc elem = 
    if List.length acc = 0 then
      if List.length elem = 0 then
        acc
      else
        elem::acc
    else
      let map_helper acc_elem = 
        if p (List.hd acc_elem) (List.hd elem) then
          acc_elem@elem
        else
          acc_elem
      in
      let temp = List.rev (List.fold_left (fun acc a -> a::acc) [] acc) in
      let accumlate = (List.map (map_helper) acc) in
      if (List.equal (fun a b -> List.equal (fun a1 b1 -> a1 = b1) a b ) accumlate temp ) then
        accumlate@[elem]
      else
        accumlate
  in
  List.fold_left (helper) [] list;;


(* val map : ('a -> 'b) -> 'a list -> 'b list *)
(* val fold_left : ('acc -> 'a -> 'acc) -> 'acc -> 'a list -> 'acc *)
(* val fold_right : ('a -> 'acc -> 'acc) -> 'a list -> 'acc -> 'acc *)
(* print_int_list_list (buckets (=) [1;1;2;3;4]);; *)

(**************************)
(* Problem 5: fib_tailrec *)
(**************************)

let fib_tailrec n =
  if n = 0 || n = 1 then
    if n = 0 then
      0
    else
      1
  else
    let rec func n1 n2 curr = 
      if curr > n then
        n2
      else
        func (n2) (n1+n2) (curr+1) 
    in func 0 1 2

(* let rec fib n = 
      if n = 0 then 0
      else if n = 1 then 1
      else fib (n-1) + fib (n-2);;  *)

(* print_int ((fib 50) - (fib_tailrec 50));; *)

(***********************)
(* Problem 6: sum_rows *)
(***********************)

let sum_rows (rows:int list list) : int list =
  let help l =
    let sum acc h = acc+h in
    List.fold_left sum 0 l
  in  
  List.map help rows

(* val map : ('a -> 'b) -> 'a list -> 'b list *)
(* val fold_left : ('acc -> 'a -> 'acc) -> 'acc -> 'a list -> 'acc *)
(* val fold_right : ('a -> 'acc -> 'acc) -> 'a list -> 'acc -> 'acc *)

(*****************)
(* Problem 7: ap *)
(*****************)

let ap fs args =
  let x = List.map (fun x -> List.map x args) fs in
  List.fold_right (fun h acc-> h@acc) x [] 

(* val map : ('a -> 'b) -> 'a list -> 'b list *)
(* val fold_left : ('acc -> 'a -> 'acc) -> 'acc -> 'a list -> 'acc *)
(* val fold_right : ('a -> 'acc -> 'acc) -> 'a list -> 'acc -> 'acc *)

(***********************)
(* Problem 8: prefixes *)
(***********************)

let prefixes l =
  let og_lst = l in
  let l1 = List.init (List.length og_lst ) (fun x -> List.init (x+1) (fun y -> y)) in
  let help = List.fold_left (fun acc x -> (List.nth og_lst x)::acc) [] in
  let helper = List.map help l1 in
  List.map List.rev helper

(* print_string_list_list (prefixes ["a";"b";"c";"d"]);; *)


(***********************)
(* Problem 9: powerset *)
(***********************)

let powerset l =
  let fold_helper acc elem = 
    let map_helper subset = 
      subset@[elem];
    in
    acc@List.map (map_helper) acc;
  in
  List.fold_left (fold_helper) [[]] l

(* Strategy for this way of getting powerset *)
(* start with [[]] an empty list list and for each element in the list (e.g [1;2;3]) which we doing fold_left 
and use each of element to append with every list in the subset list to get a new list of subset list
then append that list to the original list *)
(* Steps below: *)
(* 0. acc -> acc @ List.map (subset@[elem]) acc -> result_set *)
(* 1. [[]] -> [[]] @ [[1]] -> [[];[1]] *)
(* 2. [[];[1]] -> [[];[1]] @ [[2];[1;2]] -> [[];[1];[2];[1;2]] *)
(* 3. [[];[1];[2];[1;2]] -> [[];[1];[2];[1;2]] @ [[3];[1;3];[2;3];[1;2;3]] -> [[];[1];[2];[1;2];[3];[1;3];[2;3];[1;2;3]] *)
(* Done *)
 

(* let x = powerset [1;2;3];;
print_int_list_list x;; *)

(* Forbidden way (bitwise operation) *)
(* let powerset l =
  (* inspired from truthtable (gray code) *)
  let gray_code = List.init (int_of_float (( ** ) 2.0 (float_of_int (List.length l)))) (fun x -> x) in
  let power = List.rev(List.init (List.length l) (fun x -> x)) in
  let list = List.init (int_of_float (( ** ) 2.0 (float_of_int (List.length l)))) (fun x -> []) in
  let fold_helper gray_c acc index = 
    if (land) gray_c (1 lsl index) != 0 then
      (List.nth l index)::acc
    else
      acc
  in
  let func gray_c = List.fold_left (fold_helper gray_c) [] power in
  let run list = List.map (func) gray_code in
  run list *)
  (* By using bitwise and to check with the gray code chart to get if that element is that subset without duplicates *)
  
  (*000 = 0 in integer
    001 > bitwise and with 1 shift 0 times
    000*)

  (*Step1:  111 = 7 in integer
            001 > bitwise and with 1 shift 0 times
            001 > not equal to zero then that element exist in this subset
  *)
  (*Step2:  111 = 7 in integer
            010 > bitwise and with 1 shift 1 times
            001 > not equal to zero then that element exist in this subset
  *)
  (*Step3:  111 = 7 in integer
            100 > bitwise and with 1 shift 2 times
            100 > not equal to zero then that element exist in this subset
  *)


(* Thoughts *)
(* let x = powerset [1;2;3];;
print_int_list_list x;; *)
(* val map : ('a -> 'b) -> 'a list -> 'b list *)
(* val fold_left : ('acc -> 'a -> 'acc) -> 'acc -> 'a list -> 'acc *)
(* val fold_right : ('a -> 'acc -> 'acc) -> 'a list -> 'acc -> 'acc *)

(* let num_lst1 = List.init (int_of_float (( ** ) 2.0 (float_of_int (List.length [1;2;3])))) (fun x -> x);;
print_int_list num_lst1;;
(* [0; 1; 2; 3; 4; 5; 6; 7] *)

let num_lst2 =  List.init (List.length [1;2;3]) (fun x -> int_of_float (( ** ) 2.0 (float_of_int (x))));;
print_int_list num_lst2;;
(* [1; 2; 4] *)

let num_lst3 = List.init (List.length [1;2;3]) (fun x -> x);;
print_int_list num_lst3;;
[0; 1; 2] *)

    

(**************************)
(* Problem 10: assoc_list *)
(**************************)

let assoc_list lst =
  let helper acc element = 
    let map_helper element (x,count) = 
      if element = x then
        (x,count+1)
      else
        (x,count)
    in
    if(List.length acc = 0) then
      (element,1)::acc
    else
      if List.fold_left 
        (fun acc (x,count)-> 
          if x = element then 
            true 
        else 
          if acc = true then 
            true 
          else 
            false
        ) false acc then
        List.map (map_helper element) acc 
      else
        (element,1)::acc
  in
  List.fold_left (helper) [] lst 
(* fold with map *)

(* let rec print_list_of_tuples = function
  | [] -> ()
  | (x, y)::rest ->
    Printf.printf "(%s, %d)\n" x y;
    print_list_of_tuples rest;;
print_list_of_tuples (List.rev ((assoc_list ["a";"a";"b";"c";"a";"b";]))) *)


(* val map : ('a -> 'b) -> 'a list -> 'b list *)
(* val fold_left : ('acc -> 'a -> 'acc) -> 'acc -> 'a list -> 'acc *)
(* val fold_right : ('a -> 'acc -> 'acc) -> 'a list -> 'acc -> 'acc *)

(********)
(* Done *)
(********)

let _ = print_string ("Testing your code ...\n")

let main () =
  let error_count = ref 0 in

  let cmp x y = if x < y then (-1) else if x = y then 0 else 1 in

  (* Testcases for cond_dup *)
  let _ =
    try
      assert (cond_dup [3;4;5] (fun x -> x mod 2 = 1) = [3;3;4;5;5]);
      assert (cond_dup [] (fun x -> x mod 2 = 1) = []);
      assert (cond_dup [1;2;3;4;5] (fun x -> x mod 2 = 0) = [1;2;2;3;4;4;5])
    with e -> (error_count := !error_count + 1; print_string ((Printexc.to_string e)^"\n")) in

  (* Testcases for n_times *)
  let _ =
    try
      assert (n_times((fun x-> x+1), 50, 0) = 50);
      assert (n_times ((fun x->x+1), 0, 1) = 1);
      assert (n_times((fun x-> x+2), 50, 0) = 100)
    with e -> (error_count := !error_count + 1; print_string ((Printexc.to_string e)^"\n")) in

  (* Testcases for zipwith *)
  let _ =
    try
      assert ([5;7] = (zipwith (+) [1;2;3] [4;5]));
      assert ([(1,5); (2,6); (3,7)] = (zipwith (fun x y -> (x,y)) [1;2;3;4] [5;6;7]))
    with e -> (error_count := !error_count + 1; print_string ((Printexc.to_string e)^"\n")) in

  (* Testcases for buckets *)
  let _ =
    try
      assert (buckets (=) [1;2;3;4] = [[1];[2];[3];[4]]);
      assert (buckets (=) [1;2;3;4;2;3;4;3;4] = [[1];[2;2];[3;3;3];[4;4;4]]);
      assert (buckets (fun x y -> (=) (x mod 3) (y mod 3)) [1;2;3;4;5;6] = [[1;4];[2;5];[3;6]])
    with e -> (error_count := !error_count + 1; print_string ((Printexc.to_string e)^"\n")) in

  (* Testcases for fib_tailrec *)
  let _ =
    try
      assert (fib_tailrec 50 = 12586269025);
      assert (fib_tailrec 90 = 2880067194370816120)
    with e -> (error_count := !error_count + 1; print_string ((Printexc.to_string e)^"\n")) in

  (* Testcases for sum_rows *)
  let _ =
    try
      assert (sum_rows [[1;2]; [3;4]] = [3; 7]);
      assert (sum_rows [[5;6;7;8;9]; [10]] = [35; 10])
    with e -> (error_count := !error_count + 1; print_string ((Printexc.to_string e)^"\n")) in

  (* Testcases for ap *)
  let _ =
    let x = [5;6;7;3] in
    let b = [3] in
    let c = [] in
    let fs1 = [((+) 2) ; (( * ) 7)] in
    try
      assert  ([7;8;9;5;35;42;49;21] = ap fs1 x);
      assert  ([5;21] = ap fs1 b);
      assert  ([] = ap fs1 c);
    with e -> (error_count := !error_count + 1; print_string ((Printexc.to_string e)^"\n")) in

  (* Testcases for prefixes *)
  let _ =
    try
      assert (prefixes [1;2;3;4] = [[1]; [1;2]; [1;2;3]; [1;2;3;4]]);
      assert (prefixes [] = []);
    with e -> (error_count := !error_count + 1; print_string ((Printexc.to_string e)^"\n")) in

  (*sort a list of lists *)
  let sort ls =
    List.sort cmp (List.map (List.sort cmp) ls) in

  (* Testcases for powerset *)
  let _ =
    try
      (* Either including or excluding [] in the powerset is marked correct by the tester *)
      assert (sort (powerset [1;2;3]) = sort [[1]; [1; 2]; [1; 2; 3]; [1; 3]; [2]; [2; 3]; [3]] || sort (powerset [1;2;3]) = sort [[];[1]; [1; 2]; [1; 2; 3]; [1; 3]; [2]; [2; 3]; [3]]);
      assert ([] = powerset [] || [[]] = powerset [])
    with e -> (error_count := !error_count + 1; print_string ((Printexc.to_string e)^"\n")) in

  (* Testcases for assoc_list *)
  let _ =
    let y = ["a";"a";"b";"a"] in
    let z = [1;7;7;1;5;2;7;7] in
    let a = [true;false;false;true;false;false;false] in
    let b = [] in
    try
      assert ([("a",3);("b",1)] = List.sort cmp (assoc_list y));
      assert ([(1,2);(2,1);(5,1);(7,4)] = List.sort cmp (assoc_list z));
      assert ([(false,5);(true,2)] = List.sort cmp (assoc_list a));
      assert ([] = assoc_list b)
    with e -> (error_count := !error_count + 1; print_string ((Printexc.to_string e)^"\n")) in


  Printf.printf ("%d out of 10 programming questions passed.\n") (10 - !error_count)

let _ = main()

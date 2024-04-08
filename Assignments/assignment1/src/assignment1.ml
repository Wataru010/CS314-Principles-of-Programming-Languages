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

(* sz583 Sihua Zhou Done*)
(********************)
(* Problem 1: pow *)
(********************)

let rec pow x p =
  if p=0 then 1 else x * pow (x) (p-1)
  (* used to be if p=1 then x else x * pow (x) (p-1) didn't consider the cases of 0 (non-negative value), so assignment1.ml -0.2  *)

(********************)
(* Problem 2: range *)
(********************)

let rec range num1 num2 =
  if num2 < num1 then 
    []
  else
    if num1 = num2 then num2::[] else num1::range (num1+1)(num2) 

(**********************)
(* Problem 3: flatten *)
(**********************)

let rec flatten l =
  match l with
  [] -> []
  | h::[] -> h
  | h::t -> h @ flatten t

(*****************************)
(* Problem 4: remove_stutter *)
(*****************************)

let rec remove_stutter l =
  match l with
  [] -> []
  | h::[] -> h::[]
  | h::t::[] -> if h = t then h::[] else h::t::[]
  | h::t::r -> if h = t then remove_stutter(t::r) else h::remove_stutter(t::r)

(* let x4 = remove_stutter [1;2;2;3;1;1;1;4;4;2;2];; 
print_int_list x4;; *)

(*********************)
(* Problem 5: rotate *)
(*********************)

(* debug this *)
let rotate l n =
  (* (mod) n (List.lenght l) is to get rid of extra (since rotating List.length l times is just the list itself) *)
  (* and using list length to minus the value of actually times to shift the list is to get the complement times of shifts on the list *)
  (* because the function is adding first element to the end, so it is like reverse shifting, and that is why it needs complements *)
  (* i.e. 7 elements rotate 2 times needs to reverse 5 times to get the same result  *)
  let num = abs (List.length l - (mod) n (List.length l))
  in(
    let rec f list n = 
      if n = 0 
        then list 
      else 
        match list with 
          [] -> []
          | t::[] -> [t]
          | h::t -> f (t @ [h]) (n-1)
    in(f l num)
  )

(* let x5 = rotate ["a"; "b"; "c"; "d"; "e"; "f"; "g"; "h"] 2;;
print_string_list x5;; 
let x5 = rotate [1;2;3] 5;;
print_int_list x5;; *)



(*******************)
(* Problem 6: jump *)
(*******************)

let jump lst1 lst2 =
  let rec j l1 l2 curr =
    if (mod) (curr) (2) = 1 then
      let r2 = 
        match l2 with
        [] -> []
        | h::[] -> [h] 
        | h::r2 -> r2
      in
      match l1 with
      [] -> []
      | h::[] -> [h] 
      | h::r1 -> h::j (r1) (r2) (curr+1)
    else 
      let r1 = 
        match l1 with
        [] -> []
        | h::[] -> [h] 
        | h::r1 -> r1
      in
      match l2 with 
      [] -> []
      | h::[] -> [h]
      | h::r2 -> h::j (r1) (r2) (curr+1)
    in(j lst1 lst2 0)
    (* Some design or algorithm flaws for this function let assignment1 -0.2*2 *)
    (* Case 16: jump [1; 3; 5; 7; 9] [0; 2; 4; 6] *)
    (* Case 18: jump [] ["c"; "d"; "e"] *)

(* let x6 = jump [1; 3; 5; 7; 9; 11; 13; 15; 17; 19] [0; 2; 4; 6; 8];;
print_string "x6 jump:\n";;
print_int_list x6;; *)

(* let x6 = jump [1; 3; 5; 7] [0; 2; 4; 6; 8];;
print_string "x6 jump:\n";;
print_int_list x6;; *)

(* let x6 = jump ["a"; "b"] ["c"];;
print_string "x6 jump:\n";;
print_string_list x6;; *)

(******************)
(* Problem 7: nth *)
(******************)

let nth l n =
  let rec f l n count = 
    match l with
    [] -> []
    | h::[] -> if (mod) count n = 0 then h::[] else []
    | h::t -> if (mod) count n = 0 then h::f (t)(n) (count+1) else f (t) (n) (count+1)
  in(f (l) (n) (1))


(* let x7 = nth [1; 2; 3; 4; 5; 6; 7] 7;;
print_string "x7 nth:\n";;
print_int_list x7;; *)

(* let x7 = nth ["a";"b";"c";"d";"e";"f";"g";"j";"fjhf";] 3;;
print_string "x7 nth:\n";;
print_string_list x7;; *)

(*****************************************************)
(* Problem 8: Digital Roots and Additive Persistence *)
(*****************************************************)

(* digits : int -> int list
 * we assume n >= 0
 * (digits n) is the list of digits of n in the order in which they appear in n
 * e.g. (digits 31243) is [3,1,2,4,3]
 *)

let rec digitsOfInt n =
  if (<) n 0 then 
    []
  else
    let rec f1 n =
      if (mod) n 10 = n
        then n::[]
      else
        let x = (/) n 10
        in((mod) n 10::digitsOfInt x )
    in(
      let rec f2 l = 
        match l with
        [] -> []
        | h::[] -> [h]
        | h::t -> t @ f2 [h]
      in(f2 (f1 n))
    )
    
(* let x81 = digitsOfInt (-1);;
print_int_list x81;; *)


(* From http://mathworld.wolfram.com/AdditivePersistence.html
 * Consider the process of taking a number, adding its digits,
 * then adding the digits of the number derived from it, etc.,
 * until the remaining number has only one digit.
 * The number of additions required to obtain a single digit from a number n
 * is called the additive persistence of n, and the digit obtained is called
 * the digital root of n.
 * For example, the sequence obtained from the starting number 9876 is (9876, 30, 3), so
 * 9876 has an additive persistence of 2 and a digital root of 3.
 *)

let additivePersistence n =
  let rec f1 l =
    match l with
    [] -> 0
    | h::[] -> h
    | h::t -> h + f1 (t)
  in(
    let rec f2 n = 
      if (mod) n 10 = n 
        then 1
      else 
        1 + f2 (f1 (digitsOfInt n))
    in (
      if (mod) n 10 = n
        then 0
      else
        f2 (f1 (digitsOfInt n))
    )
  )

(* let x82 = additivePersistence (8);;
print_string "x82 additive persistence\n";;
print_int x82;;
print_string "\n";; *)

let digitalRoot n =
  let rec f1 l =
    match l with
    [] -> 0
    | h::[] -> h
    | h::t -> h + f1 (t)
  in(
    let rec f2 n = 
      if (mod) n 10 = n then n else f2 (f1 (digitsOfInt n))
    in (f2 (f1 (digitsOfInt n)))
  )

(* let x83 = digitalRoot (111111111);;
print_string "x83 digital root \n";;
print_int x83;;
print_string "\n";; *)

(********)
(* Done *)
(********)

let _ = print_string ("Testing your code ...\n")

let main () =
  let error_count = ref 0 in

  (* Testcases for pow *)
  let _ =
    try
      assert (pow 3 1 = 3);
      assert (pow 3 2 = 9);
      assert (pow (-3) 3 = -27)
    with e -> (error_count := !error_count + 1; print_string ((Printexc.to_string e)^"\n")) in

  (* Testcases for range *)
  let _ =
    try
      assert (range 2 5 = [2;3;4;5]);
      assert (range 0 0 = [0])
    with e -> (error_count := !error_count + 1; print_string ((Printexc.to_string e)^"\n")) in

  (* Testcases for flatten *)
  let _ =
    try
      assert (flatten [[1;2];[3;4]] = [1;2;3;4]);
      assert (flatten [[1;2];[];[3;4];[]] = [1;2;3;4])
    with e -> (error_count := !error_count + 1; print_string ((Printexc.to_string e)^"\n")) in

  (* Testcases for remove_stutter *)
  let _ =
    try
      assert (remove_stutter [1;2;2;3;1;1;1;4;4;2;2] = [1; 2; 3; 1; 4; 2]);
      assert (remove_stutter [] = []);
      assert (remove_stutter [1;1;1;1;1] = [1]);
      assert (remove_stutter [1;1;1;1;1;2] = [1;2])
    with e -> (error_count := !error_count + 1; print_string ((Printexc.to_string e)^"\n")) in

  (* Testcases for rotate *)
  let _ =
    try
      assert (rotate ["a"; "b"; "c"; "d"; "e"; "f"; "g"; "h"] 2 = ["g"; "h"; "a"; "b"; "c"; "d"; "e"; "f"]);
      assert (rotate ["a"; "b"; "c"; "d"; "e"; "f"; "g"; "h"] 0 = ["a"; "b"; "c"; "d"; "e"; "f"; "g"; "h"]);
      assert (rotate ["a"; "b"; "c"; "d"; "e"; "f"; "g"; "h"] 7 = ["b"; "c"; "d"; "e"; "f"; "g"; "h"; "a"])
    with e -> (error_count := !error_count + 1; print_string ((Printexc.to_string e)^"\n")) in

  (* Testcases for jump *)
  let _ =
    try
      assert (jump ["first"; "second"; "third"; "fourth"] ["fifth"; "sixth"; "seventh"; "eighth"] = ["fifth"; "second"; "seventh"; "fourth"]);
      assert (jump [1; 3; 5; 7] [0; 2; 4; 6; 8] = [0; 3; 4; 7]);
      assert (jump ["a"; "b"] ["c"] = ["c"])
    with e -> (error_count := !error_count + 1; print_string ((Printexc.to_string e)^"\n")) in

  (* Testcases for nth *)
  let _ =
    try
      (*print_int_list (nth [1; 2; 3; 4; 5; 6; 7] 1);*)
      assert (nth [1; 2; 3; 4; 5; 6; 7] 1 = [1; 2; 3; 4; 5; 6; 7]);
      assert (nth [1; 2; 3; 4; 5; 6; 7] 2 = [2; 4; 6]);
      assert (nth [1; 2; 3; 4; 5; 6; 7] 3 = [3; 6])
    with e -> (error_count := !error_count + 1; print_string ((Printexc.to_string e)^"\n")) in

  (* Testcases for digitsOfInt *)
  let _ =
    try
      assert (digitsOfInt 3124 = [3;1;2;4]);
      assert (digitsOfInt 352663 = [3;5;2;6;6;3]);
      assert (digitsOfInt 31243 = [3;1;2;4;3]);
      assert (digitsOfInt 23422 = [2;3;4;2;2])
    with e -> (error_count := !error_count + 1; print_string ((Printexc.to_string e)^"\n")) in

  (* Testcases for additivePersistence *)
  let _ =
    try
      assert (additivePersistence 9876 = 2)
    with e -> (error_count := !error_count + 1; print_string ((Printexc.to_string e)^"\n")) in

  (* Testcases for digitalRoot *)
  let _ =
    try
      assert (digitalRoot 9876 = 3)
    with e -> (error_count := !error_count + 1; print_string ((Printexc.to_string e)^"\n")) in

  Printf.printf ("%d out of 10 programming questions are correct.\n") (10 - !error_count)

let _ = main()
